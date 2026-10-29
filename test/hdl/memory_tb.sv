// Independent memory peer and scoreboard for a 3-lane, 8-bit wrapper.
module memory_tb;
  logic clk=0, rst=1, cmd_valid=0, cmd_ready;
  logic [7:0] cmd_src=0, cmd_dst=128;
  logic [8:0] cmd_count=11;
  logic done_valid, done_error, done_ready=0;
  logic [2:0] mem_req_valid, mem_req_write, mem_req_ready=0;
  logic [23:0] mem_req_addr, mem_req_wdata;
  logic [2:0] mem_rsp_valid=0, mem_rsp_ready;
  logic [23:0] mem_rsp_rdata=0;
  gin_memory_accelerator dut(.*);
  always #5 clk=~clk;
  integer ticks=0, reads=0, writes=0;
  integer delay_count[0:2];
  logic pending[0:2];
  logic [7:0] response_data[0:2];
  logic blocked[0:2];
  logic [16:0] blocked_payload[0:2];
  integer seen[0:255];
  logic [7:0] memory[0:255];
  integer address;

  initial begin
    for (integer i=0; i<256; i=i+1) begin memory[i]=i*17; seen[i]=0; end
    for (integer i=0; i<3; i=i+1) begin pending[i]=0; blocked[i]=0; delay_count[i]=0; end
  end
  // Drive the memory peer away from the DUT's active clock edge.
  always @(negedge clk) begin
    for (integer i=0; i<3; i=i+1) begin
      mem_req_ready[i] = !rst && ((ticks+i)%4 != 0);
      mem_rsp_valid[i] = !rst && pending[i] && (delay_count[i] == 0)
        && ((ticks+i)%3 != 0);
      mem_rsp_rdata[i*8 +: 8] = response_data[i];
    end
  end
  always @(posedge clk) begin
    ticks=ticks+1;
    if (ticks>4000) $fatal(1,"timeout");
    for (integer i=0; i<3; i=i+1) begin
      if (rst) begin pending[i]=0; blocked[i]=0; delay_count[i]=0; end
      else begin
        if (blocked[i] && (!mem_req_valid[i] ||
            {mem_req_write[i],mem_req_addr[i*8 +: 8],mem_req_wdata[i*8 +: 8]}
              !== blocked_payload[i]))
          $fatal(1,"request changed under backpressure");
        blocked[i]=mem_req_valid[i] && !mem_req_ready[i];
        blocked_payload[i]={
          mem_req_write[i],mem_req_addr[i*8 +: 8],mem_req_wdata[i*8 +: 8]};
        if (pending[i] && delay_count[i]>0) delay_count[i]=delay_count[i]-1;
        if (mem_rsp_valid[i] && mem_rsp_ready[i]) begin
          if (!pending[i]) $fatal(1,"unsolicited response");
          pending[i]=0;
        end
        if (mem_req_valid[i] && mem_req_ready[i]) begin
          if (pending[i]) $fatal(1,"more than one outstanding request");
          address=mem_req_addr[i*8 +: 8];
          pending[i]=1;
          delay_count[i]=2+i;
          if (mem_req_write[i]) begin
            if (address<128 || address>=139) $fatal(1,"bad write address");
            if (seen[address]!=0) $fatal(1,"duplicate write");
            if (mem_req_wdata[i*8 +: 8] !== ((memory[address-128]+1)&255))
              $fatal(1,"wrong transformed data");
            seen[address]=seen[address]+1;
            memory[address]=mem_req_wdata[i*8 +: 8];
            writes=writes+1;
            response_data[i]=0;
          end else begin
            if (address>=11 || address%3!=i) $fatal(1,"bad read mapping");
            response_data[i]=memory[address];
            reads=reads+1;
          end
        end
      end
    end
  end
  task command(input [7:0] source, input [7:0] destination, input [8:0] count);
    begin
      @(negedge clk); cmd_src=source; cmd_dst=destination; cmd_count=count; cmd_valid=1;
      do @(posedge clk); while (!cmd_ready);
      @(negedge clk); cmd_valid=0;
    end
  endtask
  task consume_done(input logic expected_error);
    begin
      wait(done_valid);
      repeat (5) begin
        @(negedge clk);
        if (!done_valid || done_error!==expected_error || cmd_ready)
          $fatal(1,"unstable completion");
      end
      done_ready=1;
      @(negedge clk); done_ready=0;
    end
  endtask
  initial begin
    repeat (2) @(negedge clk); rst=0;
    command(0,128,11);
    consume_done(0);
    if (reads!=11 || writes!=11) $fatal(1,"lost transaction");
    for (integer i=128; i<139; i=i+1) if (seen[i]!=1) $fatal(1,"missing output");
    command(250,128,11); consume_done(1);
    command(0,0,11); consume_done(1);
    command(0,0,0); consume_done(0);
    if (reads!=11 || writes!=11) $fatal(1,"invalid or empty command issued traffic");
    // Cancel outstanding reads and reset the memory peer at the same edge.
    command(0,128,11);
    wait(reads>11);
    @(negedge clk); rst=1;
    @(negedge clk);
    if (done_valid || mem_req_valid!=0 || mem_rsp_ready!=0)
      $fatal(1,"reset did not cancel command");
    reads=0; writes=0;
    for (integer i=128; i<139; i=i+1) seen[i]=0;
    rst=0;
    command(0,128,11); consume_done(0);
    if (reads!=11 || writes!=11) $fatal(1,"restart lost transaction");
    $display("MEMORY-PASS");
    $finish;
  end
endmodule
