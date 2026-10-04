import Std.Data.HashSet

/-!
# Reserved hardware identifiers

The words gin refuses as identifiers: the union of the Verilog-2005,
SystemVerilog-2017 and VHDL-2008 reserved words, words the supported tools
reject, and predeclared VHDL names. This is a copy of `reservedWords` in
`src/Gin/Netlist/Types.hs`, section for section; `scripts/export-examples.sh`
checks that the two lists are the same set of words.
-/

namespace Gin.Export

/-- The reserved words, separated by whitespace. -/
def reservedWordsText : String :=
  -- Verilog-2005 (IEEE 1364-2005 Annex B)
  "always and assign automatic begin buf bufif0 bufif1 case casex casez cell \
    cmos config deassign default defparam design disable edge else end endcase \
    endconfig endfunction endgenerate endmodule endprimitive endspecify endtable \
    endtask event for force forever fork function generate genvar highz0 highz1 \
    if ifnone incdir include initial inout input instance integer join large \
    liblist library localparam macromodule medium module nand negedge nmos nor \
    noshowcancelled not notif0 notif1 or output parameter pmos posedge primitive \
    pull0 pull1 pulldown pullup pulsestyle_onevent pulsestyle_ondetect rcmos real \
    realtime reg release repeat rnmos rpmos rtran rtranif0 rtranif1 scalared \
    showcancelled signed small specify specparam strong0 strong1 supply0 supply1 \
    table task time tran tranif0 tranif1 tri tri0 tri1 triand trior trireg unsigned \
    use uwire vectored wait wand weak0 weak1 while wire wor xnor xor " ++
  -- SystemVerilog-2017 additions (IEEE 1800-2017 Annex B)
  "accept_on alias always_comb always_ff always_latch assert assume before bind \
    bins binsof bit break byte chandle checker class clocking const constraint \
    context continue cover covergroup coverpoint cross dist do endchecker endclass \
    endclocking endgroup endinterface endpackage endprogram endproperty endsequence \
    enum eventually expect export extends extern final first_match foreach forkjoin \
    global iff ignore_bins illegal_bins implements implies import inside int \
    interconnect interface intersect join_any join_none let local logic longint \
    matches modport nettype new nexttime null package packed priority program \
    property protected pure rand randc randcase randsequence ref reject_on restrict \
    return s_always s_eventually s_nexttime s_until s_until_with sequence shortint \
    shortreal soft solve static string strong struct super sync_accept_on \
    sync_reject_on tagged this throughout timeprecision timeunit type typedef union \
    unique unique0 until until_with untyped var virtual void wait_order weak \
    wildcard with within " ++
  -- VHDL-2008 (IEEE 1076-2008 15.10)
  "abs access after alias all architecture array assert assume assume_guarantee \
    attribute begin block body buffer bus case component configuration constant \
    context cover default disconnect downto else elsif end entity exit fairness file \
    for force function generate generic group guarded if impure in inertial inout is \
    label library linkage literal loop map mod nand new next nor not null of on open \
    or others out package parameter port postponed procedure process property \
    protected pure range record register reject release rem report restrict \
    restrict_guarantee return rol ror select sequence severity shared signal sla sll \
    sra srl strong subtype then to transport type unaffected units until use \
    variable vmode vprop vunit wait when while with xnor xor " ++
  -- VHDL predeclared names that generated designs and testbenches use
  "std ieee std_logic_1164 std_logic std_logic_vector std_ulogic numeric_std unsigned signed \
    resize to_unsigned to_integer rising_edge natural integer boolean \
    work line write writeline to_string to_hstring shift_left shift_right \
    textio output env finish stop now time string character bit bit_vector \
    ns note error warning failure true false " ++
  -- Rejected by Icarus Verilog 13, Verilator 5.052 (-Wall SYMRSVDWORD) or
  -- nvc 1.23 although not reserved by the language standards
  "bool wone wreal reverse_range mailbox semaphore randomize abort alignas \
    alignof and_eq asm atomic_cancel atomic_commit atomic_noexcept auto bitand \
    bitor catch cdecl char char16_t char32_t compl complex concept const_cast \
    const_iterator constexpr decltype delete double dynamic_cast explicit far \
    float friend goto huge inline interrupt iterator long mutable namespace near \
    noexcept not_eq nullptr operator or_eq override pascal private public queue \
    reference requires sc_clock sc_in sc_inout sc_out sc_signal sensitive \
    sensitive_neg sensitive_pos short sizeof stack static_assert static_cast \
    switch synchronized template thread_local throw transaction_safe \
    transaction_safe_dynamic try type_info typeid typename uint16_t uint32_t \
    uint8_t using volatile wchar_t xor_eq"

/-- The reserved words. -/
def reservedWords : Std.HashSet String :=
  Std.HashSet.ofList ((reservedWordsText.split Char.isWhitespace).toList.map (·.toString)
    |>.filter (!·.isEmpty))

end Gin.Export
