# Generic memory accelerator

`Gin.Memory.generateMemoryAccelerator` accepts a combinational normal-form
kernel with one bit-vector input and one output of the same width. It emits
the checked kernel and a synthesizable SystemVerilog wrapper. Configuration
selects 1–16 independent lanes and 1–64 address bits. These are logical memory
ports; mapping them to HBM channels, AXI, clocks, pins and physical constraints
belongs to a platform adapter.

The wrapper accepts a command on `cmd_valid && cmd_ready`. Its `src`, `dst`
and `count` are word addresses and a number of words. Source and destination
ranges must fit the address space and be disjoint. Invalid commands complete
with `done_error` and issue no memory requests. Zero-length commands succeed.
`done_valid` and `done_error` remain stable until `done_ready`.

Lane i visits i, i+lanes, … below count. Each lane performs a read request,
waits for its response, transforms that word, performs a write request and
waits for its acknowledgement before proceeding. There is at most one
outstanding request on each lane. Every accepted request requires exactly
one response; write-response data is ignored. Responses must preserve order
per lane. Request payload remains stable until accepted. The interface does
not contain transaction IDs or memory-error recovery. Completion follows all
write acknowledgements. Different lanes may complete out of order, while
each destination address receives its corresponding transformed source word.

Reset is synchronous, active high. It cancels the current command and clears
completion. The memory adapter must also reset or drain cancelled responses
before accepting another command. Reset is not a promise to undo writes that
the memory already accepted.

`simulateMemory` models independent ports with explicit request acceptance
period, response presentation period, read latency, write acknowledgement
latency, channel count and a cycle cap. Word address modulo channel count
selects a channel. Each channel accepts at most one request and presents at
most one response per service cycle; separate round-robin arbiters advance
after each grant. More lanes therefore cannot multiply a fixed channel's
service bandwidth. The arbiter models an external adapter, which is not
included in the generic per-lane HDL ports. Inputs are a finite sequence of unsigned kernel
words; the model places destinations in a disjoint logical range. Its trace
and counts describe this deterministic model only. `CycleLimit` preserves
partial output and is inconclusive about eventual completion. The three
default scenarios illustrate latency and backpressure sensitivity. Cycles
are not nanoseconds, transaction counts are not watts, and this model makes
no HBM bandwidth, timing closure, area or physical power claim.

Public API: `MemoryConfig`, `defaultMemoryConfig`, `MemoryDesign`,
`generateMemoryAccelerator`, `TrafficScenario`, `defaultTrafficScenarios`,
`MemoryRunStatus`, `MemoryRun`, `MemoryEvent`, `MemoryOperation`, and
`simulateMemory`. `decodeTrafficScenarios` reads the strict JSON format shown
in `examples/memory-traffic.json`: every field is required, names are unique
1–64 character ASCII identifiers, and unknown or duplicate keys fail.
`decodeMemoryWords` reads an array such as `examples/memory-words.json`.
JSON words use the existing decoder's unsigned 31-bit number bound; the
Haskell API accepts wider integers when they fit the kernel width.
Inputs are validated on every operation, including record
updates. The cycle cap is at most 1,000,000; simulated words at most 100,000;
the word/kernel-bind product at most 20,000,000. Results retain at most four accepted
handshakes per word.
