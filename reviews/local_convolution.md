# Actual locally L2 convolution

Frozen source: `lean/LocalConvolution.lean`.

SHA256: `D87C7668CEF342CCDF13D48DFB2E8B08C41A5A72571829D52F084E3EADA26190`.

The pinned Lean 4.19 compiler and direct olean emission completed successfully on 2026-10-20. All five exported theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

For any actual locally integrable complex kernel and an actual compactly supported L1 source with an L2 representative, the literal convolution is L2 on every observation ball. The proof truncates the kernel at the sum of observation and source radii, identifies the actual integral there exactly, and applies the previously proved L1 convolution operator. Local integrability follows by finite-measure L2 to L1 and compact containment.

Root independently audited the full mathematical source and accepted the exact cutoff and actual spatial L2 conclusion. The final source explicitly specifies the global Lebesgue measure in its integrability hypotheses, avoiding an elaborator ambiguity with the observation-region restriction. No mathematical premise was added to solve that elaboration issue.

Hotspots subsequently independently audited the complete source and also found no defect.
