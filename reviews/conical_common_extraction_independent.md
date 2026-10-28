# ConicalCommonExtraction — independent root audit

PASS. Fresh pinned Lean 4.19.0 source check, exit 0, 3 qualified standard-only axiom reports, no compiler warnings or errors. Uses existing dependency objects; not a clean aggregate build.

Log: `lean/logs/ConicalCommonExtraction-root-audit.log`.
Source SHA256: `b5329531e72cfd75b1f14cdb06c24e12fee2abcd8c98987f488cd8060ae762b4`.
Log SHA256: `293684c6dc926324d48345e328c48309b9ffcb2d3b488b3ea02b5ed2d6a601e4`.

The full source was read. Subtracting a System from itself supplies a genuine zero-correction comparison. Existing correction and particular-pair stability estimates bound the difference of the extraction numerator and total pairing by a constant times the local correction bound. This is a quantified extraction estimate; nonzero actual common coefficients still need the convergence and nonzero static pairing assembled.
