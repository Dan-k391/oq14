# Radial harmonic test calculus audit

Root full-source and targeted compiler audit: PASS.
Independent 6.1 Sol full-source review and recompile: PASS.

Seven declarations prove the actual first and second spatial derivatives of
`ψ(‖x‖²)`, its Laplacian, the second product derivative, the Laplacian product
rule, and the Laplacian of a radial factor times an actual homogeneous
harmonic function. The last theorem has explicit actual smoothness, Euler
and zero-Laplacian premises; it does not posit a separate spatial operator.

Final targeted source SHA256:
`B3FAE1EBDFAAC66C0548EBD3C993715ADB266725493D438827DEA8B269608C8D`.
All seven compiler reports contain only `propext`, `Classical.choice` and
`Quot.sound`.

This is a test-function calculation. It is not by itself an exterior
uniqueness theorem.
