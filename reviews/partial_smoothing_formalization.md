# Actual weak derivative smoothing and test density

`lean/WeakPoynting/PartialSmoothing.lean` is frozen at SHA-256
`fcbc7c5899e51e6ebf789751e2fecdcd419f939dc3918d22da17ab40420626a8`.
Its direct compiler capture and source-scoped provenance are
`partial-smoothing-verification.txt` and `partial-smoothing-provenance.json`
beside the source. All nine selected exports compile with only
`propext`, `Classical.choice`, and `Quot.sound`.

The module proves convolution commutation for actual distributional scalar
partial derivatives, using the reflected compact C1 test and its derivative
sign. When the original L2 class has a compact representative, the same
convolutions are actual Schwartz functions; both their values and each of
their three partial derivatives converge in L2.

Applied to an arbitrary compact C1 test, this gives a simultaneous Schwartz
approximation of the test and its first derivatives. Continuity of the actual
bilinear L2 integral then proves that identities established on Schwartz tests
extend to every test in the existing `HasWeakPartial` and `HasWeakCurl`
definitions. The final two exported theorems provide this interface directly.

No density or compact embedding premise is assumed. The module proves the
approximation bridge; a uniform compactness theorem is separate work.
