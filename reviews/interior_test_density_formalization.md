# Interior compact-test density

`lean/WeakPoynting/InteriorTestDensity.lean` is frozen after a clean direct Lean 4.19.0 check. Its eight selected exports use only `propext`, `Classical.choice`, and `Quot.sound`.

Source SHA-256: `05dd3b4fd702786febb014f6c93f0064e163fdce1d786d167ffcc00fe02e0d5d`.

The main theorem, `OQ14.InteriorTestDensity.interior_test_approximation`, constructs, for every actual `DomainCurl.Test Ω` with Ω open, a sequence of Schwartz functions supported in one fixed compact subset of Ω. The sequence converges in the actual whole-space L2 norm to the test, and each of its three first derivatives converges in L2 to the corresponding test derivative.

The proof uses the already proved actual compact-C1 Schwartz approximation, then multiplies every approximant by one constructed smooth compact cutoff equal to one near the original support. Bounded multiplication is proved continuous on L2 classes; the ordinary derivative product rule identifies the derivative limits. The construction does not assume a density or extension theorem, and does not require smoothness of the boundary of Ω.

This is test-function density. It does not assert extension by zero of arbitrary regional H(curl) fields, any boundary trace theorem, or compactness up to a boundary.

The complete compiler output and source-hash-scoped dependency provenance are saved as `lean/WeakPoynting/interior-test-density-verification.txt` and `lean/WeakPoynting/interior-test-density-provenance.json`. The independently emitted olean is available in the existing local build cache.
