# ExteriorHelmholtz verification

Frozen source: `lean/ExteriorHelmholtz.lean`.
SHA256: `EC9DA031304ACCC3A1C9C2B50056DFDF9F84E2CA7C73841E0508416343E665BB`.

Pinned Lean 4.19 compilation and importable object export completed with exit
0 and no warnings. All eight selected theorem dependency reports contain
only `propext`, `Classical.choice`, and `Quot.sound`.

The scalar Laplacian is defined by the sum of the actual three pure second
coordinate Frechet derivatives. It is proved equal both to the actual
divergence of the actual gradient and, under local smoothness, to the trace
of the actual second Frechet derivative. The existing verified curl-curl
identity is restated using this concrete Laplacian, without duplicating its
coordinate-calculus proof.

For the actual compact integrable electric and magnetic source fields,
neighborhood Maxwell equations and neighborhood smoothness give genuine
curl-curl values k^2 E and k^2 H. The existing exterior Gauss equations hold
throughout the exterior neighborhood for k nonzero. Congruence of actual
Frechet derivatives with the locally zero divergence functions gives zero
gradient of divergence. The genuine curl-curl identity then proves each
actual electric and magnetic component satisfies Delta f+k^2 f=0.

No Helmholtz relation, divergence relation, field differentiability, or weak
solution identification is supplied as a premise of the actual-field
Helmholtz exports. Their premises are real nonzero frequency and the actual
integrability and compact support of the source. No exterior Rellich or
interior unique-continuation conclusion is asserted in this module.

Root completed the independent full-source audit at the frozen hash above and accepted all eight selected results. Final freeze PASS.
