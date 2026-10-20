# Independent Sol audit of the actual local Green identity

Source: `lean/ExteriorGreen.lean`.

Audited SHA256: `01FF2B9A36E06C5B93AC6A308589D2396F36EDE7E1003D690DC314A0C1EBCCB7`.

Independent full-source mathematical audit: PASS. Independent pinned Lean 4.19 compilation: exit 0, no warnings, eleven dependency reports containing only `propext`, `Classical.choice`, and `Quot.sound`, on 2026-10-20. The frozen source was not edited.

The compact interior cutoff is an actual globally smooth function equal to one on a neighborhood of every point in the compact test support, with compact support inside the open domain. Multiplication localizes the arbitrary exterior-smooth field to a globally smooth compactly supported field; outside the open domain the cutoff vanishes on a neighborhood, which correctly supplies smoothness without any regularity assumption on the original field there.

The second-coordinate derivative identity applies the genuine compact-test integration-by-parts theorem twice. Its second application uses compact support of the differentiated test. Finite summation and proved integrability give the actual Laplacian Green identity.

The local transfer uses neighborhood equality on the test support, including equality of actual second derivatives. Outside that support both the test and its Laplacian vanish, so the integrands agree pointwise without outside-domain assumptions on the original field. The separate local integrability theorem uses the same localization and compact support of the actual test Laplacian. Finally the actual classical Helmholtz equation on the domain yields the bilateral weak compact-test Helmholtz identity with the correct sign and factor k squared. No PDE, Green identity, or integrability conclusion is inserted as a premise.
