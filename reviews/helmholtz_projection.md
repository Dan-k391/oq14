# Actual closed-gradient-space characterization

Source: `lean/HelmholtzProjection.lean`, using the frozen scalar/vector Fourier and actual Schwartz differential modules.

The spectral coordinates are genuine scalar L2 fields on Euclidean three-space. Their coordinate-weighted sum xi dot F is locally integrable: L2 gives local integrability, and multiplying by a continuous coordinate preserves integrability on compact sets. The explicit inner product with an inverse-Fourier Schwartz gradient is the integral of the conjugated scalar test against this sum, with the correct conjugate of 2 pi i.

For a field orthogonal to every actual Schwartz gradient, inverse Fourier transforms of compact smooth real scalar tests therefore annihilate xi dot F. The proved distribution test theorem forces it to vanish almost everywhere. Actual measure-preserving coordinate maps transfer this identity to the previously constructed symbol, so the physical longitudinal projection vanishes. The converse follows from self-adjointness and the proved action on gradients.

The rest is an exact Hilbert-space identification: the orthogonal complement of the span of actual Schwartz gradients is the kernel of P; double orthogonal complement gives the closed span; P F lies in it and F-P F lies in its orthogonal complement. Thus P equals its actual orthogonal projection and its range equals that closed span. A variational uniqueness export identifies any member of this closed span whose residual annihilates all actual Schwartz gradients with P F.

Independent review: hotspots read the complete source, checking the representatives, local integrability, conjugation and Fourier normalization, real-test separation of a complex distribution, a.e. coordinate transfer, and orthogonal-complement closure reasoning. No defect found.

Validation: complete source compiled without warnings or errors. All 16 theorem exports were checked with `#print axioms` and each reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no custom axioms or proof placeholders.

Scope: the closed space is explicitly the closure of the complex span of gradients of scalar Schwartz functions. No equality with a separately defined Newton convolution, no compact-support-gradient density assertion, and no dynamic Maxwell remainder estimate is assumed or claimed here.
