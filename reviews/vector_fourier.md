# Actual vector Plancherel and physical projection

Source: `lean/VectorFourier.lean`, Lean 4.19.0 with the pinned mathlib and the frozen `FourierL2` and `LongitudinalProjection` modules.

The Euclidean-space/Cartesian-coordinate identification uses mathlib's actual measurable equivalence and its proved preservation of volume. Pullback in both directions gives inverse scalar L2 isometries; the scalar Fourier transform is transported through these maps.

The component decomposition is constructed on genuine vector-valued L2, rather than postulated as an identification. Coordinate extraction uses actual continuous linear coordinate maps on Euclidean complex vectors. Integrating the finite Hermitian coordinate sum proves inner-product preservation. Actual coordinate insertion and finite assembly prove surjectivity, giving the vector-L2/component-L2 isometric equivalence.

The vector Fourier transform is then obtained by applying the actual scalar Fourier equivalence in all three components. It is a complex linear isometric equivalence. The exported Schwartz embedding and almost-everywhere integral agreement identify both its input field and transformed field with the actual component functions and ordinary Fourier integrals.

The physical-space longitudinal projection is the constructed conjugate F-inverse M F of the previously checked multiplier. Its operator norm is at most one; it is idempotent, self-adjoint, and positive. The exact Fourier-coordinate formula is exported, including the zero-frequency convention inherited from the symbol. There is no assumption of a Fourier map, coordinate equivalence, or longitudinal operator.

Independent review: hotspots read the complete source. The coordinate inverse and measure arguments, finite component inner product, insertion/assembly inverse, Fourier integral agreement, and projection conjugation all passed. No mathematical or scope defect found.

Validation: the complete source compiled without errors or warnings. All 31 exported theorem dependencies were checked explicitly; each has exactly `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom or proof placeholder is used.

Remaining scope: identification of this physical Fourier projection with the Newton-potential convolution or a particular Maxwell static-volume kernel is not asserted here. Likewise, this module alone does not formalize existence or scattering for the finite dielectric devices.
