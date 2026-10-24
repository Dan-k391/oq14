# Partner-ball transfer: what the doubled counting statement needs (author scope note, October 24)

Author scope note by the channel proof agent. All statements below marked COMPILED are in final author-PASS modules (hashes in the individual reviews); statements marked PROPOSED are not compiled. Nothing here assumes the missing physical bridge as a premise.

## 1. Local facts requested (compiled)

(1) `lean/RestrictedTEPartnerBalls.lean` (reviews/restricted_te_partner_balls.md). The doubled family has index type `ι ⊕ ι` with centres `Sum.elim p (fun l => rot (p l))` and radii `Sum.elim r r`; `partnerCoefficient p r χ hχ := FiniteSphereStatic.coefficient (partnerCentre p) (partnerRadius r) χ hχ`, `partnerSupport` its `BoundedMaterialKernel.SupportData` in `closedBall 0 R`. The partner balls DOUBLE the dipole count (`card_partner : Fintype.card (ι ⊕ ι) = 2 * Fintype.card ι`). COMPILED: `partner_symmetric : HalfTurnVectorAction.Symmetric (partnerCoefficient p r χ hχ)`; `partner_bound : (partnerCoefficient p r χ hχ).bound = χ`; `partner_zero_outside` (value zero outside `closedBall 0 R` when `‖p l‖ + r l ≤ R`); `partner_carrier_norm : x ∈ carrier → ‖x‖ ≤ R`; `partnerData` for the scaled radii `ρ a`; device geometry `rot_abovePoint`, `partner_gap`, `partner_separation` (separation `min δ (2|r|)`), `partner_height`.

(2) `lean/RestrictedTEEvenDatum.lean` (reviews/restricted_te_even_datum.md). The sector predicate is not needed: the finite TE potentials are built from `EvenHarmonicProjection.project`, so `RestrictedTEFields.electric_half_turn` gives half-turn invariance of the incident electric field of EVERY `A : Index →₀ ℂ`; the outputs of `PhysicalTEBandInterpolation.interpolate` are automatically in the even sector and need no further projection. COMPILED: `electric_invariant`, `magnetic_invariant` (`HalfTurnMaxwellParity.Invariant`), `electric_rot`, `magnetic_rot` (`F (rot x) i = o i * F x i`), and
`datum_fixed (c) (hsym : Symmetric c) (d) (A) : HalfTurnVectorAction.U (RestrictedTEMaterial.datum c d A) = RestrictedTEMaterial.datum c d A`, plus `partner_datum_fixed` for the partner coefficient.

Extra compiled facts used below: `RestrictedTEPartnerSmall.partner_perturbation_small : ∃ δ0 > 0, ∀ a (ha : 0<a) (ha1 : a≤1), a < δ0 → perturbationBound (partnerData p ρ χ R hρ hχ hi a ha ha1) 1 (b/a) < 1/2` (for `b > 0`), which discharges `hpar : perturbationBound d 1 (q^n) < 1` of `SourcePairedParityClosure.paired_shell_solutions_tendsto_parity_of_small` along `a = b/q^n`.

## 2. Can the counting statement be re-instantiated with the doubled family? Yes (compiled)

`RestrictedTEPartnerCount.doubled_device_counting` is `RestrictedTEPlaneJets.explicit_parity_device_counting` applied to the index type `ι ⊕ ι`, with centres `partnerCentre (p a)`, plane positions `Sum.elim c (fun l => -c l)`, normals `Sum.elim n (fun l => -n l)`, the same orthonormal family `A`, and a section `D` with `-q ∈ D ↔ q ∈ D`. The flux of the partner dipoles through `D` is exactly the half-turn image of the original flux through `D`: by the half-turn covariance of the incident fields (`partner_jets`: `E_z(-q) = E_z(q)`, `H_t(-q) = -H_t(q)` for every input) the passage coefficient of a partner dipole equals that of the original one (`kap_partner`), and `halfPlane (-n) h = halfPlane n h` (`halfPlane_neg`). Hence the doubled constant is `p0' = 2 * p0`, with `ηt < 2 p0 < δt`; its jet hypotheses (HT, HK, HB) are those of the original family with the original `p0`. Statement (compiled):

    theorem doubled_device_counting (p ρ χ δ R b γ ...) (hsep hi hh' for the partner centres) (c h hhpos hp hcd)
      (n hn) (D) (hDsym : ∀ q, -q ∈ D ↔ q ∈ D) (hD : local half-plane structure at each original point)
      (A) (horth) (HT HK) (p0 ηt δt) (HB : ∑ l, (kap ρ χ A' c n l).re * halfPlane (n l) (h l) = p0 on the unit sphere)
      (hη : ηt < 2*p0) (hδt : 2*p0 < δt) :
      ∀ᶠ a in 𝓝[>] 0, ∀ A' ∈ span ℂ (range A), physicalPower A' = 1 →
        ηt ≤ passage volume D (Fflux (fun a => partnerCentre (p a)) ρ χ R b hρ hχ hi a A') ∧
        bypass volume D (Fflux (fun a => partnerCentre (p a)) ρ χ R b hρ hχ hi a A') ≤ δt

and the concrete instance `RestrictedTEConcreteDoubled.concrete_doubled_counting` (points `(r,y_l,0)`, `r > 0`, images above `(-r,-y_l,0)`, section `D = {|x| > r}`, jets from the interpolation theorem) with `ηt < 2*(Vb ρ * halfPlane (1,0) h / scale) < δt`. The section `D` is unbounded; a bounded symmetric section with the same local half-plane structure at the `2N` points satisfies the same hypotheses of the abstract theorem (the abstract statement uses only the local structure).

## 3. What the transfer to the actual dielectric still needs (PROPOSED, in the order of the diagonal argument)

Matching of parameters. Take `b = 1`, `a_n := (q^n)⁻¹`, so `1/a_n = q^n` and `a_n ≤ 1`, `a_n -> 0`. For each fixed `n` set `ci_n := partnerCoefficient (p a_n) (fun _ => ρ*a_n) χ hχ`, `d_n := partnerData p ρ χ R hρ hχ hi a_n _ _`, `f_n := RestrictedTEMaterial.datum ci_n d_n A'`. COMPILED inputs for `paired_shell_solutions_tendsto_parity_of_small`: `hsym` (`partner_symmetric`), `hcar` (`partner_carrier_norm`, with `0 < R` from `ρ > 0`), `hf : U f_n = f_n` (`datum_fixed`, for every `A'` in the span), `hpar` (`partner_perturbation_small`, for `n` large).

R1 (smallness of the data, root definitions). PROPOSED, needs `SourcePairedSmallness.limitKernelNorm`:

    theorem partner_dataSmallness (q hq) (p ρ χ R ...) :
      ∀ᶠ n in atTop, SourcePairedSmallness.dataSmallness q hq n (partnerCoefficient (p (q^n)⁻¹) (fun _ => ρ*(q^n)⁻¹) χ hχ)
        (partnerData p ρ χ R hρ hχ hi (q^n)⁻¹ _ _) R < 1

The expected mechanism: carrier volume is `O(a_n^3)` while the limit kernel norm grows like `q^(2n) = O(a_n^-2)`, so the product is `O(a_n)`; the dynamic `errorBound ci 1 R` term must be checked as well. This is the only closure hypothesis I cannot discharge without the definition of `limitKernelNorm`.

R2 (from effective solutions to plane flux). `paired_shell_solutions_tendsto_parity_of_small` gives convergence in vector L2 of the effective inclusion solutions to the parity solution `solution d_n 1 (q^n) f_n`. The counting statement is about the whole-plane flux. PROPOSED (shape): for every unit-power `A'` and `n` large, as the shell index `r -> infinity` the actual plane flux density of the paired-shell device converges in whole-plane L1 to `Fflux (fun a => partnerCentre (p a)) ρ χ R 1 hρ hχ hi a_n A'`; this needs the identification of the actual plane field (incident plus shell Green response plus inclusion response) with the parity-device plane representative `ParityPlaneFields.totalElectric` plus a uniform-in-`r` inverse-cube tail bound for the actual kernel (the analogue of `cl:planebounds` for the finite-stack kernel). That bridge is the physical finite-stack/remote-annulus step owned by root and the modal track.

R3 (diagonal choice). PROPOSED: given margins `ηt < p0' < δt`, choose `ε` with `3 ε < min (p0' - ηt) (δt - p0')`, then `n` with `a_n` in the regime of `doubled_device_counting` (all compiled hypotheses of section 2 hold for `a ∈ (0, a0)` eventually), then `r` large so that the actual-flux L1 error to `Fflux` is at most `ε`; the conclusion follows from `RestrictedTEPassageTransfer.abs_passage_sub_le`, `abs_bypass_sub_le` exactly as in `explicit_parity_device_counting`. The order matches uc:counterexample (fix `a`, then the remote radius).

R4. Throughput and power normalization of the full scattering map (unit throughput) and homogeneity of the counting inequalities beyond the unit sphere, unchanged from the earlier scope note.

## 4. Summary

(1) and (2) are clean and compiled. The doubled counting statement is obtained by re-instantiating the existing theorem on `ι ⊕ ι` with `p0' = 2 p0` and a half-turn symmetric section; the interpolation family needs no change and no extra even projection. What blocks the transfer to the actual dielectric is R1 (a smallness inequality in root definitions) and R2 (plane-flux convergence of the actual finite-stack device), not the partner-ball construction.
