# CoreRadiatedMajorant — author verification (modal Sol)

Eight new modules (nothing existing edited), imported in this order; every module compiled with the pinned
toolchain from `D:\oq14\lean` (`lake env lean X.lean -o .lake/build/lib/lean/X.olean`), exit 0, zero warnings, zero
errors, no `sorry`, one `#print axioms` for every theorem (including the primed `term_eq'`, `term_bound'`,
`continuous_term_y'`), all 101 reports `[propext, Classical.choice, Quot.sound]`. No docstring line begins with the
words axiom or constant. Author review only; root independent audit pending.

| module | lines | source SHA256 | final log SHA256 | reports |
|---|---|---|---|---|
| CoreWeakSeries | 210 | `DBD32B3D8276FD09B0FB84F4CBA177B9A13C5FF800D7379944B055805498F5F1` | `EB01DCFCCD6DB0420C48FA61A64675F5DBCA5E0BCC3BDAD6CE8B94E553586FDF` | 8 |
| CoreWeakLinear | 110 | `B402107E399119CCB6C822BDB846C06693D3DAC1928002C3372BDBACD7F31860` | `D3B96C5DA405C1586D6B6A7A39EFE230080D303F0530371B6AFCA523B8CE345A` | 5 |
| CoreOutgoingModes | 209 | `1EE40A099BB30E4C679EC7A2BF98D3AA09A10A5338F250203C0766F397D15AE0` | `EDC4607D3CC40F7ACC78E032E69D406CCD70F3AA4BFD1A5E47EB056439157831` | 22 |
| CoreFreePotential | 521 | `D34C7F77B96090E6AA101558E70A5188C63207D49A0815AE9D8DE6C91F890384` | `5A2B0332525FCE4D255F54F895A95EE71BF4C40F4A4BB1AF51CFCE29898A357F` | 21 |
| CoreReactionDegree | 335 | `95D0462677851B51E4DE8C960E99EF878E3A76AB8347B6B7B2554E901FD2C647` | `CEC69DC3150C653CDBF64FA8FB405329FBE1044E9A1674665FC8E55D1C606815` | 5 |
| CoreRegularModes | 279 | `0D26B8EA1B90F1AB582E87B39CA5FE4D9C073F4DD8FE8752FCC0E2FA44AA76D2` | `2D92E2EA934F0027FD84633813913ABBD78468C4C8ED1027635593C58DC20480` | 10 |
| CoreReaction | 806 | `999F35850697860F070E99CA1D59EB4DEA5489A4CC4507149C417D7B502425FA` | `6D39FD9FBD9D92EFCE58EC673692C1B6A9601CE7FC679B79D5F61C6A457DD07A` | 23 |
| CoreRadiatedMajorant | 224 | `C0667E106CDA6CCFE3ED42FF335E3851EBE183210D24B3B6C1F4264C07E5E927` | `10A146AEC16B486103D96A1BDB6325A72EE0C0E14CF798419A74F05C05B99420` | 7 |

Logs: `lean/logs/<module>-final.log` and `<module>-final.exit.log` (= 0); drafts `<module>-checkN.log`.

## Architecture

Generic machinery (CoreWeakSeries, CoreWeakLinear). `decomp_tsum_gen` is `SourceRemotePlaneSeries.decomp_tsum` for an
arbitrary index type. `WeakOn Ω E H` is the weak first Maxwell equation `curl E = I H` tested against Schwartz
functions of compact support inside the open set `Ω` (the frozen `curlPair`, `fieldPair`). `weakOn_tsum`: if the
mode pairs `(E a, H a)` are continuous on `Ω`, have a common summable sup-majorant on `Ω` and satisfy `WeakOn`, so
does the pair of sums (dominated convergence for the test integrals). `weak_unique`: two magnetic fields continuous
on `Ω` with the same electric field and `WeakOn` coincide on `Ω` (the fundamental lemma
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` plus `Measure.eqOn_open_of_ae_eq`). `weakOn_combo`: the rotated
pair `(α E + β H, α H - β E)` of a weak pair with `curl H = -I E` is weak. `weakOn_congr`, `weakOn_of_scaled`.

This is the device that identifies the magnetic series without differentiating the electric series: the mode-wise
weak Maxwell equations plus the weak Maxwell equation of the actual field (frozen `response_forced`,
`representative_forced`, `electric_ae_interior`) plus continuity force `H = sum of the dual mode series`.

(1) Free potential (CoreOutgoingModes, CoreFreePotential). The vacuum modes of `OutgoingSpatialSeries` are
`-I * outE`, `-I * outH` (`vacE_eq`, `vacH_eq` with `vacuum (data l) = data l` by `rfl`); `weak_out_pair` gives the
weak equations from the frozen `SourceUnclippedMaxwell.first/second_weak_maxwell`. Moments `momentTM`, `momentTE` (the
integrals of the regular dyad coefficients `tmCoefficient`, `teCoefficient` against the source), bounded by
`coefBound b B a * mass`. `electric_free_hasSum`: for `R < |x|` the dyadic potential is
`sum_a (-I momentTM_a) outE_a(x) + (-I momentTE_a) outH_a(x)` (dominated convergence in `y` with the frozen geometric
majorant `OutgoingGeometricTail.majorant`, `OutgoingFreeDyadic.actual_free_dyadic`). `outgoing_piece` decomposes each
mode with `BackgroundFluxMajorant.eh_decomp_state` on the outgoing state and the frozen
`HankelExteriorBounds.regular_outgoing_geometric`; the degree constants are `degConst b R m a = (m/4) majorant b R a`.
`magnetic_free_hasSum`: `H = sum_a (-I momentTM_a) outH_a - (-I momentTE_a) outE_a` by the weak device above.

(2) Reaction (CoreReactionDegree, CoreRegularModes, CoreReaction). The frozen total-index series
`SourceTensorResponse.physical_hasSum` holds for EVERY `|x| < R_r` and `|y| <= b` (the conditions involve only
`b, B, T < R_r`), so the growing core is covered by the identity; the term is
`tm(y) (muTM solidE(x)) + te(y) (muTE solidH(x))` (`SourceModeReaction.tm/te_normalization`), with
`mu = gamma + I` the reaction multiplier and `solidE`, `solidH` the regular Maxwell pair `SolidMaxwellProfiles`.
`reaction_degree_bound` is the new uniform radial estimate (see the gap list: this is the only genuinely new analytic
input): there is `C` depending only on `(q, M, d, b0, rho0)` with
`amplitude l 0 * b0^l * |gamma_l + I| * (|psi_l(s)| + |psi_l'(s)|) <= C (l+1) (1/2)^l` for all stacks with inner
radius `R >= max rho0 (2 e^{3/4} b0)`, outer radius at most `2R`, thickness at most `d`, all degrees `l` and all
radii `rho0 <= s <= R`. Three degree ranges: `angular l <= R^2/4` (`RadialSource.gamma_low_range`: `|gamma|` bounded,
the regular state bounded by the outgoing geometric lemma at radius `>= rho0`); `R^2/4 < angular l`, `l <= 2 q R`
(`RadialIntermediateBound.actual_gamma_window_bound`: `|gamma| <= C e^{c l}`, absorbed by the same geometric lemma
at the scale `b0 e^{8 exponent}`); `2 q R <= l` (`RadialStackHighTail.actual_reaction_bound` at `s` and at `b0`,
Cauchy-Schwarz, `RiccatiGaussianBound.regular_gaussian_lower` to compare `amplitude b0^(l+1)` with `psi_l(b0)`,
`RiccatiLogDerivative.barrier_logDerivative_bounds` for `psi'`). `regular_piece`/`regular_pair_decomp` give the plane
decomposition of the polarized regular pair with the degree constant
`regConst b m C a = m scale0 scaleA C (a.1+2)^9 (1/2)^(a.1+1)`. `reactionField_hasSum` is the series of the shell
reaction field (dominated convergence; the majorant in `a` is the unit-moment bound `unit_bound`);
`reaction_magnetic_hasSum` identifies the magnetic reaction field with the dual series by the weak device: the weak
equation of `(reactionField, magneticReactionField)` in the hole is `weak_reaction` (the frozen
`reactionField_eq_free`, `magneticReactionField_eq_free` identify them with the free fields of the induced shell
polarization `shellSource`, a source vanishing on the ball of radius `R_r`), and the continuity of the magnetic
reaction field in the hole is `magnetic_hollow_continuousAt` (differentiation under the integral of the shell
source, the frozen `response_dcoord_hollow`).

(3) Total (CoreRadiatedMajorant). `core_total_decomp` adds the decomposition of the background and of the two
radiated parts with `decomp_add`/`decomp_mono`; `core_flux_majorant` applies `flux_bound_of_decomp`;
`core_flux_majorant_te` instantiates the background with the TE family `famBackground`, `famBackgroundH` of
`BackgroundFluxMajorant.background_decomp_majorant`.

## Exact statements (all in namespaces `OQ14.<module>`)

`CoreFreePotential.free_potential_decomp (b B R m) (hb : 0 <= b) (hB : 0 <= B) (hscale : degreeScale 2 b <= B)
(hR : 2 <= R) (hBR : 2*(B*base) <= R) (hbR : b <= R) (rho : Fin 3 -> Space -> C) (hrho : forall j, Integrable (rho j))
(hc : forall j y, y notin closedBall 0 b -> rho j y = 0) (hF : exists F : VectorL2, forall j, physicalCoordinate F j =ae rho j)
(hm : mass rho <= m) : forall x, R < ||x|| -> Decomp (3 * freeConst b R m) (freeConst b R m) (ExteriorContinuity.electric 1 rho x) x
/\ Decomp (3 * freeConst b R m) (freeConst b R m) (MagneticResponse.magnetic 1 rho x) x`, with
`freeConst b R m = sum' a, (m/4) * OutgoingGeometricTail.majorant b R a` (linear in `m`, independent of `rho`
beyond `mass rho = sum_j int |rho j|`). `hF` (an `L2` representative of the source) is used only for the magnetic part.

`CoreReaction.reaction_core_decomp (q hq n) (ci) (d : SupportData ci) (b) (hb : 0 <= b) (hcar : forall x in d.carrier, ||x|| <= b)
(rho1) (hrho1 : rhoMin q b <= rho1) : exists K, 0 <= K /\ eventually (r : N) in atTop, forall (u : VectorL2) (x : Space),
rho1 < ||x|| -> ||x|| < (SourcePairedInclusion.data q hq n r).R -> Decomp (3*K*||u||) (K*||u||) (fun i => reactionField (shell q hq n r) ci
(data..).X (data..).R (data..).X u x i) x /\ Decomp (3*K*||u||) (K*||u||) (fun i => magneticReactionField ..) x`,
with `rhoMin q b = max 1 (2 * (max 1 (degreeScale 2 b) * base * exp (8 * exponent q)))`.
`K = massConst ci d * sum' a, regConst b 1 C a` depends on `q, n` (through the thickness of the stack), `b`, `rho1`, the
carrier mass constant `3 sqrt(ci.bound) sqrt(vol carrier)`, not on `r`, `u`, `x`.

`CoreRadiatedMajorant.core_total_decomp (q hq n) (ci d b hb hcar) (rho1) (hrho1 : coreMin q b <= rho1)
(Einc Hinc : N -> Field) (K1b K2b L1b L2b) (hE : forall r x, rho1 < ||x|| -> Decomp K1b K2b (Einc r x) x)
(hH : ..) : exists K, 0 <= K /\ eventually r, forall u x, rho1 < ||x|| -> ||x|| < R_r ->
Decomp (K1b + 3*K*||u||) (K2b + K*||u||) (fun i => pairedPlaneElectric q hq n r ci u (Einc r) x i) x /\
Decomp (L1b + 3*K*||u||) (L2b + K*||u||) (fun i => pairedPlaneMagnetic q hq n r ci u (Hinc r) x i) x`.

`CoreRadiatedMajorant.core_flux_majorant (same, K1b K2b L1b L2b >= 0) (U) : exists C >= 0, eventually r, forall u,
||u|| <= U -> forall x, x 2 = 0 -> rho1 < ||x|| -> ||x|| < R_r -> ||crossProduct (E_tot x) (conjugate (H_tot x)) 2|| <= C / ||x||^3`.

`CoreRadiatedMajorant.core_flux_majorant_te (q hq n) (A : Index ->0 C) (ci d b hb hcar) (U) : exists rho1 C, 0 < rho1 /\ 0 <= C /\
eventually r, forall u, ||u|| <= U -> forall x, x 2 = 0 -> rho1 < ||x|| -> ||x|| < R_r ->
||crossProduct (pairedPlaneElectric q hq n r ci u (famBackground (physicalTE q _ n r) A.support (teCoeff A) _ polynomial) x)
(conjugate (pairedPlaneMagnetic q hq n r ci u (famBackgroundH (physicalTE ..) ..) x)) 2|| <= C / ||x||^3`.

## Gaps and scope (exact)

1. All reaction statements are EVENTUAL in the shell index (`R_r = radius r = 2 pi (r+1)` larger than the explicit
   thresholds `T`, `b`, `max rho1 (2 e^{3/4} b0)`, and the thickness at most `R_r`). The region is
   `rho1 < |x| < R_r` with `rho1 >= rhoMin q b` (resp. `coreMin q b`); the point `|x| = rho1` is excluded (strict
   inequality, needed to have an open annulus for the weak/continuity device), and `|x| >= R_r` (shell, annulus,
   exterior) is not covered here (the layered mode series outside the core is a separate piece).
2. The free-potential statement needs an `L2` representative `hF` of the source for the magnetic part (true for
   `source ci u` with `F = sqrtMultiplier ci u`); the electric part does not. The strict inequality `R < |x|`.
3. `core_flux_majorant` / `core_total_decomp` take the incident fields `Einc r`, `Hinc r` as abstract fields with a
   decomposition hypothesis; `core_flux_majorant_te` instantiates them with the TE background family
   (`famBackground`, `famBackgroundH`). The identification of the physical background `backgroundElectric cs X inc fs`
   of the combined solution (stage 33, `combined_total_electric_eq`) with this family on the core is the stage-30/32
   statement and is NOT re-proved here.
4. The norm of the inclusion vector enters linearly; the statements are uniform over `||u|| <= U`; a uniform bound for the
   effective inclusion solutions `effective^{-1}(datum)` is the caller's input.
5. `reaction_degree_bound` constants are not optimized: `C` is explicit in `CoreReactionDegree` (sum of the low/window/
   barrier constants); the 8 exponent in `rhoMin` (`exp (8 exponent q)`) is what the window range needs to absorb the
   exponential growth `e^{c l}` of `gamma` against the factorial decay of the source factor.
6. Nothing is claimed about the actual flux defined piecewise outside the core, about the L2/continuous-representative
   identification at core points inside the ball of the carrier (stage-33 note), or about parity/closure.

No existing file was edited. The queued follow-up (`BackgroundTransmissionParity`) was not started.
