# Radial state bounds scope (rg:states), October 24, 2026

Author: modal Sol agent. Read of the sources named in the task, plus `RadialSource`, `RadialGluing`, `RadialStack`, `RadialGreen`, `RadialPropagation`, `RadialIntermediateBound`, `HankelPositive`, `RiccatiGaussianBound` and `manuscript/sections/radial_green_limit.tex` (Lemma `rg:states`). Statements are copied from the sources; long ones are abridged with an ellipsis. One new module was written: `lean/BarrierSourceStateBounds.lean` (hashes in `reviews/barrier_source_state_bounds.md`).

## 0. Summary

- The degree-uniform, radius-uniform bounds that already existed control the shell reaction coefficient `gamma_l` (and the reaction series with source radial factors on compact balls). They do not bound the actual exterior radial states `(u_l, p_l)(x)` for `x >= X` or in the annulus.
- The exact relation `|A_l|^2 = -Im gamma_l` links the exterior amplitude `A_l = 1/beta_l` to `gamma_l`; it was in the tree (`RadialSource.gamma_im`) but not stated as an amplitude bound. It is now (`amplitude_sq_le_gamma`).
- New: a Lean bound of the exterior source state `sourceState l gs R X hR x` for all exterior radii `x > X`, in all three degree regimes (low, intermediate window, barrier/high), each uniform in the exterior radius and independent of the degree within its regime, and in the barrier range the source-weighted geometric bound that `rg:states` needs. What is still missing is (i) the same bound inside the annulus `[R, X]` (the glued state through the layer interfaces), (ii) the summation over degrees with the source moment bounds and angular weights (the actual sums of `rg:states`), and (iii) all-degree constants in the single-mode plane flux theorem. Section 4 states the smallest next theorem exactly.

## 1. The source state and its normalization

`RadialSource.coefficients l gs R X hR : State` with `beta := (coefficients l gs R X hR).2`, `gamma := (coefficients ...).1 / beta`, `SourceRadiation.amplitude d = (coefficients d.l d.gs d.R d.X d.hR).2⁻¹` (so `A_l = beta⁻¹`). `RadialGluing.sourceState l gs R X hR x` is the continuous radial state through all interfaces: the core wave `(coreWave, coreWaveD)` for `x <= R`, the layered profile for `R < x <= X`, and `beta⁻¹ • outgoing l x` for `x > X` (`RadialGluing.sourceState_exterior`). Exact identities in the tree:

- `RadialSource.gamma_im (l gs R X hR) (hX : 0 < X) : (gamma l gs R X hR).im = -1/Complex.normSq (coefficients l gs R X hR).2`.
- `RadialSource.coreWave_wronskian (l gs R X hR x) (hx : x ≠ 0) : (regular l x : ℂ)*coreWaveD l gs R X hR x - (regularD l x : ℂ)*coreWave l gs R X hR x = 1`.
- `RadialSource.coreWave_boundary (l gs R X hR) (hX : 0 < X) : coreWave l gs R X hR R = (traverse l gs (outgoing l X)).1/(coefficients l gs R X hR).2 ∧ coreWaveD l gs R X hR R = (traverse l gs (outgoing l X)).2/(coefficients l gs R X hR).2`.
- `RadialGreen.source_value_cancellation`, `source_derivative_cancellation`, `loadDenom_normSq_lower` (the Wronskian cancellation algebra of `rg:wcancellation`, in terms of a load `h` with `h.re <= 0`).
- Barrier monotonicity: `RadialGreen.barrier_interval_monotonicity` (radial load monotone, `|u|^2` and `|p|^2` antitone on an interval for a barrier ODE), `RadialPropagation.actual_layer_barrier`, `RadialStack.back_load`, `traverse_load`, `outgoing_traverse_load`, `outgoing_traverse_logDerivative`.

## 2. What degree-uniform bounds already existed

### Shell reaction coefficient `gamma_l`

- Low range: `RadialLowTail.actual_gamma_low_bound (l) (hc : Chain gs X R) (M d) (hM : 0 <= M) (hR : 0 < R) (hd : X-R <= d) (hl : 2*((l:ℝ)+1) <= R) (hp : ∀ g ∈ gs, 1 <= g.σ ∧ g.σ <= M ∧ g.q^2 <= M) : ‖RadialSource.gamma l gs R X hR‖ <= bound M d`; `RadialSource.gamma_low_range`.
- Intermediate window: `RadialIntermediateBound.actual_gamma_window_bound (l) (hc) (q M d) (hq : 1 <= q) (hM) (hR : 1 <= R) (hX : X <= 2*R) (hd) (hl : (l:ℝ) <= 2*q*R) (hp) : ‖gamma l gs R (zero_lt_one.trans_le hR)‖ <= (frameConstant q)^2*Real.exp (4*HankelIntermediateBounds.exponent q*R+(2*M+angularBound q)*d)`.
- General energy bound, all degrees: `RadialSource.gamma_stack_bound : ‖gamma l gs R X hR‖ <= frobeniusSq l R*Real.exp (totalCost l gs)*frobeniusSq l X`; `gamma_energy_bound`.
- High order with the source regular factor: `RadialHighOrderBound.actual_reaction_high_order (l gs R X s) ... (hl : 2*R <= l) (hstack : ∀ g ∈ gs, g.q^2*g.b^2 <= HankelEnergy.angular l) : ‖gamma l gs R X hR‖*(regular l s)^2 <= 4*Real.exp (3*R/2)*s^(2*l+2)/((2*l+1:ℝ)*R^(2*l+1))`; `RadialStackHighTail.common_stack_barrier`, `actual_reaction_bound`, `actual_tail_bound : weightedTail gs X (2*q) s k R <= 4*s^2*Real.exp (-R/2)*geometricWeight k`, `actual_tail_decay`, `actual_tail_tendsto_zero`; `RadialHighOrderTail.weightedTail_le`, `weightedTail_decay`.
- Assembled majorant, uniform for `R >= 4`, `e*b <= R`, `X <= 2R`, `X-R <= d`: `RadialFullMajorant.component_weighted_bound (l k m n) (hc) (q M d b) ... : (l+1)^k*‖component l m n gs R X _ z w‖ <= majorant q M d b k l`, `majorant_summable`, `actual_norm_series_summable`. Here `component l m n = gamma * origin^(m) z * origin^(n) w`, so with `m = n = 0`, `z = w = s` this is `(l+1)^k ‖gamma_l‖ regular_l(s)^2 <= majorant`: the source-radial-factor-weighted `gamma` is summable in `l` uniformly in `R`. `RadialLowTail.uniform_angularTail_decay`, `RadialMiddleTail.uniform_normTail_decay` give the moving-cutoff tails.
- Compact jets: `PhysicalReactionLimit.uniform_physical_jet_limit`, `VectorReactionLimit.uniform_physical_jet_limit`, `SourcePairedTensor.uniform_actual_jet_limit`: convergence of the reaction series and its jets in compact regions, with summable index majorants (`eventually_map_majorant`).

### Hankel and angular factors

- Exterior Hankel, all degrees: `HankelExteriorBounds.xi_uniform (l R r) (hR : 0 < R) (hr : R <= r) : ‖xi l r‖ <= coefficient l l/R^l*Real.exp R`, `xiD_uniform`, `regular_outgoing_product : amplitude l 0*B^l*‖xi l r‖ <= Real.exp R/(2*l+1)*(B/R)^l`, `regular_outgoing_geometric`, `polynomial_weighted_summable`. Note the factor `exp R`: these are not uniform in the shell radius `R`.
- `HankelIntermediateBounds.xi_intermediate_bound`, `xiD_intermediate_bound`: `‖xi l r‖ <= exp (exponent q*R)` for `R <= r <= 2R`, `l <= 2qR`. `HankelEnergy.low_range_normSq_bounds (l c R r) (hc : c^2 < 1) ... (hl : angular l <= c^2*R^2) : normSq (xiD l r) <= 2 ∧ normSq (xi l r) <= 2/(1-c^2)`; `energy_monotone`, `energy_le_two`.
- Angular: `AngularExteriorBounds.envelope l = scale*(l+1)^3*base^l`, with `radial_bound`, `toroidal_bound : ‖angularToroidal (representative l m) n i‖ <= 2*envelope l`, `poloidal_bound : ... <= (l+1)*envelope l`: all-degree explicit constants for the angular factors.

### Fixed-degree and single-mode (not degree-uniform)

`RadialPhaseLimit.actual_gamma_limit`, `normalizedCoefficients_limit`, `RadialFiniteLimit.physical_pairs_limit`; `SourceFarAmplitude.electric_exterior`, `electric_ray`, `magnetic_ray` and their limits; `SourceRemotePlaneFlux.plane_flux_bound` (constant `8‖amplitude d‖^2 l(l+1) M1 M2`, degree-dependent, per mode); `TransversePlaneFlux.leading_zero`.

## 3. What the exterior flux of the full response needs

By `SourceFarAmplitude.electric_exterior` and `magnetic_exterior`, the degree-`l` exterior field is the amplitude `A_l` times the scaled Hankel polynomial factors `p_l(r), p'_l(r)` times the source moment and angular factors. The absolute plane flux over the exterior needs, uniformly in the shell radius `R >= R0` and in the exterior radius `r >= X`,

`Sum_l (l+1)^k * |f_lm| * (|u_l(r)| + |p_l(r)|) <= C`,

with `u_l = A_l xi_l`, `p_l = A_l xi_l'`, and `|f_lm| <~ ‖P‖_2 (l+1)^b S^(l+1)/(2l+1)!!` (the source moment bound, which is `~ regular_l(S)`). Equivalently: the source-weighted exterior state bound `regular l S * (‖u_l‖+‖p_l‖)` is summable in `l` with polynomial weights uniformly in `R` and `r`. The Hankel bounds above alone cannot give this (`|xi_l|` is factorially large for `l > r`, and `|A_l|` alone is not small); one needs the combined quantity `A_l xi_l` through the stack, which is exactly Wronskian cancellation plus barrier monotonicity.

## 4. New Lean content and what remains

`lean/BarrierSourceStateBounds.lean` (27 theorems, all standard-only; reviews/barrier_source_state_bounds.md). Main statements (copied):

```lean
theorem endpoint_state_bound (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hν : R^2<OQ14.RiccatiBarrier.ν l) :
    ‖coreWave l gs R X hR R‖ ≤ 1/regularD l R ∧ ‖coreWaveD l gs R X hR R‖ ≤ 1/regular l R

theorem exterior_state_bound_high ... (hl : 2*q*R ≤ l) (x : ℝ) (hx : X<x) :
    ‖(sourceState l gs R X hR x).1‖ ≤ 1/regularD l R
theorem exterior_momentum_bound_high ... :
    ‖(sourceState l gs R X hR x).2‖ ≤ max (1/regular l R) (Real.sqrt (1/(regular l R*regularD l R)))
theorem source_weighted_exterior_high ... (s : ℝ) (hs : 0<s) (hsR : s ≤ R) (x : ℝ) (hx : X<x) :
    regular l s*‖(sourceState l gs R X hR x).1‖ ≤ 2*R*Real.exp (R/2)/((l : ℝ)+1)*(s/R)^(l+1) ∧
    regular l s*‖(sourceState l gs R X hR x).2‖ ≤ Real.exp (R/2)*(s/R)^(l+1)

theorem low_exterior_state_bound ... (hl : 2*((l : ℝ)+1) ≤ R) ... :
    ‖(sourceState l gs R X hR x).1‖^2 ≤ RadialLowTail.bound M d*(2/(1-(1/2 : ℝ)^2)) ∧
    ‖(sourceState l gs R X hR x).2‖^2 ≤ RadialLowTail.bound M d*2
theorem middle_exterior_state_bound ... (hl : (l : ℝ) ≤ 2*q*R) ... :
    ‖(sourceState ... x).1‖^2 ≤ G*(exp (exponent q*R))^2 ∧ ‖(sourceState ... x).2‖^2 ≤ G*((1+2*q)*exp (exponent q*R))^2
  -- G = (frameConstant q)^2*exp (4*exponent q*R+(2*M+angularBound q)*d)
theorem amplitude_sq_le_gamma (l gs R X hR) (hX : 0<X) : (‖(coefficients l gs R X hR).2‖⁻¹)^2 ≤ ‖gamma l gs R X hR‖
theorem regularD_lower (l R) (hR : 0<R) (hl : 2*R ≤ l) : ((l : ℝ)+1)/(2*R)*regular l R ≤ regularD l R
theorem regular_at_lower (l R) (hR) (hl : 2*R ≤ l) : amplitude l 0*R^(l+1)*Real.exp (-R/2) ≤ regular l R
theorem norm_xi_antitone / norm_xiD_le_max : ‖xi l r‖ ≤ ‖xi l R‖ (R ≤ r);  ‖xiD l x‖ ≤ max ‖xiD l X‖ 1 (X ≤ x)
```

The barrier-range proof is the manuscript's: the traversed outgoing state has nonpositive radial load (`outgoing_traverse_load`), the Wronskian identity plus that sign gives `reg^2|p|^2 + regD^2|w|^2 <= 1` at `R`, the normalized state moduli are monotone through the barrier layers (`back_normSq_ge`, `traverse_normSq_ge`, via `actual_layer_barrier`), and the exterior outgoing function has decreasing modulus. The result is `|A_l xi_l(x)| <= 1/psi'_l(R)` and `|A_l xi_l'(x)| <= max(1/psi_l(R), ...)` for every `x > X`, hence the geometric source-weighted bound with the `exp (R/2)` factor of `rg:barrierstates` (the Gaussian lower bound for `psi_l(R)` and `psi'_l(R) >= (l+1)/(2R) psi_l(R)` are proved, not assumed). In the low and intermediate regimes the exterior state bound is `|A_l|^2 <= ||gamma_l||` times the Hankel moduli bounds.

Not in the new file, in decreasing order of size:

1. Annulus states. The same bound for `x` in the stack, `R <= x <= X`, i.e. for the glued `RadialGluing.profile` between interfaces (the exterior statement only used the endpoints). Proposed statement, barrier range: `∀ x ∈ Icc R X, ‖(sourceState l gs R X hR x).1‖ ≤ 1/regularD l R ∧ ‖(sourceState l gs R X hR x).2‖ ≤ 1/regular l R` under `hbarrier` and `R^2 < ν l`. Route: `RadialGreen.barrier_interval_monotonicity` on each layer and continuity across interfaces (`profile_continuous`, `sourceState_continuousOn`). This is the smallest missing theorem (a stack-induction argument; not attempted).
2. The degree sums of `rg:states`: with the source moments `|f_lm| <= C‖P‖_2 (l+1)^b S^(l+1)/(2l+1)!!`, `∃ R0 C, ∀ R >= R0, ∀ x > X, Summable (fun l => (l+1)^k*regular l S*(‖u_l(x)‖+‖p_l(x)‖)) ∧ tsum <= C`, built from the low/intermediate/barrier pieces above plus factorial decay against `exp (exponent q*R)` in the intermediate window (the moving-cutoff machinery `RadialMiddleTail.movingTail`, `majorant` is the model).
3. All-degree constants in `SourceRemotePlaneFlux.plane_flux_bound` (use `AngularExteriorBounds.poloidal_bound` and `radial_bound`), the TE dual, finite sums over modes and the plane integral of the `r^-3` tail; then the annulus and exterior flux (`rg:remote`).

Feasibility: item 1 is a day-scale induction over the layer list; item 2 is several days; item 3 is days. None of these needs a new estimate beyond what the manuscript lemma states.


## Update: annulus states (BarrierAnnulusStateBounds)

Item 1 above is now proved in `lean/BarrierAnnulusStateBounds.lean` (11 theorems, standard-only; `reviews/barrier_annulus_state_bounds.md`): `annulus_state_bound` (barrier range, `‖(sourceState l gs R X hR x).1‖ ≤ 1/regularD l R ∧ ‖(sourceState ...).2‖ ≤ 1/regular l R` for every `x ∈ Icc R X`), `source_weighted_all_high` (the geometric source-weighted bound at every `x ≥ R`), `profile_energy_le` and `annulus_energy_le` (layerwise energy propagation), `low_annulus_state_bound` and `middle_annulus_state_bound`. Items 2 and 3 remain.
