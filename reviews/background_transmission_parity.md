# BackgroundTransmissionParity — author verification (modal Sol)

New module `lean/BackgroundTransmissionParity.lean` (444 lines, imports `RadialPairedFamily`,
`BackgroundCoreTransmission`, `RestrictedTEActualCore`, `RestrictedTEEffectiveBand`; nothing existing edited).
Source SHA256 `60F1CC92DEF53123243BC21758203B07FF35D2A77D0FD40746BF253CBEDD300F`. Final log
`lean/logs/BackgroundTransmissionParity-final.log` SHA256 `8B52B9957B5F1179B14904859D0B9396DA64AE0F6EF4E33389126DFCFAED9510`,
exit file `lean/logs/BackgroundTransmissionParity-final.exit.log` = 0, object `.lake/build/lib/lean/BackgroundTransmissionParity.olean`
(896336 bytes). Exit 0, zero warnings, zero errors, no `sorry`, 38 theorems and 38 `#print axioms` reports, all
`[propext, Classical.choice, Quot.sound]`. No docstring line begins with the words axiom or constant. Drafts
`BackgroundTransmissionParity-check1..14.log`. Author review only; root independent audit pending.

## Result (exact)

`pairs q σ n` is `n` copies of a high segment (width `π/(2q)`, index `q`, permittivity `σ`) and a low segment
(width `π/2`); `width (pairs q σ n) = n (π/(2q) + π/2)` (`width_pairs`). `te q = pairs q 1`, `tm q = pairs q (q^2)`.
`limitingTransmission l gs = 2 I / (phase l * exp (I * width gs) * (limitingCoefficients l gs).2)`.

1. Second limiting coefficient (`second_even`, `second_odd`), from the frozen `backward_reference_pairs`:
   `(limitingCoefficients (2j) (pairs q σ n)).2 = -((-1)^j (-σ/q)^n)`,
   `(limitingCoefficients (2j+1) (pairs q σ n)).2 = (-1)^(j+1) (-q/σ)^n * I`.
2. The factor `phase l = (-I)^(l+1)` cancels exactly against the sign `(-1)^j` (resp. `(-1)^(j+1)`) in these values
   (`phase (2j) * c2 = I (-σ/q)^n`, `phase (2j+1) * c2 = I (-q/σ)^n`), hence (`limT_even`, `limT_odd`)
   `limitingTransmission (2j) (pairs q σ n) / 2 = (-q/σ)^n * exp (-I * width)`,
   `limitingTransmission (2j+1) (pairs q σ n) / 2 = (-σ/q)^n * exp (-I * width)`.
3. With `parityPhase q n := (-1)^n * exp (-(I * (n (π/(2q) + π/2))))`:
   * `limitingTransmission_even : Even l -> limitingTransmission l (te q hq n) / 2 = (q^n : ℂ) * parityPhase q n`,
   * `limitingTransmission_odd : ¬Even l -> ... = ((q^n)⁻¹ : ℂ) * parityPhase q n`,
   * TM family: `limitingTransmission_tm_even = (q^n)⁻¹ * parityPhase q n`, `limitingTransmission_tm_odd = q^n * parityPhase q n`,
   * `te_even_norm`, `te_odd_norm`: moduli `q^n` and `(q^n)⁻¹`, `parityPhase_norm : ‖parityPhase q n‖ = 1`.
   So the unimodular factor `c_l = parityPhase q n` is INDEPENDENT of `l` and of the parity of `l` (and of TE versus TM);
   the gain is `q^n` (TE even), `q^(-n)` (TE odd).
4. `parityPhase_eq : q ≠ 0 -> parityPhase q n = exp (I * (n π (q-1)/(2q)))`. It depends on BOTH `n` and `q`, and not
   through a power of `i`: it is `1` for `q = 1`, `exp (i n π/4)` for `q = 2`, `exp (i n π/3)` for `q = 3`, `-> i^n` only as
   `q -> ∞`. `parityPhase_succ : parityPhase q (n+1) = parityPhase q n * exp (I π (q-1)/(2q))` and
   `parityPhase_succ_ne : 1 < q -> parityPhase q (n+1) ≠ parityPhase q n` (the step `exp (I θ)`, `0 < θ < π/2`, is not `1`).
5. Consequences for `transInf q hq n l = limitingTransmission l (te q _ n) / 2`:
   * `transInf_even`, `transInf_odd`;
   * `scaledCoeff_even_twist` / `scaledCoeff_even_literal`: for `A` with `∀ k ∈ A.support, Even k.val.1`,
     `scaledCoeff A (transInf q hq n) = (q^n : ℂ) • parityTwist q n A`, where `parityTwist q n = phaseTwist (parityPhase q n)`
     is multiplication by the global phase, with `parityTwist_unitary : TwistUnitary (parityTwist q n)` and
     `parityTwist_power : physicalPower (parityTwist q n x) = physicalPower x`;
   * `scaledCoeff_odd` (odd support: gain `(q^n)⁻¹`), and for every `A` the exact parity splitting
     `scaledCoeff_parity : scaledCoeff A transInf = parityPhase q n • scaledCoeff A (fun l => if Even l then q^n else (q^n)⁻¹)`;
   * for EVERY `A : Vec` (the odd and degree-zero columns of the input vanish,
     `RestrictedTEEffectiveBand.column_zero`): `effective_scaledCoeff : effective (scaledCoeff A transInf) = (q^n * parityPhase q n) • effective A`,
     `input_scaledCoeff : input (scaledCoeff A transInf) = (q^n * parityPhase q n) • input A`,
     `physicalPower_scaledCoeff : physicalPower (scaledCoeff A transInf) = (q^n)^2 * physicalPower A`.

## What this means for the assembly hypothesis `htw`

`htw : ∀ q > 1, ∀ᶠ n, ∀ x, scaledCoeff x (transInf q hq.le n) = (q^n) • twist x` with ONE twist independent of `q` and `n`
cannot hold literally, for two independent reasons proved here:
(a) the global constant `parityPhase q n` depends on `n` (`parityPhase_succ_ne`) and on `q`; it is not a power of `i` and
cannot be absorbed into a fixed twist; (b) for `x` with odd-degree (or degree-zero) entries the literal vector identity
fails (gain `(q^n)⁻¹ = q^n * q^(-2n)` on those entries), although those entries have zero physical input.
What is true, with the unitary twist the multiplication by the global phase `c_n(q) = parityPhase q n`: the literal identity on even-supported vectors
(`scaledCoeff_even_twist`), and the identities modulo the null columns for all vectors (`effective_scaledCoeff`,
`input_scaledCoeff`). If the fields of the device depend on the vector only through its effective part (the TE incident field uses
`RestrictedTEIncoming.polynomial`, which vanishes for odd degrees, and constants have zero toroidal part; this dependence
is NOT checked in this module) and since the passage/bypass/flux functionals are quadratic in the pair `(E, H)` (invariant
under a common unimodular factor), the assembly can use the identity twist plus a phase `c_n(q)` that depends on `(q, n)`, or equivalently feed the actual device
with the input `c_n(q)⁻¹ x`: the family `A_k = twist⁻¹ B_k` then changes only by a global unimodular factor with `n`, the
spans `span A_k` do not change. A `htw` stated for the active (even) part and allowing a `(q, n)`-dependent global
unimodular phase in the twist is what is available; a fixed twist is not.

Conventions: `exp (I * width)` in `limitingTransmission` is the source of the `n`- and `q`-dependence
(`width = n π (1 + q)/(2q)`); `phase l = (-I)^(l+1)` drops out completely; the sign `(-1)^n` comes from
`(-σ/q)^n` (the high and low pair maps of `backward_reference_pair` have the factors `-σ/q` and `-q/σ`).
