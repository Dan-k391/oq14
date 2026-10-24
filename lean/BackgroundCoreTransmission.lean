import RadialPhaseLimit
import SourcePairedGeometry
import RestrictedTEDatumLinear

/-! Background lift to the core.  For a layered stack with actual source coefficients
`c = coefficients l gs R X hR` (`traverse (outgoing X) = c.1 * regularState + c.2 * irregularState` at `R`),
the real transfers commute with complex conjugation, so the incoming vacuum wave continues to
`conj c.1 * regularState + conj c.2 * irregularState`.  A combination of incoming and outgoing waves at
`X` therefore continues to the pure regular core state (`regular_transport`); the unit incoming wave plus
`reflection` times the outgoing wave continues to `transmission` times the regular state
(`background_transport`).  For a fixed physical stack the transmission converges along the shell radii
`2 pi (s+1)` (`transmission_limit`), and a finite harmonic coefficient vector rescaled degreewise by the
transmissions has a convergent TE datum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BackgroundCoreTransmission
open Complex Filter OQ14.RadialGreen OQ14.RadialStack OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit
  OQ14.HankelRealBasis OQ14.ModalAlgebra
open scoped Topology ComplexConjugate

/-! ### States and the real basis at the stack radius -/

def regularState (l : ℕ) (R : ℝ) : State := (((regular l R : ℝ) : ℂ),((regularD l R : ℝ) : ℂ))
def irregularState (l : ℕ) (R : ℝ) : State := (((irregular l R : ℝ) : ℂ),((irregularD l R : ℝ) : ℂ))
def conjState (s : State) : State := (conj s.1,conj s.2)
def incomingState (l : ℕ) (X : ℝ) : State := (xiMinus l (X : ℂ),xiMinusD l (X : ℂ))

theorem incomingState_eq (l : ℕ) (X : ℝ) : incomingState l X=conjState (outgoing l X) :=
  Prod.ext (xi_conj_real l X).symm (xiD_conj_real l X).symm

theorem act_add (m : RealTransfer) (s t : State) : act m (s+t)=act m s+act m t := by
  apply Prod.ext <;> simp only [act,Prod.fst_add,Prod.snd_add] <;> ring

theorem traverse_add (l : ℕ) (gs : List Layer) (s t : State) :
    traverse l gs (s+t)=traverse l gs s+traverse l gs t := by
  induction gs generalizing s t with
  | nil => rfl
  | cons g gs ih =>
    change traverse l gs (act _ (s+t))=traverse l gs (act _ s)+traverse l gs (act _ t)
    rw [act_add,ih]

theorem act_conj (m : RealTransfer) (s : State) : act m (conjState s)=conjState (act m s) := by
  apply Prod.ext <;> simp [act,conjState,map_add,map_mul,Complex.conj_ofReal]

theorem traverse_conj (l : ℕ) (gs : List Layer) (s : State) :
    traverse l gs (conjState s)=conjState (traverse l gs s) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    change traverse l gs (act _ (conjState s))=conjState (traverse l gs (act _ s))
    rw [act_conj,ih]

theorem act_fundamental (l : ℕ) (R : ℝ) (hR : R≠0) (s : State) :
    act (fundamental l R hR) s=s.1 • regularState l R+s.2 • irregularState l R := by
  apply Prod.ext <;> simp [act,fundamental,regularState,irregularState] <;> ring

/-! ### Continuation of the outgoing and incoming vacuum waves to the core -/

/-- The outgoing wave at `X` continues to `c.1 * regularState + c.2 * irregularState` at `R`. -/
theorem traverse_outgoing (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) :
    traverse l gs (outgoing l X)=
      (OQ14.RadialSource.coefficients l gs R X hR).1 • regularState l R+
        (OQ14.RadialSource.coefficients l gs R X hR).2 • irregularState l R := by
  rw [← OQ14.RadialSource.continuation l gs R X hR,act_fundamental]

/-- The incoming wave `conj (outgoing)` continues to the conjugate combination. -/
theorem traverse_incoming (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) :
    traverse l gs (incomingState l X)=
      conj (OQ14.RadialSource.coefficients l gs R X hR).1 • regularState l R+
        conj (OQ14.RadialSource.coefficients l gs R X hR).2 • irregularState l R := by
  rw [incomingState_eq,traverse_conj,← OQ14.RadialSource.continuation l gs R X hR,← act_conj,
    act_fundamental]
  rfl

/-- Wronskian identity of the actual source coefficients. -/
theorem coefficients_wronskian (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X) :
    (OQ14.RadialSource.coefficients l gs R X hR).2*conj (OQ14.RadialSource.coefficients l gs R X hR).1-
      conj (OQ14.RadialSource.coefficients l gs R X hR).2*(OQ14.RadialSource.coefficients l gs R X hR).1=
      2*I := by
  have h := OQ14.RadialSource.coefficients_load l gs R X hR hX
  simp only [imaginaryLoad] at h
  apply Complex.ext
  · simp [Complex.mul_re,Complex.mul_im]
  · simp only [Complex.sub_im,Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.mul_re] at h ⊢
    simp
    linarith

theorem transport_coeffs (c1 c2 : ℂ) (hW : c2*conj c1-conj c2*c1=2*I) :
    (-(conj c2)/(2*I))*c1+(c2/(2*I))*conj c1=1 ∧ (-(conj c2)/(2*I))*c2+(c2/(2*I))*conj c2=0 := by
  have h2I : (2*I : ℂ)≠0 := mul_ne_zero two_ne_zero I_ne_zero
  constructor
  · have e : (-(conj c2)/(2*I))*c1+(c2/(2*I))*conj c1=(c2*conj c1-conj c2*c1)/(2*I) := by ring
    rw [e,hW,div_self h2I]
  · field_simp
    ring

/-- **Regular transport.**  The combination `a * outgoing + b * incoming` at `X`, with
`a = -conj c.2/(2I)` and `b = c.2/(2I)`, continues to exactly the regular state at the stack radius. -/
theorem regular_transport (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X) :
    traverse l gs ((-(conj (OQ14.RadialSource.coefficients l gs R X hR).2)/(2*I)) • outgoing l X+
      ((OQ14.RadialSource.coefficients l gs R X hR).2/(2*I)) • incomingState l X)=regularState l R := by
  obtain ⟨hA,hB⟩ := transport_coeffs _ _ (coefficients_wronskian l gs R X hR hX)
  rw [traverse_add,traverse_smul,traverse_smul,traverse_outgoing,traverse_incoming]
  apply Prod.ext
  · simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    linear_combination (regularState l R).1*hA+(irregularState l R).1*hB
  · simp only [Prod.snd_add,Prod.smul_snd,smul_eq_mul]
    linear_combination (regularState l R).2*hA+(irregularState l R).2*hB

/-! ### Transmission and reflection -/

/-- Transmission of a unit incoming vacuum wave at `X` to the regular core state at `R`. -/
def transmission (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) : ℂ :=
  2*I/(OQ14.RadialSource.coefficients l gs R X hR).2

/-- Reflection coefficient (outgoing amplitude accompanying a unit incoming wave). -/
def reflection (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) : ℂ :=
  -(conj (OQ14.RadialSource.coefficients l gs R X hR).2)/(OQ14.RadialSource.coefficients l gs R X hR).2

theorem transmission_ne_zero (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X) :
    transmission l gs R X hR≠0 :=
  div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
    (OQ14.RadialSource.coefficients_second_ne_zero l gs R X hR hX)

/-- **Background transport.**  A unit incoming vacuum wave plus `reflection` times the outgoing wave at `X`
continues inward to `transmission` times the regular core state. -/
theorem background_transport (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X) :
    traverse l gs (incomingState l X+reflection l gs R X hR • outgoing l X)=
      transmission l gs R X hR • regularState l R := by
  have hc2 := OQ14.RadialSource.coefficients_second_ne_zero l gs R X hR hX
  have h2I : (2*I : ℂ)≠0 := mul_ne_zero two_ne_zero I_ne_zero
  have hs : incomingState l X+reflection l gs R X hR • outgoing l X=
      transmission l gs R X hR • ((-(conj (OQ14.RadialSource.coefficients l gs R X hR).2)/(2*I)) • outgoing l X+
        ((OQ14.RadialSource.coefficients l gs R X hR).2/(2*I)) • incomingState l X) := by
    simp only [smul_add,smul_smul,transmission,reflection]
    have e1 : 2*I/(OQ14.RadialSource.coefficients l gs R X hR).2*
        ((OQ14.RadialSource.coefficients l gs R X hR).2/(2*I))=1 := by
      field_simp
    have e2 : 2*I/(OQ14.RadialSource.coefficients l gs R X hR).2*
        (-(conj (OQ14.RadialSource.coefficients l gs R X hR).2)/(2*I))=
        -(conj (OQ14.RadialSource.coefficients l gs R X hR).2)/
          (OQ14.RadialSource.coefficients l gs R X hR).2 := by
      field_simp
      ring
    rw [e1,e2,one_smul,add_comm]
  rw [hs,traverse_smul,regular_transport l gs R X hR hX]

/-- Unit modulus of the reflection coefficient. -/
theorem reflection_normSq (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X) :
    Complex.normSq (reflection l gs R X hR)=1 := by
  have hc2 := OQ14.RadialSource.coefficients_second_ne_zero l gs R X hR hX
  have hn : 0<Complex.normSq (OQ14.RadialSource.coefficients l gs R X hR).2 :=
    Complex.normSq_pos.mpr hc2
  unfold reflection
  rw [map_div₀,Complex.normSq_neg,Complex.normSq_conj,div_self hn.ne']

/-- `|transmission|^2 = 4 * (-Im gamma)`. -/
theorem transmission_normSq (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X) :
    Complex.normSq (transmission l gs R X hR)=
      4*(-(OQ14.RadialSource.gamma l gs R X hR).im) := by
  have hc2 := OQ14.RadialSource.coefficients_second_ne_zero l gs R X hR hX
  have hn : 0<Complex.normSq (OQ14.RadialSource.coefficients l gs R X hR).2 :=
    Complex.normSq_pos.mpr hc2
  rw [OQ14.RadialSource.gamma_im l gs R X hR hX]
  unfold transmission
  rw [map_div₀]
  have h4 : Complex.normSq (2*I : ℂ)=4 := by
    simp [Complex.normSq_apply]
    norm_num
  rw [h4]
  field_simp

/-! ### The physical stack: limit along the shell radii `2 pi (s+1)` -/

theorem coefficients_factorization (l : ℕ) (gs : List Segment) (R : ℝ) (hR : 0<R) :
    OQ14.RadialSource.coefficients l (layers gs R hR) R (R+width gs) hR=
      (phase l*Complex.exp (I*((R+width gs : ℝ) : ℂ))) • normalizedCoefficients l gs R := by
  rw [OQ14.RadialSource.coefficients,outgoing_factorization,traverse_smul,act_smul]
  rw [normalizedCoefficients,shape_eq_act l R hR.ne',RadialBackwardLimit.retreat_is_traverse l gs R hR]

/-- Transmission of the stack `layers gs R` (outer radius `R + width gs`). -/
def stackTransmission (l : ℕ) (gs : List Segment) (R : ℝ) (hR : 0<R) : ℂ :=
  transmission l (layers gs R hR) R (R+width gs) hR

/-- At the shell radius `2 pi (n+1)` the phase `exp (I R) = 1`, so the un-normalized coefficient is the
fixed constant `phase l * exp (I * width)` times the normalized (convergent) coefficient. -/
theorem coefficients_radius (l : ℕ) (gs : List Segment) (n : ℕ) :
    OQ14.RadialSource.coefficients l (layers gs (radius n) (radius_pos n)) (radius n)
      (radius n+width gs) (radius_pos n)=
      (phase l*Complex.exp (I*(width gs : ℂ))) • normalizedCoefficients l gs (radius n) := by
  rw [coefficients_factorization]
  congr 2
  rw [Complex.ofReal_add,mul_add,Complex.exp_add,radius_exp,one_mul]

theorem stackTransmission_radius (l : ℕ) (gs : List Segment) (n : ℕ) :
    stackTransmission l gs (radius n) (radius_pos n)=
      2*I/(phase l*Complex.exp (I*(width gs : ℂ))*(normalizedCoefficients l gs (radius n)).2) := by
  unfold stackTransmission transmission
  rw [coefficients_radius]
  rfl

/-- The limiting transmission of the stack: `2 I / (phase l * exp (I * width) * c∞.2)` with
`c∞ = limitingCoefficients l gs`. -/
def limitingTransmission (l : ℕ) (gs : List Segment) : ℂ :=
  2*I/(phase l*Complex.exp (I*(width gs : ℂ))*(limitingCoefficients l gs).2)

theorem limiting_factor_ne_zero (l : ℕ) (gs : List Segment) :
    phase l*Complex.exp (I*(width gs : ℂ))*(limitingCoefficients l gs).2≠0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)) (Complex.exp_ne_zero _))
    (limiting_second_ne_zero l gs)

/-- **Transmission limit.**  Along the shell radii `2 pi (n+1)` the transmission of the fixed stack
converges to `limitingTransmission`. -/
theorem transmission_limit (l : ℕ) (gs : List Segment) :
    Tendsto (fun n : ℕ => stackTransmission l gs (radius n) (radius_pos n)) atTop
      (𝓝 (limitingTransmission l gs)) := by
  have h := (tendsto_const_nhds (x := phase l*Complex.exp (I*(width gs : ℂ)))).mul
    (normalizedCoefficients_limit l gs).snd_nhds
  have h2 := (tendsto_const_nhds (x := (2*I : ℂ))).div h (limiting_factor_ne_zero l gs)
  refine h2.congr (fun n => ?_)
  exact (stackTransmission_radius l gs n).symm

theorem limitingTransmission_normSq (l : ℕ) (gs : List Segment) :
    Complex.normSq (limitingTransmission l gs)=
      4/Complex.normSq (limitingCoefficients l gs).2 := by
  have hn : 0<Complex.normSq (limitingCoefficients l gs).2 :=
    Complex.normSq_pos.mpr (limiting_second_ne_zero l gs)
  have hp := phase_normSq l
  have he : Complex.normSq (Complex.exp (I*(width gs : ℂ)))=1 := by
    rw [Complex.normSq_eq_norm_sq,Complex.norm_exp]
    simp
  have h4 : Complex.normSq (2*I : ℂ)=4 := by
    simp [Complex.normSq_apply]
    norm_num
  unfold limitingTransmission
  rw [map_div₀,h4,map_mul,map_mul,hp,he]
  ring

/-- The transmission of the actual physical paired stack at shell index `s`. -/
def physicalTransmission (q : ℝ) (hq : 0<q) (n l s : ℕ) : ℂ :=
  transmission l (OQ14.SourcePairedGeometry.physicalData q hq n s).gs
    (OQ14.SourcePairedGeometry.physicalData q hq n s).R
    (OQ14.SourcePairedGeometry.physicalData q hq n s).X
    (OQ14.SourcePairedGeometry.physicalData q hq n s).hR

/-- Limiting transmission of the physical paired stack, of degree `l`. -/
def physicalLimit (q : ℝ) (hq : 0<q) (n l : ℕ) : ℂ :=
  limitingTransmission l (OQ14.RadialPairedFamily.tm q hq n)

theorem physicalTransmission_eq (q : ℝ) (hq : 0<q) (n l s : ℕ) :
    physicalTransmission q hq n l s=
      stackTransmission l (OQ14.RadialPairedFamily.tm q hq n) (radius s) (radius_pos s) := rfl

theorem physical_transmission_limit (q : ℝ) (hq : 0<q) (n l : ℕ) :
    Tendsto (fun s : ℕ => physicalTransmission q hq n l s) atTop (𝓝 (physicalLimit q hq n l)) :=
  transmission_limit l (OQ14.RadialPairedFamily.tm q hq n)

/-! ### Finite harmonic coefficient vectors rescaled degreewise -/

/-- The coefficient vector `q ↦ A q * t (degree q)` with the support of `A` (at most). -/
def scaledCoeff (A : SymmetricHarmonicJets.Index →₀ ℂ) (t : ℕ → ℂ) :
    SymmetricHarmonicJets.Index →₀ ℂ :=
  ∑ q ∈ A.support,Finsupp.single q (A q*t q.val.1)

theorem scaledCoeff_apply (A : SymmetricHarmonicJets.Index →₀ ℂ) (t : ℕ → ℂ)
    (q : SymmetricHarmonicJets.Index) : scaledCoeff A t q=A q*t q.val.1 := by
  classical
  unfold scaledCoeff
  rw [Finsupp.finset_sum_apply]
  by_cases hq : q∈A.support
  · rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply,hb]
    · intro h
      exact absurd hq h
  · have hA : A q=0 := Finsupp.not_mem_support_iff.mp hq
    rw [hA,zero_mul]
    apply Finset.sum_eq_zero
    intro b hb
    have hbq : b≠q := fun h => hq (h ▸ hb)
    simp [Finsupp.single_apply,hbq]

theorem scaledCoeff_support (A : SymmetricHarmonicJets.Index →₀ ℂ) (t : ℕ → ℂ) :
    (scaledCoeff A t).support ⊆ A.support := by
  intro q hq
  by_contra h
  have hA : A q=0 := Finsupp.not_mem_support_iff.mp h
  have := Finsupp.mem_support_iff.mp hq
  rw [scaledCoeff_apply,hA,zero_mul] at this
  exact this rfl

theorem map_scaledCoeff {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (L : (SymmetricHarmonicJets.Index →₀ ℂ) →ₗ[ℂ] E) (A : SymmetricHarmonicJets.Index →₀ ℂ)
    (t : ℕ → ℂ) :
    L (scaledCoeff A t)=∑ q ∈ A.support,(A q*t q.val.1) • L (Finsupp.single q 1) := by
  unfold scaledCoeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finsupp.smul_single_one q (A q*t q.val.1),map_smul]

/-- A linear function of the finite coefficient vector, rescaled by degreewise factors that converge,
converges. -/
theorem tendsto_scaledCoeff {α E : Type*} [AddCommMonoid E] [Module ℂ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℂ E]
    (L : (SymmetricHarmonicJets.Index →₀ ℂ) →ₗ[ℂ] E) (A : SymmetricHarmonicJets.Index →₀ ℂ)
    {F : Filter α} (t : α → ℕ → ℂ) (t0 : ℕ → ℂ)
    (ht : ∀ l, Tendsto (fun a => t a l) F (𝓝 (t0 l))) :
    Tendsto (fun a => L (scaledCoeff A (t a))) F (𝓝 (L (scaledCoeff A t0))) := by
  simp only [map_scaledCoeff]
  exact tendsto_finset_sum _ (fun q _ =>
    ((tendsto_const_nhds.mul (ht q.val.1)).smul_const (L (Finsupp.single q 1))))

/-- The TE datum of the rescaled coefficient vector converges in `VectorL2`. -/
theorem datum_scaledCoeff_tendsto {α : Type*} (c : OQ14.StaticCoefficient.Coefficient)
    (d : OQ14.BoundedMaterialKernel.SupportData c) (A : SymmetricHarmonicJets.Index →₀ ℂ)
    {F : Filter α} (t : α → ℕ → ℂ) (t0 : ℕ → ℂ)
    (ht : ∀ l, Tendsto (fun a => t a l) F (𝓝 (t0 l))) :
    Tendsto (fun a => OQ14.RestrictedTEMaterial.datum c d (scaledCoeff A (t a))) F
      (𝓝 (OQ14.RestrictedTEMaterial.datum c d (scaledCoeff A t0))) :=
  tendsto_scaledCoeff (OQ14.RestrictedTEDatumLinear.datumMap c d) A t t0 ht

/-- The regular TE electric field of the rescaled coefficient vector converges pointwise. -/
theorem electric_scaledCoeff_tendsto {α : Type*} (A : SymmetricHarmonicJets.Index →₀ ℂ)
    {F : Filter α} (t : α → ℕ → ℂ) (t0 : ℕ → ℂ)
    (ht : ∀ l, Tendsto (fun a => t a l) F (𝓝 (t0 l))) :
    Tendsto (fun a => OQ14.RestrictedTEPlaneLocal.electric (scaledCoeff A (t a))) F
      (𝓝 (OQ14.RestrictedTEPlaneLocal.electric (scaledCoeff A t0))) := by
  have h := tendsto_scaledCoeff OQ14.RestrictedTEFieldLinear.electricMap A t t0 ht
  simpa only [OQ14.RestrictedTEFieldLinear.electricMap_apply] using h

/-- **Background datum limit for the physical paired stacks.**  With the degreewise transmissions of the
physical stack at shell index `s`, the TE datum of the rescaled finite coefficient vector converges to the
datum of the vector rescaled by the limiting transmissions. -/
theorem background_datum_tendsto (q : ℝ) (hq : 0<q) (n : ℕ)
    (c : OQ14.StaticCoefficient.Coefficient) (d : OQ14.BoundedMaterialKernel.SupportData c)
    (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    Tendsto (fun s : ℕ => OQ14.RestrictedTEMaterial.datum c d
        (scaledCoeff A (fun l => physicalTransmission q hq n l s))) atTop
      (𝓝 (OQ14.RestrictedTEMaterial.datum c d (scaledCoeff A (fun l => physicalLimit q hq n l)))) :=
  datum_scaledCoeff_tendsto c d A (fun s l => physicalTransmission q hq n l s)
    (fun l => physicalLimit q hq n l) (fun l => physical_transmission_limit q hq n l)


/-! ### The layered background state

Core: `transmission * regularState`; stack: the glued profile of the exterior combination at `X`;
beyond `X`: `incoming + reflection * outgoing`.  It equals `-conj c.2` times the difference of the actual
source state and its conjugate (`backgroundState_eq`), hence inherits its continuity. -/

section BackgroundState
open OQ14.RadialGluing

theorem conjState_smul (c : ℂ) (s : State) : conjState (c • s)=conj c • conjState s := by
  apply Prod.ext <;> simp [conjState,map_mul]

theorem conjState_sub (s t : State) : conjState (s-t)=conjState s-conjState t := by
  apply Prod.ext <;> simp [conjState,map_sub]

theorem wave_conj (l : ℕ) (g : Layer) (s : State) (x : ℝ) :
    wave l g (conjState s) x=conj (wave l g s x) ∧
      waveMomentum l g (conjState s) x=conj (waveMomentum l g s x) := by
  constructor <;>
  simp [wave,waveMomentum,OQ14.RadialLayer.value,OQ14.RadialLayer.momentum,
    OQ14.RadialLayer.initialAlpha,OQ14.RadialLayer.initialBeta,conjState,map_add,map_mul,map_sub,
    map_neg,Complex.conj_ofReal]

theorem wave_add (l : ℕ) (g : Layer) (s t : State) (x : ℝ) :
    wave l g (s+t) x=wave l g s x+wave l g t x ∧
      waveMomentum l g (s+t) x=waveMomentum l g s x+waveMomentum l g t x := by
  constructor <;>
  simp [wave,waveMomentum,OQ14.RadialLayer.value,OQ14.RadialLayer.momentum,
    OQ14.RadialLayer.initialAlpha,OQ14.RadialLayer.initialBeta] <;> ring

theorem wave_smul (l : ℕ) (g : Layer) (c : ℂ) (s : State) (x : ℝ) :
    wave l g (c • s) x=c*wave l g s x ∧ waveMomentum l g (c • s) x=c*waveMomentum l g s x := by
  constructor <;>
  simp [wave,waveMomentum,OQ14.RadialLayer.value,OQ14.RadialLayer.momentum,
    OQ14.RadialLayer.initialAlpha,OQ14.RadialLayer.initialBeta] <;> ring

theorem profile_conj (l : ℕ) (gs : List Layer) (s : State) (x : ℝ) :
    profile l gs (conjState s) x=conjState (profile l gs s x) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [profile]
    split_ifs
    · exact Prod.ext (wave_conj l g s x).1 (wave_conj l g s x).2
    · have h : back l g (conjState s)=conjState (back l g s) := act_conj _ _
      rw [h,ih]

theorem profile_add (l : ℕ) (gs : List Layer) (s t : State) (x : ℝ) :
    profile l gs (s+t) x=profile l gs s x+profile l gs t x := by
  induction gs generalizing s t with
  | nil => rfl
  | cons g gs ih =>
    simp only [profile]
    split_ifs
    · exact Prod.ext (wave_add l g s t x).1 (wave_add l g s t x).2
    · have h : back l g (s+t)=back l g s+back l g t := act_add _ _ _
      rw [h,ih]

theorem profile_smul (l : ℕ) (gs : List Layer) (c : ℂ) (s : State) (x : ℝ) :
    profile l gs (c • s) x=c • profile l gs s x := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [profile]
    split_ifs
    · exact Prod.ext (wave_smul l g c s x).1 (wave_smul l g c s x).2
    · have h : back l g (c • s)=c • back l g s := act_smul _ _ _
      rw [h,ih]

theorem incoming_add_outgoing (l : ℕ) (x : ℝ) :
    incomingState l x+outgoing l x=(2 : ℂ) • regularState l x := by
  apply Prod.ext
  · simp only [incomingState,outgoing,regularState,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    rw [← xi_conj_real,add_comm,Complex.add_conj]
    simp [regular]
  · simp only [incomingState,outgoing,regularState,Prod.snd_add,Prod.smul_snd,smul_eq_mul]
    rw [← xiD_conj_real,add_comm,Complex.add_conj]
    simp [regularD]

/-- The layered background state. -/
def backgroundState (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (x : ℝ) : State :=
  if x ≤ R then transmission l gs R X hR • regularState l x
  else if x ≤ X then profile l gs (incomingState l X+reflection l gs R X hR • outgoing l X) x
  else incomingState l x+reflection l gs R X hR • outgoing l x

theorem backgroundState_core (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (x : ℝ) (hx : x ≤ R) :
    backgroundState l gs R X hR x=transmission l gs R X hR • regularState l x := if_pos hx

theorem backgroundState_stack (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (x : ℝ)
    (h1 : R<x) (h2 : x ≤ X) :
    backgroundState l gs R X hR x=
      profile l gs (incomingState l X+reflection l gs R X hR • outgoing l X) x := by
  unfold backgroundState
  rw [if_neg (not_le.mpr h1),if_pos h2]

theorem backgroundState_exterior (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hRX : R ≤ X)
    (x : ℝ) (hx : X<x) :
    backgroundState l gs R X hR x=incomingState l x+reflection l gs R X hR • outgoing l x := by
  unfold backgroundState
  rw [if_neg (not_le.mpr (hRX.trans_lt hx)),if_neg (not_le.mpr hx)]

/-- In the exterior the background is `2 * regular` (the regular incident wave of amplitude two) plus
`reflection - 1` times the outgoing wave. -/
theorem backgroundState_exterior_decomposition (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R)
    (hRX : R ≤ X) (x : ℝ) (hx : X<x) :
    backgroundState l gs R X hR x=
      (2 : ℂ) • regularState l x+(reflection l gs R X hR-1) • outgoing l x := by
  rw [backgroundState_exterior l gs R X hR hRX x hx,sub_smul,one_smul,← incoming_add_outgoing]
  abel

theorem kappa_gamma (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X) :
    -(conj (OQ14.RadialSource.coefficients l gs R X hR).2)*
      (OQ14.RadialSource.gamma l gs R X hR-conj (OQ14.RadialSource.gamma l gs R X hR))=
      transmission l gs R X hR := by
  have hc2 := OQ14.RadialSource.coefficients_second_ne_zero l gs R X hR hX
  have hc2c : conj (OQ14.RadialSource.coefficients l gs R X hR).2≠0 := (map_ne_zero _).mpr hc2
  have hW := coefficients_wronskian l gs R X hR hX
  unfold OQ14.RadialSource.gamma transmission
  rw [map_div₀]
  have h : -(conj (OQ14.RadialSource.coefficients l gs R X hR).2)*
      ((OQ14.RadialSource.coefficients l gs R X hR).1/(OQ14.RadialSource.coefficients l gs R X hR).2-
        conj (OQ14.RadialSource.coefficients l gs R X hR).1/
          conj (OQ14.RadialSource.coefficients l gs R X hR).2)=
      ((OQ14.RadialSource.coefficients l gs R X hR).2*conj (OQ14.RadialSource.coefficients l gs R X hR).1-
        conj (OQ14.RadialSource.coefficients l gs R X hR).2*
          (OQ14.RadialSource.coefficients l gs R X hR).1)/
        (OQ14.RadialSource.coefficients l gs R X hR).2 := by
    field_simp
    ring
  rw [h,hW]

/-- **The background state is `-conj c.2` times the source state minus its conjugate.** -/
theorem backgroundState_eq (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X) (hRX : R ≤ X)
    (x : ℝ) :
    backgroundState l gs R X hR x=
      (-(conj (OQ14.RadialSource.coefficients l gs R X hR).2)) •
        (sourceState l gs R X hR x-conjState (sourceState l gs R X hR x)) := by
  have hc2 := OQ14.RadialSource.coefficients_second_ne_zero l gs R X hR hX
  have hc2c : conj (OQ14.RadialSource.coefficients l gs R X hR).2≠0 := (map_ne_zero _).mpr hc2
  have e1 : -(conj (OQ14.RadialSource.coefficients l gs R X hR).2)*
      ((OQ14.RadialSource.coefficients l gs R X hR).2)⁻¹=reflection l gs R X hR := by
    unfold reflection
    rw [div_eq_mul_inv,neg_mul]
  have e2 : -(conj (OQ14.RadialSource.coefficients l gs R X hR).2)*
      (conj (OQ14.RadialSource.coefficients l gs R X hR).2)⁻¹=-1 := by
    rw [neg_mul,mul_inv_cancel₀ hc2c]
  have hk := kappa_gamma l gs R X hR hX
  by_cases h1 : x ≤ R
  · rw [backgroundState_core l gs R X hR x h1,sourceState_core l gs R X hR x h1]
    apply Prod.ext
    · simp only [Prod.smul_fst,Prod.fst_sub,smul_eq_mul,conjState,regularState,OQ14.RadialSource.coreWave,map_add,
        map_mul,Complex.conj_ofReal]
      linear_combination (-(regular l x : ℂ))*hk
    · simp only [Prod.smul_snd,Prod.snd_sub,smul_eq_mul,conjState,regularState,OQ14.RadialSource.coreWaveD,map_add,
        map_mul,Complex.conj_ofReal]
      linear_combination (-(regularD l x : ℂ))*hk
  · have hs : sourceState l gs R X hR x=
        ((OQ14.RadialSource.coefficients l gs R X hR).2)⁻¹ • outerMatched l gs X x := by
      unfold sourceState; rw [if_neg h1]
    rw [hs,conjState_smul,map_inv₀]
    by_cases h2 : x ≤ X
    · rw [backgroundState_stack l gs R X hR x (not_le.mp h1) h2]
      have ho : outerMatched l gs X x=profile l gs (outgoing l X) x := by
        unfold outerMatched; rw [if_pos h2]
      rw [ho,← profile_conj,← incomingState_eq,profile_add,profile_smul]
      rw [smul_sub,smul_smul,smul_smul,e1,e2,neg_smul,one_smul,sub_neg_eq_add,add_comm]
    · have hx2 : X<x := not_le.mp h2
      rw [backgroundState_exterior l gs R X hR hRX x hx2]
      have ho : outerMatched l gs X x=outgoing l x := by
        unfold outerMatched; rw [if_neg h2]
      rw [ho,← incomingState_eq]
      rw [smul_sub,smul_smul,smul_smul,e1,e2,neg_smul,one_smul,sub_neg_eq_add,add_comm]

theorem backgroundState_continuousOn (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (hR : 0<R) : ContinuousOn (backgroundState l gs R X hR) (Set.Ioi 0) := by
  have hRX := chain_ordered h
  have hX : 0<X := hR.trans_le hRX
  have hS := sourceState_continuousOn l h hR
  have hC : Continuous conjState :=
    (Complex.continuous_conj.comp continuous_fst).prodMk (Complex.continuous_conj.comp continuous_snd)
  refine ((hS.sub (hC.comp_continuousOn hS)).const_smul
    (-(conj (OQ14.RadialSource.coefficients l gs R X hR).2))).congr (fun x _ => ?_)
  exact backgroundState_eq l gs R X hR hX hRX x

end BackgroundState

end OQ14.BackgroundCoreTransmission
#print axioms OQ14.BackgroundCoreTransmission.incomingState_eq
#print axioms OQ14.BackgroundCoreTransmission.act_add
#print axioms OQ14.BackgroundCoreTransmission.traverse_add
#print axioms OQ14.BackgroundCoreTransmission.act_conj
#print axioms OQ14.BackgroundCoreTransmission.traverse_conj
#print axioms OQ14.BackgroundCoreTransmission.act_fundamental
#print axioms OQ14.BackgroundCoreTransmission.traverse_outgoing
#print axioms OQ14.BackgroundCoreTransmission.traverse_incoming
#print axioms OQ14.BackgroundCoreTransmission.coefficients_wronskian
#print axioms OQ14.BackgroundCoreTransmission.transport_coeffs
#print axioms OQ14.BackgroundCoreTransmission.regular_transport
#print axioms OQ14.BackgroundCoreTransmission.transmission_ne_zero
#print axioms OQ14.BackgroundCoreTransmission.background_transport
#print axioms OQ14.BackgroundCoreTransmission.reflection_normSq
#print axioms OQ14.BackgroundCoreTransmission.transmission_normSq
#print axioms OQ14.BackgroundCoreTransmission.coefficients_factorization
#print axioms OQ14.BackgroundCoreTransmission.coefficients_radius
#print axioms OQ14.BackgroundCoreTransmission.stackTransmission_radius
#print axioms OQ14.BackgroundCoreTransmission.limiting_factor_ne_zero
#print axioms OQ14.BackgroundCoreTransmission.transmission_limit
#print axioms OQ14.BackgroundCoreTransmission.limitingTransmission_normSq
#print axioms OQ14.BackgroundCoreTransmission.physicalTransmission_eq
#print axioms OQ14.BackgroundCoreTransmission.physical_transmission_limit
#print axioms OQ14.BackgroundCoreTransmission.scaledCoeff_apply
#print axioms OQ14.BackgroundCoreTransmission.scaledCoeff_support
#print axioms OQ14.BackgroundCoreTransmission.map_scaledCoeff
#print axioms OQ14.BackgroundCoreTransmission.tendsto_scaledCoeff
#print axioms OQ14.BackgroundCoreTransmission.datum_scaledCoeff_tendsto
#print axioms OQ14.BackgroundCoreTransmission.electric_scaledCoeff_tendsto
#print axioms OQ14.BackgroundCoreTransmission.background_datum_tendsto
#print axioms OQ14.BackgroundCoreTransmission.conjState_smul
#print axioms OQ14.BackgroundCoreTransmission.conjState_sub
#print axioms OQ14.BackgroundCoreTransmission.wave_conj
#print axioms OQ14.BackgroundCoreTransmission.wave_add
#print axioms OQ14.BackgroundCoreTransmission.wave_smul
#print axioms OQ14.BackgroundCoreTransmission.profile_conj
#print axioms OQ14.BackgroundCoreTransmission.profile_add
#print axioms OQ14.BackgroundCoreTransmission.profile_smul
#print axioms OQ14.BackgroundCoreTransmission.incoming_add_outgoing
#print axioms OQ14.BackgroundCoreTransmission.backgroundState_core
#print axioms OQ14.BackgroundCoreTransmission.backgroundState_stack
#print axioms OQ14.BackgroundCoreTransmission.backgroundState_exterior
#print axioms OQ14.BackgroundCoreTransmission.backgroundState_exterior_decomposition
#print axioms OQ14.BackgroundCoreTransmission.kappa_gamma
#print axioms OQ14.BackgroundCoreTransmission.backgroundState_eq
#print axioms OQ14.BackgroundCoreTransmission.backgroundState_continuousOn
