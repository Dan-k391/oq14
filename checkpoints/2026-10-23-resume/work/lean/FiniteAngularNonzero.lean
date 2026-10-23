import FiniteAngularHerglotz

/-! Nonzero finite angular approximants with literal uniform electric control. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.FiniteAngularNonzero
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereHarmonicBasis
open scoped ComplexInnerProductSpace Topology
abbrev Space := Maxwell.Space
abbrev Sphere := AngularPower.Sphere
abbrev ModeIndex := ComplexTransverseExpansion.ModeIndex

theorem modeIndex_nonempty : Nonempty ModeIndex := by
  classical
  let F := TransversePlaneFields.field 0 0 0
  have hF : F≠0 := by
    intro hz
    have he : TransversePlaneFields.plane 0 0 0=0 :=
      ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) angularMeasure (by simpa only [map_zero] using hz)
    let n : Sphere := ⟨EuclideanSpace.single 1 (1 : ℝ),by simp [Metric.mem_sphere]⟩
    have hp := congrArg (fun f : C(Sphere,ComplexVectorSphere.Vector) => f n 0) he
    norm_num [TransversePlaneFields.plane,TransversePlaneFields.projected,TransversePlaneFields.unit,
      SphereReactionKernel.wave,TransversePlaneFields.normal,ComplexVectorSphere.embed_apply,n,
      EuclideanSpace.single_apply] at hp
  by_contra hn
  haveI : IsEmpty ModeIndex := not_nonempty_iff.mp hn
  have he := ComplexTransverseExpansion.expansion F (TransversePlaneFields.field_tangent 0 0 0)
  apply hF
  exact he.unique (by
    convert (hasSum_zero : HasSum (fun _ : ModeIndex => (0 : ComplexVectorSphere.Ambient)) 0) using 1
    )

theorem electric_zero (k : ℝ) (x : Space) (i : Fin 3) :
    (FiniteAngularHerglotz.incident k 0).E x i=0 := by
  rw [FiniteAngularHerglotz.electric_value]
  simp [HerglotzAngularL2.finiteAmplitude]

theorem single_bound (k : ℝ) (m : ModeIndex) (z : ℂ) (x : Space) (i : Fin 3) :
    ‖(FiniteAngularHerglotz.incident k (Finsupp.single m z)).E x i‖ ≤ HerglotzAngularL2.bound*‖z‖ := by
  rw [FiniteAngularHerglotz.electric_value]
  have h := HerglotzAngularL2.value_norm_le k x i (HerglotzAngularL2.finiteAmplitude (Finsupp.single m z))
  simpa only [HerglotzAngularL2.finiteAmplitude,Finsupp.sum_single_index,
    zero_smul,norm_smul,ComplexTransverseExpansion.vector_orthonormal.norm_eq_one,mul_one] using h

theorem uniform_plane_approximation (k R : ℝ) (c : ConicalRungeClosure.WaveIndex →₀ ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ModeIndex →₀ ℂ, d≠0 ∧ ∀ x ∈ closedBall (0 : Space) R, ∀ i : Fin 3,
      ‖(FiniteAngularHerglotz.incident k d).E x i-ConicalFinitePlanes.electric k c x i‖ < ε := by
  classical
  obtain ⟨d,hd⟩ := FiniteAngularHerglotz.uniform_plane_approximation k R c (ε/2) (by positivity)
  by_cases hdz : d=0
  · let m : ModeIndex := Classical.choice modeIndex_nonempty
    let z : ℝ := ε/(4*(HerglotzAngularL2.bound+1))
    have hB : 0 ≤ HerglotzAngularL2.bound := HerglotzAngularL2.bound_nonnegative
    have hz : 0 < z := div_pos hε (by positivity)
    refine ⟨Finsupp.single m (z : ℂ),Finsupp.single_ne_zero.mpr (by exact_mod_cast hz.ne'),?_⟩
    intro x hx i
    have he := hd x hx i
    rw [hdz,electric_zero,zero_sub,norm_neg] at he
    have hs := single_bound k m (z : ℂ) x i
    have hzn : ‖(z : ℂ)‖=z := by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz]
    rw [hzn] at hs
    have hsmall : HerglotzAngularL2.bound*z < ε/2 := by
      dsimp only [z]
      rw [←mul_div_assoc,div_lt_iff₀ (by positivity : 0 < 4*(HerglotzAngularL2.bound+1))]
      nlinarith
    exact (norm_sub_le _ _).trans_lt (add_lt_add (hs.trans_lt hsmall) he |>.trans_eq (by ring))
  · exact ⟨d,hdz,fun x hx i => (hd x hx i).trans (by linarith)⟩

end OQ14.FiniteAngularNonzero
#print axioms OQ14.FiniteAngularNonzero.modeIndex_nonempty
#print axioms OQ14.FiniteAngularNonzero.electric_zero
#print axioms OQ14.FiniteAngularNonzero.single_bound
#print axioms OQ14.FiniteAngularNonzero.uniform_plane_approximation
