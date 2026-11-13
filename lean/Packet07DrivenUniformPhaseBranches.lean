import Packet05RegionalPhysicalBranches
import Packet07DrivenUniformHostGraph
import Packet07DrivenUniformOriented

/-! The actual complex volume-kernel mode has two continuous physical phase
branches on a constant-host graph chart, with all scalar regularity derived. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet07DrivenUniformPhaseBranches
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.ConicalGradientGraph OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalPhysicalBranches OQ14.Packet05ActualHostModeGraph
  OQ14.Packet05ChartBasis OQ14.Packet05ChartWeakGradient OQ14.Packet05ChartWeakDivergence
  OQ14.Packet05GraphPullback OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap
  OQ14.Packet05FlatWeight OQ14.Packet05ScalarDielectricFlux
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane
abbrev Space := Maxwell.Space

theorem actual_driven_phase_branches
    {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {contrast threshold : ℝ}
    (setup : Packet07PlanarSetup.Setup N Pset contrast threshold) (k : ℝ) (hk0 : k ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius contrast setup.enclosing) (j0 : ℕ)
    (body : Set Space) (host : ℂ) (hhost : host ≠ 0) (d : ℝ) (hd : 0 ≤ d)
    (outer : ContDiffBump (0 : Space)) (up : Bool) (axis : Fin 3)
    (g : Plane → ℝ) (hg3 : ContDiff ℝ 3 g) (hg : ContDiff ℝ 2 g)
    (Vchart Wgraph : Set Space)
    (hmapV : ∀ x ∈ Vchart, inverseOriented up axis x ∈ ball (0 : Space) outer.rIn)
    (hmapW : ∀ x ∈ Wgraph, graphMap (liftedHeight g) x ∈ Vchart)
    (hside : ∀ x ∈ Wgraph, inverseOriented up axis (graphMap (liftedHeight g) x) ∈ body ↔ 0 < x 2)
    (hmaterial : ∀ x ∈ Wgraph, Packet06MaxwellScalarEquation.epsilon (setup.rounded j0)
      (inverseOriented up axis (graphMap (liftedHeight g) x)) =
        host * (by classical exact if inverseOriented up axis (graphMap (liftedHeight g) x) ∈ body
          then (1+d : ℂ) else 1))
    (B3 : Fin 3 → ℝ) (hB3 : ∀ j x, ‖slopeC g j x‖ ≤ B3 j)
    (hdi : ∀ j k, MemLp (fun x => dcoord (slopeC g j) x k) ⊤ volume)
    (hdd : ∀ j k l, MemLp (fun x => dcoord (fun y => dcoord (slopeC g j) y k) x l) ⊤ volume)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (hAgraph : ∀ x ∈ Wgraph, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (Ω S₀ V S : Set Space) (hΩW : Ω ⊆ Wgraph)
    (θ : Test) (hθΩ : tsupport θ.function ⊆ Ω)
    (hθS : ∀ x ∈ S₀, θ.function =ᶠ[nhds x] (fun _ => (1 : ℂ)))
    (τ : RealTest Set.univ) (hτV : ∀ x ∈ V, τ.function x = 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hτS : ∀ t, t ≠ 2 → ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport τ.function,
      x ∈ S₀ ∧ x+h • basis t ∈ S₀)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ l x, ‖slopeC g l.castSucc x‖ ≤ B l)
    (hmetric : ∀ x ∈ tsupport τ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (a τa τb : ℝ) (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hτa : ∀ x, ‖τ.complexTest.function x‖ ≤ τa)
    (hτb : ∀ j x, ‖dcoord τ.complexTest.function x j‖ ≤ τb)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκ3 : ContDiff ℝ 3 κ.function)
    (hκΩ : tsupport κ.function ⊆ Ω) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[nhds x] (fun _ => (1 : ℝ)))
    (V₁ S₁ W₁ V₂ U₂ T : Set Space) (hV₁ : IsOpen V₁) (hW₁ : IsOpen W₁)
    (hW₁V₁ : W₁ ⊆ V₁) (hV₁S : V₁ ⊆ S) (hU₂ : IsOpen U₂) (hT : IsOpen T)
    (hV₂W₁ : V₂ ⊆ W₁) (hU₂V₂ : U₂ ⊆ V₂) (hTU₂ : T ⊆ U₂) (hTS : T ⊆ S)
    (τ₁ : RealTest Set.univ) (hτ₁2 : ContDiff ℝ 2 τ₁.function) (hτ₁V : ∀ x ∈ V₁, τ₁.function x = 1)
    (δ₁ : ℝ) (hδ₁ : 0 < δ₁)
    (hτ₁S0 : ∀ h : ℝ, |h| < δ₁ → ∀ x ∈ tsupport τ₁.function, x ∈ S ∧ x+h • basis 0 ∈ S)
    (hτ₁S1 : ∀ h : ℝ, |h| < δ₁ → ∀ x ∈ tsupport τ₁.function, x ∈ S ∧ x+h • basis 1 ∈ S)
    (κ₁ : RealTest Set.univ) (hκ₁2 : ContDiff ℝ 2 κ₁.function) (hκ₁V : tsupport κ₁.function ⊆ V₁)
    (hκ₁S : ∀ x ∈ S₁, κ₁.function =ᶠ[nhds x] (fun _ => (1 : ℝ)))
    (ζ₁ : RealTest Set.univ) (δ₂ : ℝ) (hδ₂ : 0 < δ₂)
    (hζ₁S0 : ∀ h : ℝ, |h| < δ₂ → ∀ x ∈ tsupport ζ₁.function, x ∈ S₁ ∧ x+h • basis 0 ∈ S₁)
    (hζ₁S1 : ∀ h : ℝ, |h| < δ₂ → ∀ x ∈ tsupport ζ₁.function, x ∈ S₁ ∧ x+h • basis 1 ∈ S₁)
    (hκ₁W : ∀ x ∈ W₁, κ₁.function x = 1) (hζ₁W : ∀ x ∈ W₁, ζ₁.function x = 1)
    (hmetricτ₁ : ∀ x ∈ tsupport τ₁.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (hmetricζ₁ : ∀ x ∈ tsupport ζ₁.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (τa₁ τb₁ ηa₁ ηb₁ : ℝ) (hτa₁ : ∀ x, ‖τ₁.complexTest.function x‖ ≤ τa₁)
    (hτb₁ : ∀ j x, ‖dcoord τ₁.complexTest.function x j‖ ≤ τb₁)
    (hηa₁ : ∀ x, ‖ζ₁.complexTest.function x‖ ≤ ηa₁)
    (hηb₁ : ∀ j x, ‖dcoord ζ₁.complexTest.function x j‖ ≤ ηb₁)
    (θ₁ η₁ χ₁ : Test) (hθ₁2 : ContDiff ℝ 2 θ₁.function) (hθ₁W : tsupport θ₁.function ⊆ W₁)
    (hθ₁V : ∀ x ∈ V₂, θ₁.function x = 1)
    (hη₁V : tsupport η₁.function ⊆ V₂) (hη₁U : ∀ x ∈ U₂, η₁.function x = 1)
    (hχ₁U : tsupport χ₁.function ⊆ U₂) (hχ₁2 : ContDiff ℝ 2 χ₁.function)
    (hχ₁T : ∀ x ∈ T, χ₁.function x = 1)
    (hTW : T ⊆ Wgraph) :
    let E := setup.electric k j0 input
    ∃ lower upper : Fin 3 → Space → ℂ,
      (∀ j, Continuous (lower j)) ∧ (∀ j, Continuous (upper j)) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict
        (OQ14.Packet05PhysicalChartBranches.physicalFlatMap up axis g ⁻¹' (T ∩ {x | x 2 < 0}))] lower j) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict
        (OQ14.Packet05PhysicalChartBranches.physicalFlatMap up axis g ⁻¹' (T ∩ {x | 0 < x 2}))] upper j) := by
  dsimp only
  let c := setup.rounded j0
  let mode := Packet07SelectedRadiation.actualUnknown setup k j0 input
  let hc := ConicalCommonBinaryPeaks.support setup.dataFamily setup.radii setup.centers contrast setup.contrast_pos.le
    setup.contrast_bound setup.radii_outer setup.outer_sep setup.radii_pos setup.enclosing setup.outer_enclosed j0
  let U := Packet06ComplexConePotential.potentialData (k : ℂ) setup.enclosing (StaticCoefficient.sqrtMultiplier c mode)
    (DynamicVolume.source c mode) (DynamicVolume.source_zero c mode setup.enclosing hc) (StaticNewton.material_source_ae c mode)
  let Wp : Field := fun x l => (FiniteAngularHerglotz.incident k input).E x l +
    Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source c mode) x l
  obtain ⟨hWp',hgraphall⟩ := Packet07DrivenUniformHostGraph.actual_host_driven_graph setup k hk0 input hk
    body host hhost d hd outer up axis g hg3 Vchart Wgraph hmapV hmapW hside B3 hB3 hdi hdd A hAgraph
  let hWp := hWp' j0
  let v := pullback g hg.continuous (chartPull up axis (value outer U))
  let G := chartVector up axis (gradient outer U)
  let Q := chartVector up axis (Packet06ScalarGaussLocalization.correction outer Wp hWp)
  let C := pulledGradient g hg G B3 hB3
  let F : L2Vector := fun j => -mulWeight d hd (transformedFlux g hg Q B3 hB3 j)
  have hgraph := hgraphall j0 hmaterial
  change CompactRepresentative v ∧ (∀ j, HasWeakPartial v (C j) j) ∧
    HasDivergenceOn Wgraph (fun j => flux A C d hd j-F j) 0 ∧
    (∀ j, CompactRepresentative (F j)) ∧
    ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
      (∀ k, k ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 k j) k) ∧
      (∀ k, k ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 k j) (F2 k t j) t) at hgraph
  obtain ⟨hv,hC,hdiv,hF,F1,F2,hF1,hF2⟩ := hgraph
  have hdivΩ : HasDivergenceOn Ω (fun j => flux A C d hd j-F j) 0 :=
    fun φ hφ => hdiv φ (hφ.trans hΩW)
  obtain ⟨hWq,horient⟩ := Packet07DrivenUniformOriented.oriented_driven_scalar setup k hk0 input hk outer up axis Vchart hmapV
  have hE : ∀ j, ∀ᵐ y ∂volume, y ∈ ball (0 : Space) outer.rIn →
      gradient outer U j y + Packet06ScalarGaussLocalization.correction outer Wp hWp j y =
        setup.electric k j0 input y j := (horient j0).2.2.2.2.2.2
  have hmapT : ∀ x ∈ T, inverseOriented up axis (graphMap (liftedHeight g) x) ∈ ball (0 : Space) outer.rIn :=
    fun x hx => hmapV _ (hmapW x (hTW hx))
  have hmetricT : ∀ x ∈ T, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ) := fun x hx => hAgraph x (hTW hx)
  exact regional_physical_branches g hg A hA2 hA3 v C F F1 F2 d hd hC hv hF hF1 hF2
    Ω S₀ V S hdivΩ θ hθΩ hθS τ hτV δ hδ hτS b hb M hM B hB hmetric a τa τb ha hτa hτb
    κ hκ2 hκ3 hκΩ hκV hκS V₁ S₁ W₁ V₂ U₂ T hV₁ hW₁ hW₁V₁ hV₁S hU₂ hT hV₂W₁ hU₂V₂ hTU₂ hTS
    τ₁ hτ₁2 hτ₁V δ₁ hδ₁ hτ₁S0 hτ₁S1 κ₁ hκ₁2 hκ₁V hκ₁S ζ₁ δ₂ hδ₂ hζ₁S0 hζ₁S1 hκ₁W hζ₁W
    hmetricτ₁ hmetricζ₁ τa₁ τb₁ ηa₁ ηb₁ hτa₁ hτb₁ hηa₁ hηb₁
    θ₁ η₁ χ₁ hθ₁2 hθ₁W hθ₁V hη₁V hη₁U hχ₁U hχ₁2 hχ₁T
    up axis G Q B3 hB3 rfl rfl hmetricT outer Wp hWp rfl
    (setup.electric k j0 input)
    (gradient outer U) (Packet06ScalarGaussLocalization.correction outer Wp hWp) rfl rfl
    (ball (0 : Space) outer.rIn) hmapT hE

end OQ14.Packet07DrivenUniformPhaseBranches
#print axioms OQ14.Packet07DrivenUniformPhaseBranches.actual_driven_phase_branches
