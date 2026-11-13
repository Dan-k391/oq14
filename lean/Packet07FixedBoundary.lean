import Packet07AffineSmooth
import Packet07PlanarExact
import Packet07AffineComponents
import Packet07SmoothAngular
import Packet07BoundaryNull

/-! Actual fixed-frequency planar peak packing by affine transfer. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.Packet07FixedBoundary
open Filter MeasureTheory Set Metric Packet07PlanarSetup Packet07PlanarCenters Packet07AffineGeometry
open scoped Topology
abbrev Plane := Packet07PlanarCenters.Plane
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

/-- Any fixed positive frequency admits actual finite binary devices with N
    prescribed planar peak regions and a single normalized physical illumination.
    Peak assertions are positive-volume superlevels; attained maxima require separate results. -/
theorem fixed_frequency_planar_superlevels (N : ℕ) (hN : 0 < N)
    (P : Set Plane) (hP : IsOpen P) (hne : P.Nonempty)
    (d t target : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) (htarget : 0 < target) :
    ∃ (g : Setup N (ball (0 : Plane) 1) d t) (u : Plane) (k s : ℝ) (input : Input),
      u ∈ P ∧ 0 < k ∧ 0 < s ∧ s*k = target ∧ input ≠ 0 ∧
      (∀ i, u + s⁻¹ • g.points i ∈ P) ∧
      (∀ i, planeEmbed (u + s⁻¹ • g.points i) 2 = 0) ∧
      Tendsto (Packet07AffinePower.centeredInwardPower s k (planeEmbed u) input) atTop (𝓝 1) ∧
      ((2 * Real.pi^2 / target^2) *
        ‖ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ
          (Packet07AngularTranslation.translatedAmplitude target (planeEmbed u)
            (FiniteVectorAngular.amplitude ((s : ℂ) • input)))‖^2 = 1) ∧
      (∀ n, @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.normal n)
        (Packet07AngularTranslation.translatedAmplitude target (planeEmbed u)
          (FiniteVectorAngular.amplitude ((s : ℂ) • input)) n) = 0) ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (Packet07SmoothAngular.extension target (planeEmbed u) ((s : ℂ) • input) i)) ∧
      (∀ (n : SphereHarmonicBasis.Sphere) i, Packet07SmoothAngular.extension target (planeEmbed u) ((s : ℂ) • input) i n =
        Packet07AngularTranslation.translatedAmplitude target (planeEmbed u)
          (FiniteVectorAngular.amplitude ((s : ℂ) • input)) n i) ∧
      (∀ x i, AngularHerglotz.electric target
          (fun n j => Packet07AngularTranslation.translatedAmplitude target (planeEmbed u)
            (FiniteVectorAngular.amplitude ((s : ℂ) • input)) n j) x i =
        Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident k input).E x i) ∧
      (∀ x i, AngularHerglotz.magnetic target
          (fun n j => Packet07AngularTranslation.translatedAmplitude target (planeEmbed u)
            (FiniteVectorAngular.amplitude ((s : ℂ) • input)) n j) x i =
        Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident k input).H x i) ∧
      ∀ thresholds : Fin N → ℝ, ∃ (n : ℕ) (components : Fin N → Fin 3),
        MaterialMaxwell.TestMaxwell target
          (MaterialMaxwell.dielectric (Packet07AffineMaxwell.affineCoeff s (planeEmbed u) (g.rounded n)))
          (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.electric k n input))
          (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.magnetic k n input)) ∧
        (∀ i, 0 < (volume.restrict (ball (planeEmbed (u + s⁻¹ • g.points i)) ((g.radius/2)/s)))
          {x | thresholds i < ‖Packet07AffineMaxwell.affineField s (planeEmbed u) (g.electric k n input) x (components i)‖}) ∧
        (∀ i x, x ∈ ball (planeEmbed (u + s⁻¹ • g.points i)) ((g.radius/2)/s) →
          planeProject x ∈ P) ∧
        IsOpen (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n) ∧
        (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n) ⊆
          closedBall (planeEmbed u) (g.enclosing/s) ∧
        (∀ i : Fin N, ∀ up : Bool,
          IsOpen (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i up)) ∧
        (∀ i : Fin N, ∀ up : Bool,
          (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i up).Nonempty) ∧
        (∀ i j : Fin N × Bool, i ≠ j → Disjoint
          (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2)
          (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n j.1 j.2)) ∧
        (∀ x : Space, x ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n ↔
          ∃ i : Fin N, ∃ up : Bool, x ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i up) ∧
        (∀ i : Fin N × Bool, ∀ x ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2,
          connectedComponentIn (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n) x =
            Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2) ∧
        (∀ x ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n,
          ∃! i : Fin N × Bool, connectedComponentIn (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n) x =
            Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2) ∧
        volume (frontier (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n)) = 0 ∧
        (∀ x ∈ frontier (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n),
          ∃ (i : Fin 3) (gchart : Plane → ℝ) (V : Set Plane) (up : Bool),
            IsOpen V ∧ (Packet07BoundaryCoordinates.chart i x).1 ∈ V ∧ ContDiffOn ℝ 2 gchart V ∧
            (∀ᶠ y in 𝓝 x, (Packet07BoundaryCoordinates.chart i y).1 ∈ V ∧
              (y ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n ↔
                if up then gchart (Packet07BoundaryCoordinates.chart i y).1 < (Packet07BoundaryCoordinates.chart i y).2
                  else (Packet07BoundaryCoordinates.chart i y).2 < gchart (Packet07BoundaryCoordinates.chart i y).1))) ∧
        (∀ x ∈ frontier (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n),
          ∃ f : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
            ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
              (y ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n ↔ 0 < f y)) ∧
        (let ρ := DynamicVolume.source (g.rounded n) (Packet07SelectedRadiation.actualUnknown g k n input);
          (∀ᵐ x : Space ∂volume, g.enclosing < ‖s • (x-planeEmbed u)‖ →
            ∀ i, Packet07AffineMaxwell.affineField s (planeEmbed u) (g.electric k n input) x i =
              Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident k input).E x i +
              Packet07AffineMaxwell.affineField s (planeEmbed u) (ExteriorContinuity.electric k ρ) x i) ∧
          (∀ x i, Packet07AffineMaxwell.affineField s (planeEmbed u) (g.magnetic k n input) x i =
            Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident k input).H x i +
            Packet07AffineMaxwell.affineField s (planeEmbed u) (MagneticResponse.magnetic k ρ) x i) ∧
          (∀ v : Space, ‖v‖ = 1 →
            Tendsto (fun r : ℝ => MaxwellFarField.factor target r •
              Packet07AffineMaxwell.affineField s (planeEmbed u) (ExteriorContinuity.electric k ρ) (planeEmbed u + r • v))
              atTop (nhds (MaxwellFarField.electricAmplitude k ρ v))) ∧
          (∀ v : Space, ‖v‖ = 1 →
            Tendsto (fun r : ℝ => MaxwellFarField.factor target r •
              Packet07AffineMaxwell.affineField s (planeEmbed u) (MagneticResponse.magnetic k ρ) (planeEmbed u + r • v))
              atTop (nhds (MaxwellFarField.magneticAmplitude k ρ v)))) ∧
        (∀ x : Space, (Packet07AffineMaxwell.affineCoeff s (planeEmbed u) (g.rounded n)).value
          (VectorFourier.coordinateMap x) = (by classical exact
            if x ∈ (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers n) then d else 0)) := by
  obtain ⟨u,hu⟩ := hne
  obtain ⟨ε,hε,hpatch⟩ := Metric.isOpen_iff.mp hP u hu
  have hball : IsOpen (ball (0 : Plane) 1) := isOpen_ball
  have hnonempty : (ball (0 : Plane) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨g,δ,hδ,hsmall⟩ := Packet07PlanarExact.planar_binary_peaks_small_frequency N hN
    (ball (0 : Plane) 1) hball hnonempty d t hd ht ht1
  let εfit : ℝ := ε / (2 * (g.radius + 1))
  have hεfit : 0 < εfit := by
    have hr := g.radius_pos
    dsimp [εfit]
    positivity
  obtain ⟨k,hk,hkδ,hsε⟩ := Packet07PatchDilation.choose_auxiliary_frequency δ target εfit hδ htarget hεfit
  let s : ℝ := target/k
  have hs : 0 < s := div_pos htarget hk
  have hsk : s*k = target := by dsimp [s]; field_simp
  have hsfit : s⁻¹ * (g.radius + 1) < ε/2 := by
    have hh : s⁻¹ * (2*(g.radius+1)) < ε := by
      apply (lt_div_iff₀ (by linarith [g.radius_pos] : 0 < 2*(g.radius+1))).mp
      exact hsε
    nlinarith
  obtain ⟨input,hin,hpower,hdevices⟩ := hsmall k hk hkδ
  have hpower' := Packet07FrequencyScaling.finite_unit_power_dilation s k hs hk input hpower
  have hpowerTarget : Tendsto (FiniteMixedScaledFlux.inwardPowerK target ((s : ℂ) • input)) atTop (𝓝 1) := by
    rw [← hsk]
    exact hpower'
  refine ⟨g,u,k,s,input,hu,hk,hs,hsk,hin,?_,?_,
    Packet07AffinePower.centered_unit_power s k hs (planeEmbed u) input hpower,
    Packet07AngularTranslation.translated_unit_angular_power target htarget (planeEmbed u) ((s : ℂ) • input) hpowerTarget,
    Packet07AngularTranslation.translated_tangent target (planeEmbed u) _
      (FiniteAngularHerglotz.amplitude_tangent ((s : ℂ) • input)),
    ?_,?_,?_,?_,?_⟩
  · intro i
    apply hpatch
    rw [mem_ball, dist_eq_norm]
    have hp : ‖g.points i‖ < 1 := by simpa only [mem_ball, dist_zero_right] using g.points_mem i
    have he : u + s⁻¹ • g.points i - u = s⁻¹ • g.points i := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    have hmul := mul_nonneg (inv_pos.mpr hs).le g.radius_pos.le
    nlinarith [inv_pos.mpr hs, norm_nonneg (g.points i)]
  · intro i
    exact planeEmbed_coord _
  · intro i
    exact Packet07SmoothAngular.extension_smooth target (planeEmbed u) ((s : ℂ) • input) i
  · intro n i
    exact Packet07SmoothAngular.extension_on_sphere target (planeEmbed u) ((s : ℂ) • input) i n
  · intro x i
    rw [Packet07AngularTranslation.translated_electric]
    change (FiniteAngularHerglotz.incident target ((s : ℂ) • input)).E (x-planeEmbed u) i = _
    rw [← hsk, Packet07FrequencyScaling.finite_electric_dilation]
    rfl
  · intro x i
    rw [Packet07AngularTranslation.translated_magnetic]
    change (FiniteAngularHerglotz.incident target ((s : ℂ) • input)).H (x-planeEmbed u) i = _
    rw [← hsk, Packet07FrequencyScaling.finite_magnetic_dilation]
    rfl
  · intro thresholds
    obtain ⟨n,components,hm,hpeak,hopen,hsupport,hnonempty,hdisjoint,hcover,hexact,hunique,hsmooth,hvalue⟩ :=
      hdevices (fun i => thresholds i / s)
    refine ⟨n,components,?_,?_,?_,preimage_open s (planeEmbed u) _ hopen,
      preimage_enclosed s hs (planeEmbed u) _ g.enclosing hsupport,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [← hsk]
      exact Packet07AffineMaxwell.affine_maxwell s k hs (g.rounded n) _ _ hm (planeEmbed u)
    · intro i
      rw [Packet07AffineGeometry.placed_center]
      exact Packet07AffineMaxwell.affine_peak s hs (planeEmbed u) (g.centers i) (g.radius/2) (thresholds i)
        (g.electric k n input) (components i) (hpeak i)
    · intro i x hx
      apply hpatch
      rw [mem_ball]
      have hproj : dist (planeProject x) (u + s⁻¹ • g.points i) < (g.radius/2)/s := by
        have hp := planeProject_dist_le x (planeEmbed (u + s⁻¹ • g.points i))
        rw [planeProject_embed] at hp
        exact lt_of_le_of_lt hp hx
      have hcenter : dist (u + s⁻¹ • g.points i) u < s⁻¹ := by
        rw [dist_eq_norm]
        have he : u + s⁻¹ • g.points i - u = s⁻¹ • g.points i := by abel
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
        have hp : ‖g.points i‖ < 1 := by simpa only [mem_ball, dist_zero_right] using g.points_mem i
        exact mul_lt_of_lt_one_right (inv_pos.mpr hs) hp
      have htri := dist_triangle (planeProject x) (u + s⁻¹ • g.points i) u
      have hmul := mul_nonneg (inv_pos.mpr hs).le g.radius_pos.le
      rw [div_eq_mul_inv] at hproj
      nlinarith [inv_pos.mpr hs]
    · intro i up
      exact preimage_open s (planeEmbed u) _ (Packet07LobeGeometry.lobe_open g.dataFamily g.radii g.centers n i up)
    · intro i up
      exact preimage_nonempty s hs.ne' (planeEmbed u) _ (hnonempty i up)
    · intro i j hij
      exact preimage_disjoint s (planeEmbed u) _ _ (hdisjoint i j hij)
    · intro x
      exact hcover (Packet07AffineGeometry.map s (planeEmbed u) x)
    · have hp := Packet07AffineComponents.affine_exact_partition s hs.ne' (planeEmbed u)
        (fun i : Fin N × Bool => Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2)
        (CommonBinaryInterface.body g.dataFamily g.radii g.centers n)
        (fun i => Packet07LobeGeometry.lobe_open g.dataFamily g.radii g.centers n i.1 i.2)
        (fun i => hnonempty i.1 i.2) hdisjoint (by
          ext x
          simp only [mem_iUnion, Prod.exists]
          exact (hcover x).symm) hexact
      exact hp.1
    · have hp := Packet07AffineComponents.affine_exact_partition s hs.ne' (planeEmbed u)
        (fun i : Fin N × Bool => Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers n i.1 i.2)
        (CommonBinaryInterface.body g.dataFamily g.radii g.centers n)
        (fun i => Packet07LobeGeometry.lobe_open g.dataFamily g.radii g.centers n i.1 i.2)
        (fun i => hnonempty i.1 i.2) hdisjoint (by
          ext x
          simp only [mem_iUnion, Prod.exists]
          exact (hcover x).symm) hexact
      exact hp.2
    · exact Packet07BoundaryNull.bounded_regular_body_boundary_null _ (planeEmbed u) (g.enclosing/s)
        (preimage_enclosed s hs (planeEmbed u) _ g.enclosing hsupport)
        (Packet07AffineSmooth.smooth_boundary_preimage s hs.ne' (planeEmbed u) _ hsmooth)
    · intro x hx
      exact Packet07BoundaryOrientedActual.oriented_chart_of_regular_boundary _ x
        (Packet07AffineSmooth.smooth_boundary_preimage s hs.ne' (planeEmbed u) _ hsmooth x hx)
    · exact Packet07AffineSmooth.smooth_boundary_preimage s hs.ne' (planeEmbed u) _ hsmooth
    · have hout := Packet07SelectedRadiation.selected_outgoing g k s hs (planeEmbed u) n input
      rw [hsk] at hout
      exact hout
    · intro x
      change (g.rounded n).value (VectorFourier.coordinateMap (Packet07AffineGeometry.map s (planeEmbed u) x)) = _
      exact hvalue (Packet07AffineGeometry.map s (planeEmbed u) x)

end OQ14.Packet07FixedBoundary
#print axioms OQ14.Packet07FixedBoundary.fixed_frequency_planar_superlevels
