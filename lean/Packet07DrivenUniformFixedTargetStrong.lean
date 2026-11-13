import Packet07DrivenUniformAffineHotspot
import Packet07SmoothAngular
import Packet07AffineSmooth
import Packet07LobeNonempty
import Packet07ExactComponents

/-! Exact target frequency and planar-center placement of the same driven hotspots. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.Packet07DrivenUniformFixedTargetStrong
open Filter MeasureTheory Set Metric Packet07PlanarSetup Packet07PlanarCenters Packet07AffineGeometry
  Packet07DrivenUniformAffineGeometry Packet07DrivenUniformHotspot
open scoped Topology
abbrev Plane := Packet07PlanarCenters.Plane
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem fixed_target_hotspots (N : ℕ) (hN : 0 < N) (P : Set Plane) (hP : IsOpen P) (hne : P.Nonempty)
    (d t target ell : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) (htarget : 0 < target) (hell : 0 < ell) :
    ∃ (g : Setup N (ball (0 : Plane) 1) d t) (u : Plane) (freq s : ℝ) (input : Input),
      u ∈ P ∧ 0 < freq ∧ |freq| ≤ MaterialVolumeLimit.commonRadius d g.enclosing ∧ 0 < s ∧ s*freq=target ∧ input ≠ 0 ∧
      (∀ i, u+s⁻¹ • g.points i ∈ P) ∧ g.radius/s < ell ∧
      2*((g.radius/2)/s) < ell ∧
      (∀ i j, i ≠ j → Disjoint
        (closedBall (planeEmbed (u+s⁻¹ • g.points i)) ((g.radius/2)/s))
        (closedBall (planeEmbed (u+s⁻¹ • g.points j)) ((g.radius/2)/s))) ∧
      (∀ x : Space, dist x (planeEmbed u) ≤ g.enclosing/s → planeProject x ∈ P) ∧
      (∀ i x, dist x (planeEmbed (u+s⁻¹ • g.points i)) ≤ (g.radius/2)/s → planeProject x ∈ P) ∧
      Tendsto (Packet07AffinePower.centeredInwardPower s freq (planeEmbed u) input) atTop (𝓝 1) ∧
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
        Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).E x i) ∧
      (∀ x i, AngularHerglotz.magnetic target
          (fun n j => Packet07AngularTranslation.translatedAmplitude target (planeEmbed u)
            (FiniteVectorAngular.amplitude ((s : ℂ) • input)) n j) x i =
        Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).H x i) ∧
      (∀ᶠ j : ℕ in atTop,
        MaterialMaxwell.TestMaxwell target
          (MaterialMaxwell.dielectric (Packet07AffineMaxwell.affineCoeff s (planeEmbed u) (g.rounded j)))
          (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.electric freq j input))
          (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.magnetic freq j input)) ∧
        IsOpen (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j) ∧
        (∀ x ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j,
          planeProject x ∈ P) ∧
        (∀ i : Fin N, ∀ up : Bool,
          (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i up).Nonempty) ∧
        (∀ i l : Fin N × Bool, i ≠ l → Disjoint
          (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2)
          (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j l.1 l.2)) ∧
        (∀ i : Fin N × Bool, ∀ x ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2,
          connectedComponentIn (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j) x =
            Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2) ∧
        (∀ x ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j,
          ∃! i : Fin N × Bool, connectedComponentIn (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j) x =
            Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2) ∧
        (∀ x ∈ frontier (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j),
          ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧ fderiv ℝ F x ≠ 0 ∧
            ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
              (y ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j ↔ 0 < F y)) ∧
        (∀ x : Space, (Packet07AffineMaxwell.affineCoeff s (planeEmbed u) (g.rounded j)).value
          (VectorFourier.coordinateMap x) =
            (by classical exact if x ∈ Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j then d else 0)) ∧
        (let ρ := DynamicVolume.source (g.rounded j) (Packet07SelectedRadiation.actualUnknown g freq j input)
         (∀ᵐ x : Space ∂volume, g.enclosing < ‖s • (x-planeEmbed u)‖ →
          ∀ i, Packet07AffineMaxwell.affineField s (planeEmbed u) (g.electric freq j input) x i =
            Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).E x i +
            Packet07AffineMaxwell.affineField s (planeEmbed u) (ExteriorContinuity.electric freq ρ) x i) ∧
         (∀ x i, Packet07AffineMaxwell.affineField s (planeEmbed u) (g.magnetic freq j input) x i =
            Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).H x i +
            Packet07AffineMaxwell.affineField s (planeEmbed u) (MagneticResponse.magnetic freq ρ) x i) ∧
         (∀ v : Space, ‖v‖=1 → Tendsto (fun r : ℝ => MaxwellFarField.factor target r •
            Packet07AffineMaxwell.affineField s (planeEmbed u) (ExteriorContinuity.electric freq ρ) (planeEmbed u+r • v))
            atTop (nhds (MaxwellFarField.electricAmplitude freq ρ v))) ∧
         (∀ v : Space, ‖v‖=1 → Tendsto (fun r : ℝ => MaxwellFarField.factor target r •
            Packet07AffineMaxwell.affineField s (planeEmbed u) (MagneticResponse.magnetic freq ρ) (planeEmbed u+r • v))
            atTop (nhds (MaxwellFarField.magneticAmplitude freq ρ v))))) ∧
      ∃ B : Fin N → ℝ, (∀ i, 0 ≤ B i) ∧ ∀ M : Fin N → ℝ,
        ∀ᶠ j : ℕ in atTop, ∀ i,
          HotspotAbove (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.electric freq j input))
            (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j)
            (planeEmbed (u+s⁻¹ • g.points i)) ((g.radius/2)/s) (M i) (s*B i) := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  obtain ⟨u,hu⟩ := hne
  obtain ⟨ε,hε,hpatch⟩ := Metric.isOpen_iff.mp hP u hu
  have hnonempty : (ball (0 : Plane) 1).Nonempty := ⟨0,by simp⟩
  obtain ⟨g,δ,hδ,hsmall⟩ := Packet07DrivenUniformSelectedHotspots.one_input_all_hotspots N hN
    (ball (0 : Plane) 1) isOpen_ball hnonempty d t hd ht ht1
  let e := min (ε/(2*(g.enclosing+g.radius+2))) (ell/(2*(g.radius+1)))
  have he : 0 < e := by
    have hr := g.radius_pos
    have hR := g.enclosing_nonnegative
    dsimp [e]
    positivity
  have hrad : 0 < MaterialVolumeLimit.commonRadius d g.enclosing :=
    MaterialVolumeLimit.commonRadius_positive d g.enclosing hd.le
  obtain ⟨freq,hfreq,hfreqδ,hfit⟩ := Packet07PatchDilation.choose_auxiliary_frequency
    (min δ (MaterialVolumeLimit.commonRadius d g.enclosing)) target e (lt_min hδ hrad) htarget he
  have hsmallδ : freq < δ := hfreqδ.trans_le (min_le_left _ _)
  have hcommon : |freq| ≤ MaterialVolumeLimit.commonRadius d g.enclosing := by
    rw [abs_of_pos hfreq]
    exact (hfreqδ.trans_le (min_le_right _ _)).le
  let s : ℝ := target/freq
  have hs : 0 < s := div_pos htarget hfreq
  have hsk : s*freq=target := by dsimp [s]; field_simp
  have hsε' : s⁻¹ < ε/(2*(g.enclosing+g.radius+2)) := hfit.trans_le (min_le_left _ _)
  have hsε : s⁻¹*(g.enclosing+g.radius+2) < ε/2 := by
    have hh := (lt_div_iff₀ (by linarith [g.enclosing_nonnegative,g.radius_pos] : 0 < 2*(g.enclosing+g.radius+2))).mp hsε'
    nlinarith
  have hsℓ : s⁻¹ < ell/(2*(g.radius+1)) := hfit.trans_le (min_le_right _ _)
  have hsize : g.radius/s < ell := by
    have hmul := (lt_div_iff₀ (by linarith [g.radius_pos] : 0 < 2*(g.radius+1))).mp hsℓ
    rw [div_eq_mul_inv]
    nlinarith [g.radius_pos,inv_pos.mpr hs]
  obtain ⟨input,hin,hpower,B,hB,hhot⟩ := hsmall freq hfreq hsmallδ
  have hpower' := Packet07FrequencyScaling.finite_unit_power_dilation s freq hs hfreq input hpower
  have hpowerTarget : Tendsto (FiniteMixedScaledFlux.inwardPowerK target ((s : ℂ) • input)) atTop (𝓝 1) := by
    rw [←hsk]
    exact hpower'
  refine ⟨g,u,freq,s,input,hu,hfreq,hcommon,hs,hsk,hin,?_,hsize,?_,?_,?_,?_,
    Packet07AffinePower.centered_unit_power s freq hs (planeEmbed u) input hpower,
    Packet07AngularTranslation.translated_unit_angular_power target htarget (planeEmbed u) ((s : ℂ) • input) hpowerTarget,
    Packet07AngularTranslation.translated_tangent target (planeEmbed u) _
      (FiniteAngularHerglotz.amplitude_tangent ((s : ℂ) • input)),?_,?_,?_,?_,?_,B,hB,?_⟩
  · intro i
    apply hpatch
    rw [mem_ball,dist_eq_norm]
    have hp : ‖g.points i‖ < 1 := by simpa only [mem_ball,dist_zero_right] using g.points_mem i
    have heq : u+s⁻¹ • g.points i-u=s⁻¹ • g.points i := by abel
    rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
    nlinarith [inv_pos.mpr hs,norm_nonneg (g.points i),g.enclosing_nonnegative,g.radius_pos]
  · have he : 2*((g.radius/2)/s)=g.radius/s := by ring
    rw [he]
    exact hsize
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hci : placement s hs (planeEmbed u) (g.centers i) = planeEmbed (u+s⁻¹ • g.points i) :=
      (Packet07AffineGeometry.placed_center s u (g.points i)).symm
    have hcj : placement s hs (planeEmbed u) (g.centers j) = planeEmbed (u+s⁻¹ • g.points j) :=
      (Packet07AffineGeometry.placed_center s u (g.points j)).symm
    have htri := dist_triangle (placement s hs (planeEmbed u) (g.centers i)) x
      (placement s hs (planeEmbed u) (g.centers j))
    rw [Packet07DrivenUniformAffineHotspot.distance_placement,hci,hcj] at htri
    have hi : dist (planeEmbed (u+s⁻¹ • g.points i)) x ≤ (g.radius/2)/s := by simpa [dist_comm] using hxi
    have hj : dist x (planeEmbed (u+s⁻¹ • g.points j)) ≤ (g.radius/2)/s := hxj
    have hsep := g.separation i j hij
    have hh := mul_lt_mul_of_pos_left hsep (inv_pos.mpr hs)
    rw [div_eq_mul_inv] at hi hj
    dsimp [Setup.centers] at htri
    have hr := mul_pos g.radius_pos (inv_pos.mpr hs)
    nlinarith
  · intro x hx
    apply hpatch
    rw [mem_ball]
    have hp := planeProject_dist_le x (planeEmbed u)
    rw [planeProject_embed] at hp
    rw [div_eq_mul_inv] at hx
    nlinarith [g.enclosing_nonnegative,g.radius_pos,inv_pos.mpr hs]
  · intro i x hx
    apply hpatch
    rw [mem_ball]
    have hp := planeProject_dist_le x (planeEmbed (u+s⁻¹ • g.points i))
    rw [planeProject_embed] at hp
    have hc : dist (u+s⁻¹ • g.points i) u < s⁻¹ := by
      rw [dist_eq_norm]
      have heq : u+s⁻¹ • g.points i-u=s⁻¹ • g.points i := by abel
      rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
      have hi : ‖g.points i‖ < 1 := by simpa only [mem_ball,dist_zero_right] using g.points_mem i
      exact mul_lt_of_lt_one_right (inv_pos.mpr hs) hi
    have htri := dist_triangle (planeProject x) (u+s⁻¹ • g.points i) u
    rw [div_eq_mul_inv] at hx
    nlinarith [g.enclosing_nonnegative,g.radius_pos,inv_pos.mpr hs]
  · intro i
    exact Packet07SmoothAngular.extension_smooth target (planeEmbed u) ((s : ℂ) • input) i
  · intro n i
    exact Packet07SmoothAngular.extension_on_sphere target (planeEmbed u) ((s : ℂ) • input) i n
  · intro x i
    rw [Packet07AngularTranslation.translated_electric]
    change (FiniteAngularHerglotz.incident target ((s : ℂ) • input)).E (x-planeEmbed u) i = _
    rw [←hsk,Packet07FrequencyScaling.finite_electric_dilation]
    rfl
  · intro x i
    rw [Packet07AngularTranslation.translated_magnetic]
    change (FiniteAngularHerglotz.incident target ((s : ℂ) • input)).H (x-planeEmbed u) i = _
    rw [←hsk,Packet07FrequencyScaling.finite_magnetic_dilation]
    rfl
  · filter_upwards [CommonBinaryInterface.eventually_body_smooth g.dataFamily g.radii g.centers
      g.radii_pos g.radii_outer g.outer_sep, Packet07ExactComponents.eventually_exact_components
      g.dataFamily g.radii g.centers g.radii_outer g.outer_sep g.radii_pos] with j hcert hlobes
    obtain ⟨hnonempty,hexact,_⟩ := hlobes
    have hdisjoint := Packet07LobeGeometry.lobes_pairwise_disjoint g.dataFamily g.radii g.centers
      g.radii_outer g.outer_sep g.radii_pos j
    have hcover : (⋃ i : Fin N × Bool, Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2) =
        CommonBinaryInterface.body g.dataFamily g.radii g.centers j := by
      ext x
      constructor
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.1,hi.1⟩
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        rcases (Packet07LobeGeometry.lobe_split g.dataFamily g.radii g.centers j i x).mp hi with h | h
        · exact mem_iUnion.mpr ⟨⟨i,false⟩,h⟩
        · exact mem_iUnion.mpr ⟨⟨i,true⟩,h⟩
    have hpartition := Packet07AffineComponents.affine_exact_partition s hs.ne' (planeEmbed u)
      (fun i : Fin N × Bool => Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2)
      (CommonBinaryInterface.body g.dataFamily g.radii g.centers j)
      (fun i => Packet07LobeGeometry.lobe_open g.dataFamily g.radii g.centers j i.1 i.2)
      (fun i => hnonempty i.1 i.2) hdisjoint hcover hexact
    have hm := ConicalCommonBinaryPeaks.rounded_maxwell g.dataFamily g.radii g.centers d g.contrast_pos.le
      g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing freq g.enclosing_nonnegative
      hcommon g.outer_enclosed j (FiniteAngularHerglotz.incident freq input)
    refine ⟨?_,Packet07AffineGeometry.preimage_open s (planeEmbed u) _
      (CommonBinaryInterface.body_open g.dataFamily g.radii g.centers j),?_,?_,?_,hpartition.1,hpartition.2,
      Packet07AffineSmooth.smooth_boundary_preimage s hs.ne' (planeEmbed u) _ hcert,?_,?_⟩
    · rw [←hsk]
      exact Packet07AffineMaxwell.affine_maxwell s freq hs (g.rounded j) _ _ hm (planeEmbed u)
    · intro x hx
      have hsupport := CommonBinaryInterface.body_support g.dataFamily g.radii g.centers g.radii_pos
        g.radii_outer g.enclosing g.outer_enclosed j
      have hbound := Packet07AffineGeometry.preimage_enclosed s hs (planeEmbed u) _ g.enclosing hsupport hx
      apply hpatch
      rw [mem_ball]
      have hp := planeProject_dist_le x (planeEmbed u)
      rw [planeProject_embed] at hp
      have hd' : dist x (planeEmbed u) ≤ g.enclosing/s := hbound
      rw [div_eq_mul_inv] at hd'
      nlinarith [g.enclosing_nonnegative,g.radius_pos,inv_pos.mpr hs]
    · intro i up
      exact Packet07AffineGeometry.preimage_nonempty s hs.ne' (planeEmbed u) _ (hnonempty i up)
    · intro i l hil
      exact Packet07AffineGeometry.preimage_disjoint s (planeEmbed u) _ _ (hdisjoint i l hil)
    · intro x
      change (g.rounded j).value (VectorFourier.coordinateMap (Packet07AffineGeometry.map s (planeEmbed u) x)) = _
      exact CommonBinaryInterface.coefficient_body g.dataFamily g.radii g.centers d g.contrast_pos.le
        g.contrast_bound g.radii_pos g.radii_outer g.outer_sep d (fun _ => g.contrast_eq) j _
    · have hout := Packet07SelectedRadiation.selected_outgoing g freq s hs (planeEmbed u) j input
      rw [hsk] at hout
      exact hout
  · intro M
    filter_upwards [hhot (fun i => M i/s)] with j hj i
    have hh := Packet07DrivenUniformAffineHotspot.affine_actual_hotspot (g.electric freq j input)
      (CommonBinaryInterface.body g.dataFamily g.radii g.centers j)
      (CommonBinaryInterface.body_open g.dataFamily g.radii g.centers j)
      (g.centers i) (g.radius/2) (M i/s) (B i) (hj i) s hs (planeEmbed u)
    have hbody : placement s hs (planeEmbed u) '' CommonBinaryInterface.body g.dataFamily g.radii g.centers j =
      Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j :=
      (placement s hs (planeEmbed u)).image_eq_preimage _
    have hcenter : placement s hs (planeEmbed u) (g.centers i) = planeEmbed (u+s⁻¹ • g.points i) := by
      symm
      exact Packet07AffineGeometry.placed_center s u (g.points i)
    rw [hbody,hcenter] at hh
    simpa only [mul_div_cancel₀ _ hs.ne'] using hh
end OQ14.Packet07DrivenUniformFixedTargetStrong
#print axioms OQ14.Packet07DrivenUniformFixedTargetStrong.fixed_target_hotspots
