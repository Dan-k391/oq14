import Packet07Enclosure

/-! Complete finite planar geometry and common conical material data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07PlanarConeGeometry
open Set Metric Packet07PlanarCenters
abbrev Plane := Packet07PlanarCenters.Plane
abbrev Space := Maxwell.Space

/-- For every finite N and nonempty open planar patch, construct actual common
    singular-cone data, one positive radius and N distinct enclosed planar centers. -/
theorem exists_planar_cone_geometry (N : ℕ) (P : Set Plane) (hP : IsOpen P) (hne : P.Nonempty)
    (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ (c : Fin N → Plane) (p : ConicalStaticVolume.Data) (a R : ℝ),
      Function.Injective c ∧ (∀ i, c i ∈ P) ∧
      Function.Injective (fun i => planeEmbed (c i)) ∧
      (∀ i, planeEmbed (c i) 2 = 0) ∧
      p.contrast = d ∧ p.threshold = t ∧ p.exponent < 1 ∧
      0 < a ∧ a < p.cutoff.rIn ∧ a ≤ p.cutoff.rOut ∧ 0 ≤ R ∧
      (∀ i j, i ≠ j → a+a < dist (planeEmbed (c i)) (planeEmbed (c j))) ∧
      (∀ i j, i ≠ j → Disjoint (closedBall (planeEmbed (c i)) p.cutoff.rOut)
        (closedBall (planeEmbed (c j)) p.cutoff.rOut)) ∧
      (∀ i, closedBall (planeEmbed (c i)) p.cutoff.rOut ⊆ closedBall (0 : Space) R) ∧
      UnionFreeRunge.balls (fun i => planeEmbed (c i)) (fun _ => a) ⊆ closedBall (0 : Space) R := by
  obtain ⟨c, hci, hcP, hcenter, hcplane⟩ := exists_planar_centers N P hP hne
  obtain ⟨p,a,hpd,hpt,hν,ha,hai,haout,hsep,houter⟩ :=
    Packet07CommonConeData.exists_common_cone (fun i => planeEmbed (c i)) hcenter d t hd ht ht1
  have hout0 : 0 ≤ p.cutoff.rOut := le_trans p.cutoff.rIn_pos.le p.cutoff.rIn_lt_rOut.le
  obtain ⟨R,hR0,hR⟩ := Packet07Enclosure.exists_enclosing_radius (fun i => planeEmbed (c i)) p.cutoff.rOut hout0
  refine ⟨c,p,a,R,hci,hcP,hcenter,hcplane,hpd,hpt,hν,ha,hai,haout,hR0,hsep,houter,hR,?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact hR i (closedBall_subset_closedBall haout hi)

end OQ14.Packet07PlanarConeGeometry
#print axioms OQ14.Packet07PlanarConeGeometry.exists_planar_cone_geometry
