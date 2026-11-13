import Packet07FrequencyScaling

/-! A finite planar packing setup with all conical and geometric data constructed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07PlanarSetup
open Set Metric Packet07PlanarCenters
abbrev Plane := Packet07PlanarCenters.Plane
abbrev Space := Maxwell.Space

/-- All finite-family geometric prerequisites for the actual binary-peak theorem. -/
structure Setup (N : ℕ) (P : Set Plane) (d t : ℝ) where
  points : Fin N → Plane
  datum : ConicalStaticVolume.Data
  radius : ℝ
  enclosing : ℝ
  contrast_pos : 0 < d
  points_injective : Function.Injective points
  points_mem : ∀ i, points i ∈ P
  contrast_eq : datum.contrast = d
  threshold_eq : datum.threshold = t
  exponent_lt_one : datum.exponent < 1
  radius_pos : 0 < radius
  radius_in : radius < datum.cutoff.rIn
  radius_out : radius ≤ datum.cutoff.rOut
  enclosing_nonnegative : 0 ≤ enclosing
  separation : ∀ i j, i ≠ j → radius + radius < dist (planeEmbed (points i)) (planeEmbed (points j))
  outer_disjoint : ∀ i j, i ≠ j → Disjoint (closedBall (planeEmbed (points i)) datum.cutoff.rOut)
    (closedBall (planeEmbed (points j)) datum.cutoff.rOut)
  outer_enclosed : ∀ i, closedBall (planeEmbed (points i)) datum.cutoff.rOut ⊆ closedBall (0 : Space) enclosing
  balls_enclosed : UnionFreeRunge.balls (fun i => planeEmbed (points i)) (fun _ => radius) ⊆ closedBall (0 : Space) enclosing

/-- The setup exists for all finite N without hidden geometry or cone-data assumptions. -/
theorem exists_setup (N : ℕ) (P : Set Plane) (hP : IsOpen P) (hne : P.Nonempty)
    (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) : Nonempty (Setup N P d t) := by
  obtain ⟨c,p,a,R,hci,hcP,hcenter,hplane,hpd,hpt,hν,ha,hai,haout,hR0,hsep,houter,hR,hballs⟩ :=
    Packet07PlanarConeGeometry.exists_planar_cone_geometry N P hP hne d t hd ht ht1
  exact ⟨⟨c,p,a,R,hd,hci,hcP,hpd,hpt,hν,ha,hai,haout,hR0,hsep,houter,hR,hballs⟩⟩

namespace Setup
variable {N : ℕ} {P : Set Plane} {d t : ℝ} (g : Setup N P d t)

def dataFamily : Fin N → ConicalStaticVolume.Data := fun _ => g.datum
def radii : Fin N → ℝ := fun _ => g.radius
def centers : Fin N → Space := fun i => planeEmbed (g.points i)

theorem contrast_bound : ∀ i, (g.dataFamily i).contrast ≤ d := fun _ => by simp [dataFamily, g.contrast_eq]
theorem radii_pos : ∀ i, 0 < g.radii i := fun _ => g.radius_pos
theorem radii_outer : ∀ i, g.radii i ≤ (g.dataFamily i).cutoff.rOut := fun _ => g.radius_out
theorem outer_sep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer g.dataFamily g.centers i)
    (ConicalCommonMaterial.outer g.dataFamily g.centers j) := by
  intro i j hij
  exact g.outer_disjoint i j hij

def rounded (n : ℕ) : StaticCoefficient.Coefficient :=
  ConicalCommonBinaryPeaks.rounded g.dataFamily g.radii g.centers d g.contrast_pos.le
    g.contrast_bound g.radii_outer g.outer_sep g.radii_pos n

def electric (k : ℝ) (n : ℕ) (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ) : Maxwell.Field :=
  ConicalCommonBinaryPeaks.electric g.dataFamily g.radii g.centers d g.contrast_pos.le
    g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing k n (FiniteAngularHerglotz.incident k input)

def magnetic (k : ℝ) (n : ℕ) (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ) : Maxwell.Field :=
  ConicalCommonBinaryPeaks.magnetic g.dataFamily g.radii g.centers d g.contrast_pos.le
    g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing k n (FiniteAngularHerglotz.incident k input)

end Setup

end OQ14.Packet07PlanarSetup
#print axioms OQ14.Packet07PlanarSetup.exists_setup

#print axioms OQ14.Packet07PlanarSetup.Setup.contrast_bound
#print axioms OQ14.Packet07PlanarSetup.Setup.radii_pos
#print axioms OQ14.Packet07PlanarSetup.Setup.radii_outer
#print axioms OQ14.Packet07PlanarSetup.Setup.outer_sep
