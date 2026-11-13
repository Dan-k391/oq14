import Packet06AxialHotspot

/-! Coordinate-plane hotspots supply the generic transported-plane predicate. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06AxialHotspotStart
open Set Maxwell Packet06AxialHotspot

theorem coordinate_hotspot (c : StaticCoefficient.Coefficient) (z : ℂ)
    (u : VectorFourier.VectorL2) (body : Set Space) (center : Space) (r M B : ℝ)
    (h : Packet06PlacedHotspot.PhysicalHotspot c z u body center r M B) :
    AxialHotspot c z u body {x : Space | x 2 = 0} center r M B := h

end OQ14.Packet06AxialHotspotStart
#print axioms OQ14.Packet06AxialHotspotStart.coordinate_hotspot
