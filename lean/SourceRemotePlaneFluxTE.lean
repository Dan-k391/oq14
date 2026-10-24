import SourceRemotePlaneFlux
import SourceTERadiation

/-! The TE dual of the single-mode exterior plane flux bound. The actual TE source fields are
`teElectric = magnetic` and `teMagnetic = - electric`, so the normal flux density of the TE field is
exactly the complex conjugate of the TM one, and the same bound holds with the same constants. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.SourceRemotePlaneFluxTE
open Complex Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
open scoped Topology ComplexConjugate

theorem te_flux_eq_conj (d : Data) (P : Poly) (x : Space) :
    crossProduct (SourceGeneralMaxwell.teElectric d P x)
        (conjugate (SourceGeneralMaxwell.teMagnetic d P x)) 2=
      (starRingEnd ℂ) (crossProduct (SourceUnclippedMaxwell.electric d P x)
        (conjugate (SourceUnclippedMaxwell.magnetic d P x)) 2) := by
  simp only [SourceRemotePlaneFlux.cross_two,conjugate,SourceGeneralMaxwell.teElectric,
    SourceGeneralMaxwell.teMagnetic,map_sub,map_mul,map_neg,Complex.conj_conj]
  ring

theorem te_plane_flux_bound (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ∃ r0 C : ℝ, 0 ≤ C ∧ ∀ x : Space, x 2=0 → r0 ≤ ‖x‖ → d.X<‖x‖ →
      ‖crossProduct (SourceGeneralMaxwell.teElectric d P x)
        (conjugate (SourceGeneralMaxwell.teMagnetic d P x)) 2‖ ≤ C/‖x‖^3 := by
  obtain ⟨r0,C,hC,h⟩ := SourceRemotePlaneFlux.plane_flux_bound d P hp
  refine ⟨r0,C,hC,?_⟩
  intro x hx2 hr hX
  rw [te_flux_eq_conj]
  have : ‖(starRingEnd ℂ) (crossProduct (SourceUnclippedMaxwell.electric d P x)
      (conjugate (SourceUnclippedMaxwell.magnetic d P x)) 2)‖=
      ‖crossProduct (SourceUnclippedMaxwell.electric d P x)
        (conjugate (SourceUnclippedMaxwell.magnetic d P x)) 2‖ := by simp
  rw [this]
  exact h x hx2 hr hX

end OQ14.SourceRemotePlaneFluxTE
#print axioms OQ14.SourceRemotePlaneFluxTE.te_flux_eq_conj
#print axioms OQ14.SourceRemotePlaneFluxTE.te_plane_flux_bound
