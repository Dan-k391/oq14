import SphereAxialTests

/-! Genuine tangential coordinate identities for ambient test integration on the sphere. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.SphereAxialSurface
open MeasureTheory Set Real OQ14.Maxwell OQ14.AngularPower OQ14.AxialCoordinates OQ14.SphereAxialTests
open scoped Topology

def azimuthD (z θ : ℝ) : Space := (WithLp.equiv 2 Coordinates).symm
  ![-transverse z*sin θ,transverse z*cos θ,0]
def axialTangent (z θ : ℝ) : Space := basis 2-z • latitude z θ
def axialTangentD (z θ : ℝ) : Space := -latitude z θ-z • latitudeD z θ
def azimuthCoefficient (z θ : ℝ) : Space := (WithLp.equiv 2 Coordinates).symm
  ![-sin θ/transverse z,cos θ/transverse z,0]
def azimuthCoefficientD (z θ : ℝ) : Space := (WithLp.equiv 2 Coordinates).symm
  ![-cos θ/transverse z,-sin θ/transverse z,0]

theorem latitude_hasDerivAt_azimuth (z θ : ℝ) :
    HasDerivAt (fun s => latitude z s) (azimuthD z θ) θ := by
  have h : HasDerivAt (fun s : ℝ => ![transverse z*cos s,transverse z*sin s,z])
      ![-transverse z*sin θ,transverse z*cos θ,0] θ := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert (Real.hasDerivAt_cos θ).const_mul (transverse z) using 1
      simp
    · simpa using (Real.hasDerivAt_sin θ).const_mul (transverse z)
    · simpa using hasDerivAt_const θ z
  simpa [Function.comp_def,latitude,physical,AxialCoordinates.map,azimuthD]
    using ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt θ h)

theorem axialTangent_hasDerivAt (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y => axialTangent y θ) (axialTangentD z θ) z := by
  simpa [axialTangent,axialTangentD] using
    (((hasDerivAt_id z).smul (latitude_hasDerivAt z θ hz)).const_sub (basis 2))

theorem azimuthCoefficient_hasDerivAt (z θ : ℝ) :
    HasDerivAt (fun s => azimuthCoefficient z s) (azimuthCoefficientD z θ) θ := by
  have h : HasDerivAt (fun s : ℝ => ![-sin s/transverse z,cos s/transverse z,0])
      ![-cos θ/transverse z,-sin θ/transverse z,0] θ := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using (Real.hasDerivAt_sin θ).neg.div_const (transverse z)
    · simpa using (Real.hasDerivAt_cos θ).div_const (transverse z)
    · simpa using hasDerivAt_const θ (0 : ℝ)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt θ h

theorem axialTangent_at_poles (θ : ℝ) : axialTangent (-1) θ = 0 ∧ axialTangent 1 θ = 0 := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [axialTangent,latitude,physical,AxialCoordinates.map,basis,transverse]

theorem coordinate_curvature (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    axialTangentD z θ+azimuthCoefficientD z θ = (-2 : ℝ) • latitude z θ := by
  have hp := transverse_pos z hz
  have hs := transverse_sq z ⟨hz.1.le,hz.2.le⟩
  ext i
  fin_cases i <;> simp [axialTangentD,azimuthCoefficientD,latitudeD,latitude,physical,AxialCoordinates.map]
  · field_simp [hp.ne']
    linear_combination -cos θ*hs
  · field_simp [hp.ne']
    linear_combination -sin θ*hs
  · ring

theorem tangent_decomposition (i : Fin 3) (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    basis i-(latitude z θ) i • latitude z θ =
      (axialTangent z θ) i • latitudeD z θ+
      (azimuthCoefficient z θ) i • azimuthD z θ := by
  have hp := transverse_pos z hz
  have hs := transverse_sq z ⟨hz.1.le,hz.2.le⟩
  have htr := Real.cos_sq_add_sin_sq θ
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [basis,axialTangent,latitudeD,azimuthD,azimuthCoefficient,latitude,physical,AxialCoordinates.map]
  all_goals field_simp [hp.ne']
  all_goals nlinarith [sq_nonneg (sin θ),sq_nonneg (cos θ)]

theorem azimuth_endpoint_matching (z : ℝ) :
    latitude z (-Real.pi) = latitude z Real.pi ∧
    azimuthCoefficient z (-Real.pi) = azimuthCoefficient z Real.pi := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [latitude,physical,AxialCoordinates.map,azimuthCoefficient]

end OQ14.SphereAxialSurface
