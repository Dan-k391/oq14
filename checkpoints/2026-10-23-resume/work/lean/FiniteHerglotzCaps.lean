import AngularHerglotz
import SphereSmoothCaps
import ConicalFinitePlanes

/-! Literal smooth angular caps produce genuine finite angular Maxwell illuminations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.FiniteHerglotzCaps
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereReactionKernel OQ14.ConicalRungeClosure
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Sphere := AngularPower.Sphere

/-- An ambient smooth representative of the transverse angular profile. -/
def ambient (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (y : Space) (j : Fin 3) : ℂ :=
  c.sum (fun w z => z*(SphereSmoothCaps.ambient w.1 r hr y : ℂ)*
    ((if w.2=j then 1 else 0)-(y w.2 : ℂ)*(y j : ℂ)))

def amplitude (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) : Sphere → Vector :=
  fun θ j => ambient c r hr θ j

theorem ambient_smooth (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ambient c r hr y j) := by
  apply ContDiff.sum
  intro w _
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space => (y w.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) w.2).contDiff
  have hj : ContDiff ℝ (⊤ : ℕ∞) (fun y : Space => (y j : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).contDiff
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (SphereSmoothCaps.ambient_smooth w.1 r hr))).mul
    (contDiff_const.sub (hi.mul hj))

theorem amplitude_continuous (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (j : Fin 3) :
    Continuous (fun θ => amplitude c r hr θ j) :=
  (ambient_smooth c r hr j).continuous.comp continuous_subtype_val

theorem amplitude_formula (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (θ : Sphere) (j : Fin 3) :
    amplitude c r hr θ j=∑ w ∈ c.support, c w*(SphereSmoothCaps.density w.1 r hr θ : ℂ)*
      ConicalPlaneWaves.polarization θ w.2 j := by
  simp only [amplitude,ambient,Finsupp.sum,ConicalPlaneWaves.polarization_eq _ (AngularPower.sphere_norm θ)]
  rfl

theorem amplitude_tangent (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (θ : Sphere) :
    dot (ConicalPlaneWaves.direction θ) (amplitude c r hr θ)=0 := by
  simp only [dot,amplitude_formula,Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  have hs (w : WaveIndex) : (∑ j : Fin 3, ConicalPlaneWaves.direction θ j*
      (c w*(SphereSmoothCaps.density w.1 r hr θ : ℂ)*ConicalPlaneWaves.polarization θ w.2 j))=0 := by
    have ht := ConicalPlaneWaves.polarization_tangent (θ : Space) (AngularPower.sphere_norm θ) w.2
    have ht' : (∑ j : Fin 3, ConicalPlaneWaves.direction θ j*ConicalPlaneWaves.polarization θ w.2 j)=0 := by
      simpa only [Fin.sum_univ_three,dot] using ht
    calc
      _=c w*(SphereSmoothCaps.density w.1 r hr θ : ℂ)*
        (∑ j : Fin 3, ConicalPlaneWaves.direction θ j*ConicalPlaneWaves.polarization θ w.2 j) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _=0 := by rw [ht',mul_zero]
  apply Finset.sum_eq_zero
  intro w _
  simpa only [Fin.sum_univ_three] using hs w

def electric (k : ℝ) (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) : Field :=
  AngularHerglotz.electric k (amplitude c r hr)

def magnetic (k : ℝ) (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) : Field :=
  AngularHerglotz.magnetic k (amplitude c r hr)

theorem electric_smooth (k : ℝ) (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => electric k c r hr x j) :=
  AngularHerglotz.electric_smooth k _ (amplitude_continuous c r hr) j

theorem magnetic_smooth (k : ℝ) (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => magnetic k c r hr x j) :=
  AngularHerglotz.magnetic_smooth k _ (amplitude_continuous c r hr) j

theorem maxwell_at (k : ℝ) (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (x : Space) :
    MaxwellAt k 1 1 (electric k c r hr) (magnetic k c r hr) x :=
  AngularHerglotz.maxwell_at k _ (amplitude_continuous c r hr) (amplitude_tangent c r hr) x

theorem amplitude_memLp (c : WaveIndex →₀ ℂ) (r : ℝ) (hr : 0 < r) (j : Fin 3) :
    MemLp (fun θ => amplitude c r hr θ j) 2 AngularPower.angularMeasure :=
  (amplitude_continuous c r hr j).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end OQ14.FiniteHerglotzCaps
#print axioms OQ14.FiniteHerglotzCaps.ambient_smooth
#print axioms OQ14.FiniteHerglotzCaps.amplitude_continuous
#print axioms OQ14.FiniteHerglotzCaps.amplitude_formula
#print axioms OQ14.FiniteHerglotzCaps.amplitude_tangent
#print axioms OQ14.FiniteHerglotzCaps.electric_smooth
#print axioms OQ14.FiniteHerglotzCaps.magnetic_smooth
#print axioms OQ14.FiniteHerglotzCaps.maxwell_at
#print axioms OQ14.FiniteHerglotzCaps.amplitude_memLp
