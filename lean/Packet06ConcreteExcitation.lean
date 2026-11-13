import Packet06ActualBranchExcitation
import Packet06ActualAngularL2
import Packet06InsertedConeSystem
import Packet06ConcreteModalBranch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ConcreteExcitation
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
  OQ14.Packet06ConcreteModalGeometry OQ14.Packet06ConcreteModalBranch
open scoped Topology
abbrev V := VectorFourier.VectorL2

theorem local_geometry {N : ℕ} {n : ℝ} (g : Geometry N n) (i : Fin N) :
    (∀ x ∈ closedBall (0 : Maxwell.Space) g.radius, x+g.center i ∈ ball 0 1) ∧
      closedBall (g.center i) g.radius ⊆ closedBall (0 : Maxwell.Space) 1 := by
  have hsub : closedBall (g.center i) g.radius ⊆ ball (0 : Maxwell.Space) 1 :=
    (closedBall_subset_closedBall g.radius_outer).trans (g.outer_inside i)
  constructor
  · intro x hx
    apply hsub
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_right,dist_zero_right,sub_zero] using hx
  · exact hsub.trans ball_subset_closedBall

theorem concrete_eventual {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) (hη0 : Tendsto η atTop (𝓝 0)) (hηb : ∀ j, η j ≤ 1)
    (z : ℕ → ℂ) (u : ℕ → V) (hz : ∀ j, z j ≠ 0)
    (hker : ∀ j, ComplexConvolutionAnalytic.volumeBlock (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j) (z j) 1 (u j) = 0)
    (z₀ a₀ : ℂ) (hz₀ : z₀ ≠ 0) (hdet : ModalAlgebra.tmDet 1 (n : ℂ) z₀=0)
    (hfield : ∀ i, Packet06SphereLocalField.inner n z₀ a₀ (g.center i) 2 ≠ 0)
    (hresponse : Tendsto (fun j => ComplexExteriorResponse.response (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j) (z j) 1 1 (u j)) atTop
      (𝓝 (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z₀ 1 1
        (a₀ • (Packet06SectorOperator.numerator n hn z₀ : V)))))
    (Z L : ℝ) (hZ : ∀ j, ‖z j‖ ≤ Z) (hL : 0 ≤ L)
    (hsource : ∀ j i, ‖NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j) (u j)) i‖ ≤ L) :
    ∃ (p : ℕ → ConicalStaticVolume.Data) (hp : ∀ j, (p j).cutoff = g.datum.cutoff ∧
      (p j).contrast = η j ∧ (p j).threshold = (3/4 : ℝ) ∧ (p j).exponent < 1)
      (s : ∀ j, Fin N → System (p j) g.radius),
      (∀ j i k, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 g.radius →
        totalCoordinate (s j i) k x = Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j) (u j)) (DynamicVolume.source (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j) (u j))
          (x+g.center i) k) ∧
      ∀ᶠ j in atTop, ∀ i, ConicalIntrinsicCoefficient.coefficient (s j i) g.radius_pos
        (by rw [(hp j).1]; exact g.radius_inner)
        (hp j).2.2.2 ≠ 0 := by
  obtain ⟨p,hp,hell,hνlim,_⟩ := Packet06ActualAngularL2.convergent_positive_branch g.datum.cutoff (3/4)
    (by norm_num) (by norm_num) η hη hη0
  have hp' (j : ℕ) : (p j).cutoff = g.datum.cutoff ∧ (p j).contrast = η j ∧
      (p j).threshold = (3/4 : ℝ) ∧ (p j).exponent < 1 :=
    ⟨(hp j).1,(hp j).2.1,(hp j).2.2.1,(hp j).2.2.2.2.1⟩
  have hbi (j : ℕ) : g.radius < (p j).cutoff.rIn := by rw [(hp' j).1]; exact g.radius_inner
  have hhalf : ∀ᶠ j in atTop, (1/2 : ℝ) ≤ (p j).exponent :=
    ((tendsto_order.mp hνlim).1 (1/2) (by norm_num)).mono (fun _ h => h.le)
  have hcontrast (j : ℕ) : (p j).contrast ≤ 1 := by rw [(hp' j).2.1]; exact hηb j
  have hα : n^2 ≠ 0 := pow_ne_zero 2 (by linarith : n ≠ 0)
  obtain ⟨hax,hmer,hsupp⟩ := admissible g
  obtain ⟨_,_,_,hc,_,_⟩ := Packet06SphereInsertion.admissible n hn (cone g) hax hmer hsupp η
    (fun j => (hη j).le) hηb hη0
  have hmatch (j : ℕ) (i : Fin N) (y : Maxwell.Space) (hy : y ∈ ball 0 g.radius) :
      1+(Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j).value (VectorFourier.coordinateMap (y+g.center i)) =
        n^2 * ConicalLocalGauss.epsilon (p j) y := by
    have hsphere : ∀ x ∈ ball (0 : Maxwell.Space) g.radius, ‖x+g.center i‖ < 1 := by
      intro x hx
      have h := (local_geometry g i).1 x (ball_subset_closedBall hx)
      simpa using h
    have h := Packet06InsertedConeSystem.actual_local_match (fun _ : Fin N => g.datum)
      (fun _ => g.radius) g.center (n^2) (sq_nonneg n) (fun _ => g.contrast.le)
      (fun _ => g.radius_outer) g.outer_disjoint n hn i g.contrast (η j) (hη j).le
      (p j) (hp' j).2.1 (by rw [(hp' j).2.2.1,g.threshold]) g.radius le_rfl hsphere y hy
    simpa only [Packet06SphereInsertion.family,cone] using h
  let s : ∀ j, Fin N → System (p j) g.radius := fun j i =>
    Packet06ComplexConeSystem.system (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j) (z j) (hz j) 1 1 (by norm_num) (by norm_num)
      (u j) (hc j) (hker j) (p j) g.radius (hbi j) (g.center i) (n^2) hα (local_geometry g i).2 (hmatch j i)
  have hactual (j : ℕ) (i : Fin N) (k : Fin 3) := Packet06ComplexConeSystem.system_actual
    (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j) (z j) (hz j) 1 1 (by norm_num) (by norm_num) (u j) (hc j) (hker j)
      (p j) g.radius (hbi j) (g.center i) (n^2) hα (local_geometry g i).2 (hmatch j i) k
  refine ⟨p,hp',s,hactual,?_⟩
  apply Filter.eventually_all.mpr
  intro i
  have hc0 : g.center i 0 = 0 := (g.onAxis i).1
  have hc1 : g.center i 1 = 0 := (g.onAxis i).2
  obtain ⟨hA,R₀,hR₀,hclose⟩ := Packet06SphereProjection.sphere_average_near_center n z₀ a₀ (g.center i)
    hc0 hc1 (hfield i)
  have hF (k : Fin 3) : Continuous (fun x => Packet06SphereLocalField.inner n z₀ a₀ x k) :=
    continuous_const.mul (ModalOrigin.centerE_continuous ((n : ℂ)*z₀) k)
  have hbase (k : Fin 3) := Packet06CenteredBall.restrict_sphere_base g.radius (g.center i) n hn z₀ a₀ hz₀ hdet
    1 (by norm_num) (local_geometry g i).1 k
  have he := Packet06ActualBranchExcitation.eventual_nonzero (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le)) z u hz hker hc p (3/4)
    (by norm_num) (by norm_num) (fun j => (hp' j).2.2.1) hell
    (by simpa only [funext (fun j => (hp' j).2.1)] using hη0) 1 (by norm_num) hcontrast
    (fun j => (hp' j).2.2.2) hhalf g.radius g.radius_pos g.radius_lt_one.le hbi
    (g.center i) (local_geometry g i).1 (local_geometry g i).2 (n^2) hα (fun j y hy => hmatch j i y hy)
    Z L hZ hL hsource _ (by simpa only [← Packet06LocalPencil.response_actual] using hresponse)
    (Packet06SphereLocalField.inner n z₀ a₀) hF hbase _ hA R₀ hR₀ hclose
  simpa only [s] using he
#print axioms OQ14.Packet06ConcreteExcitation.local_geometry
#print axioms OQ14.Packet06ConcreteExcitation.concrete_eventual
end OQ14.Packet06ConcreteExcitation
