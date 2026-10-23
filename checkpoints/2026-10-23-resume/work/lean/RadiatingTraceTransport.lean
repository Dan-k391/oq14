import RadiatingTrace

/-! Actual outgoing traces respect exterior agreement and complex linear operations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RadiatingTraceTransport
open MeasureTheory Filter OQ14.Maxwell OQ14.AngularPower OQ14.RadiatingTrace
open scoped Topology

theorem ray_agreement (R : ℝ) (E F : Field) (he : ∀ x : Space,R<‖x‖ → E x=F x) :
    ∀ᶠ r : ℝ in atTop,∀ n : Sphere,E (r • (n : Space))=F (r • (n : Space)) := by
  filter_upwards [eventually_gt_atTop (max R 0)] with r hr n
  apply he
  simpa only [norm_smul,sphere_norm,mul_one,Real.norm_eq_abs,
    abs_of_pos ((le_max_right _ _).trans_lt hr)] using (le_max_left R 0).trans_lt hr

def exteriorCongr {k : ℝ} {E H F G : Field} (t : Trace k E H) (R : ℝ)
    (he : ∀ x : Space,R<‖x‖ → F x=E x) (hh : ∀ x : Space,R<‖x‖ → G x=H x) : Trace k F G where
  far := t.far
  transverse := t.transverse
  sphericalContinuous := by
    filter_upwards [ray_agreement R F E he,ray_agreement R G H hh,t.sphericalContinuous] with r hrE hrH hr
    have hE := funext hrE
    have hH := funext hrH
    rwa [hE,hH]
  bounded := by
    obtain ⟨C,hC,hb⟩ := t.bounded
    refine ⟨C,hC,?_⟩
    filter_upwards [ray_agreement R F E he,ray_agreement R G H hh,hb] with r hrE hrH hr n i
    rw [hrE n,hrH n]
    exact hr n i
  electricLimit n := by
    apply (t.electricLimit n).congr'
    filter_upwards [ray_agreement R F E he] with r hr
    rw [hr n]
  magneticLimit n := by
    apply (t.magneticLimit n).congr'
    filter_upwards [ray_agreement R G H hh] with r hr
    rw [hr n]

def smul {k : ℝ} {E H : Field} (t : Trace k E H) (c : ℂ) : Trace k (c • E) (c • H) where
  far n := c • t.far n
  transverse n := by
    have ht := t.transverse n
    dsimp only [dot] at ht ⊢
    simp only [Pi.smul_apply,smul_eq_mul]
    linear_combination c*ht
  sphericalContinuous := by
    filter_upwards [t.sphericalContinuous] with r hr
    exact ⟨(continuous_const : Continuous (fun _ : Sphere => c)).smul hr.1,
      (continuous_const : Continuous (fun _ : Sphere => c)).smul hr.2⟩
  bounded := by
    obtain ⟨C,hC,hb⟩ := t.bounded
    refine ⟨‖c‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
    filter_upwards [hb] with r hr n i
    simp only [Pi.smul_apply,smul_eq_mul]
    constructor
    · calc
        _ = ‖c‖*‖MaxwellFarField.factor k r*E (r • (n : Space)) i‖ := by rw [←norm_mul];congr 1;ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hr n i).1 (norm_nonneg _)
    · calc
        _ = ‖c‖*‖MaxwellFarField.factor k r*H (r • (n : Space)) i‖ := by rw [←norm_mul];congr 1;ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hr n i).2 (norm_nonneg _)
  electricLimit n := by
    simpa only [Pi.smul_apply,smul_smul,mul_comm] using (t.electricLimit n).const_smul c
  magneticLimit n := by
    rw [map_smul]
    simpa only [Pi.smul_apply,smul_smul,mul_comm] using (t.magneticLimit n).const_smul c

def add {k : ℝ} {E H F G : Field} (t : Trace k E H) (s : Trace k F G) : Trace k (E+F) (H+G) where
  far n := t.far n+s.far n
  transverse n := by
    have ht := t.transverse n
    have hs := s.transverse n
    dsimp only [dot] at ht hs ⊢
    simp only [Pi.add_apply]
    linear_combination ht+hs
  sphericalContinuous := by
    filter_upwards [t.sphericalContinuous,s.sphericalContinuous] with r hr hs
    exact ⟨hr.1.add hs.1,hr.2.add hs.2⟩
  bounded := by
    obtain ⟨C,hC,hb⟩ := t.bounded
    obtain ⟨D,hD,hd⟩ := s.bounded
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    filter_upwards [hb,hd] with r hr hs n i
    simp only [Pi.add_apply,mul_add]
    exact ⟨(norm_add_le _ _).trans (add_le_add (hr n i).1 (hs n i).1),
      (norm_add_le _ _).trans (add_le_add (hr n i).2 (hs n i).2)⟩
  electricLimit n := by
    simpa only [Pi.add_apply,smul_add] using (t.electricLimit n).add (s.electricLimit n)
  magneticLimit n := by
    simpa only [Pi.add_apply,smul_add,map_add] using (t.magneticLimit n).add (s.magneticLimit n)

end OQ14.RadiatingTraceTransport

#print axioms OQ14.RadiatingTraceTransport.ray_agreement
#print axioms OQ14.RadiatingTraceTransport.exteriorCongr
#print axioms OQ14.RadiatingTraceTransport.smul
#print axioms OQ14.RadiatingTraceTransport.add
