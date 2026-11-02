import FlatDifferenceCoercivity

/-!
UNCOMPILED INTERFACE PROPOSAL -- NOT A PDE PROOF.

Packet 03 target statements, using actual regional DomainCurl.HCurl objects.
Target toolchain: Lean 4.19.0.
Target mathlib: c44e0c8ee63ca166450922a373c7409c5d26b00b.

Every declaration below is a definition or a structure. In particular,
uniformFlatEstimateStatement is the proposition still to be implemented in
Lean, not an assumption, axiom, or proved theorem. Its mathematical proof is
in 03_flat_interface_report.txt. This file deliberately contains no proof
stubs. It does not modify any supplied or frozen project source.

The explicit sum-of-components norm avoids confusing the physical vector
L2 norm with the default Pi norm on Fin 3 -> L2Scalar.
-/

noncomputable section
set_option autoImplicit false

namespace OQ14.Packet03Targets

open MeasureTheory OQ14.Maxwell
open scoped BigOperators

abbrev Field := Space → Fin 3 → ℂ

/-- The genuine regional equations, now with complex frequency. -/
def WeakMaxwellC {Ω : Set Space} (k : ℂ) (ε : Space → ℝ)
    (E H : DomainCurl.HCurl Ω) : Prop :=
  (∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
    E.val.2 j x = Complex.I * k * H.val.1 j x) ∧
  (∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
    H.val.2 j x = -(Complex.I * k) * (ε x : ℂ) * E.val.1 j x)

def fieldValue {Ω : Set Space} (u : DomainCurl.HCurl Ω) : Field :=
  fun x j => u.val.1 j x

def actualCurl {Ω : Set Space} (u : DomainCurl.HCurl Ω) : Field :=
  fun x j => u.val.2 j x

def vectorL2Sq (S : Set Space) (F : Field) : ℝ :=
  ∑ j : Fin 3, ∫ x in S, ‖F x j‖ ^ 2

def vectorL2 (S : Set Space) (F : Field) : ℝ :=
  Real.sqrt (vectorL2Sq S F)

/-- Use on regions whose translated points lie in the source domain. -/
def difference (F : Field) (i : Fin 3) (h : ℝ) : Field :=
  fun x j => ((h : ℂ)⁻¹) * (F (x + h • basis i) j - F x j)

/-- A supplied positive tubular margin; choosing the actual separation
distance in the report gives these hypotheses. No smooth boundary is needed. -/
structure PatchGeometry (Ω U V : Set Space) (r : ℝ) : Prop where
  openOmega : IsOpen Ω
  openU : IsOpen U
  openV : IsOpen V
  nonemptyU : U.Nonempty
  compactClosureU : IsCompact (closure U)
  compactClosureV : IsCompact (closure V)
  closureU_subset_V : closure U ⊆ V
  closureV_subset_Omega : closure V ⊆ Ω
  radius_pos : 0 < r
  tube_inside : ∀ y ∈ closure U, Metric.ball y r ⊆ V

def massPlus (k : ℂ) : ℝ := max ((k ^ 2).re) 0

def frequencyFactor (k : ℂ) (r : ℝ) : ℝ :=
  Real.sqrt (2 * massPlus k + 64 / r ^ 2)

def magneticConstant (d : ℝ) (k : ℂ) (r : ℝ) : ℝ :=
  (1 + d) * (frequencyFactor k r) ^ 2 +
    Real.sqrt (1 + d) * frequencyFactor k r * (4 / r)

def mixedConclusion {Ω : Set Space} (U V : Set Space)
    (r d : ℝ) (k : ℂ) (E H : DomainCurl.HCurl Ω) : Prop :=
  ∀ i : Fin 3, i ≠ 2 → ∀ h : ℝ, 0 < |h| → |h| < r / 8 →
    vectorL2 U (difference (actualCurl H) i h) ≤
      Real.sqrt (1 + d) * frequencyFactor k r *
        (‖k‖ * (1 + d) * vectorL2 V (fieldValue E) +
          (4 / r) * vectorL2 V (fieldValue H))

def magneticConclusion {Ω : Set Space} (U V : Set Space)
    (r d : ℝ) (k : ℂ) (H : DomainCurl.HCurl Ω) : Prop :=
  ∀ i : Fin 3, i ≠ 2 → ∀ h : ℝ, 0 < |h| → |h| < r / 8 →
    vectorL2 U (difference (actualCurl H) i h) ≤
      magneticConstant d k r * vectorL2 V (fieldValue H)

/-- Exact proposed theorem TYPE. No term inhabiting it is supplied here. -/
def uniformFlatEstimateStatement : Prop :=
  ∀ (Ω U V : Set Space) (r d : ℝ) (k : ℂ),
    PatchGeometry Ω U V r → 0 ≤ d → k ≠ 0 →
    ∀ E H : DomainCurl.HCurl Ω,
      WeakMaxwellC k (FlatDifferenceCoercivity.dielectric d) E H →
      mixedConclusion U V r d k E H ∧
      magneticConclusion U V r d k H

end OQ14.Packet03Targets
