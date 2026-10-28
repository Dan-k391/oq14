/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import LWSymmetricEval

/-!
# The Lindemann-Weierstrass theorem

Ported from mathlib PR 28013, commit d173f68c80a51efe617648e78fa1ae3e2b994a9d.
-/

open Finset Polynomial

theorem exists_sum_map_aroot_smul_eq {R S : Type*} [CommRing R] [Field S] [Algebra R S] (p : R[X])
    (k : R) (e : ℕ) (q : R[X]) (hk : p.leadingCoeff ∣ k) (he : q.natDegree ≤ e)
    (inj : Function.Injective (algebraMap R S))
    (card_aroots : (p.aroots S).card = p.natDegree) :
    ∃ c, ((p.aroots S).map fun x => k ^ e • aeval x q).sum = algebraMap R S c := by
  obtain ⟨k', rfl⟩ := hk; let k := p.leadingCoeff * k'
  have :
    (fun x : S => k ^ e • aeval x q) =
      (fun x => aeval x (∑ i ∈ range (e + 1), monomial i (k' ^ i * k ^ (e - i) * q.coeff i))) ∘
        fun x => p.leadingCoeff • x := by
    funext x; rw [Function.comp_apply]
    simp_rw [map_sum, aeval_eq_sum_range' (Nat.lt_add_one_iff.mpr he), aeval_monomial, smul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [← Algebra.smul_def, smul_pow, smul_smul, smul_smul, mul_comm (_ * _) (_ ^ _), ← mul_assoc,
      ← mul_assoc, ← mul_pow, ← pow_add,
      add_tsub_cancel_of_le (Nat.lt_add_one_iff.mp (mem_range.mp hi))]
  rw [this, ← Multiset.map_map _ fun x => p.leadingCoeff • x]
  have h1 : ((p.aroots S).map fun x => p.leadingCoeff • x).card =
      Fintype.card (Fin (p.aroots S).card) := by
    rw [Multiset.card_map, Fintype.card_fin]
  have h2 : Fintype.card (Fin (p.aroots S).card) ≤ p.natDegree := by
    rw [Fintype.card_fin]; exact (card_roots' _).trans natDegree_map_le
  rw [← MvPolynomial.symmetricSubalgebra.aevalMultiset_sumPolynomial _ _ h1,
    ← MvPolynomial.symmetricSubalgebra.scaleAEvalRoots_eq_aevalMultiset _ _ inj h2 card_aroots]
  exact ⟨_, rfl⟩

namespace OQ14.LWSumAEvalARoots
theorem integral_root_sum {R S : Type*} [CommRing R] [Field S] [Algebra R S]
    (p : Polynomial R) (k : R) (e : ℕ) (q : Polynomial R)
    (hk : p.leadingCoeff ∣ k) (he : q.natDegree ≤ e)
    (inj : Function.Injective (algebraMap R S))
    (card_aroots : (p.aroots S).card = p.natDegree) :
    ∃ c, ((p.aroots S).map fun x => k ^ e • Polynomial.aeval x q).sum = algebraMap R S c :=
  exists_sum_map_aroot_smul_eq p k e q hk he inj card_aroots
end OQ14.LWSumAEvalARoots

#print axioms OQ14.LWSumAEvalARoots.integral_root_sum
