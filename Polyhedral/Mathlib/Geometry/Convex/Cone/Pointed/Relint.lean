/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Partition.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Rank
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Dual
-- import Polyhedral.Halfspace

open Function Module OrderDual LinearMap
open Submodule hiding span dual DualClosed
open PointedCone

-- ## RELINT

/-
The relative interior (relint for short) is a topological notion, and hence might depend on the
exact topology chosen on the ambient space. In finite dimensions, the topology is essentially
unique, but in infinite dimensions it is possible that a cone has a non-empty or empty relint
depending on the topology.

Without a topology one can consider algebraic notions of relative interior.

The `core` is one possible notion with the following equivalent definitions: a point x ∈ C lies in
the core iff one of the following equivalent conditions holds:
  * x lies in no proper face of C
  * hull R (C ∪ (-x)) = span R C
  * ∀ t : M, ∃ c > 0, x + c • t ∈ C
  * ∀ φ : Dual R M, φ x = 0 → φ ∈ lineal (dual (Dual.eval R M) C)

The `weak relint` is another notion that is not always equivalent to the core. It is the relative
interior w.r.t. the topology obtain from the double-dual closure operation (or, weak topology).

In finite dimensions all these notions are the same, while in infinite dimensions this is not
true anymore. We always have `weak relint ≤ core`.

The core has moreover the property that the cone is the disjoint union of the cores of the faces.
This is not true for the weak relint. One still has disjointness of the weak relints, but not that
they cover all of the cone.

Here we chose the core for defining the algebraic relint. Among its many equivalent deinitions,
we chose the most elementary one: `hull R (C ∪ (-x)) = span R C`, because it does not depend on
duality or the notions of faces.

See also: https://en.wikipedia.org/wiki/Algebraic_interior

-/

/- TODO:
  * the relints of the faces of a cone partition the cone.
  * the relint is preserved under taking the double dual closure.
-/

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C D : PointedCone R M} {x : M}

/-- Algebraic relative interior, also known as core. -/
def relint (C : PointedCone R M) : ConvexCone R M where
  carrier := {x ∈ C | ∀ t ∈ C.linSpan, ∃ c : R, 0 < c ∧ x + c • t ∈ C}
  smul_mem' c hc x hx := by
    refine ⟨C.smul_mem (le_of_lt hc) hx.1, fun t ht ↦ ?_⟩
    obtain ⟨d, hd⟩ := hx.2 t ht
    refine ⟨c * d ,⟨mul_pos hc hd.1, ?_⟩⟩
    simpa [mul_smul, ← smul_add] using C.smul_mem (le_of_lt hc) hd.2
  add_mem' x hx y hy := by
    refine ⟨C.add_mem hx.1 hy.1, fun t ht ↦ ?_⟩
    obtain ⟨a, ha⟩ := hx.2 t ht
    obtain ⟨b, hb⟩ := hy.2 t ht
    use a+b, add_pos ha.1 hb.1
    suffices x + y + (a + b) • t = x + a • t + (y + b • t) by
      simpa [this] using C.add_mem ha.2 hb.2
    module

lemma relint_le : C.relint ≤ C := fun _ hx => hx.1

lemma mem_relint_iff_forall_exists_gt_zero_forall_le_add_smul_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ t ∈ C.linSpan, ∃ c : R, c > 0 ∧ x + c • t ∈ C := by simp [relint]

lemma neg_mem_linSpan_of_mem {C : PointedCone R M} {x : M} (hc : x ∈ C) : -x ∈ C.linSpan := by
  simpa only [neg_mem_iff, restrictScalars_mem] using C.le_linSpan hc

lemma map_linSpan (f : M →ₗ[R] N) {C : PointedCone R M} :
    (C.map f).linSpan = C.linSpan.map f := by
  refine le_antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · obtain ⟨tp, ⟨sp, hsp, rfl⟩ , tn, ⟨sn, hsn, rfl⟩, ht⟩ := mem_linSpan.mp hy
    use (sp - sn), (mem_linSpan.2 ⟨sp, hsp, sn, hsn, by module⟩)
    simp at ht
    simp [ht]
  obtain ⟨x, hxC, hfx⟩ := hy
  obtain ⟨tp, htp , tn, htn, ht⟩ := mem_linSpan.mp hxC
  apply mem_linSpan.mpr
  use (f tp), ⟨tp, htp, rfl⟩, (f tn), ⟨tn, htn, rfl⟩
  simp [ht, hfx]

/-- Relint maps to relint. i dont think the assumption on f is necessary -/
theorem map_relint (f : M →ₗ[R] N) {C : PointedCone R M} (hf : f.ker ⊓ C.linSpan ≤ C.lineal) :
    (C.map f).relint = C.relint.map f := by
  refine le_antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · obtain ⟨⟨x, hxC, hfx⟩, hx⟩ := hy
    refine ⟨x, ⟨hxC, fun t ht ↦ ?_⟩, hfx⟩ -- this needs to be changed if we drop the condition on f
    obtain ⟨c, hc0, ⟨z, hzC, hz⟩⟩ := hx (f t) (by simpa [map_linSpan f] using ⟨t, ht, rfl⟩)
    use c, hc0
    simp only [LinearMap.coe_restrictScalars, SetLike.mem_coe] at hz hfx hzC hxC
    replace hxf : ((x + c • t) - z) ∈ f.ker := by simp [hz, hfx]
    have := sub_mem (C.linSpan.add_mem (C.le_linSpan hxC) <| C.linSpan.smul_mem c ht)
    <| C.le_linSpan hzC
    have : ((x + c • t) - z) ∈ C.lineal := by
      apply hf
      simp [hxf, this]
    rw [show x + c • t = ((x + c • t) - z) + z by module]
    exact C.add_mem (C.lineal_le this) hzC
  obtain ⟨x, ⟨hxC, hx⟩, hfx⟩ := hy
  refine ⟨⟨x, hxC , hfx⟩, fun t ht ↦ ?_⟩
  obtain ⟨tp, ⟨sp, hspC, rfl⟩, tn, ⟨sn, hsnC, rfl⟩, ht⟩ := mem_linSpan.1 ht
  apply sub_eq_of_eq_add at ht
  simp [← map_sub] at ht
  obtain ⟨c, hc0, hc⟩ := hx (sp - sn) (mem_linSpan.2 ⟨sp, hspC, sn, hsnC, by module⟩)
  use c, hc0, (x + c • (sp - sn)), hc
  simp [ht, hfx]

set_option backward.isDefEq.respectTransparency false in
lemma mem_relint_iff_mem_span_neg_eq_top :
    x ∈ C.relint ↔ x ∈ C ∧ span R (insert (-x) C) = C.linSpan := by
    constructor
    · refine fun ⟨hxC, hx⟩ ↦ ⟨relint_le ⟨hxC, hx⟩, ?_⟩
      apply le_antisymm
      · refine span_le.mpr <| Set.insert_subset ?_ Submodule.subset_span
        simpa using mem_span_of_mem <| relint_le ⟨hxC, hx⟩
      intro t ht
      obtain ⟨c, hc_pos, hc⟩ := hx t ht
      apply mem_span_insert.mpr
      simp only [span_coe_eq_restrictScalars, Submodule.restrictScalars_self, smul_neg,
        Subtype.exists, Nonneg.mk_smul, exists_prop]
      use c⁻¹, inv_nonneg_of_nonneg <| le_of_lt hc_pos, c⁻¹ • (x + c • t),
       C.smul_mem (inv_nonneg_of_nonneg <| le_of_lt hc_pos) hc
      simp [smul_smul]
      field_simp
      rw [one_smul]
    refine fun ⟨hxC, hx⟩ ↦ ⟨hxC, fun t ht ↦ ?_⟩
    replace ht : t ∈ span R (insert (-x) C) := by simp [hx, ht]
    obtain ⟨⟨a, ha0⟩, ha⟩ := mem_span_insert.mp ht
    simp only [span_coe_eq_restrictScalars, Submodule.restrictScalars_self, smul_neg,
      Nonneg.mk_smul] at ha
    obtain ⟨z, hzC, rfl⟩ := ha
    by_cases! h : a = 0
    · use 1
      simpa [h] using C.add_mem hxC hzC
    use a⁻¹
    simp [lt_of_le_of_ne ha0 h.symm, smul_smul]
    field_simp
    simpa using C.smul_mem (inv_nonneg_of_nonneg ha0) hzC

set_option backward.isDefEq.respectTransparency false in
lemma mem_relint_iff_mem_forall_isFaceOf_eq_top_of_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ F : PointedCone R M, F.IsFaceOf C → x ∈ F → F = C := by
  constructor
  · refine fun ⟨hxC, hx⟩ ↦ ⟨relint_le ⟨hxC, hx⟩, fun F hF hxF ↦ ?_⟩
    apply le_antisymm hF.1
    intro y hy
    obtain ⟨b, hb0, hb⟩ := hx (y-x) <| C.linSpan.sub_mem (C.le_linSpan hy) (C.le_linSpan hxC)
    by_cases! hb1 : 1 ≤ b
    · sorry --this uses convexity, should not be hard
    obtain ⟨a, ha0, ha⟩ := hx (x-y) <| C.linSpan.sub_mem (C.le_linSpan hxC) (C.le_linSpan hy)
    have : (a/b) • (x + b • (y - x)) + (x + a • (x - y)) = (1 + a/b) • x := by
      simp only [smul_add, smul_smul, add_smul, one_smul]
      field_simp
      module
    have hab : 0 < a/b := div_pos ha0 hb0
    have hxF' : (1 + a/b) • x ∈ F := F.smul_mem (le_of_lt <| add_pos zero_lt_one hab) hxF
    rw [← this] at hxF'
    have hxyF := (hF.2 hb ha hab hxF')
    rw [show x + b • (y - x) = b • y + (1-b) • x by module] at hxyF
    exact hF.2 hy (C.smul_mem (by linarith) hxC) hb0 hxyF
  refine fun ⟨hxC, hx⟩ ↦ ⟨hxC, fun t ht ↦ ?_⟩
  by_contra!
  sorry -- this might be very hard since we somehow need to construct a proper face containing x



lemma mem_relint_iff_mem_forall_face_eq_top_of_mem :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ F : Face C, x ∈ F → F = ⊤ := by
  sorry

variable [Fact p.SeparatingLeft] in
lemma mem_relint_iff_forall_dual_zero_le_mem_lineal_of_eq_zero :
    x ∈ C.relint ↔ x ∈ C ∧ ∀ y ∈ dual p C, p x y = 0 → y ∈ (dual p C).lineal := by
  constructor
  · refine fun ⟨hxC, hx⟩ ↦ ⟨relint_le ⟨hxC, hx⟩, fun y hy hpxy ↦ ⟨hy, ?_⟩⟩
    intro t ht
    obtain ⟨c, hc0, hc⟩ := hx (-t) (neg_mem_linSpan_of_mem ht)
    specialize hy hc
    simp only [smul_neg, map_add, _root_.map_neg, map_smul, add_apply, hpxy, neg_apply, smul_apply,
      smul_eq_mul, zero_add, Left.nonneg_neg_iff] at hy
    simp only [_root_.map_neg, Left.nonneg_neg_iff]
    nlinarith
  refine fun ⟨hxC, hx⟩ ↦ ⟨hxC, fun t ht ↦ ?_⟩
  by_contra!
  sorry



/- not sure what the correct assumption on C is. A counterexample without the assumption is
   the union of a halfspace and a ray -/
variable [Fact p.SeparatingLeft] in
lemma mem_relint_dual {y : N} (hC : DualClosed p C) :
    y ∈ (dual p C).relint ↔ y ∈ dual p C ∧ ∀ x ∈ C, p x y = 0 → x ∈ C.lineal := by
  constructor
  · refine fun ⟨hyC, hy⟩ ↦ ⟨relint_le ⟨hyC, hy⟩, fun x hx hpxy ↦ ⟨hx, ?_⟩⟩
    rw [← hC]
    intro t ht
    obtain ⟨c, hc0, hc⟩ := hy (-t) (neg_mem_linSpan_of_mem ht)
    specialize hc hx
    simp only [smul_neg, map_add, hpxy, _root_.map_neg, map_smul, smul_eq_mul, zero_add,
      Left.nonneg_neg_iff] at hc
    simp only [flip_apply, _root_.map_neg, Left.nonneg_neg_iff]
    nlinarith
  refine fun ⟨hyC, hy⟩ ↦ ⟨hyC, fun t ht ↦ ?_⟩
  sorry



lemma finset_sum_mem_relint_of_subset_of_le_span {s : Finset M} (hs : (s : Set M) ⊆ C)
    (hC : C ≤ Submodule.span R (s : Set M)) : ∑ x ∈ s, x ∈ relint C := by
  refine ⟨C.sum_mem hs, fun t ht ↦ ?_⟩
  apply (span_le.mpr hC : C.linSpan ≤ Submodule.span R s) at ht
  obtain ⟨f, _, rfl⟩ := mem_span_finset.1 ht
  obtain ⟨c, hc⟩ := bddBelow_iff_subset_Ici.mp (s.image f).bddBelow
  simp only [Finset.coe_image, Set.image_subset_iff] at hc
  by_cases! h : c ≥ 0
  · use 1, zero_lt_one
    apply C.add_mem <| C.sum_mem hs
    rw [one_smul]
    apply C.sum_mem fun x hx ↦ C.smul_mem (h.trans <| hc hx) (hs hx)
  use -c⁻¹, by simp [h]
  rw [s.smul_sum, ← s.sum_add_distrib]
  apply C.sum_mem fun x hx ↦ ?_
  nth_rw 1 [show x = (1 : R) • x by simp, smul_smul, ← add_smul]
  apply C.smul_mem ?_ (hs hx)
  simp only [neg_mul, le_add_neg_iff_add_le, zero_add]
  field_simp
  exact div_le_one_of_ge (hc hx) <| le_of_lt h

lemma finset_sum_mem_relint_span {s : Finset M} : ∑ x ∈ s, x ∈ relint (span R (s : Set M)) := by
  refine finset_sum_mem_relint_of_subset_of_le_span subset_span <| span_le.2 ?_
  simp only [Submodule.coe_restrictScalars, Submodule.subset_span]

/- When C has finite rank there exists a finite generating set for C.linSpan which is
   contained in C. -/
lemma genrating_set_of_FinRank {C : PointedCone R M} (hC : C.FinRank) :
    ∃ s : Finset M, (s : Set M) ⊆ C ∧ C.linSpan = .span R s := 
  (Submodule.fg_span_iff_fg_span_finset_subset (C : Set M)).mp hC

lemma relint_nonempty' (h : C.FinRank) : Nonempty C.relint := by
  obtain ⟨s, hs⟩ := genrating_set_of_FinRank h
  use ∑ x ∈ s, x
  apply finset_sum_mem_relint_of_subset_of_le_span hs.1
  simpa [hs.2] using C.le_linSpan

lemma relint_nonempty (h : C.FinSalRank) : Nonempty C.relint := by
  let f := C.lineal.mkQ
  suffices Nonempty C.salientQuot.relint by
    rw [map_relint] at this
    · simp only [ConvexCone.mem_map, mkQ_apply, nonempty_subtype, ↓existsAndEq, and_true] at this
      obtain ⟨x, hx⟩ := this
      exact ⟨x, hx⟩
    simp only [ker_mkQ, inf_le_left]
  exact relint_nonempty' h

 -- potential short proof of `IsExposedFace.exists_dual_pos`
variable (p) [Fact p.SeparatingLeft] in
example {C : PointedCone R M} (hCF : C.FinSalRank) (hC : C.DualClosed p) :
    ∃ φ : N, ∀ x ∈ C, 0 ≤ p x φ ∧ (p x φ = 0 → x ∈ C.lineal) := by
  obtain ⟨φ, hφ⟩ := relint_nonempty (hCF.dual_finSalRank p)
  rw [mem_relint_dual hC] at hφ
  exact ⟨φ, fun _ h => ⟨by simpa using hφ.1 h, hφ.2 _ h⟩⟩

lemma ofSubmodule_relint (S : Submodule R M) : (S : PointedCone R M).relint = S := by
  refine le_antisymm relint_le fun x hx ↦ ⟨hx, fun t ht ↦ ?_⟩
  use 1, zero_lt_one
  simp at ht hx
  simp [add_mem hx ht]

end PointedCone
