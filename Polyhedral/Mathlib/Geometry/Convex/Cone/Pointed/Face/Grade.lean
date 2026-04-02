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
import Mathlib.Order.Grade

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.MinkowskiWeyl
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Rank
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice
import Polyhedral.Polyhedral.Basic
-- import Polyhedral.Hyperplane
-- import Polyhedral.Halfspace

open Module



-- ## PREDICATE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

-- ...

end PointedCone




-- ## BUNDLED STRUCTURE

namespace PointedCone

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}
variable {C F F₁ F₂ : PointedCone R M}

-- My impression is someone should first implement the grading for the lattice of submodules.
-- (if not already done). This here is then a simple derivate thereof.

#check Submodule.finrank_strictMono
#check IsFaceOf.iff_le_of_isFaceOf

omit [FiniteDimensional R M] in
lemma test' {F : Face C} : (F : PointedCone R M).linSpan = F.span := by
  apply le_antisymm <;> exact Submodule.span_le.mpr Submodule.subset_span

omit [FiniteDimensional R M] in
lemma test {F G : Face C} : F ≤ G ↔ F.span ≤ G.span := by
  refine ⟨Submodule.span_mono, fun hFG x hx ↦ ?_⟩
  have hxC : x ∈ C := F.isFaceOf.le hx
  have : x ∈ G.span := hFG <| Submodule.mem_span_of_mem hx
  rw [← test', G.isFaceOf.mem_linSpan_iff_mem hxC] at this
  simpa

omit [FiniteDimensional R M] in
lemma test'' {F G : Face C} : F = G ↔ F.span = G.span := by
  refine ⟨fun h ↦ by rw[h], fun h ↦ ?_⟩
  exact le_antisymm (test.mpr <| le_of_eq h) (test.mpr <| le_of_eq h.symm)

lemma salFinrank_strictMono (C : PointedCone R M) : -- (hC : C.IsPolyhedral) :
    StrictMono fun F : Face C => salFinrank (F : PointedCone R M) := by
  intro F G hFG
  have : (F : PointedCone R M).IsFaceOf G :=
   (F.isFaceOf.iff_le_of_isFaceOf G.isFaceOf).mpr <| le_of_lt hFG
  simp only [finRank_of_isNoetherian, this.salFinrank_eq_salFinrank_add_finrank_quot_linSpan,
    lt_add_iff_pos_right, gt_iff_lt]
  by_contra! h
  simp only [nonpos_iff_eq_zero, Submodule.finrank_eq_zero, linSpan_quot] at h
  have := LinearMap.le_ker_iff_map.mpr h
  simp only [Submodule.ker_mkQ] at this
  have : G.span ≤ F.span := by rwa [← test', ← test']
  rw [test''.mpr <| le_antisymm this <| test.mp (le_of_lt hFG)] at hFG
  simp at hFG

lemma salFinrank_covBy {C : PointedCone R M} (hC : C.IsPolyhedral) (F G : Face C) (hFG : F ⋖ G) :
    salFinrank (F : PointedCone R M) ⋖ salFinrank (G : PointedCone R M) := by
  have : (F : PointedCone R M).IsFaceOf G :=
   (F.isFaceOf.iff_le_of_isFaceOf G.isFaceOf).mpr <| le_of_lt hFG.lt
  simp only [finRank_of_isNoetherian, this.salFinrank_eq_salFinrank_add_finrank_quot_linSpan,
    Nat.covBy_iff_add_one_eq, Nat.add_left_cancel_iff]
  apply le_antisymm
  · by_contra! h
    simp only [Nat.lt_one_iff, Submodule.finrank_eq_zero, linSpan_quot] at h
    replace hFG := hFG.lt
    have := LinearMap.le_ker_iff_map.mpr h
    simp only [Submodule.ker_mkQ] at this
    have : G.span ≤ F.span := by rwa [← test', ← test']
    rw [test''.mpr <| le_antisymm this <| test.mp hFG.le] at hFG
    simp at hFG
  by_contra! h
  apply Nat.succ_le_of_lt at h
  simp at h
  sorry






noncomputable instance {C : PointedCone R M} (hC : C.IsPolyhedral) : GradeOrder ℕ (Face C) where
  grade F := salFinrank (F : PointedCone R M)
  grade_strictMono := salFinrank_strictMono C
  covBy_grade := salFinrank_covBy hC


end PointedCone
