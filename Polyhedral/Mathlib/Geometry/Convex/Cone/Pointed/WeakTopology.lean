import Polyhedral.Mathlib.Algebra.Module.Submodule.FGDual
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
import Mathlib.Topology.Algebra.Module.WeakBilin
import Mathlib.Topology.Order.Basic

namespace PointedCone

open Module Function

variable {R M N : Type*}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [TopologicalSpace R] [OrderTopology R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable (p : M →ₗ[R] N →ₗ[R] R) -- bilinear pairing
variable [Fact p.SeparatingLeft]

variable (C : PointedCone R (WeakBilin p))

def cast : Set M → Set (WeakBilin p) := fun a ↦ a

lemma closed_of_halfspace {y : N} {a : R} :
    IsClosed {x : WeakBilin p | a ≤ p x y} :=
  isClosed_le continuous_const <| WeakBilin.eval_continuous p y

lemma closed_of_halfspace' {y : N} {a : R} :
    IsClosed {x : WeakBilin p | p x y ≤ a} :=
  isClosed_le (WeakBilin.eval_continuous p y) continuous_const

lemma open_of_open_halfspace {y : N} {a : R} :
    IsOpen {x : WeakBilin p | a < p x y} :=
  isOpen_lt continuous_const <| WeakBilin.eval_continuous p y

lemma open_of_open_halfspace' {y : N} {a : R} :
    IsOpen {x : WeakBilin p | p x y < a} :=
  isOpen_lt (WeakBilin.eval_continuous p y) continuous_const

set_option backward.isDefEq.respectTransparency false in
lemma closed_dual (s : Set N) :
    IsClosed (cast p (dual p.flip s)) := by
  simp only [cast, dual, LinearMap.flip_apply, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk,
    AddSubsemigroup.coe_set_mk]
  have : {y : M | ∀ ⦃x : N⦄, x ∈ s → 0 ≤ (p y) x} = ⋂ x ∈ s, {y : WeakBilin p | 0 ≤ (p y) x} :=
    Set.ext fun y ↦
    ⟨fun h ↦ Set.mem_iInter₂_of_mem h, fun h x hx ↦ Set.mem_iInter.1 (Set.mem_iInter.1 h x) hx⟩
  rw [this]
  exact isClosed_biInter fun _ _ ↦ closed_of_halfspace p

lemma closed_of_dualClosed (hC : DualClosed p C) :
    IsClosed C.carrier := by
  rw [← hC]
  change IsClosed (cast p (dual p.flip _ : Set M))
  exact closed_dual p _

set_option backward.isDefEq.respectTransparency false in
instance instT2Space : T2Space (WeakBilin p) := {
  t2 := by
    intro x y hxy
    obtain ⟨z, hz⟩ : ∃ z, p x z ≠ p y z := by
      by_contra! h
      replace h : ∀ z, p (x-y) z = 0 := fun z ↦ by rw [p.map_sub, (p x).sub_apply, h z, sub_self]
      have mem_ker : x-y ∈ p.ker := p.mem_ker.mpr <| (p (x-y)).ext_iff.mpr h
      apply sub_ne_zero_of_ne hxy
      have : p.ker = 0 := LinearMap.SeparatingLeft.ker_eq_bot
      rw [this] at mem_ker
      simpa only [Submodule.zero_eq_bot]
    wlog hxy : p x z < p y z generalizing z
    · specialize this (-z)
      simp only [not_lt] at hxy
      simp [hz, lt_of_le_of_ne hxy hz.symm] at this
      simpa
    use {u : WeakBilin p | p u z < (p x z + p y z)/2},
     {u : WeakBilin p | (p x z + p y z)/2 < p u z},
     open_of_open_halfspace' p, open_of_open_halfspace p
    field_simp
    simp only [Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    refine Set.disjoint_left.mpr fun u hu hu' ↦ ?_
    have := by calc
      p u z * 2 < _ := hu
      _ < 2 * p u z := hu'
      _ = p u z * 2 := by ring
    linarith
}

instance instProperSpace : ProperSpace (WeakBilin p) := {
  proper := by
    intro K hK
    rw [isCompact_iff_ultrafilter_le_nhds]
    intro f hf
    have : ∃ x, f ≤ 𝓝 x := by
      haveI : Nonempty (Subtype (λ x : WeakBilin p => f ≤ 𝓝 x)) := ⟨⟨_, hf⟩⟩
      exact Subtype.exists_of_nonempty
    obtain ⟨x, hx⟩ := this
    use x
    exact hx
}

lemma compact_of_closed (S : Set (WeakBilin p)) (hS : IsClosed S) :
    IsCompact S := by
  apply isCompact

end PointedCone
