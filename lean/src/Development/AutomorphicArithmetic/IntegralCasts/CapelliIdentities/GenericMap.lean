import Mathlib

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Reformulated.B.GenericMap

noncomputable section

variable {X : Scheme.{0}} {Ω : Type} [inst : Field Ω]

theorem aux1 : IsLocalRing Ω := inferInstance

def genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : X := ξ (IsLocalRing.closedPoint Ω)

def Cpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) := {p : X // genPt ξ ⤳ p}

variable (ξ : Spec (CommRingCat.of Ω) ⟶ X)

theorem aux4 (p : Cpt ξ) : genPt ξ ⤳ p.1 := p.2

theorem aux5 : IsLocalRing (CommRingCat.of Ω) := inferInstance

def genMap (p : Cpt ξ) : X.presheaf.stalk p.1 →+* Ω :=
  (X.presheaf.stalkSpecializes (aux4 ξ p) ≫ Scheme.stalkClosedPointTo ξ).hom

def regAt (p : Cpt ξ) : Subring Ω := (genMap ξ p).range

def unitAt (p : Cpt ξ) (a : Ω) : Prop := a ≠ 0 ∧ a ∈ regAt ξ p ∧ a⁻¹ ∈ regAt ξ p

def InFibre (p : ℕ) (q : Cpt ξ) : Prop := ¬unitAt ξ q (p : Ω)

def Char0 (p : Cpt ξ) : Prop := ∀ r : ℕ, r.Prime → ¬InFibre ξ r p

namespace Hlp

private theorem units_nat {Ω : Type} [Field Ω] (S : Subring Ω)
    (hp : ∀ r : ℕ, r.Prime → ((r : Ω) ≠ 0 ∧ (r : Ω) ∈ S ∧ (r : Ω)⁻¹ ∈ S)) :
    ∀ n : ℕ, n ≠ 0 → ((n : Ω) ≠ 0 ∧ (n : Ω) ∈ S ∧ (n : Ω)⁻¹ ∈ S) := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp [S.one_mem]
  | prime p hpp => intro _; exact hp p hpp
  | mul a b ha hb =>
    intro hab
    have ha0 : a ≠ 0 := fun h => hab (by simp [h])
    have hb0 : b ≠ 0 := fun h => hab (by simp [h])
    obtain ⟨a1, a2, a3⟩ := ha ha0
    obtain ⟨b1, b2, b3⟩ := hb hb0
    refine ⟨by push_cast; exact mul_ne_zero a1 b1, by push_cast; exact S.mul_mem a2 b2, ?_⟩
    push_cast; rw [mul_inv]; exact S.mul_mem a3 b3
end Hlp

theorem main {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ} :
    Char0 ξ q → ∀ n : ℕ, n ≠ 0 → unitAt ξ q (n : Ω) :=
  fun h => Hlp.units_nat (regAt ξ q) (fun r hr => not_not.mp (h r hr))

end
end UpperTheory.Reformulated.B.GenericMap
