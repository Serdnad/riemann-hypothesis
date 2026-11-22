import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

namespace UpperTheory.Reformulated.B.Qe28

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    {r : ℕ} {Comp : Type}

@[reducible] def FDSec (X : Comp → Data E r) := (c : Comp) → Frame (X c).Ψ r → ℂ

def IsHolCusp (X : Comp → Data E r) (la : (c : Comp) → Wt (X c).Ψ r) (P : FDSec X) : Prop :=
  ∀ c, P c ∈ (X c).SS (la c)

noncomputable def holSub (X : Comp → Data E r) (la : (c : Comp) → Wt (X c).Ψ r) : Submodule ℂ (FDSec X) :=
  Submodule.span ℂ {P | IsHolCusp X la P}

theorem holSub_mul : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    {r : ℕ}, SiegelSpaceAlgebra (E := E) → ∀ {Comp : Type} {X : Comp → Data E r}
      {la la' : (c : Comp) → Wt (X c).Ψ r} {P Q : FDSec X},
      P ∈ holSub X la → Q ∈ holSub X la' → P * Q ∈ holSub X (la + la') := by
  intro E _ _ _ r h5 Comp X la la' P Q hP hQ
  have key : ∀ (l : (k : Comp) → Wt (X k).Ψ r) (R : FDSec X),
      R ∈ holSub X l → IsHolCusp X l R := by
    intro l R hR
    induction hR using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact fun c => (h5 r (X c) (l c) (l c) 0).1.1
    | add x y _ _ hx hy => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.1 _ (hx c) _ (hy c)
    | smul a x _ hx => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.2 a _ (hx c)
  exact Submodule.subset_span fun c =>
    (h5 r (X c) (la c) (la' c) 0).2.1 _ (key la P hP c) _ (key la' Q hQ c).1

end UpperTheory.Reformulated.B.Qe28
