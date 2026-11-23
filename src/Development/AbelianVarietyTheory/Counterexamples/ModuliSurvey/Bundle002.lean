module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

noncomputable section
namespace GlobalTheory.ModuliProbe
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem zeta_prim (n : ℕ) (hn : 0 < n) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn.ne'

theorem le_of_conj (l : Level H) (F : IntermediateField ℚ ℂ) (hc : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F)
    (hz : zeta l.M' ∈ F) : KA l ≤ F := by
  rw [KA, IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    have h1 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, h0, H.sqrt_neg_disc_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · rw [← h]; exact hc τ _
    · have : H.rt0 = τ (-(H.rt : E)) := by rw [map_neg, h, neg_neg]
      rw [this]; exact hc τ _
  · have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
    haveI : NeZero l.M' := ⟨hM.ne'⟩
    have hp : zeta l.A ^ l.M' = 1 := by
      obtain ⟨c, hc⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
      rw [hc, pow_mul, (zeta_prim _ l.A_pos).pow_eq_one, one_pow]
    obtain ⟨i, -, hi⟩ := (zeta_prim _ hM).eq_pow_of_pow_eq_one hp
    rw [← hi]
    exact pow_mem hz i

theorem coeff_nonempty (l : Level H) : Nonempty (Coeff l) := by
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  let F : IntermediateField ℚ ℂ :=
    IntermediateField.normalClosure ℚ E ℂ ⊔ IntermediateField.adjoin ℚ {zeta l.M'}
  have hc : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F := fun τ a =>
    (le_sup_left : _ ≤ F) (AlgHom.fieldRange_le_normalClosure τ.toRatAlgHom ⟨a, rfl⟩)
  have hz : zeta l.M' ∈ F := (le_sup_right : _ ≤ F) (IntermediateField.mem_adjoin_simple_self _ _)
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l.M'}) :=
    IntermediateField.adjoin.finiteDimensional ((zeta_prim _ hM).isIntegral hM).tower_top
  exact ⟨⟨F, inferInstance, hc, hz, le_of_conj l F hc hz⟩⟩

end GlobalTheory.ModuliProbe
end
end

section

noncomputable section

namespace GlobalTheory.ModelRelProbe

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem j_over {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  unfold Model.j
  rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.ModelRelProbe
end
end

section

noncomputable section

namespace GlobalTheory.ModelScope

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem range_j_subset_abLocus (Y : Model Xo c β) : Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨x, rfl⟩
  have h : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨x, rfl⟩
  exact h

end GlobalTheory.ModelScope
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.RelTests

section Ext
variable {V W : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]

end Ext

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem isNsmul_b {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, hl⟩ := H
  have key : ∀ (n : ℕ) (hn : n < k + 1), (gs ⟨n, hn⟩).b = g.b ^ n := by
    intro n
    induction n with
    | zero => intro hn; rw [pow_zero]; exact h0.1
    | succ n ih =>
      intro hn
      have e := (hs ⟨n, by omega⟩).1
      rw [pow_succ, ← ih (by omega)]
      exact e
  rw [← hl]
  exact key k (Nat.lt_succ_self k)

end Tors

end GlobalTheory.UU.RelTests
end
end
