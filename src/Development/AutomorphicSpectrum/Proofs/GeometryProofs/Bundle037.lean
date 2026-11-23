module

import Development.WeilBound.CoreStatements.VolumeEquality.RegularFunctionChartAdjoin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordLoc

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hξ : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (f : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hξ).hom f) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have h2 := congrArg (fun g => g.hom f) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes q.2).hom
    ((X.presheaf.germ U q.1 hq).hom f)) = _
  rw [h2]

end GlobalTheory.CompanionTheory.Ar.CoordLoc

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_iff_exists_chart_fraction : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ) (p : Cpt ξ), InChart ξ x c p → ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ Algebra.adjoin o (Set.range fun j => x j / x c), unitAt ξ p s ∧ s * a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  apply SheetDecomposition.regular_function_chart_adjoin <;> assumption

end GlobalTheory.CompanionTheory.Ar
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.finite_open_hopf_order : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → ∃ (H : Subgroup T) (A : Subalgebra R (H → R)), (∀ t, t ∈ H ↔ ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U) ∧ IsHopfOrder A ∧ ∀ f : H → R, f ∈ A ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : H) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = algebraMap R _ (f t) := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)


theorem _root_.GlobalTheory.T.chart_bundle_lattice_generators : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap | exact GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)


theorem _root_.GlobalTheory.T.chart_bundle_local_generation : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)),
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O x i) ∧ (∀ l, c l ∈ chartRing O x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, ∃ b : Fin r → Fin r → Ω, LinearIndependent Ω b ∧
        Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e : Fin r → Ω,
          ((∃ n : ℕ, f l ^ n • e ∈ dotDual (chartRing O x i) (B.lat i)) ↔
            ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O x i) ∧ e = ∑ q, a q • b q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame | exact GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

namespace RootMono

theorem card_fiber {α : Type*} [DecidableEq α] (l : List α) (c : α) :
    Fintype.card {i : Fin l.length // l.get i = c} = l.count c := by
  rw [Fintype.card_subtype, Finset.card_filter]
  induction l with
  | nil => simp
  | cons a l ih =>
    have h := Fin.sum_univ_succ (n := l.length)
      (fun i : Fin (l.length + 1) => if (a :: l).get i = c then 1 else 0)
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at h ih
    simp only [List.get_eq_getElem, List.length_cons]
    rw [h, ih, List.count_cons]
    by_cases hac : a = c
    · simp [hac, add_comm]
    · simp [hac, add_comm]

theorem exists_perm_fin {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (h : l₁.Perm l₂) {n : ℕ} (hn : l₁.length = n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (i : Fin n) (h₁ : (i : ℕ) < l₁.length) (h₂ : (σ i : ℕ) < l₂.length),
      l₂[(σ i : ℕ)] = l₁[(i : ℕ)] := by
  subst hn
  have hc : ∀ c, Fintype.card {i : Fin l₁.length // l₁.get i = c} =
      Fintype.card {i : Fin l₂.length // l₂.get i = c} := fun c => by
    rw [card_fiber, card_fiber, h.count_eq]
  let e : Fin l₁.length ≃ Fin l₂.length := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c)
  have he : ∀ i, l₂.get (e i) = l₁.get i := Equiv.ofFiberEquiv_map _
  refine ⟨e.trans (finCongr h.length_eq.symm), fun i h₁ h₂ => ?_⟩
  simpa using he i

theorem length_toList {J : Type} (m : J →₀ ℕ) : (Finsupp.toMultiset m).toList.length = m.degree := by
  rw [Multiset.length_toList, Finsupp.card_toMultiset]
  simp only [Finsupp.sum, id]
  rfl

end RootMono


open RootMono in
theorem arMono_add_single (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem)
    (t : ℝ) (m : Ψ × Fin N →₀ ℕ) (r : Ψ × Fin N) (hII : IsIntersectionSystem II) (hm : m.degree = dimFl Ψ N) :
    M.arMono II t ((m + Finsupp.single r 1).mapDomain some) =
      II M.K M.ι M.P (dimFl Ψ N + 1)
        (Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r)) / (M.δ : ℝ) := by
  classical
  have hn : (m + Finsupp.single r 1).mapDomain some = m.mapDomain some + Finsupp.single (some r) 1 := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  have hdm : (m.mapDomain some).degree = dimFl Ψ N := by
    rw [Finsupp.degree_mapDomain, hm]
  have hdeg : ((m + Finsupp.single r 1).mapDomain some).degree = dimFl Ψ N + 1 := by
    rw [hn, map_add (f := _), hdm, Finsupp.degree_single]
  have hnone : ((m + Finsupp.single r 1).mapDomain some) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  have hperm : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.Perm
      ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList, hn, map_add (f := _)]
    simp
  have hlen₁ : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length = dimFl Ψ N + 1 := by
    rw [length_toList, hdeg]
  have hlen₀ : (Finsupp.toMultiset (m.mapDomain some)).toList.length = dimFl Ψ N := by
    rw [length_toList, hdm]
  have hsm : ∀ o, IsSmoothHerm (M.line t o) := by
    intro o
    cases o with
    | none => exact M.A_smooth
    | some b => exact M.x_smooth t b
  set L : Fin (dimFl Ψ N + 1) → HermLine M.ι :=
    Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r) with hL
  have hval : ∀ (j : Fin (dimFl Ψ N + 1))
      (hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length),
      L j = M.line t (((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[(j : ℕ)]) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro hj
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.last (dimFl Ψ N) : Fin _) : ℕ)] = some r := by
        simp [List.getElem_append, hlen₀]
      rw [this, hL, Fin.snoc_last]
      rfl
    · intro hj
      have hk : (k : ℕ) < (Finsupp.toMultiset (m.mapDomain some)).toList.length := by
        rw [hlen₀]; exact k.2
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.castSucc k : Fin _) : ℕ)] =
          (Finsupp.toMultiset (m.mapDomain some)).toList[(k : ℕ)] := by
        exact List.getElem_append_left hk
      rw [this, hL, Fin.snoc_castSucc]
      simp only [monoLines, dif_pos hk]
      rfl
  have hLs : ∀ j, IsSmoothHerm (L j) := by
    intro j
    have hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, j.2]
    rw [hval j hj]
    exact hsm _
  obtain ⟨σ, hσ⟩ := exists_perm_fin hperm hlen₁
  have hfun : monoLines (M.line t) ((m + Finsupp.single r 1).mapDomain some) (dimFl Ψ N + 1) = L ∘ σ := by
    funext i
    have h₁ : (i : ℕ) < (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length := by
      rw [hlen₁]; exact i.2
    have h₂ : (σ i : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, (σ i).2]
    simp only [monoLines, dif_pos h₁, Function.comp, hval (σ i) h₂, hσ i h₁ h₂]
    rfl
  unfold RootModel.arMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one, hfun]
  congr 1
  exact (hII M.K M.ι).1 M.P (dimFl Ψ N + 1) L σ M.arith hLs

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem line_smooth_at (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem line_a_eq (M : RootModel Ψ N) (t s : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line s j).a := by
  cases j with
  | none => rfl
  | some r => exact (M.x_deg t r).trans (M.x_deg s r).symm

theorem monoLines_line_smooth (M : RootModel Ψ N) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (k : Fin d) :
    IsSmoothHerm (monoLines (M.line t) m d k) := by
  unfold monoLines
  split_ifs with h
  · exact line_smooth_at M t _
  · exact contDiffOn_const

theorem monoLines_line_a (M : RootModel Ψ N) (t s : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (k : Fin d) :
    (monoLines (M.line t) m d k).a = (monoLines (M.line s) m d k).a := by
  unfold monoLines
  split_ifs with h
  · exact line_a_eq M t s _
  · rfl

theorem ptsIntegral_line_eq (hD : DegreeStatement) (M : RootModel Ψ N) (t s : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    ptsIntegral M.P (pot (monoLines (M.line t) m (dimFl Ψ N))) (fun _ => 1) =
      ptsIntegral M.P (pot (monoLines (M.line s) m (dimFl Ψ N))) (fun _ => 1) := by
  rw [hD M.K M.ι M.P (dimFl Ψ N) _ 2 M.arith (monoLines_line_smooth M t m _) Nat.prime_two,
    hD M.K M.ι M.P (dimFl Ψ N) _ 2 M.arith (monoLines_line_smooth M s m _) Nat.prime_two]
  simp only [monoLines_line_a M t s m]

theorem geoMono_eq (hD : DegreeStatement) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ)
    (m : Ψ × Fin N →₀ ℕ) (hm : m.degree = dimFl Ψ N) :
    ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (fun _ => 1) / (M.δ : ℝ) =
      M.geoMono (m.mapDomain some) := by
  have hdeg : (m.mapDomain some).degree = dimFl Ψ N := by
    rw [Finsupp.degree_mapDomain, hm]
  have hnone : (m.mapDomain some) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  rw [ptsIntegral_line_eq hD M t 1]
  unfold RootModel.geoMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstReg

theorem stalkClosedPointTo_germ_top {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ ⊤ (genPt ξ) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (ξ.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (genPt ξ) trivial ≫ Scheme.stalkClosedPointTo ξ =
      ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
    refine (Scheme.germ_stalkClosedPointTo ξ ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem genMap_germ_const {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) {O : Type} [CommRing O] [Algebra O Ω]
    (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (p : Cpt ξ) (o : O) :
    genMap ξ p ((X.presheaf.germ ⊤ p.1 trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = algebraMap O Ω o := by
  have h1 : genMap ξ p ((X.presheaf.germ ⊤ p.1 trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ ⊤ (genPt ξ) trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, stalkClosedPointTo_germ_top]
  have h2 : ξ.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom (algebraMap O Ω))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hs]; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom o)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O Ω)))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (algebraMap O Ω o) =
      (Spec.map (CommRingCat.ofHom (algebraMap O Ω))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  rw [← h3']
  simp

theorem isUnit_germ_const_iff {X : Scheme.{0}} {O : Type} [CommRing O]
    (s : X ⟶ Spec (CommRingCat.of O)) (x : X) (o : O) :
    IsUnit ((X.presheaf.germ ⊤ x trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) ↔ o ∉ (s x).asIdeal := by
  rw [← Scheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top, Scheme.Hom.mem_preimage,
    basicOpen_eq_of_affine (R := CommRingCat.of O) o]
  exact Iff.rfl

theorem regular_const : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)), ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p ∧ (IsCptGen ξ → (unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal)) := by
  intro X Ω _ ξ O _ _ _ s hs p o
  have hg := genMap_germ_const ξ s hs p o
  refine ⟨⟨_, hg⟩, fun hc => ?_⟩
  rw [← isUnit_germ_const_iff s p.1 o]
  constructor
  · intro hu
    obtain ⟨u, hu, e⟩ := (unitAt_iff_of_isCptGen ξ hc p _).1 hu
    rwa [← hc.inj p (e.trans hg.symm)]
  · intro hu
    rw [← hg]
    exact RegAtMono.unitAt_of_isUnit ξ p hu

end GlobalTheory.CompanionTheory.Ar.Flat.ConstReg
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem mem_of_finite_of_closedFibre {R : Type} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  haveI := hY
  haveI : IsIso (⊤ : Y.left.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  have hfin : IsFinite ((⊤ : Y.left.Opens).ι ≫ Y.hom) := inferInstance
  have hle := GlobalTheory.T.finite_open_le_closed_fibre R Y.left Y.hom ⊤ (h.left ⁻¹ᵁ W) hfin (fun x hx => by
    apply hW
    have hw : h.left ≫ X.hom = Y.hom := Over.w h
    have hc := Scheme.Hom.comp_apply h.left X.hom x
    rw [hw] at hc
    rw [← hc]
    exact hx)
  exact hle (show z ∈ (⊤ : Y.left.Opens) from trivial)

abbrev openOver {S : Scheme.{0}} (X : Over S) (U : X.left.Opens) : Over S := Over.mk (U.ι ≫ X.hom)

abbrev openIncl {S : Scheme.{0}} (X : Over S) (U : X.left.Opens) : openOver X U ⟶ X := Over.homMk U.ι rfl

theorem exists_factor_openIncl {S : Scheme.{0}} {X Y : Over S} (U : X.left.Opens) (x : Y ⟶ X)
    (hx : ∀ z, x.left z ∈ U) : ∃ x' : Y ⟶ openOver X U, x' ≫ openIncl X U = x := by
  have hr : Set.range x.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hx z
  have hc : IsOpenImmersion.lift U.ι x.left hr ≫ U.ι = x.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι x.left hr) ?_, ?_⟩
  · simp only [Over.mk_hom]
    rw [← Category.assoc, hc]
    exact Over.w x
  · ext1
    exact hc

theorem QFGroup.isFinOpenSub_of_closedFibre :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
      (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) →
      (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  intro R _ _ _ T _ Γ U hfin hU
  haveI := hfin
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  haveI := hV
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite_of_closedFibre U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite_of_closedFibre U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite_of_closedFibre U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → Γ.btOrder U = Γ.btOrder U' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_base_change_action : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (O : Type) [CommRing O] (act : OAct O G) (act' : OAct O G'), (∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → Submodule.span L' (Set.range j) = ⊤ → ∀ ρ : O →+* Module.End L V, MV.IsActOf act.act ρ → ∃ ρ' : O →+* Module.End L' V', MV'.IsActOf act'.act ρ' ∧ ∀ a x, ρ' a (j x) = j (ρ a x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends | exact GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends | (intros; apply GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torsion_pullback_correspondence : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (N : ℕ), IsGrpPullback G₀ G x ψ → (∀ i : Γ.G.left ⟶ G.left, Γ.IsTorsionAlong G x N i → ∃ i₀ : Γ.G.left ⟶ G₀.left, i₀ ≫ ψ = i ∧ Γ.IsTorsionAlong G₀ (𝟙 _) N i₀) ∧ ∀ i₀ : Γ.G.left ⟶ G₀.left, Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ → Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.torsionAlong_iff_pullback_torsion | exact GlobalTheory.CompanionTheory.Ar.torsionAlong_iff_pullback_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.torsionAlong_iff_pullback_torsion <;> assumption)
end
