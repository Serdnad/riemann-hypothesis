module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem intNumL_perm_of_perm (F : Type) [Field F] (K : Type) [DecidableEq K] (ι : K → Type)
    (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)) (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  haveI : LeftCommutative (diffStep : (K → ℤ) → ((K → ℤ) → ℤ) → ((K → ℤ) → ℤ)) := by
    constructor
    intro a b g
    funext m
    simp only [diffStep]
    rw [sub_right_comm m a b]
    ring
  unfold intNumL intNum GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff
  rw [List.ofFn_get, List.ofFn_get, h.foldr_eq]

theorem numbers_list_perm : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (MRing ι O) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  refine ⟨fun F _ K _ _ ι _ V l l' h => intNumL_perm_of_perm F K ι V l l' h, ?_⟩
  intro O _ _ _ K _ _ ι _ Z l l' h
  unfold cycList
  congr 1
  funext W
  exact intNumL_perm_of_perm _ K ι (specialIdeal W) l l' h

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.CkAppend

theorem classList_mapDomain_eq {K σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (Finsupp.mapDomain e μ) = classList (cls ∘ e) μ := by
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_rename_eq {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (he : Function.Injective e)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he, classList_mapDomain_eq]

theorem psumExpansion_rename (N k : ℕ) (i : Fin N) :
    psumExpansion N k i =
      rename (Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)) (psumExpansion 1 k 0) := by
  simp [psumExpansion]

theorem pairNum_psumExpansion {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {N : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin N → K → ℤ)
    (f g : Fin N → MRing ι O) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P x x' f g (psumExpansion N k) Q =
      ∑ i, pairNum P (fun _ : Fin 1 => x i) (fun _ => x' i) (fun _ => f i) (fun _ => g i)
        (psumExpansion 1 k) Q := by
  unfold pairNum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_one]
  have he : Function.Injective (Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)) :=
    Sum.map_injective.mpr ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  have hc : Sum.elim x x' ∘ Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i) =
      Sum.elim (fun _ : Fin 1 => x i) (fun _ : Fin 1 => x' i) := by
    funext s
    rcases s with s | s <;> rfl
  simp only [psumExpansion_rename N k i, classNum_rename_eq _ _ he, hc]

theorem ck_append : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (j j' : ℕ) (T : LocPair ι O (Fin (j + j')))
    (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)),
    T.ck P k Q = (T.comp (Fin.castAdd j')).ck P k Q + (T.comp (Fin.natAdd j)).ck P k Q := by
  intro O _ _ _ K _ _ ι _ j j' T P k Q
  unfold LocPair.ck
  rw [pairNum_psumExpansion, pairNum_psumExpansion, pairNum_psumExpansion, Fin.sum_univ_add]
  rfl

end GlobalTheory.CompanionTheory.Ar.Num.CkAppend
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num.RootPerm

theorem classList_mapDomain {K σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (Finsupp.mapDomain e μ) = classList (cls ∘ e) μ := by
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_rename {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (he : Function.Injective e)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he, classList_mapDomain]

theorem rename_psumExpansion {r : ℕ} (e : Equiv.Perm (Fin r)) (k : ℕ) (i : Fin r) :
    rename (Sum.map e e) (psumExpansion r k i) = psumExpansion r k (e i) := by

  simp [psumExpansion, map_sum, rename_X]

theorem root_perm : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (r : ℕ) (e : Equiv.Perm (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), (∀ (a : O) (x : Fin r → K → ℤ), laNum P a (x ∘ e) k Q = laNum P a x k Q) ∧ ∀ T : LocPair ι O (Fin r), (T.comp e).ck P k Q = T.ck P k Q := by
  intro O _ _ _ K _ _ ι _ r e P k Q
  refine ⟨fun a x => ?_, fun T => ?_⟩
  · have h : ∀ W : Ideal (MRing ι O), classNum (x ∘ e) (psum (Fin r) ℤ (k - 1)) Q W =
        classNum x (psum (Fin r) ℤ (k - 1)) Q W := fun W => by
      rw [← classNum_rename x e e.injective, rename_psum]
    simp only [laNum, h]
  · have h : ∀ (i : Fin r) (W : Ideal (MRing ι O)),
        classNum (Sum.elim (T.x ∘ e) (T.x' ∘ e)) (psumExpansion r k i) Q W =
          classNum (Sum.elim T.x T.x') (psumExpansion r k (e i)) Q W := fun i W => by
      have hc : Sum.elim T.x T.x' ∘ Sum.map e e = Sum.elim (T.x ∘ e) (T.x' ∘ e) := by
        funext s
        rcases s with s | s <;> rfl
      rw [← rename_psumExpansion, classNum_rename _ _ (Sum.map_injective.mpr ⟨e.injective, e.injective⟩), hc]
    simp only [LocPair.ck, pairNum, LocPair.comp, Function.comp_apply, h]
    exact Equiv.sum_comp e fun j => cycEval (fun W => classNum (Sum.elim T.x T.x') (psumExpansion r k j) Q W)
      (ratDiv P (T.f j) (T.g j))

end GlobalTheory.CompanionTheory.Ar.Num.RootPerm
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ConsPoly

theorem length_classList {K σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = m := by
  have h := hH (mem_support_iff.mp hμ)
  rw [← h]
  simp [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply, Finsupp.sum]

theorem cycList_const {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hM : IsModelOver P l.length) (u : Oˣ) (e : ℕ) :
    cycList (divCycle P (C ((u : O) * ϖ ^ e))) l =
      (e : ℤ) * intNumL (FractionRing O) (genFib P) l := by
  haveI : P.IsPrime := hM.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P := by
    intro a ha hmem
    apply ha
    have ha' : a ∈ P.comap (C : O →+* MRing ι O) := Ideal.mem_comap.2 hmem
    rw [hM.noTorsion] at ha'
    exact Ideal.mem_bot.1 ha'
  have hfin := ScalarQuotient.divCycle_support_finite P (C ϖ)
  have key : cycEval (fun W => vNumL W l) (divCycle P (C ϖ)) =
      intNumL (FractionRing O) (genFib P) l :=
    ConservationOfNumber.full O ϖ hϖ K ι P l.length hM l.get
  unfold cycList
  rw [ScalarQuotient.divCycle_const P hC hϖ.ne_zero u e, ← key]
  unfold cycEval
  show ∑ᶠ W, ((e : ℤ) * divCycle P (C ϖ) W) * vNumL W l =
    (e : ℤ) * ∑ᶠ W, divCycle P (C ϖ) W * vNumL W l
  rw [mul_finsum]
  · exact finsum_congr fun W => by ring
  all_goals exact hfin.subset (Function.support_mul_subset_left _ _)

end GlobalTheory.CompanionTheory.Ar.Num.ConsPoly


open GlobalTheory.CompanionTheory.Ar.Num.ConsPoly in
theorem GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (u : Oˣ) (e : ℕ) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (divCycle P (C ((u : O) * ϖ ^ e))) cls H Q = (e : ℝ) * genNum (FractionRing O) (genFib P) cls H Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hM u e σ cls H m hH Q hd
  unfold cycNum genNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : (classList cls μ ++ Q).length = d := by
    rw [List.length_append, GlobalTheory.CompanionTheory.Ar.Num.ConsPoly.length_classList cls hH hμ, hd]
  have hM' : IsModelOver P (classList cls μ ++ Q).length := by
    rw [hlen]
    exact hM
  rw [GlobalTheory.CompanionTheory.Ar.Num.ConsPoly.cycList_const hϖ _ hM' u e]
  push_cast
  ring
end
