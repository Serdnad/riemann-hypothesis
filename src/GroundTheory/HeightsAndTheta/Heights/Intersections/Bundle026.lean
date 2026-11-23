module

import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle023
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle018
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section Semiloc

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def semiLocRing (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) : Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u w : MRing ι) (a : K → ℕ)
    (hw : Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P)),
    (∀ W ∈ 𝒲, w ∉ W) ∧ IsMultiHomog u a ∧ IsMultiHomog w a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hw⟩}

end Semiloc

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def fibreOver (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (W : Ideal (MRing ι)) :
    Set (Ideal (MRing ι')) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ imageZ v W' = W}


open Classical in
theorem rename_isMultiHomog {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename v f) (Function.extend κ a 0) := by
  apply GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.isMultiHomog_rename <;> assumption

abbrev quotMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    MRing ι ⧸ imageZ v P' →+* MRing ι' ⧸ P' :=
  Ideal.quotientMap P' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom le_rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem quotMapZ_injective (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    Function.Injective (quotMapZ v P') :=
  Ideal.quotientMap_injective


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem imageZ_isPrime_of_prime (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    (imageZ v P').IsPrime :=
  Ideal.comap_isPrime _ _

def fracMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    FractionRing (MRing ι ⧸ imageZ v P') →+* FractionRing (MRing ι' ⧸ P') :=
  haveI := imageZ_isPrime_of_prime v P'
  IsFractionRing.lift (g := (algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ v P'))
    ((IsFractionRing.injective (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ_injective v P'))

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem fracMapZ_algebraMap (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] (f : MRing ι) :
    fracMapZ v P' (algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename v f)) := by
  have := imageZ_isPrime_of_prime v P'
  unfold fracMapZ
  rw [IsFractionRing.lift_algebraMap]
  rfl

theorem fracMapZ_mem {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ imageZ v P'))
    (hx : x ∈ locRing (imageZ v P') W) : fracMapZ v P' x ∈ semiLocRing P' (fibreOver v P' W) := by
  have := imageZ_isPrime_of_prime v P'
  have hle : locRing (imageZ v P') W ≤ (semiLocRing P' (fibreOver v P' W)).comap (fracMapZ v P') := by
    rw [locRing, Subring.closure_le]
    rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_comap]
    have hw0 : rename v w ∉ P' := by
      intro h
      apply nonZeroDivisors.ne_zero hw
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact h
    have hw' : Ideal.Quotient.mk P' (rename v w) ∈ nonZeroDivisors (MRing ι' ⧸ P') :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    apply Subring.subset_closure
    refine ⟨rename v u, rename v w, Function.extend κ a 0, hw', ?_, rename_isMultiHomog hv hu,
      rename_isMultiHomog hv hwa, ?_⟩
    · rintro W' ⟨-, -, hW'⟩ hmem
      apply hwW
      rw [← hW']
      exact hmem
    · rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀]
      exact congrArg₂ (· / ·) (fracMapZ_algebraMap v P' u) (fracMapZ_algebraMap v P' w)
  exact hle hx

def locToSemiloc {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) :
    locRing (imageZ v P') W →+* semiLocRing P' (fibreOver v P' W) :=
  (fracMapZ v P').restrict _ _ (fun x hx => fracMapZ_mem hv P' W x hx)

theorem locToSemiloc_coe {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : locRing (imageZ v P') W) :
    ((locToSemiloc hv P' W x : semiLocRing P' (fibreOver v P' W)) : FractionRing (MRing ι' ⧸ P')) =
      fracMapZ v P' x :=
  rfl

end Block

namespace SemilocRing

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def blkW : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1


open Classical in
theorem isMultiHomog_of_wh {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by
  intro m hm k
  rw [← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, Ne.symm hb]
  · simp

theorem isMultiHomog_coordPow (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by
  have h : IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)
      (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) :=
    IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow (α k)
  have e : (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) = α := by
    funext k
    simp only [blkW, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact isMultiHomog_of_wh h

end SemilocRing

theorem exists_form_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {W : Ideal (MRing ι)}
    (hW : IsRelevant W) (hWp : W.IsPrime) (α : K → ℕ) : ∃ t : MRing ι, IsMultiHomog t α ∧ t ∉ W := by
  choose i hi using hW
  refine ⟨∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k, SemilocRing.isMultiHomog_coordPow i α, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp h
  exact hi k (hWp.mem_of_pow_mem _ hk)

section Example

end Example

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {n : ℕ}
  {A A' : HermLine ι} {s s' : MRing ι}

theorem De_eq_zero_of_semiPos (hLe : DeLeSemiPos.Statement) {L : Fin n → HermLine ι}
    (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hLp : ∀ j, IsSemiPosHerm (L j))
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) :
    De P L A A' s s' = 0 := by
  have h1 := hLe K ι P n L A A' s s' hP hL hLp hA hA' hs hs' hnc
  have h2 := hLe K ι P n L A' A s' s hP hL hLp hA' hA hs' hs (fun W h h' => hnc W h' h)
  rw [De_swap] at h2
  linarith

theorem De_eq_zero_of_semiPos_off (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) (hP : IsArithVar P (n + 2)) (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) (S : Finset (Fin n)) :
    ∀ L : Fin n → HermLine ι, (∀ j, IsSmoothHerm (L j)) → (∀ j, j ∉ S → IsSemiPosHerm (L j)) →
      De P L A A' s s' = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro L hL hLp
    exact De_eq_zero_of_semiPos hLe hP hL (fun j => hLp j (Finset.notMem_empty j)) hA hA' hs hs' hnc
  | @insert j S hj ih =>
    intro L hL hLp
    obtain ⟨T, hT, hTp, hLTp⟩ := hTw K ι (L j) (hL j)
    have hadd := hAdd K ι P n L j (L j) T A A' s s' hP hL (hL j) hT hA hA' hs hs' hnc
    rw [Function.update_eq_self] at hadd
    have hsm : ∀ X : HermLine ι, IsSmoothHerm X → ∀ i, IsSmoothHerm (Function.update L j X i) := by
      intro X hX i
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hL i
    have hpos : ∀ X : HermLine ι, IsSemiPosHerm X → ∀ i, i ∉ S →
        IsSemiPosHerm (Function.update L j X i) := by
      intro X hX i hi
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hLp i (by simp [Finset.mem_insert, hij, hi])
    rw [ih _ (hsm _ (isSmoothHerm_tensor (hL j) hT)) (hpos _ hLTp),
      ih _ (hsm _ hT) (hpos _ hTp)] at hadd
    linarith

theorem ProjectiveLineTwo.proof (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) : SectionSpaceSymmetry := by
  intro K _ ι _ P n L A A' s s' hP hL hA hA' hs hs' hnc
  have h := De_eq_zero_of_semiPos_off hAdd hTw hLe hP hA hA' hs hs' hnc Finset.univ L hL
    (fun j hj => absurd (Finset.mem_univ j) hj)
  unfold De at h
  linarith

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace FlagPivotIdentity

variable {R : Type} [CommRing R] {n : ℕ}

def leadDet (M : Matrix (Fin n) (Fin n) R) (k : ℕ) : R :=
  if h : k ≤ n then (M.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def pivotCof (M : Matrix (Fin n) (Fin n) R) {a : ℕ} (ha : a + 1 ≤ n) (i : Fin (a + 1)) : R :=
  (-1) ^ ((i : ℕ) + a) * (M.submatrix (Fin.castLE ha ∘ i.succAbove) (Fin.castLE (by omega))).det

theorem pivotMinor_eq_sum (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) :
    pivotMinor M a b = ∑ i : Fin (a + 1),
      pivotCof M (a := a) (by have := a.2; omega) i * M (Fin.castLE (by have := a.2; omega) i) b := by
  unfold pivotMinor
  rw [Matrix.det_succ_column _ (Fin.last a)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcol : pivotCols a b ∘ (Fin.last (a : ℕ)).succAbove = Fin.castLE (by have := a.2; omega) := by
    funext c
    rw [Fin.succAbove_last]
    ext
    simp [pivotCols]
  have hlast : pivotCols a b (Fin.last a) = b := by simp [pivotCols]
  simp only [pivotCof, Matrix.submatrix_apply, Matrix.submatrix_submatrix, Fin.val_last, hlast, hcol]
  ring

def pivotCoeff (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) : Matrix (Fin (j + 1)) (Fin (j + 1)) R :=
  Matrix.of fun a i =>
    if h : (i : ℕ) ≤ a then pivotCof M (a := a) (by have := j.2; have := a.2; omega) ⟨i, by omega⟩ else 0

theorem sum_castLE {m k : ℕ} (h : k ≤ m) (f : Fin m → R) (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) :
    ∑ i : Fin k, f (Fin.castLE h i) = ∑ i : Fin m, f i := by
  have e : ∑ i : Fin k, f (Fin.castLE h i) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb h), f i := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_
  by_contra hlt
  push Not at hlt
  exact hi (Finset.mem_map.2 ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem pivotMatrix_rows (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) {m : ℕ} (e : Fin m → Fin n) :
    (pivotMatrix M).submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e =
      pivotCoeff M j * M.submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e := by
  ext a b
  have ha : (a : ℕ) < n - 1 := by have := j.2; have := a.2; omega
  rw [Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, Fin.val_castLE, dif_pos ha]
  rw [pivotMinor_eq_sum M ⟨a, ha⟩ (e b)]
  rw [← sum_castLE (m := (j : ℕ) + 1) (k := (a : ℕ) + 1) (Nat.succ_le_of_lt a.2)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((Fin.castLE (n := (a : ℕ) + 1) (m := (j : ℕ) + 1) (Nat.succ_le_of_lt a.2) i) : ℕ) ≤ a :=
      Nat.lt_succ_iff.mp i.2
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_pos hi]
    rfl
  · intro i hi
    have : ¬ ((i : ℕ) ≤ a) := by omega
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_neg this, zero_mul]

theorem pivotCoeff_isLowerTriangular (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) :
    (pivotCoeff M j).IsLowerTriangular := by
  intro a i hai
  have hai' : (a : ℕ) < i := OrderDual.toDual_lt_toDual.mp hai
  have : ¬ ((i : ℕ) ≤ a) := by omega
  simp only [pivotCoeff, Matrix.of_apply, dif_neg this]

theorem pivotCoeff_diag (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (a : Fin (j + 1)) :
    pivotCoeff M j a a = leadDet M a := by
  have ha : (a : ℕ) ≤ n := by have := j.2; have := a.2; omega
  simp only [pivotCoeff, Matrix.of_apply, dif_pos le_rfl, pivotCof, leadDet, dif_pos ha]
  have hl : (⟨a, Nat.lt_succ_self _⟩ : Fin ((a : ℕ) + 1)) = Fin.last a := rfl
  rw [hl, Fin.succAbove_last, Even.neg_one_pow ⟨a, rfl⟩, one_mul]
  rfl

theorem leadMinor_eq (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) :
    leadMinor M a = leadDet M (a + 1) := by
  have h : (a : ℕ) + 1 ≤ n := by have := a.2; omega
  unfold leadMinor pivotMinor leadDet
  rw [dif_pos h]
  congr 2
  funext c
  rcases c with ⟨c, hc⟩
  ext
  simp only [pivotCols, Fin.castLE_mk]
  split_ifs <;> (simp; try omega)

theorem leadDet_zero (M : Matrix (Fin n) (Fin n) R) : leadDet M 0 = 1 := by
  simp [leadDet]

theorem proof : FlagPivotIdentity.Statement := by
  intro R _ n M j S
  have hP : flagMinor (pivotMatrix M) j S =
      (∏ k ∈ Finset.range j, leadDet M (k + 1)) * flagMinor M j S := by
    unfold flagMinor
    rw [pivotMatrix_rows, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular _ (pivotCoeff_isLowerTriangular M j)]
    simp only [pivotCoeff_diag]
    rw [Fin.prod_univ_eq_prod_range (fun k => leadDet M k), Finset.prod_range_succ', leadDet_zero, mul_one]
  have hI : ∏ a ∈ Finset.Iic j, leadMinor M a = ∏ k ∈ Finset.range (j + 1), leadDet M (k + 1) := by
    simp only [leadMinor_eq]
    have e := Finset.prod_map (Finset.Iic j) Fin.valEmbedding (fun k => leadDet M (k + 1))
    rw [Fin.map_valEmbedding_Iic] at e
    rw [← show (Finset.Iic (j : ℕ)) = Finset.range (j + 1) by ext; simp, e]
    rfl
  rw [hP, hI, Finset.prod_range_succ, leadMinor_eq]
  ring

end FlagPivotIdentity

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section GenPt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem quotientMap_imageZ_injective (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) :
    Function.Injective (Ideal.quotientMap W' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom
      (le_refl (imageZ v W'))) :=
  Ideal.quotientMap_injective' le_rfl


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
instance imageZ_isPrime (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) [W'.IsPrime] :
    (imageZ v W').IsPrime :=
  Ideal.IsPrime.comap _

def genFibreOf (v : (Σ k, ι k) → (Σ k', ι' k')) (W' : Ideal (MRing ι')) [W'.IsPrime] : GenFibre v W' :=
  letI g : MRing ι ⧸ imageZ v W' →+* FnField W' :=
    (algebraMap (MRing ι' ⧸ W') (FnField W')).comp
      (Ideal.quotientMap W' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom (le_refl (imageZ v W')))
  have hg : Function.Injective g :=
    (IsFractionRing.injective (MRing ι' ⧸ W') (FnField W')).comp (quotientMap_imageZ_injective v W')
  letI alg : Algebra (FnField (imageZ v W')) (FnField W') :=
    (IsFractionRing.lift (K := FnField (imageZ v W')) hg).toAlgebra
  { Φ := FnField (imageZ v W')
    Φ' := FnField W'
    alg := alg
    x := genPt (imageZ v W')
    x' := genPt W'
    ker_x := by
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk (imageZ v W')) f
    gen := fun c => by
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ imageZ v W') c
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨f, g, ?_, ?_⟩
      · rw [aeval_genPt]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      · rw [aeval_genPt, aeval_genPt]
    genericFibre_ker_target := by
      ext f
      rw [RingHom.mem_ker, aeval_genPt]
      exact SetLike.ext_iff.1 (ker_algebraMap_comp_mk W') f
    compat := fun p => by
      show genPt W' (v p) = IsFractionRing.lift hg (genPt (imageZ v W') p)
      rw [genPt, genPt, IsFractionRing.lift_algebraMap]
      simp [g, Ideal.quotientMap_mk] }

theorem GenericPointExists.proof : GenericPointExists.Statement := by
  intro K _ ι _ K' _ ι' _ v W' hW'
  exact ⟨genFibreOf v W'⟩

end GenPt

end GroundTheory.Heights₂.Heights.Inter
end
end
