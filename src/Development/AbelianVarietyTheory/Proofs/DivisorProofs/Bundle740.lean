module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PhlaBlockWtCpt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

theorem resT_lpMinor_le (p q s : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hs : s ≤ p) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
  have key : lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ s hs hs) := rfl
  rw [key, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  have hi : (Fin.castLE h1 i : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs i) := Fin.ext rfl
  have hj : (Fin.castLE h2 j : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs j) := Fin.ext rfl
  rw [hi, hj, resT, aeval_X]
  simp [resVarT]

theorem resT_lpMinor_ge (p q u : ℕ) (h1 : p + u ≤ p + q) (h2 : p + u ≤ p + q) (hu : u ≤ q) :
    resT ℚ p q (lpMinor ℚ (p + u) h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  have key : lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ p le_rfl le_rfl) *
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := MvPolynomial (Fin p × Fin p) ℚ))
        (lpMinor ℚ u hu hu) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [key, lpMinor, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₂₁ (B := 0)]
  congr 1
  ext (a | a) (b | b)
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q a := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q b := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]

theorem nuNext_natAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (j : Fin q) :
    nuNext ν (Fin.natAdd p j) = nuNext (fun j => ν (Fin.natAdd p j)) j := by
  unfold nuNext
  simp only [Fin.val_natAdd]
  split_ifs with h h' h'
  · congr 1
  · omega
  · omega
  · rfl

theorem nuNext_castAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (i : Fin p) (hi : (i : ℕ) + 1 < p) :
    nuNext ν (Fin.castAdd q i) = nuNext (fun i => ν (Fin.castAdd q i)) i := by
  unfold nuNext
  simp only [Fin.val_castAdd]
  rw [dite_eq_left (by omega), dite_eq_left hi]
  rfl

theorem sum_sub_nuNext (q : ℕ) (μ : Fin (q + 1) → ℕ) (hμ : Antitone μ) :
    ∑ j, (μ j - nuNext μ j) = μ 0 := by
  induction q with
  | zero => simp [nuNext]
  | succ q ih =>
    rw [Fin.sum_univ_succ]
    have h1 : ∀ j : Fin (q + 1), nuNext μ j.succ = nuNext (fun j => μ j.succ) j := by
      intro j
      unfold nuNext
      simp only [Fin.val_succ]
      split_ifs with h h' h' <;> first | omega | rfl
    simp_rw [h1]
    rw [ih (fun j => μ j.succ) (fun a b hab => hμ (Fin.succ_le_succ_iff.mpr hab))]
    have h0 : nuNext μ 0 = μ (Fin.succ 0) := by
      unfold nuNext; rw [dite_eq_left (by simp)]; rfl
    rw [h0]
    have := hμ (Fin.zero_le (Fin.succ 0 : Fin (q + 2)))
    omega

theorem resT_lpMinor_ge' (p q s u : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hu : u ≤ q) (hs : s = p + u) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  subst hs
  exact resT_lpMinor_ge p q u h1 h2 hu

theorem prod_tmul_prod {ι A B : Type} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (s : Finset ι) (a : ι → A) (b : ι → B) :
    ∏ i ∈ s, (a i ⊗ₜ[ℚ] b i) = (∏ i ∈ s, a i) ⊗ₜ[ℚ] (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.TensorProduct.one_def]
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

theorem hw_first (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) :
    (∏ i : Fin p, lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^
        (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) *
      lpMinor ℚ p le_rfl le_rfl ^ (∑ j : Fin q, (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) := by
  rcases p with _ | p
  · simp [hw, lpMinor, Matrix.det_isEmpty]
  · rw [hw, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
    simp only [Fin.val_last]
    rw [← pow_add]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      rw [nuNext_castAdd (p + 1) q ν k.castSucc (by simp)]
    · have hl : nuNext (fun i => ν (Fin.castAdd q i)) (Fin.last p) = 0 := by
        unfold nuNext; rw [dite_eq_right (by simp)]
      rw [hl, Nat.sub_zero]
      congr 1
      simp_rw [nuNext_natAdd]
      rcases q with _ | q
      · simp [nuNext]
      · rw [sum_sub_nuNext q (fun j => ν (Fin.natAdd (p + 1) j))
          (fun a b hab => hν (by rw [Fin.le_def] at hab ⊢; simp only [Fin.val_natAdd]; omega))]
        have h0 : nuNext ν (Fin.castAdd (q + 1) (Fin.last p)) = ν (Fin.natAdd (p + 1) 0) := by
          unfold nuNext; rw [dite_eq_left (by simp <;> omega)]; congr 1
        have := hν (show Fin.castAdd (q + 1) (Fin.last p) ≤ Fin.natAdd (p + 1) 0 by
          simp [Fin.le_def])
        rw [h0]
        omega

theorem resHw_holds : ResHw := by
  intro p q ν hν
  rw [hw, map_prod, Fin.prod_univ_add]
  have e1 : ∀ i : Fin p, resT ℚ p q (lpMinor ℚ ((Fin.castAdd q i : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) =
      (lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^ (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) ⊗ₜ[ℚ]
        (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
    intro i
    rw [map_pow, resT_lpMinor_le p q _ _ _ (by simp <;> omega), Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  have e2 : ∀ j : Fin q, resT ℚ p q (lpMinor ℚ ((Fin.natAdd p j : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      (lpMinor ℚ p le_rfl le_rfl ^ (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) ⊗ₜ[ℚ]
        (lpMinor ℚ ((j : ℕ) + 1) (by omega) (by omega) ^
          ((fun j => ν (Fin.natAdd p j)) j - nuNext (fun j => ν (Fin.natAdd p j)) j)) := by
    intro j
    rw [map_pow, resT_lpMinor_ge' p q _ ((j : ℕ) + 1) _ _ (by omega) (by simp <;> omega),
      Algebra.TensorProduct.tmul_pow, nuNext_natAdd]
  rw [Finset.prod_congr rfl fun i _ => e1 i, Finset.prod_congr rfl fun j _ => e2 j, prod_tmul_prod,
    prod_tmul_prod, Algebra.TensorProduct.tmul_mul_tmul, Finset.prod_const_one, one_mul,
    Finset.prod_pow_eq_pow_sum, hw_first p q ν hν]
  rfl

end GlobalTheory.LeviCut
end
end

section

open GlobalTheory.LeviCut

namespace GlobalTheory.BetaDenProof

theorem dvd_lam_of_le {l w t : ℕ} (hl : l.Prime) (ht : 1 ≤ t) (htw : t ≤ w) :
    t ∣ (∏ s ∈ Finset.Icc 1 w, ordCompl[l] s) * l ^ Nat.log l w := by
  have ht0 : t ≠ 0 := by omega
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self t l]
  rw [mul_comm (ordProj[l] t)]
  apply Nat.mul_dvd_mul
  · exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨ht, htw⟩)
  · apply Nat.pow_dvd_pow
    apply Nat.le_log_of_pow_le hl.one_lt
    exact (Nat.ordProj_le l ht0).trans htw

theorem beta_dvd {Λ w : ℕ} (h : ∀ t, 1 ≤ t → t ≤ w → t ∣ Λ) :
    ∀ k j : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial) := by
  intro k
  induction k with
  | zero =>
    intro j hj
    simp only [Nat.add_zero, Nat.factorial_zero, mul_one, Nat.factorial_succ]
    exact Nat.mul_dvd_mul (h (j + 1) (by omega) (by omega)) dvd_rfl
  | succ k ih =>
    intro j hj
    have h1 := ih j (by omega)
    have h2 := ih (j + 1) (by omega)
    have e : Λ * (j.factorial * (k + 1).factorial) + Λ * ((j + 1).factorial * k.factorial)
        = (j + k + 2) * (Λ * (j.factorial * k.factorial)) := by
      rw [Nat.factorial_succ k, Nat.factorial_succ j]; ring
    have hA : (j + (k + 1) + 1).factorial ∣ (j + k + 2) * (Λ * (j.factorial * k.factorial)) := by
      have : (j + (k + 1) + 1).factorial = (j + k + 2) * (j + k + 1).factorial := by
        rw [show j + (k + 1) + 1 = (j + k + 1) + 1 by omega, Nat.factorial_succ]
      rw [this]; exact Nat.mul_dvd_mul dvd_rfl h1
    have hB : (j + (k + 1) + 1).factorial ∣ Λ * ((j + 1).factorial * k.factorial) := by
      rw [show j + (k + 1) + 1 = j + 1 + k + 1 by omega]; exact h2
    rw [← e] at hA
    exact (Nat.dvd_add_left hB).mp hA

end GlobalTheory.BetaDenProof

theorem GlobalTheory.LeviCut.betaDen : GlobalTheory.LeviCut.BetaDen := by
  intro l w hl
  refine ⟨∏ s ∈ Finset.Icc 1 w, ordCompl[l] s, ?_, ?_⟩
  · intro hd
    obtain ⟨s, hs, hds⟩ := (Prime.dvd_finsetProd_iff hl.prime _).mp hd
    have : s ≠ 0 := by have := (Finset.mem_Icc.mp hs).1; omega
    exact Nat.not_dvd_ordCompl hl this hds
  · intro j k hjk
    exact GlobalTheory.BetaDenProof.beta_dvd (fun t ht htw => GlobalTheory.BetaDenProof.dvd_lam_of_le hl ht htw) k j hjk
end

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

def colPull {k N : ℕ} (τ : Fin k → Fin N) : (Fin N → ℕ) →+ (Fin k → ℕ) where
  toFun g := g ∘ τ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colPull_single_mem {k N : ℕ} {τ : Fin k → Fin N} (hτ : Function.Injective τ) (s : Fin k) :
    colPull τ (Pi.single (τ s) 1) = Pi.single s 1 := by
  funext t
  change (Pi.single (τ s) 1 : Fin N → ℕ) (τ t) = _
  by_cases h : t = s
  · subst h; simp
  · rw [Pi.single_eq_of_ne (fun h' => h (hτ h')), Pi.single_eq_of_ne h]

theorem colPull_single_not {k N : ℕ} {τ : Fin k → Fin N} {y : Fin N} (hy : y ∉ Set.range τ) :
    colPull τ (Pi.single y 1) = 0 := by
  funext t
  change (Pi.single y 1 : Fin N → ℕ) (τ t) = 0
  exact Pi.single_eq_of_ne (fun h => hy ⟨t, h⟩) _

theorem mem_dualWeyl_iff' {R : Type} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, mem_weightedHomogeneousSubmodule,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]

theorem aeval_isWeightedHomogeneous {R σ ι Mo : Type} [CommRing R] [AddCommMonoid Mo] (w : ι → Mo)
    (φ : σ → MvPolynomial ι R) (ω : σ → Mo) (hφ : ∀ v, IsWeightedHomogeneous w (φ v) (ω v))
    (x : MvPolynomial σ R) (κ : Mo) (hx : IsWeightedHomogeneous ω x κ) :
    IsWeightedHomogeneous w (aeval φ x) κ := by
  conv => enter [2, 2]; rw [x.as_sum]

  rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial, ← hx (mem_support_iff.mp hd), Finsupp.weight_apply, MvPolynomial.algebraMap_eq]
  refine IsWeightedHomogeneous.C_mul ?_ _
  unfold Finsupp.prod Finsupp.sum
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _

theorem isWeightedHomogeneous_map_weight {R σ M M' : Type} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']
    (π : M →+ M') (w : σ → M) (x : MvPolynomial σ R) (κ : M) (hx : IsWeightedHomogeneous w x κ) :
    IsWeightedHomogeneous (fun v => π (w v)) x (π κ) := by
  intro d hd
  rw [← hx hd, Finsupp.weight_apply, Finsupp.weight_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [map_nsmul]

theorem substMem : SubstMem := by
  intro R _ k N τ hτ ψ h1 h2 h3 ν f hf
  rw [mem_dualWeyl_iff'] at hf ⊢
  have hinj := hτ.injective
  refine ⟨?_, fun l j hlj => ?_⟩
  · have hvar : ∀ v : Fin N × Fin N,
        IsWeightedHomogeneous (colW k k) (ψ v) (colPull τ (colW N N v)) := by
      rintro ⟨x, y⟩
      change IsWeightedHomogeneous _ _ (colPull τ (Pi.single y 1))
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        rw [colPull_single_mem hinj]
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1]
          exact isWeightedHomogeneous_X _ _ _
        · rw [h2 x s hx]
          exact isWeightedHomogeneous_zero _ _ _
      · rw [colPull_single_not hy]
        obtain ⟨c, hc⟩ := h3 x y hy
        rw [hc]
        exact isWeightedHomogeneous_C _ _
    exact aeval_isWeightedHomogeneous (colW k k) ψ _ hvar f _
      (isWeightedHomogeneous_map_weight (colPull τ) _ f ν hf.1)
  · let ψO : Option (Fin N × Fin N) → MvPolynomial (Option (Fin k × Fin k)) R :=
      fun o => o.elim (X none) fun v => rename some (ψ v)
    have hA : (aeval ψO).comp (rename some) = (rename some).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      simp [ψO]
    have hB : (aeval ψO).comp (colAddGen R (r := N) (τ l) (τ j)) = (colAddGen R l j).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      obtain ⟨x, y⟩ := v
      simp only [AlgHom.comp_apply, aeval_X]
      rw [colAddGen, aeval_X]
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1, colAddGen, aeval_X]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h1]
          · simp [ψO, h1]
        · rw [h2 x s hx, map_zero]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h2 x _ hx]
          · simp [ψO, h2 x _ hx]
      · obtain ⟨c, hc⟩ := h3 x y hy
        have hyj : y ≠ τ j := fun h => hy ⟨j, h.symm⟩
        rw [if_neg hyj, hc]
        simp [ψO, hc]
    have e1 := congrArg (fun φ => φ f) hA
    have e2 := congrArg (fun φ => φ f) hB
    simp only [AlgHom.comp_apply] at e1 e2
    rw [← e2, hf.2 (τ l) (τ j) (hτ hlj), e1]

end GlobalTheory.LeviCut
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

noncomputable section

theorem det_ratio_pow_mul_borel_eq_weight_prod {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (k : ℕ) (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (M : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
    ((M * KU.tl X (mat b τ)).det / (M * KU.tl X (mat b τ)).toBlocks₂₂.det ^ 2) ^ k =
      (∏ i, b τ i i ^ laS X k τ i) * (M.det / M.toBlocks₂₂.det ^ 2) ^ k := by
  set T := KU.tl X (mat b τ) with hT
  have h22 : (M * T).toBlocks₂₂ = M.toBlocks₂₂ * T.toBlocks₂₂ := by
    rw [KU.toBlocks₂₂_mul, KU.tl_bor₁₂ X hb τ, Matrix.mul_zero, zero_add]
  set D1 : ℂ := ∏ j : Fin (r - X.p0), b τ (KU.eT X (Sum.inl j)) (KU.eT X (Sum.inl j)) with hD1
  set D2 : ℂ := ∏ i : Fin X.p0, b τ (KU.eT X (Sum.inr i)) (KU.eT X (Sum.inr i)) with hD2
  have hD2ne : D2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => FrameDegreeData.bdiag_ne X hb τ _
  have hdetT : T.det = D1 * D2 := by
    have ht : (mat b τ).BlockTriangular id := fun i j hij => (hb τ).2 i j hij
    rw [hT, KU.tl, Matrix.det_submatrix_equiv_self, Matrix.det_of_upperTriangular ht,
      ← Fintype.prod_equiv (KU.eT X) (fun s => mat b τ (KU.eT X s) (KU.eT X s)) _ (fun _ => rfl),
      Fintype.prod_sum_type]
    rfl
  have hdetT22 : T.toBlocks₂₂.det = D2 := by
    have ht : T.toBlocks₂₂.BlockTriangular id := by
      intro i j hij
      simp only [hT, KU.tl, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, KU.eT_inr]
      exact (hb τ).2 _ _ (show (Fin.castLE X.p0_le j : ℕ) < Fin.castLE X.p0_le i from hij)
    rw [Matrix.det_of_upperTriangular ht]
    rfl
  have hchar : (∏ i, b τ i i ^ laS X k τ i) = D1 ^ k * (D2 ^ k)⁻¹ := by
    rw [← Fintype.prod_equiv (KU.eT X) (fun s => b τ (KU.eT X s) (KU.eT X s) ^ laS X k τ (KU.eT X s)) _
      (fun _ => rfl), Fintype.prod_sum_type, hD1, hD2, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_inv_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      have : X.p0 ≤ (KU.eT X (Sum.inl j) : ℕ) := by simp [KU.eT]
      simp [laS, this]
    · refine Finset.prod_congr rfl fun i _ => ?_
      have : ¬ X.p0 ≤ (KU.eT X (Sum.inr i) : ℕ) := by simp [KU.eT]
      simp [laS, this, zpow_neg]
  rw [Matrix.det_mul, h22, Matrix.det_mul, hdetT, hdetT22, hchar, ← inv_pow, ← mul_pow, ← mul_pow]
  congr 1
  have hc : D2 * (D2 ^ 2)⁻¹ = D2⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hD2ne, one_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_inv]
  calc M.det * (D1 * D2) * ((M.toBlocks₂₂.det ^ 2)⁻¹ * (D2 ^ 2)⁻¹)
      = D1 * (D2 * (D2 ^ 2)⁻¹) * (M.det * (M.toBlocks₂₂.det ^ 2)⁻¹) := by ring
    _ = _ := by rw [hc]

theorem qS_rmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → qS X x0 k (rmul x b) = bchar (laS X k) b * qS X x0 k x := by
  intro E _ _ _ r X x0 k x b hb
  unfold qS bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [KU.Mx_rmul]
  exact det_ratio_pow_mul_borel_eq_weight_prod X k b hb τ _

end

end GlobalTheory.ScalarPoin
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

theorem phla_laS_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), z ∈ OmF X x0 →
    phla X (laS X k) (cpt X x0 z) = 2 * (k : ℝ) * rhF X x0 z := by
  intro E _ _ _ r X x0 ho k z hz
  rw [IW.phla_eq X hz, rhF, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set x := cpt X x0 z
  let L' : ℕ → ℝ := fun j => if h : j < r + 1 then IW.Lm X x τ ⟨j, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have hk : ∀ i : Fin r, ((laS X k τ i : ℤ) : ℝ) =
      2 * (k : ℝ) * (if (i : ℕ) < X.p0 then (0 : ℝ) else 1) - (k : ℝ) := fun i => by
    unfold laS
    by_cases h : (i : ℕ) < X.p0
    · rw [if_neg (not_le.2 h), if_pos h]; push_cast; ring
    · rw [if_pos (not_lt.1 h), if_neg h]; push_cast; ring
  have hL0 : L' 0 = 0 := by
    simp only [L', dif_pos (Nat.succ_pos r)]; exact IW.Lm_zero X x τ
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 ho z τ
  have hLp : L' X.p0 = Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ := by
    simp only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]; rfl
  simp_rw [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i)) r]
  have hsplit : ∑ i ∈ Finset.range r,
      (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i) =
      2 * (k : ℝ) * ∑ i ∈ Finset.range r, (if i < X.p0 then (0 : ℝ) else 1) * (L' (i + 1) - L' i) -
        (k : ℝ) * ∑ i ∈ Finset.range r, (L' (i + 1) - L' i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, GlobalTheory.CurvMargin.tele_tail L' X.p0 r X.p0_le, Finset.sum_range_sub L' r, hLr, hL0, hLp]
  ring

end GlobalTheory.ScalarPoin
end
