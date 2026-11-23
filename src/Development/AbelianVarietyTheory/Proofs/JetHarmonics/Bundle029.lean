module

public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.HermitianCurvature.StatementM
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwoBracketsLePowMulProdEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle004
public import Formalism.RealPlaceAnalysis.Bundle002
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Formalism.RealPlaceAnalysis.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
public import Formalism.RealPlaceAnalysis.Bundle005
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle026
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

section

open Finset
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompareIterDegree

open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms

theorem fdeg_ratio_abs {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) (t : ℝ) (hinj : Function.Injective μ) :
    fdegHC (μ + Pi.single s t) / fdegHC μ = ∏ c ∈ univ.erase s, |(μ s + t - μ c) / (μ s - μ c)| := by
  set μ' : Fin n → ℝ := μ + Pi.single s t with hμ'
  have hμ'a : ∀ a, μ' a = μ a + if a = s then t else 0 := by
    intro a; simp [hμ', Pi.single_apply]
  set r : Fin n → ℝ := fun c => |(μ s + t - μ c) / (μ s - μ c)| with hr
  have hfac : ∀ a b : Fin n, a < b →
      |μ' a - μ' b| / |μ a - μ b| = (if a = s then r b else 1) * (if b = s then r a else 1) := by
    intro a b hab
    have hne : a ≠ b := ne_of_lt hab
    by_cases has : a = s
    · subst has
      have hbs : b ≠ a := fun h => hne h.symm
      rw [hμ'a, hμ'a, if_pos rfl, if_neg hbs, if_pos rfl, if_neg hbs]
      simp [hr, abs_div]
    · by_cases hbs : b = s
      · subst hbs
        rw [hμ'a, hμ'a, if_neg has, if_pos rfl, if_neg has, if_pos rfl]
        simp only [hr, one_mul, add_zero, abs_div]
        rw [abs_sub_comm (μ a) (μ b + t), abs_sub_comm (μ a) (μ b)]
      · rw [hμ'a, hμ'a, if_neg has, if_neg hbs, if_neg has, if_neg hbs]
        have h0 : μ a - μ b ≠ 0 := sub_ne_zero.2 (fun h => hne (hinj h))
        simp only [add_zero, mul_one]
        exact div_self (abs_ne_zero.2 h0)
  have hden : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun a _ => prod_ne_zero_iff.2 fun b hb => ?_
    have hab : a < b := (mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  unfold fdegHC
  rw [div_div_div_cancel_right₀ hden, ← prod_div_distrib]
  simp_rw [← prod_div_distrib]
  rw [prod_congr rfl (fun a _ => prod_congr rfl (fun b hb => hfac a b (mem_filter.1 hb).2))]
  simp_rw [prod_mul_distrib]
  have h1 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if a = s then r b else 1)) = ∏ b ∈ univ.filter (fun b : Fin n => s < b), r b := by
    rw [prod_eq_single s]
    · simp
    · intro a _ has; simp [has]
    · intro h; exact absurd (mem_univ s) h
  have h2 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if b = s then r a else 1)) = ∏ a ∈ univ.filter (fun a : Fin n => a < s), r a := by
    rw [prod_filter]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_ite_eq']
    simp
  rw [h1, h2, ← prod_filter_mul_prod_filter_not (univ.erase s) (fun c => s < c)]
  congr 1
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega

end GlobalTheory.CompareIterDegree
end
end

section

open Formalism.FourierDecayAlt Finset

namespace GlobalTheory.NormaliserCutBound

theorem prod_fin_eq_prod_Icc (n : ℕ) (f : Fin n → ℝ) (g : ℕ → ℝ)
    (h : ∀ s : Fin n, g (s.val + 1) = f s) : ∏ s, f s = ∏ s ∈ Finset.Icc 1 n, g s := by
  have h1 : ∏ s, f s = ∏ s : Fin n, g (s.val + 1) := Finset.prod_congr rfl (fun s _ => (h s).symm)
  rw [h1, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) n, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

theorem qC_re (P : M.Par) (y : ℝ) :
    (M.qC P (y : ℂ)).re = I.qpoly P.k P.T P.T' P.u P.u' y := by
  have : M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
    unfold M.qC I.qpoly
    push_cast
    rfl
  rw [this, Complex.ofReal_re]

theorem main : ∀ (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (nn : ℝ → ℝ) (Y : Finset ℝ), P.OK → 0 ≤ C → 1 ≤ l → l ≤ P.k → 1 ≤ c → c + 2 ≤ b → (P.k : ℝ) ≤ b → |P.u l| ≤ b → |P.u' l| ≤ b → (∀ s, |lam s| ≤ b) → (∀ s t : Fin (2 * P.r + P.k + 1), s.val + 1 = t.val → t.val + 2 ≤ P.k → lam t + 2 * c ≤ lam s) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T' → (∀ y, 0 ≤ nn y ∧ nn y ≤ ∏ s, (|y + lam s| + c)) → (∀ y ∈ Y, I.OnCut P.u P.u' l y) → ∀ y ∈ Y, nn y * nn (y + 1) ≤ (b ^ ((6 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) ^ 2 * (M.qC P (y : ℂ)).re := by
  intro C b c P l lam nn Y hP hC hl hlk hc hcb hkb hu hu' hlam hgap hint hint' hT hT' hnn hcut y hy
  have hcy := hcut y hy
  have hb3 : 3 ≤ b := by linarith
  obtain ⟨n, hn⟩ : ∃ n, n = 2 * P.r + P.k + 1 := ⟨_, rfl⟩
  revert lam
  rw [← hn]
  intro lam hlam hgap hint hint' hnn
  let lamN : ℕ → ℝ := fun s => if h : s - 1 < n then lam ⟨s - 1, h⟩ else 0
  have hlamN : ∀ s : Fin n, lamN (s.val + 1) = lam s := by
    intro s
    simp [lamN, s.isLt]
  have hlamN' : ∀ (s : ℕ) (h : s - 1 < n), lamN s = lam ⟨s - 1, h⟩ := by
    intro s h
    simp [lamN, h]
  have hn' : P.k + 2 * P.r + 1 = n := by omega
  have hinter : I.Interlaces P.k P.u P.u' P.lo := by
    intro i hi
    have hg := hP.gap i hi
    unfold M.Par.hi at hg
    have h1 := min_le_left (P.u i) (P.u' i)
    have h2 := min_le_right (P.u i) (P.u' i)
    have h3 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
    have h4 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> unfold M.Par.lo <;> linarith
  have hint2 : ∀ v : ℕ → ℝ, (∀ s : Fin n, s.val + 2 ≤ P.k →
      (s.val + 1 ≠ l → lam s + 1 / 2 ≤ v (s.val + 1)) ∧
        (s.val + 2 ≠ l → v (s.val + 2) + 1 / 2 ≤ lam s)) →
      ∀ s : ℕ, 1 ≤ s → s + 1 ≤ P.k → (s ≠ l → lamN s + 1 / 2 ≤ v s) ∧
        (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lamN s) := by
    intro v hv s hs hsk
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have ht : t < n := by omega
    have h := hv ⟨t, ht⟩ hsk
    rw [← hlamN ⟨t, ht⟩] at h
    exact h
  have hmain := GlobalTheory.two_brackets_le_pow_mul_prod_entries P.k P.r l b c y lamN P.u P.u' hl hlk hc hcb
    hkb hu hu'
    (by
      intro s hs
      rw [Finset.mem_Icc] at hs
      rw [hlamN' s (by omega)]
      exact hlam _)
    (by
      intro s hs hsk
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have ht : t < n := by omega
      have ht' : t + 1 < n := by omega
      have h := hgap ⟨t, ht⟩ ⟨t + 1, ht'⟩ rfl (by simp only; omega)
      rw [← hlamN ⟨t, ht⟩, ← hlamN ⟨t + 1, ht'⟩] at h
      exact h)
    (hint2 _ hint) (hint2 _ hint')
    (by
      intro i hi hik
      obtain ⟨h1, h2, h3, h4⟩ := hinter i (Finset.mem_Icc.mpr ⟨hi, hik⟩)
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩)
    hcy
  rw [hn'] at hmain
  have e0 : ∏ s, (|y + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + lamN s| + c) (fun s => by simp only [hlamN])
  have e1 : ∏ s, (|y + 1 + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + 1 + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + 1 + lamN s| + c) (fun s => by simp only [hlamN])
  rw [← e0, ← e1] at hmain
  have hq := Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' P.lo l y P.T P.T' hl hlk hinter hcy
    hP.T_pos hP.T'_pos
  have hTT : 0 < P.T * P.T' := mul_pos hP.T_pos hP.T'_pos
  have hqe : I.qpoly P.k P.T P.T' P.u P.u' y = (P.T * P.T') *
      ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| := by
    rw [← abs_of_pos hq]
    unfold I.qpoly
    rw [abs_mul, abs_neg, abs_of_pos hTT, Finset.abs_prod]
  have hsize := (GlobalTheory.LamSize.main C b P.T P.T' P.r 1 hC hb3 (by push_cast; linarith) hT hT').2
  rw [Nat.cast_one, one_mul] at hsize
  have hA : 0 ≤ ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| :=
    Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  rw [qC_re, hqe, ← mul_assoc]
  calc nn y * nn (y + 1) ≤ (∏ s, (|y + lam s| + c)) * ∏ s, (|y + 1 + lam s| + c) :=
        mul_le_mul (hnn y).2 (hnn (y + 1)).2 (hnn (y + 1)).1 ((hnn y).1.trans (hnn y).2)
    _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_right hsize hA

end GlobalTheory.NormaliserCutBound
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem inner_casK_eq_sum {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (h : KUnit ε E) (x y : M) :
    ⟪x, CasK ε E y⟫_ℂ = ∑ a, ∑ b, if ε a = ε b then ⟪E a b x, E a b y⟫_ℂ else 0 := by
  unfold CasK
  rw [Finset.sum_comm]
  simp only [LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : ε a = ε b
  · rw [if_pos hab.symm, if_pos hab, Module.End.mul_apply, h a b hab]
  · rw [if_neg (fun e => hab e.symm), if_neg hab]
    simp

theorem casK_isSymmetric_and_form :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E →
      LinearMap.IsSymmetric (CasK ε E) ∧
        ∀ x, (⟪x, CasK ε E x⟫_ℂ).re = ∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0 := by
  intro M _ _ n ε E h
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [← inner_conj_symm, inner_casK_eq_sum h, inner_casK_eq_sum h]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [inner_conj_symm]
    · simp
  · rw [inner_casK_eq_sum h]
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    · simp

end GlobalTheory
end

section

open Formalism.REAL Finset

namespace GlobalTheory

theorem capelli_left_comatrix :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E →
      ∀ (u : ℂ) (j l : Fin (m + 1)),
        ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
            (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
          if l = j then qdet E u else 0 := by
  intro A _ _ m E hE u j l
  set b : Fin (m + 1) → Fin (m + 1) := Fin.cons l (Fin.succAbove j) with hb
  have hexp := PI.QmColExpWork.expFirst E id b u
  have hbc : b ∘ Fin.succ = Fin.succAbove j := by
    funext k; simp [hb]
  have hb0 : b 0 = l := by simp [hb]
  rw [hbc, hb0] at hexp
  have hcast : ∀ (k : ℕ) (x : A), (((-1 : ℤ) ^ k : ℤ) : A) * x = ((-1 : ℂ) ^ k) • x := by
    intro k x
    rw [Algebra.smul_def]
    push_cast
    simp
  have hL : ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
      (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
      ((-1 : ℂ) ^ (j : ℕ)) • qminor E id b u := by
    rw [hexp, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcast, smul_smul, ← pow_add, add_comm (j : ℕ) (a : ℕ)]
    rfl
  rw [hL]
  by_cases hlj : l = j
  · subst hlj
    have hbcyc : b = id ∘ PI.QmColExpWork.cyc0 m l := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp [hb, PI.QmColExpWork.cycle_perm_zero]
      · simp [hb, PI.QmColExpWork.cycle_perm_succ]
    rw [if_pos rfl, hbcyc, qSkewCol A (m + 1) (m + 1) E hE id id _ u, PI.QmColExpWork.sign_cycle_perm,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hcast, smul_smul, ← mul_pow]
    simp [qdet]
  · rw [if_neg hlj]
    obtain ⟨k0, hk0⟩ := Fin.exists_succAbove_eq hlj
    have hfix : b ∘ Equiv.swap (0 : Fin (m + 1)) k0.succ = b := by
      funext k
      have h0 : b 0 = b k0.succ := by simp [hb, hk0]
      simp only [Function.comp, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, h0]
      · rw [h2, h0]
      · rfl
    have hs := qSkewCol A (m + 1) (m + 1) E hE id b (Equiv.swap 0 k0.succ) u
    rw [hfix, Equiv.Perm.sign_swap (Fin.succ_ne_zero k0).symm] at hs
    have h2 : (2 : ℂ) • qminor E id b u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hs]
      simp
    have hz : qminor E id b u = 0 := by
      have h3 := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2
      simpa [smul_smul] using h3
    rw [hz, smul_zero]

end GlobalTheory
end

section

open Formalism.REAL

namespace GlobalTheory

theorem _root_.GlobalTheory.lastComatrixRow_inverts_dual : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), _root_.Formalism.REAL.GlRel E → (∀ w v, _root_.Formalism.REAL.qdet E w v = (∏ j, (w + m j)) • v) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∃ K : ℂ → ((PiLp 2 (fun _ : Fin (n + 1) => V)) →ₗ[ℂ] V), (∀ u x, K u ((u - (n : ℂ)) • x + Om x) = (∏ j, (u + m j)) • x (Fin.last n)) ∧ ∀ u v, K u (PiLp.single 2 (Fin.last n) v) = _root_.Formalism.REAL.qdet (fun a b : Fin n => E a.castSucc b.castSucc) u v := by
  intro V _ _ _ n E Om m hE hdet hOm
  let c : ℂ → Fin (n + 1) → Module.End ℂ V := fun u j =>
    ((((-1 : ℤ) ^ ((Fin.last n : ℕ) + (j : ℕ)) : ℤ) : Module.End ℂ V)) * _root_.Formalism.REAL.qminor E j.succAbove (Fin.last n).succAbove u
  refine ⟨fun u => ∑ j, (c u j) ∘ₗ ((LinearMap.proj j).comp (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).toLinearMap), ?_, ?_⟩
  · intro u x
    have hproj : ∀ (y : PiLp 2 (fun _ : Fin (n + 1) => V)) j, (WithLp.addEquiv 2 (Fin (n + 1) → V)).toFun y j = y.ofLp j := fun _ _ => rfl
    have hcom := _root_.Formalism.REAL.qComatrix (Module.End ℂ V) n E hE u (Fin.last n)
    have hT : ∀ j, (u - (n : ℂ)) • x j + Om x j = ∑ l, _root_.Formalism.REAL.Tm E (u - (n : ℂ)) j l (x l) := by
      intro j
      have hite : ∀ l, (if j = l then (u - (n : ℂ)) • (1 : Module.End ℂ V) else 0) (x l) = if j = l then (u - (n : ℂ)) • x l else 0 := by
        intro l; split_ifs <;> simp
      simp only [_root_.Formalism.REAL.shiftedGenerator_eq_ite_smul_add, LinearMap.add_apply, Finset.sum_add_distrib, hOm, ite_smul, zero_smul, hite, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [LinearMap.sum_apply]

    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, WithLp.linearEquiv_apply, LinearMap.proj_apply, hproj, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, hT, map_sum]
    rw [Finset.sum_comm]
    simp only [← Module.End.mul_apply, ← LinearMap.sum_apply]
    have hite : ∀ l, (if Fin.last n = l then _root_.Formalism.REAL.qdet E u else 0) (x l) = if Fin.last n = l then _root_.Formalism.REAL.qdet E u (x l) else 0 := by
      intro l; split_ifs <;> simp
    simp only [c, hcom, hite, Finset.sum_ite_eq, Finset.mem_univ, if_true, hdet]
  · intro u v
    have hproj : ∀ (y : PiLp 2 (fun _ : Fin (n + 1) => V)) j, (WithLp.addEquiv 2 (Fin (n + 1) → V)).toFun y j = y.ofLp j := fun _ _ => rfl
    rw [LinearMap.sum_apply, Finset.sum_eq_single (Fin.last n)]
    · simp only [c, LinearMap.comp_apply, LinearEquiv.coe_coe, WithLp.linearEquiv_apply, LinearMap.proj_apply, hproj, PiLp.ofLp_single, Pi.single_eq_same, Fin.succAbove_last, Module.End.mul_apply]
      have hsign : ((-1 : ℤ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
        rw [← two_mul, pow_mul]; simp
      rw [hsign, Int.cast_one, Module.End.one_apply]
      unfold _root_.Formalism.REAL.qdet
      rw [_root_.Formalism.REAL.quantumMinor_eq_sum_term, _root_.Formalism.REAL.quantumMinor_eq_sum_term]
      unfold _root_.Formalism.REAL.exchangeTwo_self_eq_one
      simp only [_root_.Formalism.REAL.shiftedGenerator_eq_ite_smul_add, Fin.castSucc_inj, id]
    · intro j _ hj
      simp [LinearMap.comp_apply, hproj, PiLp.ofLp_single, Pi.single_eq_of_ne hj]
    · simp

end GlobalTheory
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.CasKAdjoint

def adMat {n : ℕ} (a b : Fin n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun i j =>
  (if i.1 = a ∧ j = (b, i.2) then 1 else 0) - (if i.2 = b ∧ j = (i.1, a) then 1 else 0)

end GlobalTheory.CasKAdjoint
end

section

open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.UnitDeterminantBasis

theorem det_ne_zero {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O]
    [Algebra k O] [IsDomain O] {n : ℕ} {e : A}
    (b : Module.Basis (Fin n) k (LinearMap.range (LinearMap.mulLeft k e)))
    (T : Fin n → (A →ₐ[k] O)) (hT : Function.Injective T) (hTe : ∀ j, T j e = 1) :
    (Matrix.of fun i j => T j (b i : A)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hc0
  have hli := (linearIndependent_algHom_toLinearMap k A O).comp T hT
  rw [Fintype.linearIndependent_iff] at hli
  funext j
  refine hli c ?_ j
  have h1 : (∑ j, c j • (T j).toLinearMap) ∘ₗ
      (LinearMap.range (LinearMap.mulLeft k e)).subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    simpa [LinearMap.sum_apply, mul_comm] using this
  ext a
  have h2 := LinearMap.congr_fun h1 ⟨e * a, a, rfl⟩
  simpa [LinearMap.sum_apply, hTe] using h2

end GlobalTheory.UnitDeterminantBasis
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.isAdicComplete_of_pow_le_of_pow_le (A : Type) [CommRing A] (J J' : Ideal A) (k l : ℕ)
    (h1 : J ^ k ≤ J') (h2 : J' ^ l ≤ J) (h : IsAdicComplete J A) : IsAdicComplete J' A := by
  have hk : J ^ (k + 1) ≤ J' := le_trans (Ideal.pow_le_pow_right (Nat.le_succ k)) h1
  have hl : J' ^ (l + 1) ≤ J := le_trans (Ideal.pow_le_pow_right (Nat.le_succ l)) h2
  have hJ : ∀ m, J ^ ((k + 1) * m) ≤ J' ^ m := fun m => by
    rw [pow_mul]; exact Ideal.pow_right_mono hk m
  have hJ' : ∀ m, J' ^ ((l + 1) * m) ≤ J ^ m := fun m => by
    rw [pow_mul]; exact Ideal.pow_right_mono hl m
  exact
    { haus' := fun x hx => h.toIsHausdorff.haus' x fun m =>
        (hx ((l + 1) * m)).mono (Submodule.smul_mono_left (hJ' m))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun m => f ((l + 1) * m))
          (fun {m n} hmn => (hf (Nat.mul_le_mul_left (l + 1) hmn)).mono
            (Submodule.smul_mono_left (hJ' m)))
        refine ⟨L, fun n => ?_⟩
        have hn : n ≤ (l + 1) * ((k + 1) * n) :=
          (Nat.le_mul_of_pos_left n (Nat.succ_pos k)).trans
            (Nat.le_mul_of_pos_left _ (Nat.succ_pos l))
        exact (hf hn).trans ((hL ((k + 1) * n)).mono (Submodule.smul_mono_left (hJ n))) }

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.hermitian_datum_direct_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ), ∃ (Dw' : Datum H) (e : Dw'.La ≃ₗ[𝓞 E] (Fin n → Dw.La)), (∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i)) ∧ Dw'.p = n * Dw.p ∧ Dw'.q = n * Dw.q := by
  first | exact @GlobalTheory.exists_datum_pow | exact GlobalTheory.exists_datum_pow | (intros; apply GlobalTheory.exists_datum_pow <;> assumption)
end
