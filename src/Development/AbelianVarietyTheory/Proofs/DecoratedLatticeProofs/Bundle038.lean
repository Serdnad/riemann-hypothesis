module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle037
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle028
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open PowerSeries GlobalTheory.Honda

noncomputable section

namespace GlobalTheory.Honda.HeightTwo

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_natCast_coprime_eq_one (l u : ℕ) (hp : l.Prime) (hl1 : ‖(l : K)‖ < 1) (hu : ¬ l ∣ u) :
    ‖(u : K)‖ = 1 := by
  apply GlobalTheory.Honda.Lazard.norm_natCast_eq_one_of_not_dvd <;> assumption

theorem pow_le_norm_natCast (l : ℕ) (hp : l.Prime) (hl1 : ‖(l : K)‖ < 1) (k : ℕ) (hk : 1 ≤ k) :
    ‖(l : K)‖ ^ (k - 1) ≤ ‖(k : K)‖ := by
  obtain ⟨v, u, hu, hkv⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : k ≠ 0) l hp.one_lt.ne'
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero l)
  have hvk : v ≤ k - 1 := by
    have h1 : v < l ^ v := Nat.lt_pow_self hp.one_lt
    have h2 : l ^ v ≤ k := by rw [hkv]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
    omega
  have hn : ‖(k : K)‖ = ‖(l : K)‖ ^ v := by
    rw [hkv]; push_cast
    rw [norm_mul, norm_pow, norm_natCast_coprime_eq_one l u hp hl1 hu, mul_one]
  rw [hn]
  exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le hvk

theorem coeff_mul_pow_le (l : ℕ) (hp : l.Prime) (hl1 : ‖(l : K)‖ < 1) (f : K⟦X⟧)
    (hder : CoefLe 1 (derivative f)) (k : ℕ) (hk : 1 ≤ k) :
    ‖coeff k f‖ * ‖(l : K)‖ ^ k ≤ ‖(l : K)‖ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hd := hder k'
  rw [coeff_derivative, norm_mul] at hd
  have hle := pow_le_norm_natCast l hp hl1 (k' + 1) hk
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hle
  calc ‖coeff (k' + 1) f‖ * ‖(l : K)‖ ^ (k' + 1)
      = (‖coeff (k' + 1) f‖ * ‖(l : K)‖ ^ k') * ‖(l : K)‖ := by ring
    _ ≤ 1 * ‖(l : K)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (mul_le_mul_of_nonneg_left hle (norm_nonneg _)).trans hd
    _ = ‖(l : K)‖ := one_mul _

theorem norm_coeff_pow_le (g : K⟦X⟧) (r : ℝ) (m : ℕ) (hr : 0 ≤ r) (hg : ∀ j ≤ m, ‖coeff j g‖ ≤ r) :
    ∀ k j, j ≤ m → ‖coeff j (g ^ k)‖ ≤ r ^ k := by
  intro k
  induction k with
  | zero =>
    intro j _
    rw [pow_zero, pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    intro j hj
    rw [pow_succ', coeff_mul, pow_succ']
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [norm_mul]
    exact mul_le_mul (hg _ (by omega)) (ih _ (by omega)) (norm_nonneg _) hr

theorem norm_coeff_succ_pow_le (g : K⟦X⟧) (hg0 : constantCoeff g = 0) (r : ℝ) (m : ℕ) (hr : 0 ≤ r)
    (hg : ∀ j ≤ m, ‖coeff j g‖ ≤ r) (k : ℕ) :
    ‖coeff (m + 1) (g ^ (k + 2))‖ ≤ r ^ (k + 2) := by
  rw [pow_succ' g (k + 1), coeff_mul, pow_succ' r (k + 1)]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases ha : p.1 = 0
  · rw [ha, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, norm_zero]; positivity
  by_cases hb : p.2 = 0
  · rw [hb, coeff_zero_eq_constantCoeff_apply, map_pow, hg0, zero_pow (by omega), mul_zero, norm_zero]
    positivity
  rw [norm_mul]
  exact mul_le_mul (hg _ (by omega)) (norm_coeff_pow_le g r m hr hg _ _ (by omega)) (norm_nonneg _) hr

theorem coeff_subst_eq_sum (f g : K⟦X⟧) (hg0 : constantCoeff g = 0) (n : ℕ) :
    coeff n (subst g f) = ∑ d ∈ Finset.range (n + 1), coeff d f * coeff n (g ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg0)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hdn
    apply hd
    obtain ⟨g', rfl⟩ := X_dvd_iff.mpr hg0
    simp only [mul_pow, coeff_X_pow_mul', if_neg (by omega : ¬ d ≤ n), smul_zero]

theorem norm_coeff_le_of_subst (f g : K⟦X⟧) (ρ : ℝ) (hρ : 0 ≤ ρ) (hf0 : coeff 0 f = 0) (hf1 : coeff 1 f = 1)
    (hf : ∀ k, 1 ≤ k → ‖coeff k f‖ * ρ ^ k ≤ ρ) (hg0 : constantCoeff g = 0) (N : ℕ)
    (hy : ∀ n ≤ N, ‖coeff n (subst g f)‖ ≤ ρ) : ∀ n ≤ N, ‖coeff n g‖ ≤ ρ := by
  have key : ∀ m, m ≤ N → ∀ j ≤ m, ‖coeff j g‖ ≤ ρ := by
    intro m
    induction m with
    | zero =>
      intro _ j hj
      rw [Nat.le_zero.mp hj, coeff_zero_eq_constantCoeff_apply, hg0, norm_zero]; exact hρ
    | succ m ih =>
      intro hm j hj
      rcases Nat.lt_or_ge j (m + 1) with hj' | hj'
      · exact ih (by omega) j (by omega)
      obtain rfl : j = m + 1 := by omega
      have ih' := ih (by omega)
      have hs := coeff_subst_eq_sum f g hg0 (m + 1)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : 1 < m + 1 + 1)), hf1, pow_one,
        one_mul] at hs
      have hrest : ‖∑ d ∈ (Finset.range (m + 1 + 1)).erase 1, coeff d f * coeff (m + 1) (g ^ d)‖ ≤ ρ := by
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hρ fun d hd => ?_
        have hd1 := Finset.ne_of_mem_erase hd
        rcases Nat.lt_or_ge d 2 with hd2 | hd2
        · obtain rfl : d = 0 := by omega
          rw [hf0, zero_mul, norm_zero]; exact hρ
        obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
        rw [norm_mul]
        calc ‖coeff (k + 2) f‖ * ‖coeff (m + 1) (g ^ (k + 2))‖ ≤ ‖coeff (k + 2) f‖ * ρ ^ (k + 2) :=
              mul_le_mul_of_nonneg_left (norm_coeff_succ_pow_le g hg0 ρ m hρ ih' k) (norm_nonneg _)
          _ ≤ ρ := hf _ (by omega)
      have hgm : coeff (m + 1) g = coeff (m + 1) (subst g f) -
          ∑ d ∈ (Finset.range (m + 1 + 1)).erase 1, coeff d f * coeff (m + 1) (g ^ d) := by
        rw [hs]; ring
      rw [hgm, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy _ hm) ?_)
      rwa [norm_neg]
  exact fun n hn => key n hn n le_rfl

theorem norm_coeff_hondaSum_le (τ : K →+* K) (q : ℕ) (hq : 2 ≤ q) (c : ℕ → K) (f : K⟦X⟧) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hc0 : ‖c 0‖ ≤ ρ) (hf1 : coeff 1 f = 1) (n : ℕ) (hn : n ≤ q) :
    ‖coeff n (hondaSum τ q c f)‖ ≤ ρ := by
  unfold hondaSum
  rw [coeff_mk]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hρ fun j hj => ?_
  have hjn := Finset.mem_range.mp hj
  unfold frobOp
  rw [coeff_subst_X_pow (pow_ne_zero _ (by omega))]
  split_ifs with hdvd
  · have hle := Nat.le_of_dvd (by omega) hdvd
    have hqq : q < q ^ 2 := by rw [sq]; nlinarith
    have hj0 : j = 0 := by
      by_contra hj0
      have : q ^ 2 ≤ q ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    subst hj0
    have hnq : n = q := by rw [zero_add, pow_one] at hle; omega
    subst hnq
    simpa [Nat.div_self (by omega : 0 < n), coeff_map, hf1] using hc0
  · rw [mul_zero, norm_zero]; exact hρ

theorem norm_first_coeff_eq_one : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ)
    (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) →
    CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) →
    (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) → ‖c 0‖ = 1 := by
  intro K _ _ _ l σ hU f e hIL c hc hH hex
  obtain ⟨hp, hl2, hl1, hmax, -, -⟩ := hU
  obtain ⟨⟨hf0, hf1, he0, -, hef⟩, hder, -⟩ := hIL
  have hρ : 0 ≤ ‖(l : K)‖ := norm_nonneg _
  by_contra hne
  have hc0 : ‖c 0‖ ≤ ‖(l : K)‖ := hmax _ (lt_of_le_of_ne (hc 0) hne)
  have hf0' : coeff 0 f = 0 := by rw [coeff_zero_eq_constantCoeff_apply, hf0]
  have hlf0 : constantCoeff (C (l : K) * f) = 0 := by simp [hf0]
  have hg0 : constantCoeff (Formalism.L2.Th1.C.mulBy f e (l : K)) = 0 := by
    unfold Formalism.L2.Th1.C.mulBy
    exact constantCoeff_subst_eq_zero hlf0 e he0
  have hfg : subst (Formalism.L2.Th1.C.mulBy f e (l : K)) f = C (l : K) * f := by
    unfold Formalism.L2.Th1.C.mulBy
    rw [← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' he0)
      (HasSubst.of_constantCoeff_zero' hlf0), hef, subst_X (HasSubst.of_constantCoeff_zero' hlf0)]
  have hy : ∀ n ≤ l ^ 2, ‖coeff n (subst (Formalism.L2.Th1.C.mulBy f e (l : K)) f)‖ ≤ ‖(l : K)‖ := by
    intro n hn
    rw [hfg]
    have h1 := hH n
    have h2 := norm_coeff_hondaSum_le (σ ^ 2) (l ^ 2) (by nlinarith) c f _ hρ hc0 hf1 n hn
    have : coeff n (C (l : K) * f) = coeff n (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) +
        coeff n (hondaSum (σ ^ 2) (l ^ 2) c f) := by rw [map_sub]; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  have hg := norm_coeff_le_of_subst f _ _ hρ hf0' hf1 (coeff_mul_pow_le l hp hl1 f hder) hg0 _ hy
  obtain ⟨n, hn, hn1⟩ := hex
  have := hg n hn
  linarith

end GlobalTheory.Honda.HeightTwo
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem atMostOne_holds : AtMostOne := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S t
  have hclass : S.OneClass t ν := GlobalTheory.T.symmetricChain_oneLatticeClass k ν hν s κ S t
  have hsupp : S.SupportOne t := GlobalTheory.T.symmetricChain_supportOne_of_pattern k s κ S t hpat
  exact ⟨GlobalTheory.T.symData_oneIndex_of_oneClass_of_supportOne k ν hν s κ S t hclass hsupp, GlobalTheory.T.symmetricChain_projected_level_of_pattern k s κ S t hpat, GlobalTheory.T.symmetricChain_oneCoupling_coset_of_pattern k s κ S t hpat⟩

end GlobalTheory.SymChain
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat

theorem symCollapse_of_allPositions : AllPositions → GlobalTheory.LocFlat.SymCollapse := by
  intro hA k _ _ _ _ _ _ ν hν s κ S t _ _
  obtain ⟨hO, hE⟩ := hA k ν hν s κ S t
  have hP : S.Pattern t := GlobalTheory.SymChain.pattern_iter k s κ S t
  have hC := GlobalTheory.T.flatColumnIndicator_pure_at_symmetricPosition k ν hν s κ S t hP hE
  have hR := GlobalTheory.T.flatRowIndicator_of_symLevelExchange k ν hν s κ S t hP hE
  exact ⟨GlobalTheory.T.flatColumnSupport_of_oneIndexAt_symPosition k ν hν s κ S t hO, hC, hR, GlobalTheory.T.symLevel_doubleStep_of_flatColumn_flatRow k ν hν s κ S t hP hO hC hR⟩

end GlobalTheory.LocFlat
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHeckeReps

theorem exists_reps_both : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    (∀ g : GL (A ⊕ D) k, ∃ R d, IsReps g R d) ∧ ∀ g : GL D k, ∃ R, IsRepsK g R :=
  fun _ _ _ _ _ _ _ _ _ _ _ => ⟨fun g => Model.exists_isReps g, fun g => Model.exists_isRepsK g⟩

end GlobalTheory.ParHeckeReps
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke GlobalTheory.ParHeckeSource GlobalTheory.ParahoricConjBlocks

noncomputable section

namespace GlobalTheory.LowerHecke

theorem lowU_conj_blocks {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (M W : Matrix D D k) (ν : Matrix D A k) (a : Matrix A A k) (b : Matrix A D k) (c : Matrix D A k) (e : Matrix D D k) :
    fromBlocks 1 0 0 M * fromBlocks 1 0 (-ν) 1 * fromBlocks a b c e * fromBlocks 1 0 0 W =
      fromBlocks a (b * W) (M * (c - ν * a)) (M * (e - ν * b) * W) := by
  simp only [fromBlocks_multiply]
  congr 1 <;> simp [Matrix.mul_sub, sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] <;> abel

end GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

theorem exists_lowU_diag_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ j ∈ parahoric k A D, ∃ g ∈ R, ∃ ν₀ : Matrix D A k, (∀ i a, valuation k (ν₀ i a) < 1) ∧ ∀ ν : Matrix D A k, (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν₀ - ν = g.1 * μ) → (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) ∈ parahoric k A D := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ j hj
  set w := torusElt k D ϖ (indic s) with hw
  have hjI : IsIntM j.1 := isIntM_of_mem_parahoric hj
  have hjl : ∀ i l, valuation k (j.1 (.inr i) (.inl l)) < 1 := (mem_parahoric.1 hj).2
  have hjd : valuation k j.1.det = 1 := val_det_of_mem_KO (mem_parahoric.1 hj).1
  obtain ⟨ha, he⟩ := (val_det_iff_of_lower j.1 (fun i l => hjI i l) hjl).1 hjd
  obtain ⟨haI, hbI, hcI, heI⟩ := isIntM_toBlocks hjI
  set a := j.1.toBlocks₁₁ with ha_def
  set b := j.1.toBlocks₁₂ with hb_def
  set c := j.1.toBlocks₂₁ with hc_def
  set e := j.1.toBlocks₂₂ with he_def
  have hcM : ∀ i l, valuation k (c i l) < 1 := fun i l => hjl i l
  have ha0 : IsUnit a.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at ha; exact zero_ne_one ha
  have hainvI : IsIntM a⁻¹ := isIntM_inv haI ha
  have hinva : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha0
  letI : Invertible a := Matrix.invertibleOfIsUnitDet a ha0
  set E := e - c * a⁻¹ * b with hE_def
  have hjE : j.1.det = a.det * E.det := by
    rw [← fromBlocks_toBlocks j.1, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hEd : valuation k E.det = 1 := by
    rw [hjE, map_mul, ha, one_mul] at hjd; exact hjd
  have hEI : IsIntM E := isIntM_sub heI (isIntM_mul (isIntM_mul hcI hainvI) hbI)
  have hEu : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).2
    (isUnit_iff_ne_zero.2 fun h0 => by rw [h0, map_zero] at hEd; exact zero_ne_one hEd)
  set E' : GL D k := hEu.unit with hE'_def
  have hE'v : E'.1 = E := hEu.unit_spec
  have hE'K : E' ∈ KO k D := mem_KO_of (by rw [hE'v]; exact hEI) (by rw [hE'v]; exact hEd)
  obtain ⟨g, ⟨hgR, hgK⟩, -⟩ := hR.2 E' hE'K
  obtain ⟨hκg, hκ'g, hgeq⟩ := hκ g hgR

  refine ⟨g, hgR, c * a⁻¹, fun i l => GlobalTheory.StepData.MaxM.mul_intM (k := k) hcM (fun i l => hainvI i l) i l, ?_⟩
  rintro ν ⟨μ, hμ, hνμ⟩
  have hν : ν = c * a⁻¹ - g.1 * μ := by rw [← hνμ]; abel
  set K1 := κ g with hK1
  set K2 := κ' g with hK2
  have hm : (w⁻¹ * K1⁻¹) * g = K2 := by rw [hgeq]; group
  have hm' : K2 * g⁻¹ = w⁻¹ * K1⁻¹ := by rw [← hm]; group
  have hX : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, K1) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) =
      emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w) := by
    rw [mtor_eq, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_lowU, ← map_inv, ← map_inv, Prod.inv_mk, Prod.inv_mk,
      inv_one, ← emb_mul_emb]
    simp only [mul_assoc, hw]
  rw [hX]
  set M : Matrix D D k := (w⁻¹ * K1⁻¹).1 with hM
  have hXv : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1 =
      fromBlocks a (b * w.1) (M * (c - ν * a)) (M * (e - ν * b) * w.1) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_emb_one, val_emb_one, val_lowU, ← fromBlocks_toBlocks j.1]
    exact lowU_conj_blocks _ _ _ _ _ _ _
  have h21 : M * (c - ν * a) = K2.1 * (μ * a) := by
    rw [hν, Matrix.sub_mul, Matrix.mul_assoc c, hinva, Matrix.mul_one, sub_sub_cancel, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hM, ← Units.val_mul, hm, Matrix.mul_assoc]
  have he' : e - ν * b = E + g.1 * μ * b := by rw [hν, hE_def, Matrix.sub_mul]; abel
  have h22 : M * (e - ν * b) * w.1 = (K2 * (g⁻¹ * (E' * w))).1 + K2.1 * (μ * b * w.1) := by
    rw [he', Matrix.mul_add, Matrix.add_mul]
    congr 1
    · rw [hM, ← hm', ← hE'v]; simp only [Units.val_mul, Matrix.mul_assoc]
    · rw [← hm, hM]; simp only [Units.val_mul, Matrix.mul_assoc]
  have hwI : IsIntM w.1 := by
    have h := inv_torusElt_int (D := D) hϖ s
    rw [val_inv_torusElt] at h
    rw [hw, val_torusElt]; simpa using h
  have hμa : ∀ i l, valuation k ((μ * a) i l) < 1 := GlobalTheory.StepData.MaxM.mul_intM (k := k) hμ (fun i l => haI i l)
  have hll : ∀ i l, valuation k ((K2.1 * (μ * a)) i l) < 1 := val_lt_mul (isIntM_of_mem_KO hκ'g) hμa
  have hwdet : (w⁻¹).1.det * w.1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine mem_parahoric_of ?_ ?_ ?_
  · rw [hXv, h21, h22]
    refine isIntM_fromBlocks_iff.2 ⟨haI, isIntM_mul hbI hwI, fun i l => (hll i l).le, ?_⟩
    intro i l
    exact add_mem (isIntM_of_mem_KO (mul_mem hκ'g hgK) i l)
      (isIntM_mul (isIntM_of_mem_KO hκ'g) (isIntM_mul (isIntM_mul (fun i l => (hμ i l).le) hbI) hwI) i l)
  · have hdet : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1.det =
        (K1⁻¹).1.det * j.1.det * ((w⁻¹).1.det * w.1.det) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, val_emb_one,
        val_emb_one, val_lowU, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, Units.val_mul,
        Matrix.det_mul]
      simp only [Matrix.det_one]; ring
    rw [hdet, hwdet, mul_one, map_mul, hjd, mul_one]
    exact val_det_of_mem_KO (inv_mem hκg)
  · intro i l
    rw [hXv, fromBlocks_apply₂₁, h21]
    exact hll i l

end GlobalTheory.LowerHecke

end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

theorem _root_.GlobalTheory.T.lowerUnipotent_blockDiag_cosets_distinct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ g ∈ R, ∀ g' ∈ R, ∀ ν ν' : Matrix D A k, (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (lowU ν' * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g') * mtor ϖ (indic s)) ∈ parahoric k A D → g = g' ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν' - ν = g.1 * μ := by
  first | exact @GlobalTheory.CosetDistinct.coset_uniq | exact GlobalTheory.CosetDistinct.coset_uniq | (intros; apply GlobalTheory.CosetDistinct.coset_uniq <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.parahoricHeckeGenericEigenvalue_map_mul : ∀ (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ), genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n := by
  first | exact @GlobalTheory.ParHecke.genVal_map_mul | exact GlobalTheory.ParHecke.genVal_map_mul | (intros; apply GlobalTheory.ParHecke.genVal_map_mul <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

theorem _root_.GlobalTheory.T.sum_powersetCard_borelParam_eq_genVal : ∀ (q N : ℕ), 0 < q → ∀ (α : Fin N → ℂˣ) (n : ℕ), ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, ((q : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, borelParam q α a) = genVal q 0 N (Finset.univ.val.map α) n := by
  first | exact @GlobalTheory.SatakeSubsetSum.satake_subset_sum | exact GlobalTheory.SatakeSubsetSum.satake_subset_sum | (intros; apply GlobalTheory.SatakeSubsetSum.satake_subset_sum <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.exists_unit_solution_twisted_frobenius_square : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ c : K, ‖c‖ = 1 → ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * (σ ^ 2) ε := by
  first | exact @GlobalTheory.Honda.unit_solution_twisted_frobenius | exact GlobalTheory.Honda.unit_solution_twisted_frobenius | (intros; apply GlobalTheory.Honda.unit_solution_twisted_frobenius <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.hondaType_reduction_to_one_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (l q : ℕ) (τ : K →+* K), 2 ≤ q → ‖(l : K)‖ < 1 → (∀ x, ‖τ x‖ = ‖x‖) → ∀ (f : K⟦X⟧), constantCoeff f = 0 → ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) → ‖c 0‖ = 1 → CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum τ q c f) → ∃ c' : K, ‖c'‖ = 1 ∧ CoefLe ‖(l : K)‖ (C (l : K) * f - C c' * frobOp τ q 1 f) := by
  first | exact @GlobalTheory.Honda.OneTerm.exists_one_term | exact GlobalTheory.Honda.OneTerm.exists_one_term | (intros; apply GlobalTheory.Honda.OneTerm.exists_one_term <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

theorem _root_.GlobalTheory.T.honda_functional_equation_one_term_type : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), Formalism.L2.Th1.C.IsLogPair f e → ∀ c ε : K, ‖ε‖ = 1 → ε = c * (σ ^ 2) ε → CoefLe ‖(l : K)‖ (C (l : K) * f - C c * frobOp (σ ^ 2) (l ^ 2) 1 f) → CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  first | exact @GlobalTheory.HondaFunEq.honda_funEq | exact GlobalTheory.HondaFunEq.honda_funEq | (intros; apply GlobalTheory.HondaFunEq.honda_funEq <;> assumption)
end

section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (s : Type) (A : MvPowerSeries s K), (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → ∀ (i : ℕ) (h : l ^ i ≠ 0) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (A ^ (l ^ i) - MvPowerSeries.expand (l ^ i) h (MvPowerSeries.map (σ ^ i) A))‖ ≤ ‖(l : K)‖ := by
  first | exact @GlobalTheory.Honda.pow_frob_sub_le | exact GlobalTheory.Honda.pow_frob_sub_le | (intros; apply GlobalTheory.Honda.pow_frob_sub_le <;> assumption)
end
