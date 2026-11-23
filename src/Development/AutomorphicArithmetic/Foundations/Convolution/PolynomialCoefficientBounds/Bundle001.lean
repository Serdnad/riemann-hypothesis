module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Tactic.Continuity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

section

open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.exp_le_factorial_eventually (k : ℕ) (hk : k ≠ 0) :
    ∀ᶠ j : ℕ in atTop, Real.exp ((k : ℝ) * j) ≤ ((j / k).factorial : ℝ) := by
  set C : ℝ := Real.exp ((k : ℝ) * k) with hC
  have hCpos : 0 < C := Real.exp_pos _
  have h1 : ∀ᶠ n : ℕ in atTop, C ^ n / (n.factorial : ℝ) ≤ 1 / C :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop C).eventually
      (ge_mem_nhds (by positivity))
  have h2 : ∀ᶠ n : ℕ in atTop, C ^ (n + 1) ≤ (n.factorial : ℝ) := by
    filter_upwards [h1] with n hn
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_le_div_iff₀ hf hCpos] at hn
    rw [pow_succ]
    linarith
  filter_upwards [(Nat.tendsto_div_const_atTop hk).eventually h2] with j hj
  refine le_trans ?_ hj
  rw [hC, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h3 : j ≤ k * (j / k + 1) := (Nat.lt_mul_div_succ j (Nat.pos_of_ne_zero hk)).le
  have h4 : (j : ℝ) ≤ k * ((j / k + 1 : ℕ) : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (k : ℝ) * j ≤ k * (k * ((j / k + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h4 h5
    _ = _ := by ring

theorem UpperTheory.ConvolutionTheory.FX.degree :
    ∃ d : ℕ → ℕ, Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) ∧ ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial := by
  classical
  let P : ℕ → ℕ → Prop := fun j k => Real.exp ((k : ℝ) * j) ≤ ((j / k).factorial : ℝ)
  let κ : ℕ → ℕ := fun j => Nat.findGreatest (P j) j
  have hκ : ∀ K : ℕ, K ≠ 0 → ∀ᶠ j : ℕ in atTop, K ≤ κ j ∧ P j (κ j) := by
    intro K hK
    filter_upwards [UpperTheory.ConvolutionTheory.FX.exp_le_factorial_eventually K hK, eventually_ge_atTop K] with j h1 h2
    exact ⟨Nat.le_findGreatest h2 h1, Nat.findGreatest_spec (P := P j) h2 h1⟩
  have hlim : Tendsto κ atTop atTop := by
    refine tendsto_atTop.mpr fun K => ?_
    filter_upwards [hκ (K + 1) (Nat.succ_ne_zero K)] with j hj
    exact le_trans (Nat.le_succ K) hj.1
  refine ⟨fun j => j / κ j, ?_, fun B => ?_⟩
  · have h0 : Tendsto (fun j : ℕ => ((κ j : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hlim)
    refine squeeze_zero' (Eventually.of_forall fun j => by positivity) ?_ h0
    filter_upwards [eventually_gt_atTop 0] with j hj
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    rw [div_le_iff₀ hj', inv_mul_eq_div]
    exact Nat.cast_div_le
  · filter_upwards [hκ (⌈B⌉₊ + 1) (Nat.succ_ne_zero _)] with j hj
    refine le_trans (Real.exp_le_exp.mpr ?_) hj.2
    have h1 : ((⌈B⌉₊ + 1 : ℕ) : ℝ) ≤ κ j := by exact_mod_cast hj.1
    have h2 : B ≤ ⌈B⌉₊ := Nat.le_ceil B
    push_cast at h1
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg j)
end

section

open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.two_node_sep (a b a' b' : ℂ) (h : (a, b) ≠ (a', b')) :
    ∃ Q : MvPolynomial (Fin 2) ℂ, eval ![a, b] Q = 1 ∧ eval ![a', b'] Q = 0 := by
  by_cases ha : a = a'
  · have hb : b - b' ≠ 0 := by
      intro hb
      exact h (by rw [ha, sub_eq_zero.mp hb])
    refine ⟨C (b - b')⁻¹ * (X 1 - C b'), ?_, ?_⟩
    · simp [inv_mul_cancel₀ hb]
    · simp
  · have ha' : a - a' ≠ 0 := sub_ne_zero.mpr ha
    refine ⟨C (a - a')⁻¹ * (X 0 - C a'), ?_, ?_⟩
    · simp [inv_mul_cancel₀ ha']
    · simp

private theorem UpperTheory.ConvolutionTheory.FX.two_node_poly (J : Type) [Fintype J] [DecidableEq J] (x z : J → ℂ)
    (h : Function.Injective (fun i => (x i, z i))) (i : J) :
    ∃ P : MvPolynomial (Fin 2) ℂ, ∀ j, eval ![x j, z j] P = if j = i then 1 else 0 := by
  have : ∀ j, ∃ Q : MvPolynomial (Fin 2) ℂ, j ≠ i →
      eval ![x i, z i] Q = 1 ∧ eval ![x j, z j] Q = 0 := by
    intro j
    by_cases hj : j = i
    · exact ⟨0, fun h => absurd hj h⟩
    · obtain ⟨Q, hQ⟩ := UpperTheory.ConvolutionTheory.FX.two_node_sep (x i) (z i) (x j) (z j)
        (fun e => hj (h e).symm)
      exact ⟨Q, fun _ => hQ⟩
  choose Q hQ using this
  refine ⟨∏ j ∈ Finset.univ.erase i, Q j, fun j => ?_⟩
  rw [map_prod]
  split_ifs with hj
  · subst hj
    exact Finset.prod_eq_one fun k hk => (hQ k (Finset.ne_of_mem_erase hk)).1
  · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩) (hQ j hj).2

theorem UpperTheory.ConvolutionTheory.FX.two_node :
    ∀ (J : Type) [Fintype J] (x z : J → ℂ), Function.Injective (fun i => (x i, z i)) → ∃ (s₀ : ℕ) (K : ℝ), ∀ (c : J → ℂ) (ε : ℝ), (∀ s ≤ s₀, ∀ s' ≤ s₀, ‖∑ i, c i * x i ^ s * z i ^ s'‖ ≤ ε) → ∀ i, ‖c i‖ ≤ K * ε := by
  intro J _ x z h
  classical
  choose P hP using UpperTheory.ConvolutionTheory.FX.two_node_poly J x z h
  refine ⟨Finset.univ.sup fun i => (P i).totalDegree,
    ∑ i, ∑ m ∈ (P i).support, ‖(P i).coeff m‖, fun c ε hε i => ?_⟩
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε 0 (Nat.zero_le _) 0 (Nat.zero_le _))
  have h1 : c i = ∑ m ∈ (P i).support, (P i).coeff m * ∑ j, c j * x j ^ m 0 * z j ^ m 1 := by
    have : c i = ∑ j, c j * eval ![x j, z j] (P i) := by
      simp [hP]
    rw [this]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hdeg : ∀ m ∈ (P i).support, ∀ k, m k ≤ Finset.univ.sup fun i => (P i).totalDegree := by
    intro m hm k
    exact ((monomial_le_degreeOf k hm).trans (degreeOf_le_totalDegree _ _)).trans
      (Finset.le_sup (f := fun i => (P i).totalDegree) (Finset.mem_univ i))
  calc ‖c i‖ ≤ ∑ m ∈ (P i).support, ‖(P i).coeff m‖ * ε := by
        rw [h1]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hε _ (hdeg m hm 0) _ (hdeg m hm 1)) (norm_nonneg _)
    _ = (∑ m ∈ (P i).support, ‖(P i).coeff m‖) * ε := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ hε0
        exact Finset.single_le_sum (f := fun i => ∑ m ∈ (P i).support, ‖(P i).coeff m‖)
          (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
end

section

open MvPolynomial Filter Topology

private noncomputable def l1 {ι : Type} (p : MvPolynomial ι ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖p.coeff α‖

private theorem matrixEntryAbsSum_unitaryLie_coordinates_split {ι : Type} (p : MvPolynomial ι ℂ) (s : Finset (ι →₀ ℕ))
    (h : p.support ⊆ s) : l1 p = ∑ α ∈ s, ‖p.coeff α‖ := by
  unfold l1
  refine Finset.sum_subset h ?_
  intro x _ hx
  rw [notMem_support_iff.mp hx, norm_zero]

private theorem intMvPolynomialCoeffAbsSum_add_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p + q) ≤ l1 p + l1 q := by
  classical
  rw [matrixEntryAbsSum_unitaryLie_coordinates_split (p + q) (p.support ∪ q.support) support_add,
    matrixEntryAbsSum_unitaryLie_coordinates_split p (p.support ∪ q.support) Finset.subset_union_left,
    matrixEntryAbsSum_unitaryLie_coordinates_split q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun α _ => ?_
  rw [MvPolynomial.coeff_add]
  exact norm_add_le _ _

private theorem intMvPolynomialCoeffAbsSum_sum_le {ι κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι ℂ) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (intMvPolynomialCoeffAbsSum_add_le _ _).trans (by linarith)

private theorem intMvPolynomialCoeffAbsSum_monomial {ι : Type} (a : ι →₀ ℕ) (c : ℂ) :
    l1 (monomial a c : MvPolynomial ι ℂ) = ‖c‖ := by
  classical
  rw [matrixEntryAbsSum_unitaryLie_coordinates_split _ {a} support_monomial_subset]
  simp

private theorem intMvPolynomialCoeffAbsSum_mul_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p * q) ≤ l1 p * l1 q := by
  have h : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      (monomial (a + b) (p.coeff a * q.coeff b) : MvPolynomial ι ℂ) := by
    conv_lhs => rw [p.as_sum, q.as_sum, Finset.sum_mul_sum]
    simp only [monomial_mul]
  rw [h]
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ?_
  conv_rhs => rw [l1, l1, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans (le_of_eq ?_)
  simp only [intMvPolynomialCoeffAbsSum_monomial, norm_mul]

private theorem l1_C_mul {ι : Type} (p : MvPolynomial ι ℂ) (c : ℂ) :
    l1 (C c * p) = ‖c‖ * l1 p := by
  rw [matrixEntryAbsSum_unitaryLie_coordinates_split (C c * p) p.support, l1, Finset.mul_sum]
  · simp only [coeff_C_mul, norm_mul]
  · intro a ha
    rw [mem_support_iff] at ha ⊢
    rw [coeff_C_mul] at ha
    exact right_ne_zero_of_mul ha

private theorem l1_homogeneousComponent_le {ι : Type} (p : MvPolynomial ι ℂ) (k : ℕ) :
    l1 (homogeneousComponent k p) ≤ l1 p := by
  rw [matrixEntryAbsSum_unitaryLie_coordinates_split (homogeneousComponent k p) p.support, l1]
  · refine Finset.sum_le_sum fun a _ => ?_
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact le_rfl
    · simp
  · intro a ha
    rw [mem_support_iff] at ha ⊢
    rw [coeff_homogeneousComponent] at ha
    intro h
    apply ha
    split_ifs
    · exact h
    · rfl

private theorem l1_rename {ι ι' : Type} (p : MvPolynomial ι ℂ) (δ : ι → ι') :
    l1 (rename δ p) ≤ l1 p := by
  have h : rename δ p = ∑ a ∈ p.support,
      (monomial (Finsupp.mapDomain δ a) (p.coeff a) : MvPolynomial ι' ℂ) := by

    conv_lhs => rw [p.as_sum, map_sum]
    simp only [rename_monomial]
  rw [h]
  refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans (le_of_eq ?_)
  simp only [intMvPolynomialCoeffAbsSum_monomial]
  rfl

theorem UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts :
    ∀ (ι : Type) (p q : MvPolynomial ι ℂ), (∑ α ∈ (p + q).support, ‖(p + q).coeff α‖) ≤ (∑ α ∈ (p).support, ‖(p).coeff α‖) + (∑ α ∈ (q).support, ‖(q).coeff α‖) ∧ (∑ α ∈ (p * q).support, ‖(p * q).coeff α‖) ≤ (∑ α ∈ (p).support, ‖(p).coeff α‖) * (∑ α ∈ (q).support, ‖(q).coeff α‖) ∧ (∀ c : ℂ, (∑ α ∈ (C c * p).support, ‖(C c * p).coeff α‖) = ‖c‖ * (∑ α ∈ (p).support, ‖(p).coeff α‖)) ∧ (∀ (α₀ : ι →₀ ℕ) (c : ℂ), (∑ α ∈ ((monomial α₀ c : MvPolynomial ι ℂ)).support, ‖((monomial α₀ c : MvPolynomial ι ℂ)).coeff α‖) = ‖c‖) ∧ (∀ k, (∑ α ∈ (homogeneousComponent k p).support, ‖(homogeneousComponent k p).coeff α‖) ≤ (∑ α ∈ (p).support, ‖(p).coeff α‖)) ∧ ∀ (ι' : Type) (δ : ι → ι'), (∑ α ∈ (rename δ p).support, ‖(rename δ p).coeff α‖) ≤ (∑ α ∈ (p).support, ‖(p).coeff α‖) := by
  intro ι p q
  exact ⟨intMvPolynomialCoeffAbsSum_add_le p q, intMvPolynomialCoeffAbsSum_mul_le p q, l1_C_mul p, fun a c => intMvPolynomialCoeffAbsSum_monomial a c, l1_homogeneousComponent_le p,
    fun _ δ => l1_rename p δ⟩
end

section

open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.cheb_closed (y s : ℝ) (hs : s ^ 2 = y ^ 2 - 1) (m : ℕ) :
    (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y = ((y + s) ^ m + (y - s) ^ m) / 2 := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
    have e : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    have e1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e1] at h1
    rw [e, Polynomial.Chebyshev.T_add_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    rw [h0, h1]
    linear_combination (-((y + s) ^ n + (y - s) ^ n) / 2) * hs

theorem UpperTheory.ConvolutionTheory.FX.cheb_facts :
    ∀ (m : ℕ) (y : ℝ), (|y| ≤ 1 → |(Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y| ≤ 1) ∧ (1 ≤ y → (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y = ((y + Real.sqrt (y ^ 2 - 1)) ^ m + (y - Real.sqrt (y ^ 2 - 1)) ^ m) / 2 ∧ |(Polynomial.Chebyshev.T ℝ (m : ℤ)).eval y| ≤ (2 * y) ^ m) := by
  intro m y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨h1, h2⟩ := abs_le.mp hy
    rw [← Real.cos_arccos h1 h2, Polynomial.Chebyshev.T_real_cos]
    exact Real.abs_cos_le_one _
  · have h0 : 0 ≤ y ^ 2 - 1 := by nlinarith
    have hs : Real.sqrt (y ^ 2 - 1) ^ 2 = y ^ 2 - 1 := Real.sq_sqrt h0
    have hs0 : 0 ≤ Real.sqrt (y ^ 2 - 1) := Real.sqrt_nonneg _
    have hsy : Real.sqrt (y ^ 2 - 1) ≤ y := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> linarith
    have hc := UpperTheory.ConvolutionTheory.FX.cheb_closed y _ hs m
    refine ⟨hc, ?_⟩
    rw [hc]
    generalize Real.sqrt (y ^ 2 - 1) = s at *
    have ha : 0 ≤ y + s := by linarith
    have hb : 0 ≤ y - s := by linarith
    have pa : (y + s) ^ m ≤ (2 * y) ^ m := pow_le_pow_left₀ ha (by linarith) m
    have pb : (y - s) ^ m ≤ (2 * y) ^ m := pow_le_pow_left₀ hb (by linarith) m
    have qa := pow_nonneg ha m
    have qb := pow_nonneg hb m
    rw [abs_of_nonneg (by linarith)]
    linarith
end

section

open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.eval_esymm_eq {n : ℕ} (x : Fin n → ℂ) (k : ℕ) :
    eval x (esymm (Fin n) ℂ k) = (Finset.univ.val.map x).esymm k := by
  have := MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℂ k x
  rw [← this]
  rfl

private theorem UpperTheory.ConvolutionTheory.FX.perm_of_multiset {n : ℕ} (x y : Fin n → ℂ)
    (h : Finset.univ.val.map x = Finset.univ.val.map y) :
    ∃ w : Equiv.Perm (Fin n), y = x ∘ w := by
  classical
  have hc : ∀ c : ℂ, Fintype.card {i // y i = c} = Fintype.card {i // x i = c} := by
    intro c
    have h1 := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have e1 : ∀ z : Fin n → ℂ, (Finset.univ.filter (fun i => z i = c)).card
        = (Multiset.filter (fun a => c = z a) Finset.univ.val).card := by
      intro z
      simp only [Finset.card, Finset.filter_val, eq_comm]
    rw [e1, e1, h1]
  let e : ∀ c : ℂ, {i // y i = c} ≃ {i // x i = c} := fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map e i).symm

theorem UpperTheory.ConvolutionTheory.FX.perm_of_esymm :
    ∀ (n : ℕ) (x y : Fin n → ℂ), (∀ i : Fin n, eval x (esymm (Fin n) ℂ (i + 1)) = eval y (esymm (Fin n) ℂ (i + 1))) ↔ ∃ w : Equiv.Perm (Fin n), y = x ∘ w := by
  intro n x y
  constructor
  · intro h
    apply UpperTheory.ConvolutionTheory.FX.perm_of_multiset
    set s := Finset.univ.val.map x with hs
    set t := Finset.univ.val.map y with ht
    have hsc : s.card = n := by simp [hs]
    have htc : t.card = n := by simp [ht]
    have he : ∀ k, k ≤ n → s.esymm k = t.esymm k := by
      intro k hk
      rcases k with _ | k
      · simp [Multiset.esymm]
      · have := h ⟨k, hk⟩
        rw [UpperTheory.ConvolutionTheory.FX.eval_esymm_eq, UpperTheory.ConvolutionTheory.FX.eval_esymm_eq] at this
        exact this
    have hp : (s.map fun a => Polynomial.X - Polynomial.C a).prod
        = (t.map fun a => Polynomial.X - Polynomial.C a).prod := by
      rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hsc, htc]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [he j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    have := congrArg Polynomial.roots hp
    rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this
  · rintro ⟨w, rfl⟩ i
    rw [UpperTheory.ConvolutionTheory.FX.eval_esymm_eq, UpperTheory.ConvolutionTheory.FX.eval_esymm_eq]
    congr 1
    rw [← Multiset.map_map]
    congr 1
    exact (Multiset.map_univ_val_equiv w).symm
end
