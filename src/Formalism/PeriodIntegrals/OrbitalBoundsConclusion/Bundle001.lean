module

public import Formalism.LocalToGlobal.AdelicCompactOpens.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDefiniteOrthonormal.Imports
public import Formalism.PeriodIntegrals.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IndexUpperBound.OneSubSumLeProd
public import Formalism.PeriodIntegrals.Bundle003
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.Bundle006
public import Formalism.PeriodIntegrals.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinimalLatticeNorm.NormTwoEqOne
public import Formalism.PeriodIntegrals.Bundle009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeJacobi.NotIsSquareOfJacobi
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientSigmaFiniteness.SigmaFiniteOfWeil
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

section

theorem posDefCongruentOne : Formalism.L2.Props.HermDefON := fun _ G hG => PI.UnitaryGroupMassFormula.HermDefON.exists_congr_one G hG
end

section

theorem product_lowerBound : PI.IndexUBound.IndexUBound := by
  classical
  intro ι S g r y hg hy
  have h2 : ∀ v ∈ S, (2 : ℝ) ≤ g v := fun v hv => by exact_mod_cast hg v hv

  have hfac : ∀ v ∈ S, ∏ i ∈ Finset.Ico 1 r, ((g v : ℝ) ^ i - 1) =
      (g v : ℝ) ^ (r * (r - 1) / 2) * ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i) :=
    fun v hv => PI.UnitaryGroupMassFormula.IndexUBound.prod_factor _ (by linarith [h2 v hv] : (0 : ℝ) < g v).ne' r
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]

  have hQ := PI.UnitaryGroupMassFormula.IndexUBound.one_sub_sum_le_prod S
    (fun v => ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i)) (fun v => 1 / ((g v : ℝ) - 1))
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).1)
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).2.1)
    (fun v hv => div_nonneg zero_le_one (by linarith [h2 v hv]))
    (fun v hv => (PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds _ (h2 v hv) r).2.2)
  beta_reduce at hQ
  have hpos : 0 ≤ ∏ v ∈ S, (g v : ℝ) ^ (r * (r - 1) / 2) :=
    Finset.prod_nonneg fun v _ => by positivity
  have key := mul_le_mul_of_nonneg_right
    (show 1 - y ≤ ∏ v ∈ S, ∏ i ∈ Finset.Ico 1 r, (1 - (g v : ℝ)⁻¹ ^ i) by linarith) hpos
  linarith
end

section

theorem isConvIdempotent_pi : PI.PhProdConv.ProdConv := by
  intro ι _ _ G _ _ _ _ _ _ μ _ _ _ ph m hint hconv
  refine ⟨MeasureTheory.Integrable.fintype_prod_dep hint, ?_⟩
  unfold PI.PhProdConv.PhConv
  refine ⟨?_, fun g => ?_, fun x y => ?_⟩
  · exact Finset.prod_eq_one (fun i _ => (hconv i).1)
  · change ∏ i, ph i ((g i)⁻¹) = starRingEnd ℂ (∏ i, ph i (g i))
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => (hconv i).2.1 (g i))
  · have key : (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) =
        fun g => ∏ i, (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)) i (g i) := by
      funext g
      rw [← Finset.prod_mul_distrib]
      rfl
    change MeasureTheory.Integrable
        (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i))
        (MeasureTheory.Measure.pi μ) ∧
      ∫ g, (fun g : ∀ i, G i => (∏ i, ph i (g i)) * ∏ i, ph i ((x⁻¹ * g⁻¹ * y) i)) g
        ∂(MeasureTheory.Measure.pi μ) = (∏ i, m i (x i)) * ∏ i, ph i (y i)
    rw [key]
    refine ⟨MeasureTheory.Integrable.fintype_prod_dep
      (fun i => ((hconv i).2.2 (x i) (y i)).1), ?_⟩
    rw [MeasureTheory.integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (fun i (h : G i) => ph i h * ph i ((x i)⁻¹ * h⁻¹ * y i)), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => ((hconv i).2.2 (x i) (y i)).2)
end

section

private theorem sum_range_add_choose_eq_choose_succ (E n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k + E).choose E = (n + E + 1).choose (E + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show n + 1 + E + 1 = (n + E + 1) + 1 by omega,
      Nat.choose_succ_succ (n + E + 1) E, show n + 1 + E = n + E + 1 by omega]
    simp only [Nat.succ_eq_add_one]
    omega

private theorem card_antidiagonal_tuple_succ_eq_sum_range (D k : ℕ) :
    (Finset.Nat.antidiagonalTuple (D + 1) k).card =
      ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card := by
  calc (Finset.Nat.antidiagonalTuple (D + 1) k).card
      = ((Finset.range (k + 1)).sigma fun i => Finset.Nat.antidiagonalTuple D (k - i)).card := by
        refine Finset.card_nbij' (fun x => ⟨x 0, Fin.tail x⟩) (fun p => Fin.cons p.1 p.2)
          ?_ ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hx
          rw [Fin.sum_univ_succ] at hx
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple, Fin.tail]
          omega
        · rintro ⟨i, y⟩ hp
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range,
            Finset.Nat.mem_antidiagonalTuple] at hp
          simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ,
            Fin.cons_zero, Fin.cons_succ]
          omega
        · intro x _
          simp
        · rintro ⟨i, y⟩ _
          simp
    _ = ∑ i ∈ Finset.range (k + 1), (Finset.Nat.antidiagonalTuple D (k - i)).card :=
        Finset.card_sigma _ _

private theorem card_antidiagonal_tuple_succ_eq_choose (D : ℕ) :
    ∀ k, (Finset.Nat.antidiagonalTuple (D + 1) k).card = (k + D).choose D := by
  induction D with
  | zero =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range, Finset.sum_eq_single k]
    · simp [Finset.Nat.antidiagonalTuple_zero_zero]
    · intro i hi hik
      simp only [Finset.mem_range] at hi
      obtain ⟨m, hm⟩ : ∃ m, k - i = m + 1 := ⟨k - i - 1, by omega⟩
      rw [hm, Finset.Nat.antidiagonalTuple_zero_succ, Finset.card_empty]
    · intro h
      simp at h
  | succ D ih =>
    intro k
    rw [card_antidiagonal_tuple_succ_eq_sum_range]
    simp only [ih]
    have h : ∑ j ∈ Finset.range (k + 1), (k - j + D).choose D =
        ∑ j ∈ Finset.range (k + 1), (j + D).choose D := by
      have := Finset.sum_range_reflect (fun i => (i + D).choose D) (k + 1)
      simpa only [Nat.add_sub_cancel] using this
    rw [h, sum_range_add_choose_eq_choose_succ, Nat.add_assoc]

theorem sum_antidiagonalTuple : PI.SumAntidiagonalTuple := by
  intro D T hDT
  cases D with
  | zero =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.choose_zero_right]
    rw [Finset.sum_range_succ']
    simp [Finset.Nat.antidiagonalTuple_zero_succ, Finset.Nat.antidiagonalTuple_zero_zero]
  | succ E =>
    obtain ⟨n, rfl⟩ : ∃ n, T = n + E + 2 := ⟨T - E - 2, by omega⟩
    have h1 : n + E + 2 - (E + 1) = n + 1 := by omega
    have h2 : n + E + 2 - 1 = n + E + 1 := by omega
    rw [h1, h2]
    simp only [card_antidiagonal_tuple_succ_eq_choose]
    exact sum_range_add_choose_eq_choose_succ E n
end

section

theorem sumEqTrace_holds : PI.EmbTraceSum := by
  intro E _ _ K φ₀ S _ emb hinj hext hcard y
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have hcomm : ∀ (s : S) (a : K), emb s (algebraMap K E a) = algebraMap K ℂ a := fun s a => hext s a
  let f : S → (E →ₐ[K] ℂ) := fun s => { emb s with commutes' := hcomm s }
  have hf : Function.Injective f := by
    intro s t hst
    apply hinj
    ext x
    exact AlgHom.congr_fun hst x
  have : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  have hcard' : Fintype.card S = Fintype.card (E →ₐ[K] ℂ) := by
    rw [hcard, AlgHom.card]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard'⟩
  have htr := trace_eq_sum_embeddings (K := K) (L := E) (E := ℂ) (x := y)
  calc ∑ s, emb s y = ∑ s, f s y := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ y := Fintype.sum_bijective f hbij _ _ (fun _ => rfl)
    _ = algebraMap K ℂ (Algebra.trace K E y) := htr.symm
    _ = φ₀ ((Algebra.trace K E y : K) : E) := rfl
end

section

private lemma hform_add_right_orbital_bounds_conclusion {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (y + z) = PI.NormGramAtOrigin.hform σ J x y + PI.NormGramAtOrigin.hform σ J x z := by
  simp only [PI.NormGramAtOrigin.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma hform_smul_right_orbital_bounds_conclusion {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    PI.NormGramAtOrigin.hform σ J x (c • y) = c * PI.NormGramAtOrigin.hform σ J x y := by
  simp only [PI.NormGramAtOrigin.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hform_sum_right' {E : Type} [Field E] (σ : E →+* E) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (f : Fin k → Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (∑ a, f a) = ∑ a, PI.NormGramAtOrigin.hform σ J x (f a) := by
  simp only [PI.NormGramAtOrigin.hform, Finset.sum_apply, Finset.mul_sum]
  calc _ = ∑ i, ∑ a, ∑ j, σ (x i) * J i j * f a j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma Hf_sub_right' {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    PI.NormGramAtOrigin.hform σ J x (y - z) = PI.NormGramAtOrigin.hform σ J x y - PI.NormGramAtOrigin.hform σ J x z := by
  simp only [PI.NormGramAtOrigin.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma hform_symm_of_involutive_of_hermitian {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (PI.NormGramAtOrigin.hform σ J x y) = PI.NormGramAtOrigin.hform σ J y x := by

  simp only [PI.NormGramAtOrigin.hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hJ j i]; ring

private lemma hform_add_smul_self_ne_zero_of_isotropic_pair {E : Type} [Field E] [CharZero E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (w y : Fin n → E)
    (hw : PI.NormGramAtOrigin.hform σ J w w = 0) (hy : PI.NormGramAtOrigin.hform σ J y y = 0) (t : E)
    (ht : PI.NormGramAtOrigin.hform σ J w y = t) (ht0 : t ≠ 0) :
    PI.NormGramAtOrigin.hform σ J (w + σ t • y) (w + σ t • y) ≠ 0 := by
  have e1 : PI.NormGramAtOrigin.hform σ J w (w + σ t • y) = σ t * t := by
    rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hw, ht, zero_add]
  have e2 : PI.NormGramAtOrigin.hform σ J y w = σ t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ w y, ht]
  have e3 : PI.NormGramAtOrigin.hform σ J y (w + σ t • y) = σ t := by
    rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hy, e2, mul_zero, add_zero]
  have e4 : PI.NormGramAtOrigin.hform σ J (w + σ t • y) w = t * σ t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ w, e1, map_mul, hσ]
  have e5 : PI.NormGramAtOrigin.hform σ J (w + σ t • y) y = t := by
    rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ y, e3, hσ]
  rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, e4, e5]
  have hs : σ t ≠ 0 := by
    intro h
    apply ht0
    rw [← hσ t, h, map_zero]
  have e6 : t * σ t + σ t * t = 2 * (t * σ t) := by ring
  rw [e6]
  exact mul_ne_zero two_ne_zero (mul_ne_zero ht0 hs)

private lemma exists_ne_zero_mulVec_eq_zero_of_lt {E : Type} [Field E] {k n : ℕ} (hk : k < n) (A : Fin k → Fin n → E) :
    ∃ y : Fin n → E, y ≠ 0 ∧ ∀ a, ∑ j, A a j * y j = 0 := by
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (Matrix.det_eq_zero_of_row_eq_zero
      (A := Matrix.of fun (i j : Fin n) => if h : (i : ℕ) < k then A ⟨i, h⟩ j else 0)
      ⟨k, hk⟩ (fun j => by simp))
  refine ⟨y, hy0, fun a => ?_⟩
  have h := congrFun hy ⟨a, lt_trans a.isLt hk⟩
  simpa [Matrix.mulVec, dotProduct] using h

private lemma exists_hform_ne_zero_of_det_ne_zero {E : Type} [Field E] (σ : E →+* E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJd : J.det ≠ 0) (y : Fin n → E) (hy : y ≠ 0) :
    ∃ z : Fin n → E, PI.NormGramAtOrigin.hform σ J z y ≠ 0 := by
  have hJy : Matrix.mulVec J y ≠ 0 := fun h => hJd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨y, hy, h⟩)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hJy
  refine ⟨Pi.single i 1, ?_⟩
  have e : PI.NormGramAtOrigin.hform σ J (Pi.single i 1) y = Matrix.mulVec J y i := by
    unfold PI.NormGramAtOrigin.hform
    rw [Finset.sum_eq_single i]
    · simp [Matrix.mulVec, dotProduct]
    · intro l _ hl
      simp [Pi.single_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [e]
  exact hi

private lemma hermC_ppos_col_castLE {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (v : Fin k → Fin n → E)
    (hvo : ∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0)
    (hvd : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0) (z y0 : Fin n → E)
    (hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0) (hz : PI.NormGramAtOrigin.hform σ J z y0 ≠ 0) :
    ∃ p : Fin n → E, (∀ b, PI.NormGramAtOrigin.hform σ J (v b) p = 0) ∧ PI.NormGramAtOrigin.hform σ J p y0 ≠ 0 := by
  refine ⟨z - ∑ a, (PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) • v a,
    fun b => ?_, ?_⟩
  · rw [Hf_sub_right', hform_sum_right', Finset.sum_eq_single b]
    · rw [hform_smul_right_orbital_bounds_conclusion, div_mul_cancel₀ _ (hvd b), sub_self]
    · intro a _ hab
      rw [hform_smul_right_orbital_bounds_conclusion, hvo b a (Ne.symm hab), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ b) h
  · rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ y0, Hf_sub_right', hform_sum_right']
    have h0 : ∀ a, PI.NormGramAtOrigin.hform σ J y0
        ((PI.NormGramAtOrigin.hform σ J (v a) z / PI.NormGramAtOrigin.hform σ J (v a) (v a)) • v a) = 0 := by
      intro a
      rw [hform_smul_right_orbital_bounds_conclusion, ← hform_symm_of_involutive_of_hermitian σ hσ J hJ (v a) y0, hy0W a, map_zero, mul_zero]
    simp only [h0, Finset.sum_const_zero, sub_zero]
    rw [hform_symm_of_involutive_of_hermitian σ hσ J hJ]
    exact hz

private lemma Hf_e_e_eq_ite {E : Type} [Field E] [CharZero E] (σ : E →+* E) (hσ : ∀ a, σ (σ a) = a)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (hJd : J.det ≠ 0) :
    ∀ k, k ≤ n → ∃ v : Fin k → Fin n → E,
      (∀ a b, a ≠ b → PI.NormGramAtOrigin.hform σ J (v a) (v b) = 0) ∧
      ∀ a, PI.NormGramAtOrigin.hform σ J (v a) (v a) ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hvo, hvd⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨y0, hy0, hW0⟩ := exists_ne_zero_mulVec_eq_zero_of_lt (Nat.lt_of_succ_le hk) (fun a j => ∑ l, σ (v a l) * J l j)
    have hy0W : ∀ a, PI.NormGramAtOrigin.hform σ J (v a) y0 = 0 := by
      intro a
      calc _ = ∑ j, (∑ l, σ (v a l) * J l j) * y0 j := by
            simp only [PI.NormGramAtOrigin.hform, Finset.sum_mul]
            exact Finset.sum_comm
        _ = 0 := hW0 a
    obtain ⟨z, hz⟩ := exists_hform_ne_zero_of_det_ne_zero σ J hJd y0 hy0
    obtain ⟨p, hpW, hp⟩ := hermC_ppos_col_castLE σ hσ J hJ v hvo hvd z y0 hy0W hz
    have key : ∃ y, (∀ a, PI.NormGramAtOrigin.hform σ J (v a) y = 0) ∧
        PI.NormGramAtOrigin.hform σ J y y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      refine hform_add_smul_self_ne_zero_of_isotropic_pair σ hσ J hJ p y0 (hcon p hpW) (hcon y0 hy0W) _ rfl hp (hcon _ fun a => ?_)
      rw [hform_add_right_orbital_bounds_conclusion, hform_smul_right_orbital_bounds_conclusion, hpW a, hy0W a, mul_zero, add_zero]
    obtain ⟨y, hyW, hyy⟩ := key
    refine ⟨Fin.snoc (α := fun _ => Fin n → E) v y, fun a b hab => ?_, fun a => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvo a b fun h => hab (congrArg Fin.castSucc h)
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact hyW a
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← hform_symm_of_involutive_of_hermitian σ hσ J hJ, hyW b, map_zero]
      · exact absurd rfl hab
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact hvd a
      · simp only [Fin.snoc_last]
        exact hyy

theorem exists_nondegenerate : PI.NormGramAtOrigin.Statement := by
  unfold PI.NormGramAtOrigin.Statement
  intro E _ _ _ n r hr J hJ hJd
  have hσ : ∀ a : E, starRingEnd E (starRingEnd E a) = a := fun a => by simp
  have hJ' : ∀ i j, starRingEnd E (J j i) = J i j := fun i j => by
    rw [starRingEnd_apply]
    exact hJ i j
  obtain ⟨v, hvo, hvd⟩ := Hf_e_e_eq_ite (starRingEnd E) hσ J hJ' hJd r hr
  refine ⟨v, ?_⟩
  have hg : PI.NormGramAtOrigin.gram (starRingEnd E) J v =
      Matrix.diagonal (fun a => PI.NormGramAtOrigin.hform (starRingEnd E) J (v a) (v a)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [PI.NormGramAtOrigin.gram]
    · simp [PI.NormGramAtOrigin.gram, Matrix.diagonal_apply_ne _ h, hvo a b h]
  rw [hg, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => hvd a
end

section

namespace PI

theorem exists_minimalNormVector : PI.LatMin := by
  intro p _ σ B L W hp2 _ _ hL hsm hadd hsym hne
  refine PI.LatMinWork.main hp2 B L hL ?_ hadd hsym hne
  intro c u v
  have h : c • u = (c : ℚ_[p]) • u := (algebraMap_smul ℚ_[p] c u).symm
  rw [h, hsm]

end PI
end

section

open NumberField

theorem isPrime_span_of_jacobi_neg_one : PI.InertPrime := by
  intro K _ _ hK b d p hb hp hj
  exact PI.InertPrimeWork.inert K hK b d p hb hp hj
end

section

theorem quotient_sigma_finite : PI.QuotNuSigma.Target :=
  fun _ _ _ _ _ _ _ _ _ μG _ A B μA μB ν hA hB hW =>
    PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil μG A B μA μB ν hA hB hW
end
