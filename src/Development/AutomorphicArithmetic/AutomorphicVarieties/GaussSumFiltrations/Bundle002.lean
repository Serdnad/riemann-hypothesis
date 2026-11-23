module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.Growth

open UpperHalfPlane hiding I

def sF (w : ℍ) : ℝ := (1 + ‖(w : ℂ)‖ ^ 2) / w.im

lemma sq_norm_coe (w : ℍ) : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, coe_re, coe_im]
  ring

lemma one_le_sF (w : ℍ) : 1 ≤ sF w := by
  have him := w.im_pos
  rw [sF, le_div_iff₀ him, one_mul, sq_norm_coe]
  nlinarith [sq_nonneg w.re, sq_nonneg (w.im - 1)]

lemma sF_nonneg (w : ℍ) : 0 ≤ sF w := zero_le_one.trans (one_le_sF w)

lemma poly_bound (a b c d x y : ℝ) :
    (c * x + d) ^ 2 + (c * y) ^ 2 + ((a * x + b) ^ 2 + (a * y) ^ 2) ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (1 + (x ^ 2 + y ^ 2)) := by
  nlinarith [sq_nonneg (a - b * x), sq_nonneg (c - d * x), sq_nonneg (b * y), sq_nonneg (d * y)]

lemma normSq_lin (a b : ℝ) (z : ℍ) :
    Complex.normSq ((a : ℂ) * z + b) = (a * z.re + b) ^ 2 + (a * z.im) ^ 2 := by
  simp [Complex.normSq_apply]; ring

lemma sF_smul (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, sF (g • z) ≤ K * sF z := by
  have hD : 0 < |g.det.val| := abs_pos.mpr g.det.ne_zero
  refine ⟨((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) / |g.det.val|, by positivity, fun z => ?_⟩
  have hN : 0 < Complex.normSq (denom g z) := normSq_denom_pos g z.im_ne_zero
  have him := z.im_pos
  have h1 : sF (g • z) =
      (Complex.normSq (denom g z) + Complex.normSq (num g z)) / (|g.det.val| * z.im) := by
    rw [sF, im_smul_eq_div_normSq, coe_smul, norm_σ, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
    field_simp
  have h2 : Complex.normSq (denom g z) + Complex.normSq (num g z) ≤
      ((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) * (1 + ‖(z : ℂ)‖ ^ 2) := by
    have e1 : Complex.normSq (denom g z) = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    have e2 : Complex.normSq (num g z) = (g 0 0 * z.re + g 0 1) ^ 2 + (g 0 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    rw [e1, e2, sq_norm_coe]
    exact poly_bound _ _ _ _ _ _
  rw [h1, sF, div_mul_div_comm]
  exact div_le_div_of_nonneg_right h2 (mul_pos hD him).le

lemma denom_inv (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, ‖denom g z‖⁻¹ ≤ K * sF z := by
  have hq : 0 < (g 1 0) ^ 2 + (g 1 1) ^ 2 := by
    by_contra hc
    push_neg at hc
    have h10 : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have h11 : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hdet := g.det.ne_zero
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h11] at hdet
  refine ⟨1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2), by positivity, fun z => ?_⟩
  have him := z.im_pos
  have hm : 0 < ‖denom g z‖ := norm_pos_iff.mpr (denom_ne_zero g z)
  have hN : ‖denom g z‖ ^ 2 = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 := by
    rw [Complex.sq_norm]
    exact normSq_lin _ _ z
  have key : ((g 1 0) ^ 2 + (g 1 1) ^ 2) * z.im ^ 2 ≤ ‖denom g z‖ ^ 2 * (1 + ‖(z : ℂ)‖ ^ 2) := by
    rw [hN, sq_norm_coe]
    nlinarith [sq_nonneg (g 1 0 * z.re + g 1 1),
      sq_nonneg ((g 1 0 * z.re + g 1 1) * z.re + g 1 0 * z.im ^ 2)]
  have hK1 : 1 ≤ 1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by
    have : 0 ≤ 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by positivity
    linarith
  have hKq : (1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2)) * ((g 1 0) ^ 2 + (g 1 1) ^ 2) =
      ((g 1 0) ^ 2 + (g 1 1) ^ 2) + 1 := by
    field_simp
  have hT1 : 1 ≤ 1 + ‖(z : ℂ)‖ ^ 2 := by nlinarith [sq_nonneg ‖(z : ℂ)‖]
  set q := (g 1 0) ^ 2 + (g 1 1) ^ 2 with hqdef
  set K := 1 + 1 / q with hKdef
  set T := 1 + ‖(z : ℂ)‖ ^ 2 with hTdef
  set m := ‖denom g z‖ with hmdef
  have h1 : 1 ≤ K ^ 2 * q * T := by
    have e : K ^ 2 * q * T = K * (K * q) * T := by ring
    rw [e, hKq]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK1 (by linarith)) hT1
  have hsq : z.im ^ 2 ≤ (K * T * m) ^ 2 := by
    have e : (K * T * m) ^ 2 = K ^ 2 * T * (m ^ 2 * T) := by ring
    rw [e]
    have hKT : 0 ≤ K ^ 2 * T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left key hKT, mul_le_mul_of_nonneg_right h1 (sq_nonneg z.im)]
  have hP : 0 ≤ K * T * m := by positivity
  have hy : z.im ≤ K * T * m := by nlinarith
  rw [inv_eq_one_div, div_le_iff₀ hm, sF, ← hTdef,
    show K * (T / z.im) * m = (K * T * m) / z.im by ring, le_div_iff₀ him, one_mul]
  exact hy

variable {F : Type} [Field F] [NumberField F]

def sP (z : Hn F) : ℝ := ∏ v, sF (z v)

lemma one_le_sP (z : Hn F) : 1 ≤ sP z := by
  calc (1 : ℝ) = ∏ v, (1 : ℝ) := by simp
    _ ≤ ∏ v, sF (z v) := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun v _ => one_le_sF _)

lemma sP_nonneg (z : Hn F) : 0 ≤ sP z := zero_le_one.trans (one_le_sP z)

lemma gr_iff (f : Hn F → ℂ) : Gr f ↔ ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C * sP z ^ A := by
  rw [Gr.eq_1]
  constructor
  · rintro ⟨C, A, hC⟩
    refine ⟨max C 0, A, le_max_right _ _, fun z => (hC z).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (sP_nonneg z) A)
  · rintro ⟨C, A, -, hC⟩
    exact ⟨C, A, hC⟩

lemma gr_add {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f + g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 + C2, A1 + A2, add_nonneg hC1 hC2, fun z => ?_⟩
  have hP := one_le_sP z
  have e1 : sP z ^ A1 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  have e2 : sP z ^ A2 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  calc ‖(f + g) z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C1 * sP z ^ A1 + C2 * sP z ^ A2 := add_le_add (h1 z) (h2 z)
    _ ≤ C1 * sP z ^ (A1 + A2) + C2 * sP z ^ (A1 + A2) :=
      add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
    _ = (C1 + C2) * sP z ^ (A1 + A2) := by ring

lemma gr_mul {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f * g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 * C2, A1 + A2, mul_nonneg hC1 hC2, fun z => ?_⟩
  calc ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C1 * sP z ^ A1) * (C2 * sP z ^ A2) :=
      mul_le_mul (h1 z) (h2 z) (norm_nonneg _) (mul_nonneg hC1 (pow_nonneg (sP_nonneg z) _))
    _ = C1 * C2 * sP z ^ (A1 + A2) := by ring

lemma gr_const (c : ℂ) : Gr (fun _ : Hn F => c) := by
  rw [gr_iff]
  exact ⟨‖c‖, 0, norm_nonneg _, fun z => by simp⟩

lemma gr_smul (c : ℂ) {f : Hn F → ℂ} (hf : Gr f) : Gr (c • f) := gr_mul (gr_const c) hf

lemma gr_act (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (fun z => f (act h z)) := by
  rw [gr_iff] at hf ⊢
  obtain ⟨C, A, hC, hfz⟩ := hf
  choose K hK0 hK using fun v : InfinitePlace F => sF_smul (cmp v h)
  have hact : ∀ z : Hn F, sP (act h z) ≤ (∏ v, K v) * sP z := by
    intro z
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro v _
      exact sF_nonneg _
    · intro v _
      rw [act.eq_1]
      exact hK v (z v)
  refine ⟨C * (∏ v, K v) ^ A, A,
    mul_nonneg hC (pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) A), fun z => ?_⟩
  calc ‖f (act h z)‖ ≤ C * sP (act h z) ^ A := hfz _
    _ ≤ C * ((∏ v, K v) * sP z) ^ A :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sP_nonneg _) (hact z) A) hC
    _ = C * (∏ v, K v) ^ A * sP z ^ A := by ring

lemma gr_denom (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    Gr (fun z : Hn F => (∏ v, denom (GlobalTheory.HilbertThetaSeries.cmp v h) (z v))⁻¹ ^ k) := by
  rw [gr_iff]
  choose K hK0 hK using fun v : InfinitePlace F => denom_inv (cmp v h)
  refine ⟨(∏ v, K v) ^ k, k, pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) k, fun z => ?_⟩
  have hb : ‖(∏ v, denom (cmp v h) (z v))⁻¹‖ ≤ (∏ v, K v) * sP z := by
    rw [norm_inv, norm_prod, ← Finset.prod_inv_distrib]
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro v _
      positivity
    · intro v _
      exact hK v (z v)
  rw [norm_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hb k

lemma hilbertModerateGrowth_unnormalizedSlash (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl0 k h f) :=
  gr_mul (gr_denom k h) (gr_act h hf)

lemma gr_sl (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl k h f) :=
  gr_mul (gr_const _) (hilbertModerateGrowth_unnormalizedSlash k h hf)

theorem gr_closed : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Gr f → Gr g → Gr (f + g) ∧ Gr (c • f) ∧ Gr (f * g) ∧ Gr (1 : Hn F → ℂ) ∧ Gr (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Gr (sl0 k h f) ∧ Gr (sl k h f) :=
  fun _ _ _ k _ _ c hf hg =>
    ⟨gr_add hf hg, gr_smul c hf, gr_mul hf hg, gr_const 1, gr_const 0, fun h _ => ⟨hilbertModerateGrowth_unnormalizedSlash k h hf, gr_sl k h hf⟩⟩

end GlobalTheory.HilbertThetaSeries.Growth
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem isSB_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ)
    (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  intro F _ _ κ _ _ N Φ hN hSB
  classical
  obtain ⟨hsupp, hper⟩ := hSB
  have memLL : ∀ y : κ → F, y ∈ LL F κ ↔ ∀ k, IsIntegral ℤ (y k) := by
    intro y
    simp [LL, AddSubgroup.mem_pi, mem_integralClosure_iff]
  have memaL : ∀ (c : F) (x : κ → F), x ∈ aL κ c ↔ ∃ y ∈ LL F κ, c • y = x := by
    intro c x
    simp [aL]
  have intB : ∀ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ,
      IsIntegral ℤ (∑ i, c i • integralBasis F i) := by
    intro c
    have hmem : (∑ i, c i • integralBasis F i) ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, rfl⟩
    obtain ⟨a, ha⟩ := (mem_span_integralBasis F).mp hmem
    rw [← ha]
    exact RingOfIntegers.isIntegral_coe a
  have decomp : ∀ z : F, IsIntegral ℤ z →
      ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • integralBasis F i = z := by
    intro z hz
    have hmem : z ∈ Submodule.span ℤ (Set.range (integralBasis F)) :=
      (mem_span_integralBasis F).mpr ⟨⟨z, hz⟩, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hM : (0 : ℤ) < ((N * N : ℕ) : ℤ) := by positivity
  let g : (κ → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → Fin (N * N)) → ℂ := fun r =>
    Φ (fun k => (N : F)⁻¹ * ∑ i, (((r k i : ℕ) : ℤ) • integralBasis F i))
  refine ((Set.finite_range g).insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  rw [Set.mem_insert_iff]
  by_cases h0 : Φ x = 0
  · exact Or.inl h0
  right
  obtain ⟨y, hy, rfl⟩ := (memaL _ x).mp (hsupp x h0)
  have hyi := (memLL y).mp hy
  choose c hc using fun k => decomp (y k) (hyi k)
  have hcast : ∀ k i, (((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) = c k i % ((N * N : ℕ) : ℤ) :=
    fun k i => Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  refine ⟨fun k i => ⟨(c k i % ((N * N : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
  · have h2 := Int.emod_lt_of_pos (c k i) hM
    have h3 := hcast k i
    omega
  · show Φ (fun k => (N : F)⁻¹ *
        ∑ i, ((((c k i % ((N * N : ℕ) : ℤ)).toNat : ℕ) : ℤ) • integralBasis F i)) = Φ ((N : F)⁻¹ • y)
    simp only [hcast]
    have hl : ((N : F)⁻¹ • y - fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) ∈ aL κ (N : F) := by
      rw [memaL]
      refine ⟨fun k => ∑ i, (c k i / ((N * N : ℕ) : ℤ)) • integralBasis F i, ?_, ?_⟩
      · rw [memLL]
        intro k
        exact intB _
      · funext k
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [← hc k, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [zsmul_eq_mul]
        have hdiv : ((c k i : ℤ) : F) = ((N : F) * N) * ((c k i / ((N * N : ℕ) : ℤ) : ℤ) : F) +
            ((c k i % ((N * N : ℕ) : ℤ) : ℤ) : F) := by
          exact_mod_cast (Int.mul_ediv_add_emod (c k i) ((N * N : ℕ) : ℤ)).symm
        have key : ∀ (cF rF qF : F), cF = ((N : F) * N) * qF + rF →
            (N : F) * (qF * integralBasis F i) =
              (N : F)⁻¹ * (cF * integralBasis F i) - (N : F)⁻¹ * (rF * integralBasis F i) := by
          intro cF rF qF h
          rw [h]
          field_simp
          ring
        exact key _ _ _ hdiv
    have hp := hper (fun k => (N : F)⁻¹ *
        ∑ i, ((c k i % ((N * N : ℕ) : ℤ)) • integralBasis F i)) _ hl
    rw [add_sub_cancel] at hp
    exact hp.symm

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.lattice_periodic_function_range_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (N : ℕ) (Φ : (κ → F) → ℂ), 0 < N → IsSB N Φ → (Set.range Φ).Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.isSB_range_finite | exact GlobalTheory.HilbertThetaSeries.isSB_range_finite | (intros; apply GlobalTheory.HilbertThetaSeries.isSB_range_finite <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_abs_eq_place {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    |reAt v x| = v x := by
  have hw : v.IsReal := IsTotallyReal.isReal v
  rw [← InfinitePlace.norm_embedding_of_isReal hw x]
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply hw x, Complex.ofReal_re, Real.norm_eq_abs]

theorem reAt_sub_place {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) (x y : F) :
    reAt v (x - y) = reAt v x - reAt v y := by
  unfold reAt
  simp [map_sub]

theorem reAt_zero_place {F : Type} [Field F] [NumberField F] (v : InfinitePlace F) :
    reAt v 0 = 0 := by
  unfold reAt; simp

private theorem infinitePlace_le_of_totally_positive_gap {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ξ η : F)
    (h1 : η = 0 ∨ TP η) (h2 : ξ - η = 0 ∨ TP (ξ - η)) (w : InfinitePlace F) : w η ≤ w ξ := by
  have key : 0 ≤ reAt w η ∧ reAt w η ≤ reAt w ξ := by
    rcases h1 with h1 | h1
    · subst h1
      refine ⟨by simp [reAt_zero_place], ?_⟩
      rcases h2 with h2 | h2
      · rw [sub_zero] at h2
        simp [h2, reAt_zero_place]
      · have := h2 w
        rw [sub_zero] at this
        simpa [reAt_zero_place] using this.le
    · refine ⟨(h1 w).le, ?_⟩
      rcases h2 with h2 | h2
      · rw [sub_eq_zero] at h2
        simp [h2]
      · have := h2 w
        rw [reAt_sub_place] at this
        linarith
  rw [← reAt_abs_eq_place w η, ← reAt_abs_eq_place w ξ, abs_of_nonneg key.1,
    abs_of_nonneg (key.1.trans key.2)]
  exact key.2

theorem finite_tp_box : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (D : ℕ), 0 < D → ∀ ξ : F, {η : F | (η = 0 ∨ TP η) ∧ (ξ - η = 0 ∨ TP (ξ - η)) ∧ IsIntegral ℤ ((D : F) * η)}.Finite := by
  intro F _ _ _ D hD ξ
  have hfin := NumberField.Embeddings.finite_of_norm_le F ℂ ((D : ℝ) * ∑ w : InfinitePlace F, w ξ)
  have hD' : (D : F) ≠ 0 := by exact_mod_cast hD.ne'
  refine (Set.Finite.preimage (f := fun η : F => (D : F) * η)
    (fun a _ b _ h => mul_left_cancel₀ hD' h) hfin).subset ?_
  rintro η ⟨h1, h2, h3⟩
  refine ⟨h3, fun φ => ?_⟩
  have hle : (InfinitePlace.mk φ) η ≤ (InfinitePlace.mk φ) ξ := infinitePlace_le_of_totally_positive_gap ξ η h1 h2 _
  have hsum : (InfinitePlace.mk φ) ξ ≤ ∑ w : InfinitePlace F, w ξ :=
    Finset.single_le_sum (f := fun w : InfinitePlace F => w ξ) (fun w _ => apply_nonneg w ξ)
      (Finset.mem_univ _)
  rw [InfinitePlace.apply] at hle
  show ‖φ ((D : F) * η)‖ ≤ (D : ℝ) * ∑ w : InfinitePlace F, w ξ
  rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (hle.trans hsum) (Nat.cast_nonneg _)

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.totallyPositive_summands_with_denominator_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (D : ℕ), 0 < D → ∀ ξ : F, {η : F | (η = 0 ∨ TP η) ∧ (ξ - η = 0 ∨ TP (ξ - η)) ∧ IsIntegral ℤ ((D : F) * η)}.Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.finite_tp_box | exact GlobalTheory.HilbertThetaSeries.finite_tp_box | (intros; apply GlobalTheory.HilbertThetaSeries.finite_tp_box <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.HolKeep

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F]

def U (F : Type) [Field F] [NumberField F] : Set (InfinitePlace F → ℂ) := {z | ∀ v, 0 < (z v).im}

theorem cmp_det (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    ((cmp v h).det : ℝ) = (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  simp [cmp, Matrix.GeneralLinearGroup.map_det]

def mob (h : GL (Fin 2) (InfinitePlace F → ℝ)) (z : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
  fun v => num (cmp v h) (z v) / denom (cmp v h) (z v)

theorem mob_im_pos {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) (v) :
    0 < (mob h z v).im := by
  have hd : 0 < ((cmp v h).det : ℝ) := by
    rw [cmp_det]
    exact hh v
  have hzv : 0 < (z v).im := hz v
  show 0 < (num (cmp v h) (z v) / denom (cmp v h) (z v)).im
  rw [moebius_im]
  exact div_pos (mul_pos hd hzv) (normSq_denom_pos _ hzv.ne')

theorem mob_mapsTo {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) : Set.MapsTo (mob h) (U F) (U F) := by
  intro z hz
  show ∀ v, 0 < (mob h z v).im
  exact fun v => mob_im_pos hh hz v

theorem mob_diff (h : GL (Fin 2) (InfinitePlace F → ℝ)) : DifferentiableOn ℂ (mob h) (U F) := by
  rw [differentiableOn_pi]
  intro v z hz
  have hzv : (z v).im ≠ 0 := (hz v).ne'
  have hp : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => w v) z := differentiable_apply v z
  have hn : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => num (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  have hd : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => denom (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun w => num (cmp v h) (w v) / denom (cmp v h) (w v)) z
  simp only [div_eq_mul_inv]
  exact hn.mul (hd.inv (denom_ne_zero_of_im _ hzv))

theorem act_eq {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) :
    act h (fun v => ofComplex (z v)) = fun v => ofComplex (mob h z v) := by
  funext v
  rw [act.eq_1, ofComplex_apply_of_im_pos (hz v), ofComplex_apply_of_im_pos (mob_im_pos hh hz v)]
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [cmp_det]; exact hh v)]
  rfl

theorem hilbertHolomorphic_unnormalizedSlash_of_pos (k : ℕ) {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {f : Hn F → ℂ} (hf : Hol f) :
    Hol (sl0 k h f) := by
  have hF : DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => f (fun v => ofComplex (z v))) (U F) := hf
  have hcomp := hF.comp (mob_diff h) (mob_mapsTo hh)
  have hden : DifferentiableOn ℂ
      (fun z : InfinitePlace F → ℂ => (∏ v, denom (cmp v h) (z v))⁻¹ ^ k) (U F) := by
    intro z hz
    have hne : (∏ v, denom (cmp v h) (z v)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun v _ => denom_ne_zero_of_im _ (hz v).ne'
    have hpr : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => ∏ v, denom (cmp v h) (w v)) z := by
      simp only [denom]
      fun_prop
    exact ((hpr.inv hne).pow k).differentiableWithinAt
  show DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => sl0 k h f (fun v => ofComplex (z v))) (U F)
  refine (hden.mul hcomp).congr ?_
  intro z hz
  have hc : ∀ v, ((ofComplex (z v) : ℍ) : ℂ) = z v := fun v => by
    rw [ofComplex_apply_of_im_pos (hz v)]
  simp only [sl0.eq_1, act_eq hh hz, hc, Function.comp_apply, Pi.mul_apply]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Hol f → Hol g → Hol (f + g) ∧ Hol (c • f) ∧ Hol (f * g) ∧ Hol (1 : Hn F → ℂ) ∧ Hol (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Hol (sl0 k h f) ∧ Hol (sl k h f) := by
  intro F _ _ k f g c hf hg
  refine ⟨DifferentiableOn.add hf hg, DifferentiableOn.const_smul hf c, DifferentiableOn.mul hf hg,
    differentiableOn_const 1, differentiableOn_const 0, fun h hh => ⟨hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf, ?_⟩⟩
  exact DifferentiableOn.mul (differentiableOn_const _) (hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf)

end GlobalTheory.HilbertThetaSeries.HolKeep
end
end
