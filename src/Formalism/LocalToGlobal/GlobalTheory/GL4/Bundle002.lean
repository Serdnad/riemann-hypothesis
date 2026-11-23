module

public import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
public import Formalism.LocalRingCardinality.Bundle002
public import Formalism.LocalToGlobal.Columns.Bundle008
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Formalism.LocalToGlobal.Columns.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree Formalism.HN

theorem trace_re_sum (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding z).re := by
  classical
  have h1 : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ z := by
    have h : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z :=
      trace_eq_sum_embeddings ℂ (x := z)
    rw [show ((Algebra.trace ℚ E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E z) from
      (eq_ratCast _ _).symm, h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ z)
      (fun σ : E →ₐ[ℚ] ℂ => σ z) (fun _ => rfl)).symm
  have h2 : ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ φ : E →+* ℂ, (φ z).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  rw [h2, ← Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ)
    (fun φ : E →+* ℂ => (φ z).re)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfib : ∀ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w),
      (φ z).re = (w.embedding z).re := by
    intro φ hφ
    have hw := (Finset.mem_filter.mp hφ).2
    subst hw
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
  have hm : w.mult = 2 := InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  rw [hm]
  norm_num

theorem two_nPl (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : 2 * nPl E = Module.finrank ℚ E := by
  classical
  rw [← InfinitePlace.sum_mult_eq]
  have h : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  unfold nPl
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma sum_log_le_card_mul_log_mean_of_pos {ι : Type*} [Fintype ι] (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (hn : 0 < (Fintype.card ι : ℝ)) :
    ∑ i, Real.log (S i) ≤ (Fintype.card ι : ℝ) * Real.log ((∑ i, S i) / Fintype.card ι) := by
  have hT : 0 < ∑ i, S i := by
    have : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hn)
    exact Finset.sum_pos (fun i _ => hS i) Finset.univ_nonempty
  set M := (∑ i, S i) / (Fintype.card ι : ℝ) with hM
  have hMpos : 0 < M := div_pos hT hn
  have h1 : ∀ i, Real.log (S i) - Real.log M ≤ S i / M - 1 := by
    intro i
    rw [← Real.log_div (hS i).ne' hMpos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (hS i) hMpos)
  have h2 : ∑ i, (Real.log (S i) - Real.log M) ≤ ∑ i, (S i / M - 1) :=
    Finset.sum_le_sum fun i _ => h1 i
  have h3 : (∑ i, S i) / M = (Fintype.card ι : ℝ) := by
    have := hT.ne'
    have := hn.ne'
    rw [hM]
    field_simp
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, h3, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one] at h2
  linarith

theorem shortAt_mean_log (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) [IsTotallyComplex D.host.E]
    (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hy : Formalism.MainNotions.flipTwoThree.ShortAt D u c y)
    (hpos : ∀ (w : InfinitePlace D.host.E) a, 0 < (w.embedding ((D.sp.X 0).hT (y a) (y a))).re) :
    (∑ w : InfinitePlace D.host.E, Real.log (∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re)) / (nPl D.host.E : ℝ) ≤
      Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
  classical
  obtain ⟨-, -, htr⟩ := hy
  have hk : D.R.N 0 = D.R.k := Formalism.BasicNotions.Ranks.N_zero D.R
  have hfin := Formalism.MainNotions.flipTwoThree.b_finrank_host D
  have hnf : nPl D.host.E = D.R.f := by
    have h2 := two_nPl D.host.E
    rw [hfin] at h2
    omega
  have hfo : D.R.f = 2 * D.R.ord := Formalism.BasicNotions.Ranks.f_eq_ord D.R
  have hf : 0 < D.R.f := by
    have := D.R.m_le_f
    have := D.R.two_le_m
    omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hbound : ∀ a, ∑ w : InfinitePlace D.host.E, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤
      (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2) := by
    intro a
    have h := htr a
    rw [trace_re_sum, div_le_iff₀ (by linarith), ← Finset.mul_sum] at h
    nlinarith [h]
  have hS : ∀ w : InfinitePlace D.host.E, 0 < ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re := by
    intro w
    have hne : (Finset.univ : Finset (Fin (D.R.N 0))).Nonempty := by
      refine ⟨⟨0, ?_⟩, Finset.mem_univ _⟩
      rw [hk]
      have := D.R.m_add_three_le_k
      omega
    exact Finset.sum_pos (fun a _ => hpos w a) hne
  have htot : ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤
      (D.R.k : ℝ) * ((D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2)) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _a : Fin (D.R.N 0), (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2) :=
          Finset.sum_le_sum fun a _ => hbound a
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hk, nsmul_eq_mul]
  have hcard : (nPl D.host.E : ℝ) = (Fintype.card (InfinitePlace D.host.E) : ℝ) := rfl
  have hcf : (Fintype.card (InfinitePlace D.host.E) : ℝ) = D.R.f := by
    rw [← hcard]
    exact_mod_cast hnf
  have hnpos : (0 : ℝ) < (Fintype.card (InfinitePlace D.host.E) : ℝ) := by rw [hcf]; exact hfR
  have key := sum_log_le_card_mul_log_mean_of_pos _ hS hnpos
  have hTpos : 0 < ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re :=
    Finset.sum_pos (fun w _ => hS w)
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by exact_mod_cast hnpos)))
  rw [hcard, div_le_iff₀ hnpos]
  refine key.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hnpos.le
  apply Real.log_le_log (div_pos hTpos hnpos)
  rw [div_le_iff₀ hnpos, hcf]
  nlinarith [htot]

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.Col Formalism.MainNotions.flipTwoThree Formalism.L2.DIV

section Mono

variable {ι : Type} [Fintype ι] {n : ℕ}

private theorem map_algebraMap_rat_complex_hw {N : ℕ} (ν : Fin N → ℕ) :
    MvPolynomial.map (algebraMap ℚ ℂ) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) ν) = Formalism.GradedWeylDivisibility.hw ℂ (le_refl N) ν := by
  unfold Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.map_X]

theorem fockN_ext_cNu (lam : DomWeight n) :
    fockN (extremal ℂ n lam) = cNu lam.natW * ∏ s, ((lam.natW s).factorial : ℝ) := by
  have hprod : (∏ s, ((lam.natW s).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  unfold extremal cNu
  rw [← map_algebraMap_rat_complex_hw, Formalism.L2.Col.fock_norm_rational_eq, div_mul_cancel₀ _ hprod]

theorem cNu_natW_pos (lam : DomWeight n) : 0 < cNu lam.natW := by
  have hnn : (0 : ℚ) ≤ Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) := by
    unfold Formalism.GradedWeylDivisibility.fockQ
    exact Finset.sum_nonneg fun m _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)
  have hpos : (0 : ℚ) < Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl lam.natW) :=
    lt_of_le_of_ne hnn (Formalism.L2.DIV.we_hw_norm_ne le_rfl lam.natW).symm
  unfold cNu
  apply div_pos
  · exact_mod_cast hpos
  · exact Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _

def monCnu (lam : ι → DomWeight n) : ℝ := ((n : ℝ) ^ (∑ τ, dW (lam τ)) * ∏ τ, cNu (lam τ).natW)⁻¹

private theorem sub_one_mul_padicValNat_factorial_le' {n : ℕ} (g : Fin n → ℕ) :
    (∑ a, g a).factorial ≤ n ^ (∑ a, g a) * ∏ a, (g a).factorial := by
  classical
  have hmul := Nat.multinomial_spec Finset.univ g
  have hle : Nat.multinomial Finset.univ g ≤ n ^ (∑ a, g a) := by
    have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℕ)) (∑ a, g a)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, one_pow,
      Finset.prod_const_one, Nat.cast_id] at h
    rw [h]
    apply Finset.single_le_sum (f := fun k => Nat.multinomial Finset.univ k) (fun _ _ => Nat.zero_le _)
    rw [Finset.mem_piAntidiag]
    exact ⟨rfl, fun i _ => Finset.mem_univ i⟩
  calc (∑ a, g a).factorial = (∏ a, (g a).factorial) * Nat.multinomial Finset.univ g := hmul.symm
    _ ≤ (∏ a, (g a).factorial) * n ^ (∑ a, g a) := Nat.mul_le_mul_left _ hle
    _ = _ := mul_comm _ _

theorem monW_ge_cNu (lam : ι → DomWeight n) (m : MonI lam) : monCnu lam ≤ monW lam m := by
  classical
  have hC : 0 < ∏ τ, cNu (lam τ).natW := Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)
  have hF : (0 : ℝ) < ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun s _ => by exact_mod_cast Nat.factorial_pos _
  have hND : (0 : ℝ) < (n : ℝ) ^ (∑ τ, dW (lam τ)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [dW]
    · exact pow_pos (by exact_mod_cast hn) _
  have hext : extremalFockNormProduct lam = (∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) := by
    unfold extremalFockNormProduct
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => fockN_ext_cNu (lam τ)
  have hcombN : ∏ τ, ∏ s, ((lam τ).natW s).factorial ≤ Formalism.L2.DIV.mfact m.1 * n ^ (∑ τ, dW (lam τ)) := by
    have hmf : Formalism.L2.DIV.mfact m.1 = ∏ τ, ∏ s, ∏ a, (m.1 (τ, a, s)).factorial := by
      unfold Formalism.L2.DIV.mfact
      rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
        rw [show m.1 k = 0 from by simpa using hk, Nat.factorial_zero])]
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Fintype.prod_prod_type, Finset.prod_comm]
    have hpow : n ^ (∑ τ, dW (lam τ)) = ∏ τ, ∏ s, n ^ ((lam τ).natW s) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      unfold dW
      rw [← Finset.prod_pow_eq_pow_sum]
    rw [hmf, hpow, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
    intro τ _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
    intro s _
    have h := sub_one_mul_padicValNat_factorial_le' (fun a => m.1 (τ, a, s))
    rw [m.2 τ s] at h
    exact h.trans (le_of_eq (mul_comm _ _))
  have hcomb : (∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ)) ≤
      (Formalism.L2.DIV.mfact m.1 : ℝ) * (n : ℝ) ^ (∑ τ, dW (lam τ)) := by
    exact_mod_cast hcombN
  unfold monCnu monW
  rw [hext, inv_eq_one_div, div_le_div_iff₀ (mul_pos hND hC) (mul_pos hC hF)]
  calc 1 * ((∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ))
      = (∏ τ, cNu (lam τ).natW) * ∏ τ, ∏ s, (((lam τ).natW s).factorial : ℝ) := one_mul _
    _ ≤ (∏ τ, cNu (lam τ).natW) * ((Formalism.L2.DIV.mfact m.1 : ℝ) * (n : ℝ) ^ (∑ τ, dW (lam τ))) :=
      mul_le_mul_of_nonneg_left hcomb hC.le
    _ = _ := by ring

theorem monCnu_pos (lam : ι → DomWeight n) : 0 < monCnu lam := by
  unfold monCnu
  apply inv_pos.mpr
  apply mul_pos
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [dW]
    · exact pow_pos (by exact_mod_cast hn) _
  · exact Finset.prod_pos fun τ _ => cNu_natW_pos (lam τ)

theorem log_monCnu (lam : ι → DomWeight n) (hn : 0 < n) :
    -Real.log (monCnu lam) = ∑ τ, ((dW (lam τ) : ℝ) * Real.log n + Real.log (cNu (lam τ).natW)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ∀ τ, cNu (lam τ).natW ≠ 0 := fun τ => (cNu_natW_pos (lam τ)).ne'
  unfold monCnu
  rw [Real.log_inv, neg_neg, Real.log_mul (pow_ne_zero _ hn'.ne') (Finset.prod_ne_zero_iff.mpr fun τ _ => hc τ),
    Real.log_pow, Real.log_prod (fun τ _ => hc τ), Finset.sum_add_distrib]
  push_cast
  rw [Finset.sum_mul]

end Mono

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
