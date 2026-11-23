module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GenFrameSpan

open CutKW

theorem genFrameSB_of (hb : StepBack) (hs : StepSpan) (ht : StepSat) : CutKW.KWsb := by
  intro hSB Lt _ _ l _ N0 N1 nu Th B
  exact ⟨fun h I => ht hSB Lt l N0 nu _ B (hs Lt l N0 N1 nu Th I) (h I), hb Lt l N0 N1 nu Th B⟩

end GenFrameSpan
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

theorem stepSat_of (hP : ProjZ) : StepSat := by
  intro hadm Lt _ _ l _ N0 nu P B hPmem hPc
  obtain ⟨T, hTmem, hTfix⟩ := hP hadm Lt N0 nu
  have ha : ∀ m, ∃ a : ColChoice N0 nu →₀ ℤ,
      (a.sum fun J k => k • nablaX N0 nu J) = T (MvPolynomial.monomial m 1) :=
    fun m => Finsupp.mem_span_range_iff_exists_finsupp.mp (hTmem _)
  choose a ha using ha
  let S : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
    (MvPolynomial.basisMonomials _ ℂ_[l]).constr ℂ_[l]
      fun m => MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1))
  have hS1 : ∀ m, S (MvPolynomial.monomial m 1) =
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
    intro m
    have h := (MvPolynomial.basisMonomials _ ℂ_[l]).constr_basis ℂ_[l]
      (fun m => MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1))) m
    simpa [MvPolynomial.coe_basisMonomials] using h
  have hSφ : ∀ Q : MvPolynomial (Lt × ℕ × Fin N0) ℤ,
      S (MvPolynomial.map (Int.castRingHom ℂ_[l]) Q) =
        MvPolynomial.map (Int.castRingHom ℂ_[l]) (T Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on' with
    | monomial m k =>
      have hk : MvPolynomial.monomial m k = k • MvPolynomial.monomial m (1 : ℤ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hk]
      simp only [map_zsmul]
      rw [MvPolynomial.map_monomial, map_one, hS1]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  have hle : Submodule.span ℂ_[l] (Set.range fun J : ColChoice N0 nu =>
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)) ≤ LinearMap.eqLocus S LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨J, rfl⟩
    exact (LinearMap.mem_eqLocus).mpr (by rw [hSφ, hTfix]; rfl)
  have hSP : S P = P := (LinearMap.mem_eqLocus).mp (hle hPmem)
  have hSexp : S P = ∑ m ∈ P.support, AddMonoidAlgebra.coeff P m •
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
    conv_lhs => rw [MvPolynomial.as_sum P]

    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hS1, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  let c : ColChoice N0 nu →₀ ℂ_[l] := ∑ m ∈ P.support,
    AddMonoidAlgebra.coeff P m • Finsupp.mapRange (Int.cast : ℤ → ℂ_[l]) Int.cast_zero (a m)
  have hc : ∀ J, c J = ∑ m ∈ P.support, AddMonoidAlgebra.coeff P m * (a m J : ℂ_[l]) := by
    intro J
    simp [c, Finsupp.finsetSum_apply]
  refine ⟨c, fun J => ?_, ?_⟩
  · rw [hc]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg l) _) fun m _ => ?_
    rw [norm_mul]
    calc ‖AddMonoidAlgebra.coeff P m‖ * ‖(a m J : ℂ_[l])‖ ≤ ‖AddMonoidAlgebra.coeff P m‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one _ _) (norm_nonneg _)
      _ ≤ (l : ℝ) ^ (-B) := by rw [mul_one]; exact hPc m
  · rw [← Finsupp.linearCombination_apply]
    have hΦ : ∀ m, Finsupp.linearCombination ℂ_[l]
        (fun J => MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J))
        (Finsupp.mapRange (Int.cast : ℤ → ℂ_[l]) Int.cast_zero (a m)) =
        MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
      intro m
      rw [← ha, Finsupp.linearCombination_apply, map_finsuppSum]
      rw [Finsupp.sum_mapRange_index (by intro; exact zero_smul _ _)]
      refine Finsupp.sum_congr fun J _ => ?_
      rw [map_zsmul, Int.cast_smul_eq_zsmul]

    simp only [c, map_sum, map_smul, hΦ]
    rw [← hSexp, hSP]

end GenFrameSpan
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW

theorem stepBack : StepBack := by
  intro Lt _ _ l _ N0 N1 nu Th B h I m
  obtain ⟨c, hc, heq⟩ := h I
  rw [heq]
  have hC : (0 : ℝ) ≤ (l : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun J _ => ?_
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, norm_mul]
  have h1 : ‖(Int.castRingHom ℂ_[l]) (AddMonoidAlgebra.coeff (nablaX N0 nu J) m)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_intCast_le_one ℂ_[l] (AddMonoidAlgebra.coeff (nablaX N0 nu J) m)
  calc ‖c J‖ * ‖(Int.castRingHom ℂ_[l]) (AddMonoidAlgebra.coeff (nablaX N0 nu J) m)‖
      ≤ (l : ℝ) ^ (-B) * 1 := mul_le_mul (hc J) h1 (norm_nonneg _) hC
    _ = _ := mul_one _

end GenFrameSpan
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW MvPolynomial

section Span

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]

def atMon (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) :
    MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def Lj (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    MvPolynomial (XZ Lt N0 N1) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  (basisMonomials (XZ Lt N0 N1) ℤ).constr ℤ (atMon Th)

def Sj (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    MvPolynomial (Lt × Fin N0 × Fin N1) ℤ →ₗ[ℤ] ℂ_[l] :=
  (basisMonomials (Lt × Fin N0 × Fin N1) ℤ).constr ℤ fun β =>
    (β.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff β Th

theorem basisMonomials_apply' {σ : Type} (μ : σ →₀ ℕ) :
    basisMonomials σ ℤ μ = monomial μ (1 : ℤ) := by
  simp [coe_basisMonomials]

theorem Lj_monomial (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ)
    (c : ℤ) : Lj Th (monomial μ c) = c • atMon Th μ := by
  have h : (monomial μ c : MvPolynomial (XZ Lt N0 N1) ℤ) = c • basisMonomials (XZ Lt N0 N1) ℤ μ := by
    rw [basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Lj, Module.Basis.constr_basis]

theorem Sj_monomial (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (β : Lt × Fin N0 × Fin N1 →₀ ℕ) (c : ℤ) :
    Sj Th (monomial β c) = c • ((β.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff β Th) := by
  have h : (monomial β c : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) =
      c • basisMonomials (Lt × Fin N0 × Fin N1) ℤ β := by
    rw [basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Sj, Module.Basis.constr_basis]

theorem applyAt0_eq (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : applyAt0 N0 N1 l Th P = Lj Th P := by
  conv_rhs => rw [P.as_sum]

  rw [map_sum]
  unfold applyAt0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Lj_monomial, atMon, smul_monomial, zsmul_eq_mul, mul_assoc]

theorem sfe_inl_inr (α : Lt × ℕ × Fin N0 →₀ ℕ) (β : Lt × Fin N0 × Fin N1 →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp
      (α.mapDomain (Sum.inl : _ → XZ Lt N0 N1) + β.mapDomain Sum.inr) = (α, β) := by
  ext x
  · rw [Finsupp.fst_sumFinsuppEquivProdFinsupp, Finsupp.add_apply,
      Finsupp.mapDomain_apply_of_injective Sum.inl_injective, Finsupp.mapDomain_of_notMem_range] <;> simp
  · rw [Finsupp.snd_sumFinsuppEquivProdFinsupp, Finsupp.add_apply,
      Finsupp.mapDomain_apply_of_injective Sum.inr_injective, Finsupp.mapDomain_of_notMem_range] <;> simp

theorem Lj_inl_inr (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (a : MvPolynomial (Lt × ℕ × Fin N0) ℤ) (q : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) :
    Lj Th (rename (Sum.inl : _ → XZ Lt N0 N1) a * rename (Sum.inr : _ → XZ Lt N0 N1) q) =
      Sj Th q • map (Int.castRingHom ℂ_[l]) a := by
  induction a using MvPolynomial.induction_on' with
  | monomial α r =>
    induction q using MvPolynomial.induction_on' with
    | monomial β t =>
      rw [rename_monomial, rename_monomial, monomial_mul, Lj_monomial, Sj_monomial, map_monomial,
        atMon, sfe_inl_inr]
      simp only [smul_monomial, zsmul_eq_mul, smul_eq_mul, eq_intCast, Int.cast_mul]
      congr 1
      ring
    | add q1 q2 h1 h2 => rw [map_add (f := _), mul_add, map_add (f := _), h1, h2, map_add (f := _), add_smul]
  | add a1 a2 h1 h2 => rw [map_add (f := _), add_mul, map_add (f := _), h1, h2, map_add (f := _), smul_add]

def Xm (s : Lt) (p : ℕ) : Matrix (Fin p) (Fin N0) (MvPolynomial (Lt × ℕ × Fin N0) ℤ) :=
  Matrix.of fun i a => X (s, (i : ℕ), a)

def Dm (s : Lt) (p : ℕ) (f : Fin p → Fin N0) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ((Xm (N0 := N0) s p).submatrix id f).det

def Zm (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) (f : Fin p → Fin N0) :
    MvPolynomial (Lt × Fin N0 × Fin N1) ℤ :=
  ∏ i, X (s, f i, I i)

theorem minorXZ_expand (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    minorXZ N0 N1 s p I = ∑ f : Fin p → Fin N0,
      rename (Sum.inl : _ → XZ Lt N0 N1) (Dm s p f) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (Zm s p I f) := by
  let A : Matrix (Fin p) (Fin N0) (MvPolynomial (XZ Lt N0 N1) ℤ) :=
    Matrix.of fun i a => X (Sum.inl (s, (i : ℕ), a))
  let B : Matrix (Fin N0) (Fin p) (MvPolynomial (XZ Lt N0 N1) ℤ) :=
    Matrix.of fun a k => X (Sum.inr (s, a, I k))
  have hAB : minorXZ N0 N1 s p I = (A * B).det := by
    unfold minorXZ
    congr 1
  rw [hAB, det_mul_rect]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [mul_comm]
  congr 1
  · rw [Dm, AlgHom.map_det]
    congr 1
    ext i k
    simp [A, Xm, AlgHom.mapMatrix_apply, rename_X]
  · simp [Zm, B, map_prod, rename_X]

theorem Gxz_expand (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) :
    Gxz N0 N1 nu I = ∑ F : (∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0),
      rename (Sum.inl : _ → XZ Lt N0 N1) (∏ s, ∏ c, Dm s _ (F s c)) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (∏ s, ∏ c, Zm s _ (I s c) (F s c)) := by
  unfold Gxz
  simp_rw [minorXZ_expand, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  simp only [map_prod, Finset.prod_mul_distrib]

theorem nablaX_eq (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    nablaX N0 nu J = ∏ s, ∏ c, Dm s _ (J s c) := by
  unfold nablaX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  unfold Dm Xm
  rfl

theorem prodD_mem (nu : Lt → YoungDiagram)
    (F : ∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0) :
    map (Int.castRingHom ℂ_[l]) (∏ s, ∏ c, Dm s _ (F s c)) ∈ nablaSpanC Lt l N0 nu := by
  by_cases h : ∀ s (c : Fin ((nu s).rowLen 0)), ∃ (J : Fin ((nu s).colLen c) ↪o Fin N0) (e : ℤ),
      Dm s _ (F s c) = (e : MvPolynomial (Lt × ℕ × Fin N0) ℤ) * Dm s _ J
  · choose Jf ef hJ using h
    have hp : ∏ s, ∏ c, Dm s _ (F s c) =
        ((∏ s, ∏ c, ef s c : ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℤ) *
          nablaX N0 nu (Jf : ColChoice N0 nu) := by
      have hn : nablaX N0 nu Jf = ∏ s, ∏ c, Dm s _ (Jf s c) := nablaX_eq nu Jf
      rw [hn]
      simp_rw [hJ, Finset.prod_mul_distrib]
      push_cast
      rfl
    rw [hp, map_mul, map_intCast, ← zsmul_eq_mul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun J : ColChoice N0 nu =>
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)) Jf)) _
  · push Not at h
    obtain ⟨s, c, hsc⟩ := h
    have h0 : Dm s _ (F s c) = 0 := by
      rcases det_submatrix_fun (Xm (N0 := N0) s _) (F s c) with h0 | ⟨J, e, he⟩
      · exact h0
      · exact absurd he (hsc J e)
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero (Finset.mem_univ c) h0),
      map_zero]
    exact Submodule.zero_mem _

end Span

theorem stepSpan : StepSpan := by
  intro Lt _ _ l _ N0 N1 nu Th I

  rw [applyAt0_eq, Gxz_expand, map_sum]
  refine Submodule.sum_mem _ fun F _ => ?_
  rw [Lj_inl_inr]
  exact Submodule.smul_mem _ _ (prodD_mem nu F)

end GenFrameSpan
end
end
