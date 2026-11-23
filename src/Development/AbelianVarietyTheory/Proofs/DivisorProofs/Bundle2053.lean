module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle322
public import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

noncomputable section

namespace GlobalTheory.SizesArch

open Formalism.BasicNotions NumberField

theorem log_gamma_nat_le (n : ℕ) (hn : 1 ≤ n) : Real.log (Real.Gamma n) ≤ n * Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hg : Real.Gamma ((m + 1 : ℕ) : ℝ) = (m.factorial : ℝ) := by
    rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]
  have hf : (m.factorial : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by
    have h1 : m.factorial ≤ (m + 1) ^ (m + 1) :=
      (Nat.factorial_le_pow m).trans ((Nat.pow_le_pow_left (Nat.le_succ m) m).trans
        (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.le_succ m)))
    exact_mod_cast h1
  rw [hg, ← Real.log_pow]
  exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos m) hf

theorem log_cmConst_le {Φ : Type} [Fintype Φ] (dF d : ℝ) (k : ℕ) (κ : Φ → ℕ) (hdF : 0 < dF) (hd : 1 ≤ d)
    (hk : 1 ≤ k) :
    Real.log (Formalism.PairingDivisionLocalBalance.cmConst dF d k κ) ≤ (((k : ℝ) - 1) / 2) * Real.log dF +
      ∑ τ, Real.log (Real.Gamma ((k : ℝ) + κ τ)) + (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) * 8 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hG : ∀ τ, 0 < Real.Gamma ((k : ℝ) + κ τ) := fun τ =>
    Real.Gamma_pos_of_pos (by have : (0 : ℝ) ≤ κ τ := Nat.cast_nonneg _; linarith)
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hq : 0 < 2 * Real.pi / Real.sqrt d := div_pos (by positivity) (by linarith)
  unfold Formalism.PairingDivisionLocalBalance.cmConst
  rw [Real.log_mul (mul_ne_zero (Real.rpow_pos_of_pos hdF _).ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (hG τ).ne'))
      (pow_ne_zero _ hq.ne'),
    Real.log_mul (Real.rpow_pos_of_pos hdF _).ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (hG τ).ne'),
    Real.log_rpow hdF, Real.log_prod (fun τ _ => (hG τ).ne'), Real.log_pow]
  have h1 : Real.log (2 * Real.pi / Real.sqrt d) ≤ 8 := by
    have h3 := Real.log_le_sub_one_of_pos hq
    have h2 : 2 * Real.pi / Real.sqrt d ≤ 2 * Real.pi := div_le_self (by positivity) hsd
    linarith [Real.pi_le_four]
  have h0 : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.absK κ := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h1 h0
  linarith

end GlobalTheory.SizesArch

namespace GlobalTheory.SizesArch

open Formalism.BasicNotions NumberField GlobalTheory.ChiGrid

theorem sizes : ∀ ε : ℝ, ∃ Cx x₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (large₂ : Formalism.BasicNotions.SizeData₂ D), large₂.sc.eps = ε → x₁ ≤ large₂.sc.x →
    Rec large₂ → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
      Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) +
        (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤
        bTH D Cx large₂.sc.x large₂.sc.b := by
  intro ε
  refine ⟨200, 0, fun D large₂ _ _ hR i j s hs1 hs2 => ?_⟩
  obtain ⟨-, -, hm4, hm, -, hmfNd, -, -, -, hrd1, hrd2, -, -, -⟩ := hR.size
  obtain ⟨hgb, hb675⟩ := GlobalTheory.BigTop.Fun.gap_le_b hR.size
  have hbL : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hL1 : 1 ≤ large₂.sc.L := by
    rw [← hbL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hx1 : 1 < large₂.sc.x := large₂.sc.one_lt_alt
  have hlogx : 0 ≤ Real.log large₂.sc.x := Real.log_nonneg hx1.le
  have hcard : Fintype.card D.what₂.Tau = D.R.f := Formalism.MainNotions.Lnk.card_Tau D
  have hf1n : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1n

  have hsb : (s : ℝ) ≤ large₂.sc.b := by
    have h1 := GlobalTheory.BigTop.Fun.rankV_lt_gap (D := D) i.2 j.2
    have e := (ranks_exact D i j).2.2
    have h3 : rankV D i j ≤ rankV D (i + 1) (j + 1) := by unfold rankV; gcongr <;> omega
    have : s ≤ gap D 1 := by omega
    exact (by exact_mod_cast this : (s : ℝ) ≤ gap D 1).trans hgb

  have hκ : ∀ τ, (kap D 1 i j s τ : ℝ) ≤ 5 * large₂.sc.b := by
    intro τ
    obtain ⟨e0, e1⟩ := GlobalTheory.BigTop.Fun.numE_bounds hR.size τ j.2
    obtain ⟨c0, c1⟩ := GlobalTheory.BigTop.Fun.cen_bounds hR.size τ (i := D.R.m - i) (by omega) (by omega)
    have h : (kap D 1 i j s τ : ℤ) ≤ (num D 1 τ).e (j + 1) + cen D 1 τ (D.R.m - i) := by
      unfold kap; omega
    have h' : ((kap D 1 i j s τ : ℤ) : ℝ) ≤ ((num D 1 τ).e (j + 1) : ℝ) + (cen D 1 τ (D.R.m - i) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith

  have hN1 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
  have hd1 : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hdb : (D.host.d : ℝ) ≤ large₂.sc.b := by
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by omega)
    have hN : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
    have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm1 hf1) (one_le_pow₀ hN)
    exact (le_mul_of_one_le_left (by linarith) h1).trans hmfNd
  have hlogd : Real.log D.host.d ≤ large₂.sc.L := hbL ▸ Real.log_le_log (by linarith) hdb
  have hlogd0 : 0 ≤ Real.log D.host.d := Real.log_nonneg hd1
  have hdl : |large₂.logDerivativeAtOne| ≤ large₂.sc.L := hR.dlog

  have hdF : |(discr (maximalRealSubfield D.host.E) : ℝ)| = (2 * D.host.v) ^ D.R.f := by
    rw [← hR.hF]; exact GlobalTheory.CovDom.NormConst.abs_discr_F D
  have h2v : 2 * D.host.v = D.host.rdE := by show 2 * (D.host.rdE / 2) = D.host.rdE; ring
  have hdF0 : 0 < |(discr (maximalRealSubfield D.host.E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
  have hlogdF : Real.log |(discr (maximalRealSubfield D.host.E) : ℝ)| ≤ (D.R.f : ℝ) * large₂.sc.L := by
    rw [hdF, Real.log_pow, h2v]
    have : Real.log D.host.rdE ≤ large₂.sc.L := by linarith
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

  have hC := log_cmConst_le |(discr (maximalRealSubfield D.host.E) : ℝ)| (D.host.d : ℝ) (2 * s) (kap D 1 i j s) hdF0 hd1
    (by omega)
  have hC0 : C0 D.host.E D.host.d (2 * s) (kap D 1 i j s) =
      Formalism.PairingDivisionLocalBalance.cmConst |(discr (maximalRealSubfield D.host.E) : ℝ)| (D.host.d : ℝ) (2 * s) (kap D 1 i j s) := rfl
  rw [hC0]
  set b := large₂.sc.b
  set L := large₂.sc.L
  set F : ℝ := (D.R.f : ℝ) with hF
  have hb0 : 0 ≤ b := by linarith
  have hk : ((2 * s : ℕ) : ℝ) ≤ 2 * b := by push_cast; linarith
  have hk1 : (1 : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * s by omega)

  have T1 : (((2 * s : ℕ) : ℝ) - 1) / 2 * Real.log |(discr (maximalRealSubfield D.host.E) : ℝ)| ≤ 2 * (F * b * L) := by
    have a1 : 0 ≤ (((2 * s : ℕ) : ℝ) - 1) / 2 := by linarith
    have a2 := mul_le_mul_of_nonneg_left hlogdF a1
    have a3 : (((2 * s : ℕ) : ℝ) - 1) / 2 ≤ b := by linarith
    have a4 : 0 ≤ F * L := by positivity
    have a5 := mul_le_mul_of_nonneg_right a3 a4
    nlinarith

  have T2 : ∑ τ, Real.log (Real.Gamma (((2 * s : ℕ) : ℝ) + kap D 1 i j s τ)) ≤ 49 * (F * b * L) := by
    have each : ∀ τ, Real.log (Real.Gamma (((2 * s : ℕ) : ℝ) + kap D 1 i j s τ)) ≤ 49 * (b * L) := by
      intro τ
      have e : ((2 * s : ℕ) : ℝ) + kap D 1 i j s τ = ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      have hn1 : 1 ≤ 2 * s + kap D 1 i j s τ := by omega
      refine (log_gamma_nat_le _ hn1).trans ?_
      have hn : ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) ≤ 7 * b := by push_cast; linarith [hκ τ]
      have hn0 : (1 : ℝ) ≤ ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := by exact_mod_cast hn1
      have hl0 : 0 ≤ Real.log ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := Real.log_nonneg hn0
      have hl : Real.log ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) ≤ 7 * L := by
        have l1 := Real.log_le_log (by linarith) hn
        rw [Real.log_mul (by norm_num) (by linarith), hbL] at l1
        have l2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 by norm_num)
        linarith
      have := mul_le_mul hn hl hl0 (by linarith)
      linarith
    refine (Finset.sum_le_sum fun τ _ => each τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    linarith

  have hsumκ : (Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) : ℝ) ≤ 5 * (F * b) := by
    unfold Formalism.PairingDivisionLocalBalance.absK
    push_cast
    refine (Finset.sum_le_sum fun τ _ => hκ τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    linarith
  have hsumκ0 : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) := Nat.cast_nonneg _
  have T3 : (Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) : ℝ) * 8 ≤ 40 * (F * b * L) := by
    have : F * b ≤ F * b * L := le_mul_of_one_le_right (by positivity) hL1
    linarith

  have hM : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) ≤ 12 * (F * b) := by
    unfold Formalism.PairingDivisionLocalBalance.wtM
    push_cast
    rw [hcard]
    have : (2 * (s : ℝ)) * F ≤ 2 * b * F := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    push_cast at hsumκ
    linarith
  have T4 : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤ 12 * (F * b * L) := by
    have a1 : (Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2 ≤ L := by linarith
    have a2 : 0 ≤ (Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2 := by positivity
    have := mul_le_mul hM a1 a2 (by positivity)
    linarith
  have hfin : 0 ≤ F * b * Real.log large₂.sc.x := by positivity
  unfold bTH
  rw [hbL]
  have e : 200 * (D.R.f : ℝ) * b * (L + Real.log large₂.sc.x) = 200 * (F * b * L) + 200 * (F * b * Real.log large₂.sc.x) := by
    rw [hF]; ring
  rw [e]
  have hP : 0 ≤ F * b * L := by positivity
  linarith

end GlobalTheory.SizesArch
end
end

section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

theorem _root_.GlobalTheory.T.dualWeylModule_le_span_extremalTranslates : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight n), nablaSq K n lam ≤ Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) := by
  first | exact @GlobalTheory.nablaSq_le_span_extremal | exact GlobalTheory.nablaSq_le_span_extremal | (intros; apply GlobalTheory.nablaSq_le_span_extremal <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.isCompact_finiteAdeleAnnihilator_stdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F | ∀ y ∈ L, ψ (pairA D.host.F 0 (x ⬝ᵥ y)) = 1} := by
  first | exact @GlobalTheory.AnnCompactStdChar.isCompact_annihilator_of_isStdChar | exact GlobalTheory.AnnCompactStdChar.isCompact_annihilator_of_isStdChar | (intros; apply GlobalTheory.AnnCompactStdChar.isCompact_annihilator_of_isStdChar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open _root_.Formalism.L2.Col

theorem mem_dualFr_span_iff_dualsum {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Set (Fin n → K))
    (φ : Fin n → K) :
    φ ∈ dualFr (Submodule.span (𝓞 K) S) ↔ ∀ x ∈ S, φ ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro h x hx
    exact h x (Submodule.subset_span hx)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => rw [dotProduct_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
    | smul a x _ hx => rw [dotProduct_smul]; exact Submodule.smul_mem _ a hx

theorem dualFr_tauLat_sumLat : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n N : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 E) (Fin n → E))
    (L : Submodule (𝓞 E) (Fin N → E)),
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ τ : ι, dualFr (tauLat emb τ L) = Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) 1 := by
  intro E K ι _ _ _ _ _ emb n N hN M L hL τ
  subst hN
  have hC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => rfl
  have hLst : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  have split : ∀ φ x : Fin (n + 1) → K, φ ⬝ᵥ x = (fun k => φ (Fin.castSucc k)) ⬝ᵥ (fun k => x (Fin.castSucc k))
      + φ (Fin.last n) * x (Fin.last n) := by
    intro φ x
    simp only [dotProduct, Fin.sum_univ_castSucc]
  ext φ
  rw [tauLat, mem_dualFr_span_iff_dualsum]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [tauLat, mem_dualFr_span_iff_dualsum]
      rintro _ ⟨m, hm, rfl⟩
      let v : Fin (n + 1) → E := Fin.lastCases 0 m
      have hv : v ∈ L := by
        rw [hL]
        refine ⟨?_, 0, ?_⟩
        · simpa [hC, v] using hm
        · simp [hLst, v]
      have := h _ ⟨v, hv, rfl⟩
      rw [split] at this
      simpa [hC, v] using this
    · let v : Fin (n + 1) → E := Pi.single (Fin.last n) 1
      have hv : v ∈ L := by
        rw [hL]
        refine ⟨?_, 1, ?_⟩
        · have : (fun k : Fin n => v (Formalism.L2.Col.Br.iC rfl k)) = 0 := by
            funext k; simp [hC, v, Fin.castSucc_ne_last]
          rw [this]; exact M.zero_mem
        · simp [hLst, v]
      have := h _ ⟨v, hv, rfl⟩
      rw [split] at this
      have h0 : (fun k : Fin n => (fun a => emb τ (v a)) (Fin.castSucc k)) = 0 := by
        funext k; simp [v, Fin.castSucc_ne_last]
      rw [h0, dotProduct_zero, zero_add] at this
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
      refine ⟨c, ?_⟩
      rw [hLst, mul_one]
      have hv1 : (fun (x : Fin (n + 1) → E) a => emb τ (x a)) v (Fin.last n) = 1 := by simp [v]
      rw [hv1, mul_one] at hc
      rw [← hc]
  · rintro ⟨h1, c, hc⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, hL] at hv
    obtain ⟨hvM, d, hd⟩ := hv
    rw [split]
    refine add_mem ?_ ?_
    · rw [tauLat, mem_dualFr_span_iff_dualsum] at h1
      have := h1 _ ⟨_, hvM, rfl⟩
      simpa [hC] using this
    · rw [hLst] at hc hd
      refine Submodule.mem_one.2 ⟨c * RingOfIntegers.mapRingHom (emb τ) d, ?_⟩
      rw [map_mul, hc, mul_one]
      show _ = _ * emb τ (v (Fin.last n))
      rw [← hd]
      rfl

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem latLast_isLattice : ∀ {E : Type} [Field E] [NumberField E] {n N : ℕ} (hN : N = n + 1)
    (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    Submodule.IsLattice E L := by
  intro E _ _ n N hN M L hM hL
  subst hN
  have hiC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => Fin.ext rfl
  have hiL : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := Fin.ext rfl
  simp only [hiC, hiL] at hL
  let g : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
    { toFun := fun x => Fin.snoc (α := fun _ => E) x 0
      map_add' := by
        intro x y; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      map_smul' := by
        intro a x; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }
  have gC : ∀ x k, g x (Fin.castSucc k) = x k := fun x k => by simp [g]
  have gL : ∀ x, g x (Fin.last n) = 0 := fun x => by simp [g]
  let e : Fin (n + 1) → E := Pi.single (Fin.last n) 1
  have gm : ∀ m ∈ M, g m ∈ L := fun m hm => (hL _).2 ⟨by simpa [gC] using hm, 0, by simp [gL]⟩
  have he : e ∈ L := (hL _).2 ⟨by
      have : (fun k : Fin n => e (Fin.castSucc k)) = 0 := by
        funext k; simp [e, Pi.single_apply, Fin.castSucc_ne_last]
      rw [this]; exact M.zero_mem, 1, by simp [e]⟩
  have dec : ∀ x : Fin (n + 1) → E, x = g (fun k => x (Fin.castSucc k)) + x (Fin.last n) • e := by
    intro x; ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [gL, e]
    · simp [gC, e, Pi.single_apply, Fin.castSucc_ne_last]
  have hLeq : L = M.map (g.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {e} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hvM, c, hc⟩ := (hL v).1 hv
      rw [dec v]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_map_of_mem hvM))
        (Submodule.mem_sup_right ?_)
      have hs : (c : E) • e = c • e := algebraMap_smul E c e
      rw [← hc, hs]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)
    · exact sup_le (Submodule.map_le_iff_le_comap.2 fun m hm => gm m hm)
        (Submodule.span_le.2 (by simpa using he))
  refine ⟨?_, ?_⟩
  · rw [hLeq]
    exact Submodule.FG.sup (hM.fg.map _) (Submodule.fg_span_singleton e)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory
end

section

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapBase

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Scale

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

end Scale

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m)

theorem oneMapRow0_of_rows (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ)
    (hpins : OMPins T R κ v₀ O i)
    (hequiv : (O i).EquivAt (κ i) cc)
    (hid : OneMapRow (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (Wc D i)
      (unfBC (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c')) (O i).dict (O i).mu (xiR D) (wtA (κ i))
      (actLev (O i).c' (O i).lev2) (O i).dδ (O i).Cl' (O i).w (O i).La (O i).Nc (O i).gam (O i).vol (O i).ep (O i).io
      (O i).thAd (O i).Plc D.what₂.embLL.toRatAlgHom.fieldRange
      (cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc ph)
    (hrat : (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc ph) :
    OneMapRow0 T R κ v₀ O i :=
  ⟨cc, ph, hequiv, ⟨hpins.1.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ (O i).hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O i).hle _ _ hpins.2.act.1).2, hid⟩, hrat⟩

end GlobalTheory.OneMapBase
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspFormAdelicFunctions_independent_goodEmbedding : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.PhiIndep.phiC_indep | exact GlobalTheory.PhiIndep.phiC_indep | (intros; apply GlobalTheory.PhiIndep.phiC_indep <;> assumption)
end
