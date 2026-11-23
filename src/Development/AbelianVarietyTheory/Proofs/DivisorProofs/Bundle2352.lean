module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle089
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle046
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle085
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle083
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle087
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLif
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle013
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefArith

theorem sum_laOf_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hq : Dw.q = 0) (hn : Even n) (τ : Psi H) :
    (∑ k, (laOf Dw a n τ k : ℝ)) = (GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ) + (Dw.p : ℝ) * n / 2 := by
  have hm : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hk : ∀ k : Fin (Dw.p + Dw.q), (laOf Dw a n τ k : ℝ) = (a (τ.1, k) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro k
    have h := k.2
    have hlt : (k : ℕ) < Dw.p := by omega
    simp [laOf, weightOf, hlt]
    norm_cast
  simp_rw [hk]
  rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)) (Dw.p + Dw.q)]
  have hs : (GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ) = ∑ i ∈ Finset.range Dw.p, (a (τ.1, i) : ℝ) := by
    unfold GlobalTheory.DualWeyl.size part
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)) (Dw.mult τ.1), hm]
  rw [hs, hq, add_zero]
  obtain ⟨r, rfl⟩ := hn
  have : (r + r) / 2 = r := by omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, this, hq, add_zero]
  push_cast
  ring

end GlobalTheory.DefArith

namespace GlobalTheory.DefArith

theorem two_defBound_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (lo : ℝ), Dw.q = 0 → 1 ≤ Dw.p → Even n → -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) - |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) - (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) - (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ 2 * defBound Dw a n (-flatDegVal Dw lo) := by
  intro E _ _ _ H Dw a n kc lo hq hp hn
  have hp0 : (Dw.p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Dw.p := by exact_mod_cast hp
    exact this.ne'

  have hτ : ∀ τ : Psi H, -((Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
      |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) ≤
      2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) := by
    intro τ
    have hS := sum_laOf_eq Dw a n hq hn τ
    have hsplit : (∑ k, (laOf Dw a n τ k : ℝ)) =
        (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) + ∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hq, add_zero]
      ring
    have hb : -(|lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) ≤
        -((∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo) := by
      rw [neg_le_neg_iff]
      calc (∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo
          ≤ |(∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo| := le_abs_self _
        _ = |∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))| * |lo| := abs_mul _ _
        _ ≤ (∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) * |lo| :=
            mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
        _ = |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| := mul_comm _ _
    have he : 2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) =
        -((∑ k, (laOf Dw a n τ k : ℝ)) * lo) - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) := by
      rw [hS]
      unfold flatDegVal
      rw [hq]
      field_simp
      ring
    rw [he, hsplit]
    linarith
  have hlog : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hN : 0 ≤ (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) := by positivity
  have hl : -((n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E|) ≤
      2 * ((n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)) := by
    have h1 := le_abs_self (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E)
    have h2 : -|GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ Real.log (2 * Real.pi) / 2 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hN
    nlinarith
  have hsum := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => hτ τ
  have eL : -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
      |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) -
      (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) =
      ∑ τ : Psi H, (-((Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
        |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  have eR : 2 * defBound Dw a n (-flatDegVal Dw lo) =
      ∑ τ : Psi H, 2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) +
      2 * ((n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)) := by
    unfold defBound
    rw [mul_add, Finset.mul_sum]
  rw [eL, eR]
  linarith

end GlobalTheory.DefArith
end

section

open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.DefPt.ArchVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exists_homN_eq {σ : c.F →+* ℂ} (U : Unf Xo c σ r) {ξ : ℝ} (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hξ : ∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {G : WTZ E} (hG : G.2 = 0) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c (exZ Dw G)) {Z : Comp Xo c} {y : FrPt Xo c (CAt σ)} (hy : LiesOn Z y) {N : ℝ}
    (hN : GlobalTheory.LamT.IsMetric y N fun _ => 1) :
    ∃ z ∈ framesOn U Z, homN U ξ G f z = ‖toC (evR Xo c f y)‖ := by
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ r U hU y
  refine ⟨⟨k, x.1⟩, ⟨x.2, liesOn_frBor ht hy⟩, ?_⟩
  obtain ⟨g, hg0, hgd, hchg⟩ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hξ0 : 0 < ξ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hξ k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 (U.X k).ξ0_ne)
  have hκ : 0 < 2 * Real.pi * ξ := by positivity
  have hm0 := GlobalTheory.OrthoMetric.isMetric_of_isOrtho E H Dw l Xo c σ r U ξ hσ hU hpq k x (hξ k) hx
  have hm1 := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨-, hGr⟩ := GlobalTheory.LamT.MetUniq.isMetric_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ),
      ‖toC (t (some p) : CAt σ)‖ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
    rintro ⟨τ, i⟩
    have hs : (Real.sqrt (2 * Real.pi * ξ))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hκ, ← Real.exp_neg]
      congr 1; ring
    rw [← hgd τ i, ← hs]
    exact GlobalTheory.LamT.OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _ hκ
      (fun i j hij => hg0 τ j i hij) (congrFun hGr τ).symm i
  haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have hev := GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.lawsFieldsSeparately.2.1 Xo c _ hf (CAt σ) t _ _ ht
  have hw : ‖toC ((∏ i, t i ^ exZ Dw G i : (CAt σ)ˣ) : CAt σ)‖ = lieFacZ Dw ξ G := by
    have e : ‖toC ((∏ i, t i ^ exZ Dw G i : (CAt σ)ˣ) : CAt σ)‖ = ∏ i, ‖toC (t i : CAt σ)‖ ^ exZ Dw G i := by
      show ‖((∏ i, (show Ix Dw → ℂˣ from t) i ^ exZ Dw G i : ℂˣ) : ℂ)‖ = _
      rw [Units.coe_prod, norm_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [Units.val_zpow_eq_zpow_val, norm_zpow]; rfl
    rw [e, Fintype.prod_option]
    simp only [hsome, exZ, hG, zpow_zero, one_mul, ← Real.rpow_intCast, ← Real.exp_mul]
    rw [← Real.exp_sum, lieFacZ, ← Finset.mul_sum, Fintype.sum_sigma]
    congr 1; ring
  have hrd : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
  rw [homN, ptN, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ hx),
    hev, ← hw]
  show _ * ‖rdU U f k x.1‖ = _
  rw [hrd]
  exact (norm_mul (toC _) (toC _)).symm

theorem cInf_eq {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {ξ : ℝ} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hξ : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c}
    {la : GlobalTheory.AllWt.Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s : ConstSec U ξ Z la δ) {σ : c.F →+* ℂ}
    {y : FrPt Xo c (CAt σ)} (hy : LiesOn Z y) {N : ℝ} (hN : GlobalTheory.LamT.IsMetric y N fun _ => 1) :
    s.cInf σ = ‖toC (evR Xo c s.sig y)‖ := by
  have key : ∀ σ' : c.F →+* ℂ, goodOf c σ = σ' → ∀ y' : FrPt Xo c (CAt σ'), LiesOn Z y' →
      (GlobalTheory.LamT.IsMetric y' N fun _ => 1) → s.cInf σ = ‖toC (evR Xo c s.sig y')‖ := by
    rintro _ rfl y' hy' hN'
    have hg := goodEmb_goodOf c σ
    obtain ⟨z, hz, e⟩ := exists_homN_eq (U _) hg (hU _ hg) (hξ _ hg) hpq (G := wtOf Dw la 0) rfl s.sig_mem hy' hN'
    rw [← e, s.homN_eq hz]
  by_cases hσ : GoodEmb c σ
  · exact key σ (if_pos hσ) y hy hN
  · have hB := GlobalTheory.lawsFieldsSeparately.2.1
    obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (FrameNorm.conjAlg σ) y
    have hm' := GlobalTheory.LamT.isMetric_conj E H Dw l Xo c σ y y' N (fun _ => 1) hpq hy' hN
    have h1 : (fun b : E →+* ℂ => ((1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)).map (starRingEnd ℂ)) =
        fun _ => 1 := funext fun b => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1] at hm'
    haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
    have hev := evR_frMap (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 s.sig s.sig_mem.1
      (FrameNorm.conjAlg σ) y (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) y) y' hy'
    rw [key _ (if_neg hσ) y' (liesOn_frMap hy' hy) hm', hev]
    exact Complex.norm_conj _

theorem cInf_eq_norm_div_norm_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ σ, s.cInf σ = ‖σ b‖ / ‖(P.X σ τ.1).det‖ := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s b _ hb σ
  obtain ⟨-, hX, hA⟩ := P.arch σ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F (CAt σ)
    (Algebra.ofId c.F (CAt σ)) P.y₀
  have hu : ∀ τ', IsUnit (M := ℂ) (P.X σ τ').det := fun τ' => (hX τ').isUnit
  obtain ⟨y, hy⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c (CAt σ) (fun τ' => (P.X σ τ')ᵀ) 1 z).1
    (fun τ' => show IsUnit (M := ℂ) ((P.X σ τ')ᵀ).det from (Matrix.det_transpose (P.X σ τ')).symm ▸ hu τ') isUnit_one
  have hon : LiesOn Z y := fun q => by
    have e : ptF y = ptF z := by
      apply Limits.pullback.hom_ext
      · rw [ptF, Limits.pullback.lift_fst, ptF, Limits.pullback.lift_fst, hy.1]
      · rw [ptF, Limits.pullback.lift_snd, ptF, Limits.pullback.lift_snd]
    rw [e]
    exact liesOn_frMap hz P.on q
  have h : toC (evR Xo c s.sig y) * (P.X σ τ.1).det = σ b := hb (CAt σ) z y (P.X σ) 1 hu isUnit_one hz hy
  rw [cInf_eq hD.unf hD.xi (hD.p.trans (Nat.le_add_right _ _)) s hon (hA z y hz hy), ← h, norm_mul,
    mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 (hX τ.1))]

end GlobalTheory.DefPt.ArchVal

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

namespace GlobalTheory.ModelChg

theorem det_ne_zero_of_hasSig {n r s : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : HasSig A r s) : A.det ≠ 0 := by
  obtain ⟨hrs, P, hP⟩ := h
  have hu : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) (0 : Matrix (Fin r) (Fin s) ℂ)
      (0 : Matrix (Fin s) (Fin r) ℂ) (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (Pᵀ * A * P.map star).rank ≤ A.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hP, h1] at h2
  simp at h2
  have h3 : A.rank = n := le_antisymm (by simpa using A.rank_le_card_width) (by omega)
  have h4 : LinearMap.range A.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact (Matrix.finrank_range_mulVecLin A).trans h3)
  have h5 : Function.Surjective A.mulVec := LinearMap.range_eq_top.mp h4
  exact (Matrix.isUnit_iff_isUnit_det A |>.mp (Matrix.mulVec_surjective_iff_isUnit.mp h5)).ne_zero

theorem det_ne_zero_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (B : Base F E) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ w, HasSig (c • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h1 := det_ne_zero_of_hasSig (h w)
  rw [Matrix.det_smul] at h1
  intro h0
  apply h1
  rw [show (J.map (B.emb w).1).det = (B.emb w).1 J.det from ((B.emb w).1.map_det J).symm, h0, map_zero, mul_zero]

theorem modelChange (hK : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.ModelChange := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ om₁ hP₁
  obtain ⟨a, ha, hco⟩ := GlobalTheory.T.good_models_differ_by_symplectic_matrix F E σ B.ψ n d X W M M₁ hP.good hP₁.good
  obtain ⟨e, c, hc, hev, hbij, hθ⟩ :=
    GlobalTheory.T.symplectic_change_of_good_models_intertwines hK F E σ B n d X W M M₁ r s r' s' hP.base hP.herm hP.skew hP.good hP₁.good a ha hco
  obtain ⟨om₂, hW₂, hint⟩ := GlobalTheory.T.eigen_intertwiner_preserves_schwartz_space hK F E σ B n d X W M χX χW om r s r' s' hP M₁ hP₁.good e hev hbij
  have hX : X.J.det ≠ 0 :=
    det_ne_zero_of_sig B X.J 1 one_ne_zero (fun w => by simpa using hP.herm.sig w)
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_sig B W.J Complex.I Complex.I_ne_zero hP.skew.sig
  have huniq := GlobalTheory.T.adelicWeilRep_schrodingerModel_unique F E σ hP.base.cm n d X W M₁ B.ψ χX χW hP.base.std hP.herm.herm hX
    hP.skew.skew hWd om₂ om₁ hW₂ hP₁.weil
  refine ⟨e, c, hc, hev, hbij, fun Φ hΦ => ⟨hθ Φ hΦ, fun x => ?_⟩⟩
  rw [hint x Φ hΦ, huniq x (e Φ) (hbij.mapsTo hΦ)]

end GlobalTheory.ModelChg
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem _root_.GlobalTheory.T.polynomial_datum_action_of_pair : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  first | exact @GlobalTheory.PolActsPf.polActs_of_isPair | exact GlobalTheory.PolActsPf.polActs_of_isPair | (intros; apply GlobalTheory.PolActsPf.polActs_of_isPair <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.weil_eigen_bijective_schwartz : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ om₁ : Rep σ X W, M₁.IsWeil B.ψ χX χW om₁ ∧ ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  first | exact @GlobalTheory.ModelTr.exists_isWeil_trans_of_bijOn | exact GlobalTheory.ModelTr.exists_isWeil_trans_of_bijOn | (intros; apply GlobalTheory.ModelTr.exists_isWeil_trans_of_bijOn <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.petersson_norm_mul_le_sqrt_bergman_mul_component : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b) (β : ℝ), 0 ≤ β → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict a β → ∀ σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (a + b) 0) σ (w.1 * f.1) ≤ Real.sqrt β * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ w.1 * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ f.1 := by
  first | exact @GlobalTheory.HSApp.petOn_mul_le | exact GlobalTheory.HSApp.petOn_mul_le | (intros; apply GlobalTheory.HSApp.petOn_mul_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.derivationHomotopyOperator_filtration_properties : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B) (e : ℕ → B) (N : ℕ), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → (∀ k, e k ∈ fil δ k) → (∀ x y, hot v e N (x + y) = hot v e N x + hot v e N y) ∧ (∀ b, hot v e N (algebraMap B (DR R B) b) = 0) ∧ (∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], hot v e N x ∈ ⋀[B]^j Ω[B⁄R]) ∧ (∀ x ∈ rel R δ, hot v e N x ∈ rel R δ) ∧ ∀ n, ∀ x ∈ filDR R δ n, hot v e N x ∈ filDR R δ (n + 1) := by
  first | exact @GlobalTheory.PDForm.HotFil.hot_fil | exact GlobalTheory.PDForm.HotFil.hot_fil | (intros; apply GlobalTheory.PDForm.HotFil.hot_fil <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_lift_pair_hom (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (hi : φ₀ ≫ D.i = D'.i ≫ φ) (p : Pair φ) :
    ∃ θ : Λ.L.obj (Opposite.op p.1.2) ⟶ m.obj (Λ'.L.obj (Opposite.op p.1.1)),
      ∀ a, θ.φ (Λ.e (Opposite.op p.1.2) a) = Λ'.e (Opposite.op p.1.1) (CechDR.secPull D.s D'.s p a) := by
  let T' := Λ'.L.obj (Opposite.op p.1.1)
  let e' : Sec D'.s p.1.1.1 →+* T'.B := Λ'.e (Opposite.op p.1.1)
  let y₀ : Sec D.s p.1.2.1 →+* (m.obj T').B := e'.comp (CechDR.secPull D.s D'.s p)
  have hy : ∀ r : D.R, y₀ (algebraMap D.R _ r) = algebraMap D.R (m.obj T').B r := by
    intro r
    have h1 := semiHom_secPull hφ p r 1
    rw [map_one, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at h1
    change e' (CechDR.secPull D.s D'.s p (algebraMap D.R _ r)) = algebraMap D'.R T'.B (σ r)
    rw [h1]
    exact (Λ'.e (Opposite.op p.1.1)).commutes _
  let y : Sec D.s p.1.2.1 →ₐ[D.R] (m.obj T').B := { y₀ with commutes' := hy }
  refine ((GlobalTheory.T.hom_spec_points_levels D Λ).1 (Opposite.op p.1.2) (m.obj T') y).1 ?_
  change spMap ((T'.π.comp e').comp (CechDR.secPull D.s D'.s p)) ≫ affPt D.s p.1.2 = (T'.x ≫ φ₀) ≫ D.i
  rw [Cris.spMap_comp, Category.assoc, secPull_affPt, ← Category.assoc, Category.assoc T'.x, hi, ← Category.assoc]
  exact congrArg (· ≫ φ) (Λ'.pt (Opposite.op p.1.1))

end GlobalTheory.PDForm
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.pullbackBijective12_resMap_of_affine_inter : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) → ((Cx.single (Coef.ofAlg (O κ t))).resMap (pE κ t i)).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs | exact GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs | (intros; apply GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C] [Algebra R C] (JC : Ideal C) (δC : DividedPowers JC) (π : C →ₐ[R] B) (w : C →+ K1 R δ), (∀ x y, w (x * y) = π x • w y + π y • w x) → (∀ r, w (algebraMap R C r) = 0) → (∀ n, ∀ a ∈ JC, w (δC.dpow (n + 1) a) = π (δC.dpow n a) • w a) → ∃ ρ : DR R C → DR R B, (∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) ∧ (∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R δ) ∧ (∀ c, ρ (algebraMap C (DR R C) c) - algebraMap B (DR R B) (π c) ∈ rel R δ) ∧ (∀ c ω, Submodule.Quotient.mk ω = w c → ρ (ι1 (D R C c)) - ι1 ω ∈ rel R δ) ∧ (∀ x ∈ rel R δC, ρ x ∈ rel R δ) ∧ (∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ := by
  first | exact @GlobalTheory.PDForm.exists_lift_of_pdDerivation | exact GlobalTheory.PDForm.exists_lift_of_pdDerivation | (intros; apply GlobalTheory.PDForm.exists_lift_of_pdDerivation <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.quotient_dividedPowerFiltration_compatibleForms : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : B →+* G) (h : SemiHom (RingHom.id R) q) (n : ℕ), IsDPMorphism δ δ' q → Function.Surjective q → J' = J.map q → (∀ b, q b = 0 ↔ b ∈ fil δ (n + 1)) → (∀ x, h.mDR x ∈ rel R δ' → x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), h.mDR x ∈ rel R δ' := by
  first | exact @GlobalTheory.PDForm.quot_fil_rel | exact GlobalTheory.PDForm.quot_fil_rel | (intros; apply GlobalTheory.PDForm.quot_fil_rel <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift : (∀ (D : Data) (Λ : Lift D), (∀ k, ∃! w, Λ.Res1 k w) ∧ (∀ w, ∃! k, Λ.Res1 k w) ∧ ∀ k w, Λ.Res1 k w → (k ∈ ((KK D.κ D.t).res Λ.L).Z1 ↔ w ∈ cechDeRhamTotalCocyclesOne (OAff D.s)) ∧ ((∃ g, ((KK D.κ D.t).res Λ.L).D0 g = k) ↔ ∃ g, dTot0 (OAff D.s) g = w)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ k, ∃! w, Λ.Res2 k w) ∧ (∀ w, ∃! k, Λ.Res2 k w) ∧ ∀ k w, Λ.Res2 k w → (k ∈ ((KK D.κ D.t).res Λ.L).Z2 ↔ w ∈ cechDeRhamTotalCocyclesTwo (OAff D.s)) ∧ ((∃ g, ((KK D.κ D.t).res Λ.L).D1 g = k) ↔ ∃ g, dTot1 (OAff D.s) g = w) := by
  first | exact @GlobalTheory.PDForm.lift_res_bij | exact GlobalTheory.PDForm.lift_res_bij | (intros; apply GlobalTheory.PDForm.lift_res_bij <;> assumption)
end
