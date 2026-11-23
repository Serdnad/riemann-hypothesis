module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle030
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
public import Formalism.LocalToGlobal.HilbertRowConditions.Bundle001
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.UnipotentAdelicQuotients.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle399
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle411
public import Formalism.LocalRingCardinality.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle446
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle042
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle448
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle447
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.LintegralFintypeProd
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localData_of_term_lattice_and_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∃ y : Dat Z FP, LocOver Λ y ∧ ∀ p d, GlobalTheory.LocOver.Over (FP p) d (GlobalTheory.LocOver.locU Z p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) ↔ LocNG.Datum.Rel d (y p) := by
  first | exact @GlobalTheory.Unfold.TermLocal.local_data_of_term | exact GlobalTheory.Unfold.TermLocal.local_data_of_term | (intros; apply GlobalTheory.Unfold.TermLocal.local_data_of_term <;> assumption)
end

section

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.terms_same_row_same_weight_same_localData : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → Formalism.L2.SG.TermOp.wt t = Formalism.L2.SG.TermOp.wt t' ∧ (nmlOf Y u u' t = nmlOf Y u u' t' → ∀ (p : PlF D) (P : LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), P.RelG (LocNG.theta (Y.M p)) → ∀ d, Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) → Over P d (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t'.toTerm.lam (lf D (X.Fu u)) (Quot.out t'.toTerm.cls).1 (Tu D u) (Tu D u'))) := by
  first | exact @GlobalTheory.LocOver.TermSame.same | exact GlobalTheory.LocOver.TermSame.same | (intros; apply GlobalTheory.LocOver.TermSame.same <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl Formalism.IndefR.principalLevelFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.constructedSpectralObjects_irreducibilityConditions : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (F0 : ∀ u, Forms0 D u) (s : SAt R F eE F0) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r), StdPsi hF PY → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → GlobalTheory.LabPin.TypeLab D rep → GoodFTAll D → Formalism.MainNotions.S.AutTie D s.P.X.B s.P.X.pl ∧ RowDictTie s.P.X s.P.G s.S.hI.eHH ∧ GlobalTheory.LabPin.LabTie s.P.X s.S.hI.eHH := by
  first | exact @GlobalTheory.Sat.ties_at | exact GlobalTheory.Sat.ties_at | (intros; apply GlobalTheory.Sat.ties_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

theorem _root_.GlobalTheory.T.irreducibilityRow_of_concreteAutomorphicData : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∃ cIc : ℝ, 0 < cIc ∧ ∀ 𝒞 : FamClass, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => 𝒞 Fm → ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, ∃ (X : HidaSetting (Fm.D x i)) (G : GoodOp X) (ι : (Fm.D x i).s.HH ≃ₗᵢ[ℂ] HHX X), AutTie (Fm.D x i) X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i), LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) := by
  exact GlobalTheory.IrrRowConcrete.irr_row_closed
end

section

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalConst

theorem constC : ConstC := by
  intro D X Y u C hB hG hcov
  have hS : ∀ τ, GoodS D (lamD D τ) (locS hB u u τ) := fun τ => (hG.2 u τ).2
  have hc : ∀ τ, 0 < cOf hB u τ := fun τ => (hS τ).2.2.2.2.2.2.2.1
  set d : D.what₂.Tau → ℝ := fun τ => (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) with hd
  set L : D.what₂.Tau → ℝ := fun τ => (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal with hL
  have hcL : ∀ τ, cOf hB u τ = L τ / d τ := fun τ => rfl
  have hdpos : ∀ τ, 0 < d τ := by
    intro τ
    rcases (show (0:ℝ) ≤ d τ by positivity).lt_or_eq with h | h
    · exact h
    · have := hc τ; rw [hcL, ← h, div_zero] at this; exact absurd this (lt_irrefl 0)
  have hLpos : ∀ τ, 0 < L τ := by
    intro τ
    rcases (show (0:ℝ) ≤ L τ from ENNReal.toReal_nonneg).lt_or_eq with h | h
    · exact h
    · have := hc τ; rw [hcL, ← h, zero_div] at this; exact absurd this (lt_irrefl 0)
  refine ⟨fun τ => ⟨hc τ, ?_⟩, ?_⟩
  · have e : cOf hB u τ * (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) /
        (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal = 1 := by
      change L τ / d τ * d τ / L τ = 1
      field_simp [(hdpos τ).ne', (hLpos τ).ne']
    unfold sclOf
    rw [e, Real.sqrt_one, Complex.ofReal_one]
  ·
    obtain ⟨cN, hN0, hNT, hN⟩ := GlobalTheory.T.unipotentHaar_eq_const_mul_transported_product D X C hB hG u
    obtain ⟨cH, hH0, hHT, hHu, hH⟩ := GlobalTheory.T.haarMeasure_besselUnitary_eq_pullback_product D X C hB hG u
    have hP := GlobalTheory.T.prod_localQuotientMass_eq_measureRatio D X C hB hG u cN cH hN0 hNT hH0 hHT hN hH
    have hP' : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = cN * cH := by
      rw [← hP]; exact Finset.prod_congr rfl fun τ _ => GlobalTheory.T.l2SG_phiOf_eq_l2SG_wT_of_goodLoc D X C hB hG u τ
    have hFN : MeasurableSet (Y.FN u) := (Y.FN_fund u).1
    have hmN : (X.muN u (Y.FN u)).toReal = cN.toReal * (covN C Y u).toReal := by
      rw [hN _ hFN, ENNReal.toReal_mul]; rfl
    have hmH : (X.muH u Set.univ).toReal = cH.toReal := by rw [hHu]
    have hkey : (∏ τ, L τ) * (covN C Y u).toReal =
        (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
      have : (∏ τ, L τ) = (∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := by
        rw [ENNReal.toReal_prod]
      rw [this, hP', ENNReal.toReal_mul, hmN, hmH]; ring
    have hdd : (Module.finrank ℂ (X.Vpi u) : ℝ) = ∏ τ, d τ := by
      rw [Formalism.L2.SG.Pf.finrank_Vpi X u, Nat.cast_prod]
      exact (Fintype.prod_equiv X.pl.symm (fun τ => d τ) _ fun τ => rfl).symm
    have hprod : ∏ τ, cOf hB u τ = (∏ τ, L τ) / ∏ τ, d τ := by
      rw [← Finset.prod_div_distrib]; exact Finset.prod_congr rfl fun τ _ => hcL τ
    unfold Formalism.L2.SG.TermOp.scl Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X
    rw [hprod, ← hdd]
    set mN := (X.muN u (Y.FN u)).toReal
    set mH := (X.muH u Set.univ).toReal
    set dd := (Module.finrank ℂ (X.Vpi u) : ℝ)
    set V := X.volK2
    set cv := (covN C Y u).toReal
    have hdd0 : 0 < dd := by rw [hdd]; exact Finset.prod_pos fun τ _ => hdpos τ
    have hmN0 : 0 ≤ mN := ENNReal.toReal_nonneg
    have hmH0 : 0 ≤ mH := ENNReal.toReal_nonneg
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    have hc0 : 0 ≤ V * mN * mH / dd := by positivity
    rw [Real.sqrt_mul_self hc0]
    by_cases h0 : V * mN * mH = 0
    · rw [h0, zero_div, _root_.inv_zero]; simp
    · have hV : V ≠ 0 := by intro h; apply h0; rw [h]; ring
      have hmN : mN ≠ 0 := by intro h; apply h0; rw [h]; ring
      have hmH : mH ≠ 0 := by intro h; apply h0; rw [h]; ring
      have e : (V * mN * mH / dd)⁻¹ * V * ((∏ τ, L τ) / dd) * cv = 1 := by
        field_simp
        linear_combination hkey
      rw [e]

end GlobalTheory.LocalConst
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.formalDegree_eq_harishChandra_of_gap : ∀ (D : D7), Ties D → ∀ (τ : D.what₂.Tau) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) → Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ)) h → Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h → D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) :=
  GlobalTheory.dsig_eq_fdegHC_of_gap
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProductL2
open Formalism.L2.SG.Pf.AmpWinLoc

theorem prod_lint (D : D7) (X : HidaSetting D) (u : D.what₂.Word)
    (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞) (hβm : ∀ v, Measurable (β v)) :
    ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ y, β v y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hW : ∀ x : X.B.I.Ginf, ‖X.Wu u x‖ₑ ^ 2 = ∏ v, ‖X.Wloc u v (x v)‖ₑ ^ 2 := by
    intro x
    have : ‖X.Wu u x‖ₑ = ∏ v, ‖X.Wloc u v (x v)‖ₑ := by
      rw [← ofReal_norm_eq_enorm, Formalism.L2.SG.Pf.WuDec.norm_Wu,
        ENNReal.ofReal_prod_of_nonneg (fun v _ => norm_nonneg _)]
      simp only [ofReal_norm_eq_enorm]
    rw [this, Finset.prod_pow]
  simp_rw [hW, ← Finset.prod_mul_distrib]
  have : ∀ v, SigmaFinite (Formalism.REAL.muG (X.B.I.ε v)) := fun v => inferInstance
  exact QPK.lintegral_fintype_prod (μ := fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v y => β v y * ‖X.Wloc u v y‖ₑ ^ 2)
    (fun v => (hβm v).mul ((X.Wloc_cont u v).enorm.measurable.pow_const 2))

theorem muH_univ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) :
    Measure.pi (fun v => muHl C u (X.pl v) v) Set.univ = 1 := by
  haveI : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := fun v => by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ _ rfl; exact sf_muHl C u τ
    exact h _ _ (X.pl.symm_apply_apply v)
  rw [Measure.pi_univ]
  refine Finset.prod_eq_one fun v _ => ?_
  have h : ∀ τ w, vOf X τ = w → muHl C u τ w Set.univ = 1 := by
    rintro τ _ rfl
    rw [← Set.preimage_univ (f := eT C τ (vOf X τ)), ← Measure.map_apply (eT_emb C τ _).measurable MeasurableSet.univ,
      map_muHl C u τ, C.muW_one u τ]
  exact h _ _ (X.pl.symm_apply_apply v)

end GlobalTheory.ProductL2

namespace GlobalTheory.ProductL2
open Formalism.L2.SG.Pf.AmpWinLoc

theorem l2prod : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → 0 < (X.muN u (Y.FN u)).toReal → 0 < (X.muH u Set.univ).toReal → (∀ τ, 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) ∧ (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
  intro D X Y θ C hB u hθ _ _ _
  have key : ∀ v, ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) = 1) ∧
      (∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) =
        l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v))) ∧
      SigmaFinite (QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
    intro v
    have h : ∀ τ w, vOf X τ = w → ∃ β : Formalism.REAL.UJ (X.B.I.ε w) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ w) (muHl C u τ w)) = 1) ∧
        (∫⁻ y, β y * ‖X.Wloc u w y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε w)) =
          l2SG (C.nuS u τ) (phiOf hB u τ)) ∧
        SigmaFinite (QPK.mulMap (muNl C τ w) (muHl C u τ w)) := by
      rintro τ _ rfl
      obtain ⟨β, h1, h2, h3⟩ := GlobalTheory.T.exists_bruhatFunction_localBesselIntegral_eq_L2Mass D X θ C hB u τ
      exact ⟨β, h1, h2, h3, (invOn_mulMap C u τ).1⟩
    exact h (X.pl v) v (X.pl.symm_apply_apply v)
  choose β hβm hβ1 hβl hsf using key
  obtain ⟨κN, hN0, hNt, hN⟩ := GlobalTheory.T.unipotentHaar_eq_const_smul_pi_localMeasures D X θ C u
  obtain ⟨κH, hH0, hHt, hH⟩ := GlobalTheory.T.subgroupHaar_eq_const_smul_pi_localMeasures D X θ C u
  have hS := GlobalTheory.T.unipotentSubgroupHaarProduct_eq_pi_localImage D X θ C u κN κH hN hH
  have hW := GlobalTheory.T.weil_formula_besselNormSq_bruhatProduct D X u (κN * κH) _ hsf hS β hβm hβ1
  rw [prod_lint D X u β hβm] at hW
  simp only [hβl] at hW
  have hP : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = κN * κH := by
    rw [← hW]; exact (Equiv.prod_comp X.pl (fun τ => l2SG (C.nuS u τ) (phiOf hB u τ))).symm
  have hP0 : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 := by rw [hP]; exact mul_ne_zero hN0 hH0
  have hPt : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ ⊤ := by rw [hP]; exact ENNReal.mul_ne_top hNt hHt
  have hne0 : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 := fun τ =>
    (Finset.prod_ne_zero_iff.1 hP0) τ (Finset.mem_univ τ)
  have hnet : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ ⊤ := by
    intro τ ht
    apply hPt
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ht]
    exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun τ' _ => hne0 τ')
  refine ⟨fun τ => ENNReal.toReal_pos (hne0 τ) (hnet τ), ?_⟩
  rw [← ENNReal.toReal_prod, hP, ← GlobalTheory.T.pi_pulledBack_unipotentMeasure_eq_besselImage D X θ C (Y.FN u) hθ (Y.FN_fund u).1, hN, hH,
    Measure.smul_apply, Measure.smul_apply, muH_univ D X θ C u]
  simp only [smul_eq_mul, mul_one, ENNReal.toReal_mul]
  ring

end GlobalTheory.ProductL2
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.DsigSize

theorem thrE_add_one_lt {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) :
    Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
  have hn := Formalism.MainNotions.nS_cast D
  have h6 := Formalism.MainNotions.six_le_n D
  rw [← hn] at h6 ⊢
  set n : ℝ := ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ)
  have hthr : Formalism.MainNotions.GapDS.thrE (epsSH D.R) ≤ 4 * n ^ 3 :=
    Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by linarith only [h6])
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have hmf : D.R.m ^ 4 ≤ D.R.f := by unfold StandingHypotheses at hH; exact hH.2.2.1
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast le_trans this hmf
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ (by linarith only [h6])
  have hn16 : 6 ≤ n ^ 16 :=
    (show (6 : ℝ) ≤ 6 ^ 16 by norm_num).trans (pow_le_pow_left₀ (by norm_num) h6 16)
  calc
    _ < 4 * n ^ 3 + 2 := by linarith only [hthr]
    _ ≤ 6 * n ^ 3 := by linarith only [hn3]
    _ ≤ n ^ 16 * n ^ 3 := mul_le_mul_of_nonneg_right hn16 (by positivity)
    _ = n ^ 19 := (pow_add n 16 3).symm
    _ ≤ n ^ 19 * (D.R.f : ℝ) ^ 5 := le_mul_of_one_le_right (by positivity) hf5
    _ ≤ (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5) :=
      le_mul_of_one_le_left (by positivity) hCL
    _ = Cl * n ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by ac_rfl

theorem dsigHC : Formalism.L2.SG.Pf.SzHypFD.DsigHC := by
  intro D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ
  exact GlobalTheory.dsig_eq_fdegHC_of_gap D hT τ _ (Formalism.MainNotions.BridgeLemma.szh_hc hH τ) (Formalism.MainNotions.BridgeLemma.szh_gap hH τ)
    (thrE_add_one_lt hH hCL)

end GlobalTheory.DsigSize
end
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.covolume_unipotentIntegral_normalisedHaar : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := by
  first | exact @GlobalTheory.CovNFormulaPf.main | exact GlobalTheory.CovNFormulaPf.main | (intros; apply GlobalTheory.CovNFormulaPf.main <;> assumption)
end
