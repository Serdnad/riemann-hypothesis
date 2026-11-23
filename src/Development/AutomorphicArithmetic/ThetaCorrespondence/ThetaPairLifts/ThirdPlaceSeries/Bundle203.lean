module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle051
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle200
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle117
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle176
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle118
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle112
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.SelAll
theorem rpk_eq_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} (P : Formalism.L2.Rows.RowSideFamily O.ex)
    {Dc Dc' : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Sp : ∀ Zs, SPer (Dc Zs)} {Sp' : ∀ Zs, SPer (Dc' Zs)}
    {Z Z' : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {B : _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Z S} {B' : _root_.Formalism.IndefR.RealTBAlt R P Dc' Sp' Z' S}
    (h1 : Dc = Dc') (h2 : HEq Sp Sp') (h3 : Z = Z') (h4 : HEq B B') :
    (⟨P, Dc, Sp, Z, B⟩ : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) = ⟨P, Dc', Sp', Z', B'⟩ := by
  subst h1; subst h3; cases h2; cases h4; rfl
theorem real_tb_congr_of_heq {D : D7} {O : Obj D} (R : _root_.Formalism.L2.RecTAlt O.ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (P : Formalism.L2.Rows.RowSideFamily O.ex)
    {Dc Dc' : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Sp : ∀ Zs, SPer (Dc Zs)} {Sp' : ∀ Zs, SPer (Dc' Zs)}
    {Z Z' : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    (h1 : Dc = Dc') (h2 : HEq Sp Sp') (h3 : Z = Z') :
    _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Z S = _root_.Formalism.IndefR.RealTBAlt R P Dc' Sp' Z' S := by
  subst h1; subst h3; cases h2; rfl

theorem bwit_exists_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) := by
  intro hG hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN hM
  refine ((GlobalTheory.Fc.EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and hM).mono ?_
  rintro κ K - ⟨hH, hMK⟩ q R hR c DH _ _
  have hMq := hMK q
  have hcols : R.T.cols = q.x.col.C := hR.s.cols
  obtain ⟨sP, sS, hP, hS⟩ : ∃ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP),
      HEq sP q.saturationAtWeightedPoint.P ∧ HEq sS q.saturationAtWeightedPoint.S := by
    rw [hcols]; exact ⟨q.saturationAtWeightedPoint.P, q.saturationAtWeightedPoint.S, HEq.rfl, HEq.rfl⟩
  have hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK := sP.fin.inHH
  obtain ⟨a, x, ax, C, hDc, hSp, hW', hXg, hCP, hZ, hsp, κS, sEEc, hsE, hκ, hsee⟩ :=
    _root_.GlobalTheory.T.exists_selected_realization_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS DH.1.1 DH.1.2 c hin
  obtain ⟨y, hyt, hyc, hySx, hyeF, hyfi, hyu⟩ := _root_.GlobalTheory.T.selected_realization_geometric_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax hin hsp κS sEEc hsE hκ hsee
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.T.selected_realization_side_alt hG hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax y
  have pin := _root_.GlobalTheory.T.selected_lower_map_holds_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax
  obtain ⟨HD, hHD⟩ := _root_.GlobalTheory.HostDatumExists.exists_hostDatum_alt hGAR _ _ _ _ _ _ _ _ q.O.ex R.T.toTiedDataS (GlobalTheory.Mem.Top.Bl.hostPins_wpt hRF _ _ q) q.x.pin.d3b
  have side := _root_.GlobalTheory.T.selected_side_realization_holds_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax y r HD hHD
  have h1 : C.c.face = x.F.Dc := eq_of_heq hDc
  have h3 : GlobalTheory.Fc.zsc (divisionPairOfAdelicFormsFaceColumnsData x) DH.1.1 DH.1.2 c = x.F.Zsc := hZ.symm
  have hB := _root_.GlobalTheory.Mem.R3.SelAll.real_tb_congr_of_heq R (sS.toRealSpectralMatching R) (divisionPairOfAdelicFormsFaceColumnsData x) h1 hSp h3
  have hx : Holds x.R x.F := by
    have e : a.x = x := eq_of_heq ax
    rw [← e]; exact a.intersectionNumber_baseChange
  let b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c := ⟨R, sS.toRealSpectralMatching R, divisionPairOfAdelicFormsFaceColumnsData x, pin, DH, C, cast hB.symm (_root_.GlobalTheory.Mem.R3.boundedRealisationOfInput y)⟩
  have heq : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y := _root_.GlobalTheory.Mem.R3.SelAll.rpk_eq_alt (divisionPairOfAdelicFormsFaceColumnsData x) h1 hSp h3 (cast_heq _ _)
  exact ⟨b, rfl, ⟨{ x := x, a := a, ax := ax, y := ⟨hx, y, r, heq, HD⟩, recPin := hR, s := ⟨sP, sS, hP, hS, rfl⟩, pt := ⟨hyt, hyc⟩, sx := hySx, eF := hyeF, fi := hyfi, uS := hyu, parts := hr, cW := ⟨hW', hXg⟩, d3b := heq_of_eq hHD, side := side, colPins := hCP }⟩⟩
end GlobalTheory.Mem.R3.SelAll
end
end

section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
noncomputable section
namespace GlobalTheory.ThetaSizeBounds
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem run_params_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => (dat p i).q ≤ (Fm.D x ι).R.m ∧ 0 ≤ GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ∧ lenT p i PP * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ≤ C * unitE p ∧ ∀ DF : ℕ, 1 ≤ DF → (DF : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 → GlobalTheory.EtaAn.RunOK (Fm.D x ι).host.E (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) (Fm.D x ι).R.m ∧ ∀ s : ℝ, (Y.d.l₂.M : ℝ) * s < (Fm.L x ι).sc.b → Real.sqrt s < ReciprocityTheory.ChartRestriction.G.I2.th (E := (Fm.D x ι).host.E) ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) := by
  intro _
  refine (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) _root_.GlobalTheory.CovTop.WtShape.wtN_z).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨A, -, a, ha⟩, ⟨C2, -, b0, hb0⟩⟩ := hh
  refine ⟨200000, by norm_num, max a b0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  have hN : HostNum (Fm.D x ι) (Fm.L x ι) (Fm.parT x hx ι).PP A 6 := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hW : WtNum p i (Fm.parT x hx ι).PP := hb0 x hx ((le_max_right _ _).trans hle) ι p hp i
  have S := Fm.sizes x hx ι
  have P := Fm.params x hx ι
  have hm4 := Formalism.L2.Pj.host_m_pow_four_le_f S
  have hf2 := Formalism.L2.Pj.host_f_sq_le_rd P
  have hrd16 := Formalism.L2.Pj.host_rd_ge_sixteen P
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have ef := Formalism.L2.Pj.hostSize_f (Fm.D x ι)
  have erd := Formalism.L2.Pj.hostSize_rd (Fm.D x ι)
  have a1 := (Fm.D x ι).R.two_le_m
  have a2 := (Fm.D x ι).R.m_add_three_le_k
  have a3 : (Fm.D x ι).R.r + 5 ≤ (Fm.D x ι).R.t := (Fm.D x ι).R.rank_add_five_le
  have a4 : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.k := (Fm.D x ι).R.f_le_k
  have a5 : (Fm.D x ι).R.k ≤ (Fm.D x ι).R.r ∧ (Fm.D x ι).R.m ≤ (Fm.D x ι).R.r ∧ 6 ≤ (Fm.D x ι).R.r := by
    unfold Formalism.BasicNotions.Ranks.r; omega
  have hf8 := hN.f8
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hLL := hN.big.2.2.2
  have hfR : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
  have hrR : (6 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast a5.2.2
  have hmR : (2 : ℝ) ≤ (Fm.D x ι).R.m := by exact_mod_cast a1
  have ht : (11 : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : 11 ≤ (Fm.D x ι).R.t)
  have hft : ((Fm.D x ι).R.f : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.t)
  have hrt : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.r ≤ (Fm.D x ι).R.t)
  have hb1 : 1 ≤ (Fm.L x ι).sc.b := Real.one_le_exp (by linarith)
  have hb0' : 0 < (Fm.L x ι).sc.b := Real.exp_pos _
  have hq : (1 : ℝ) ≤ (Fm.D x ι).host.q := by exact_mod_cast (Fm.D x ι).host.hyp.1.one_lt.le
  have hd' : (1 : ℝ) ≤ (Fm.D x ι).host.d := by exact_mod_cast (Fm.D x ι).host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ (Fm.D x ι).R.n := by exact_mod_cast (Fm.D x ι).R.ord_pos
  have hqd : (1 : ℝ) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d := by nlinarith
  have hs : Real.sqrt (((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d) ≤ ((Fm.D x ι).host.q : ℝ) * (Fm.D x ι).host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) := by
    unfold szCond
    exact UpperTheory.Ram.Rd.rdE_le_cond _
  have hc1 : (1 : ℝ) ≤ szCond (Fm.L x ι) := h1.trans hc
  have hsb : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hrdb : (Fm.D x ι).host.rdE ≤ (Fm.L x ι).sc.b := by
    have e1 : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) ^ 36 * ((Fm.D x ι).R.t : ℝ) ^ 150 :=
      hc.trans ((le_self_pow₀ hc1 (by norm_num)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))))
    exact (e1.trans sC).trans hsb
  have hlogrd : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E) ≤ 2 * (Fm.L x ι).sc.L := by
    rw [erd]
    have := Real.log_le_log (by linarith) hrdb
    unfold Formalism.BasicNotions.Scale.b at this
    rw [Real.log_exp] at this
    linarith
  have hlfr := hN.logfr.1
  have hlf : Real.log (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) ≤ 2 * (Fm.L x ι).sc.L := by
    rw [ef]
    have hf0 : (0 : ℝ) < (Fm.D x ι).R.f := by linarith
    have := Real.log_le_log hf0 (le_mul_of_one_le_right hf0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.r))
    linarith
  have hlr : Real.log ((Fm.D x ι).R.r : ℝ) ≤ (Fm.L x ι).sc.L := by
    have hr0 : (0 : ℝ) < (Fm.D x ι).R.r := by linarith
    have := Real.log_le_log hr0 (le_mul_of_one_le_left hr0.le (by linarith : (1 : ℝ) ≤ (Fm.D x ι).R.f))
    linarith
  have hg0 : ∀ k, (0 : ℝ) < (Fm.D x ι).host.g k := fun k => by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
  have hq1 : 1 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ((Fm.D x ι).host.g_prime 0).ne_zero ((Fm.D x ι).host.g_prime 1).ne_zero)
  have hlq : Real.log (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ≤ 70 * (Fm.L x ι).sc.L := by
    push_cast
    rw [Real.log_mul (hg0 0).ne' (hg0 1).ne']
    linarith [hN.logg 0, hN.logg 1]
  have hP := archimedeanBoundTotalConstant_nonneg_le_bound (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m
    (Fm.L x ι).sc.L (by linarith) (by rw [ef]; omega) (by omega) (by omega) a5.2.1 hq1 (by rw [erd]; exact h1)
    hlogrd hlf hlr hlq
  rw [ef] at hP
  refine ⟨?_, hP.1, ?_, fun DF hDF hDFb => ⟨?_, ?_⟩⟩
  · rw [hW.sig.2.1]; unfold Formalism.BasicNotions.Ranks.sigW; omega
  ·
    have hZ1 : (1 : ℝ) ≤ zBase (Fm.L x ι) := by
      unfold zBase
      have := mul_le_mul hfR hrR (by norm_num) (by linarith)
      nlinarith
    have hZ : zBase (Fm.L x ι) ^ 2 ≤ (Fm.parT x hx ι).PP :=
      (pow_le_pow_right₀ hZ1 (by norm_num)).trans hN.ppLow
    have hD1 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) := by
      rw [hW.dim]
      have : 1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.choose_pos (by omega)).ne')
      exact_mod_cast this
    have hT0 : (0 : ℝ) ≤ lenT p i (Fm.parT x hx ι).PP := Nat.cast_nonneg _
    have hPP0 : 0 ≤ (Fm.parT x hx ι).PP := le_trans (by positivity) hZ
    have hrow := hW.what₂.2
    have hTP : (lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP ≤ (Fm.L x ι).sc.b := by
      revert hrow hD1 hT0 hPP0 hL10
      generalize (lenT p i (Fm.parT x hx ι).PP : ℝ) = T
      generalize (Fm.parT x hx ι).PP = PP
      generalize (dimFlag (dat p i) : ℝ) = Dd
      generalize (Fm.L x ι).sc.L = L
      generalize (Fm.L x ι).sc.b = b
      intro hrow hD1 hT0 hPP0 hL10
      have e0 : 0 ≤ PP * T := mul_nonneg hPP0 hT0
      have e1 : PP * T * 1 ≤ PP * T * Dd ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hD1) e0
      have e2 : PP * T * Dd ^ 2 * 1 ≤ PP * T * Dd ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have hU : (Fm.L x ι).sc.b ≤ unitE p := by
      rw [hW.unit]
      have e1 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m := by nlinarith
      have e2 : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x) := by
        have := mul_le_mul e1 (by linarith : (1 : ℝ) ≤ (Fm.L x ι).sc.L) zero_le_one (by linarith)
        have := mul_le_mul this hLL zero_le_one (by linarith)
        linarith
      have : (Fm.L x ι).sc.b * 1 ≤ (Fm.L x ι).sc.b *
          ((Fm.D x ι).R.f * (Fm.D x ι).R.m * (Fm.L x ι).sc.L * Real.log (Real.log (Fm.L x ι).sc.x)) :=
        mul_le_mul_of_nonneg_left e2 (by linarith)
      nlinarith
    have hPz : GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1)
        (Fm.D x ι).R.m 5 1 ≤ 200000 * zBase (Fm.L x ι) ^ 2 := hP.2
    calc (lenT p i (Fm.parT x hx ι).PP : ℝ) * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r
          ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1
        ≤ (lenT p i (Fm.parT x hx ι).PP : ℝ) * (200000 * (Fm.parT x hx ι).PP) :=
          mul_le_mul_of_nonneg_left (hPz.trans (by linarith)) hT0
      _ = 200000 * ((lenT p i (Fm.parT x hx ι).PP : ℝ) * (Fm.parT x hx ι).PP) := by ring
      _ ≤ 200000 * unitE p := by linarith
  ·
    have hDF1 : (1 : ℝ) ≤ DF := by exact_mod_cast hDF
    have hk : (1 : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.k)
    have hg : ∀ k, (Fm.L x ι).sc.b ^ 8 ≤ ((Fm.D x ι).host.g k : ℝ) := fun k =>
      (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
    have key := size_inequality_real (Fm.D x ι).host.rdE (szCond (Fm.L x ι)) (Fm.D x ι).R.t (Fm.L x ι).sc.b (Fm.D x ι).R.f
      (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0) ((Fm.D x ι).host.g 1) h1 hc sC ht (by linarith) hft (by linarith) hrt
      hDF1 hDFb (hg 0) (hg 1)
    have hrun := GlobalTheory.RunParametersOfLower.runOK_of_le (Fm.D x ι).host.E (Fm.D x ι).R.r DF
      ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m hDF (by rw [ef]; nlinarith) (by omega) hm4 hf2 hrd16
      (by unfold ReciprocityTheory.ChartRestriction.G.I2.RR; rw [ef, erd]; push_cast; exact key)
    rw [ef] at hrun
    exact hrun
  ·
    intro s hs
    have hR0 : (1 : ℝ) ≤ Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      have : (0 : ℝ) ≤ DF := Nat.cast_nonneg _
      nlinarith
    have hRR : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.RR (E := (Fm.D x ι).host.E) := by
      unfold ReciprocityTheory.ChartRestriction.G.I2.RR; exact one_le_pow₀ (by linarith)
    have := sqrt_lt_th_real ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Y.d.l₂.M : ℝ)
      (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF)))
      (ReciprocityTheory.ChartRestriction.G.I2.RR (E := (Fm.D x ι).host.E)) (Fm.L x ι).sc.b s hq1 hb0' (level_ge p i Y hY (by linarith))
      (by rw [ef]; linarith) hR0 hRR hs
    unfold ReciprocityTheory.ChartRestriction.G.I2.th
    exact this
end GlobalTheory.ThetaSizeBounds
end
end
end
