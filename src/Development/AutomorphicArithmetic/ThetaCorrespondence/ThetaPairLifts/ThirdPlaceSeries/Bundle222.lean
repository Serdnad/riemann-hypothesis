module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle017
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle172
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle139
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle088
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle073
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle126
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle086
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle220
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle161
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle219
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle137
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle140
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle087
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle081
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle004

@[expose] public section

section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct

theorem _root_.GlobalTheory.T.real_datum_normalized_rational_base_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧
          ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val =
            c • (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P) := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.expOne_level_alt | exact _root_.GlobalTheory.BigOn.Exp.expOne_level_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.expOne_level_alt <;> assumption)
end
end

section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DimLogTop
theorem log_top_dimension_le_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) ≤ PP := by
  intro hP hSz
  have hBex := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP
  obtain ⟨Cb, -, hB⟩ := hBex
  have hG := _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain hP
  have hQ := _root_.GlobalTheory.QuoWt.weights_at_point_alt hSz
  have hS := _root_.GlobalTheory.CovTop.CovSz.size_rows_alt hSz
  have hW := _root_.GlobalTheory.HSApp.wtBig_run_alt
  refine Closed.imp (Closed.and (Closed.and hQ hS) hW) ?_
  intro eps Fm CH heps hh
  obtain ⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩ := hh
  refine ⟨0, le_rfl, max (max (max x1 x2) x3) ((max Cb 1) ^ eps⁻¹), ?_⟩
  intro x hx hle ι p hp i hi Y hY Z
  have hle1 : max (max x1 x2) x3 ≤ x := (le_max_left _ _).trans hle
  have hq := h1 x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle1)) ι p hp i hi
  have hs := h2 x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle1)) ι p hp i hi Y hY
  have hwb := h3 x hx ((le_max_right _ _).trans hle1) ι p hp i hi
  obtain ⟨hp1, hq1, hE, -, hstr, -, -⟩ := hq
  obtain ⟨hLJ, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, -, hkap, hZ12, -, -, -, -, hwt⟩ := hs
  set PP := (Fm.parT x hx ι).PP with hPP
  have hx1 : Fm.x1 < x := hx
  have hLx : (Fm.L x ι).sc.L = x ^ eps := by
    unfold Scale.L; rw [Fm.L_x x ι hx1, Fm.L_eps x ι]
  have hLC : max Cb 1 ≤ (Fm.L x ι).sc.L := by
    rw [hLx]
    have h0 : (0 : ℝ) ≤ (max Cb 1) ^ eps⁻¹ := Real.rpow_nonneg (by positivity) _
    calc max Cb 1 = ((max Cb 1) ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow (by positivity) heps.ne').symm
      _ ≤ x ^ eps := Real.rpow_le_rpow h0 ((le_max_right _ _).trans hle) heps.le
  have hT2 : 2 ≤ GlobalTheory.FlagTan.dimFlag (dat p i) + lenT p i PP := by
    have hT1 := hwb.le_T
    have hD1 := hwb.one_le
    change 1 ≤ GlobalTheory.FlagTan.dimFlag (dat p i) at hD1
    change GlobalTheory.FlagTan.dimFlag (dat p i) + 1 ≤ lenT p i PP at hT1
    omega
  have hanti := GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i)
    (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)) (lenT p i PP)
    (fun τ => (hstr τ).1) hT2 hp1 hq1
  have hsum := hwt (lenT p i PP) le_rfl
  have hsize : Real.log (∑ τ, ∑ k, |(((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
      WtPar (dat p i)).wt (lenT p i PP)) τ k : ℝ)|) ≤ 20 * (Fm.L x ι).sc.L := by
    refine GlobalTheory.CovTop.DimLogTop.log_size_le ((Fm.D x ι).R.f : ℝ) ((Fm.D x ι).R.r : ℝ) (Fm.L x ι).sc.L (kap p i) _
      (by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)) (by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r))
      hL1 (sizeK_nonneg _ _ _) hkap hfr (by positivity) ?_
    have : (0 : ℝ) ≤ 6 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 := by positivity
    have e : zBase (Fm.L x ι) = ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) * (Fm.L x ι).sc.L := by unfold zBase; ring
    rw [← e]; linarith
  have hBr := (hB (Fm.D x ι) p.T hLJ ((i : ℕ) + 1) hp1 hq1 hE hInR Y (expL (Fm.L x ι).sc.L)
    (391 * zBase (Fm.L x ι) ^ 2) hY.1 (Fm.L x ι).sc.L hL1 hM hfs hfr (by unfold zBase; exact le_rfl)
    _ (fun τ => (hanti τ).1) hsize Z).2.2
  have hGd := (hG (Fm.D x ι) p.T hLJ ((i : ℕ) + 1) hp1 hq1 hE hInR Y (expL (Fm.L x ι).sc.L)
    (391 * zBase (Fm.L x ι) ^ 2) hY.1 _ (fun τ => (hanti τ).1) (fun τ => (hanti τ).2)).2 Z
  have hrk : Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
      WtPar (dat p i)).wt (lenT p i PP)) Z = (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i)
      ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt
      (lenT p i PP)) 0)) : ℝ) := by
    show ((rankOn Y.U Z _ : ℕ) : ℝ) = _
    unfold rankOn
    rw [rkK_eq_finrank_of_span_top _ hGd.2.2]
  rw [← hrk]
  have hfr1 : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) := by
    have : 1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hLZ : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    unfold zBase; nlinarith
  have hcube := GlobalTheory.CovTop.DimLogTop.cube_le Cb (Fm.L x ι).sc.L (zBase (Fm.L x ι)) ((le_max_left _ _).trans hLC) hL1 hLZ
  have h2 : Cb * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 = Cb * zBase (Fm.L x ι) ^ 3 := by
    unfold zBase; ring
  linarith
end GlobalTheory.CovTop.DimLogTop
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.log_finrank_cuspOn_le : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) ≤ PP := by
  first | exact @_root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le_alt | exact _root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le_alt | (intros; apply _root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le_alt <;> assumption)
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.StageZeroRow
theorem tupAllUsed_at_part_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : Formalism.L2.DIV.TupAllUsed b.P :=
  _root_.GlobalTheory.Fc.FourBoundsAtBundles.tupAllUsed_part_alt b
theorem p_div_at_piece_of_div3g {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b :=
  _root_.GlobalTheory.Fc.FourBoundsAtBundles.p_div_of_div3g b h
theorem row_rRows_stage0_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesClassification → _root_.GlobalTheory.BigOn.SurjectiveOntoX → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotDivisorCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowGoodnessCondition Q Lk → _root_.GlobalTheory.Fc.S0.GeometricWeakCompatibility' Q Lk → _root_.GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries Q Lk → _root_.GlobalTheory.Fc.S0.FunctionalCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowKappaCondition Q Lk → _root_.GlobalTheory.Fc.RL.RowDefectCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition _root_.GlobalTheory.Fc.DefiniteSideCondition Q Lk := by
  intro hDS hHC hCR hCW hDC hOnto hLam Q Lk hPA hDiv hGood hGeo hL3 hFun hMi hKap hDf
  refine _root_.GlobalTheory.Fc.row_rRows_of_parts_alt _root_.GlobalTheory.Fc.DefiniteSideCondition Q Lk ?_ hMi hKap hDf
  refine (((((hPA.and hDiv).and hGood).and hGeo).and hL3).and hFun).imp fun 𝒜 σ hsel H => ?_
  obtain ⟨⟨⟨⟨⟨hpa, hdv⟩, hgd⟩, hall⟩, hl3⟩, hfun⟩ := H
  choose τ hτ using fun {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) x hx i => hall Fm hc x hx i
  let τ' : _root_.GlobalTheory.Fc.CompatibleSelection σ := fun Fm hc x hx i => τ Fm hc x hx i
  have hduty : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm := fun _ Fm hc =>
    let ⟨_, _, h7, _⟩ := hsel Fm hc
    (DQ.familyClass_sevenDuties_and_stableLattices _ Fm h7).1
  have hiota : AtAll _root_.GlobalTheory.Fc.Ind.IotaPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => (hτ Fm hc x hx i).1
  have hppa : AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => hpa Fm hc x hx i
  have hpdiv : AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := fun Fm hc x hx i => _root_.GlobalTheory.Fc.StageZeroRow.p_div_at_piece_of_div3g _ (hdv Fm hc x hx i)
  have hcs : AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') :=
    fun Fm hc x hx i => ⟨(hτ Fm hc x hx i).2.1, (hτ Fm hc x hx i).2.2.1⟩
  have hrows : Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') := _root_.GlobalTheory.T.eventually_pDiv_ties_of_class_sum_pin hDS hHC hCR hCW 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hppa hpdiv hgd hcs
  have hmore : Ind.EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') :=
    evW_of_atAll' fun Fm hc x hx i => (hτ Fm hc x hx i).2.2.2
  refine ⟨τ', ?_, hl3, _root_.GlobalTheory.T.eventually_norm_bound_of_more_points hOnto 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows hmore, _root_.GlobalTheory.T.eventually_L6_bound_of_lamLow hLam 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') hduty hrows, hfun⟩
  exact _root_.GlobalTheory.T.eventually_small_of_seeEx_primitive 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ') (fun Fm hc x hx i =>
      _root_.GlobalTheory.T.indefinite_scale_theta_nonvanishing_alt hDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_root_.GlobalTheory.Fc.summandSelection σ τ' Fm hc x hx i).B.Q (_root_.GlobalTheory.Fc.summandSelection σ τ' Fm hc x hx i).pins
        (hiota Fm hc x hx i)) hppa
end GlobalTheory.Fc.StageZeroRow
end
end
