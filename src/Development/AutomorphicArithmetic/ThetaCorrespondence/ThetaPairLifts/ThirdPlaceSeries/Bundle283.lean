module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle247
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle076
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle265
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle246
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle241
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle715
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle751
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle738
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle758
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle248
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle279
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle258
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle267
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle261
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle281
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle067
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

@[expose] public section

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho


theorem tripleLayer_inputs_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ (cf : CharFrame (w.D Z)) (Rw : RowSide (w.D Z)) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.D Z).host.E)) → PlE (w.D Z).host) (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ) (_ : SideB (w.D Z) cf Rw low Pq S hL' eig θ) (Sb : Finset (PlE (w.D Z).host)), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (S.A j).IsKsForm) ∧ GlobalTheory.TwInputs.EigTrue (w.D Z) cf Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig ∧ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw ∧ (w.D Z).nexp.sig_all ∧ (∀ a σ v, IsSplitPl (w.D Z).host v → (w.D Z).naut.locW a σ v = Rw.locR σ v) ∧ ∀ a, GlobalTheory.RowTriple.ReadTw (w.D Z) a := by
  intro hP hS hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.GalLoc.galois_side_at_place_alt hP hS hL)
    (_root_.GlobalTheory.HeightCounting.Up.cuspParameter_at_member_alt hP hL)) (_root_.GlobalTheory.RowTriple.Lay.EigCopy.eigenvalues_at_member_tripleLayer_alt hP hS hL))
    fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨⟨G, -, -, -⟩, hpar⟩, heigH⟩ := h
  have hcf : HEq (TC.cf w.I w.l Z) (cfL c.a.nt.L c.a.nt.cf) := heq_cf_of_pack c.a.nt.pack
  obtain ⟨eig, heig⟩ := exists_heq_of_eq (F := fun D : D7 => ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) c.a.nt.eq.symm
    c.a.nt.eig
  obtain ⟨θ, hθ⟩ := exists_heq_of_eq (F := fun D : D7 => ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    c.a.nt.eq.symm c.a.nt.θ
  obtain ⟨Rw, hRw, ⟨Bs⟩, hloc⟩ := _root_.GlobalTheory.RowTriple.Lay.sideB_built_alt hL (w.D Z) c.a.nt.toNBuilt c.a.all.chiD.psi c.a.all.chi.psi (TC.cf w.I w.l Z) hcf
    c.a.Pq c.a.Pq_eq.symm _ c.row.S_eq.symm c.row.hecke.hL c.row.hL_eq.symm
    eig heig θ hθ
  obtain ⟨Sb, hSb, hET⟩ := heigH _ c.row.hecke.hL eig θ c.row.S_eq.symm c.row.hL_eq.symm heig hθ
  obtain ⟨hT, hO⟩ := hET Rw hRw
  have hR : ∀ a, ReadTw (withLoc c.a.nt.L) a := _root_.GlobalTheory.RowTriple.Lay.readTw_withLoc_alt hL _ c.a.nt.toNBuilt
  rw [← c.a.nt.eq] at hR
  exact ⟨TC.cf w.I w.l Z, Rw, c.a.nt.low, c.a.Pq, _, c.row.hecke.hL, eig, θ, Bs, Sb, hSb,
    _root_.GlobalTheory.RowTriple.Lay.isKsForm_of_built_heq hL (w.D Z) c.a.nt.toNBuilt _ c.row.S_eq c.a.ratIn.ks, hT, hO, hpar Rw hRw,
    _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.sig_all G.triple, hloc, hR⟩
end GlobalTheory.RowTriple.Lay
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.compatibleSystem_tripleLayer_inputs_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ (cf : CharFrame (w.D Z)) (Rw : RowSide (w.D Z)) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.D Z).host.E)) → PlE (w.D Z).host) (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ) (_ : SideB (w.D Z) cf Rw low Pq S hL' eig θ) (Sb : Finset (PlE (w.D Z).host)), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (S.A j).IsKsForm) ∧ GlobalTheory.TwInputs.EigTrue (w.D Z) cf Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig ∧ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw ∧ (w.D Z).nexp.sig_all ∧ (∀ a σ v, IsSplitPl (w.D Z).host v → (w.D Z).naut.locW a σ v = Rw.locR σ v) ∧ ∀ a, GlobalTheory.RowTriple.ReadTw (w.D Z) a := by
  first | exact @_root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt | exact _root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt | (intros; apply _root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt <;> assumption)
end
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
theorem GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis ∧ _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt ∧ SerN ∧ ∃ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL := by
  intro hN hX
  have hS := GlobalTheory.SerStdFit.seriesRat_of_seriesRatS
  obtain ⟨hLoc, hA, hCo, ⟨hToric, -, hT, -, -⟩, -⟩ := hN
  obtain ⟨hL, hPr⟩ := _root_.GlobalTheory.Mem.LiteralAutomorphy.localLanglandsGL_and_purity_at_member_alt hLoc hA
  have hRatio := GlobalTheory.ToricRatioBridge.ratioConj_of_toricRatioConjugates
    (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport hT)
  obtain ⟨hkInt, hkTr, hkRead⟩ := GlobalTheory.HeckeMember.heckeInt_transform_readTie
  obtain ⟨hRS, hInt⟩ := GlobalTheory.seriesRatS_and_serInt_of_globalArtin hA.art
  have hSer : SerN := ⟨hS hRS, hInt, hkInt, hkTr, hkRead, hRatio⟩
  have hE : _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis := by
    obtain ⟨hCheb, hDeg1, -, hTC, hCD, hTame, hAdm4, hRay⟩ :=
      GlobalTheory.twist_front_inputs (GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hCo.pt) hCo.lf hCo.lt hCo.lfK hCo.ltK hCo.leK
        hA.art
    exact
      { e1 := hCheb, e2 := hTC, e3 := hCD, e4 := hTame, e5 := hCo.lf, e6 := hCo.lt, e7 := hCo.le, e8 := hCo.gf,
        e9 := hCo.ge, e10 := hCo.uo, e11 := hAdm4, e12 := hCo.gw, e13 := hRay, e14 := hDeg1, e15 := hToric,
        e16 := hSer.rat, e17 := hSer.int, e18 := hSer.hkInt, e19 := hSer.hkTr, e20 := hSer.hkRead,
        e21 := hPr.what₂.fin, e22 := hPr.what₂.gal, e23 := hPr.what₂.berger,
        e24 := _root_.GlobalTheory.GalOfCusp.local_global_above_ell_of_cusp_alt hPr.what₂,
        e25 := GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hCo.bk hCo.ltK hCo.leK }
  refine ⟨hE, hPr, hSer, hL, ?_⟩
  exact
    { pr := hPr
      ser := hSer
      arch := _root_.GlobalTheory.ArchFromLit.archimedean_local_langlands_compatibility_alt hLoc hA hL
      par := _root_.GlobalTheory.HeightCounting.Up.conjDualParam_stable_of_prime_not_dividing_level_alt
        hPr (_root_.GlobalTheory.MtInMain.prN_sMt_alt_alt hPr) hL
      pt := _root_.GlobalTheory.HeightCounting.Up.ptSt_of_inputs_geometric_compat hPr hX hL
      parMem := _root_.GlobalTheory.HeightCounting.Up.cuspParameter_at_member_alt hPr hL }
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy

theorem _root_.GlobalTheory.T.hyps_e_third_layer_ser_n_of_geometric_galois : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis ∧ _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt ∧ SerN ∧ ∃ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL :=
  @_root_.GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat
end
end
end
