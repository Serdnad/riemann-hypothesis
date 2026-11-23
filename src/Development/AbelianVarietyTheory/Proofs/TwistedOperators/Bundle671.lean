module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle629
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle642
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle670
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle665
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle911
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle669
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle428
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle015

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeckeGeoRead

theorem theta_trace_read : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ a ∈ Rc, ∀ (C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          (∀ j, j ≠ none → t j = 1) → FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z →
    ∀ (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
      (∀ (h : GA D (Wc D i)), ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h →
      ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom)
        (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
        (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ a, z a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
        Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
            GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
          ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ a, Y.θ (z a)) →
    ∀ γ' ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ' (h * a) →
    ∀ (Wt' : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) (Y' : UnitAt Wt')
      (e : AE D), IsIdemAt e P → ∀ Δ : Finset (WO (Vc D i) (Wc D i)),
        GlobalTheory.HeckeVacuum.IsHalfReps (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (cA D e) a Δ →
    ∀ (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z' : Fin (Vc D i).rank → Fin Wt'.g → ℂ),
        (∀ a, z' a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt' fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
      Formalism.L2.PjFree.toC (t none : CAt σ) ^ (Vc D i).rank *
                (ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h)) *
                ∏ a, (Complex.exp (-(Real.pi / 2 * hermForm Y'.Hm (z' a) (z' a))) * Y'.θ (z' a)) =
        ∑ x ∈ Δ, R.ωP i A.μ0 (1, γ' * h) (heisO R.ψ (Vc D i) (Wc D i) x (R.vacP i))
          (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hS h hx
  intro a ha C z hz hx' t ht hb ph b hph hbON hpin γ' hγ' hfr' Wt' Y' e he Δ hΔ X z' hz'
  have hfin : ∀ x ∈ Δ, x.map (infPart D) = 0 := fun x hx =>
    GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj he.1) (hΔ.1 x hx).2
  have hex : ∀ x : WO (Vc D i) (Wc D i), ∃ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E)
      (w : WO (Vc D i) (Wc D i)), x.map (infPart D) = 0 →
        (w.map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i ∧
          x = actO (Vc D i) (Wc D i) 1 (γ' * h)⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w) := by
    intro x
    by_cases h0 : x.map (infPart D) = 0
    · obtain ⟨ℓ, w, h1, h2, h3⟩ := GlobalTheory.T.exists_rational_approx_finitePoint_vacuumLevel D G Pl0 T0 A T R hLev hFam hThP i (γ' * h) x h0
      exact ⟨ℓ, w, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h' => absurd h' h0⟩
  choose ℓ u hℓu using hex
  rw [GlobalTheory.T.heckePointThetaTrace_eq_phasedTranslateSum D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hS h hx
    a ha C z hz hx' t ht hb ph b hph hbON hpin γ' hγ' hfr' Wt' Y' e he Δ hΔ ℓ u (fun x hx => hℓu x (hfin x hx)) X z' hz']
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [GlobalTheory.T.heisenbergTranslate_vacuum_read_rationalPoints D G Pl0 T0 A T R hLev hFam hThP i (γ' * h) x (hfin x hx) (ℓ x) (u x)
    (hℓu x (hfin x hx)).1 (hℓu x (hfin x hx)).2.1 (hℓu x (hfin x hx)).2.2 X]

end GlobalTheory.HeckeGeoRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
namespace GlobalTheory.ChiGrid.GridData

theorem modul_witness : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), ∀ v ∈ G.pl.S0,
  (∃ m ∈ G.modul, m ∉ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1)) ∧ ∃ m ∈ G.modul, m ∉ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := by
  intro D T L sc G v hv
  classical
  obtain ⟨e, he⟩ := G.pl.w_split v (Finset.mem_insert.2 (G.pl.mem_S0_of_sum_eq.1 hv))
  have hconj : Formalism.DivisionValues.conjPl (G.pl.w v) ≠ G.pl.w v := GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt he

  have eqOf : ∀ (v' : HeightOneSpectrum (𝓞 D.host.F)) (Q : HeightOneSpectrum (𝓞 D.host.E)),
      (G.pl.w v').asIdeal ≤ Q.asIdeal → G.pl.w v' = Q := fun v' Q h =>
    HeightOneSpectrum.ext ((G.pl.w v').isMaximal.eq_of_le Q.isPrime.ne_top h)
  have hmod : G.modul = ∏ v' ∈ G.pl.S0, (G.pl.w v').asIdeal ^ G.pl.depth sc v' := rfl
  refine ⟨?_, ?_⟩
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : G.modul ≤ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1) := fun m hm => hcon m hm
    rw [hmod, ← Finset.mul_prod_erase _ _ hv] at hle
    set J := ∏ v' ∈ G.pl.S0.erase v, (G.pl.w v').asIdeal ^ G.pl.depth sc v'
    have hd : (G.pl.w v).asIdeal ^ G.pl.depth sc v * (G.pl.w v).asIdeal ∣
        (G.pl.w v).asIdeal ^ G.pl.depth sc v * J := by
      rw [← pow_succ]; exact Ideal.dvd_iff_le.2 hle
    have hJ : (G.pl.w v).asIdeal ∣ J :=
      (mul_dvd_mul_iff_left (pow_ne_zero _ (G.pl.w v).ne_bot)).1 hd
    have hJle : J ≤ (G.pl.w v).asIdeal := Ideal.le_of_dvd hJ
    obtain ⟨v', hv'S, hpow⟩ := (Ideal.IsPrime.prod_le (G.pl.w v).isPrime).1 hJle
    have hvv := Finset.mem_erase.1 hv'S
    have := eqOf v' (G.pl.w v) (Ideal.IsPrime.le_of_pow_le hpow)
    apply hvv.1
    rw [← G.pl.under_w hvv.2, ← G.pl.under_w hv, this]
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : G.modul ≤ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := fun m hm => hcon m hm
    rw [hmod] at hle
    obtain ⟨v', hv'S, hpow⟩ := (Ideal.IsPrime.prod_le (Formalism.DivisionValues.conjPl (G.pl.w v)).isPrime).1 hle
    have h1 := eqOf v' _ (Ideal.IsPrime.le_of_pow_le hpow)
    have h2 : v' = v := by
      rw [← G.pl.under_w hv'S, ← G.pl.under_w hv, h1, GlobalTheory.ChainTw.ParInv.under_conjPl]
    subst h2
    exact hconj h1.symm

end GlobalTheory.ChiGrid.GridData
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host


theorem _root_.GlobalTheory.T.weilTraceAddCharAtPlace_mem_subfield_of_roots : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) {W : G.Weil} {w : Pl D.host.E}, (∀ z : ℂ, z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1 → z ∈ F) → HasConductor (psiAt W w) 1 → ∀ (x : Kw w), valuation (Kw w) ((((unifAt w) ^ depthAt G w : (Kw w)ˣ) : Kw w) * x) ≤ 1 → (psiAt W w x : ℂ) ∈ F := by
  first | exact @GlobalTheory.FunObj.psiAt_mem_subfield_of_roots | exact GlobalTheory.FunObj.psiAt_mem_subfield_of_roots | (intros; apply GlobalTheory.FunObj.psiAt_mem_subfield_of_roots <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.T.unitaryInBasis_integral_at_conjugatePlace : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsFrame β Λ → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∀ x ∈ UA D.sp.cm V.gram, ∀ w : Pl D.host.E, inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin V.rank) → inBasis rfl β (Formalism.DivisionValues.conjPl w) x ∈ GlobalTheory.SplitWeil.KO (Kw (Formalism.DivisionValues.conjPl w)) (Fin V.rank) := by
  first | exact @GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO | exact GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO | (intros; apply GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section



namespace GlobalTheory.StdFstFix

variable {D : D7}

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : e • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = x := Matrix.ext fun i j => hx i j
  have e1 : e • actO S T g h x = actO S T g h x := by
    unfold actO
    conv_rhs => rw [← hx']
    rw [Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  exact congrFun (congrFun e1 i) j

theorem actO_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem finCong_of_mem_GinfC {V : HSp D} (N : ℕ) {k : GA D V} (hk : k ∈ GinfC V) : GlobalTheory.Member.FinCong V N k := by
  have h1 : finHom V k = finHom V 1 := by rw [map_one]; exact hk
  have := GlobalTheory.Member.PrincLevel.finCong_one V N
  unfold GlobalTheory.Member.FinCong at this ⊢
  rw [h1]
  exact this

end GlobalTheory.StdFstFix

namespace GlobalTheory.StdFstFix



theorem stdFst_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧ ∀ k ∈ U, k ∈ GfC A →
      (∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k) 1 u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)) ∧
      ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
          (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ 1⁻¹ x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
  intro D T L sc G W i j A A' WW X hX t
  classical
  have hI := hX.is
  have hν : Continuous (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
      (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) := (hI.weil' t).hecT.1
  have he := hI.idem t
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := isSelfDualC_neg' hI.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  obtain ⟨M, hM, hB⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) hsdS.1.fg hsdT.1.fg X.rA.β X.rW.β
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hsdS)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hsdT) X.rA.β X.rW.β
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D _ hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ X.ideal (locPl G) t :=
    ⟨_, Nat.pos_of_ne_zero fun h => GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t (Ideal.absNorm_eq_zero_iff.1 h),
      Ideal.absNorm_mem _⟩
  obtain ⟨c, hc, hcS⟩ : ∃ c : ℕ, 0 < c ∧ ∀ P ∈ locPl G t, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    refine ⟨∏ P ∈ locPl G t, Ideal.absNorm P.asIdeal, Finset.prod_pos fun P _ =>
      Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun P hP => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun P : Pl D.host.E => Ideal.absNorm P.asIdeal) hP
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem P.asIdeal)
  obtain ⟨m, hm⟩ := GlobalTheory.VacTranslate.exists_finCong_mod (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT
    (K * (n₀ * (n * c) * M)) (Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM))

  have key : ∀ g ∈ GfC (GlobalTheory.Grid.neg A), GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial g → ∀ x : WO A WW,
      (IsHalf (X.e t) x ∧ IsIntM (frMapO A WW X.rA.β X.rW.β x) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t) (frMapO A WW X.rA.β X.rW.β x i j)) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
                   (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
                   (actO (GlobalTheory.Grid.neg A) WW g 1 x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
          (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
    intro g hg hgc x hx
    obtain ⟨l, hl', e1⟩ := hm g hg hgc (K • x) (hC x (GlobalTheory.PlaceDatum.infPart_of_half hinf hx.1) hx.2.1)
    have e2 : actO (GlobalTheory.Grid.neg A) WW g 1 x = x + (n₀ * (n * c) * M) • l := by
      have e3 : K • actO (GlobalTheory.Grid.neg A) WW g 1 x = K • (x + (n₀ * (n * c) * M) • l) := by
        rw [← actO_nsmul, e1, smul_add, smul_smul]
      rw [← GlobalTheory.PlaceModel.inv_smul_nsmul (GlobalTheory.Grid.neg A) WW hK (actO (GlobalTheory.Grid.neg A) WW g 1 x), e3,
        GlobalTheory.PlaceModel.inv_smul_nsmul (GlobalTheory.Grid.neg A) WW hK]
    refine StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_shift he hnI hl hcS A WW X.rA.β X.rW.β
      (W := fun i j => (M : Lev.EAf D) * frMapO A WW X.rA.β X.rW.β l i j)
      ⟨fun _ => hx.1, fun _ => isHalf_actO g 1 hx.1⟩ (fun i j => hB l hl' i j) fun i j => ?_
    rw [e2, GlobalTheory.PlaceDatum.frMapO_add]
    push_cast
    ring
  refine ⟨(GlobalTheory.VacFixTarget.congGroup (GlobalTheory.Grid.neg A) m.factorial).comap (GlobalTheory.Grid.ofSgn true A).symm.toMonoidHom,
    (GlobalTheory.Grid.continuous_ofSgn_symm true A).isOpen_preimage _
      (GlobalTheory.VacFixTarget.isOpen_congGroup (GlobalTheory.Grid.neg A) m.factorial_pos), fun k hk => ?_, fun k hkU hkf => ?_⟩
  · show GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial ((GlobalTheory.Grid.ofSgn true A).symm k)
    refine finCong_of_mem_GinfC _ ?_
    rw [GlobalTheory.SgnIdent.mem_GinfC_sgn, MulEquiv.apply_symm_apply]
    exact hk
  · have hκf : (GlobalTheory.Grid.ofSgn true A).symm k ∈ GfC (GlobalTheory.Grid.neg A) := by
      rw [GlobalTheory.SgnIdent.mem_GfC_sgn, MulEquiv.apply_symm_apply]
      exact hkf
    have hκc : GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial ((GlobalTheory.Grid.ofSgn true A).symm k) := hkU
    refine ⟨fun u => ⟨fun hu => ?_, fun hu => ?_⟩, fun x => ?_⟩
    · obtain ⟨l, hl', e⟩ := hm _ hκf hκc u hu
      rw [e]
      exact add_mem hu (nsmul_mem hl' _)
    · obtain ⟨l, hl', e⟩ := hm _ (inv_mem hκf) (GlobalTheory.Member.PrincLevel.finCong_inv hκc) _ hu
      have e' := GlobalTheory.WeilVacMove.actO_inv_actO ((GlobalTheory.Grid.ofSgn true A).symm k) (1 : GA D WW) u
      rw [inv_one] at e'
      rw [e'] at e
      rw [e]
      exact add_mem hu (nsmul_mem hl' _)
    · rw [inv_one]
      set g := ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ with hgdef
      have hg : g ∈ GfC (GlobalTheory.Grid.neg A) := inv_mem hκf
      have hgc : GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial g := GlobalTheory.Member.PrincLevel.finCong_inv hκc
      by_cases hx : IsHalf (X.e t) x ∧ IsIntM (frMapO A WW X.rA.β X.rW.β x) ∧
          ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t) (frMapO A WW X.rA.β X.rW.β x i j)
      · exact key g hg hgc x hx
      · by_cases hx' : IsHalf (X.e t) (actO (GlobalTheory.Grid.neg A) WW g 1 x) ∧
            IsIntM (frMapO A WW X.rA.β X.rW.β (actO (GlobalTheory.Grid.neg A) WW g 1 x)) ∧
            ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t)
              (frMapO A WW X.rA.β X.rW.β (actO (GlobalTheory.Grid.neg A) WW g 1 x) i j)
        · have h2 := key g⁻¹ (inv_mem hg) (GlobalTheory.Member.PrincLevel.finCong_inv hgc) _ hx'
          have e' := GlobalTheory.WeilVacMove.actO_inv_actO g (1 : GA D WW) x
          rw [inv_one] at e'
          rw [e'] at h2
          exact h2.symm
        · unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
          rw [if_neg hx, if_neg hx']

end GlobalTheory.StdFstFix
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixPair

theorem om_pow_eq {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ))
    (g : GA D S × GA D V) (f : WO S V → ℂ) (c : ℂ) (hc : om g f = c • f) : ∀ m : ℕ, om (g ^ m) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    rw [pow_succ, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]



theorem pair_fix_vacO : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S N k → GlobalTheory.Member.FinCong T N k' → om (k, k') v = v := by
  intro D ψ θ S T sS sT ΛS ΛT v χS χT om hvac hsdS hsdT hcS hcT hW
  have hθ : IsInfFam θ := hvac.2.inf
  have hev := (GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).1
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC S, ∀ x' ∈ GfC T, GlobalTheory.Member.FinCong S n.factorial x →
      GlobalTheory.Member.FinCong T n.factorial x' →
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T x x' u ∈
          (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' u hu hu' using hne
    have ht : Filter.Tendsto (fun n => ((k n, k' n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc).prodMk_nhds
        (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk' hkc')
    obtain ⟨n, hn⟩ := (ht.eventually hev).exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S n₁.factorial k →
      GlobalTheory.Member.FinCong T n₁.factorial k' → ∃ c : ℂ, ‖c‖ = 1 ∧ om (k, k') v = c • v := by
    intro k hk k' hk' hc hc'
    have hΛ : ∀ u : WO S T, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
        (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T
        (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        u = actO S T k k' u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO S T k⁻¹ k'⁻¹ u, hn₁ k⁻¹ (inv_mem hk) k'⁻¹ (inv_mem hk')
          (GlobalTheory.Member.PrincLevel.finCong_inv hc) (GlobalTheory.Member.PrincLevel.finCong_inv hc') u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ k'⁻¹ u
        rw [inv_inv, inv_inv] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk k' hk' hc hc' u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ
      sS sS sT sT _ _ _ _ k k'
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hk τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hk' τ, Matrix.one_mul, Matrix.mul_one]) hΛ v hvac
    exact GlobalTheory.VacUnique.vacUniqueO D ψ θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T)
      sS sT (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT ΛS ΛT
      hsdS hsdT v _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun p : GA D S × GA D T => om p v w₀ := hW.om_cont _ hvac.2.theta w₀
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S (n₁.factorial * n.factorial) k →
      GlobalTheory.Member.FinCong T (n₁.factorial * n.factorial) k' → om (k, k') v = v := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om (k n ^ m, k' n ^ m) v = c • v ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (k' n) (hk' n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
        (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc' n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (by rw [← Prod.pow_mk]; exact om_pow_eq om _ v c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have hmem' : ∀ n, k' n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k' n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) from ⟨hk' n, hkc' n⟩) _
    have ht : Filter.Tendsto (fun n => ((k n ^ m n, k' n ^ m n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)).prodMk_nhds
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k' n ^ m n) (fun n => (hmem' n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem' n).2))
    have e1 : om (1 : GA D S × GA D T) v w₀ = v w₀ := by
      rw [map_one]
      rfl
    have h2 : Filter.Tendsto (fun n => om (k n ^ m n, k' n ^ m n) v w₀) Filter.atTop (𝓝 (v w₀)) := by
      have := (hcont.tendsto 1).comp ht
      rw [← e1]
      exact this
    have hpos : 0 < ‖v w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (v w₀)]
  obtain ⟨n, hn⟩ := key
  exact ⟨n₁.factorial * n.factorial, Nat.mul_pos n₁.factorial_pos n.factorial_pos,
    fun k hk k' hk' hc hc' => hn k hk k' hk' hc hc'⟩

end GlobalTheory.VacFixPair
end
end
