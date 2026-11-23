module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle345
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle654
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle447
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEOffS0ColumnPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle431
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle655
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle657
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle502
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle628
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle526
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle656
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

theorem isThetaFunO_small_of_isMatched {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hM : IsMatched B t ρ i j Θ Θ') :
    ∀ d ∈ Θ'.support, IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hM
  intro d hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hd)
  obtain ⟨d₀, hd₀, hd₁⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hP)
  obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hd₁)
  obtain ⟨hA, hB⟩ := hloc d₀ hd₀
  have hv₁ := (ρ.vT_is t i j i.2.le j.2).2.theta
  have hv₂ := (ρ.vX_is i j i.2 j.2.le).2.theta
  have hf₁ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hA.2 hv₁
  have hf₂ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hB.2 hv₂
  exact ⟨GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ P.1.2 hf₁,
    GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ P.2 hf₂⟩

theorem kerSmall_eq_thetaKO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωB : GlobalTheory.Grid.WRep (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωB →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerSmall W Θ' g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωB u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumB W Θ') := by
  intro D T L sc G μ₀ hL W t i j ωB hωB B ρ Θ Θ' hM g g₁ u
  have hth := isThetaFunO_small_of_isMatched W B ρ t i j Θ Θ' hM
  have hω := (GlobalTheory.Grid.isWeil_false W.ψ _ _ _ _ ωB).mp hωB
  have key : ∀ d ∈ Θ'.support, W.kerA (.down t i j) d.1.2 g u * W.kerA (.right i j) d.2 u g₁ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
        ωB (u, GlobalTheory.SquareComm.blk _ _ (g, g₁))
          (box2 (S := G.V (.grid i j)) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j)) d.1.2
            (fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y))) 0 := by
    intro d hd
    have h := (GlobalTheory.SeesawSmall.seesaw_small hL W t i.2 j.2 ωB hω d.1.2 d.2 (hth d hd).1 (hth d hd).2).2 g u g₁
    have hadj : GlobalTheory.SeesawSmall.adjFn (G.V (.grid i j)) (G.V (.grid (i + 1) j)) d.2 =
        fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y) := by
      funext y
      exact congrArg d.2 (GlobalTheory.AdjSwap.dagger_eq_adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y)
    rw [hadj] at h
    exact h

  simp only [kerSmall, GlobalTheory.SquareDict.datumB, thetaKO, Finsupp.sum, map_sum, Finset.sum_apply, map_smul,
  Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [key d hd]
  ring

end GlobalTheory.SquareDict
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.routeDatum_mem_algebraicVectors_grid_frames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (A : Fr (G.V (.grid (↑i + 1) (↑j + 1)))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
      GlobalTheory.SquareDict.datumA W Θ ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) := by
  first | exact @GlobalTheory.SquareAlg.datumA_mem_algF | exact GlobalTheory.SquareAlg.datumA_mem_algF | (intros; apply GlobalTheory.SquareAlg.datumA_mem_algF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.smallRouteDatum_mem_algebraicVectors_grid_frames : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (A₁ : Fr (G.V (.grid ↑i ↑j))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A₁ → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
      GlobalTheory.SquareDict.datumB W Θ' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) := by
  first | exact @GlobalTheory.SquareDict.datumB_mem_algF | exact GlobalTheory.SquareDict.datumB_mem_algF | (intros; apply GlobalTheory.SquareDict.datumB_mem_algF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

theorem _root_.GlobalTheory.T.detIdele_conjugatedTopPoint_eq_prod_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (e : AE D),
    IsIdemSum e (locPl G t) →
    detAt e (G.V (.top (j + 1))) (conjPt S j k) =
      ∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w)) := by
  first | exact @GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod | exact GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod | (intros; apply GlobalTheory.TopLevelInv.detAt_conjPt_eq_prod <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

theorem _root_.GlobalTheory.T.psiE_off_S0_column_pair : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  first | exact @GlobalTheory.CharXFB.OffPl.psi_pair_trivial_off | exact GlobalTheory.CharXFB.OffPl.psi_pair_trivial_off | (intros; apply GlobalTheory.CharXFB.OffPl.psi_pair_trivial_off <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.PairAt

variable {D : D7}
open GlobalTheory.SeeSaw (idV FI conjFI)

theorem conjFI_modul {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) = ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) := by
  have h := congrArg (conjFI D) (GlobalTheory.CharXFB.OffPl.conjFI_modulBar P sc)
  rw [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  exact h.symm

private theorem mul_mem_idAt' {D : D7} {v : GlobalTheory.FinPl.Pl D} {a : AE D} (b : AE D) (ha : a ∈ idAt D (· = v)) :
    a * b ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPlLoc.mem_idAt_iff] at ha ⊢
  rw [← mul_assoc, ha]

theorem pair_mem_idV_of_maps {S T : HSp D} {ΛS : Lat S} {ΛT : Lat T} (sdT : IsSelfDualC T ΛT) {u : WO S T}
    {v : GlobalTheory.FinPl.Pl D} {yS : Fin S.rank → AE D} {yT : Fin T.rank → AE D} {𝔟S 𝔟T 𝔐 : FI D} (h𝔟S : 𝔟S ≠ 0)
    (h𝔟T : 𝔟T ≠ 0) (h𝔐 : 𝔐 ≠ 0)
    (hu : ∀ y ∈ latV S ΛS (· = v), ∀ s ∈ idV 𝔐 v, s • (u *ᵥ y) ∈ latV T ΛT (· = v))
    (hyS : ∀ t ∈ idV 𝔟S v, t • yS ∈ latV S ΛS (· = v)) (hyT : ∀ r ∈ idV 𝔟T v, r • yT ∈ latV T ΛT (· = v)) :
    GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈
      idV (1 * 𝔟T⁻¹ * (conjFI D 𝔐)⁻¹ * (conjFI D 𝔟S)⁻¹) v := by
  have hx : GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈ idAt D (· = v) :=
    mul_mem_idAt' _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have cS : conjFI D 𝔟S ≠ 0 := fun h => h𝔟S ((conjFI D).injective (by rw [h, map_zero]))
  have cM : conjFI D 𝔐 ≠ 0 := fun h => h𝔐 ((conjFI D).injective (by rw [h, map_zero]))
  have n1 : (1 : FI D) * 𝔟T⁻¹ ≠ 0 := mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)
  have n2 : (1 : FI D) * 𝔟T⁻¹ * (conjFI D 𝔐)⁻¹ ≠ 0 := mul_ne_zero n1 (inv_ne_zero cM)
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v (conjFI D 𝔟S) _ cS n2 _ hx).1 ?_
  intro t ht
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v (conjFI D 𝔐) _ cM n1 _ (mul_mem_idAt' t hx)).1 ?_
  intro m hm
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v 𝔟T 1 h𝔟T one_ne_zero _
    (mul_mem_idAt' m (mul_mem_idAt' t hx))).1 ?_
  intro r hr
  rw [GlobalTheory.SeeSaw.idV_one_eq_intAt]
  have ht' : cA D t ∈ idV 𝔟S v := by
    have h := GlobalTheory.SeeSaw.cA_mem_idV ht
    rwa [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  have hm' : cA D m ∈ idV 𝔐 v := by
    have h := GlobalTheory.SeeSaw.cA_mem_idV hm
    rwa [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  have hz := GlobalTheory.CharXFB.OffPl.hA_mem_intAt sdT (hyT r hr) (hu _ (hyS _ ht') _ hm')
  have hprod := GlobalTheory.IdealQuot.intAt_mul (GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)) hz
  have e : GlobalTheory.FinPlLoc.idem D (· = v) * hA T (r • yT) (cA D m • (u *ᵥ (cA D t • yS))) =
      GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) * t * m * r := by
    rw [GlobalTheory.CharXFB.OffPl.hA_smul_left, GlobalTheory.CharXFB.OffPl.hA_smul_right, Matrix.mulVec_smul,
      GlobalTheory.CharXFB.OffPl.hA_smul_right, GlobalTheory.SeeSaw.cA_cA, GlobalTheory.SeeSaw.cA_cA]
    ring
  rw [← e]
  exact hprod

private theorem stairId_ne_zero_twisted_operators {D : D7} {A B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hA : A ≠ 0) (hB : B ≠ 0)
    (c : ℕ) (p : Fin c) : GlobalTheory.ChiGrid.stairId A B c p ≠ 0 := by
  rw [GlobalTheory.ChiGrid.stairId]
  exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

theorem pair_mem_AA_AAbar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))) (v : GlobalTheory.FinPl.Pl D), (∀ y ∈ latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) → ∀ p : Fin (σ + 1), GlobalTheory.FinPlLoc.idem D (· = v) * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈ GlobalTheory.SeeSaw.idV (D.host.AA * D.host.AAbar) v := by
  intro D T L sc G σ h h' u v hu p
  have hAA : (D.host.AA : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    first
      | exact (GlobalTheory.SeeSaw.ChainIdeals.host_ne_zero D).2.1
      | exact Formalism.IndefR.Fin.PDA.AA_ne_zero (D := D)
      | exact GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign.AA_ne_zero D
      | exact GlobalTheory.SeeSaw.LatAt.AA_ne_zero (D := D)
  have hAbar : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := fun e =>
    hAA ((conjFI D).injective (by rw [GlobalTheory.SeeSaw.conjFI_AA, e, map_zero]))
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := fun e =>
    hm ((conjFI D).injective (by rw [conjFI_modul G.pl sc, e, map_zero]))
  have hstA : G.pl.stA sc ≠ 0 := by
    rw [GlobalTheory.ChiGrid.Places.stA]
    exact mul_ne_zero hAA (inv_ne_zero hmB)
  have hstAbar : G.pl.stAbar sc ≠ 0 := by
    rw [GlobalTheory.ChiGrid.Places.stAbar]
    exact mul_ne_zero hAbar (inv_ne_zero hm)
  have sdT : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  have hyT : ∀ r ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.ChiGrid.stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)
      (Fin.castLE (by omega) p)) v,
      r • ratV (fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) ∈
        latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro r hr
    have hl := GlobalTheory.CharXFB.OffPl.scaled_auxiliary_vector_mem_lattice_completion (G.colDec (2 * σ + 2) (by omega) h') (G.sp.P (2 * σ + 2)).lat _ _ v hr
    rw [show G.Λ (.grid (2 * σ + 2) 0) = _ from G.sp.colLat (2 * σ + 2) (by omega) h']
    exact hl
  have hyS : ∀ t ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.ChiGrid.stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) v,
      t • ratV (fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈
        latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v) := by
    intro t ht
    have hl := GlobalTheory.CharXFB.OffPl.scaled_auxiliary_vector_mem_lattice_completion (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega))
      (G.sp.P (2 * (σ + 1) + 1)).lat _ _ v ht
    rw [show G.Λ (.grid (2 * σ + 2 + 1) 0) = _ from G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)]
    exact hl
  have key := pair_mem_idV_of_maps (ΛS := G.Λ (.grid (2 * σ + 2 + 1) 0)) sdT (u := u) (v := v)
    (stairId_ne_zero_twisted_operators hstA hstAbar _ _) (stairId_ne_zero_twisted_operators hstA hstAbar _ _)
    (mul_ne_zero (inv_ne_zero hAA) (inv_ne_zero hm)) hu hyS hyT
  have hcM : conjFI D (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) =
      D.host.AAbar⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    rw [map_mul, map_inv₀, map_inv₀, GlobalTheory.SeeSaw.conjFI_AA, conjFI_modul]
  have hst := GlobalTheory.CharXFB.OffPl.stair_prod hstA hstAbar (GlobalTheory.CharXFB.OffPl.conjFI_stA G.pl sc)
    (GlobalTheory.CharXFB.OffPl.conjFI_stAbar G.pl sc) σ p (by omega) (by omega)
  have hid : ∀ X Y : GlobalTheory.SeeSaw.FI D, 1 * X⁻¹ * (D.host.AAbar⁻¹)⁻¹ * Y⁻¹ = D.host.AAbar * G.pl.stA sc →
      1 * X⁻¹ * (D.host.AAbar⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹)⁻¹ * Y⁻¹ =
        D.host.AA * D.host.AAbar := by
    intro X Y hXY
    rw [mul_inv, inv_inv (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D))]
    calc 1 * X⁻¹ * ((D.host.AAbar⁻¹)⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) * Y⁻¹
        = (1 * X⁻¹ * (D.host.AAbar⁻¹)⁻¹ * Y⁻¹) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
          ring
      _ = D.host.AAbar * (D.host.AA * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) *
          ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
          rw [hXY, GlobalTheory.ChiGrid.Places.stA]
      _ = D.host.AA * D.host.AAbar * (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ *
          ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) := by ring
      _ = D.host.AA * D.host.AAbar := by rw [inv_mul_cancel₀ hmB, mul_one]
  rw [hcM] at key
  rw [← hid _ _ hst]
  exact key

end GlobalTheory.CharXFB.PairAt
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
open GlobalTheory.XCharBF

theorem _root_.GlobalTheory.T.complementary_ideal_membership_criterion : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) (c : AE D), c ∈ complId (D.host.AA * G.pl.stAbar sc) → (∀ e, IsIdemSum e G.pl.W0 → e * c ∈ complId D.host.AAbar) → c ∈ complId (D.host.AA * D.host.AAbar) := by
  first | exact @GlobalTheory.XCharComb.mem_complId_AA_AAbar | exact GlobalTheory.XCharComb.mem_complId_AA_AAbar | (intros; apply GlobalTheory.XCharComb.mem_complId_AA_AAbar <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Outer

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem outer_move (M : Vol G) {K : Subgroup (GL (Fin (G.V (.grid D.R.m D.R.m)).rank) (Lev.EAf D))}
    (hK : M.IsAt (.grid D.R.m D.R.m) K) (k : GA D (G.V (.grid D.R.m D.R.m))) (k' : GA D (G.V (.top D.R.m)))
    (hk : MeasurePreserving (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k) (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)))
    (hk' : Measurable (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k⁻¹))
    (ι : GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top D.R.m)))
    (hι : ∀ h, ι h * k' = ι (h * k))
    (P P' : Fn G (.top D.R.m)) (S S' : Fn G (.grid D.R.m D.R.m))
    (hP : ∀ h, P (h * k') = P' h) (hS : ∀ h, S (h * k) = S' h)
    (hPl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, P (ι (γ * h)) = P (ι h))
    (hSl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, S (γ * h) = S h) :
    ∫ h in M.fd (.grid D.R.m D.R.m), P' (ι h) * S' h ∂M.ν (.grid D.R.m D.R.m) =
      ∫ h in M.fd (.grid D.R.m D.R.m), P (ι h) * S h ∂M.ν (.grid D.R.m D.R.m) := by
  rw [← setIntegral_fd_mul_right M hK k hk hk' (fun h => P (ι h) * S h) ?_]
  · congr 1
    funext h
    rw [← hP, ← hS, hι]
  · intro γ hγ h
    simp only [hPl γ hγ h, hSl γ hγ h]

end Outer

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem genPer_move (ch : Choice R)
    {μ0 : T} (hL : R.toLevCh.Is μ0) (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)
    (hMr : ∀ j : Fin D.R.m, ∃ K, M.IsAt (.top j) K) (hMc : ∀ i : Fin (D.R.m + 1), ∃ K, M.IsAt (.grid i D.R.m) K)
    (hd1 : ∀ j, ch.S.toGridChoice.Z.HasVec (d.1 j)) (hd2 : ∀ i, ch.S.toGridChoice.Z.HasVec (d.2 i))
    (hξ : ∀ ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g)
    (hη : ∀ η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (g : Gc D.what₂.Tau (rowSizes D)) (Q Q' : PolCol ch.G × PolRow ch.G)
    (h1 : ∀ j : Fin D.R.m, ch.W.om (.top t j) (ch.G.toPair (.top t j) (ptTop ch.W g j) (ptTop ch.W g (j + 1)))
        (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j)) =
      ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q'.1 j))
    (h2 : ∀ i : Fin D.R.m, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ptGrid ch.W g i) (ptGrid ch.W g (i + 1)))
        (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) =
      ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q'.2 i))
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) :
    genPer ch t a M d y Q' (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹)
      (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      genPer ch t a M d y Q ξ η := by

  have hfc : ∀ (P : PolCol ch.G) (j : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.top t j)) (ch.G.pT (.top t j))
      (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (P j)) := fun P j =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.top t j) j.2 (d.1 j) (hd1 j)).1 (P j)
  have hfr : ∀ (P : PolRow ch.G) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i D.R.m)) (ch.G.pT (.chi i D.R.m))
      (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (P i)) := fun P i =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.chi i D.R.m) ⟨i.2, rfl⟩ (d.2 i) (hd2 i)).1 (P i)

  have hφ' : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a) = fun x => (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (x * ptTop ch.W g 0) :=
    funext (pairVec_mul_real (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (ptTop_mem ch.W g 0))
  have hF' : formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      fun x => (formGen ch t y η) (x * ptGrid ch.W g 0) :=
    funext (formGen_mul_real ch t y η (ptGrid_mem ch.W g 0))

  have hcol := pathLift_column_translate ch.W M t (ptTop ch.W g) D.R.m le_rfl
    (fun j hj => by
      obtain ⟨K, hK⟩ := hMr ⟨j, hj⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptTop_lt ch.W g hj]
      exact kappa_fst_move ch.W g ⟨j, hj⟩ hK)
    _ _ (hfc Q.1) h1 (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ)
  have hrow := pathLift_row_translate ch.W M (ptGrid ch.W g) D.R.m le_rfl
    (fun i hi => by
      obtain ⟨K, hK⟩ := hMc ⟨i, by omega⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptGrid_le ch.W g (by omega : i < D.R.m + 1)]
      exact kappa_snd_move ch.W g ⟨i, by omega⟩ hK)
    _ _ (hfr Q.2) h2 (formGen ch t y η) (hη η)

  have htop : ∀ h, stabilizerEmbedding ch.G.sp.topDec h * ptTop ch.W g D.R.m = stabilizerEmbedding ch.G.sp.topDec (h * ptGrid ch.W g D.R.m) := by
    intro h
    rw [ptTop_m, kappaTop_apply, ptGrid_le ch.W g (Nat.lt_succ_self D.R.m), GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
    rfl

  obtain ⟨K, hK⟩ : ∃ K, M.IsAt (.grid D.R.m D.R.m) K := hMc (Fin.last D.R.m)
  have hmv : MeasurePreserving (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * ptGrid ch.W g D.R.m)
        (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)) ∧
      Measurable (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * (ptGrid ch.W g D.R.m)⁻¹) := by
    rw [ptGrid_le ch.W g (Nat.lt_succ_self D.R.m)]
    exact kappa_snd_move ch.W g (Fin.last D.R.m) hK
  show defPer t ch.S.toGridChoice M Q' d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a))
      (formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹)) =
    defPer t ch.S.toGridChoice M Q d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (formGen ch t y η)
  rw [hφ', hF']
  have hPl := fun (γ : GA D (ch.G.V (.grid D.R.m D.R.m))) (hγ : γ ∈ GQ (ch.G.V (.grid D.R.m D.R.m)))
      (h : GA D (ch.G.V (.grid D.R.m D.R.m))) =>
    (congrArg _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul ch.G.sp.topDec γ h)).trans
      (pathLift_column_leftInvariant ch.W M t D.R.m le_rfl _ (hfc Q.1) (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ) _
        (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational ch.G.sp.topDec γ hγ) (stabilizerEmbedding ch.G.sp.topDec h))
  have hSl := pathLift_row_leftInvariant ch.W M D.R.m le_rfl _ (hfr Q.2) (formGen ch t y η) (hη η)
  exact outer_move M hK (ptGrid ch.W g D.R.m) (ptTop ch.W g D.R.m) hmv.1 hmv.2 (stabilizerEmbedding ch.G.sp.topDec) htop _ _ _ _
    hcol hrow hPl hSl

end Main

end GlobalTheory.RowReal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.givenStageFunction_rowArrow_eq_halfExtension : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (Φ : G.Datum) {e e₀ : AE D}, IsIdemSum e (locPl G t) → IsIdemSum e₀ G.pl.W0 → (∀ w ∈ L.Q t, w ∉ G.pl.W0 → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (i : Fin D.R.m), GlobalTheory.FlipStart.givenFn B t Φ e (.right i 0) = GlobalTheory.CosetRow.extFn e₀ (e - e₀) (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _) (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) (cosInd e₀ (Φ i)) := by
  first | exact @GlobalTheory.CosetRow.givenFn_right_eq_extFn | exact GlobalTheory.CosetRow.givenFn_right_eq_extFn | (intros; apply GlobalTheory.CosetRow.givenFn_right_eq_extFn <;> assumption)
end
