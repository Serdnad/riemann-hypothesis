module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle412
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle283
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle449
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle467
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle621
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle611
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle630
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle465
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLine
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle419
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.jacobiActionFunction_isUnfolding_noCompactCore : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) := by
  first | exact @GlobalTheory.th_isTh_lev | exact GlobalTheory.th_isTh_lev | (intros; apply GlobalTheory.th_isTh_lev <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PlaceLevelCosets

variable {D : D7}

theorem mem_GinfC_of_off (V : HSp D) (S : GlobalTheory.FinPl.Pl D → Prop) {g : GA D V} (h1 : g ∈ grpOff V S)
    (h2 : g ∈ grpOff V (fun v => ¬ S v)) : g ∈ GinfC V := by
  have h3 : g ∈ grpOff V (fun _ => True) := by
    refine GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.2 fun i j => ?_
    have a := GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.1 h1 i j
    have b := GlobalTheory.FinPl.PlacesAdeles.mem_congGrp.1 h2 i j
    simp only [GlobalTheory.FinPl.idOff, Submodule.mem_iInf] at a b ⊢
    intro w
    by_cases hw : S w.1
    · exact a ⟨w.1, hw⟩
    · exact b ⟨w.1, hw⟩
  exact GlobalTheory.FinPl.OffInh.mem_GinfC_of_all (fun _ => trivial) h3




theorem mem_lev_of_inK {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node)
    (hΛ : Submodule.IsFullLattice D.host.E (G.Λ X)) {κ : GA D (G.V X)}
    (hκ : InK (G.V X) (G.Λ X) (fun v => v ∉ G.pl.S0) κ) : κ ∈ lev G X := by
  classical
  have hfg : (G.Λ X).FG := Submodule.IsLattice.fg D.host.E (G.Λ X)
  obtain ⟨hGf, hpr⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff (G.V X) _ κ).1 hκ.1
  obtain ⟨β, hβ⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E (G.V X).rank (G.Λ X) hΛ
  have hS : Lev.finE (G.V X) κ ∈ Formalism.L2.DIV.St β :=
    (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (G.V X) β (G.Λ X) hβ κ).2
      (GlobalTheory.AdelicU.mem_levelOpen.1 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK (G.V X) (G.Λ X) hfg _ hκ))
  refine ⟨hGf, ?_⟩
  show Lev.finE (G.V X) κ ∈ congLev D.sp.cm (G.V X).gram (G.Λ X) G.modul
  rw [← GlobalTheory.ColMeas.princ_eq_congLev D.sp.cm (G.V X).gram hβ G.modul]
  refine ⟨GlobalTheory.LevSplit.finE_mem_UA (G.V X) κ, ?_⟩
  obtain ⟨y, hy⟩ := hS
  refine GlobalTheory.Grid.mem_princGL.2 ⟨y, hy, fun a b => ?_⟩

  have hE : ∀ c d, ((Lev.finE (G.V X) κ).1 - 1) c d = toEAf D ((Formalism.L2.Theta.mt (G.V X) κ - 1) c d) := by
    intro c d
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
    congr 1
    by_cases h : c = d
    · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero]
  have hW : ∀ w ∈ G.pl.W0, ((Lev.finE (G.V X) κ).1 - 1).map (GlobalTheory.StdFrames.cpt w) = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    have h1 := (GlobalTheory.FinPl.KOpen.proj_eq_one_iff (G.V X) v κ).1 (hpr v (not_not.2 hv))
    refine Matrix.ext fun c d => ?_
    rw [Matrix.map_apply, hE, Matrix.zero_apply]
    exact (GlobalTheory.LocHat.prV_eq_zero_iff_cpt v _).1 (GlobalTheory.StabOff.prV_toEAf_eq_zero v _ (h1 c d)) _ (G.pl.under_w hv)
  have hconj : (Lev.finE (G.V X) κ).1 = β.1 * (Formalism.L2.DIV.intGL D.host.F D.host.E _ y).1 * (β⁻¹).1 := by
    rw [← hy]; rfl
  have hY := GlobalTheory.LevRedTriv.conj_sub_one β _ _ hconj
  refine (GlobalTheory.FunObj.Comparison₂.mem_idS_modul G _).2 fun w hw => ?_
  have hM : ((Formalism.L2.DIV.intGL D.host.F D.host.E _ y).1 - 1).map (GlobalTheory.StdFrames.cpt w) = 0 := by
    rw [hY, Matrix.map_mul, Matrix.map_mul, hW w hw, Matrix.mul_zero, Matrix.zero_mul]
  have e0 : GlobalTheory.StdFrames.cpt w (((y.1 - 1) a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = 0 := by
    rw [GlobalTheory.LevRedTriv.coe_sub_one_apply]
    exact congrFun (congrFun hM a) b
  rw [e0, map_zero]
  exact zero_le'

theorem idAt_le_idOff_compl (P : GlobalTheory.FinPl.Pl D → Prop) : idAt D (fun v => ¬ P v) ≤ idOff D P := by
  intro a ha
  simp only [GlobalTheory.FinPl.idAt, GlobalTheory.FinPl.idOff, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, not_not.2 w.2⟩

theorem idAt_le_idOff_compl' (P : GlobalTheory.FinPl.Pl D → Prop) : idAt D P ≤ idOff D (fun v => ¬ P v) := by
  intro a ha
  simp only [GlobalTheory.FinPl.idAt, GlobalTheory.FinPl.idOff, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, w.2⟩

end GlobalTheory.PlaceLevelCosets


open GlobalTheory.PlaceLevelCosets GlobalTheory.FinPl.PlacesAdeles in
theorem GlobalTheory.PlaceLevelCosets.levCoset_of_places : All fun {D} _ _ _ {G} _ _ => ∀ i, i ≤ D.R.m → (lev G (.grid i 0) ≤ GfC _ ∧ IsCompact (lev G (.grid i 0) : Set (GA D (G.V (.grid i 0)))) ∧ IsOpen (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0))))) ∧ ∀ (R : Subgroup (GA D (G.V (.grid i 0)))) h, (∀ v ∉ G.pl.S0, ∀ h₁ ∈ grpAt _ (· = v), ∀ h₂ ∈ grpOff _ (· = v), h = h₁ * h₂ → CosetAt _ R (G.Λ (.grid i 0)) v h₁) → (∀ h₁ ∈ grpAt _ (fun v => v ∈ G.pl.S0), ∀ h₂ ∈ grpOff _ (fun v => v ∈ G.pl.S0), h = h₁ * h₂ → ∃ r ∈ R, r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid i 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ h₁ = r * k) → ∃ r ∈ R, ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid i 0), h = r * a * k := by
  intro D _ T L μ0 hL sc G W M _ i hi
  have hV := node_isV G hL (X := .grid i 0) ⟨hi, Nat.zero_le _⟩
  have hlat : Submodule.IsFullLattice D.host.E (G.Λ (.grid i 0)) :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd
  have hoc := congLev_open_compact (G.V (.grid i 0)) hlat (G.pl.modul_ne_bot sc)
  refine ⟨⟨inf_le_left, hoc.2, ?_⟩, ?_⟩
  · have e : (((lev G (.grid i 0)).subgroupOf (GfC _) : Subgroup (GfC (G.V (.grid i 0)))) : Set (GfC (G.V (.grid i 0)))) =
        Subtype.val ⁻¹' ((((congLev D.sp.cm (G.V (.grid i 0)).gram (G.Λ (.grid i 0)) G.modul).comap
          (Lev.finE (G.V (.grid i 0))) : Subgroup (GA D (G.V (.grid i 0)))) : Set (GA D (G.V (.grid i 0))))) := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hoc.1.preimage continuous_subtype_val
  · intro R h hA hB
    have hsd : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := hV.sd
    have hoff : ∀ v, (fun v => v ∉ G.pl.S0) v → ∃ hv ∈ grpAt (G.V (.grid i 0)) (· = v), ∃ h' ∈ grpOff (G.V (.grid i 0)) (· = v),
        h = hv * h' ∧ ∃ r ∈ R, r ∈ grpAt (G.V (.grid i 0)) (· = v) ∧ ∃ κ, InK (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) κ ∧
          hv = r * κ := by
      intro v hv
      obtain ⟨x, hx, y, hy, e⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 (G.V (.grid i 0))).1 h
      exact ⟨x, hx, y, hy, e, hA v hv x hx y hy e⟩
    obtain ⟨r₁, hr₁, hr₁P, g, hg, κ₁, hκ₁, e₁⟩ :=
      GlobalTheory.FinPl.placesToAdeles_all D (G.V (.grid i 0)) (G.Λ (.grid i 0)) (fun v => v ∉ G.pl.S0) hsd R h hoff
    obtain ⟨hdec, hcomm, -, -⟩ := (GlobalTheory.FinPl.localComponents D (fun v => v ∈ G.pl.S0)).2 (G.V (.grid i 0))
    obtain ⟨g₁, hg₁, g₂, hg₂, eg⟩ := hdec g
    have hin : ∀ x ∈ grpAt (G.V (.grid i 0)) (fun v => v ∉ G.pl.S0), x ∈ grpOff (G.V (.grid i 0)) (fun v => v ∈ G.pl.S0) :=
      fun x hx => congGrp_mono (idAt_le_idOff_compl (fun v => v ∈ G.pl.S0)) hx
    have hr₁off := hin r₁ hr₁P
    have hκ₁off := hin κ₁ hκ₁.1
    have hg₁off : g₁ ∈ grpOff (G.V (.grid i 0)) (fun v => ¬ v ∈ G.pl.S0) :=
      congGrp_mono (idAt_le_idOff_compl' (fun v => v ∈ G.pl.S0)) hg₁
    have hg₂off : g₂ ∈ grpOff (G.V (.grid i 0)) (fun v => ¬ v ∈ G.pl.S0) := by
      have : g₂ = g₁⁻¹ * g := by rw [eg]; group
      rw [this]
      exact mul_mem (inv_mem hg₁off) hg
    have c1 : r₁ * g₁ = g₁ * r₁ := (hcomm g₁ hg₁ r₁ hr₁off).symm
    have eh : h = g₁ * (r₁ * g₂ * κ₁) := by
      rw [e₁, eg, ← mul_assoc, ← mul_assoc, ← mul_assoc, c1]
    obtain ⟨r₀, hr₀, -, k₀, hk₀, hk₀S, ek⟩ := hB g₁ hg₁ _ (mul_mem (mul_mem hr₁off hg₂) hκ₁off) eh
    have c2 : k₀ * r₁ = r₁ * k₀ := hcomm k₀ hk₀S r₁ hr₁off
    have c3 : k₀ * g₂ = g₂ * k₀ := hcomm k₀ hk₀S g₂ hg₂
    refine ⟨r₀ * r₁, R.mul_mem hr₀ hr₁, g₂, mem_GinfC_of_off _ _ hg₂ hg₂off, k₀ * κ₁,
      mul_mem hk₀ (mem_lev_of_inK G _ hlat hκ₁), ?_⟩
    calc h = g₁ * (r₁ * g₂ * κ₁) := eh
      _ = r₀ * (k₀ * r₁) * g₂ * κ₁ := by rw [ek]; simp only [mul_assoc]
      _ = r₀ * r₁ * (k₀ * g₂) * κ₁ := by rw [c2]; simp only [mul_assoc]
      _ = r₀ * r₁ * g₂ * (k₀ * κ₁) := by rw [c3]; simp only [mul_assoc]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff Pointwise
open GlobalTheory.AscFin


open GlobalTheory.StairLine GlobalTheory.SeeSaw in
theorem GlobalTheory.AscFin.primAt_jac_std : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, PrimAt W.ψ (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  intro D hOff T L μ0 hL sc G W M hM F hF ρ h v hv
  obtain ⟨hc, he, -⟩ := hF.hJ ρ h
  have hlat := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  let 𝔟 : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)
  have hline : ∀ p : Fin ρ, ∀ a, GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔
      a ∈ idV (𝔟 p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := hlat
    rw [e2]
    exact line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega)
      (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v a
  intro i j hij s hs
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    unfold Places.modulBar
    intro h0
    apply G.pl.modul_ne_bot sc
    have h1 := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using h1
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hB : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hne : ∀ p, 𝔟 p ≠ 0 := fun p => mul_ne_zero
    (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)))
    (by
      unfold stairId
      refine mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)))
  have key : (∀ a : AE D, GlobalTheory.FinPl.colMul (F.dJ ρ h).jX j a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) →
      GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i (s * a) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v)) ↔
      ∀ a ∈ idV (𝔟 j) v, s * a ∈ idV (𝔟 i) v :=
    ⟨fun H a ha => (hline i _).1 (H a ((hline j a).2 ha)), fun H a hc => (hline i _).2 (H a ((hline j a).1 hc))⟩
  rw [key, GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v _ _ (hne j) (hne i) s hs, ← DiffDual.idV_dI_iff D W.ψ W.ψ_std v s hs]
  have hid : 𝔟 i * (𝔟 j)⁻¹ * (((G.pl.modul sc * G.pl.modulBar sc : Ideal (𝓞 D.host.E))) : FI D) = dI D := by
    have hst := stairId_succ (𝔞 := G.pl.stA sc) (c := 2 * ρ + 1 - 1) hB (Fin.castLE (by omega) i) (Fin.castLE (by omega) j)
      (by simp only [Fin.coe_castLE]; exact hij)
    have hSj : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j) ≠ 0 := by
      unfold stairId
      exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))
    show FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (i.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) i) *
      (FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (j.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j))⁻¹ * _ = _
    rw [hst]
    revert hSj
    generalize stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j) = Sj
    intro hSj
    rw [FractionalIdeal.coeIdeal_mul, mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
    unfold Places.stA Places.stAbar dI
    have hx : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (-D.host.xi0) ^ (j.1 + 1) = -D.host.xi0 := by
      rw [hij, pow_succ (-D.host.xi0) (i.1 + 1), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)), one_mul]
    calc _ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ (i.1 + 1))⁻¹) *
          FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((-D.host.xi0) ^ (j.1 + 1)) * D.host.AA * D.host.AAbar *
          (Sj * Sj⁻¹) * (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) *
          (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ hSj, mul_inv_cancel₀ hN, mul_inv_cancel₀ hN', FractionalIdeal.spanSingleton_mul_spanSingleton, hx,
          mul_one, mul_one, mul_one]
        congr 2
        rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
        exact ⟨-1, by simp⟩
  constructor
  · intro hs'
    refine idV_le_of_loc (fun z hz => ?_) hs'
    obtain ⟨t, ht, htm⟩ := exists_modul G.pl sc hv
    exact ⟨t, ht, by rw [← hid, mul_comm (algebraMap _ _ _)]; exact FractionalIdeal.mul_mem_mul hz htm⟩
  · intro hs'
    refine GlobalTheory.SeeSaw.idV_mono ?_ v hs'
    rw [← hid]
    calc _ ≤ 𝔟 i * (𝔟 j)⁻¹ * 1 := by first | exact FractionalIdeal.mul_left_mono _ FractionalIdeal.coeIdeal_le_one | exact mul_le_mul_right FractionalIdeal.coeIdeal_le_one _ | exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _ | exact mul_le_mul' le_rfl FractionalIdeal.coeIdeal_le_one
      _ = _ := mul_one _
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.ColsFB.cols_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dJ (σ + 1) h) (xFB F σ h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D _ T L μ0 _ sc G W M _ F hF σ h h' v hv i a ha
  obtain ⟨hc, he, -⟩ := hF.hJ (σ + 1) h
  obtain ⟨hc', he', -⟩ := hF.hB σ h'
  have hz := hF.zB' σ h'
  have hζ := hF.ζ (σ + 1)
  have hrat : ∀ {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E),
      GlobalTheory.MixModel.rat N *ᵥ ratV z = ratV (N *ᵥ z) := by
    intro m n N z
    funext k

    simp [GlobalTheory.MixModel.rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  set t := a * incA D ((-D.host.xi0) ^ (i.1 + 1)) with ht
  have hL : FinPl.colMul (F.dJ (σ + 1) h).jX i a =
      fun k => t * incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k ⟨i.1, by omega⟩) := by
    funext k
    simp only [FinPl.colMul, HypDec.jX, GlobalTheory.MixModel.rat, he, colsOf, Matrix.map_apply, map_mul, ht]
    rw [← mul_assoc]
    rfl
  have hR : FinPl.colMul (xFB F σ h') i a =
      fun k => t * incA D ((G.colDec (2 * σ + 2) (by omega) h').a k ⟨i.1, by omega⟩) := by
    funext k
    induction i using Fin.lastCases with
    | last =>
      have e1 : (F.dB σ h').i₀ *ᵥ vecB (F.oB σ h') (F.ζ (σ + 1)) =
          (-D.host.xi0) ^ (σ + 1) • fun i => (G.colDec (2 * σ + 2) (by omega) h').a i ⟨σ, by omega⟩ := by
        rw [vecB, hζ, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hz]
      simp only [FinPl.colMul, xFB, xLast, Matrix.of_apply, Fin.snoc_last, HypDec.j0, hrat, e1, ratV, Pi.smul_apply,
        smul_eq_mul, map_mul, ht, Fin.val_last]
      rw [← mul_assoc]
    | cast j =>
      simp only [FinPl.colMul, xFB, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, GlobalTheory.MixModel.rat, he', colsOf,
        Matrix.map_apply, map_mul, ht, Fin.coe_castSucc]
      rw [← mul_assoc]
      rfl
  rw [hL, hR]
  have hΛ3 : G.Λ (.grid (2 * σ + 3) 0) = (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).lat
      (G.Λ (.core (2 * (σ + 1) + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)) :=
    G.sp.colLat _ _ _
  have hΛ2 : G.Λ (.grid (2 * σ + 2) 0) = (G.colDec (2 * σ + 2) (by omega) h').lat
      (G.Λ (.core (2 * σ + 2))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)) :=
    G.sp.colLat _ _ _
  rw [hΛ3, hΛ2, (GlobalTheory.T.embedding_column_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).1,
    (GlobalTheory.T.embedding_column_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2]
  have hst : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1) ⟨i.1, by omega⟩ =
      D.host.AA * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) ⟨i.1, by omega⟩ *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    have e : 2 * (σ + 1) + 1 - 1 - i.1 = (2 * σ + 2 - 1 - i.1) + 1 := by have := i.2; omega
    simp only [stairId, e, Places.stA]
    ring
  rw [hst, GlobalTheory.T.fractionalIdealCompletion_div_conjModulus_off_badPlaces G.pl sc hv]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.nsmul_projection_xColumns_mem_selfDual_lattice : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G (2 * ρ + 1), N • (u ⬝ (F.dB ρ h).jX ⬝ (F.dB ρ h).pX) ∈ latBig G (2 * ρ + 1) := by
  first | exact @GlobalTheory.ProjXCols.nsmul_projX_mem_latBig | exact GlobalTheory.ProjXCols.nsmul_projX_mem_latBig | (intros; apply GlobalTheory.ProjXCols.nsmul_projX_mem_latBig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.half_vector_symplectic_orthogonal : All fun {D} _ _ _ {G} _ _ => ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT (fun v => v ∉ G.pl.S0), ∀ y : WO S T, IsHalf e y → symplO S T u y = 0 := by
  first | exact @GlobalTheory.OrthOff.orthOff | exact GlobalTheory.OrthOff.orthOff | (intros; apply GlobalTheory.OrthOff.orthOff <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.LinkProd

variable {D : D7}

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  simp [heisO, symplOH_zero_left]

theorem lnk_point {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (l : Lnk L ζ L' ζ')
    {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (n : GA D W) :
    l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) = ptT d L (yZero L ρ ζ) n ∧
      cenT d L (yZero L ρ ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  constructor
  · have h : (rat l.τ : Mx D L.rank L'.rank) ⬝ zEll L' ρ ζ' = yZero L ρ ζ := by
      have h0 : ratV (-ζ) = -ratV ζ := funext fun i => map_neg (incA D) _
      rw [yZero, zEll, zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, h0, Matrix.neg_vecMulVec]
    rw [GlobalTheory.Unf.LinkPoint.ptT_eq, Lnk.κ, ptS, d.extX_apply, ← h]
    simp only [Matrix.mul_assoc]
  · have hN : D.host.xi0 * star D.host.xi0 ≠ 0 :=
      mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (star_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
    rw [GlobalTheory.Unf.LinkPoint.cenT_eq, GlobalTheory.Unf.LinkPoint.neg_cenS_eq, yZero, adj_neg, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, GlobalTheory.Unf.LinkPoint.gram_zEll, GlobalTheory.Unf.LinkPoint.gram_zEll,
      smul_smul, ← map_mul, l.norm, inv_mul_cancel_left₀ hN]

theorem perAll_box_eq_per : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle) (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma → IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) Ξ₁ Ξ₂, IsThetaFunO ψ B.A J.W₀ Ξ₁ → IsThetaFunO ψ B.L J.W₀ Ξ₂ → J.perAll ψ B s.om₀ φ G (B.o.boxS J.W₀ Ξ₁ Ξ₂) = J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) := by
  intro D ψ ρ B J s L' ζ' hL' l χA χz χ' oma omz hχ hoa hoz φ G Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have hψ := hoa.std
  have hrk : B.L.rank = L'.rank := B.line.1.trans hL'.1.symm
  have hres : ResEta D χz B.L.rank := by rw [hrk]; exact hoz.resT
  obtain ⟨omL, hoL⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D B.L J.W₀ ψ χz s.χW hψ hoz.hecT hoa.hecT hres hoa.resT
  obtain ⟨hg, -⟩ := GlobalTheory.T.linkedLineVectors_invertible_on_theta_functions D ψ hψ B.L L' J.W₀ B.ζ ζ' B.line hL' l
  have hg' : l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram := by
    rw [Int.cast_one, one_mul]; exact hg
  have hcl := (GlobalTheory.ConjLine.conj_line D ψ B.L L' J.W₀ l.τ hrk hg' χz s.χW χ' omL omz hoL hoz Ξ₂ hΞ₂).2
  have hTS := GlobalTheory.TensorSrc.tensorSource D ψ hψ B.V₀ B.A B.L B.o J.W₀
  have hw0 : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s.χW s.om₀ := hχ ▸ s.weil₀
  have hbt : IsThetaFunO ψ B.V₀ J.W₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) := hTS.box_theta Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have key : ∀ n ∈ flagN J.d, ∀ h, ∫ h₀ in B.vA.𝓕, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h ∂B.vA.μ =
      liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁ h * star (thetaJS ψ J.d ζ' omz (fun w => star (Ξ₂ (l.κ J.W₀ w))) n h) := by
    intro n _ h
    obtain ⟨hp, hc⟩ := lnk_point l J.d n
    have e1 : ∀ h₀, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) h₀ n h =
        oma (h₀, h) Ξ₁ 0 * φ h₀ * (ψ (cenT J.d B.L (yZero B.L ρ B.ζ) n) * omL (1, h) Ξ₂ (ptT J.d B.L (yZero B.L ρ B.ζ) n)) := by
      intro h₀
      rw [GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ _ hbt,
        hTS.om_box χA χz s.χW s.om₀ oma omL hw0 hoa hoL h₀ 1 h Ξ₁ Ξ₂ hΞ₁ hΞ₂]
      simp only [OrthDec.boxS, AddEquiv.apply_symm_apply]
      ring
    simp_rw [e1]
    rw [integral_mul_const, liftT_apply]
    congr 1
    have hcl' : omz (h, 1) (fun w => star (Ξ₂ (l.κ J.W₀ w))) = fun w => star (omL (1, h) Ξ₂ (l.κ J.W₀ w)) := hcl h
    rw [thetaJS, jacS, hcl', Pi.smul_apply, smul_eq_mul, heisO_at_zero, star_mul', star_star, star_psi hψ, hp, hc]
  unfold JacL.perAll JacL.per fjAll fjSrc
  congr 1
  funext h
  congr 1
  funext n
  rw [fjAllFun, fjSrcFun, key n.1 n.2 h]
  ring

end GlobalTheory.LinkProd

end
end
