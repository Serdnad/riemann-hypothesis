module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle002
public import Development.WeilBound.ThetaLifts.Reductions.MetaDef
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsCharNe
public import Development.WeilBound.ThetaLifts.Reductions.ExistsSmoothFun
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt
public import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Development.WeilBound.ThetaLifts.Reductions.SiegelGood
public import Development.WeilBound.ThetaLifts.Reductions.SiegelParMod
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKR

open scoped TensorProduct NNReal ENNReal Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Real RealInnerProductSpace Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKF PositivityTheory.ThKF.W PositivityTheory.ThKF.A GlobalTheory.HeisSchA GlobalTheory.RealWeil

theorem archLie' (hL : LocalLift) : PositivityTheory.ThKF.ArchLie := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ δ hδ T hT
  obtain ⟨C⟩ := nonempty_coord (F := F) (κ := Fin n × Fin d)
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  let x : ℝ → UA σ X.J × UA σ W.J := fun t => (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))
  have xc : Continuous x := (hγ.1.comp continuous_ofAdd).prodMk (hδ.1.comp continuous_ofAdd)
  have x0 : x 0 = 1 := by simp [x]
  have xm : ∀ t u, x (t + u) = x t * x u := fun t u => by simp [x, ofAdd_add]
  have T0 : ∀ f, T 0 f = f := fun f => DFunLike.coe_injective (pureA_inj h₁ (by
    rw [← (hT 0).1 f _ h₀]
    exact (congrArg (fun y => om y _) x0).trans (LinearMap.congr_fun om.map_one _)))
  have Tm : ∀ t u f, T (t + u) f = T t (T u f) := fun t u f => DFunLike.coe_injective (pureA_inj h₁ (by
    rw [← (hT _).1 f _ h₀, ← (hT _).1 _ _ h₀, ← (hT _).1 f _ h₀]
    exact (congrArg (fun y => om y _) (xm t u)).trans (LinearMap.congr_fun (om.map_mul _ _) _)))
  have Tc : ∀ f (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ), Continuous fun t => L (T t f) := fun f L => by
    obtain ⟨l, hl, e⟩ := exists_adm L
    have := (hs.cont l hl _ (pureA_mem f h₀)).comp xc
    convert this using 1
    funext t
    show _ = l (om (x t) _)
    rw [(hT t).1 f _ h₀, e _ _ h₀, h₁, one_mul]
  have main := lie' hL (fun t => (C.P ≪≫ₗ phL M (x t) ≪≫ₗ C.P.symm).toLinearMap) (fun w => ?_) (fun w => ?_)
    (fun t u w => ?_) (fun t w w' => ?_) _ (fun t => impl_of hP C (T := (T t).toLinearMap) (hT t).1) (fun f => by simp [T0])
    (fun t u f => by simp [Tm]) (fun f lam => Tc (C.S.symm f) (lam.comp C.S.toContinuousLinearMap))
  · obtain ⟨Q, hQ, hd⟩ := main
    intro f hf
    have hw : ∀ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, HasDerivAt (fun t => L (T t f)) (L (C.S.symm (Q (C.S f)))) 0 := fun L => by
      simpa using hd (C.S f) (L.comp (C.S.symm : _ →L[ℂ] _))
    refine ⟨C.S.symm (Q (C.S f)), ?_, ?_, hw⟩
    · refine weylAlg_induction (P := fun A => ∀ f ∈ M.Pol B.ψ B.emb, C.S.symm (A (C.S f)) ∈ M.Pol B.ψ B.emb)
        (fun f hf => by simpa using hf) (fun A w hA f hf => ?_) (fun f _ => by simp) (fun A A' h1 h2 f hf => ?_)
        (fun c A h1 f hf => ?_) hQ f hf
      · simpa [Coord.D] using hA _ (D_mem_Pol hP.base.std M C B.emb (C.P w) hf)
      · simpa using add_mem (h1 f hf) (h2 f hf)
      · simpa using Submodule.smul_mem _ c (h1 f hf)
    · refine actsD_of (T := fun t => T t f) (fun h => ⟨by simp [h], fun t => map_zero _⟩) (fun t => (hT t).1 f) fun y => ?_
      exact hw (BoundedContinuousFunction.evalCLM ℂ y ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _)
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, phL_eq]
    refine C.P.symm.toLinearMap.continuous_of_finiteDimensional.comp (continuous_infPart2.comp ?_)
    obtain ⟨u, hu⟩ := M.co.e.surjective (mixedSpaceVecPairAsAdeles F (C.P w))
    simp only [← hu, phB_e]
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
    refine (IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap).comp ?_
    exact ((Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp xc))).matrix_mul
      continuous_const).matrix_mul
        (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp xc))).matrix_transpose
  · simp [phL_eq, x0, phB_one, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [phL_eq, xm, phB_mul, phL_spec, ← phL_eq]
  · simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, C.sympl_eq, LinearEquiv.apply_symm_apply, tb_eq, ← phL_spec,
      phB_form]

end PositivityTheory.ThKR
end
end

section

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)
open PositivityTheory.ThKEst PositivityTheory.ThKEst.Sieg

namespace PositivityTheory.ThKR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}


variable (σ J X Y) in
structure IsTorus (a : (Fin r → ℝ) → GAd σ J) : Prop where
  add : ∀ s t, a (s + t) = a s * a t
  cont : Continuous a
  tor : ∀ t, IsTorusElt σ J X Y (fun i => Real.exp (t i)) (a t)
  onX : ∀ t, (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i)))
  onY : ∀ t, (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i)))
  onV : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
    (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z

theorem exists_isTorus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ a, IsTorus σ J X Y a := by
  obtain ⟨a, h1, h2, h3, h4⟩ := exists_torus h hJ hW
  exact ⟨a, ⟨h1, h2, h3, fun t => (h4 t).1, fun t => (h4 t).2.1, fun t => (h4 t).2.2⟩⟩

theorem mul_mem_minPar {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) : p * q ∈ minPar σ J X :=
  mul_mem_minimal_parabolic hp hq

theorem inv_mem_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) : p⁻¹ ∈ minPar σ J X :=
  inv_mem_minimal_parabolic h hJ hW hp


variable (X) in
def minParSub (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : Subgroup (GAd σ J) where
  carrier := minPar σ J X
  one_mem' := one_mem_minPar σ J X
  mul_mem' := mul_mem_minPar
  inv_mem' := inv_mem_minPar h hJ hW

theorem isClosed_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (minPar σ J X) :=
  isClosed_minimal_parabolic h hJ hW

theorem minParOne_subset : minParOne σ J X ⊆ minPar σ J X := fun _ ⟨B, hB, e, _⟩ => ⟨B, hB, e⟩

theorem IsTorus.mem {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (t : Fin r → ℝ) : a t ∈ minPar σ J X :=
  ⟨_, Matrix.blockTriangular_diagonal _, ha.onX t⟩

def IsTorus.sub {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (t : Fin r → ℝ) : minParSub X h hJ hW :=
  ⟨a t, ha.mem t⟩

theorem exists_tau (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) :
    ∃ τ : minParSub X h hJ hW → Fin r → ℝ, Continuous τ ∧ (∀ p q, τ (p * q) = τ p + τ q) ∧
      (∀ t, τ (ha.sub h hJ hW t) = t) ∧ (∀ p (hp : p ∈ minParOne σ J X), τ ⟨p, minParOne_subset hp⟩ = 0) ∧
      ∀ p : minParSub X h hJ hW, p.1 * (a (τ p))⁻¹ ∈ minParOne σ J X :=
  exists_torus_section h hJ hW (minParSub X h hJ hW) (fun _ => Iff.rfl) ha.add ha.onX (ha.sub h hJ hW) (fun _ => rfl)

theorem map_mul_torus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) (ν : Measure (minParSub X h hJ hW)) [ν.IsHaarMeasure] (s : Fin r → ℝ) :
    ν.map (· * ha.sub h hJ hW s) = ENNReal.ofReal (Real.exp (2 * (Module.finrank ℚ F : ℝ) * rho2 n s)) • ν :=
  PMod.map_mul_torus_of h hJ hW (minParSub X h hJ hW) (isClosed_minPar h hJ hW) (fun _ hp => hp) (fun _ hp => hp)
    ha.add ha.onX ha.onY ha.onV ha.mem ν s

theorem commute_of_goodPosition (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J)))
    (hG : GoodPosition σ J X Y K) {m : GAd σ J} (hm : m ∈ minPar σ J X) (hmK : m ∈ K) (t : Fin r → ℝ) :
    a t * m = m * a t :=
  commute_of_good_position h hJ hW (ha.tor t).1 (ha.onX t) (ha.onY t) (ha.onV t) hK hG hm hmK

end PositivityTheory.ThKR

end
end
