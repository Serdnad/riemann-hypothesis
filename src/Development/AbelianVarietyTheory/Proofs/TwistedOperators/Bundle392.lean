module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilator
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbit

theorem weil_heisDeriv_intertw_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (g : UA σ X.J)
    (Tg : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hTg : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f (Tg f)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) (hf : ActsD (evI F) (M.heisLine ψ u) f f₁) (y) :
    Tg f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).1
      (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).2 (Tg f) y := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hψ
  have hS := hW.isUSplitting
  have laws := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)
  have h1 : f₁ = D u f := by
    have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
      (laws f (D u f) (D u f)).1 (M.heisLine ψ u) (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
        (hD u hu f).1
    exact (laws f f₁ (D u f)).2.2.1 _ hf hAD
  have h2 : ∀ (f' : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) →
      om (g, 1) (pureA F f' g') = pureA F (Tg f') g' := by
    intro f' g' hg
    have hr : Rest (evI F) (⇑f') (fun x => g' (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f', g', hg, rfl⟩⟩
      show g' _ = g' _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hTg f' _ hr
  set g₀ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (GlobalTheory.RealLift.intPts F (Fin n × Fin d)).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set x₀ := GlobalTheory.RealLift.ptAt y (0 : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) with hx₀
  set u' := mat g * u with hu'def
  have hu' : At (evI F) u' := fun a ha => by rw [hu'def, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero]
  have hl := GlobalTheory.RealLift.eval_mem_adm (F := F) x₀
  have hl' := hS.adm (g, 1) _ hl
  have dA := (hD u hu f).1 g₀ hg₀ _ hl'
  have dB := (hD u' hu' (Tg f)).1 g₀ hg₀ _ hl
  have hfun : (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (g, 1)) (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) =
      fun t : ℝ => (LinearMap.proj x₀ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ)
        (M.co.rho ψ (realAd F t • u') (pureA F (Tg f) g₀)) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl (g, 1) _ _ (Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩), h2 f g₀ hg₀]
    congr 3
    simp [actAB, hu'def, mat, Matrix.mul_smul]
  change HasDerivAt (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (g, 1))
    (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) _ 0 at dA
  rw [hfun] at dA
  have e := dA.unique dB
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2 _ g₀ hg₀, hx₀, GlobalTheory.RealLift.pureA_ptAt, hg₀0,
    mul_one] at e
  rw [h1, e, (hD u' hu' (Tg f)).2]
  rfl

end GlobalTheory.HeisOrbit
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbit

open GlobalTheory.WeilM

theorem weil_heisDeriv_intertw {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (h : UA σ W.J)
    (Th : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hTh : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (Th f)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) (hf : ActsD (evI F) (M.heisLine ψ u) f f₁) (y) :
    Th f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).1
      (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).2 (Th f) y := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hψ
  have hS := hW.isUSplitting
  have laws := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)

  have h1 : f₁ = D u f := by
    have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
      (laws f (D u f) (D u f)).1 (M.heisLine ψ u) (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
        (hD u hu f).1
    exact (laws f f₁ (D u f)).2.2.1 _ hf hAD

  have h2 : ∀ (f' : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ), g ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) →
      om (1, h) (pureA F f' g) = pureA F (Th f') g := by
    intro f' g hg
    have hr : Rest (evI F) (⇑f') (fun x => g (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f', g, hg, rfl⟩⟩
      show g _ = g _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hTh f' _ hr

  set g₀ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (GlobalTheory.RealLift.intPts F (Fin n × Fin d)).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set x₀ := GlobalTheory.RealLift.ptAt y (0 : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) with hx₀
  set u' := u * (mat h)ᵀ with hu'def
  have hu' : At (evI F) u' := fun a ha => by rw [hu'def, ← Matrix.smul_mul, hu a ha, Matrix.zero_mul]
  have hl := GlobalTheory.RealLift.eval_mem_adm (F := F) x₀
  have hl' := hS.adm (1, h) _ hl
  have dA := (hD u hu f).1 g₀ hg₀ _ hl'
  have dB := (hD u' hu' (Th f)).1 g₀ hg₀ _ hl
  have hfun : (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (1, h)) (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) =
      fun t : ℝ => (LinearMap.proj x₀ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ)
        (M.co.rho ψ (realAd F t • u') (pureA F (Th f) g₀)) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl (1, h) _ _ (Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩), h2 f g₀ hg₀]
    congr 3
    simp [actAB, hu'def, mat, Matrix.smul_mul]
  change HasDerivAt (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (1, h))
    (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) _ _ at dA
  rw [hfun] at dA
  have e := dA.unique dB
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2 _ g₀ hg₀, hx₀, GlobalTheory.RealLift.pureA_ptAt, hg₀0,
    mul_one] at e
  rw [h1, e, (hD u' hu' (Th f)).2]
  rfl

end GlobalTheory.HeisOrbit
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweGlobal.TensorMap

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem finite_nonint {κ : Type} [Finite κ] (x : κ → AF F) :
    {w : Pl F | ¬ ∀ i, evFin F w (x i) ∈ w.adicCompletionIntegers F}.Finite := by
  have h : ∀ i, {w : Pl F | evFin F w (x i) ∉ w.adicCompletionIntegers F}.Finite := fun i =>
    Filter.eventually_cofinite.1 (x i).2.2
  refine (Set.finite_iUnion h).subset ?_
  intro w hw
  push_neg at hw
  obtain ⟨i, hi⟩ := hw
  exact Set.mem_iUnion.2 ⟨i, hi⟩

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}


open Classical in
def vacOff (M : Model σ Y W) (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) : ℂ :=
  ∏ᶠ w, if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i)

def prodT (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) :
    (Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap fun v =>
    (LinearMap.proj (fun i => evFin F v.1 (x i)) : ((Fin n × Fin d → Fv F v.1) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (SB _).subtype

theorem prodT_apply (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    prodT T x φ = ∏ v : T, (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) fun i => evFin F v.1 (x i) := by
  simp [prodT]

def multi (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d)) :
    (Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ) :=
  MultilinearMap.pi fun x => (f (fun i => evI F (x i)) * vacOff M T x) • prodT T x

theorem multi_apply (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (x : Fin n × Fin d → AF F) :
    multi M T f φ x = f (fun i => evI F (x i)) * vacOff M T x * prodT T x φ := by
  simp [multi]

def multiL (M : Model σ Y W) (T : Finset (Pl F)) :
    SInf F (Fin n × Fin d) →ₗ[ℂ]
      ((Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ)) where
  toFun := multi M T
  map_add' f g := by
    ext φ x
    simp only [multi_apply, MultilinearMap.add_apply, Pi.add_apply, SchwartzMap.add_apply]
    ring
  map_smul' c f := by
    ext φ x
    simp only [multi_apply, MultilinearMap.smul_apply, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring


open Classical in
theorem finprod_split (M : Model σ Y W)
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (T : Finset (Pl F)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
    (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) (h2 : ∀ v ∉ T, φ' v = M.vac v) (x : Fin n × Fin d → AF F) :
    ∏ᶠ w, φ' w (fun i => evFin F w (x i)) = vacOff M T x * prodT T x φ := by
  set ρ : Pl F → ℂ := fun w => if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i) with hρdef
  set θ : Pl F → ℂ := fun w => if w ∈ T then φ' w (fun i => evFin F w (x i)) else 1 with hθdef
  have e : (fun w => φ' w (fun i => evFin F w (x i))) = fun w => θ w * ρ w := by
    funext w
    by_cases hw : w ∈ T
    · simp [θ, ρ, hw]
    · simp [θ, ρ, hw, h2 w hw]
  have hρ : (Function.mulSupport ρ).Finite := by
    refine ((Filter.eventually_cofinite.1 hstd).union (finite_nonint x)).subset ?_
    intro w hw
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hw
    by_cases hwT : w ∈ T
    · simp [ρ, hwT]
    · simp only [ρ, hwT, if_false, hc.1]
      exact Set.indicator_of_mem (s := {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F}) hc.2 1
  have hθ : Function.mulSupport θ ⊆ (T : Set (Pl F)) := by
    intro w hw
    by_contra hc
    exact hw (by simp [θ, show w ∉ T from hc])
  rw [e, finprod_mul_distrib (T.finite_toSet.subset hθ) hρ, mul_comm]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset θ hθ, prodT_apply, ← Finset.prod_coe_sort T]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [θ, v.2, h1 v.1 v.2]

def tensL (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₗ[ℂ]
      ((Fin n × Fin d → AF F) → ℂ) :=
  TensorProduct.lift ((PiTensorProduct.lift.toLinearMap ∘ₗ multiL M T) ∘ₗ (M.Pol ψ emb).subtype)

theorem tensL_tmul (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (T : Finset (Pl F)) (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = multi M T (f : SInf F (Fin n × Fin d)) φ := by
  simp [tensL, multiL]

theorem exists_tensL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w),
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ]
        ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') ∧
      GlobalTheory.HoweGlobal.algAt M ψ emb T ≤ LinearMap.range L := by
  intro F E _ _ _ _ _ σ n d Y W M ψ emb hstd T
  have hchar : ∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
      (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
      tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : SInf F (Fin n × Fin d)) φ' := by
    intro f φ φ' h1 h2
    funext x
    rw [tensL_tmul, multi_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, finprod_split M hstd T φ φ' h1 h2 x, mul_assoc]
  refine ⟨tensL M ψ emb T, hchar, Submodule.span_le.2 ?_⟩
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨⟨f, hf⟩ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun v : T => ⟨φ v.1, hφ v.1⟩),
    hchar ⟨f, hf⟩ _ φ (fun _ _ => rfl) hv⟩

end GlobalTheory.HoweGlobal.TensorMap
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly.ReadDerB

private theorem pure_smul_twisted_operators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ)
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ τ ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = M.vac v)) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
    exact ⟨1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, hv⟩, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h₁ j
      · simpa using h₂ j
    · simp [Fin.sum_univ_add]
  | smul c x _ hx =>
    obtain ⟨m, f, φ, h, rfl⟩ := hx
    refine ⟨m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ τ).smul_mem c (h i).1, (h i).2⟩, ?_⟩
    simp [Finset.smul_sum, pure_smul_twisted_operators]

end GlobalTheory.TripleAssembly.ReadDerB

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.EqFin

theorem liftPure_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hφv : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    GlobalTheory.TripleAssembly.liftPure M pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  have H := GlobalTheory.PureLift.exists_pureLift σ Y Z M ψ hM P pr N pv s hs
  unfold GlobalTheory.TripleAssembly.liftPure
  rw [dite_eq_left H]
  exact H.choose_spec f φ hφ hφv

theorem darbAlg_stable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) (hM : M.IsGood ψ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v)
    (O : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (T₀ : Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s))
    (hgen : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v) ∧
        O (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ ∧
        GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ₁ v)) = T₀ (GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)))) :
    ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ, O Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ ∧
      GlobalTheory.TripleAssembly.liftPure M pr pv s (O Ψ) = LinearMap.lTensor P T₀ (GlobalTheory.TripleAssembly.liftPure M pr pv s Ψ) := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hφv, rfl⟩ := hx
    obtain ⟨φ₁, h1, h1v, hO, hT⟩ := hgen f φ hφ hφv
    refine ⟨?_, ?_⟩
    · rw [hO]; exact Submodule.subset_span ⟨f, φ₁, hf, h1, h1v, rfl⟩
    · rw [hO, liftPure_pure M ψ hM pr pv s hs f φ₁ h1 h1v, liftPure_pure M ψ hM pr pv s hs f φ hφ hφv,
        LinearMap.lTensor_tmul, hT]
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, ?_⟩
    · rw [map_add (f := _)]; exact Submodule.add_mem _ hx.1 hy.1
    · simp only [map_add (f := _), hx.2, hy.2]
  | smul c x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [map_smul]; exact Submodule.smul_mem _ c hx.1
    · simp only [map_smul, hx.2]

end GlobalTheory.TripleAssembly.EqFin

namespace GlobalTheory.TripleAssembly.EqFin


end GlobalTheory.TripleAssembly.EqFin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.finitePart_mem_compact_of_isotropicAnnihilator : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧ ∀ y : Mx D a b, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W (GlobalTheory.IsoMean.emb V W P Q y) u) = 1) → y.map (finPart D) ∈ K := by
  first | exact @GlobalTheory.IsoMeanAnnih.finPart_mem_compact | exact GlobalTheory.IsoMeanAnnih.finPart_mem_compact | (intros; apply GlobalTheory.IsoMeanAnnih.finPart_mem_compact <;> assumption)
end
