module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle095
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle412
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle265
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle321
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle319
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle330
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389

@[expose] public section

section

open Formalism.BasicNotions Formalism.L2.DIV MeasureTheory
open scoped Matrix

noncomputable section
open MvPolynomial GlobalTheory.KJInf

namespace GlobalTheory.AvgJet

variable {ι : Type} [Fintype ι]

def evalL {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₗ[ℂ] ℂ where
  toFun := evalAt y
  map_add' F G := by simp [evalAt]
  map_smul' c F := by simp [evalAt, smul_eval]

theorem evalL_apply {a : ℕ} (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) : evalL y F = evalAt y F := rfl

theorem dual_eq_sum_evalAt {a : ℕ} (V : Submodule ℂ (PY ι a)) [FiniteDimensional ℂ V]
    (hsep : ∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) (Λ : Module.Dual ℂ V) :
    ∃ (S : Finset {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}) (c : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ),
      ∀ v : V, Λ v = ∑ y ∈ S, c y * evalAt y.1 (v : PY ι a) := by
  set E : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ
    (Set.range fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} => (evalL y.1).comp V.subtype) with hE
  have hco : E.dualCoannihilator = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    rw [Submodule.mem_dualCoannihilator] at hv
    have h0 : (v : PY ι a) = 0 := hsep _ fun y hy => hv _ (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    exact Subtype.ext h0
  have htop : E = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := E), hco, Submodule.dualAnnihilator_bot]
  have hΛ : Λ ∈ E := htop ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hΛ
  refine ⟨c.support, c, fun v => ?_⟩
  rw [← hc, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply, smul_eq_mul]

theorem evalAt_rhoK {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (G : VV ℂ lam)
    (Y : ι → Matrix (Fin n) (Fin n) ℂ) :
    evalAt Y ((rhoK lam (invTrK g⁻¹) G : VV ℂ lam) : PY ι n) =
      (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift) *
        evalAt (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Y τ) (G : PY ι n) := by
  have htr : trAct (invTrK g⁻¹) = lft (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
    unfold trAct lft Formalism.GradedWeylDivisibility.blockAct
    congr 1
  have hdet : detTwK lam (invTrK g⁻¹) =
      ∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift := by
    unfold detTwK
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [detPow, invTrK, inside₂, Units.val_zpow_eq_zpow_val]
  show evalAt Y (actP lam (invTrK g⁻¹) G) = _
  rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, htr, hdet]
  rw [evalAt, smul_eval, ← evalAt, evalAt_lft]

theorem integrable_term {a b : ℕ} {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
    [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν] {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r)
    (Λ : FP ι a b →ₗ[ℂ] ℂ) (Q : FP ι a b) (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    Integrable (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) ν := by
  set U := GlobalTheory.KJAvg.univSubst Q with hU
  set p : PY ι a := ∑ m ∈ U.support, C (Λ (monomial m 1)) * AddMonoidAlgebra.coeff U m with hp'
  have hp : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ, Λ (mvZ g (fun _ => 1) Q) = eval (fun w => g w.1 w.2.1 w.2.2) p := by
    intro g
    rw [GlobalTheory.KJAvg.mvZ_one_eq_map_univSubst, GlobalTheory.KJAvg.linear_eq_sum_coeff Λ U.support _ (support_map_subset _ _)]

    simp only [hp', map_sum, map_mul, eval_C, coeff_map]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have e : (fun k => Λ (mvZ (fun τ => (r k τ)⁻¹) (fun _ => 1) Q) * evalAt (fun τ => r k τ * y τ) F) =
      fun k => eval (fun w => r k⁻¹ w.1 w.2.1 w.2.2) p * evalAt (fun τ => r k τ * y τ) F := by
    funext k
    rw [hp]
    simp only [GlobalTheory.KJAvg.ontoUni_inv hr]
  rw [e]
  exact GlobalTheory.KJAvg.integrable_avg_term ν hr p y F

end GlobalTheory.AvgJet


open GlobalTheory.AvgJet in
theorem GlobalTheory.AvgJet.avg_jet : ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b → 0 < a → ∀ (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (nn : ι → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' nn → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (r : K →* (ι → GL (Fin a) ℂ)), GlobalTheory.KJInf.OntoUni (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) →
    ∀ (Q : MvPolynomial (ι × Fin b × Fin a) ℂ) (Λ : Module.Dual ℂ (VV ℂ lam)), ∃ Λ' : Module.Dual ℂ (VV ℂ lam'),
    ∀ (ℓ : MvPolynomial (ι × Fin b × Fin a) ℂ →ₗ[ℂ] ℂ) (h : ι → GL (Fin b) ℂ) (v : VV ℂ lam),
      ∫ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) ∂ν =
        Λ' (rhoK lam' (invTrK h⁻¹) (Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v)) := by
  intro ι _ a b hab ha lam lam' nn hJ K _ _ _ _ _ ν _ _ r hr Q Λ
  classical
  obtain ⟨-, hcomp, -, -, -, -, hsep, -⟩ := GlobalTheory.T.fockSubstitution_identities ι a b hab
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  obtain ⟨S, c, hΛ⟩ := dual_eq_sum_evalAt (VV ℂ lam) hsep Λ
  have hav := fun y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} =>
    GlobalTheory.KJAvg.avg_span ι a b hab ha lam nn K ν (fun k τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) hr y.1 Q
  choose m y' s hinv hspan using hav
  let d : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y} → ℂ := fun y => (∏ τ, (y.1 τ).det ^ nn τ)⁻¹
  refine ⟨∑ y ∈ S, (c y * d y) • ∑ j, s y j • (evalL (y' y j)).comp (VV ℂ lam').subtype, fun ℓ h v => ?_⟩
  let hh : ι → Matrix (Fin b) (Fin b) ℂ := fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ)
  let Hh : ℂ := ∏ τ, (hh τ).det ^ (lam' τ).detShift
  let ℓ₀ : FP ι a b →ₗ[ℂ] ℂ := ℓ ∘ₗ (mvZ (fun _ => 1) hh).toLinearMap
  let F : PY ι a := (v : PY ι a) * ∏ τ, (Formalism.L2.Ker.frDet ℂ a τ : PY ι a) ^ nn τ
  have hFV : F ∈ Vn lam nn := ⟨v, (GlobalTheory.KJInf.ClsVal.cSpan_eq_VV' lam).symm ▸ v.2, rfl⟩

  have hpt : ∀ k, (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift) *
            ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) *
          ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ))
            (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q) *
          Λ (rhoK lam (invTrK (r k⁻¹)) v) =
        Hh * ∑ y ∈ S, c y * d y * (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F) := by
    intro k
    have hsub : GlobalTheory.CompactHowe.substF hh (fun τ => (((r k τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)ᵀ) Q =
        mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) := by
      rw [hcomp]
      simp only [mul_one, one_mul, Matrix.coe_units_inv]
      rfl
    rw [map_inv r k, hΛ]
    simp only [evalAt_rhoK]
    rw [hsub]
    set L := ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) with hL
    have hL' : ℓ (mvZ (fun _ => 1) hh (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q)) = L := rfl
    have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
    rw [hL', Finset.prod_mul_distrib, hH, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hdet : ∀ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun τ => (Matrix.isUnits_det_units _).ne_zero
    have key : (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ ((nn τ : ℤ) - (lam τ).detShift)) *
        (∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ (lam τ).detShift) =
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [← zpow_add₀ (hdet τ), sub_add_cancel, zpow_natCast]
    have hdy : d y * ∏ τ, (y.1 τ).det ^ nn τ = 1 :=
      inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (y.2 τ).ne_zero)
    have hF : evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F =
        evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
          ((∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * ∏ τ, (y.1 τ).det ^ nn τ) := by
      rw [GlobalTheory.KJInf.ValPol.evalAt_mul_prod, ← Finset.prod_mul_distrib]
      simp only [Matrix.det_mul, mul_pow]
    rw [hF]
    linear_combination (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a)) * key -
      (Hh * L * c y * evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) (v : PY ι a) *
        ∏ τ, ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ).det ^ nn τ) * hdy
  have hint : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y}, Integrable (fun k => c y * d y *
      (ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F)) ν :=
    fun y => (integrable_term ν hr ℓ₀ Q y.1 F).const_mul _
  have hjet : ((Formalism.L2.Ker.jetOp lam lam' (fun m => ℓ (MvPolynomial.monomial m 1)) nn v : VV ℂ lam') : PY ι b) =
      Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) := by
    have hx : Formalism.L2.Ker.jetMap (fun m => ℓ (MvPolynomial.monomial m 1)) nn (v : PY ι a) =
        ((⟨_, hJ _ _ v.2⟩ : VV ℂ lam') : PY ι b) := rfl
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.retrVV, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hx, Submodule.projectionOnto_apply_left]
  have hav' : ∀ y : {y : ι → Matrix (Fin a) (Fin a) ℂ // IsInv y},
      ∫ k, ℓ₀ (mvZ (fun τ => (((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))⁻¹) (fun _ => 1) Q) *
          evalAt (fun τ => ((r k τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) * y.1 τ) F ∂ν =
        ∑ j, s y j * ℓ (subY hab (fun τ => hh τ * y' y j τ) F) := by
    intro y
    rw [hspan y F hFV ℓ₀]
    refine Finset.sum_congr rfl fun j _ => ?_
    show s y j * ℓ (mvZ (fun _ => 1) hh (subY hab (y' y j) F)) = _
    rw [mvZ_subY]
  have hH : (∏ τ, ((h τ : GL (Fin b) ℂ) : Matrix (Fin b) (Fin b) ℂ).det ^ (lam' τ).detShift) = Hh := rfl
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hint y]
  simp only [integral_const_mul, hav']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, evalL_apply,
    smul_eq_mul, evalAt_rhoK, hjet, GlobalTheory.KJInf.ClsVal.evalAt_jetMap hab, hH]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
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




theorem _root_.GlobalTheory.T.hermitianPairing_selfDual_completion_integral_at_place : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ (v : GlobalTheory.FinPl.Pl D) (z w : Fin S.rank → AE D), z ∈ latV S L (· = v) → w ∈ latV S L (· = v) → (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.LatPairInt.pairing_mem_at | exact GlobalTheory.LatPairInt.pairing_mem_at | (intros; apply GlobalTheory.LatPairInt.pairing_mem_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.integralFiniteAdele_supported_div_prime_to_place : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (d : 𝓞 D.host.F), d ∉ v.asIdeal → ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧ α = α' * algebraMap D.host.F (Af D.host.F) (d : D.host.F) := by
  first | exact @GlobalTheory.intAf_div_prime_to_place' | exact GlobalTheory.intAf_div_prime_to_place' | (intros; apply GlobalTheory.intAf_div_prime_to_place' <;> assumption)
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


theorem _root_.GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual : ∀ {D : D7} {S S' T T' : HSp D} {LS : Lat S} {LS' : Lat S'} {LT : Lat T} {LT' : Lat T'}, IsSelfDualC S LS → IsSelfDualC S' LS' → IsSelfDualC T' LT' → ∀ (j : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E), (∀ y ∈ LS', j *ᵥ y ∈ LS) → (∀ t ∈ LT, q *ᵥ t ∈ LT') → ∀ x : WO S T, x ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) → (rat q * x * rat j : WO S' T') ∈ latO S' T' (LS' : Set _) (LT' : Set _) (fun _ => True) := by
  first | exact @GlobalTheory.Twist.RatLatO.rat_mul_mem_latO | exact GlobalTheory.Twist.RatLatO.rat_mul_mem_latO | (intros; apply GlobalTheory.Twist.RatLatO.rat_mul_mem_latO <;> assumption)
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

theorem _root_.GlobalTheory.T.hermitianSkewAdjoint_mem_adjoint_homLattice : ∀ (D : D7) (S T : HSp D) (LS LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop), (∀ a ∈ D.host.AA, ∀ s ∈ LS, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) → ∀ x ∈ latO S T (LS : Set _) (LT : Set _) P, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  first | exact @GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO | exact GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO | (intros; apply GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem inner_gW (hC : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (x y : (R.HW i σ).H) :
    ⟪R.gW i σ g x, R.gW i σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map ⟨R.gW i σ g, GlobalTheory.gW_norm_eq R hC.models.HW hC.models.gW hC.models.νW i σ g⟩ x y

theorem adjoint_projH (hC : GlobalTheory.Hk3.Core R F) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    LinearMap.adjoint (GlobalTheory.LiftLower.projH R i σ) = GlobalTheory.LiftLower.projH R i σ := by
  have hc : ∀ g, starRingEnd ℂ (RealDat.eC (A := A) σ g) = RealDat.eC (A := A) σ g⁻¹ := by
    intro g
    unfold RealDat.eC

    rw [coeff_idemOf, coeff_idemOf, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have h1 := (hX χ hχ).map_inv σ 1
    have h2 := (hX χ hχ).map_inv σ g⁻¹
    rw [inv_one] at h1
    simp only [map_mul, map_div₀, map_natCast]
    rw [h2, ← h1]
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  unfold GlobalTheory.LiftLower.projH
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hc]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [← inner_gW hC i σ g⁻¹, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem projH_projH (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    GlobalTheory.LiftLower.projH R i σ (GlobalTheory.LiftLower.projH R i σ x) = GlobalTheory.LiftLower.projH R i σ x := by
  classical
  have h1 : ∀ g, ∑ a, RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g) = RealDat.eC (A := A) σ g := by
    intro g
    unfold RealDat.eC
    conv_rhs => rw [← idemOf_mul_self A.X hX]

    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
    simp only [map_mul]
  unfold GlobalTheory.LiftLower.projH

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_congr rfl fun g _ => by rw [← h1 g, Finset.sum_smul]]
  rw [Finset.sum_comm (f := fun g a => (RealDat.eC (A := A) σ a * RealDat.eC (A := A) σ (a⁻¹ * g)) • R.gW i σ g x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_nbij' (fun g => a * g) (fun g => a⁻¹ * g) (by simp) (by simp) (by simp) (by simp) fun g _ => ?_
  rw [inv_mul_cancel_left, map_mul, Module.End.mul_apply, mul_comm]

theorem eq_of_ext {V : HSp D} {c : CoefA V} (hc : c.Is) {H : HMod (Bridge.Gf V → c.W)} (hinj : Function.Injective H.e) {z z' : H.H}
    (h : ∀ x w, inner ℂ (c.ext (H.e z) x) w = inner ℂ (c.ext (H.e z') x) w) : z = z' := by
  refine hinj (funext fun u => ?_)
  have e : c.ext (H.e z) (GlobalTheory.AdelicScalar.finLift V u) = c.ext (H.e z') (GlobalTheory.AdelicScalar.finLift V u) :=
    ext_inner_right ℂ fun w => h _ w
  exact (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z) u).symm.trans (e.trans (GlobalTheory.AdelicScalar.ext_finLift c hc (H.e z') u))

end GlobalTheory.ConjScalarProof

namespace GlobalTheory.ConjScalarProof


open GlobalTheory.LiftLower in
theorem conjScalarAt_of_sourceLevelLaw_fock_zeta : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R → GlobalTheory.ConjScalar.ConjScalarAt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hCore hX hSL hIPF hFC hFZ hRC
  intro gramR c0R c0L hT i σ hσ μ' η' c c₁ H j th hD ev
  have hμ := hD.1
  have hη := hD.2.1
  have hf := hD.2.2.1
  have hL := hD.2.2.2
  have hL2 := (GlobalTheory.GalLift.isConjLift_iff R i σ μ' η' c H th).1 hL
  obtain ⟨ω, hL3⟩ := hL2
  obtain ⟨f₀, f, B, io, thP, hL4⟩ := hL3
  have hLD := hL4.1
  have hP := hL4.2
  have h38 := GlobalTheory.T.adelicLiftDatum_of_conjugate_liftDatum R F hCore gramR c0R c0L hT i σ c c₁ H j hσ hf μ' η' hμ hη ω f₀ f B io thP hLD
  obtain ⟨s, m, h39⟩ := h38
  have hC := h39.1
  have hν := h39.2.1
  have hy := h39.2.2.1
  have hH := h39.2.2.2
  have hth := hLD.2.2.2
  have hio := hC.2.2.2.2.2.2.2.2.2.2
  have hc : c.Is := hC.2.2.2.2.2.2.2.2.2.1
  have hv0 := hio.2.2
  let v := hv0.choose
  have hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 := hv0.choose_spec.choose_spec.1
  let K : ℂ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)
  have hKdef : K = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := rfl
  have hK0 : K ≠ 0 := by
    rw [hKdef, Finset.prod_ne_zero_iff]
    intro ρ _
    have h1 := GlobalTheory.AdelicScalar.one_le_dimK i σ ρ
    exact_mod_cast (show (dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) ≠ 0 by positivity)
  have hKc : starRingEnd ℂ K = K := by
    rw [hKdef, map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  have hadj : ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W), inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w = K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h :=
    GlobalTheory.T.adjoint_conjugateThetaLift_eq_vectorValuedLift R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv thP th hth hP
  have hpp : ∀ y, projH R i σ (projH R i σ y) = projH R i σ y := projH_projH hX i σ
  have hsa : LinearMap.adjoint (projH R i σ) = projH R i σ := adjoint_projH hCore hX i σ
  have hinj : Function.Injective H.e := hH.1
  have hadjP : ∀ y, LinearMap.adjoint th (projH R i σ y) = LinearMap.adjoint th y := fun y =>
    eq_of_ext (V := Vc D i) (c := c) (H := H) hc hinj fun x w =>
      (hadj (projH R i σ y) x w).trans ((congrArg (fun z => K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e z fun ρ => v ρ) x) (hpp y)).trans (hadj y x w).symm)
  have hfix : ∀ u, projH R i σ (th u) = th u := fun u => ext_inner_right ℂ fun y =>
    (LinearMap.adjoint_inner_right (projH R i σ) (th u) y).symm.trans
      ((congrArg (fun A => inner ℂ (th u) (A y)) hsa).trans ((LinearMap.adjoint_inner_right th u (projH R i σ y)).symm.trans
        ((congrArg (inner ℂ u) (hadjP y)).trans (LinearMap.adjoint_inner_right th u y))))
  have hW : ∀ y, (R.HW i σ).e y ∈ R.Wall i σ := fun y => GlobalTheory.AdelicScalar.HMod_mem (hCore.models.HW i σ) y
  have hz : ∀ y h w, inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := by
    intro y h w
    have e1 : c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) = K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) :=
      (congrArg c.ext (H.e.map_smul K⁻¹ _)).trans (c.ext.map_smul K⁻¹ _)
    have e2 : starRingEnd ℂ K⁻¹ = K⁻¹ := by simp only [map_inv₀, hKc]
    calc inner ℂ (c.ext (H.e (K⁻¹ • LinearMap.adjoint th y)) h) w
        = inner ℂ (K⁻¹ • c.ext (H.e (LinearMap.adjoint th y)) h) w := congrArg (fun Fn => inner ℂ (Fn h) w) e1
      _ = starRingEnd ℂ K⁻¹ * inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w := inner_smul_left _ _ _
      _ = K⁻¹ * (K * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h) := by simp only [e2, hadj y h w]
      _ = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (projH R i σ y) fun ρ => v ρ) h := inv_mul_cancel_left₀ hK0 _
  have hG := GlobalTheory.T.exists_scalar_innerProductFormula_unitCoefficient R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv ev
  let C := hG.choose
  have hC2 := hG.choose_spec
  let b := stdOrthonormalBasis ℂ c.W
  have key : ∀ u, th u ∈ partH R i σ ev → ∀ y₂,
      inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by
    intro u hu y₂
    have e1 := GlobalTheory.T.classSum_inner_eq_sum_vectorThetaLifts R F hX hSL hIPF hFC hFZ hRC i σ s m μ' η' ω B f₀ f c io H hC hν hy hH v hv
      _ (hW (projH R i σ (th u))) _ (hW (projH R i σ y₂)) _ _ (hz (th u)) (hz y₂) b
    have hu' : projH R i σ (th u) ∈ partH R i σ ev := (hfix u).symm ▸ hu
    have e2 : inner ℂ (projH R i σ (th u)) (projH R i σ y₂) = inner ℂ (th u) y₂ :=
      (congrArg (fun z => inner ℂ z (projH R i σ y₂)) (hfix u)).trans
        ((congrArg (fun A => inner ℂ (th u) (A y₂)) hsa.symm).trans
          ((LinearMap.adjoint_inner_right (projH R i σ) (th u) y₂).trans (congrArg (fun z => inner ℂ z y₂) (hfix u))))
    have e4 : inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂) =
        (Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂) := by
      refine e1.trans ?_
      rw [Finset.sum_congr rfl fun k _ => hC2 _ hu' (projH R i σ y₂) (b k) (b.orthonormal.1 k), e2, Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul]
    have e3 : ∀ y, LinearMap.adjoint th y = K • (K⁻¹ • LinearMap.adjoint th y) := fun y =>
      (smul_inv_smul₀ hK0 _).symm
    calc inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y₂)
        = inner ℂ (K • (K⁻¹ • LinearMap.adjoint th (th u))) (K • (K⁻¹ • LinearMap.adjoint th y₂)) :=
          congrArg₂ (inner ℂ) (e3 _) (e3 _)
      _ = starRingEnd ℂ K * (K * inner ℂ (K⁻¹ • LinearMap.adjoint th (th u)) (K⁻¹ • LinearMap.adjoint th y₂)) :=
          (inner_smul_left _ _ _).trans (congrArg (fun z => starRingEnd ℂ K * z) (inner_smul_right _ _ _))
      _ = K * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂))) :=
          (congrArg (fun z => starRingEnd ℂ K * (K * z)) e4).trans
            (congrArg (fun k => k * (K * ((Module.finrank ℂ c.W : ℂ) * (C * inner ℂ (th u) y₂)))) hKc)
      _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y₂ := by ring
  refine ⟨(K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re, fun u hu => ?_⟩
  by_cases h0 : th u = 0
  · simp only [h0, map_zero, smul_zero]
  have hre : (((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) := by
    have e0 : ((‖LinearMap.adjoint th (th u)‖ : ℝ) : ℂ) ^ 2 = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * ((‖th u‖ : ℝ) : ℂ) ^ 2 :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (LinearMap.adjoint th (th u))).symm.trans
        ((key u hu (th u)).trans (congrArg (fun z => (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * z) (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (th u))))
    have hn : ((‖th u‖ : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.2 h0)
    have e' : (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) = ((‖LinearMap.adjoint th (th u)‖ ^ 2 / ‖th u‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [eq_div_iff hn]
      exact e0.symm
    exact (congrArg (fun z : ℂ => ((z.re : ℝ) : ℂ)) e').trans ((congrArg (fun r : ℝ => (r : ℂ)) (Complex.ofReal_re _)).trans e'.symm)
  refine ext_inner_right ℂ fun y => ?_
  calc inner ℂ (th (LinearMap.adjoint th (th u))) y = inner ℂ (LinearMap.adjoint th (th u)) (LinearMap.adjoint th y) :=
        (LinearMap.adjoint_inner_right th _ y).symm
    _ = (K * K * ((Module.finrank ℂ c.W : ℂ) * C)) * inner ℂ (th u) y := key u hu y
    _ = inner ℂ ((((K * K * ((Module.finrank ℂ c.W : ℂ) * C)).re : ℝ) : ℂ) • th u) y :=
      (congrArg (fun z => z * inner ℂ (th u) y) ((Complex.conj_ofReal _).trans hre)).symm.trans (inner_smul_left _ _ _).symm

end GlobalTheory.ConjScalarProof
end
