module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle184
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle336
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle197
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.SwapFock

open MvPolynomial

lemma sg_mul_self (e : Bool) : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e = 1 := by
  cases e <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]

lemma conj_sg (e : Bool) : starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e := by
  cases e <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]

variable {a b : ℕ}

def swSign (ε : Fin a → Bool) (ε' : Fin b → Bool) (n : Fin b × Fin a) : ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' n.1) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε n.2)

variable (ε : Fin a → Bool) (ε' : Fin b → Bool)

lemma swSign_mul_self (n : Fin b × Fin a) : swSign ε ε' n * swSign ε ε' n = 1 := by
  unfold swSign
  rw [mul_mul_mul_comm, sg_mul_self, sg_mul_self, one_mul]

lemma conj_swSign (n : Fin b × Fin a) : starRingEnd ℂ (swSign ε ε' n) = swSign ε ε' n := by
  unfold swSign
  rw [map_mul, conj_sg, conj_sg]

lemma swSign_swap (n : Fin b × Fin a) : swSign ε' ε n.swap = swSign ε ε' n := by
  unfold swSign
  exact mul_comm _ _

lemma C_swSign_mul_self {σ : Type*} (n : Fin b × Fin a) :
    (C (swSign ε ε' n) : MvPolynomial σ ℂ) * C (swSign ε ε' n) = 1 := by
  rw [← map_mul, swSign_mul_self, map_one]

lemma C_sg_mul_self {σ : Type*} (e : Bool) :
    (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) : MvPolynomial σ ℂ) * C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) = 1 := by
  rw [← map_mul, sg_mul_self, map_one]

def swapHom : LPol b a →+* LPol a b :=
  eval₂Hom ((C : ℂ →+* LPol a b).comp (starRingEnd ℂ)) fun n => C (swSign ε ε' n) * X n.swap

@[simp] lemma swapHom_C (c : ℂ) : swapHom ε ε' (C c) = C (starRingEnd ℂ c) := by
  simp [swapHom]

@[simp] lemma swapHom_X (n : Fin b × Fin a) : swapHom ε ε' (X n) = C (swSign ε ε' n) * X n.swap := by
  simp [swapHom]

lemma swapHom_smul (c : ℂ) (P : LPol b a) : swapHom ε ε' (c • P) = starRingEnd ℂ c • swapHom ε ε' P := by
  rw [smul_eq_C_mul, map_mul, swapHom_C, smul_eq_C_mul]

lemma swapHom_comp : (swapHom ε' ε).comp (swapHom ε ε') = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro n
    rw [RingHom.comp_apply, swapHom_X, map_mul, swapHom_C, swapHom_X, conj_swSign, swSign_swap,
      Prod.swap_swap, ← mul_assoc, C_swSign_mul_self, one_mul, RingHom.id_apply]

lemma swapHom_pderiv (n : Fin b × Fin a) (Q : LPol b a) :
    swapHom ε ε' (pderiv n Q) = C (swSign ε ε' n) * pderiv n.swap (swapHom ε ε' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _), mul_add]
  | mul_X p m hp =>
    have hs := C_swSign_mul_self (σ := Fin a × Fin b) ε ε' n
    by_cases h : n = m
    · subst h
      simp only [pderiv_mul, pderiv_X_self, map_add (f := _), map_mul, hp, swapHom_X, pderiv_C, mul_one, zero_mul, zero_add]
      linear_combination (-(swapHom ε ε' p)) * hs
    · have h' : m.swap ≠ n.swap := fun e => h (Prod.swap_injective e).symm
      simp only [pderiv_mul, pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne h', map_mul, hp, swapHom_X,
        pderiv_C, mul_zero, zero_mul, add_zero, zero_add]
      ring

lemma swapHom_rai (i : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' (rai ε ε' i j Q) = rai ε' ε j i (swapHom ε ε' Q) := by
  unfold rai
  have hs := C_sg_mul_self (σ := Fin a × Fin b) (ε j)
  by_cases h : ε' i = ε j
  · rw [if_pos h, if_pos h.symm]
    simp only [LinearMap.smul_apply, LinearMap.mulLeft_apply, swapHom_smul, swapHom_C, map_mul, swapHom_X, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * X (j, i) * swapHom ε ε' Q) * hs
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.smul_apply, LinearMap.neg_apply, Derivation.coeFn_coe, map_neg, swapHom_smul, swapHom_C,
      swapHom_pderiv, map_mul, conj_sg, swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (-(C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * pderiv (j, i) (swapHom ε ε' Q))) * hs

lemma swapHom_low (i : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' (low ε ε' i j Q) = low ε' ε j i (swapHom ε ε' Q) := by
  unfold low
  have hs := C_sg_mul_self (σ := Fin a × Fin b) (ε j)
  by_cases h : ε' i = ε j
  · rw [if_pos h, if_pos h.symm]
    simp only [LinearMap.smul_apply, Derivation.coeFn_coe, swapHom_smul, swapHom_C, swapHom_pderiv, map_mul, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * pderiv (j, i) (swapHom ε ε' Q)) * hs
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.smul_apply, LinearMap.mulLeft_apply, swapHom_smul, swapHom_C, map_mul, swapHom_X, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * X (j, i) * swapHom ε ε' Q) * hs

lemma swapHom_half (c : Prop) [Decidable c] (Q : LPol b a) :
    swapHom ε ε' ((if c then (1 / 2 : ℂ) • (1 : Module.End ℂ (LPol b a)) else 0) Q) =
      (if c then (1 / 2 : ℂ) • (1 : Module.End ℂ (LPol a b)) else 0) (swapHom ε ε' Q) := by
  split_ifs
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, swapHom_smul]
    rw [map_div₀, map_one, map_ofNat]
  · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

lemma swapHom_termT (i l : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' ((rai ε ε' i j * low ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0) Q) =
      (rai ε' ε j i * low ε' ε j l + if i = l then (1 / 2 : ℂ) • 1 else 0) (swapHom ε ε' Q) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, Module.End.mul_apply, swapHom_rai,
    swapHom_low, swapHom_half]

lemma swapHom_termS (i : Fin b) (j k : Fin a) (Q : LPol b a) :
    swapHom ε ε' ((rai ε ε' i j * low ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0) Q) =
      (rai ε' ε j i * low ε' ε k i + if j = k then (1 / 2 : ℂ) • 1 else 0) (swapHom ε ε' Q) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, Module.End.mul_apply, swapHom_rai,
    swapHom_low, swapHom_half]

def swapEquiv : LPol b a ≃+ LPol a b :=
  { toFun := swapHom ε ε'
    invFun := swapHom ε' ε
    left_inv := fun P => RingHom.congr_fun (swapHom_comp ε ε') P
    right_inv := fun P => RingHom.congr_fun (swapHom_comp ε' ε) P
    map_add' := map_add _ }

lemma swapEquiv_apply (P : LPol b a) : swapEquiv ε ε' P = swapHom ε ε' P := rfl

theorem locS_locT_exchange : ∀ (a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool), ∃ j : LPol b a ≃+ LPol a b,
    (∀ (c : ℂ) P, j (c • P) = conj c • j P) ∧ ∀ P : LPol b a,
      (∀ Y : Matrix (Fin b) (Fin b) ℂ, j (locT ε ε' Y P) = locS ε' ε (Y.map (starRingEnd ℂ)) (j P)) ∧
        ∀ X : Matrix (Fin a) (Fin a) ℂ, j (locS ε ε' (X.map (starRingEnd ℂ)) P) = locT ε' ε X (j P) := by
  intro a b ε ε'
  refine ⟨swapEquiv ε ε', fun c P => ?_, fun P => ⟨fun Y => ?_, fun X => ?_⟩⟩
  · rw [swapEquiv_apply, swapEquiv_apply, swapHom_smul]
  · rw [swapEquiv_apply, swapEquiv_apply]
    unfold locT locS

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, swapHom_smul, swapHom_termT, Matrix.map_apply]
  · rw [swapEquiv_apply, swapEquiv_apply]
    unfold locT locS

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, swapHom_smul, swapHom_termS, Matrix.map_apply,
    starRingEnd_self_apply]

end GlobalTheory.Chain.RealIt.SwapFock

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

variable {D : D7}

def indQ (D : D7) (Q : Finset (Pl D)) : Af D.host.F := ∑ v ∈ Q, singleV D.host.F v 1

def idemQ (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (indQ D Q)

def idemQc (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (1 - indQ D Q)

open Classical in
theorem evalV_indQ (Q : Finset (Pl D)) (w : Pl D) :
    evalV D.host.F w (indQ D Q) = if w ∈ Q then 1 else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [indQ, map_sum]
  have h : ∀ v ∈ Q, evalV D.host.F w (singleV D.host.F v 1) = if w = v then 1 else 0 := by
    intro v _
    by_cases hwv : w = v
    · subst hwv
      rw [if_pos rfl]
      change (singleV D.host.F w 1) w = 1
      exact RestrictedProduct.single_eq_same _ _ _
    · rw [if_neg hwv]
      change (singleV D.host.F v 1) w = 0
      exact RestrictedProduct.single_eq_of_ne (fun u : Pl D => u.adicCompletionIntegers D.host.F)
        (1 : Fv D.host.F v) hwv
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

theorem parts_pairA (α : Af D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
        evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  · exact (placeIdempotent_infinite_and_finite_components D w _ α rfl).2 w

open Classical in
theorem parts_idemQ (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = if w ∈ Q then 1 else 0 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQ, (parts_pairA _).2 w, evalV_indQ]
  split_ifs
  · rfl
  · exact TensorProduct.zero_tmul _ _

open Classical in
theorem parts_idemQc (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = if w ∈ Q then 0 else 1 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQc, (parts_pairA _).2 w, map_sub, map_one, evalV_indQ]
  split_ifs
  · rw [sub_self]; exact TensorProduct.zero_tmul _ _
  · rw [sub_zero]; rfl

theorem mem_idAt_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idAt D P ↔ c * a = a := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
  constructor
  · rintro ⟨ha0, haw⟩
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [if_pos h, one_mul, sub_self]
      · rw [if_neg h, haw w h, zero_mul, sub_zero]
  · intro ha
    refine ⟨?_, fun w hw => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, hc w, if_neg hw, zero_mul]

theorem mem_idOff_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idOff D P ↔ c * a = 0 := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  constructor
  · intro ha
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_mul, h0, zero_mul]
    · intro w
      rw [RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [ha w h, mul_zero]
      · rw [if_neg h, zero_mul]
  · intro ha w hw
    have := congrArg (compAt D w) ha
    rwa [RingHom.map_mul, hc w, if_pos hw, one_mul, RingHom.map_zero] at this

open Classical in
theorem mem_idAt_Q_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∈ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQ D Q) * a = a :=
  mem_idAt_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (parts_idemQ Q).2 a

open Classical in
theorem mem_idAt_Qc_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∉ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQc D Q) * a = a :=
  mem_idAt_iff_mul (· ∉ Q) _ (parts_idemQc Q).1
    (fun w => by rw [(parts_idemQc Q).2 w]; by_cases h : w ∈ Q <;> simp [h]) a

theorem idemQ_mul_self (Q : Finset (Pl D)) : idemQ D Q * idemQ D Q = idemQ D Q := by
  have e : (idemQ D Q * idemQ D Q : AF D.host.F) = pairA D.host.F 0 (indQ D Q * indQ D Q) :=
    Prod.ext (mul_zero _) rfl
  rw [e, idemQ]
  congr 1
  apply RestrictedProduct.ext
  intro w
  have h := evalV_indQ (D := D) Q w
  change evalV D.host.F w (indQ D Q * indQ D Q) = evalV D.host.F w (indQ D Q)
  rw [map_mul, h]
  split_ifs <;> simp

theorem one_sub_idemQ_mul_self (Q : Finset (Pl D)) :
    (1 - idemQ D Q) * (1 - idemQ D Q) = 1 - idemQ D Q := by
  have h := idemQ_mul_self (D := D) Q
  linear_combination h

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

def cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) : GA D V →* GA D V :=
  GlobalTheory.UnitaryIdemCut.cutUJ (sigR (AF D.host.F) D.sp.cm.sig) (JR (AF D.host.F) V.gram)
    (algebraMap (AF D.host.F) (AE D) ε) (by rw [← map_mul, hε])
    (GlobalTheory.UnitaryIdemCut.sigR_algebraMap (AF D.host.F) D.sp.cm.sig ε)

theorem mt_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutG V ε hε g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g +
      (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

end GlobalTheory.FinPl.SetCut

end
end

section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ContDiff

namespace GlobalTheory.EisCont.CentreFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isRealLine_conj (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.EisCont.CentreFinite
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealPlaceTheta

theorem exists_record_theta_all :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, ChosenSeries X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X := by
  intro hD hH
  obtain ⟨X, hX, d1, q5, a1, a2, a3, a5⟩ := GlobalTheory.RealPlaceTheta.exists_record_theta hD hH
  exact ⟨X, hX, a1, a2, a3,
    GlobalTheory.T.no_thetaLift_discreteSeries_smaller_tower_member X (GlobalTheory.FockDeg.degrees_and_adjoints X) (GlobalTheory.FockAlg.fock_structure X) d1 q5, a5⟩

end GlobalTheory.RealPlaceTheta
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPlacesDatum_mul_right_source_level : ∀ (D : D7) (a b : ℕ) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)), (∀ PP ∈ L.Pg, G PP ∈ blockTri (blkOf L.r L.t)) → ∀ hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)) ∈ L.P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG L χ (fun PP => y PP * (G PP).val) = ((L.P.chi ⟨_, hP⟩ * (∏ PP ∈ L.Pg, ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP))) * ∏ PP ∈ L.Pg, (χ PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) * omegaG L χ y := by
  first | exact @GlobalTheory.ChainOnto.RightMove.omegaG_mul_right | exact GlobalTheory.ChainOnto.RightMove.omegaG_mul_right | (intros; apply GlobalTheory.ChainOnto.RightMove.omegaG_mul_right <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPlacesDatum_inv_left_mul_target_level : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, H PP ∈ blockTri (blkOf r t)) → ∀ hP : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)) ∈ P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP) = (((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))⁻¹ * ∏ PP ∈ Pg, χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ) * omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) y := by
  first | exact @GlobalTheory.ChainOnto.omegaG_levelP_move | exact GlobalTheory.ChainOnto.omegaG_levelP_move | (intros; apply GlobalTheory.ChainOnto.omegaG_levelP_move <;> assumption)
end
