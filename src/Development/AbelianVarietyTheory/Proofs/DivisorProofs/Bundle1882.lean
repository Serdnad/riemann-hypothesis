module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle110
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertTwUnit

theorem cast_finsum_rat {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h1 : (Function.support f).Infinite := h
    have h2 : (Function.support fun i => (f i : ℂ)).Infinite := by
      have e : (Function.support fun i => (f i : ℂ)) = Function.support f := by
        ext i; simp
      rw [e]; exact h1
    rw [finsum_of_infinite_support h1, finsum_of_infinite_support h2, Rat.cast_zero]

theorem twisted_unit_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  intro E _ _ _ hU w hw K e hc hr hv hq a Q hm hd hs hQ
  unfold stTw IsCsr at *
  unfold clSum
  have hQ' : C ((cj w) (Q.coeff 0)) * Q = (Q.map (cj w)).reverse := hQ.resolve_left hw
  have hcomm : e.symm.toRingHom.comp (cj w) = (K.c : K.E →+* K.E).comp e.symm.toRingHom := by
    ext y
    have h := congrArg e.symm (hc (e.symm y))
    simp only [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h
    simp [h]
  have hrev : ∀ p : (w.adicCompletion E)[X],
      (p.reverse).map e.symm.toRingHom = (p.map e.symm.toRingHom).reverse := by
    intro p
    unfold Polynomial.reverse
    rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective, Polynomial.reflect_map]
  have hPr : C (K.c ((Q.map e.symm.toRingHom).coeff 0)) * Q.map e.symm.toRingHom =
      ((Q.map e.symm.toRingHom).map (K.c : K.E →+* K.E)).reverse := by
    have h1 := congrArg (Polynomial.map e.symm.toRingHom) hQ'
    have h0 : e.symm.toRingHom ((cj w) (Q.coeff 0)) = K.c ((Q.map e.symm.toRingHom).coeff 0) := by
      rw [Polynomial.coeff_map]
      exact RingHom.congr_fun hcomm (Q.coeff 0)
    rw [Polynomial.map_mul, Polynomial.map_C, h0] at h1
    rw [h1, hrev, Polynomial.map_map, hcomm, ← Polynomial.map_map]
  obtain ⟨B, hg, hP⟩ := GlobalTheory.T.exists_selfReciprocalInvAlg_with_poly K (Q.map e.symm.toRingHom) (hm.map _) hPr
  have hsep : B.P.Separable := by
    rw [hP]
    exact hs.map
  refine ⟨B, hg, hP, ?_⟩
  have hε : (-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1 := neg_one_pow_eq_or B.A (a - 1)
  obtain ⟨β₀, hβ₀, hX⟩ := GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual K B hg hsep _ hε
  obtain ⟨F, hF⟩ := GlobalTheory.T.twistedConjugacyClasses_equiv_unitsModNorms_nonsplit E hU w hw K e hc hr a Q hm hd hs B hg hP β₀ hβ₀
  have hterm : ∀ k : B.Cl, twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (F k).1.rep
      ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = ((B.N k.rep : ℚ) : ℂ) := by
    intro k
    obtain ⟨b, hb⟩ := hF k
    have hu : B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = ((Quot.out k).1 : B.Aˣ) := (Quot.out k).2
    have hβ : B.σ ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) =
        (β₀ * (Quot.out k).1 : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
      rw [Units.val_mul, map_mul, hβ₀, hu]
      ring
    have h := GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount E hU w hw K e hc hr a B hsep (β₀ * (Quot.out k).1) _ hε hβ b (F k).1.rep
      (fun i j => by rw [Units.val_mul]; exact hb i j)
    rw [h, Units.val_mul, hX _ hu]
    rfl
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul]
  simp only [← finsum_eq_if]
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv F]
  simp only [hterm]
  exact (cast_finsum_rat _).symm

end GlobalTheory.InertTwUnit
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

theorem GlobalTheory.HeisLatVac.vacFn_apply_add : ∀ {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    ∀ u ∈ Λ, GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀ (x₀ + u.1) = χ u * ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
  intro K κ _ _ _ ψ₀ Λ χ x₀ hcoc hχ0 u hu
  have hex : ∃ v ∈ Λ, x₀ + u.1 = x₀ + v.1 := ⟨u, hu, rfl⟩
  unfold GlobalTheory.HeisLatVac.vacFn
  rw [dite_eq_left hex]
  have hspec := hex.choose_spec
  generalize hex.choose = u' at hspec ⊢
  obtain ⟨hu', heq⟩ := hspec
  have h1 : u.1 = u'.1 := add_left_cancel heq
  have hδ : ((0 : κ → K), u.2 - u'.2) ∈ Λ := by
    have : u - u' = ((0 : κ → K), u.2 - u'.2) := Prod.ext (by simp [h1]) rfl
    rw [← this]; exact Λ.sub_mem hu hu'
  have hsum : u' + ((0 : κ → K), u.2 - u'.2) = u := Prod.ext (by simp [h1]) (by simp)
  have hc := hcoc u' hu' _ hδ
  rw [hsum] at hc
  rw [hc, hχ0 _ hδ, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dotProduct_sub, zero_dotProduct, h1]
  ring
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

namespace GlobalTheory.HeisLatVac

theorem vacFn_apply_base_add {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hY : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (u : (κ → K) × (κ → K)) (hu : u ∈ Λ) :
    vacFn ψ₀ Λ χ x₀ (x₀ + u.1) = χ u * ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
  have h : ∃ u' ∈ Λ, x₀ + u.1 = x₀ + u'.1 := ⟨u, hu, rfl⟩
  rw [vacFn, dite_eq_left h]
  obtain ⟨hu', he⟩ := h.choose_spec
  set u' := h.choose
  have h1 : u.1 = u'.1 := add_left_cancel he
  have hd : ((0 : κ → K), u.2 - u'.2) = u - u' := by
    ext <;> simp [h1]
  have hdm : ((0 : κ → K), u.2 - u'.2) ∈ Λ := hd ▸ sub_mem hu hu'
  have hsum : u = u' + ((0 : κ → K), u.2 - u'.2) := by rw [hd]; abel
  have hχ : χ u = χ u' * ψ₀ (x₀ ⬝ᵥ (u.2 - u'.2)) * ψ₀ (⅟(2 : K) * (u'.1 ⬝ᵥ (u.2 - u'.2) - (0 : κ → K) ⬝ᵥ u'.2)) := by
    conv_lhs => rw [hsum]
    rw [hco u' hu' _ hdm, hY _ hdm]
  rw [hχ, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  rw [h1]
  simp only [dotProduct_sub, zero_dotProduct]
  ring

theorem schr_vacFn : ∀ {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, ∀ w ∈ Λ, ψ₀ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) = 1) →
    ∀ w ∈ Λ, GlobalTheory.WeilM.schr ψ₀ w (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) = χ w • GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀ := by
  intro K κ _ _ _ ψ₀ Λ χ x₀ hco hY hiso w hw
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  by_cases hx : ∃ u ∈ Λ, x = x₀ + u.1
  · obtain ⟨u, hu, rfl⟩ := hx
    have e : x₀ + u.1 + w.1 = x₀ + (u + w).1 := by simp [add_assoc]
    rw [e, vacFn_apply_base_add ψ₀ Λ χ x₀ hco hY (u + w) (add_mem hu hw),
      vacFn_apply_base_add ψ₀ Λ χ x₀ hco hY u hu, hco u hu w hw]
    have h1 : ψ₀ ((x₀ + u.1) ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2)) *
        ψ₀ (-(x₀ ⬝ᵥ (u + w).2) - ⅟(2 : K) * ((u + w).1 ⬝ᵥ (u + w).2)) =
        ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      have : (x₀ + u.1) ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) + ⅟(2 : K) * (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) +
          (-(x₀ ⬝ᵥ (u + w).2) - ⅟(2 : K) * ((u + w).1 ⬝ᵥ (u + w).2)) =
          (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) + (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
        simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
        linear_combination (-(w.1 ⬝ᵥ u.2)) * (invOf_mul_self (2 : K))
      rw [this, AddChar.map_add_eq_mul, hiso u hu w hw, one_mul]
    rw [← h1]
    ring
  · have hx' : ¬∃ u ∈ Λ, x + w.1 = x₀ + u.1 := by
      rintro ⟨u', hu', he⟩
      refine hx ⟨u' - w, sub_mem hu' hw, ?_⟩
      rw [Prod.fst_sub, ← add_sub_assoc, ← he, add_sub_cancel_right]
    simp only [vacFn, dif_neg hx, dif_neg hx', mul_zero]

end GlobalTheory.HeisLatVac
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat.PairLatLattice

variable {E : Type} [Field E] [NumberField E]

theorem scLat_isLattice {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0)
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (GlobalTheory.SkewLat.scLat 𝔞 Λ) := by
  have hinv : 𝔞⁻¹ ≠ 0 := inv_ne_zero h𝔞
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hinv)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr h𝔞)
  have hb' : b ∈ 𝔞⁻¹ := hb
  have ha' : a ∈ 𝔞 := ha
  refine ⟨?_, ?_⟩
  ·
    let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
      (LinearMap.lsmul E (Fin n → E) b⁻¹).restrictScalars (𝓞 E)
    have hle : GlobalTheory.SkewLat.scLat 𝔞 Λ ≤ Λ.map f := by
      intro y hy
      refine ⟨b • y, hy b hb', ?_⟩
      simp [f, smul_smul, mul_inv_cancel₀ hb0]
    exact Submodule.FG.of_le (Submodule.FG.map f hΛ.fg) hle
  ·
    have hmem : ∀ y ∈ Λ, a • y ∈ GlobalTheory.SkewLat.scLat 𝔞 Λ := by
      intro y hy c hc
      have hca : c * a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← inv_mul_cancel₀ h𝔞]
        exact FractionalIdeal.mul_mem_mul hc ha'
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp hca
      rw [smul_smul, ← hr, algebraMap_smul]
      exact Λ.smul_mem r hy
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem prod_span_eq_top {a b : ℕ} {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsFullLattice E M) (hN : Submodule.IsFullLattice E N) :
    Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set ((Fin a → E) × (Fin b → E))) = ⊤ := by
  set S := Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set ((Fin a → E) × (Fin b → E)))
  have hl : ∀ x : Fin a → E, (x, 0) ∈ S := by
    have : Submodule.span E (M : Set (Fin a → E)) ≤ S.comap (LinearMap.inl E (Fin a → E) (Fin b → E)) := by
      refine Submodule.span_le.mpr fun m hm => ?_
      exact Submodule.subset_span (show (m, (0 : Fin b → E)) ∈ M.prod N from ⟨hm, N.zero_mem⟩)
    intro x
    have hx : x ∈ Submodule.span E (M : Set (Fin a → E)) := by rw [Submodule.IsFullLattice.span_eq_top (self := hM)]; trivial
    exact this hx
  have hr : ∀ y : Fin b → E, (0, y) ∈ S := by
    have : Submodule.span E (N : Set (Fin b → E)) ≤ S.comap (LinearMap.inr E (Fin a → E) (Fin b → E)) := by
      refine Submodule.span_le.mpr fun m hm => ?_
      exact Submodule.subset_span (show ((0 : Fin a → E), m) ∈ M.prod N from ⟨M.zero_mem, hm⟩)
    intro y
    have hy : y ∈ Submodule.span E (N : Set (Fin b → E)) := by rw [Submodule.IsFullLattice.span_eq_top (self := hN)]; trivial
    exact this hy
  apply top_unique
  intro ⟨x, y⟩ _
  simpa using S.add_mem (hl x) (hr y)
theorem pairLat_isLattice {a b d : ℕ} {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsLattice E M) (hN : Submodule.IsLattice E N) (e : Fin a ⊕ Fin b ≃ Fin d) :
    Submodule.IsLattice E (GlobalTheory.SkewLat.pairLat M N e) := by
  let φ : (Fin d → E) ≃ₗ[E] (Fin a → E) × (Fin b → E) :=
    (LinearEquiv.funCongrLeft E E e).trans (LinearEquiv.sumArrowLequivProdArrow _ _ E E)
  have hφ : GlobalTheory.SkewLat.pairLat M N e = (M.prod N).map (φ.symm.restrictScalars (𝓞 E)).toLinearMap := by
    ext x
    rw [Submodule.mem_map_equiv, GlobalTheory.SkewLat.mem_pairLat]
    rfl
  rw [hφ]
  refine ⟨Submodule.FG.map _ (Submodule.FG.prod hM.fg hN.fg), ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.SkewLat.PairLatLattice

open GlobalTheory.SkewLat.PairLatLattice in
theorem GlobalTheory.SkewLat.pairLat_scLat_isLattice : ∀ {E : Type} [Field E] [NumberField E] {a b d : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E}, 𝔞 ≠ 0 →
    ∀ {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}, Submodule.IsLattice E ΛA →
    Submodule.IsLattice E ΛB → ∀ (e : Fin a ⊕ Fin b ≃ Fin d),
    Submodule.IsLattice E (GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat 𝔞 ΛA) (GlobalTheory.SkewLat.scLat 𝔞 ΛB) e) := by
  intro E _ _ a b d 𝔞 h𝔞 ΛA ΛB hA hB e
  exact pairLat_isLattice (scLat_isLattice h𝔞 hA) (scLat_isLattice h𝔞 hB) e
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem zCo_iota {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hch : GlobalTheory.FockCompare.Chart θ σ) {S T : HSp D}
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (z : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) =
      fun τ => (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ := by
  funext τ
  have e : compAt θ τ (GlobalTheory.FockCompare.iotaW σ T S z) = Matrix.of (z τ) := congrFun (hch.pi_iota T S z) τ
  simp only [GlobalTheory.FockPos.zCo, e]
  rfl

theorem frAt_inv {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt fr τ)⁻¹ * GlobalTheory.FockPos.frAt fr τ = 1 ∧ GlobalTheory.FockPos.frAt fr τ * (GlobalTheory.FockPos.frAt fr τ)⁻¹ = 1 :=
  ⟨Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ)),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne fr τ))⟩

theorem coord_back {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) (τ : D.what₂.Tau) :
    (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹) *
      GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) := by
  have h1 := (frAt_inv frS τ).1
  have h2 := (frAt_inv frT τ).1
  calc _ = ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * GlobalTheory.FockPos.frAt frT τ) * Matrix.of (Z τ) *
        ((GlobalTheory.FockPos.frAt frS τ)⁻¹ * GlobalTheory.FockPos.frAt frS τ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ThetaLawOF

namespace GlobalTheory.ThetaLawOF
variable {D : D7}

theorem trace_conjTranspose_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    (Aᴴ * B).trace = ∑ a, ∑ b, starRingEnd ℂ (A a b) * B a b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

theorem omO_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (x y : GlobalTheory.FockCompare.RW T S) :
    GlobalTheory.VacUnique.omO S T x y = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (y τ) * GlobalTheory.FockPos.frAt frS τ) a b) *
        ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (x τ) * GlobalTheory.FockPos.frAt frS τ) a b)).re := by
  rw [GlobalTheory.VacUnique.omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (Matrix.of (x τ)) (Matrix.of (y τ))).re = _
  rw [GlobalTheory.FockJetOrigin.hAt_coord (BS := fun τ => GlobalTheory.FockPos.frAt frS τ)
    (BT := fun τ => GlobalTheory.FockPos.frAt frT τ) (GlobalTheory.FockPos.frAt_on frS hS τ) (GlobalTheory.FockPos.frAt_on frT hT τ),
    trace_conjTranspose_mul, GlobalTheory.FockJetOrigin.realPlace_cmTrace_zero_element_eq_I_mul_abs, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]

theorem torusHermitianForm_scaled_coordinate_eq {N N' : ℕ} {δ : ℂ} (hδ : δ ≠ 0) (Z X : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Z) (δ • X) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b) := by
  have e : (∑ τ, ∑ i, ∑ j, (δ • Z) τ i j * starRingEnd ℂ ((δ • X) τ i j)) =
      (δ * starRingEnd ℂ δ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hL : (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ).abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ := rfl
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [Formalism.MainNotions.TaylorLogMetric.Hf, e, hL, GlobalTheory.MomDict.area_lamOf D D.host.ccK δ D.host.ccK_ne_bot, hxi, Complex.mul_conj]
  have h0 : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hδ).ne'
  have h1 : ((Ideal.absNorm D.host.ccK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0)
  have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : Real.sqrt D.host.d ≠ 0)
  push_cast
  field_simp

theorem al_mul_self {N N' : ℕ} (T0 : Formalism.MainNotions.TaylorLogMetric.Tor D) (x : Formalism.MainNotions.TaylorLogMetric.VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.al D T0 x * Formalism.MainNotions.TaylorLogMetric.al D T0 x = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.al, ← mul_zpow, show (-1 : ℂ) * -1 = 1 by norm_num, _root_.one_zpow]

theorem entry (zz xx : ℂ) (r : ℝ) :
    (Real.pi : ℂ) * Complex.I * ((2 * (Complex.I * (r : ℂ) * (starRingEnd ℂ zz * xx)).re : ℝ) : ℂ) -
      2 * (Real.pi : ℂ) * (r : ℂ) * (zz * starRingEnd ℂ xx) - (Real.pi : ℂ) * (r : ℂ) * (xx * starRingEnd ℂ xx) =
      (Real.pi : ℂ) * (r : ℂ) * ((‖zz‖ ^ 2 : ℝ) - (‖zz + xx‖ ^ 2 : ℝ) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring

end GlobalTheory.ThetaLawOF

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem fock_monomial_zero_of_on : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), IsStdChar D ψ (-1) → IsInfFam θ → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ (F : WO S T → ℂ) (Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ), Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → F w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ := by
  intro D ψ θ S T frS frT hψ hθ hS hT F Φ hΦ hF k
  have hS' : ∀ τ, (frAt frS τ)ᴴ * gramAt D S τ * frAt frS τ = 1 := frAt_on frS hS
  have hT' : ∀ τ, (frAt frT τ)ᴴ * gramAt D T τ * frAt frT τ = 1 := frAt_on frT hT
  exact GlobalTheory.FockJetOrigin.fock_monomial_zero θ hS' hT' hψ hθ F Φ hΦ (fun w hw => hF w hw) k

end GlobalTheory.FockPos
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.riemannianHaar_frameBall_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → riemHaar Ψ G x (frBall Ψ G x ε) ≤ ENNReal.ofReal ((8 * ε) ^ (Ψ.card * (r ^ 2 - 1))) := by
  first | exact @GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le | exact GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le | (intros; apply GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV


theorem _root_.GlobalTheory.T.exists_finset_cosetReps_bounded_half_points : ∀ {D : D7} {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ), IsIdemSum e P → ∃ R : Finset (Mx D b a), (∀ r ∈ R, IsHalf e r ∧ IsSmall P β' β (-(n : ℤ)) r) ∧ (∀ t, IsHalf e t → IsSmall P β' β (-(n : ℤ)) t → ∃ r ∈ R, IsSmall P β' β n (t - r)) ∧ ∀ r ∈ R, ∀ r' ∈ R, IsSmall P β' β n (r - r') → r = r' := by
  first | exact @GlobalTheory.FunObj.exists_finset_cosetReps | exact GlobalTheory.FunObj.exists_finset_cosetReps | (intros; apply GlobalTheory.FunObj.exists_finset_cosetReps <;> assumption)
end
