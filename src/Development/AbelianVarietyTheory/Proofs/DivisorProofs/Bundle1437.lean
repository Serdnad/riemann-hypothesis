module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFramesOfKilledNilpotentDerivativ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureWeylCellOddUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW

variable {n : ℕ}

open scoped Matrix

theorem secMat_of_ne (ρ j : Fin n) (v : Fin n → ℂ) {i : Fin n} (hi : i ≠ ρ) (l : Fin n) :
    secMat ρ j v i l = if l = Equiv.swap j ρ i then 1 else 0 := by
  simp [secMat, hi]

theorem secMat_self (ρ j : Fin n) (v : Fin n → ℂ) (l : Fin n) :
    secMat ρ j v ρ l = if l ≤ ρ then v l else 0 := by
  simp [secMat]

theorem swap_of_lt' {ρ j i : Fin n} (hj : j ≤ ρ) (hi : ρ < i) : Equiv.swap j ρ i = i :=
  Equiv.swap_apply_of_ne_of_ne (lt_of_le_of_lt hj hi).ne' hi.ne'

theorem isUnit_secMat (ρ j : Fin n) (hj : j ≤ ρ) (v : Fin n → ℂ) (hv : v j ≠ 0) :
    IsUnit (Matrix.of (secMat ρ j v)) := by
  rw [← Matrix.vecMul_injective_iff_isUnit]
  have key : ∀ e : Fin n → ℂ, e ᵥ* Matrix.of (secMat ρ j v) = 0 → e = 0 := by
    intro e he
    have hcol : ∀ l, ∑ i, e i * secMat ρ j v i l = 0 := fun l => by
      have := congrFun he l
      simpa [Matrix.vecMul, dotProduct] using this
    have hρ : e ρ = 0 := by
      have h := hcol j
      rw [Finset.sum_eq_single ρ] at h
      · rw [secMat_self, if_pos hj] at h
        exact (mul_eq_zero.1 h).resolve_right hv
      · intro i _ hi
        rw [secMat_of_ne _ _ _ hi, if_neg, mul_zero]
        intro h'
        apply hi
        calc i = Equiv.swap j ρ (Equiv.swap j ρ i) := (Equiv.swap_apply_self _ _ _).symm
          _ = Equiv.swap j ρ j := by rw [← h']
          _ = ρ := Equiv.swap_apply_left _ _
      · simp
    funext i
    by_cases hi : i = ρ
    · rw [hi]; exact hρ
    · have h := hcol (Equiv.swap j ρ i)
      rw [Finset.sum_eq_single i] at h
      · rw [secMat_of_ne _ _ _ hi, if_pos rfl, mul_one] at h
        exact h
      · intro i' _ hi'
        by_cases h'' : i' = ρ
        · rw [h'', hρ, zero_mul]
        · rw [secMat_of_ne _ _ _ h'', if_neg, mul_zero]
          intro h3
          exact hi' ((Equiv.swap j ρ).injective h3).symm
      · simp
  intro c d hcd
  have := key (c - d) (by
    change (c - d) ᵥ* _ = 0
    rw [Matrix.sub_vecMul]
    exact sub_eq_zero.2 hcd)
  exact sub_eq_zero.1 this

def secLin (ρ : Fin n) : (Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i l => if i = ρ ∧ l ≤ ρ then v l else 0
      map_add' := fun v w => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h]
      map_smul' := fun c v => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h] }

theorem secMat_eq_add (ρ j : Fin n) (v : Fin n → ℂ) : secMat ρ j v = secMat ρ j 0 + secLin ρ v := by
  funext i l
  by_cases hi : i = ρ
  · subst hi
    by_cases hl : l ≤ i <;> simp [secMat, secLin, hl]
  · simp [secMat, secLin, hi]

theorem secMat_main : ∀ (n : ℕ) (ρ j : Fin n), j ≤ ρ → (∀ v : Fin n → ℂ, v j ≠ 0 → IsUnit (Matrix.of (secMat ρ j v))) ∧ (∀ g ∈ levSet n (ρ + 1), rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) j ≠ 0 → g * (toGL (Matrix.of (secMat ρ j (rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ)))))⁻¹ ∈ levSet n ρ) ∧ ∃ L : (Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ), ∀ v, secMat ρ j v = secMat ρ j 0 + L v := by
  intro n ρ j hj
  refine ⟨fun v hv => isUnit_secMat ρ j hj v hv, ?_, secLin ρ, secMat_eq_add ρ j⟩
  intro g hg hgj
  set v := rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) with hv
  have hS := isUnit_secMat ρ j hj v hgj
  set S := toGL (Matrix.of (secMat ρ j v)) with hSdef
  have hSv : (S : Matrix (Fin n) (Fin n) ℂ) = Matrix.of (secMat ρ j v) := val_toGL hS
  have hSlev : S ∈ levSet n (ρ + 1) := by
    intro i hi
    have hiρ : ρ < i := by rw [Fin.lt_def]; omega
    refine ⟨fun l hl => ?_, ?_⟩
    · rw [hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_neg hl.ne]
    · rw [hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_pos rfl]
  have hp : g * S⁻¹ ∈ levSet n (ρ + 1) :=
    (GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).1 g hg _ ((GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 S hSlev)
  set P := ((g * S⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hPdef
  have hPS : P * Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hSv, hPdef, ← Units.val_mul, inv_mul_cancel_right]
  let w : Fin n → ℂ := fun i => if i = ρ then 1 else if i < ρ then 0 else (g : Matrix (Fin n) (Fin n) ℂ) ρ i
  have hw : w ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ := by
    funext l
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    by_cases hl : l ≤ ρ
    · rw [Finset.sum_eq_single ρ]
      · simp [w, secMat_self, hl, hv, rowCut]
      · intro i _ hi
        rcases lt_or_gt_of_ne hi with h | h
        · simp [w, hi, h]
        · rw [secMat_of_ne _ _ _ hi, swap_of_lt' hj h, if_neg (lt_of_le_of_lt hl h).ne, mul_zero]
      · simp
    · have hlρ : ρ < l := lt_of_not_ge hl
      rw [Finset.sum_eq_single l]
      · simp [w, secMat_of_ne _ _ _ hlρ.ne', swap_of_lt' hj hlρ, hlρ.ne', not_lt.2 hlρ.le]
      · intro i _ hi
        by_cases h1 : i = ρ
        · rw [h1, secMat_self, if_neg hl, mul_zero]
        · rcases lt_or_gt_of_ne h1 with h | h
          · simp [w, h1, h]
          · rw [secMat_of_ne _ _ _ h1, swap_of_lt' hj h, if_neg (Ne.symm hi), mul_zero]
      · simp
  have hPw : P ρ ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ := by
    rw [← hPS]
    funext l
    simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]
  have hrow : P ρ = w := (Matrix.vecMul_injective_iff_isUnit.2 hS) (hPw.trans hw.symm)
  intro i hi
  by_cases hiρ : (i : ℕ) = ρ
  · have hie : i = ρ := Fin.ext hiρ
    subst hie
    refine ⟨fun l hl => ?_, ?_⟩
    · change P i l = 0
      rw [hrow]
      simp [w, hl, hl.ne]
    · change P i i = 1
      rw [hrow]
      simp [w]
  · exact hp i (by omega)

end GlobalTheory.JSW
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section
namespace GlobalTheory.ThetaDiagUnfold

theorem dot_sumElim {R : Type} [CommSemiring R] {κ : Type} [Fintype κ] (a b c d : κ → R) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem integral_thetaSum_schr_diag : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (κ ⊕ κ), ∀ x : κ → AF F,
      ∫ y in 𝓕₁, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) ∂μ =
        (μ.real 𝓕₁ : ℂ) * ∑' η : κ → F, Φ (Sum.elim ((fun i => algebraMap F (AF F) (η i)) + x)
          ((fun i => algebraMap F (AF F) (η i)) + x)) := by
  intro F _ _ ψ hψ κ _
  intro μ hμ 𝓕₁ hF hfin Φ hΦ x
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  haveI := hμ
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hψ
  obtain ⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (κ ⊕ κ → F) → ℂ, a = fun ξ => Φ ((fun i => algebraMap F (AF F) (ξ i)) + Sum.elim x x) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : (κ ⊕ κ → F) → (κ → F), d = fun ξ => ξ ∘ Sum.inl - ξ ∘ Sum.inr := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F (Sum.elim x x) hΦ)
    subst ha
    exact h0
  have he_norm : ∀ ξ y, ‖e ξ y‖ = 1 := fun ξ y => by rw [he]; exact hnorm _
  have he_cont : ∀ ξ, Continuous (e ξ) := fun ξ => by
    rw [he]; exact hcont.comp (continuous_const.dotProduct continuous_id)
  have hpt : ∀ y, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) =
      ∑' ξ, a ξ * e (d ξ) y := by
    intro y
    unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
    refine tsum_congr fun ξ => ?_
    have hsplit : (fun i => algebraMap F (AF F) (ξ i)) =
        Sum.elim (emb (ξ ∘ Sum.inl)) (emb (ξ ∘ Sum.inr)) := by
      funext s; cases s <;> simp [hemb]
    have hx0 : Sum.elim x x ⬝ᵥ Sum.elim y (-y) = 0 := by
      rw [dot_sumElim, dotProduct_neg, add_neg_cancel]
    have hdot : (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ Sum.elim y (-y) = emb (d ξ) ⬝ᵥ y := by
      rw [hsplit, dot_sumElim, dotProduct_neg, hd]
      have : emb (ξ ∘ Sum.inl - ξ ∘ Sum.inr) = emb (ξ ∘ Sum.inl) - emb (ξ ∘ Sum.inr) := by
        rw [hemb]; funext i; simp [map_sub]
      rw [this, sub_dotProduct, sub_eq_add_neg]
    simp only
    rw [hx0, mul_zero, add_zero, hdot, ha, he]
    ring
  have hFint : ∀ ξ : κ ⊕ κ → F, Integrable (fun y => a ξ * e (d ξ) y) (μ.restrict 𝓕₁) := fun ξ =>
    (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _
  have hnormint : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ = ‖a ξ‖ * μ.real 𝓕₁ := by
    intro ξ
    simp only [norm_mul, he_norm, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun ξ : κ ⊕ κ → F => ∫ y in 𝓕₁, ‖a ξ * e (d ξ) y‖ ∂μ := by
    simp_rw [hnormint]
    exact hsum.mul_right _
  have horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ y, e 0 y = 1 := fun y => by simp [he, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push_neg at h; exact hζ (funext h)
      haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
        refine Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_
        · exact (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩
        · rintro ⟨r, hr⟩
          obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
          exact ⟨ρ, by subst hemb; rfl⟩
      refine GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_
        (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0
      · intro r hr y
        obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]

        rw [show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by
        subst hemb; simp [dotProduct, map_sum, map_mul], htriv, one_mul]
      · intro y
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  have hFval : ∀ ξ : κ ⊕ κ → F, ∫ y in 𝓕₁, a ξ * e (d ξ) y ∂μ =
      if d ξ = 0 then (μ.real 𝓕₁ : ℂ) * a ξ else 0 := by
    intro ξ
    rw [integral_const_mul, horth]
    split_ifs <;> ring
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
  simp_rw [hFval]
  have hinj : Function.Injective (fun η : κ → F => (Sum.elim η η : κ ⊕ κ → F)) := fun η η' h => by
    funext i; exact congrFun h (Sum.inl i)
  rw [← hinj.tsum_eq, ← tsum_mul_left]
  · refine tsum_congr fun η => ?_
    have hd0 : d (Sum.elim η η) = 0 := by rw [hd]; funext i; simp
    rw [if_pos hd0, ha]
    dsimp only
    congr 2
    funext s; cases s <;> simp
  · intro ξ hξ
    have h0 : d ξ = 0 := by
      by_contra h; exact hξ (if_neg h)
    refine ⟨ξ ∘ Sum.inl, ?_⟩
    funext s
    cases s with
    | inl i => rfl
    | inr i =>
      have := congrFun h0 i
      rw [hd] at this
      simp only [Pi.sub_apply, Function.comp_apply, Pi.zero_apply, sub_eq_zero] at this
      simpa using this

end GlobalTheory.ThetaDiagUnfold
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ x : (κ → AF F),
      ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
        μ 𝓕₁ * ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 := by
  first | exact @GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq | exact GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq | (intros; apply GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : Frame X.Ψ r → ℂ), (∀ y, IsUnitFr X y → ∀ t : X.Ψ → Fin r → ℝ, F (rmul y (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) = bchar la (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) * F y) → ∃ Q : Frame X.Ψ r → ℂ, (∀ y, IsUnitFr X y → Q y = F y) ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x := by
  first | exact @GlobalTheory.HolRead.TorusExt.exists_extension | exact GlobalTheory.HolRead.TorusExt.exists_extension | (intros; apply GlobalTheory.HolRead.TorusExt.exists_extension <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ), (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → (∀ y, IsUnitFr X y → ∃ ℓ : Frame X.Ψ r →L[ℝ] ℂ, HasFDerivWithinAt (fun Z : Frame X.Ψ r => Q (rmul y (expFr Z))) ℓ (unitLie X) 0 ∧ ∀ (τ : X.Ψ) (c d : Fin r), c < d → ∀ Z ∈ unitLie X, ∀ Z' ∈ unitLie X, Z + Complex.I • Z' = unitFr τ c d → ℓ Z + Complex.I * ℓ Z' = 0) → DifferentiableOn ℂ Q X.dom := by
  first | exact @GlobalTheory.HolRead.Holo.differentiableOn_of_killed | exact GlobalTheory.HolRead.Holo.differentiableOn_of_killed | (intros; apply GlobalTheory.HolRead.Holo.differentiableOn_of_killed <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveClosure

theorem exists_closure_arith_surface_rat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∃ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ p) 1 ∧ z ≫ w = redι Z ≫ ratFibre.fst p ∧ IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
  intro k _ X p D hX Z hZ
  have := hX.isIntegral
  have := hX.finite
  let S : Closeds X := ⟨closure (ratFibre.fst p '' (Z : Set (ratFibre p))), isClosed_closure⟩
  have hSirr : IsIrreducible (S : Set X) :=
    (hZ.isIrreducible.image _ (ratFibre.fst p).continuous.continuousOn).closure
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := isIntegral_red hSirr
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  set w := redι S with hw
  haveI : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  haveI : IsPreimmersion (ratFibre.fst p) :=
    MorphismProperty.of_isPullback (ratFibre.isPullback p).flip inferInstance
  have hpb0 := (IsPullback.of_hasPullback w (ratFibre.fst p)).paste_vert (ratFibre.isPullback p)
  rw [← Category.assoc] at hpb0
  have hpb1 : IsPullback (pullback.fst w (ratFibre.fst p)) (pullback.snd w (ratFibre.fst p) ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := hpb0
  haveI : IsReduced (pullback ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) :=
    isReduced_pullback_localization ℤ ℚ (nonZeroDivisors ℤ) _ _
  haveI : IsReduced (pullback w (ratFibre.fst p)) := isReduced_of_isOpenImmersion hpb1.isoPullback.hom
  have hrange : Set.range (pullback.snd w (ratFibre.fst p)) = (Z : Set (ratFibre p)) := by
    rw [Scheme.Pullback.range_snd, hw, range_redι]
    change ratFibre.fst p ⁻¹' closure (ratFibre.fst p '' (Z : Set (ratFibre p))) = _
    rw [← (ratFibre.fst p).isEmbedding.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]
  obtain ⟨e, he⟩ := exists_iso_red_of_range _ _ (pullback.snd w (ratFibre.fst p)) Z hrange
  have hzw : (e.hom ≫ pullback.fst w (ratFibre.fst p)) ≫ w = redι Z ≫ ratFibre.fst p := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hpb : IsPullback (e.hom ≫ pullback.fst w (ratFibre.fst p)) (redι Z ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
    refine IsPullback.of_iso hpb1 e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← he]
    · simp
    · simp
  have hcZ : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    let φ : ℚ →+* Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      (redι Z ≫ ratFibre.snd p).appTop.hom.comp (Scheme.ΓSpecIso (.of ℚ)).inv.hom
    exact charZero_of_injective_ringHom φ.injective
  have hcW : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal S).subscheme, ⊤) :=
    (e.hom ≫ pullback.fst w (ratFibre.fst p)).appTop.hom.charZero
  have hproj : IsProjOver (w ≫ p) := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    exact ⟨N, w ≫ j, inferInstance, by rw [Category.assoc, hj]⟩
  have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = (1 : ℕ) := by
    rw [topologicalKrullDim_red, hZ.dim_eq]; rfl
  haveI : IsProper (w ≫ p) := by
    obtain ⟨N, i, _, hi⟩ := hproj
    have := isProper_str k N
    exact hi ▸ inferInstance
  haveI : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hX.finite
  haveI : Flat ((w ≫ p) ≫ spMap (Int.castRingHom k)) := (flat_int_iff_charZero _).2 hcW
  have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal S).subscheme = (1 + 1 : ℕ) :=
    IntModel.topologicalKrullDim_eq_succ (O := ℤ) (K := ℚ) Int.not_isField hpb hdZ
  exact ⟨_, w, e.hom ≫ pullback.fst w (ratFibre.fst p), inferInstance, hX.of_isClosedImmersion w hcW hdim,
    hzw, hpb⟩

end GlobalTheory.CurveClosure
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

theorem _root_.GlobalTheory.T.eulerChar_lineBundle_fibre_modp_eq_rat_projective : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (p : ℕ) [Fact p.Prime] (N : LB W), N.IsLB → (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); chi (ZMod p) (toMod (N.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) = chi ℚ (toMod (N.pull (ratFibre.fst q))) ∧ chi (ZMod p) (structureModule (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))) = chi ℚ (structureModule (ratFibre q))) := by
  first | exact @GlobalTheory.ChiFibre.chi_fibre_eq | exact GlobalTheory.ChiFibre.chi_fibre_eq | (intros; apply GlobalTheory.ChiFibre.chi_fibre_eq <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.haar_measure_weyl_cell_odd_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ j : ℕ, μ (shellU k y j) = (q : ENNReal) ^ (j + 2 * (j / 2)) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.measure_shellU | exact GlobalTheory.WeylCell.WeylUnipotentShell.measure_shellU | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.measure_shellU <;> assumption)
end
