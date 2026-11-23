module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Defs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle143
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle412
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle414
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle001
public import Mathlib.Analysis.MeanInequalities
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetPowContent

theorem rpow_digitSum_le (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (p : ℝ) ^ ((((Nat.digits p n).sum : ℕ) : ℝ) / ((p : ℝ) - 1)) ≤ (n : ℝ) + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdig : ∀ d : ℕ, d < p → (p : ℝ) ^ ((d : ℝ) / ((p : ℝ) - 1)) ≤ (d : ℝ) + 1 := by
    intro d hd
    have hd' : (d : ℝ) ≤ (p : ℝ) - 1 := by
      have h1 : d + 1 ≤ p := hd
      have h2 : (d : ℝ) + 1 ≤ p := by exact_mod_cast h1
      linarith
    have ht0 : 0 ≤ (d : ℝ) / ((p : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hpos.le
    have ht1 : (d : ℝ) / ((p : ℝ) - 1) ≤ 1 := (div_le_one hpos).mpr hd'
    have h := Real.geom_mean_le_arith_mean2_weighted ht0 (sub_nonneg.mpr ht1)
      (by linarith : (0 : ℝ) ≤ p) zero_le_one (add_sub_cancel _ _)
    rw [Real.one_rpow, mul_one] at h
    have e : (d : ℝ) / ((p : ℝ) - 1) * p + (1 - (d : ℝ) / ((p : ℝ) - 1)) * 1 = (d : ℝ) + 1 := by
      field_simp
      ring
    linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' (by omega) hn, List.sum_cons, Nat.cast_add, add_div,
        Real.rpow_add (by linarith)]
      have h1 := ih (n / p) (Nat.div_lt_self hn (by omega))
      have h2 := hdig (n % p) (Nat.mod_lt _ (by omega))
      have hmod : ((n % p : ℕ) : ℝ) + (p : ℝ) * ((n / p : ℕ) : ℝ) = n := by
        exact_mod_cast Nat.mod_add_div n p
      have hlt : ((n % p : ℕ) : ℝ) + 1 ≤ p := by
        exact_mod_cast (Nat.mod_lt n (by omega : 0 < p))
      have hm0 : (0 : ℝ) ≤ ((n / p : ℕ) : ℝ) := Nat.cast_nonneg _
      calc (p : ℝ) ^ (((n % p : ℕ) : ℝ) / ((p : ℝ) - 1)) *
            (p : ℝ) ^ ((((Nat.digits p (n / p)).sum : ℕ) : ℝ) / ((p : ℝ) - 1))
          ≤ (((n % p : ℕ) : ℝ) + 1) * (((n / p : ℕ) : ℝ) + 1) :=
            mul_le_mul h2 h1 (Real.rpow_nonneg (by linarith) _) (by positivity)
        _ ≤ (n : ℝ) + 1 := by nlinarith

theorem digitSum_le_logb (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    (((Nat.digits p n).sum : ℕ) : ℝ) ≤ ((p : ℝ) - 1) * Real.logb p ((n : ℝ) + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (((Nat.digits p n).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((n : ℝ) + 1) :=
    (Real.le_logb_iff_rpow_le hp1 (by positivity)).mpr (rpow_digitSum_le p hp n)
  rw [div_le_iff₀ hpos] at h2
  linarith [mul_comm (Real.logb p ((n : ℝ) + 1)) ((p : ℝ) - 1)]

theorem padicValNat_factorial_ge (p : ℕ) (hp : p.Prime) (N : ℕ) :
    (N : ℝ) / ((p : ℝ) - 1) - Real.logb p ((N : ℝ) + 1) ≤ (padicValNat p N.factorial : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h := digitSum_le_logb p hp.two_le N
  have h3 : (((Nat.digits p N).sum : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ Real.logb p ((N : ℝ) + 1) := by
    rw [div_le_iff₀ hpos]
    linarith [mul_comm (Real.logb p ((N : ℝ) + 1)) ((p : ℝ) - 1)]
  rw [GlobalTheory.LegendreBounds.legendre_real p hp N, sub_div]
  linarith

theorem toE_coe (r : ℝ) : toE (r : WithTop ℝ) = (r : EReal) := rfl

theorem toE_mono {x y : WithTop ℝ} (h : x ≤ y) : toE x ≤ toE y := by
  unfold toE
  exact WithBot.coe_le_coe.mpr h

theorem val_mfact {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ} (hp : p.Prime)
    (hv : v (p : C) = 1) {σ : Type} [Fintype σ] (α : σ →₀ ℕ) :
    v (mfact α : C) = ((∑ k, (padicValNat p (α k).factorial : ℝ) : ℝ) : WithTop ℝ) := by
  classical
  have hne : (∏ k, (α k).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => Nat.factorial_ne_zero _)
  have e : (mfact α : C) = ((∏ k, (α k).factorial : ℕ) : C) := by
    unfold mfact
    rw [Finsupp.prod_fintype _ _ (fun k => by simp), Nat.cast_prod]
  rw [e, ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hp hv hne, Nat.factorization_def _ hp, ← Nat.padicValNat_def,
    GlobalTheory.LegendreBounds.padicValNat_prod_factorial p hp Finset.univ α]

theorem content_detPow_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i c : ℕ), content v (detPow C i c) ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) ∧ ((((i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1) : ℝ)) : EReal) ≤ content v (detPow C i c) := by
  intro C _ _ v p hp hv i c
  classical
  obtain ⟨-, hint, hdiag, hrows⟩ := GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have key : ∀ α ∈ (detPow C i c).support,
      (∑ k, ((α k : ℕ) : ℝ)) = (i : ℝ) * c ∧ ∀ k, α k ≤ c := by
    intro α hα
    obtain ⟨-, hb⟩ := hrows α hα
    refine ⟨?_, ?_⟩
    · rw [Fintype.sum_sigma]
      have hb' : ∀ b : Fin i, (∑ a : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c := by
        intro b
        exact_mod_cast hb b
      simp only [hb', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rintro ⟨b, a⟩
      rw [← hb b]
      exact Finset.single_le_sum (f := fun a' => α ⟨b, a'⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ a)
  have upS : ∀ α ∈ (detPow C i c).support,
      (∑ k, (padicValNat p (α k).factorial : ℝ)) ≤ (i * c : ℝ) / (p - 1) := by
    intro α hα
    calc (∑ k, (padicValNat p (α k).factorial : ℝ))
        ≤ ∑ k, ((α k : ℕ) : ℝ) / ((p : ℝ) - 1) :=
          Finset.sum_le_sum (fun k _ => GlobalTheory.LegendreBounds.upper p hp (α k))
      _ = (i * c : ℝ) / (p - 1) := by rw [← Finset.sum_div, (key α hα).1]
  have loS : ∀ α ∈ (detPow C i c).support,
      (i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1)
        ≤ ∑ k, (padicValNat p (α k).factorial : ℝ) := by
    intro α hα
    obtain ⟨hsum, hle⟩ := key α hα
    have h1 : ∀ k, ((α k : ℕ) : ℝ) / ((p : ℝ) - 1) - Real.logb p ((c : ℝ) + 1)
        ≤ (padicValNat p (α k).factorial : ℝ) := by
      intro k
      have hl : Real.logb p (((α k : ℕ) : ℝ) + 1) ≤ Real.logb p ((c : ℝ) + 1) :=
        Real.logb_le_logb_of_le hp1 (by positivity) (by exact_mod_cast Nat.add_le_add_right (hle k) 1)
      have := padicValNat_factorial_ge p hp (α k)
      linarith
    calc (i * c : ℝ) / (p - 1) - (i : ℝ) ^ 2 * Real.logb p (c + 1)
        = ∑ k, (((α k : ℕ) : ℝ) / ((p : ℝ) - 1) - Real.logb p ((c : ℝ) + 1)) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sigma, Fintype.card_fin,
            smul_eq_mul, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ k, (padicValNat p (α k).factorial : ℝ) := Finset.sum_le_sum (fun k _ => h1 k)
  constructor
  · set α0 : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα0
    have hmem : α0 ∈ (detPow C i c).support := by
      rw [MvPolynomial.mem_support_iff, hdiag]
      exact one_ne_zero
    calc content v (detPow C i c) ≤ toE (v ((detPow C i c).coeff α0 * mfact α0)) := by
          unfold content
          exact iInf₂_le α0 hmem
      _ = (((∑ k, (padicValNat p (α0 k).factorial : ℝ)) : ℝ) : EReal) := by
          rw [hdiag, one_mul, val_mfact v hp hv α0, toE_coe]
      _ ≤ _ := EReal.coe_le_coe_iff.mpr (upS α0 hmem)
  · unfold content
    refine le_iInf₂ (fun α hα => ?_)
    obtain ⟨n, hn⟩ := hint α
    rw [← toE_coe]
    apply toE_mono
    rw [AddValuation.map_mul, val_mfact v hp hv α, hn]
    exact le_trans (WithTop.coe_le_coe.mpr (loS α hα))
      (le_add_of_nonneg_left (ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v n))

end GlobalTheory.DetPowContent
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧ ∀ x : B.Aˣ, B.σ (x : B.A) = x → {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  first | exact @GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any | exact GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any | (intros; apply GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.ResDeg

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem card_residueField_prod_any : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g →
    ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)),
      ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField
        (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  intro K B₁ B₂ h₁ h₂ _ i₁ i₂ hl
  exact card_residueField (B₁.prod B₂) (Prod.ext h₁ h₂) (IsIntegral.pair i₁ i₂) hl

end GlobalTheory.UnitLemma.ResDeg
end
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.normCoeffIdealFamily_map_basicOpen : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y] [GlobalTheory.IsNormalScheme Z]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ Set.range π →
    (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      GlobalTheory.NormSheafDescent.famIdeal π hK hfd I (Z.affineBasicOpen f) := by
  first | exact @GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen | exact GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen | (intros; apply GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.PiTensorFixed

variable {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem exists_fixed_tprod (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a))) (v : ∀ a, X a) :
    ∃ u : ∀ a, X a, (∀ a, u a ∈ fixed (ρ a) (K a)) ∧
      (twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1).mkQ (PiTensorProduct.tprod ℂ u) =
        (twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1).mkQ (PiTensorProduct.tprod ℂ v) := by
  classical
  haveI := Fintype.ofFinite α
  set N := twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1
  have key : ∀ S : Finset α, ∃ u : ∀ a, X a, (∀ a ∈ S, u a ∈ fixed (ρ a) (K a)) ∧
      N.mkQ (PiTensorProduct.tprod ℂ u) = N.mkQ (PiTensorProduct.tprod ℂ v) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨v, by simp, rfl⟩
    | insert a S ha ih =>
      obtain ⟨u, hu, e⟩ := ih
      let f : X a →ₗ[ℂ] _ := N.mkQ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap u a
      obtain ⟨y, hy, hfy⟩ := IwahoriOnto.exists_fixed_map_eq (hρ a) (hK a) f (u a) fun h hh => by
        simp only [f, LinearMap.comp_apply, MultilinearMap.toLinearMap_apply, Submodule.mkQ_apply,
          Function.update_eq_self]
        rw [Submodule.Quotient.eq]
        refine Submodule.subset_span ⟨⟨Pi.mulSingle a h, fun b _ => ?_⟩, PiTensorProduct.tprod ℂ u, ?_⟩
        · by_cases hb : b = a
          · subst hb; simpa using hh
          · simp [Pi.mulSingle_eq_of_ne hb]
        · have : (fun b => ρ b (Pi.mulSingle (M := Γ) a h b) (u b)) = Function.update u a (ρ a h (u a)) := by
            funext b
            by_cases hb : b = a
            · subst hb; simp
            · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
          simp [this]
      refine ⟨Function.update u a y, fun b hb => ?_, ?_⟩
      · by_cases hba : b = a
        · subst hba; simpa using hy
        · rw [Function.update_of_ne hba]
          exact hu b ((Finset.mem_insert.1 hb).resolve_left hba)
      · rw [← e]
        simpa [f] using hfy
  obtain ⟨u, hu, e⟩ := key Finset.univ
  exact ⟨u, fun a => hu a (Finset.mem_univ a), e⟩

theorem fixed_le_range (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a))) :
    fixed (piTensor ρ) (Subgroup.pi Set.univ K) ≤
      LinearMap.range (PiTensorProduct.map fun a => (fixed (ρ a) (K a)).subtype) := by
  set N := twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1
  set R := LinearMap.range (PiTensorProduct.map fun a => (fixed (ρ a) (K a)).subtype)
  have hR : R ≤ fixed (piTensor ρ) (Subgroup.pi Set.univ K) := by
    rintro _ ⟨x, rfl⟩
    induction x using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | smul_tprod c x =>
      rw [map_smul]
      refine Submodule.smul_mem _ c (ContraRefl.mem_fix.2 fun h hh => ?_)
      rw [PiTensorProduct.map_tprod, piTensor_tprod]
      congr 1
      funext a
      exact ContraRefl.mem_fix.1 (x a).2 _ (hh a trivial)
  have hall : ∀ w, ∃ r ∈ R, N.mkQ r = N.mkQ w := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | add x y hx hy =>
      obtain ⟨r, hr, e⟩ := hx
      obtain ⟨s, hs, e'⟩ := hy
      exact ⟨r + s, add_mem hr hs, by rw [map_add (f := _), map_add (f := _), e, e']⟩
    | smul_tprod c x =>
      obtain ⟨u, hu, e⟩ := exists_fixed_tprod ρ hρ K hK x
      refine ⟨c • PiTensorProduct.tprod ℂ u, Submodule.smul_mem _ c
        ⟨PiTensorProduct.tprod ℂ fun a => ⟨u a, hu a⟩, by simp⟩, ?_⟩
      rw [map_smul, map_smul, e]
  intro w hw
  obtain ⟨r, hr, e⟩ := hall w
  have h0 : r - w = 0 := ContraRefl.eq_zero_of_fixed_twKer (isSmooth_piTensor hρ)
    (isCompact_univ_pi hK) (sub_mem (hR hr) hw) ((Submodule.Quotient.eq N).1 e)
  rw [← sub_eq_zero.1 h0]
  exact hr

theorem finiteDimensional_fixed_piTensor : ∀ {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)), (∀ a, IsSmooth (ρ a)) → ∀ (K : ∀ a, Subgroup (Γ a)), (∀ a, IsCompact (K a : Set (Γ a))) → (∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) → FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) := by
  intro α _ Γ X _ _ _ _ _ ρ hρ K hK hfin
  exact Submodule.finiteDimensional_of_le (fixed_le_range ρ hρ K hK)

end GlobalTheory.PiTensorFixed
end

section

open GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.TypeTwo.PowIrrProof

theorem equiv_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
    (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨y, hy⟩ := exists_ne (0 : W)
  letI : ρ.IsIrreducible := hρ
  rcases eq_bot_or_eq_top S with rfl | rfl
  · obtain ⟨v, rfl⟩ := hf y
    have hv : v = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 v.property)
    exact (hy (by rw [hv, map_zero])).elim
  · let e := (topEquiv ρ).symm
    let F : ρ.IntertwiningMap σ := f.comp e.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp e.toLinearEquiv.surjective
    have hi : Function.Injective F :=
      (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right fun hF => by
        obtain ⟨x, hx⟩ := hs y
        exact hy (by simpa [hF] using hx.symm)
    exact ⟨F.ofBijective ⟨hi, hs⟩⟩

theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W] :
    Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  letI : Nontrivial S.toSubmodule := hf.nontrivial
  exact Subtype.val_injective.nontrivial (α := S.toSubmodule)

end GlobalTheory.TypeTwo.PowIrrProof
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

theorem _root_.GlobalTheory.T.isLimit_widePullbackCone_spec_single : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (0 + 1) => GlobalTheory.CechOne.fB A B) (GlobalTheory.CechOne.fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _))) := by
  first | (exact @GlobalTheory.CechOne.isLimit_cone_one) | (exact GlobalTheory.CechOne.isLimit_cone_one) | (intros; apply GlobalTheory.CechOne.isLimit_cone_one  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

theorem _root_.GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (1 + 1) => GlobalTheory.CechOne.fB A B) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (GlobalTheory.CechOne.y1 A B) (GlobalTheory.CechOne.hy1 A B))) := by
  first | (exact @GlobalTheory.CechOne.isLimit_widePullback_tensor) | (exact GlobalTheory.CechOne.isLimit_widePullback_tensor) | (intros; apply GlobalTheory.CechOne.isLimit_widePullback_tensor  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

theorem _root_.GlobalTheory.T.triple_tensor_wide_pullback_limit : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (2 + 1) => GlobalTheory.CechOne.fB A B) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B))))) (GlobalTheory.CechOne.y2 A B) (GlobalTheory.CechOne.hy2 A B))) := by
  first | (exact @GlobalTheory.CechOne.spec_tensor3_isLimit) | (exact GlobalTheory.CechOne.spec_tensor3_isLimit) | (intros; apply GlobalTheory.CechOne.spec_tensor3_isLimit  <;> assumption)
end

section

open IsLocalRing GlobalTheory.Henselisation

theorem _root_.GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Function.Injective (Hens.of i) := by
  first | exact @GlobalTheory.Henselisation.Hens.of_injective_of_nbhd | exact GlobalTheory.Henselisation.Hens.of_injective_of_nbhd | (intros; apply GlobalTheory.Henselisation.Hens.of_injective_of_nbhd <;> assumption)
end

section

open IsLocalRing GlobalTheory.Henselisation

theorem _root_.GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsLocalRing (Hens R) ∧ ∀ i : EtNbhd R, IsLocalHom (Hens.of i) := by
  first | exact @GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of | exact GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of | (intros; apply GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of <;> assumption)
end

section

open Matrix Polynomial

theorem _root_.GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  first | exact @GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | exact GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | (intros; apply GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable <;> assumption)
end
