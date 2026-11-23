module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle350
public import Mathlib.Topology.Instances.ZMod
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle018
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.coboundary_of_uniform_limit_coboundaries : ∀ {𝕜 : Type} [NormedField 𝕜] {Γ : Type} (H : Set Γ) (k f : Γ → 𝕜), (∃ s ∈ H, k s ≠ 1) → (∀ ε : ℝ, 0 < ε → ∃ X : 𝕜, ∀ s ∈ H, ‖f s - (k s * X - X)‖ ≤ ε) → ∃ X : 𝕜, ∀ s ∈ H, f s = k s * X - X := by
  first | exact @GlobalTheory.coboundary_closed_of_uniform_approx | exact GlobalTheory.coboundary_closed_of_uniform_approx | (intros; apply GlobalTheory.coboundary_closed_of_uniform_approx <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_divisible_chain_primary_torsion_group : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X], (∀ x : X, ∃ n : ℕ, l ^ n • x = 0) → Finite {x : X // l • x = 0} → (∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) → ∃ x : ℕ → X, x 0 ≠ 0 ∧ ∀ n, l • x (n + 1) = x n := by
  first | exact @GlobalTheory.Ord2.DivChain.exists_divisible_chain | exact GlobalTheory.Ord2.DivChain.exists_divisible_chain | (intros; apply GlobalTheory.Ord2.DivChain.exists_divisible_chain <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.lipschitz_padicHom_of_contraction_per_level : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (P : ℕ → Γ → Prop) (lam : Γ →* Multiplicative ℤ_[l]), (∀ m g, P (m + 1) g → P m g) → (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g, P N g → ‖(lam g).toAdd‖ ≤ ε) → (∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g, P (m + 1) g → ∃ h g' : Γ, P m h ∧ P (m + 2) g' ∧ g = h ^ l * g') → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), P m g → ‖(lam g).toAdd‖ ≤ C * ((l : ℝ)⁻¹) ^ m := by
  first | exact @GlobalTheory.lipschitz_of_contraction_per_level | exact GlobalTheory.lipschitz_of_contraction_per_level | (intros; apply GlobalTheory.lipschitz_of_contraction_per_level <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaClosed

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem isOpen_setOf_apply [Algebra.IsAlgebraic ℚ Ω] (x : Ω) (P : Ω → Prop) :
    IsOpen {σ : G ℚ Ω | P (σ x)} := by
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hH : ((IntermediateField.adjoin ℚ {x}).fixingSubgroup : Set (G ℚ Ω)) ∈ nhds (1 : G ℚ Ω) :=
    (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  rw [← map_mul_left_nhds_one σ]
  refine Filter.mem_map.2 (Filter.mem_of_superset hH fun τ hτ => ?_)
  have hτx : τ x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self ℚ x)
  show P ((σ * τ) x)
  rw [AlgEquiv.mul_apply, hτx]
  exact hσ

theorem isClosed_setOf_apply [Algebra.IsAlgebraic ℚ Ω] (x : Ω) (P : Ω → Prop) :
    IsClosed {σ : G ℚ Ω | P (σ x)} := by
  have h := isOpen_setOf_apply x (fun y => ¬ P y)
  rw [← isOpen_compl_iff]
  convert h using 1

theorem mem_dec_of_forall {A : ValuationSubring Ω} {σ : G ℚ Ω} (h : ∀ x, σ x ∈ A ↔ x ∈ A) :
    σ ∈ A.decompositionSubgroup ℚ := by
  show σ ∈ Dec (F := ℚ) A
  rw [mem_Dec]
  ext x
  rw [show x = σ ((σ⁻¹ : G ℚ Ω) x) from (mul_inv_apply x).symm, ← AlgEquiv.smul_def σ ((σ⁻¹ : G ℚ Ω) x),
    ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def, h]

theorem isClosed_Ine [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) :
    IsClosed ((Ine (F := ℚ) A : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  have e : ((Ine (F := ℚ) A : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) =
      (⋂ x : Ω, {σ : G ℚ Ω | (σ x ∈ A ↔ x ∈ A)}) ∩
        ⋂ x : Ω, {σ : G ℚ Ω | A.valuation x ≤ 1 → A.valuation (σ x - x) < 1} := by
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun x => apply_mem_iff_of_mem_Dec (F := ℚ) h.1 x, h.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mem_dec_of_forall h1, h2⟩
  rw [e]
  exact (isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x (fun y => (y ∈ A ↔ x ∈ A))).inter
    (isClosed_iInter fun x => isClosed_setOf_apply (Ω := Ω) x
      (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))

theorem continuous_toZModPow' (l : ℕ) [hl : Fact l.Prime] (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := l) n) := by
  first
  | exact @_root_.GlobalTheory.ContinuousZModPow.main
  | exact _root_.GlobalTheory.ContinuousZModPow.main
  | (apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousZModPow.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousZModPow.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousZModPow.main ..)

theorem isClosed_ker_cycMod (l : ℕ) [Fact l.Prime] (m : ℕ) :
    IsClosed (((cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  have hc : Continuous fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) :=
    (continuous_toZModPow' l m).comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))
  have e : (((cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) =
      (fun σ : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) ⁻¹' {1} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Units.val_eq_one]
    rfl
  rw [e]
  exact (isClosed_discrete _).preimage hc

end GlobalTheory.InertiaClosed


open GlobalTheory.InertiaClosed in
theorem GlobalTheory.isClosed_Ine_inf_ker_cycMod : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) (m : ℕ),
    IsClosed ((Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  intro l _ Ω _ _ _ A m
  rw [Subgroup.coe_inf]
  exact (isClosed_Ine A).inter (isClosed_ker_cycMod l m)
end
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

theorem _root_.GlobalTheory.T.isClosed_inertia_cyclotomic_kernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) (m : ℕ), IsClosed ((Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  first | exact @GlobalTheory.isClosed_Ine_inf_ker_cycMod | exact GlobalTheory.isClosed_Ine_inf_ker_cycMod | (intros; apply GlobalTheory.isClosed_Ine_inf_ker_cycMod <;> assumption)

end
end
