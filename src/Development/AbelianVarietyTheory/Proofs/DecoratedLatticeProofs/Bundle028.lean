module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.CoinvSB

theorem isLocallyConstant_indicator_const {X : Type*} [TopologicalSpace X] {U : Set X} (h1 : IsOpen U)
    (h2 : IsClosed U) (c : ℂ) : IsLocallyConstant (U.indicator fun _ => c) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [h1.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  · filter_upwards [h2.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ D : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀, ∫ a, D.1 (x₀, 0, a) ∂(Measure.pi fun _ => ν) = 0) → l D = 0 := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2 D hD
  obtain ⟨s, hs⟩ : ∃ s : kˣ, ∀ t ∈ box I₁ s, ∀ y : (I₀ → k) × (I₁ → k) × (I₂ → k),
      D.1 (y + (0, t, 0)) = D.1 y := by
    have h := GlobalTheory.SBConv.eventually_translate D.2
    have hT : Filter.Tendsto (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) := by fun_prop
      exact this.tendsto' 0 0 (by simp)
    obtain ⟨s, hs⟩ := exists_box_subset (hT.eventually h)
    refine ⟨s, fun t ht y => ?_⟩
    have := hs ht y
    simpa [sub_eq_add_neg] using this
  obtain ⟨Φ', hΦ', hl⟩ := GlobalTheory.T.exists_cutoff_of_addChar_translation_invariant_functional k ψ hψc hψ1 I₀ I₁ I₂ M l h1 D s
  have hz : ∀ x₀ x₁, ∫ a, Φ'.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0 := by
    intro x₀ x₁
    simp_rw [hΦ']
    by_cases hx : x₁ ∈ box I₁ s
    · have e : ∀ a, D.1 (x₀, x₁, a) = D.1 (x₀, 0, a) := fun a => by
        simpa using hs x₁ hx (x₀, 0, a)
      simp only [Set.indicator_of_mem hx, one_mul, e]
      exact hD x₀
    · simp [Set.indicator_of_notMem hx]
  rw [hl]
  exact GlobalTheory.T.schwartzBruhat_functional_zero_of_fibre_integral_zero k ν hν I₀ I₁ I₂ M l h2 Φ' hz

theorem coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∃! l₀ : SB (I₀ → k) →ₗ[ℂ] M, ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), ∃ Ψ : SB (I₀ → k), (∀ x, Ψ.1 x = ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∧ l Φ = l₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2
  haveI := secondCountable k
  haveI := t2Space k
  set μ : Measure (I₂ → k) := Measure.pi fun _ => ν with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set vol : ℝ := μ.real (box I₂ 1) with hvol
  have hvol0 : vol ≠ 0 := by
    refine (ENNReal.toReal_pos ?_ ?_).ne'
    · exact (isOpen_box 1).measure_ne_zero μ ⟨0, fun i _ => by simp [cball]⟩
    · exact (isCompact_box 1).measure_lt_top.ne
  have hlc : ∀ (n : Type) [Fintype n] (c : ℂ), IsLocallyConstant ((box n (1 : kˣ)).indicator fun _ => c) :=
    fun n _ c => isLocallyConstant_indicator_const (isOpen_box 1) (isCompact_box 1).isClosed c
  let σf : SB (I₀ → k) → (I₀ → k) × (I₁ → k) × (I₂ → k) → ℂ := fun Ψ x =>
    Ψ.1 x.1 * ((box I₁ (1 : kˣ)).indicator (fun _ => (1 : ℂ)) x.2.1 *
      (box I₂ (1 : kˣ)).indicator (fun _ => ((vol : ℂ))⁻¹) x.2.2)
  have hσ : ∀ Ψ, σf Ψ ∈ SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := by
    intro Ψ
    refine ⟨(Ψ.2.1.comp_continuous continuous_fst).mul
      (((hlc I₁ 1).comp_continuous (by fun_prop)).mul ((hlc I₂ _).comp_continuous (by fun_prop))), ?_⟩
    refine HasCompactSupport.intro (Ψ.2.2.prod ((isCompact_box (1 : kˣ)).prod (isCompact_box (1 : kˣ)))) ?_
    intro x hx
    simp only [σf]
    by_cases h0 : x.1 ∈ tsupport Ψ.1
    · by_cases h1' : x.2.1 ∈ box I₁ (1 : kˣ)
      · have h2' : x.2.2 ∉ box I₂ (1 : kˣ) := fun h => hx ⟨h0, h1', h⟩
        simp [Set.indicator_of_notMem h2']
      · simp [Set.indicator_of_notMem h1']
    · simp [image_eq_zero_of_notMem_tsupport h0]
  let σ : SB (I₀ → k) →ₗ[ℂ] SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) :=
    { toFun := fun Ψ => ⟨σf Ψ, hσ Ψ⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun c Ψ => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]; ring }
  have hσv : ∀ Ψ x, (σ Ψ).1 x = σf Ψ x := fun _ _ => rfl
  have hInt : ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (x : I₀ → k),
      Integrable (fun a => Φ.1 (x, 0, a)) μ := by
    intro Φ x
    refine Continuous.integrable_of_hasCompactSupport (Φ.2.1.continuous.comp (by fun_prop)) ?_
    refine HasCompactSupport.intro (IsCompact.image Φ.2.2 (continuous_snd.comp continuous_snd)) fun a ha => ?_
    exact image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩
  have hσi : ∀ Ψ x, ∫ a, (σ Ψ).1 (x, 0, a) ∂μ = Ψ.1 x := by
    intro Ψ x
    simp only [hσv, σf]
    have h0 : (0 : I₁ → k) ∈ box I₁ (1 : kˣ) := fun i _ => by simp [cball]
    simp only [Set.indicator_of_mem h0, one_mul]
    rw [integral_const_mul, integral_indicator_const _ (isOpen_box _).measurableSet]
    rw [← hvol, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hvol0), mul_one]
  refine ⟨l ∘ₗ σ, fun Φ => ⟨⟨_, GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat k ν I₀ I₁ I₂ Φ⟩, fun x => rfl, ?_⟩, ?_⟩
  · set Ψ : SB (I₀ → k) := ⟨_, GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat k ν I₀ I₁ I₂ Φ⟩
    have hk := kernel k ψ ν hψc hψ1 hν I₀ I₁ I₂ M l h1 h2 (Φ - σ Ψ) (fun x₀ => by
      simp only [Submodule.coe_sub, Pi.sub_apply]
      rw [integral_sub (hInt Φ x₀) (hInt (σ Ψ) x₀), hσi]
      exact sub_self _)
    rw [map_sub, sub_eq_zero] at hk
    simpa using hk
  · intro l₀ hl₀
    ext1 Ψ
    obtain ⟨Ψ', hΨ', hl⟩ := hl₀ (σ Ψ)
    have : Ψ' = Ψ := Subtype.ext (funext fun x => (hΨ' x).trans (hσi Ψ x))
    subst this
    simp [← hl]

end GlobalTheory.CoinvSB
end
end

section

open ValuativeRel Matrix
open scoped Classical

theorem _root_.GlobalTheory.T.exists_N_embX_inv_mul_mem_KOne' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ), ∀ x ∈ S.P.J, ∃ (n : GL (Fin κ ⊕ Fin (s + 1)) k) (γ : GL (Fin κ) k), n ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) ∧ n ∈ S.P.J ∧ GlobalTheory.RootEx.embX (s + 1) γ ∈ S.P.J ∧ (n * GlobalTheory.RootEx.embX (s + 1) γ)⁻¹ * x ∈ GlobalTheory.SplitWeil.KOne k (Fin κ ⊕ Fin (s + 1)) := by
  first | exact @GlobalTheory.SymChain.SymData.exists_N_embX_inv_mul_mem_KOne | exact GlobalTheory.SymChain.SymData.exists_N_embX_inv_mul_mem_KOne | (intros; apply GlobalTheory.SymChain.SymData.exists_N_embX_inv_mul_mem_KOne <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricLevelChain_pattern_iterated : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t := by
  first | exact @GlobalTheory.SymChain.pattern_iter | exact GlobalTheory.SymChain.pattern_iter | (intros; apply GlobalTheory.SymChain.pattern_iter <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.flatColumnMap_eq_rootExchangeOperator_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix n (n' ⊕ Unit) k, GlobalTheory.LocFlat.flCol ψ ν p Φ x = opE ψ ν p (fun z => Φ ((colE c p fun r => x r (Sum.inr ())).val * z)) x.toCols₁ := by
  first | exact @GlobalTheory.LocFlat.flCol_eq_opE_colE | exact GlobalTheory.LocFlat.flCol_eq_opE_colE | (intros; apply GlobalTheory.LocFlat.flCol_eq_opE_colE <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flatMapFourierJacobiRow_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → GlobalTheory.LocFlat.flRow ψ ν p (Φ₁ + Φ₂) = GlobalTheory.LocFlat.flRow ψ ν p Φ₁ + GlobalTheory.LocFlat.flRow ψ ν p Φ₂ := by
  first | exact @GlobalTheory.LocFlat.flRow_add | exact GlobalTheory.LocFlat.flRow_add | (intros; apply GlobalTheory.LocFlat.flRow_add <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.flatMapRow_eq_zero_unless_row_mem_dualLattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Unit) (XIx (Fin κ) t j) k, x (Sum.inr ()) ∉ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → GlobalTheory.LocFlat.flRow S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x = 0 := by
  first | exact @GlobalTheory.LocFlat.flRow_eq_zero_of_not_mem_box | exact GlobalTheory.LocFlat.flRow_eq_zero_of_not_mem_box | (intros; apply GlobalTheory.LocFlat.flRow_eq_zero_of_not_mem_box <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.flatRowMap_eq_rootExchangeOperator_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix (n ⊕ Unit) n' k, GlobalTheory.LocFlat.flRow ψ ν p Φ x = opE ψ ν p (fun z => Φ (z * (rowE (c + 1) p (x (Sum.inr ()))).val)) x.toRows₁ := by
  first | exact @GlobalTheory.LocFlat.flRow_eq_opE_rowE | exact GlobalTheory.LocFlat.flRow_eq_opE_rowE | (intros; apply GlobalTheory.LocFlat.flRow_eq_opE_rowE <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by
  first | exact @GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt | exact GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt | (intros; apply GlobalTheory.SymChain.oneIndexAt_of_classAt_supportAt <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.LocFlat.CellSupport

theorem det_colE {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, colE, upU, Matrix.det_fromBlocks_zero₂₁]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_inv_of_det_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL b k) (hg : Matrix.GeneralLinearGroup.det g = 1) (Ψ : Matrix b a k → ℂ) :
    om μ (1 : GL a k) g⁻¹ Ψ = fun z => Ψ (g.val * z) := by
  funext z
  simp only [om, map_inv, hg, inv_one, map_one, nabs_one, inv_inv, Real.one_rpow, Units.val_one, Complex.ofReal_one,
    one_mul, Matrix.mul_one]

theorem om_eq_mul_om_triv {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (h : GL b k) (Ψ : Matrix b a k → ℂ) :
    om μ (1 : GL a k) h Ψ = fun z => (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) * om 1 (1 : GL a k) h Ψ z := by
  funext z
  simp only [om, map_one, MonoidHom.one_apply, inv_one, Units.val_one]
  ring

theorem opE_const_mul [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (s : ℂ)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun z => s * Ψ z) x₀ = s * opE ψ ν p Ψ x₀ := by
  unfold opE
  rw [← integral_const_mul]
  simp only [mul_assoc]

end GlobalTheory.LocFlat.CellSupport

namespace GlobalTheory.LocFlat
open GlobalTheory.LocFlat.CellSupport

theorem flCol_support_finite_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k),
    ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p →
    p ≤ c → ∀ (μ : kˣ →* ℂˣ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsOpen (J : Set (GL (n ⊕ Fin c) k)) →
    ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (a : GL (n' ⊕ Fin (c + 1)) k),
    ∃ T : Finset (GL (n ⊕ Fin c) k), ∀ x : GL (n ⊕ Fin c) k, GlobalTheory.LocFlat.flCol ψ ν p (om μ a x Φ.1) ≠ 0 →
      ∃ β : n → k, ∃ r ∈ R k n c p, ∃ t ∈ T, ∃ j ∈ J, x = colE c p β * r * t * j := by
  intro k _ _ _ _ _ _ ψ hψc hψ ν hν n n' _ _ _ _ c p hp1 hpc μ J hJ Φ a
  obtain ⟨T, -, hT⟩ := GlobalTheory.PosOne.covers_opE_finite k n n' c p hp1 hpc ψ hψc hψ ν 1
    (by rw [MonoidHom.ker_one]; exact isOpen_univ) J hJ ⟨om μ a 1 Φ.1, om_mem_SB μ a 1 Φ.2⟩
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨X, hX⟩ := Function.ne_iff.1 hx
  rw [flCol_eq_opE_colE k ψ ν hψc hν n n' c p hp1 hpc _ (om_mem_SB μ a x Φ.2) X] at hX
  set β : n → k := fun r => X r (Sum.inr ()) with hβ
  replace hX : opE ψ ν p (om μ 1 (colE c p β)⁻¹ (om μ a x Φ.1)) X.toCols₁ ≠ 0 := by
    rw [om_inv_of_det_one μ _ (det_colE c p β)]
    exact hX
  rw [← om_mul] at hX
  have e : om μ (1 * a) ((colE c p β)⁻¹ * x) Φ.1 = om μ 1 ((colE c p β)⁻¹ * x) (om μ a 1 Φ.1) := by
    rw [← om_mul, mul_one]
  rw [e, om_eq_mul_om_triv, opE_const_mul] at hX
  obtain ⟨t, ht, hd⟩ := hT ((colE c p β)⁻¹ * x) (Function.ne_iff.2 ⟨X.toCols₁, right_ne_zero_of_mul hX⟩)
  obtain ⟨r, hr, j, hj, hx'⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hd.symm
  refine ⟨β, r, hr, t, ht, j, hj, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_assoc r, ← hx', mul_inv_cancel_left]

end GlobalTheory.LocFlat
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymSupport

noncomputable section
namespace GlobalTheory.SymSupportP

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem exists_factor {g : GL (n ⊕ Fin c) k} (hg : g ∈ KO k _) (p : ℕ) (T : n → Prop)
    (h1 : ∀ l s, T s → p ≤ l.val + 1 → valuation k (g.val (.inr l) (.inl s)) < 1)
    (h2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r →
      valuation k (g.val r (.inr i) - (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)) < 1) :
    ∃ u ∈ KOne k (n ⊕ Fin c), ∃ D : Matrix (Fin c) n k, IntM D ∧ (∀ l s, T s → D l s = 0) ∧
      ∀ a b, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
        (g * u * lowU D).val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b := by
  classical
  let P : n ⊕ Fin c → n ⊕ Fin c → Prop := fun r s =>
    Sum.elim (fun s => T s ∧ ∃ l : Fin c, r = .inr l ∧ p ≤ l.val + 1)
      (fun i => lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r) s
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
    Matrix.of fun r s => if P r s then (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s else g.val r s
  obtain ⟨u, hu, e⟩ := exists_mul_KOne hg (M := M) (fun r s => by
    by_cases hP : P r s
    · rw [Matrix.sub_apply, Valuation.map_sub_swap,
        show M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s from if_pos hP]
      rcases s with s | i
      · obtain ⟨hT, l, rfl, hl⟩ := hP
        simpa using h1 l s hT hl
      · exact h2 r i hP
    · rw [Matrix.sub_apply, show M r s = g.val r s from if_neg hP]; simp)
  have hM : IntM M := e ▸ intM_of_mem_KO (mul_mem hg (KOne_le_KO hu))
  have m2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r →
      M r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) :=
    fun r i hl => if_pos hl
  have m1 : ∀ (l : Fin c) s, T s → p ≤ l.val + 1 → M (.inr l) (.inl s) = 0 := fun l s hT hl => by
    have : M (.inr l) (.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (.inr l) (.inl s) :=
      if_pos ⟨hT, l, rfl, hl⟩
    simpa using this
  have hd : M.toBlocks₂₂.det = 1 := by
    rw [det_of_upperTriangular, Finset.prod_eq_one]
    · intro i _
      simpa [toBlocks₂₂] using m2 (.inr i) i le_rfl
    · intro i j hij
      have := m2 (.inr i) j (by simpa [lev] using (show j < i from hij).le)
      simpa [toBlocks₂₂, (show j < i from hij).ne'] using this
  obtain ⟨V, hV, hUV⟩ := exists_int_inv (U := M.toBlocks₂₂) (fun i j => hM _ _) hd
  let D : Matrix (Fin c) n k := Matrix.of fun l s => if T s then 0 else -(V * M.toBlocks₂₁) l s
  have hVM : IntM (V * M.toBlocks₂₁) := hV.mul fun i j => hM _ _
  refine ⟨u, hu, D, fun i j => ?_, fun l s hT => if_pos hT, ?_⟩
  · by_cases hT : T j
    · simp [D, hT, zero_mem]
    · simpa [D, hT] using neg_mem (hVM i j)
  · intro a b hl hab
    rw [Units.val_mul, e]
    change (M * (fromBlocks 1 0 D 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) a b = _
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [fromBlocks_multiply]
    rcases b with x | i
    · rcases a with y | l
      · simp at hab
      · have hl' : p ≤ l.val + 1 := by simpa [lev] using hl
        simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₁, Matrix.add_apply]
        by_cases hT : T x
        · have : (M.toBlocks₂₂ * D) l x = 0 := by
            rw [Matrix.mul_apply]
            exact Finset.sum_eq_zero fun m _ => by simp [D, hT]
          rw [this, add_zero]
          simpa [toBlocks₂₁] using m1 l x hT hl'
        · have : (M.toBlocks₂₂ * D) l x = (M.toBlocks₂₂ * (-(V * M.toBlocks₂₁))) l x := by
            simp only [Matrix.mul_apply]
            exact Finset.sum_congr rfl fun m _ => by simp [D, hT]
          rw [this, Matrix.mul_neg, ← Matrix.mul_assoc, hUV, Matrix.one_mul]
          simp
    · rcases a with y | l
      · simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₁₂]
        simpa [toBlocks₁₂] using m2 (.inl y) i hl
      · simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₂]
        simpa [toBlocks₂₂] using m2 (.inr l) i hl

end Local

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem supportAt (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t) :
    S.SupportAt t := by
  intro j c H p hp1 hpc h hh x₀ e hΦ
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  let B := (typeFrame S.ϖ o).bas
  let B' := (typeFrame S.ϖ o').bas
  have hG : B⁻¹ * h * B ∈ KO k _ := mem_stabLat.1 hh
  let Z := (B⁻¹).val * affPt p x₀ e * B'.val
  let J := (S.P.iter t S.μ S.tame (j + 1)).reindex o
  have hΦ' : (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o').submatrix ((ixSucc _ t j).trans o) id) ≠ 0 := by
    have e1 : ((B⁻¹ * h * B)⁻¹).val * Z = (B⁻¹).val * ((h⁻¹).val * affPt p x₀ e) * B'.val := by
      simp only [Z, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B.val, Units.mul_inv, Matrix.one_mul]
    have e2 : ((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o' = (((B⁻¹ * h * B)⁻¹).val * Z).submatrix id o' := rfl
    rw [e2, e1]
    exact hΦ
  obtain ⟨κ₀, hκ, hc⟩ := exists_match _ _ _ hG _ hΦ'
  have hκ' : κ₀ ∈ J.J := hκ
  have hZ : ∀ r s, Z r s = Sum.elim (fun _ => 1) (fun i : Fin c => ((S.ϖ : k) ^ (i.val + 1))⁻¹) r *
      affPt p x₀ e r s * Sum.elim (fun _ => 1) (fun i : Fin (c + 1) => (S.ϖ : k) ^ (i.val + 1)) s := by
    intro r s
    simp only [Z, B, B', typeFrame_val, typeFrame_inv_val, mul_diagonal, diagonal_mul]
  obtain ⟨u, hu, D, hD, hD0, hpat⟩ := exists_factor (mul_mem hG (J.le_KO hκ')) p
    (fun s => ∃ i, s = .inl (.inl i)) (by
      rintro l _ ⟨i, rfl⟩ hl
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val (.inr l) (.inl (.inl (.inl i))) -
        Z (.inr l) (.inl (.inl (.inl i)))) < 1 := hc (.inr l) (.inl (.inl i))
      have hf : ¬ (l.val + 1 < p) := by omega
      rwa [hZ, show affPt p x₀ e (.inr l) (.inl (.inl (.inl i))) = 0 by simp [affPt, basePt, Free, hf],
        mul_zero, zero_mul, sub_zero] at h1) (by
      intro r i hl
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val r (o (.inl (.inr ⟨i.val, by omega⟩))) -
        Z r (o' (.inl (.inr ⟨i.castSucc.val, by simp; omega⟩)))) < 1 := hc r (.inl (.inr ⟨i.val, by omega⟩))
      rw [standardOrderExtendedBasis_apply_low_block, standardOrderExtendedBasis_apply_low_block, hZ] at h1
      convert h1 using 3
      rcases r with r | r
      · have : ¬ (p < i.val + 1) := by simpa [lev] using hl
        simp [affPt, basePt, Free, this]
      · have : ¬ r < i := by simpa [lev] using hl
        by_cases hri : r = i
        · subst hri; simp [affPt, basePt, Free]
        · simp [affPt, basePt, Free, this, hri, Fin.val_inj])
  have hlowK : lowU D ∈ KO k _ := mem_KO.2 ⟨intM_fromBlocks.2 ⟨intM_one, intM_zero, hD, intM_one⟩,
      intM_fromBlocks.2 ⟨intM_one, intM_zero, hD.neg, intM_one⟩⟩
  have hlow : lowU D ∈ J.J := by
    refine (hP (j + 1) ((reGL o).symm (lowU D))).2 ⟨?_, fun a b hab => ?_⟩
    · obtain ⟨h1, h2⟩ := mem_KO.1 hlowK
      exact mem_KO.2 ⟨fun a b => h1 _ _, fun a b => by rw [← map_inv]; exact h2 _ _⟩
    · have : (lowU D).val (o a) (o b) = (1 : Matrix _ _ k) (o a) (o b) := by
        obtain ⟨a, rfl⟩ := o.symm.surjective a
        obtain ⟨b, rfl⟩ := o.symm.surjective b
        rw [o.apply_symm_apply, o.apply_symm_apply]
        rcases a with a | a <;> rcases b with b | b
        · simp [lowU, Matrix.one_apply]
        · simp [lowU]
        · have a1 : o.symm (.inr a) = .inl (.inr ⟨a.val, by omega⟩) :=
            o.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block _ t _ _ _ a).symm
          rcases b with (b | b) | b
          · simpa [lowU] using hD0 a _ ⟨b, rfl⟩
          · have a3 : o.symm (.inl (.inl (.inr b))) = .inl (.inr ⟨c + b.val, by omega⟩) :=
              o.symm_apply_eq.2 (stdOrd_f _ t _ _ _ b).symm
            rw [a1, a3] at hab
            exact absurd (show a.val < c + b.val by omega) hab
          · have a6 : o.symm (.inl (.inr b)) = .inr b := o.symm_apply_eq.2 rfl
            rw [a1, a6] at hab
            exact absurd trivial hab
        · simp [lowU, Matrix.one_apply]
      rw [reGL_symm_val, submatrix_apply, this]
      simp [Matrix.one_apply]
  let kap := κ₀ * u * lowU D
  have hkap : kap ∈ J.J := mul_mem (mul_mem hκ' (J.KOne_le hu)) hlow
  have hbas : (typeFrame S.ϖ (Equiv.refl (XIx (Fin κ) t (j + 1) ⊕ Fin c))).bas = B :=
    Units.ext (by rw [typeFrame_val, typeFrame_val])
  have hconj : B⁻¹ * (h * (B * kap * B⁻¹)) * B = B⁻¹ * h * B * κ₀ * u * lowU D := by
    simp only [kap]; group
  obtain ⟨r, hr, u', hu', eq⟩ := GlobalTheory.T.exists_rootExchangeParabolic_mul_principalCongruence k S.ϖ _ c p (h * (B * kap * B⁻¹))
    (by rw [hbas, hconj]
        exact mul_mem (mul_mem (mul_mem hG (J.le_KO hκ')) (KOne_le_KO hu)) hlowK)
    (by
      intro a b hl hab
      rw [hbas, hconj, hpat a b hl hab]
      simp)
  refine ⟨r, hr, u' * (B * kap⁻¹ * B⁻¹), ?_, ?_⟩
  · change (reGL o).symm (B⁻¹ * (u' * (B * kap⁻¹ * B⁻¹)) * B) ∈ (S.P.iter t S.μ S.tame (j + 1)).J
    have : B⁻¹ * (u' * (B * kap⁻¹ * B⁻¹)) * B = (B⁻¹ * u' * B) * kap⁻¹ := by group
    rw [this]
    rw [hbas] at hu'
    exact mul_mem (J.KOne_le hu') (inv_mem hkap)
  · calc h = (h * (B * kap * B⁻¹)) * (B * kap⁻¹ * B⁻¹) := by group
      _ = _ := by rw [eq]; group

end Main

theorem supportAt_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    S.Pattern t → S.SupportAt t :=
  fun _ _ _ _ _ s κ S t _ _ hP => supportAt s κ S t hP

end GlobalTheory.SymSupportP
end
end
