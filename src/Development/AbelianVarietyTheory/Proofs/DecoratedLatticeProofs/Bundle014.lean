module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle011
public import Mathlib.CategoryTheory.Category.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle013
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle044
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle002
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

section

open Matrix GlobalTheory.ClassFin

theorem _root_.GlobalTheory.T.siegelReduced_integral_form_bounded_entries : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) → B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) → (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X → ∀ i j, |(B i j : ℝ)| ≤ C' := by
  first | exact @GlobalTheory.RedBound.reduced_bound | exact GlobalTheory.RedBound.reduced_bound | (intros; apply GlobalTheory.RedBound.reduced_bound <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.CollapseCompare

section Average
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [AddCommGroup V] [Module ℂ V]

end Average

section Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

variable [MeasurableSpace k] [BorelSpace k]

variable {ν : Measure k} {μX : Measure (GL n k)} {μG : Measure (GL (n ⊕ Fin c) k)}
  {J : Subgroup (GL (n ⊕ Fin c) k)} {bas : GL (n ⊕ Fin c) k} {ψ : AddChar k Circle} {μ : kˣ →* ℂˣ}
  {lam : J →* ℂˣ} {κ : ℝ}






end Pointwise

section Transport
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}





variable [MeasurableSpace k] [BorelSpace k]

end Transport

section Normalise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical (frame)




theorem hasConductor_mulShift {ψ : AddChar k Circle} {β : kˣ} (h : HasConductor ψ β) :
    HasConductor (ψ.mulShift (β : k)) 1 := by
  have hβ : 0 < valuation k (β : k) := by simp [zero_lt_iff]
  intro x
  have h1 := h (β * x)
  rw [map_mul, mul_le_iff_le_one_right hβ] at h1
  rw [Units.val_one, map_one, ← h1]
  simp only [AddChar.mulShift_apply]
  refine ⟨fun H y hy => ?_, fun H y hy => H _ (by rw [map_mul]; exact mul_le_mul_right hy _)⟩
  have := H ((β⁻¹ : kˣ) * y) (by rwa [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hβ])
  simpa using this

variable [MeasurableSpace k] [BorelSpace k]

end Normalise

section Main

end Main

end GlobalTheory.CollapseCompare
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.AffineSB

theorem mem_SB_comp_affine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [DecidableEq R] [Fintype Q] (A : GL R k) (a : Matrix R Q k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => Φ (A.val * x + a)) ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ R Q _ _ _ A a Φ hΦ
  have hc : ∀ B : Matrix R R k, Continuous fun x : Matrix R Q k => B * x := fun B =>
    continuous_const.matrix_mul continuous_id
  let e : Matrix R Q k ≃ₜ Matrix R Q k :=
    { toFun := fun x => A.val * x + a
      invFun := fun y => (A⁻¹ : GL R k).val * (y - a)
      left_inv := fun x => by
        simp only [add_sub_cancel_right, ← Matrix.mul_assoc, Matrix.coe_units_inv]
        rw [Matrix.nonsing_inv_mul _ (by simpa using A.isUnit.map Matrix.detMonoidHom), Matrix.one_mul]
      right_inv := fun y => by
        simp only [← Matrix.mul_assoc, Matrix.coe_units_inv]
        rw [Matrix.mul_nonsing_inv _ (by simpa using A.isUnit.map Matrix.detMonoidHom), Matrix.one_mul, sub_add_cancel]
      continuous_toFun := (hc _).add continuous_const
      continuous_invFun := (hc _).comp (continuous_id.sub continuous_const) }
  exact ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩

end GlobalTheory.AffineSB
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.FlatFactor

theorem fill_add_single {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) (x : {e : m × m' // e ∈ it} → k) (e : m × m') (he : e ∈ it) (a : k) :
    fill ev it β t x + Matrix.single e.1 e.2 a = fill ev it β t (x + Pi.single ⟨e, he⟩ a) := by
  ext r q
  simp only [fill, Matrix.add_apply, Matrix.of_apply, Matrix.single_apply, Pi.add_apply]
  by_cases h : (r, q) ∈ it
  · rw [dif_pos h, dif_pos h]
    by_cases hrq : (r, q) = e
    · subst hrq
      simp [Pi.single_apply]
    · have h1 : ¬ (e.1 = r ∧ e.2 = q) := fun ⟨h1, h2⟩ => hrq (by rw [← h1, ← h2])
      have h2 : (⟨(r, q), h⟩ : {e : m × m' // e ∈ it}) ≠ ⟨e, he⟩ := fun h' => hrq (congrArg Subtype.val h')
      simp [h1, Pi.single_apply, h2]
  · rw [dif_neg h, dif_neg h]
    have h1 : ¬ (e.1 = r ∧ e.2 = q) := fun ⟨h1, h2⟩ => h (by rw [← h1, ← h2]; exact he)
    simp [h1]

theorem continuous_fill {k : Type} [Field k] [TopologicalSpace k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) : Continuous (fill ev it β t) := by
  refine continuous_pi fun r => continuous_pi fun q => ?_
  simp only [fill, Matrix.of_apply]
  by_cases h : (r, q) ∈ it
  · simp only [dif_pos h]; exact continuous_apply _
  · simp only [dif_neg h]; exact continuous_const

theorem hasCompactSupport_comp_fill {k : Type} [Field k] [TopologicalSpace k] [T2Space k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (ev it : Finset (m × m')) (β t : Matrix m m' k) (Θ : Matrix m m' k → ℂ) (hΘ : HasCompactSupport Θ) :
    HasCompactSupport (fun x => Θ (fill ev it β t x)) := by
  let pr : Matrix m m' k → ({e : m × m' // e ∈ it} → k) := fun T i => T i.1.1 i.1.2
  have hpr : Continuous pr := continuous_pi fun i => (continuous_apply i.1.2).comp (continuous_apply i.1.1)
  have hK : IsCompact (pr '' tsupport Θ) := hΘ.isCompact.image hpr
  refine HasCompactSupport.intro' hK hK.isClosed fun x hx => ?_
  by_contra h
  apply hx
  refine ⟨fill ev it β t x, subset_tsupport _ h, ?_⟩
  funext i
  simp [pr, fill, i.2]

theorem kerRed_translate_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ it, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
  intro k _ _ _ _ _ _ ψ ν _ _ hν m m' _ _ _ _ M _ _ l β ev it _ hK e he a Θ Θ' hΘ'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  rw [← sub_eq_zero, ← map_sub]
  apply hK
  intro t
  have hint : Integrable (fun x => Θ.1 (fill ev it β t x)) (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    ((Θ.2.1.continuous).comp (continuous_fill ev it β t)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_fill ev it β t Θ.1 Θ.2.2)
  have hint' : Integrable (fun x => Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)))
      (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    hint.comp_add_right _
  unfold red
  simp only [Submodule.coe_sub, Pi.sub_apply]
  have h1 : ∀ x, Θ'.1 (fill ev it β t x) = Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)) := by
    intro x; rw [hΘ', fill_add_single]
  simp_rw [h1]
  rw [integral_sub hint' hint, integral_add_right_eq_self (fun x => Θ.1 (fill ev it β t x)), sub_self]

end GlobalTheory.FlatFactor
end
end

section

open ValuativeRel

theorem _root_.GlobalTheory.T.padic_residueField_card_and_prime_irreducible : ∀ (T : ℕ) [Fact T.Prime], Nat.card (IsLocalRing.ResidueField 𝒪[ℚ_[T]]) = T ∧ Irreducible ((T : 𝒪[ℚ_[T]])) := by
  first | exact @GlobalTheory.TAdicInt.card_residueField_and_irreducible | exact GlobalTheory.TAdicInt.card_residueField_and_irreducible | (intros; apply GlobalTheory.TAdicInt.card_residueField_and_irreducible <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem exists_isConjAt_of_embedding (K : Type) [Field K] [NumberField K] [StarRing K]
    (h : ∃ σ : K →+* ℂ, ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) :
    ∃ v0 : InfinitePlace K, IsConjAt v0 := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨InfinitePlace.mk σ, fun a => ?_⟩
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e]; exact hσ a
  · rw [e]
    simp only [ComplexEmbedding.conjugate_coe_eq]
    rw [hσ a]

theorem isConjAt_exists_main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    (∃ σ : K →+* ℂ, ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) →
      ∃ v0 : InfinitePlace K, IsConjAt v0 :=
  fun K _ _ _ h => exists_isConjAt_of_embedding K h

end GlobalTheory
end

section

open MeasureTheory Topology

namespace GlobalTheory.CovolumeOneSelfDual

theorem unfold {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (hF : IsAddFundamentalDomain Γ 𝓕 μ) (c : G → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : Γ => ‖c (γ + y)‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' γ : Γ, c (γ + y) ∂μ := by
  have hm : ∀ γ : Γ, AEStronglyMeasurable (fun y => c (γ + y)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_left μ (γ : G)).quasiMeasurePreserving
    exact this.restrict
  have hl : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    rfl
  have hfin : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne
  refine ⟨?_, ?_⟩
  · have h1 : ∫⁻ y in 𝓕, ∑' γ : Γ, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : Γ, ‖c (γ + y)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : Γ, (‖c (γ + y)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  · rw [integral_tsum hm hfin, hF.integral_eq_tsum'' c hc]
    rfl

theorem finite_contributing {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] (Γ : AddSubgroup G) [DiscreteTopology Γ] {f : G → ℂ} (hs : HasCompactSupport f)
    {C : Set G} (hC : IsCompact C) : {γ : Γ | ∃ x ∈ C, f (γ + x) ≠ 0}.Finite := by
  have hK := (hs.isCompact.prod hC).image (f := fun p : G × G => p.1 - p.2) (by fun_prop)
  have ht : Filter.Tendsto ((↑) : Γ → G) Filter.cofinite (Filter.cocompact G) :=
    AddSubgroup.tendsto_coe_cofinite_of_discrete Γ (isDiscrete_iff_discreteTopology.2 inferInstance)
  have hfin := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, Filter.mem_cofinite] at hfin
  refine hfin.subset ?_
  rintro γ ⟨x, hx, h⟩ hn
  exact hn ⟨(γ + x, x), ⟨subset_tsupport f h, hx⟩, by simp⟩

theorem continuous_periodization {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [LocallyCompactSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] {f : G → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) : Continuous fun x : G => ∑' γ : Γ, f (γ + x) := by
  have hlf : LocallyFinite fun γ : Γ => Function.support fun x : G => f (γ + x) := by
    intro x
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    refine ⟨C, hx, (finite_contributing Γ hs hC).subset ?_⟩
    rintro γ ⟨p, h, h1⟩
    exact ⟨p, h1, h⟩
  have h : Continuous fun x : G => ∑ᶠ γ : Γ, f (γ + x) :=
    continuous_finsum (fun γ => by fun_prop) hlf
  refine h.congr fun x => (tsum_eq_finsum ?_).symm
  refine (finite_contributing Γ hs (isCompact_singleton (x := x))).subset ?_
  intro γ hγ
  exact ⟨x, rfl, hγ⟩

section

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
  (B : G → G → ℂ) (hc : ∀ y, Continuous fun x => B x y) (hsy : ∀ x y, B x y = B y x)
  (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hn : ∀ x y, ‖B x y‖ = 1)
  (hker : ∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) (hinj : ∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0)
  (μ : Measure G) (𝓕 : Set G) [hμ : μ.IsAddHaarMeasure] (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)

include hK hcov hc hsy hadd hn hker hinj hμ hF h1

theorem poisson {f : G → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hsum : Summable fun γ : Γ => ‖∫ x, f x * B x γ ∂μ‖) :
    ∑' ξ : Γ, f ξ = ∑' γ : Γ, ∫ x, f x * B x γ ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  have hcoef : ∀ γ : Γ, ∫ x in 𝓕, B γ x * (∑' ξ : Γ, f (ξ + x)) ∂μ = ∫ x, f x * B x γ ∂μ := by
    intro γ
    have hi : Integrable (fun x => f x * B x γ) μ :=
      (hf.mul (hc γ)).integrable_of_hasCompactSupport hs.mul_right
    rw [(unfold Γ μ 𝓕 hF _ hi).2]
    congr 1
    funext x
    rw [← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [hadd, (hker γ).2 γ.2 ξ ξ.2, one_mul, mul_comm, hsy]
  have key := GlobalTheory.CompactQuotientFourier.inversion_at_zero G Γ K hK hcov Γ (fun γ x => B γ x)
    (fun γ => hc' γ) (fun γ x y => hadd' γ x y) (fun a b x => hadd a b x) (fun a x => hn a x)
    (fun x => by rw [← hker x]; exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    (fun a h => Subtype.ext (hinj a a.2 h)) μ 𝓕 hμ hF h1 (fun x => ∑' ξ : Γ, f (ξ + x))
    (continuous_periodization Γ hf hs)
    (fun γ hγ x => by
      rw [← (Equiv.addRight (⟨γ, hγ⟩ : Γ)).tsum_eq fun ξ : Γ => f (ξ + x)]
      refine tsum_congr fun ξ => ?_
      simp [add_assoc])
    (by simp only [hcoef]; exact hsum)
  simp only [hcoef, add_zero] at key
  exact key

theorem inversion_zero {Φ : G → ℂ} (hΦ : Continuous Φ) (hs : HasCompactSupport Φ)
    (hI : Integrable (fun y => ∫ x, Φ x * B x y ∂μ) μ) :
    ∫ y, (∫ x, Φ x * B x y ∂μ) ∂μ = Φ 0 := by
  classical
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hvol : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  obtain ⟨hae, hint⟩ := unfold Γ μ 𝓕 hF _ hI
  have he : ∀ (y : G) (γ : Γ), ∫ x, Φ x * B x (γ + y) ∂μ = ∫ x, (Φ x * B x y) * B x γ ∂μ := by
    intro y γ
    congr 1
    funext x
    rw [hadd']
    ring
  have h2 : ∫ y in 𝓕, ∑' γ : Γ, (∫ x, Φ x * B x (γ + y) ∂μ) ∂μ = ∫ y in 𝓕, ∑' ξ : Γ, Φ ξ * B ξ y ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [he] at hy ⊢
    exact (poisson Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1 (hΦ.mul (hc y)) hs.mul_right hy).symm
  have hfin : {ξ : Γ | Φ ξ ≠ 0}.Finite := by
    refine (finite_contributing Γ hs (isCompact_singleton (x := (0 : G)))).subset ?_
    intro ξ hξ
    exact ⟨0, rfl, by simpa using hξ⟩
  have hFi : ∀ ξ : Γ, Integrable (fun y => Φ ξ * B ξ y) (μ.restrict 𝓕) := fun ξ =>
    Integrable.of_bound (continuous_const.mul (hc' ξ)).aestronglyMeasurable ‖Φ ξ‖
      (Filter.Eventually.of_forall fun y => by rw [norm_mul, hn, mul_one])
  have hFs : Summable fun ξ : Γ => ∫ y in 𝓕, ‖Φ ξ * B ξ y‖ ∂μ := by
    refine summable_of_hasFiniteSupport (hfin.subset ?_)
    intro ξ hξ h0
    exact hξ (by simp [h0])
  have horth : ∀ ξ : Γ, ξ ≠ 0 → ∫ y in 𝓕, B ξ y ∂μ = 0 := by
    intro ξ hξ
    obtain ⟨u, hu⟩ : ∃ u, B ξ u ≠ 1 := by
      by_contra h
      push_neg at h
      exact hξ (Subtype.ext (hinj ξ ξ.2 h))
    have key := GlobalTheory.CompactQuotientFourier.setIntegral_translate Γ μ 𝓕 hF (B ξ)
      (fun γ hγ w => by rw [hadd', (hker γ).2 hγ ξ ξ.2, one_mul]) u
    simp_rw [hadd' _ _ u] at key
    rw [integral_mul_const] at key
    have h3 : (∫ y in 𝓕, B ξ y ∂μ) * (B ξ u - 1) = 0 := by
      rw [mul_sub, key, mul_one, sub_self]
    exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hu)
  have hB0 : ∀ y, B 0 y = 1 := fun y => by
    rw [hsy]
    have hne : B y 0 ≠ 0 := fun h => by simpa [h] using hn y 0
    have h2 : B y 0 * B y 0 = B y 0 * 1 := by rw [mul_one, ← hadd', add_zero]
    exact mul_left_cancel₀ hne h2
  rw [hint, h2, ← integral_tsum_of_summable_integral_norm hFi hFs, tsum_eq_single (0 : Γ)]
  · simp [hB0, hvol]
  · intro ξ hξ
    rw [integral_const_mul, horth ξ hξ, mul_zero]

end

theorem selfDual_of_covolume_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ B : G → G → ℂ, (∀ y, Continuous fun x => B x y) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, ‖B x y‖ = 1) → (∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) → (∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0) → ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ B := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hμ hF h1
  refine ⟨hμ, fun Φ hΦ hs hI z => ?_⟩
  have he : ∀ y, ∫ x, Φ (x - z) * B x y ∂μ = (∫ x, Φ x * B x y ∂μ) * B y z := by
    intro y
    rw [← integral_add_right_eq_self (fun x => Φ (x - z) * B x y) z, ← integral_mul_const]
    congr 1
    funext x
    rw [add_sub_cancel_right, hadd, hsy z y, mul_assoc]
  have hs' : HasCompactSupport fun x => Φ (x - z) := hs.comp_homeomorph (Homeomorph.subRight z)
  have hI' : Integrable (fun y => ∫ x, Φ (x - z) * B x y ∂μ) μ := by
    simp only [he]
    exact hI.mul_bdd (c := 1) (hc z).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (hn y z).le)
  have key := inversion_zero Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1
    (Φ := fun x => Φ (x - z)) (by fun_prop) hs' hI'
  simp only [he, zero_sub] at key
  exact key

end GlobalTheory.CovolumeOneSelfDual
end

section

open Module NumberField Formalism.BasicNotions

namespace GlobalTheory.HalfRankSub

theorem fg_of_le_fg {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {L X : Submodule R M} (hL : L.FG) (hX : X ≤ L) : X.FG := by
  haveI : IsNoetherian R L := isNoetherian_of_fg_of_noetherian L hL
  have h1 : (X.comap L.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map L.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hX] at h2

end GlobalTheory.HalfRankSub
end
