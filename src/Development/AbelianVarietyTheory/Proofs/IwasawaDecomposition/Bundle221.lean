module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle210
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Derivation.Lie
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift

variable {ι : Type} {m n : ℕ}

def rowDer (n : ℕ) (τ : ι) (k l : Fin m) : Derivation ℂ (Pol ι m n) (Pol ι m n) :=
  ∑ c : Fin n, (X (τ, k, c) : Pol ι m n) • pderiv (τ, l, c)

theorem rowDer_apply (τ : ι) (k l : Fin m) (P : Pol ι m n) :
    rowDer n τ k l P = rowLie n τ k l P := by
  rw [rowLie_apply, rowDer]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]; simp

open Classical in
theorem rowLie_X (τ : ι) (k l : Fin m) (v : ι × Fin m × Fin n) :
    rowLie n τ k l (X v) = if v.1 = τ ∧ v.2.1 = l then X (τ, k, v.2.2) else 0 := by
  obtain ⟨t, i, c⟩ := v
  rw [rowLie_apply, Finset.sum_eq_single c]
  · by_cases h : t = τ ∧ i = l
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [pderiv_X_of_ne (by simpa using h)]
      simp [h]
  · intro b _ hb
    rw [pderiv_X_of_ne (by simp [hb.symm]), mul_zero]
  · simp


open Classical in
theorem rowLie_diag_comm (t t' : ι) (i k l : Fin m) :
    rowLie n t i i * rowLie n t' k l - rowLie n t' k l * rowLie n t i i =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        rowLie n t' k l := by
  have h : ⁅rowDer n t i i, rowDer n t' k l⁆ =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        rowDer n t' k l := by
    refine derivation_ext fun v => ?_
    obtain ⟨s, j, c⟩ := v
    simp only [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply, rowLie_X,
      apply_ite (rowLie n t i i), apply_ite (rowLie n t' k l), map_zero]
    by_cases h1 : t = t' <;> by_cases h2 : s = t' <;> by_cases h3 : j = l <;>
      by_cases h4 : i = k <;> by_cases h5 : i = l <;> simp_all [eq_comm]
  refine LinearMap.ext fun P => ?_
  have := DFunLike.congr_fun h P
  simp only [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply] at this
  exact this

theorem iSup_iInf_eigenspace_rowLie :
    ⨆ κ : ι → Fin m → ℤ, (⨅ t, ⨅ i,
      Module.End.eigenspace (rowLie n t i i : Module.End ℂ (Pol ι m n)) (κ t i : ℂ)) = ⊤ := by
  rw [eq_top_iff]
  rintro P -
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => exact add_mem hP hQ
  | monomial s a =>
    refine Submodule.mem_iSup_of_mem (fun t i => ∑ c, (s (t, i, c) : ℤ)) ?_
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro t i
    rw [rowLie_apply]
    simp only [X_mul_pderiv_monomial]
    push_cast
    rw [Finset.sum_smul]
    simp only [Nat.cast_smul_eq_nsmul]

theorem exists_totalDegree_le_of_finiteDimensional {X : Type} [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (Φ : X →ₗ[ℂ] Pol ι m n) : ∃ d, ∀ x, (Φ x).totalDegree ≤ d := by
  let b := Module.finBasis ℂ X
  refine ⟨Finset.univ.sup fun j => (Φ (b j)).totalDegree, fun x => ?_⟩

  rw [← b.sum_repr x, map_sum]
  refine totalDegree_finsetSum_le fun j _ => ?_
  rw [map_smul]
  exact (totalDegree_smul_le _ _).trans
    (Finset.le_sup (f := fun j => (Φ (b j)).totalDegree) (Finset.mem_univ j))

theorem colHighest_intertwiner_proportional :
    ∀ (ι : Type) [Fintype ι] (m n : ℕ), n ≤ m → ∀ (X : Type) [AddCommGroup X] [Module ℂ X]
      [FiniteDimensional ℂ X] (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X), IrrFam π →
      ∀ (Φ Ψ : X →ₗ[ℂ] Pol ι m n) (μ μ' : ι → Fin n → ℤ), Φ ≠ 0 →
      (∀ τ u x, Φ (π τ u x) = rowSub n τ u (Φ x) ∧ Ψ (π τ u x) = rowSub n τ u (Ψ x)) →
      (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0 ∧ colLie m τ k l ∘ₗ Ψ = 0) →
      (∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ ∧ colLie m τ k k ∘ₗ Ψ = (μ' τ k : ℂ) • Ψ) →
      ∃ r : ℂ, Ψ = r • Φ := by
  classical
  intro ι _ m n hnm X _ _ _ π hπ Φ Ψ μ μ' hΦ heq hup hwt
  have hker : LinearMap.ker Φ = ⊥ := by
    refine (hπ _ fun τ u x hx => ?_).resolve_right fun h => hΦ (LinearMap.ker_eq_top.1 h)
    rw [LinearMap.mem_ker] at hx ⊢
    rw [(heq τ u x).1, hx, map_zero]
  have hinj : Function.Injective Φ := LinearMap.ker_eq_bot.1 hker
  obtain ⟨d₁, hd₁⟩ := exists_totalDegree_le_of_finiteDimensional Φ
  obtain ⟨d₂, hd₂⟩ := exists_totalDegree_le_of_finiteDimensional Ψ
  have hA : ∀ τ k l x, ∃ y, Φ y = rowLie n τ k l (Φ x) ∧ Ψ y = rowLie n τ k l (Ψ x) := by
    intro τ k l x
    obtain ⟨s, c, hc⟩ := GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie ι m n (max d₁ d₂) τ k l
    refine ⟨∑ u ∈ s, c u • π τ u x, ?_, ?_⟩

    · rw [← hc _ ((hd₁ x).trans (le_max_left _ _)), map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_smul, (heq τ u x).1]

    · rw [← hc _ ((hd₂ x).trans (le_max_right _ _)), map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_smul, (heq τ u x).2]
  obtain ⟨_, ⟨x, rfl⟩, hx0, hhi, κ, hκ⟩ := GlobalTheory.exists_highest_vector
    (fun τ k l => (rowLie n τ k l : Module.End ℂ (Pol ι m n)))
    (fun t t' i k l => by convert rowLie_diag_comm (n := n) t t' i k l)
    iSup_iInf_eigenspace_rowLie (LinearMap.range Φ)
    (by
      rintro τ k l _ ⟨x, rfl⟩
      obtain ⟨y, hy, -⟩ := hA τ k l x
      exact ⟨y, hy⟩)
    (fun h => hΦ (LinearMap.range_eq_bot.1 h))
  obtain ⟨r, hr⟩ := GlobalTheory.DefLift.joint_highest_proportional ι m n hnm (Φ x) (Ψ x) κ μ μ' hx0
    (fun τ k l hkl => ⟨hhi τ k l hkl, by
      obtain ⟨y, hy, hy'⟩ := hA τ k l x
      have : y = 0 := hinj (by rw [hy, map_zero]; exact hhi τ k l hkl)
      rw [← hy', this, map_zero]⟩)
    (fun τ k => ⟨hκ τ k, by
      obtain ⟨y, hy, hy'⟩ := hA τ k k x
      have : y = (κ τ k : ℂ) • x := hinj (by rw [hy, map_smul]; exact hκ τ k)
      rw [← hy', this, map_smul]⟩)
    (fun τ k l hkl => ⟨LinearMap.congr_fun (hup τ k l hkl).1 x,
      LinearMap.congr_fun (hup τ k l hkl).2 x⟩)
    (fun τ k => ⟨LinearMap.congr_fun (hwt τ k).1 x, LinearMap.congr_fun (hwt τ k).2 x⟩)
  refine ⟨r, sub_eq_zero.1 (LinearMap.ker_eq_top.1 ((hπ _ fun τ u y hy => ?_).resolve_left
    fun h => hx0 ?_))⟩
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hy ⊢
    rw [(heq τ u y).1, (heq τ u y).2, hy, map_smul]
  · have : x ∈ LinearMap.ker (Ψ - r • Φ) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, hr, sub_self]
    rw [h, Submodule.mem_bot] at this
    rw [this, map_zero]

end GlobalTheory.DefLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_degree_bound_of_rowUnitary_invariant_pairing : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X) (β : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ), (∀ τ u P x, β (rowSub n τ u P) (π τ u x) = β P x) → ∃ d : ℕ, ∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → β (MvPolynomial.monomial α 1) = 0 := by
  first | exact @GlobalTheory.RowSupport.exists_degree_bound | exact GlobalTheory.RowSupport.exists_degree_bound | (intros; apply GlobalTheory.RowSupport.exists_degree_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_bilinearFischerPairing_matrixEntryPolynomialRing : ∀ (ι : Type) [Fintype ι] (m n : ℕ), ∃ B : Pol ι m n →ₗ[ℂ] Pol ι m n →ₗ[ℂ] ℂ, (∀ Q, (∀ P, B P Q = 0) → Q = 0) ∧ (∀ a b P Q, B (subst a b P) Q = B P (subst (fun τ => (a τ).transpose) (fun τ => (b τ).transpose) Q)) ∧ ∀ (ℓ : Pol ι m n →ₗ[ℂ] ℂ) (d : ℕ), (∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → ℓ (MvPolynomial.monomial α 1) = 0) → ∃ Q, ∀ P, B P Q = ℓ P := by
  first | exact @GlobalTheory.DefLift.BilFischer.exists_pair | exact GlobalTheory.DefLift.BilFischer.exists_pair | (intros; apply GlobalTheory.DefLift.BilFischer.exists_pair <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicitySpace_definite_continuous_invariant_equivariant : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ), AllPlus M → (∀ τ, M.sm τ = ⊤) → Function.Injective (inclT M) → IsTensAct M π → ∀ L ∈ MultT θ M J χ, ∀ x, Continuous (L x) ∧ (∀ γ ∈ GQ V, ∀ h, L x (γ * h) = L x h) ∧ ∀ τ u, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x) := by
  first | exact @GlobalTheory.multT_cont_left_equiv | exact GlobalTheory.multT_cont_left_equiv | (intros; apply GlobalTheory.multT_cont_left_equiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tensorProduct_definiteUnitary_localModels_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤) → AllPlus M → FiniteDimensional ℂ (SmT M) ∧ Function.Injective (inclT M) ∧ ∃ π, IsTensAct M π ∧ IrrFam π := by
  first | exact @GlobalTheory.DefLift.tensor_irreducible | exact GlobalTheory.DefLift.tensor_irreducible | (intros; apply GlobalTheory.DefLift.tensor_irreducible <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_colStable_complement_of_lt : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (U W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)), (∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) → (∀ Φ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ W) → U < W → ∃ U' : Submodule ℂ (X →ₗ[ℂ] Pol ι m n), U' ≠ ⊥ ∧ U' ≤ W ∧ U ⊓ U' = ⊥ ∧ ∀ Φ ∈ U', ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U' := by
  first | exact @GlobalTheory.DefLift.exists_colStable_disjoint | exact GlobalTheory.DefLift.exists_colStable_disjoint | (intros; apply GlobalTheory.DefLift.exists_colStable_disjoint <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_sum_unitarySubstitutions_eq_rowLie : ∀ (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin m), ∃ (s : Finset (Matrix.unitaryGroup (Fin m) ℂ)) (c : Matrix.unitaryGroup (Fin m) ℂ → ℂ), ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ u ∈ s, c u • rowSub n τ u P = rowLie n τ k l P := by
  first | exact @GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie | exact GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie | (intros; apply GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

theorem AllPlus.finite_smooth_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), AllPlus M → ∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro D V S M h τ
  obtain ⟨h1, h2, -, -, -, h3, -⟩ := GlobalTheory.CompactModel.model_allPos D V S M τ (funext fun a => h τ a)
  exact ⟨h1, h2, fun U hU => h3 U le_top fun g hg => hU ⟨g, hg.1⟩⟩

end GlobalTheory.DefLift

end
end

section

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric
open Classical

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def flagRoot {H : Host E} (Dw : Datum H) (x : Root Dw.mult) :
    MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : x.1 (H.rt : E) = H.rt0 then
    X (⟨x.1, h⟩, ⟨x.2, by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_mem Dw h; omega⟩)
  else
    -X (⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩,
      ⟨Dw.p + (Dw.q - 1 - x.2), by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_not_mem Dw h; omega⟩)

def flagMap {H : Host E} (Dw : Datum H) :
    MvPolynomial (Root Dw.mult) ℝ →ₐ[ℝ] MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  aeval (flagRoot Dw)

def flagLin (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) : MvPolynomial (ι × Fin N) ℝ →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ Formalism.DegreeFormula.dimFl ι N) • ∑ σ : ι → Equiv.Perm (Fin N),
    (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (Formalism.DegreeFormula.permExp σ)

theorem flagLin_apply (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    flagLin ι N P = Formalism.DegreeFormula.degFl ι N P := by
  simp [flagLin, Formalism.DegreeFormula.degFl, LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]

def schubGam {H : Host E} (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ :=
  flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) ∘ₗ (flagMap Dw).toLinearMap ∘ₗ
    LinearMap.mulRight ℝ (fibrePoint Dw.mult) ∘ₗ (chernRoots Dw.mult).toLinearMap

theorem schubGam_apply {H : Host E} (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    schubGam Dw P = Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (flagMap Dw (chernRoots Dw.mult P * fibrePoint Dw.mult)) := by
  simp [schubGam, flagLin_apply]

def admitted (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P, Θ (GlobalTheory.PointChern.relPoly τ k * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Θ ((X (τ, 0) - 1) * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (k : ℕ), Dw.mult τ < k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (X (τ, k) * P) = 0) ∧
  (∀ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) →
    Θ (monomial d 1) = 0)

end GlobalTheory.Schubert
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle.Transfer

variable {ι : Type} {m : ι → ℕ}

theorem inv_mul_cancel_left {K : Type} [Field K] {g : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (X : Mat m K) :
    g⁻¹ * (g * X) = X := by
  rw [← mul_assoc, Mat.inv_mul hg, one_mul]

theorem mul_inv_cancel_left {K : Type} [Field K] {g : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (X : Mat m K) :
    g * (g⁻¹ * X) = X := by
  rw [← mul_assoc, Mat.mul_inv hg, one_mul]

theorem det_mul_ne {K : Type} [Field K] {g g' : Mat m K} (hg : ∀ τ, (g τ).det ≠ 0) (hg' : ∀ τ, (g' τ).det ≠ 0)
    (τ : ι) : ((g * g') τ).det ≠ 0 := by
  rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hg τ) (hg' τ)

theorem par_of_three {K : Type} [Field K] {k : ι → ℕ} {h h' P Q E L : Mat m K} (hP : ∀ τ, (P τ).det ≠ 0)
    (hQ : ∀ τ, (Q τ).det ≠ 0) (hE : ∀ τ, (E τ).det ≠ 0) (hL : Par k ⊤ L) (G1 : Par k ⊤ (h * P⁻¹))
    (G2 : Par k ⊤ (h' * (L * (P * E))⁻¹)) (G3 : Par k ⊤ (h' * (Q * E)⁻¹)) : Par k ⊤ (h * Q⁻¹) := by
  have hh' : ∀ τ, (h' τ).det ≠ 0 := fun τ => by
    have := G3.det_ne τ
    rw [Pi.mul_apply, Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  have hLPE : ∀ τ, ((L * (P * E)) τ).det ≠ 0 := det_mul_ne hL.det_ne (det_mul_ne hP hE)
  have e : h * Q⁻¹ = h * P⁻¹ * L⁻¹ * (h' * (L * (P * E))⁻¹)⁻¹ * (h' * (Q * E)⁻¹) := by
    rw [Mat.mul_inv_rev h', Mat.inv_inv hLPE, Mat.mul_inv_rev Q E]
    simp only [mul_assoc]
    rw [inv_mul_cancel_left hh', mul_inv_cancel_left hE, inv_mul_cancel_left hL.det_ne,
      inv_mul_cancel_left hP]
  rw [e]
  exact ((G1.mul hL.inv).mul G2.inv).mul G3

variable {F : Type} [Field F]

theorem sp_specializes {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) (w : Sp K) :
    p w ⤳ p (IsLocalRing.closedPoint K) := by
  rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]

theorem val_map_mul {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k k' : ι → ℕ} {g g' : Mat m Y.Fn}
    (hg : Par k ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g)
    (hg' : Par k' ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g') :
    (g * g').map ((ratOf Y).val p) = g.map ((ratOf Y).val p) * g'.map ((ratOf Y).val p) :=
  hg.map_mul_of hg' _ (RatModel.valHomOf p _ (sp_specializes p)) fun _ => rfl

theorem val_map_par {Y : Var F} {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k : ι → ℕ} {g : Mat m Y.Fn}
    (hg : Par k ((ratOf Y).O (p (IsLocalRing.closedPoint K))).toSubring g) :
    Par k ⊤ (g.map ((ratOf Y).val p)) :=
  hg.map_of _ (RatModel.valHomOf p _ (sp_specializes p)) fun _ => rfl

theorem frame_change {X Y : Var F} (ψ : X.Fn →ₐ[F] Y.Fn) (A B : Mat m X.Fn) (hA : ∀ τ, (A τ).det ≠ 0)
    : ∀ C : Mat m Y.Fn, C * (B.map ψ)⁻¹ = (C * (A.map ψ)⁻¹) * (A * B⁻¹).map ψ := by
  intro C
  have hA' : ∀ τ, ((A.map ψ) τ).det ≠ 0 := fun τ => by
    have e : (A.map ψ τ).det = ψ (A τ).det := Mat.det_map A ψ.toRingHom τ
    rw [e]; exact (map_ne_zero _).2 (hA τ)
  have e1 : (A * B⁻¹).map ψ = A.map ψ * B⁻¹.map ψ := Mat.map_mul A B⁻¹ ψ.toRingHom
  have e2 : B⁻¹.map ψ = (B.map ψ)⁻¹ := Mat.map_inv B ψ.toRingHom
  rw [e1, e2]
  show C * (B.map ψ)⁻¹ = C * (A.map ψ)⁻¹ * (A.map ψ * (B.map ψ)⁻¹)
  rw [mul_assoc, inv_mul_cancel_left hA']

theorem val_map_hom {X Y : Var F} {ψ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : (ratOf X).IsHom (ratOf Y) ψ f)
    {K : Type} [Field K] (p : Sp K ⟶ Y.X) {k : ι → ℕ} {D : Mat m X.Fn}
    (hD : Par k ((ratOf X).O (f (p (IsLocalRing.closedPoint K)))).toSubring D) :
    (D.map ψ).map ((ratOf Y).val p) = D.map ((ratOf X).val (p ≫ f)) := by
  funext τ
  ext i j
  exact (hf.val_comp p (IsLocalRing.closedPoint K) ((hD τ).1 i j)).symm

theorem par_map_hom {X Y : Var F} {ψ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : (ratOf X).IsHom (ratOf Y) ψ f)
    {z : Y.X} {k : ι → ℕ} {D : Mat m X.Fn} (hD : Par k ((ratOf X).O (f z)).toSubring D) :
    Par k ((ratOf Y).O z).toSubring (D.map ψ) :=
  hD.map ψ.toRingHom fun _ hx => hf.map_mem_O hx

end GlobalTheory.FlagBundle.Transfer

namespace GlobalTheory.FlagBundle

open Transfer

theorem Bears.transfer : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F)
    (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ →
    ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ →
    ∀ A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ B ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)),
    ∀ h h' : Mat m K, Bears S₁ φ₁ A h p → Bears S₁ φ₁ B h' p → Bears S₂ φ₂ B h' q → Bears S₂ φ₂ A h q := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ R₁ R₂ K _ p q hpq A hA B hB h h' b1 b2 b3
  obtain ⟨A₁, hA₁, G1⟩ := b1
  obtain ⟨A₁', hA₁', G2⟩ := b2
  obtain ⟨A₂, hA₂, G3⟩ := b3
  refine ⟨A₂, hA₂, ?_⟩
  have hx1 : f₁ (p (IsLocalRing.closedPoint K)) = (p ≫ f₁) (IsLocalRing.closedPoint K) := rfl
  have hx2 : f₂ (q (IsLocalRing.closedPoint K)) = (p ≫ f₁) (IsLocalRing.closedPoint K) := by rw [hpq]; rfl
  have hD : Par 0 ((ratOf X).O ((p ≫ f₁) (IsLocalRing.closedPoint K))).toSubring (A * B⁻¹) := (Fr.mem_iff hB).1 hA
  have hD1 : Par 0 ((ratOf X).O (f₁ (p (IsLocalRing.closedPoint K)))).toSubring (A * B⁻¹) := hx1 ▸ hD
  have hD2 : Par 0 ((ratOf X).O (f₂ (q (IsLocalRing.closedPoint K)))).toSubring (A * B⁻¹) := hx2 ▸ hD
  have C1 := R₁.2.1 _ A₁ hA₁ A (hx1 ▸ hA)
  have C1B := R₁.2.1 _ A₁ hA₁ B (hx1 ▸ hB)
  have C2 := R₂.2.1 _ A₂ hA₂ A (hx2 ▸ hA)
  have L1 := (Fr.mem_iff hA₁).1 hA₁'
  have e1 : A₁' * (B.map φ₁)⁻¹ = (A₁' * A₁⁻¹) * (A₁ * (B.map φ₁)⁻¹) := by
    rw [mul_assoc, inv_mul_cancel_left (Fr.det_ne hA₁)]
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  rw [e1, val_map_mul p L1 C1B, frame_change φ₁ A B hAd, val_map_mul p C1 (par_map_hom R₁.1 hD1),
    val_map_hom R₁.1 p hD1] at G2
  rw [frame_change φ₂ A B hAd, val_map_mul q C2 (par_map_hom R₂.1 hD2), val_map_hom R₂.1 q hD2] at G3
  have ev : (A * B⁻¹).map ((ratOf X).val (q ≫ f₂)) = (A * B⁻¹).map ((ratOf X).val (p ≫ f₁)) :=
    congrArg (fun y => (A * B⁻¹).map ((ratOf X).val y)) hpq.symm
  rw [ev] at G3
  have hE : Par 0 ⊤ ((A * B⁻¹).map ((ratOf X).val (p ≫ f₁))) := by
    rw [← val_map_hom R₁.1 p hD1]; exact val_map_par p (par_map_hom R₁.1 hD1)
  exact par_of_three (val_map_par p C1).det_ne (val_map_par q C2).det_ne hE.det_ne (val_map_par p L1) G1 G2 G3

end GlobalTheory.FlagBundle
end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory

theorem FlagBundle.bears_self : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y : Var F) (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Reps Eb S φ f → ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ∃ A ∈ Eb.S ((w ≫ f) (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S φ A h w := by
  intro F _ ι _ m X Y Eb S φ f hR K _ w
  obtain ⟨A, hA⟩ := Eb.nonempty ((w ≫ f) (IsLocalRing.closedPoint K))
  obtain ⟨A', hA'⟩ := S.nonempty (w (IsLocalRing.closedPoint K))
  have hA₁ : A ∈ Eb.S (f (w (IsLocalRing.closedPoint K))) := (Scheme.Hom.comp_apply w f (IsLocalRing.closedPoint K)) ▸ hA
  have hN := hR.2.1 _ A' hA' A hA₁
  have hh : Par 0 ⊤ ((A' * (A.map φ)⁻¹).map ((ratOf Y).val w)) := by
    have hz := RatModel.range_eq_singleton (M := ratOf Y) w (IsLocalRing.closedPoint K)
    exact hN.map_of ((ratOf Y).val w) (RatModel.valHom (M := ratOf Y) w _ hz)
      (fun x => (RatModel.valHom_apply (M := ratOf Y) w _ hz x).symm)
  refine ⟨A, hA, _, hh, A', hA', ?_⟩
  rw [Mat.mul_inv hh.det_ne]
  exact Par.one
end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gardingVector_derivative_eq_gardingVector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ φ, IsTest φ → ∃ ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ → ℝ), ∀ X, IsTest (ψ X) ∧ (X ∈ lieG G → ∀ w, dRep (trRep σ P) X (gard ε σ φ w) = gard ε σ (ψ X) w) := by
  first | exact @GlobalTheory.SmVec.dRep_gard | exact GlobalTheory.SmVec.dRep_gard | (intros; apply GlobalTheory.SmVec.dRep_gard <;> assumption)
end
