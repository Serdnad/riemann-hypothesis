module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Formalism.RealPlaceAnalysis.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.CompactRelationsApplyComm
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.ParthasarathyTensorMatrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM

@[expose] public section

section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

lemma uqU_Jm_allTrue (k : ℕ) : Jm (fun _ : Fin k => true) = 1 := by
  unfold Jm
  simp

lemma uqU_mem_Kset {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) :
    g ∈ Kset (fun _ : Fin k => true) := by
  have h : gᴴ * Jm (fun _ : Fin k => true) * g = Jm (fun _ : Fin k => true) := hg
  rw [uqU_Jm_allTrue, Matrix.mul_one] at h
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose]
    exact h
  · rw [uqU_Jm_allTrue, Matrix.mul_one, Matrix.one_mul]

theorem hcTypeU_unique {k : ℕ} {u : Fin k → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (π' : Matrix (Fin k) (Fin k) ℂ → (H' →L[ℂ] H'))
    (hπ : Formalism.MainNotions.S.IsHCTypeU k u π) (hπ' : Formalism.MainNotions.S.IsHCTypeU k u π') :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k), ∀ v : H, π' g (U v) = U (π g v) := by
  obtain ⟨T, U₁, h₁⟩ := kType_of_hcTypeU π hπ
  obtain ⟨T', U₂, h₂⟩ := kType_of_hcTypeU π' hπ'
  obtain ⟨φ, hφ, -, -⟩ := kType_unique T T'
  refine ⟨U₁.trans (φ.trans U₂.symm), ?_⟩
  intro g hg v
  have hK := uqU_mem_Kset hg
  have hU : g ∈ Matrix.unitaryGroup (Fin k) ℂ := hK.1
  have hUJ : inUJ (fun _ : Fin k => true) g := hg
  let k0 : KG (fun _ : Fin k => true) :=
    ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hU, Unitary.star_mul_self_of_mem hU⟩, hUJ⟩, hK⟩
  have hk0 : toMK k0 = g := rfl
  apply U₂.injective
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [← hk0, h₂, h₁, hφ, LinearIsometryEquiv.apply_symm_apply]

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem parthasarathy_tensor_matrix (ε : Fin n → Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F)
    {Λ : Fin n → ℝ} {V : Submodule ℂ M} (hV : IsKIrrHW ε F Λ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G)
    (hGu : ∀ a b, ε a = ε b → G b a = (G a b)ᴴ)
    {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0) (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f)
    (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0)
    (hdom : ∀ a b, a < b → ε a = ε b → (Λ + ν) b ≤ (Λ + ν) a) :
    ∃ x : ι → M, (∀ i, x i ∈ V) ∧ x ≠ 0 ∧
      (∀ a i, F a a (x i) + ∑ j, G a a i j • x j = (((Λ + ν) a : ℝ) : ℂ) • x i) ∧
      ∀ a b, a < b → ε a = ε b → ∀ i, F a b (x i) + ∑ j, G a b i j • x j = 0 :=
  parthasarathy_tensor_matrix_alt ε hF hV hG hGu hf0 hfw hfl hdom

theorem kIrrHW_int (ε : Fin n → Bool) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) {Λ : Fin n → ℝ} {V : Submodule ℂ M}
    (hV : IsKIrrHW ε F Λ V) : ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, Λ a - Λ b = m :=
  kIrrHW_int' ε hF hV

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
