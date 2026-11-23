module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle008
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SqIntA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero

@[expose] public section

section

noncomputable section

open Finset MeasureTheory
open Formalism.MainNotions.S (umat)

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

private theorem memLp_of_weighted_diagonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (y : H)
    (hW : MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε)) :
    MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) 2 (Formalism.REAL.muG ε) := by
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => inner ℂ y (σ (umat g) y)) :=
    continuous_const.inner ((hσ.2.2 y).comp_continuous Formalism.MainNotions.BridgeCSchur.continuous_umat
      (fun g => umat_mem_UJset ε g))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : Subsingleton (Formalism.REAL.UJ ε) :=
      ⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 (Fin.cast hn i)))⟩
    have : CompactSpace (Formalism.REAL.UJ ε) := Finite.compactSpace
    refine MemLp.of_bound hcont.aestronglyMeasurable (‖y‖ * ‖y‖)
      (Filter.Eventually.of_forall fun g => ?_)
    calc ‖inner ℂ y (σ (umat g) y)‖ ≤ ‖y‖ * ‖σ (umat g) y‖ := norm_inner_le_norm _ _
      _ = _ := by rw [hσ.2.1 _ (umat_mem_UJset ε g)]
  · refine hW.of_le hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    have hs : 1 ≤ Real.sqrt (S7.hs (umat g)) :=
      Real.one_le_sqrt.mpr (sigZeroDecay_one_le_hs (umat_mem_UJset ε g) ⟨0, hn⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact le_mul_of_one_le_left (norm_nonneg _) hs

private theorem memLp_coefficients {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : G → (H →L[ℂ] H)} (hR : ∀ h : G, MeasurePreserving (fun g => g * h) μ μ)
    (hInv : MeasurePreserving (Inv.inv : G → G) μ μ)
    (hone : ρ 1 = 1) (hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (y : H) (hy : y ≠ 0) (h0 : MemLp (fun g => inner ℂ y (ρ g y)) 2 μ) (v w : H) :
    MemLp (fun g => inner ℂ w (ρ g v)) 2 μ := by
  have hall (x : H) : MemLp (fun g => inner ℂ y (ρ g x)) 2 μ :=
    GraphTrick.memLp_of_ne hR hone hmul hiso hirr y y hy h0 x
  have hinv := ((hall w).comp_measurePreserving hInv).star
  have e : star ((fun g => inner ℂ y (ρ g w)) ∘ Inv.inv) = fun g => inner ℂ w (ρ g y) := by
    funext g
    have hs := GraphTrick.star_eq (ρ := ρ) hone hmul hiso g⁻¹
    simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, inner_conj_symm]
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hs, inv_inv]
  rw [e] at hinv
  exact GraphTrick.memLp_of_ne hR hone hmul hiso hirr w y hy hinv v

theorem tf_sqInt_of_hW {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      (Real.sqrt (S7.hs (umat g)) : ℂ) * inner ℂ (w : H) (σ (umat g) (v : H)))
      2 (Formalism.REAL.muG ε)) :
    Formalism.MainNotions.S.IsSqIntOn ε (tfClRep σ (closGen E V)) := by
  have hU := tfClRep_isURepOn hgap hσ hD hV hc hVK
  have hst := closGen_stable hgap hσ hD hV hc hVK
  let ρ : Formalism.REAL.UJ ε → (closGen E V →L[ℂ] closGen E V) :=
    fun g => tfClRep σ (closGen E V) (umat g)
  have hone : ρ 1 = 1 := by
    change tfClRep σ (closGen E V) 1 = 1
    exact hU.1.1
  have hmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := by
    intro a b
    exact hU.1.2 (umat a) (umat_mem_UJset ε a) (umat b) (umat_mem_UJset ε b)
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hU.2.1 (umat g) (umat_mem_UJset ε g) v
  have hirr := Formalism.MainNotions.BridgeCSchur.irr_of (tfClRep_irred hgap hσ hD hV hc hVK)
  obtain ⟨y, hyV, hy, -⟩ := hV.2.2.2
  have hyG : y ∈ genSub E V := rorth_le_genSub hyV
  let y0 : closGen E V := ⟨((y : D) : H), Submodule.le_topologicalClosure _ ⟨y, hyG, rfl⟩⟩
  have hy0 : y0 ≠ 0 := by
    intro h
    apply hy
    have h2 : ((y : D) : H) = 0 := congrArg Subtype.val h
    exact Subtype.ext h2
  have hcoe : (fun g => inner ℂ y0 (ρ g y0)) = fun g => inner ℂ (y : H) (σ (umat g) (y : H)) := by
    funext g
    change inner ℂ (y : H) (↑(tfClRep σ (closGen E V) (umat g) y0) : H) = _
    rw [tfClRep_coe σ _ (hst (umat g) (umat_mem_UJset ε g))]
  have h0 : MemLp (fun g => inner ℂ y0 (ρ g y0)) 2 (Formalism.REAL.muG ε) := by
    rw [hcoe]
    exact memLp_of_weighted_diagonal hσ (y : H) (hW y hyG y hyG)
  have : (Formalism.REAL.muG ε).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  exact memLp_coefficients (ρ := ρ) (MeasureTheory.measurePreserving_mul_right (Formalism.REAL.muG ε))
    (Measure.measurePreserving_inv (Formalism.REAL.muG ε)) hone hmul hiso hirr y0 hy0 h0

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

theorem tf_schur_transfer {n : ℕ} {ε : Fin n → Bool} {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
    (S₁ : Submodule ℂ H₁) [S₁.HasOrthogonalProjection] (S₂ : Submodule ℂ H₂) (U : S₁ ≃ₗᵢ[ℂ] S₂)
    (hU : ∀ g ∈ UJset ε, ∀ x y : S₁, (x : H₁) = σ₁ g (y : H₁) → ((U x : S₂) : H₂) = σ₂ g ((U y : S₂) : H₂))
    (hS₁ : ∀ g ∈ UJset ε, ∀ x ∈ S₁, σ₁ g x ∈ S₁) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ₁ S₁) d) :
    ∀ x ∈ S₂, ∀ v ∈ S₂, ∫ g : Formalism.REAL.UJ ε, ‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 ∂(Formalism.REAL.muG ε) =
      ‖x‖ ^ 2 * ‖v‖ ^ 2 / d := by
  intro x hx v hv
  set x1 : S₁ := U.symm ⟨x, hx⟩ with hx1
  set v1 : S₁ := U.symm ⟨v, hv⟩ with hv1
  have ex : ((U x1 : S₂) : H₂) = x := by rw [hx1, LinearIsometryEquiv.apply_symm_apply]
  have ev : ((U v1 : S₂) : H₂) = v := by rw [hv1, LinearIsometryEquiv.apply_symm_apply]
  have hcoef : ∀ g : Formalism.REAL.UJ ε, inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g := by
    intro g
    have hg := umat_mem_UJset ε g
    set y : S₁ := ⟨σ₁ (Formalism.MainNotions.S.umat g) (v1 : H₁), hS₁ _ hg _ v1.2⟩ with hy
    have h1 := hU _ hg y v1 rfl
    rw [← ex, ← ev, ← h1, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    show inner ℂ x1 y = inner ℂ x1 (tfClRep σ₁ S₁ (Formalism.MainNotions.S.umat g) v1)
    congr 1
    exact Subtype.ext (tfClRep_coe σ₁ S₁ (hS₁ _ hg) v1).symm
  obtain ⟨-, hint, hval⟩ := hd.1, (hd.2 v1 x1 v1 x1).1, (hd.2 v1 x1 v1 x1).2
  have hnx : ‖x‖ = ‖x1‖ := by rw [← ex]; exact U.norm_map x1
  have hnv : ‖v‖ = ‖v1‖ := by rw [← ev]; exact U.norm_map v1
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have e : ∀ g : Formalism.REAL.UJ ε, ((‖inner ℂ x (σ₂ (Formalism.MainNotions.S.umat g) v)‖ ^ 2 : ℝ) : ℂ) =
      Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g * star (Formalism.MainNotions.S.coefOn (tfClRep σ₁ S₁) v1 x1 g) := by
    intro g
    rw [hcoef, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e]
  have h1 : inner ℂ v1 v1 = ((‖v1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h2 : inner ℂ x1 x1 = ((‖x1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hval, h1, h2, hnx, hnv]
  push_cast
  ring

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
