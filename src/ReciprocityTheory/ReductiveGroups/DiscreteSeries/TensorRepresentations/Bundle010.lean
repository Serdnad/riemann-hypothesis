module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquivB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockE
public import Formalism.RealPlaceAnalysis.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB

@[expose] public section

section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem occD_genSub_K {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {x : D} (hx : x ∈ genSub E V) :
    ∃ y ∈ genSub E V, (y : H) = σ k (x : H) := by
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hD.glRep hVk hx
  have hf : FiniteDimensional ℂ (layer ε E V m) := finiteDimensional_layer hVf m
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hk
  have hs := KTypeIsomorphism.orbit_hasSum hσ hD hf (layer_kStable hD.glRep hVk m) hZ ⟨x, hm⟩
  let P : Submodule ℂ H := LinearMap.range (D.subtype ∘ₗ (layer ε E V m).subtype)
  have hmem : σ (NormedSpace.exp Z) (x : H) ∈ P :=
    P.closed_of_finiteDimensional.mem_of_tendsto hs (Filter.Eventually.of_forall fun t =>
      P.sum_mem fun j _ => P.smul_mem _ ⟨_, rfl⟩)
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, layer_le_genSub m w.2, hw⟩

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occD_eeF (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') (s : Fin n)
    (hlam' : lam' = shiftF dual lam s) {ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε))}
    (hι : IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
      (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι) :
    ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      eeF dual (smE ε (rreg ε)) (ι x) = poleF dual lam s • ι x := by
  intro x hx
  have hE := (isDerivedOn_smE (rreg_isURepOn ε)).glRep
  have h1 : casimir (tensF dual (smE ε (rreg ε))) (ι x) = ((casVal lam' : ℝ) : ℂ) • ι x := by
    rw [← map_smul, ← casimir_genSub hE (datumV_casimir hP' v₀') x hx]

    simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [hι.2.2.1 a b _ (tset_genSub_E _ _ b a hx), hι.2.2.1 b a x hx]
  have h2 : casimir (tensF dual (smE ε (rreg ε))) (ι x) = ((casVal lam : ℝ) : ℂ) • ι x + (n : ℂ) • ι x +
      (2 : ℂ) • eeF dual (smE ε (rreg ε)) (ι x) := by
    have h3 : diagOp (casimir (smE ε (rreg ε))) (ι x) = ((casVal lam : ℝ) : ℂ) • ι x := funext fun c => by
      rw [diagOp_coord, casimir_genSub hE (datumV_casimir hP v₀) _ (tset_mem.mp (hι.1 x hx) c)]; rfl
    rw [← h3]
    cases dual
    · exact LinearMap.congr_fun (casimir_tensV hE) _
    · exact LinearMap.congr_fun (casimir_tensVd hE) _
  rw [h1, hlam', ← casVal_shiftF] at h2
  refine smul_right_injective _ (two_ne_zero (α := ℂ)) ?_
  show (2 : ℂ) • _ = (2 : ℂ) • _
  rw [smul_smul, ← add_right_inj (((casVal lam : ℝ) : ℂ) • ι x + (n : ℂ) • ι x), ← h2, ← add_smul, ← add_smul]
  push_cast; rfl

end Psi

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem lowFock_exists (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E)
    {lam : Fin n → ℝ} (hlam : StrictAnti lam) {V : Submodule ℂ N} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    ∃ x ∈ tensFock (n := n) V, x ∈ physicalSubspace ε ∧ x ≠ 0 ∧
      IsKHWVec ε (diagE ε (eT E) cpT cmT) (lam - rhoC ε + rhoHol ε) x := by
  have hK : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  set S0 := lowerWedgeAlt ε
  have hw : ∀ a, (lfMat ε a a).mulVec (Pi.single S0 (1 : ℂ)) =
      (((rhoHol ε - rhoN ε) a : ℝ) : ℂ) • Pi.single S0 1 :=
    fun a => lfMat_mulVec_single ε a a S0 _ (lowerWedge_weight ε a)
  have hl : ∀ a b, b < a → ε a = ε b → (lfMat ε a b).mulVec (Pi.single S0 (1 : ℂ)) = 0 := by
    intro a b hba he
    have h0 : sgE ε cpFock cmFock a b (fockBasis n S0.1) = (0 : ℂ) • fockBasis n S0.1 := by
      rw [zero_smul]; exact lowerWedge_killed_by_lowering ε hba he
    simpa using lfMat_mulVec_single ε a b S0 0 h0
  have hne : (Pi.single S0 (1 : ℂ) : LfIdx ε → ℂ) ≠ 0 := by
    intro h
    have := congrFun h S0
    simp at this
  obtain ⟨x, hxV, hx0, hxw, hxh⟩ :=
    HW.parthasarathy_tensor_matrix ε hK hV (lfMat_kRel ε) (fun a b h => lfMat_conjTranspose ε h) hne hw hl
      (lf_dom hlam hK hV)
  have hwt : lowK ε lam + (rhoHol ε - rhoN ε) = lam - rhoC ε + rhoHol ε := by
    funext a
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  refine ⟨lfLift ε x, lfLift_mem_tensFock ε hxV, lfLift_mem_physSub ε x, lfLift_ne_zero ε hx0, ?_⟩
  rw [← hwt]
  exact lfLift_isKHWVec ε hxw hxh

end ReciprocityTheory.ChartRestriction.DS
end
end
