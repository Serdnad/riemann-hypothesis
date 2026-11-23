module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
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
public import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open Filter
open scoped SchwartzMap Topology Uniformity

namespace GlobalTheory
namespace SchwartzComplete

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem iteratedFDeriv_sub' (f g : 𝓢(V, ℂ)) (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (⇑(f - g)) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
  have hf : ContDiff ℝ n f := f.smooth n
  have hg : ContDiff ℝ n g := g.smooth n
  rw [show (⇑(f - g) : V → ℂ) = ⇑f - ⇑g from rfl]
  exact iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt

theorem cauchy_seminorm {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ a ≥ N, ∀ b ≥ N, SchwartzMap.seminorm ℝ k n (u a - u b) < ε := by
  rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
  have h := ((schwartz_withSeminorms ℝ V ℂ).tendsto_nhds _ 0).1 hu (k, n) ε hε
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
  refine ⟨max N₁ N₂, fun a ha b hb => ?_⟩
  have := hN (b, a) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hb, le_of_max_le_right ha⟩)
  simpa [schwartzSeminormFamily] using this

noncomputable def limD (u : ℕ → 𝓢(V, ℂ)) (n : ℕ) (x : V) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ :=
  limUnder atTop fun j => iteratedFDeriv ℝ n (u j) x

theorem tendsto_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) (x : V) :
    Tendsto (fun j => iteratedFDeriv ℝ n (u j) x) atTop (𝓝 (limD u n x)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cauchy_seminorm hu 0 n hε
  refine ⟨N, fun a ha b hb => ?_⟩
  rw [dist_eq_norm, ← iteratedFDeriv_sub']
  have := SchwartzMap.le_seminorm ℝ 0 n (u a - u b) x
  simp only [pow_zero, one_mul] at this
  exact this.trans_lt (hN a ha b hb)

theorem key {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ j ≥ N, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖ ≤ ε := by
  obtain ⟨N, hN⟩ := cauchy_seminorm hu k n hε
  refine ⟨N, fun j hj x => ?_⟩
  have ht : Tendsto (fun b => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - iteratedFDeriv ℝ n (u b) x‖)
      atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖)) :=
    ((tendsto_const_nhds.sub (tendsto_limD hu n x)).norm).const_mul _
  refine le_of_tendsto ht (eventually_atTop.2 ⟨N, fun b hb => ?_⟩)
  rw [← iteratedFDeriv_sub']
  exact (SchwartzMap.le_seminorm ℝ k n (u j - u b) x).trans (hN j hj b hb).le

theorem tendstoUniformly_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) :
    TendstoUniformly (fun j => iteratedFDeriv ℝ n (u j)) (limD u n) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := key hu 0 n (half_pos hε)
  refine eventually_atTop.2 ⟨N, fun j hj x => ?_⟩
  have := hN j hj x
  rw [pow_zero, one_mul] at this
  rw [dist_eq_norm, norm_sub_rev]
  linarith

theorem continuous_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) :
    Continuous (limD u n) :=
  (tendstoUniformly_limD hu n).continuous (Eventually.of_forall (f := atTop) fun j =>
    ((u j).smooth ⊤).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).frequently

theorem hasFDerivAt_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (m : ℕ) (x : V) :
    HasFDerivAt (limD u m) ((limD u (m + 1) x).curryLeft) x := by
  refine hasFDerivAt_of_tendstoUniformly (f := fun j => iteratedFDeriv ℝ m (u j))
    (f' := fun j y => fderiv ℝ (iteratedFDeriv ℝ m (u j)) y)
    (g' := fun y => (limD u (m + 1) y).curryLeft) ?_ ?_ (fun y => tendsto_limD hu m y) x
  · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).isometry.uniformContinuous.comp_tendstoUniformly
      (tendstoUniformly_limD hu (m + 1))
  · intro j y
    exact ((((u j).smooth ⊤).differentiable_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_lt_top (m : ℕ))) y).hasFDerivAt

theorem hasFTaylorSeries {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) :
    HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (limD u 0 x).curry0)
      (fun x => (fun m => limD u m x : FormalMultilinearSeries ℝ V ℂ)) :=
  ⟨fun _ => rfl, fun m _ x => hasFDerivAt_limD hu m x, fun m _ => continuous_limD hu m⟩

noncomputable def limMap (u : ℕ → 𝓢(V, ℂ)) (hu : CauchySeq u) : 𝓢(V, ℂ) where
  toFun x := (limD u 0 x).curry0
  smooth' := (hasFTaylorSeries hu).contDiff
  decay' k n := by
    obtain ⟨N, hN⟩ := key hu k n one_pos
    refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x => ?_⟩
    rw [← (hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k n (u N) x
    have h3 : ‖limD u n x‖ ≤ ‖iteratedFDeriv ℝ n (u N) x‖ + ‖iteratedFDeriv ℝ n (u N) x - limD u n x‖ := by
      have := norm_sub_le (iteratedFDeriv ℝ n (u N) x) (iteratedFDeriv ℝ n (u N) x - limD u n x)
      simpa using this
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
    change ‖x‖ ^ k * ‖limD u n x‖ ≤ _
    rw [mul_add] at h4
    linarith

theorem iteratedFDeriv_limMap {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (limMap u hu) x = limD u n x :=
  ((hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x).symm

theorem tendsto_limMap {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) :
    Tendsto u atTop (𝓝 (limMap u hu)) := by
  rw [(schwartz_withSeminorms ℝ V ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨N, hN⟩ := key hu k n (half_pos hε)
  refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le fun x => ?_
  rw [iteratedFDeriv_sub', iteratedFDeriv_limMap]
  exact hN j hj x

instance completeSpace : CompleteSpace 𝓢(V, ℂ) := by
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ⟨limMap u hu, tendsto_limMap hu⟩

end SchwartzComplete

theorem schwartzMap_barrelledSpace : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V], BarrelledSpace ℂ (SchwartzMap V ℂ) := by
  intro V _ _ _
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.ThK.SqIntMaxCpt

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped Matrix TensorProduct

theorem exists_congr_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) : ∃ Q : GL (Fin n) ℂ, Q.1ᴴ * P * Q.1 = 1 := by
  have hd : P.det ≠ 0 := fun h => by
    obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [e] using hpos x hx
  obtain ⟨ε, Q, hQ⟩ := Frames.exists_congr_diagonal_sign hP hd
  refine ⟨Q, hQ.trans ?_⟩
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  have hx : Q.1 *ᵥ (Pi.single i 1 : Fin n → ℂ) ≠ 0 := fun h => by
    have := congrArg ((Q⁻¹).1 *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    simpa using congrFun this i
  have := hpos _ hx
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ] at this
  cases h : ε i
  · simp [h, Matrix.mulVec_single_one, dotProduct, Pi.single_apply, Matrix.diagonal_apply] at this
    linarith
  · simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.ThK.SqIntMaxCpt
end
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.SpGen
open Matrix

theorem upper_unipotent_eq {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) :
    (fromBlocks 1 s 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 0 1 (-1) 0 * fromBlocks 1 0 (-s) 1 * fromBlocks 0 1 (-1) 0 *
        fromBlocks (-1) 0 0 (-1) := by
  simp [fromBlocks_multiply]

theorem symplectic_generated_levi_lower_weyl :
    ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  intro K _ κ _ _ P hmul hlevi hlow hJ a ha
  have hup : ∀ s : Matrix κ κ K, sᵀ = s → P (fromBlocks 1 s 0 1) := by
    intro s hs
    rw [upper_unipotent_eq]
    exact hmul _ _ (hmul _ _ (hmul _ _ hJ (hlow _ (by simp [hs]))) hJ) (hlevi _ _ (by simp))
  have hJ0 : (fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) = -J κ K := by
    simp [J, fromBlocks_neg]
  have hsp : a ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.mem_iff']
    rw [hJ0] at ha
    simpa [Matrix.mul_neg, Matrix.neg_mul] using ha
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, a = fromBlocks A B C D :=
    ⟨_, _, _, _, a.fromBlocks_toBlocks.symm⟩
  have hExists : ∃ X : Matrix κ κ K, X.IsSymm ∧ IsUnit (A + X * C).det := by
    -- Use the field case of Mathlib's construction in LinearAlgebra/SymplecticGroup.
    have hker (x : κ → K) (hAx : A • x = 0) (hCx : C • x = 0) : x = 0 := by
      rw [smul_eq_mulVec] at hAx hCx
      have hunit := (fromBlocks A B C D).isUnit_iff_isUnit_det.2
        (SymplecticGroup.symplectic_det hsp)
      have hzero : fromBlocks A B C D *ᵥ Sum.elim x 0 =
          fromBlocks A B C D *ᵥ Sum.elim 0 0 := by
        simp [fromBlocks_mulVec, hAx, hCx]
      exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hunit hzero)).1
    have hsymm := (SymplecticGroup.fromBlocks_mem_iff.1 hsp).1
    obtain ⟨V, U, e, hV, hU, heq⟩ := exists_rank_normal_form C
    set R := V * C * U with hR
    set S := Vᵀ⁻¹ * A * U with hS
    let f := fun M : Matrix κ κ K ↦ M.submatrix e.symm e.symm
    have hf (M : Matrix κ κ K) : f M = M.submatrix e.symm e.symm := rfl
    have f_unit {M} : IsUnit M → IsUnit (f M) := (isUnit_submatrix_equiv ..).2
    have f_mul (M N) : f (M * N) = f M * f N := submatrix_mul _ _ _ _ _ e.symm.bijective
    let _ : Invertible V := hV.invertible
    let _ : Invertible U := hU.invertible
    let _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
    have hker' (x : Fin C.rank ⊕ Fin (Fintype.card κ - C.rank) → K)
        (hxS : f S • x = 0) (hxR : f R • x = 0) : x = 0 := by
      refine (f_unit hU).smul_left_cancel.1 ?_
      rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
        smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at hxS hxR
      · rw [Equiv.comp_symm_eq, Pi.zero_comp] at hxS hxR
        exact e.surjective.injective_comp_right <| by simpa using hker _ hxS hxR
      · exact f_unit hV
      · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
    have hSR : Sᵀ * R = Rᵀ * S := by
      simp only [hR, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, hS,
        inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
      rw [← mul_assoc Aᵀ, hsymm, mul_assoc]
    have hblocks : (f S).toBlocks₁₁ᵀ = (f S).toBlocks₁₁ ∧ (f S).toBlocks₁₂ = 0 := by
      apply_fun reindex e e at hSR
      rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Rᵀ, heq, hf,
        ← transpose_submatrix, ← hf S, ← (f S).fromBlocks_toBlocks, hf (_)ᵀ, hf
        ((fromBlocks 1 0 0 0).submatrix _ _)] at hSR
      simp [fromBlocks_transpose, fromBlocks_multiply] at hSR
      tauto
    have h₂₂ : IsUnit (f S).toBlocks₂₂ := by
      refine mulVec_injective_iff_isUnit.1 ?_
      rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
      refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
        (hker' _ ?_ ?_).trans Sum.elim_zero_zero.symm
      · rw [← (f S).fromBlocks_toBlocks]
        simp [hx, hblocks.2, fromBlocks_mulVec]
      · simp [hf, heq, fromBlocks_mulVec]
    set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card κ - C.rank))
      (Fin C.rank ⊕ Fin (Fintype.card κ - C.rank)) K :=
      fromBlocks (1 - (f S).toBlocks₁₁) 0 0 0 with hY
    have hYsymm : Y.IsSymm := by
      rw [hY, isSymm_fromBlocks_iff]
      exact ⟨IsSymm.sub isSymm_one hblocks.1, by simp⟩
    set X := f Vᵀ * Y * f V with hX
    refine ⟨X.submatrix e e, IsSymm.submatrix ?_ e, (isUnit_iff_isUnit_det _).1
      ((isUnit_submatrix_equiv e.symm e.symm).1 ?_)⟩
    · simp_rw [hX, Matrix.IsSymm, transpose_mul, hYsymm.eq, hf, transpose_submatrix,
        transpose_transpose, mul_assoc]
    · have hsum : f (A + X.submatrix e e * C) = f Vᵀ * (f S + Y * f R) * f U⁻¹ := by
        simp_rw [hf, submatrix_add, Pi.add_apply, hS, hR, ← hf, f_mul, hf, mul_add, ← mul_assoc,
          ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
        simp [hX]
        rfl
      rw [← hf, hsum, IsUnit.mul_iff, IsUnit.mul_iff]
      refine ⟨⟨isUnit_of_invertible _, ?_⟩, f_unit (isUnit_nonsing_inv_iff.2 hU)⟩
      nth_rw 1 [hY, heq, ← (f S).fromBlocks_toBlocks, hblocks.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add] using h₂₂
  obtain ⟨X, hX, hu⟩ := hExists
  have hUX : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
  have hprod : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks A B C D =
      fromBlocks (A + X * C) (B + X * D) C D := by
    simp [fromBlocks_multiply]
  generalize hc : A + X * C = c at hu hprod
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hLev : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp, ?_⟩
    rw [transpose_nonsing_inv]
    simp [nonsing_inv_mul _ hcT]
  have hnsp := mul_mem (mul_mem hLev hUX) hsp
  have hn : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 *
      fromBlocks A B C D = fromBlocks 1 (c⁻¹ * (B + X * D)) (cᵀ * C) (cᵀ * D) := by
    rw [Matrix.mul_assoc, hprod, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hu]
  rw [hn] at hnsp
  generalize c⁻¹ * (B + X * D) = Z at hn hnsp
  generalize cᵀ * C = Wm at hn hnsp
  generalize cᵀ * D = V at hn hnsp
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hnsp
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at h1 h3
  have hW : Wmᵀ = Wm := h1.symm
  rw [hW] at h3
  have hV : V = Wm * Z + 1 := by rw [← h3]; abel
  have hZ : Zᵀ = Z := by
    rw [hV, transpose_add, transpose_mul, hW, transpose_one, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc] at h2
    simpa using h2
  have hfac : (fromBlocks 1 Z Wm V : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 1 0 Wm 1 * fromBlocks 1 Z 0 1 := by
    rw [fromBlocks_multiply, hV]; simp
  have e2 : (fromBlocks c 0 0 cᵀ⁻¹ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks c⁻¹ 0 0 cᵀ = 1 := by
    rw [fromBlocks_multiply]
    simp [mul_nonsing_inv _ hu, nonsing_inv_mul _ hcT]
  have e3 : (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 = 1 := by
    simp [fromBlocks_multiply]
  have hdec : fromBlocks A B C D = (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) *
      fromBlocks c 0 0 cᵀ⁻¹ * (fromBlocks c⁻¹ 0 0 cᵀ * fromBlocks 1 X 0 1 * fromBlocks A B C D) := by
    rw [Matrix.mul_assoc (fromBlocks 1 (-X) 0 1), ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹),
      ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹), e2, Matrix.one_mul, ← Matrix.mul_assoc, e3,
      Matrix.one_mul]
  rw [hdec, hn, hfac]
  refine hmul _ _ (hmul _ _ (hup _ (by simp [hX.eq])) (hlevi _ _ ?_)) (hmul _ _ (hlow _ hW) (hup _ hZ))
  exact mul_nonsing_inv _ hcT

end GlobalTheory.SpGen
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RouteCoordsW

open GlobalTheory.RouteCoords GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation

theorem trace_second_pos {A : Type} [CommRing A] (c : A →+* A) {n b : ℕ} (hc : ∀ z, c (c z) = z) (ξ : A) (hξ : c ξ = -ξ)
    (g : Matrix (Fin n) (Fin n) A) (p pi : Matrix (Fin b) (Fin b) A) (hg : (g.map c)ᵀ = g) (hp : (p.map c)ᵀ = p)
    (hpi : pi * p = 1) (Z Z' : Matrix (Fin n) (Fin b) A) :
    c (ξ * (pi * ((-(Z'.map c * p)).map c)ᵀ * g * (-(Z.map c * p))).trace) =
      -(ξ * (Z * pᵀ * (Z'.map c)ᵀ * gᵀ).trace) := by
  rw [← trace_second c hc ξ hξ g p pi hg hp hpi Z Z', ← map_neg, ← mul_neg, ← trace_neg]
  congr 3
  simp only [Matrix.neg_mul, neg_neg]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RouteCoordsW
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem GlobalTheory.FlagCell2.univ_eq_of_local_preimage_eq : ∀ (M N : Type) [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] (π : N → M), Measurable π → ∀ (μ : Measure N) (ν : Measure M), (∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ T, MeasurableSet T → T ⊆ U → μ (π ⁻¹' T) = ν T) → μ Set.univ = ν Set.univ := by
  intro M N _ _ _ _ _ π hπ μ ν h
  choose U hUo hxU hU using h
  obtain ⟨S, hSc, hS⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  haveI : Countable S := hSc.to_subtype
  have hcov : ⋃ i : S, U i = Set.univ := by
    rw [← Set.biUnion_eq_iUnion S (fun i _ => U i), hS]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hxU x⟩
  have hmap : μ.map π = ν := by
    refine (Measure.ext_iff_of_iUnion_eq_univ hcov).2 fun i => ?_
    ext T hT
    have hm : MeasurableSet (T ∩ U i) := hT.inter (hUo i).measurableSet
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT, Measure.map_apply hπ hm]
    exact hU i _ hm Set.inter_subset_right
  have : μ Set.univ = μ.map π Set.univ := by
    rw [Measure.map_apply hπ MeasurableSet.univ, Set.preimage_univ]
  rw [this, hmap]
end
