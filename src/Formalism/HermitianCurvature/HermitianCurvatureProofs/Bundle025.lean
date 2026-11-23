module

public import Formalism.HermitianCurvature.StatementB
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Formalism.HermitianCurvature.StatementFr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommuteLevelZeroElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbedLoweringConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2OfFourEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2RmatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussFormMinusLetter
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle015
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusLetterFrameOfData
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PlusLetterFrameOfData
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle019
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries
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
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem isClosed_GVt (k r : ℕ) : IsClosed {x : Mt k r | Matrix.of x ∈ B.GV k r} := by
  have h0 : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have hc : Continuous (fun x : Mt k r => (Matrix.of x)ᴴ * Hpk k r * Matrix.of x) :=
    ((h0.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul h0
  exact isClosed_eq hc continuous_const

theorem exists_smoothExt {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : B.Mat k r → E) (hF : B.CkOn (⊤ : ℕ∞) (B.GV k r) F) :
    ∃ Ft : Mt k r → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ft ∧
      ∀ x : Mt k r, Matrix.of x ∈ B.GV k r → Ft x = F (Matrix.of x) := by
  set s : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ B.GV k r} with hs
  have hloc : ∀ i : s, ∃ (U : Set (Mt k r)) (f' : Mt k r → E), IsOpen U ∧ (i : Mt k r) ∈ U ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' U ∧ ∀ x ∈ U, Matrix.of x ∈ B.GV k r → F (Matrix.of x) = f' x := by
    intro i
    obtain ⟨U, f', hU, hiU, hf', hfe⟩ := hF (Matrix.of (i : Mt k r)) i.2
    exact ⟨U, f', hU, hiU, hf', fun x hx hxG => hfe (Matrix.of x) hx hxG⟩
  choose U f' hU hiU hf' hfe using hloc
  have hcov : s ⊆ ⋃ i : s, U i := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hiU ⟨x, hx⟩⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Mt k r) (isClosed_GVt k r) U hU hcov
  refine ⟨fun x => ∑ᶠ i, ρ i x • f' i x, ?_, ?_⟩
  · have h := ρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (g := f') fun i x hx => by
      have hxU : x ∈ U i := hρ i hx
      exact ((hf' i).contDiffAt ((hU i).mem_nhds hxU)).contMDiffAt
    exact contMDiff_iff_contDiff.1 h
  · intro x hx
    have hsum : ∑ᶠ i, ρ i x = 1 := ρ.sum_eq_one hx
    have heq : ∀ i, ρ i x • f' i x = ρ i x • F (Matrix.of x) := by
      intro i
      by_cases h0 : ρ i x = 0
      · simp [h0]
      · have hxU : x ∈ U i := hρ i (subset_tsupport _ h0)
        rw [hfe i x hxU hx]
    simp only [heq]
    rw [← finsum_smul, hsum, one_smul]

end Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
end
end

section

open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsInv (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : Wq →L[ℂ] Wp :=
  LinearMap.toContinuousLinearMap ((stdOrthonormalBasis ℂ Wq).toBasis.constr ℂ (fun i => v i))

lemma hsInv_basis (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) (i : Fin (Module.finrank ℂ Wq)) :
    hsInv v (stdOrthonormalBasis ℂ Wq i) = v i := by
  have := (stdOrthonormalBasis ℂ Wq).toBasis.constr_basis ℂ (fun i => v i) i
  simpa [hsInv] using this

lemma hsVec_apply' (A : Wq →L[ℂ] Wp) (i : Fin (Module.finrank ℂ Wq)) :
    hsVec A i = A (stdOrthonormalBasis ℂ Wq i) := rfl

lemma hsInv_hsVec (A : Wq →L[ℂ] Wp) : hsInv (hsVec A) = A := by
  apply ContinuousLinearMap.coe_injective
  apply (stdOrthonormalBasis ℂ Wq).toBasis.ext
  intro i
  simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis]
  rw [hsInv_basis, hsVec_apply']

lemma hsVec_hsInv (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : hsVec (hsInv v) = v := by
  ext i
  rw [hsVec_apply', hsInv_basis]

def hsE : (Wq →L[ℂ] Wp) ≃ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := hsVec
  map_add' A B := by ext i; simp [hsVec_apply']
  map_smul' c A := by ext i; simp [hsVec_apply']
  invFun := hsInv
  left_inv := hsInv_hsVec
  right_inv := hsVec_hsInv

def conjE (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  LinearMap.toContinuousLinearMap (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap)

def adjH (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  LinearMap.toContinuousLinearMap
    (hsE.symm.toLinearMap ∘ₗ (ContinuousLinearMap.adjoint (conjE T)).toLinearMap ∘ₗ hsE.toLinearMap)

lemma hsE_adjH (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (B : Wq →L[ℂ] Wp) :
    hsVec (adjH T B) = ContinuousLinearMap.adjoint (conjE T) (hsVec B) := by
  show hsE (hsE.symm _) = _
  rw [LinearEquiv.apply_symm_apply]; rfl

lemma conjE_hsVec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A : Wq →L[ℂ] Wp) :
    conjE T (hsVec A) = hsVec (T A) := by
  show hsE (T (hsE.symm (hsE A))) = _
  rw [LinearEquiv.symm_apply_apply]; rfl

theorem adjH_spec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A B : Wq →L[ℂ] Wp) :
    hsInner (T A) B = hsInner A (adjH T B) := by
  unfold hsInner
  rw [hsE_adjH, ContinuousLinearMap.adjoint_inner_left, conjE_hsVec]

lemma adjH_add (T S : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (T + S) = adjH T + adjH S := by
  ext B : 1
  apply hsE.injective
  simp only [ContinuousLinearMap.add_apply, map_add (f := _)]
  show hsVec (adjH (T + S) B) = hsVec (adjH T B) + hsVec (adjH S B)
  rw [hsE_adjH, hsE_adjH, hsE_adjH]
  have : conjE (T + S) = conjE T + conjE S := by
    ext v : 1; simp [conjE]
  rw [this, map_add (f := _), ContinuousLinearMap.add_apply]

lemma adjH_smulC (c : ℂ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (c • T) = (starRingEnd ℂ c) • adjH T := by
  ext B : 1
  apply hsE.injective
  show hsVec (adjH (c • T) B) = hsE (((starRingEnd ℂ c) • adjH T) B)
  rw [ContinuousLinearMap.smul_apply, map_smul]
  show _ = (starRingEnd ℂ c) • hsVec (adjH T B)
  rw [hsE_adjH, hsE_adjH]
  have : conjE (c • T) = c • conjE T := by
    ext v : 1; simp [conjE]
  rw [this, map_smulₛₗ, ContinuousLinearMap.smul_apply]

lemma adjH_smul (c : ℝ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjH (c • T) = c • adjH T := by
  rw [← Complex.coe_smul, adjH_smulC, Complex.conj_ofReal, Complex.coe_smul]

def adjR : ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
  LinearMap.toContinuousLinearMap
    { toFun := adjH
      map_add' := adjH_add
      map_smul' := adjH_smul }

end Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization
end
end

section

namespace Formalism.FourierDecayAlt.P

theorem plus_letter_maps_frames : Formalism.FourierDecayAlt.Fr.PlusStep :=
  plus_letter_frame_of_data position_insertion_mul_compat position_insertion_star_compat position_insertion_diagonal_compat position_insertion_free_compat letter_module_plus
    rtt_relation_entries plus_letter_form plus_letter_tau plus_letter_l

theorem minus_letter_maps_frames : Formalism.FourierDecayAlt.Fr.MinusStep :=
  minus_letter_frame_of_data position_insertion_mul_compat position_insertion_star_compat position_insertion_diagonal_compat position_insertion_free_compat letter_module_minus
    rtt_relation_entries minus_letter_form minus_letter_tau minus_letter_l

theorem frame_of_admissible_word : Formalism.FourierDecayAlt.Fr.FrameAll :=
  (frame_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position frame_module_of_word).1

theorem frame_eq_word_module : Formalism.FourierDecayAlt.Fr.FrameWord :=
  (frame_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position frame_module_of_word).2

theorem frame_of_recursive_word : Formalism.FourierDecayAlt.Fr.FrameAllRec :=
  frame_rec_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position

end Formalism.FourierDecayAlt.P
end
