module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle011
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem JacobianRankOffHypersurface.eval_pderiv_sum_mul {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (c g : ι → MvPolynomial σ ℂ) (hg : ∀ k, eval w (g k) = 0) (x : σ) :
    eval w (pderiv x (∑ k, c k * g k)) = ∑ k, eval w (c k) * eval w (pderiv x (g k)) := by

  simp [map_sum, Derivation.leibniz, smul_eq_mul, hg]

theorem JacobianRankOffHypersurface.grad_mem_span {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (a p : MvPolynomial σ ℂ) (c g : ι → MvPolynomial σ ℂ) (hsum : ∑ k, c k * g k = a * p)
    (hg : ∀ k, eval w (g k) = 0) (hp : eval w p = 0) (ha : eval w a ≠ 0) :
    (fun x ↦ eval w (pderiv x p)) ∈
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (g k))) := by
  have key : (fun x ↦ eval w (pderiv x p)) =
      (eval w a)⁻¹ • ∑ k, eval w (c k) • (fun x ↦ eval w (pderiv x (g k))) := by
    funext x
    have h1 := congrArg (fun f ↦ eval w (pderiv x f)) hsum
    simp only [JacobianRankOffHypersurface.eval_pderiv_sum_mul w c g hg x, Derivation.leibniz, smul_eq_mul,
      map_add, map_mul, hp, zero_mul, add_zero] at h1
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1]
    rw [inv_mul_cancel_left₀ ha]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem JacobianRankOffHypersurface.finrank_of_generators {σ ι : Type*} [Fintype σ] [Fintype ι]
    (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ) (t : MvPolynomial σ ℂ)
    (hqQ : ∀ j, q j ∈ Q) (hgen : ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q))
    (f : ι → MvPolynomial σ ℂ) (s δ : MvPolynomial σ ℂ) (hfQ : ∀ k, f k ∈ Q)
    (hs : ∀ p ∈ Q, s * p ∈ Ideal.span (Set.range f))
    (hδ : ∀ w : σ → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k x ↦ eval w (pderiv x (f k)))
    (hcard : Fintype.card ι + d = Fintype.card σ) (w : σ → ℂ) (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q)
    (hμ : eval w (s * t * δ) ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j)))) + d =
      Fintype.card σ := by
  have hw' : ∀ p ∈ Q, eval w p = 0 := hw
  simp only [map_mul, mul_ne_zero_iff] at hμ
  obtain ⟨⟨hs0, ht0⟩, hδ0⟩ := hμ
  have heq : Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j))) =
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (f k))) := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro j
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs (q j) (hqQ j))
      exact JacobianRankOffHypersurface.grad_mem_span w s (q j) c f hc (fun k ↦ hw' _ (hfQ k))
        (hw' _ (hqQ j)) hs0
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro k
      obtain ⟨i, hi⟩ := hgen (f k) (hfQ k)
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
      refine JacobianRankOffHypersurface.grad_mem_span w (t ^ i) (f k) c q hc (fun j ↦ hw' _ (hqQ j))
        (hw' _ (hfQ k)) ?_
      rw [map_pow]
      exact pow_ne_zero _ ht0
  rw [heq, finrank_span_eq_card (hδ w hδ0)]
  exact hcard

theorem JacobianRankOffHypersurface.exists_fin (hF : FrameJacobianGeneric.Statement) {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) :
    ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s δ : MvPolynomial (Fin n) ℂ),
      Fintype.card {j // j ∉ I₀} + d = n ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ δ ∉ J ∧
        (∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)) ∧
        ∀ w : Fin n → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k l ↦ eval w (pderiv l (f k)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, s, hcard, hfJ, hsJ, hδJ, hgen⟩ := hF n d J hJ hd b
  refine ⟨I₀, f, s, frameJacobianDet b I₀ f, ?_, hfJ, hsJ, hδJ, hgen, ?_⟩
  · have h1 : Fintype.card {j // j ∉ I₀} = n - I₀.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    have h2 : I₀.card ≤ n := (Finset.card_le_univ I₀).trans_eq (Fintype.card_fin n)
    omega
  · intro w hw
    let M : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun j l ↦ b j l
    have hdet := hw
    rw [frameJacobianDet, RingHom.map_det] at hdet
    have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
    have hrows : (fun k ↦ ((eval w).mapMatrix (Matrix.of fun k j : {j // j ∉ I₀} ↦ frameDeriv b j (f k))) k) =
        (Matrix.mulVecLin M) ∘ fun k l ↦ eval w (pderiv l (f k)) := by
      funext k j

      simp [frameDeriv, M, Matrix.mulVec, dotProduct, map_sum]
    change LinearIndependent ℂ (fun k ↦ ((eval w).mapMatrix
      (Matrix.of fun k j : {j // j ∉ I₀} ↦ frameDeriv b j (f k))) k) at hli
    rw [hrows] at hli
    exact hli.of_comp _

theorem JacobianRankOffHypersurface.proof_of_frame (hF : FrameJacobianGeneric.Statement) :
    JacobianRankOffHypersurface.Statement := by
  intro σ _ Q d r q t hQ hd hqQ htQ hgen
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := Q.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ), eval x (φ p) = eval (x ∘ e.symm) p := fun x p ↦ by
    simp [φ, eval_rename]
  have hJd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    rw [← hd]
    refine (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Q J φ.toRingEquiv.symm ?_)).symm
    exact (Ideal.map_symm (I := Q) φ.toRingEquiv).symm
  obtain ⟨I₀, f, s, δ, hcard, hfJ, hsJ, hδJ, hsgen, hlin⟩ :=
    JacobianRankOffHypersurface.exists_fin hF J hJ hJd
  have hfQ : ∀ k, φ (f k) ∈ Q := fun k ↦ Ideal.mem_comap.mp (hfJ k)
  have hsQ : φ s ∉ Q := fun h ↦ hsJ (Ideal.mem_comap.mpr h)
  have hδQ : φ δ ∉ Q := fun h ↦ hδJ (Ideal.mem_comap.mpr h)
  have hs : ∀ p ∈ Q, φ s * p ∈ Ideal.span (Set.range fun k ↦ φ (f k)) := by
    intro p hp
    have hp' : φ.symm p ∈ J := Ideal.mem_comap.mpr (by rwa [AlgEquiv.apply_symm_apply])
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hsgen _ hp')
    refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun k ↦ φ (c k), ?_⟩
    have := congrArg φ hc

    rw [map_sum, map_mul, AlgEquiv.apply_symm_apply] at this
    simpa [map_mul] using this
  have hδ : ∀ w : σ → ℂ, eval w (φ δ) ≠ 0 →
      LinearIndependent ℂ fun k x ↦ eval w (pderiv x (φ (f k))) := by
    intro w hw
    rw [hφ] at hw
    have hL := (hlin _ hw).map' (LinearMap.funLeft ℂ ℂ e)
      (LinearMap.ker_eq_bot.mpr (LinearMap.funLeft_injective_of_surjective _ _ _ e.surjective))
    have hfam : (fun k x ↦ eval w (pderiv x (φ (f k)))) =
        (LinearMap.funLeft ℂ ℂ e) ∘ fun k l ↦ eval (w ∘ e.symm) (pderiv l (f k)) := by
      funext k x
      simp only [Function.comp_apply, LinearMap.funLeft_apply]
      have hx : pderiv x (φ (f k)) = φ (pderiv (e x) (f k)) := by
        have := pderiv_rename (R := ℂ) e.symm.injective (e x) (f k)
        rw [Equiv.symm_apply_apply] at this
        exact this
      rw [hx, hφ]
    rw [hfam]
    exact hL
  have hμQ : φ s * t * φ δ ∉ Q := by
    intro h
    rcases hQ.mem_or_mem h with h | h
    · rcases hQ.mem_or_mem h with h | h
      · exact hsQ h
      · exact htQ h
    · exact hδQ h
  exact ⟨φ s * t * φ δ, hμQ, fun w hw hμ ↦
    JacobianRankOffHypersurface.finrank_of_generators Q d r q t hqQ hgen (fun k ↦ φ (f k)) (φ s) (φ δ) hfQ hs hδ
      hcard w hw hμ⟩

theorem JacobianRankOffHypersurface.proof : JacobianRankOffHypersurface.Statement :=
  JacobianRankOffHypersurface.proof_of_frame
    (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem ProjectionInjectiveOffHypersurface.proof (hF : FrameJacobianGeneric.Statement) :
    ProjectionInjectiveOffHypersurface.Statement := by
  classical
  intro σ _ I k hI hk
  set n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let φ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ := renameEquiv ℂ e
  let J : Ideal (MvPolynomial (Fin n) ℂ) := I.map φ
  have hJ : J.IsPrime := Ideal.map_isPrime_of_equiv φ
  have hJk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) := by
    rw [← hk]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I J φ rfl).symm)
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, -, hcard, hfJ, -, hdet, -⟩ := hF n k J hJ hJk b

  let T : (σ → ℂ) → EuclideanSpace ℂ (Fin n) := fun x => WithLp.toLp 2 (x ∘ e.symm)
  have hT : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ),
      eval (fun i => T x i) p = eval x (φ.symm p) := by
    intro x p
    have : φ.symm p = rename e.symm p := rfl
    rw [this, eval_rename]
  have hTinj : Function.Injective T := by
    intro x y hxy
    funext s
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v (e s)) hxy
    simpa [T] using this
  have hTc : Continuous T :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply _)
  refine ⟨φ.symm (frameJacobianDet b I₀ f), ?_, ?_⟩
  · intro hmem
    apply hdet
    exact (Ideal.mem_map_of_equiv φ _).2 ⟨_, hmem, by simp⟩
  intro z hz hzh
  have hf0 : ∀ x ∈ zeroSetIn I, ∀ j, eval (fun i => T x i) (f j) = 0 := by
    intro x hx j
    obtain ⟨q, hq, hqf⟩ := (Ideal.mem_map_of_equiv φ (f j)).1 (hfJ j)
    rw [hT, ← hqf, AlgEquiv.symm_apply_apply]
    exact hx q hq
  have hz' : eval (fun i => T z i) (frameJacobianDet b I₀ f) ≠ 0 := by rwa [hT]
  obtain ⟨Ω, V, g, -, hV, hzV, -, -, hpg, hgraph⟩ :=
    FrameImplicitGraph.proof n b I₀ f (T z) (hf0 z hz) hz' Set.univ isOpen_univ (Set.mem_univ _)
  let c : Fin k ≃ I₀ := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let A : (σ → ℂ) →L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm (c j : Fin n))
  refine ⟨T ⁻¹' V, hV.preimage hTc, hzV, A, ?_⟩

  have hback : ∀ x ∈ zeroSetIn I ∩ T ⁻¹' V, g (GroundTheory.Heights₂.Heights.frameProj b I₀ (T x)) = T x := by
    rintro x ⟨hx, hxV⟩
    have hmem : T x ∈ {y : EuclideanSpace ℂ (Fin n) | ∀ j, eval (fun i => y i) (f j) = 0} ∩ V :=
      ⟨hf0 x hx, hxV⟩
    rw [hgraph] at hmem
    obtain ⟨w, hw, hwx⟩ := hmem
    rw [← hwx, hpg w hw]
  intro x hx y hy hAxy
  apply hTinj
  have hproj : GroundTheory.Heights₂.Heights.frameProj b I₀ (T x) = GroundTheory.Heights₂.Heights.frameProj b I₀ (T y) := by
    funext i
    have := congrFun hAxy (c.symm i)
    show inner ℂ (b i) (T x) = inner ℂ (b i) (T y)
    rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner]
    simpa [A, T] using this
  rw [← hback x hx, ← hback y hy, hproj]

theorem ProjectionInjectiveOffHypersurface.proof_of_rank (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : ProjectionInjectiveOffHypersurface.Statement :=
  ProjectionInjectiveOffHypersurface.proof (FrameJacobianGeneric.proof hR hC)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
