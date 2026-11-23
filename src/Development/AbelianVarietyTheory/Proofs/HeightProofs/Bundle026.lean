module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.CoverURep

variable {p q n : ℕ}

theorem gl_isEmbedding_val :
    Topology.IsEmbedding (Units.val : (Mat p q)ˣ → Mat p q) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Mat p q => A⁻¹) (fun A hA => ?_) (fun u => ?_)
  · have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    exact (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt
  · simp

theorem inducing_pair (T : GrpData p q) (e : Ix p q ≃ Fin n) :
    Topology.IsInducing (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) := by
  have h1 : Topology.IsInducing (fun A : Mat p q => Matrix.reindex e e A) := by
    refine Topology.IsInducing.of_comp (g := fun B : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm B)
      (continuous_id.matrix_reindex e e) (continuous_id.matrix_reindex e.symm e.symm) ?_
    convert Topology.IsInducing.id using 1
    funext A i j
    simp [Matrix.reindex_apply]
  exact ((h1.comp gl_isEmbedding_val.isInducing).prodMap Units.isEmbedding_val₀.isInducing).comp T.emb.isInducing

theorem det_Jm_ne_zero {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) : (Jm p q).det ≠ 0 := by
  have : (Matrix.reindex e e (Jm p q)).det * (Matrix.reindex e e (Jm p q)).det = 1 := by
    rw [h.reindex_Jm, ← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
  rw [Matrix.det_reindex_self] at this
  exact left_ne_zero_of_mul_eq_one this

theorem norm_sq_eq_one {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    ‖((T.sq x : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg Matrix.det ((mem_Upq _).1 (T.cov_mem x))
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← T.sq_sq x] at h1
  have h2 := congrArg norm h1
  rw [norm_mul, norm_mul, norm_star, norm_pow] at h2
  have h3 : ‖(Jm p q).det‖ ≠ 0 := norm_ne_zero_iff.2 (det_Jm_ne_zero h)
  have h4 : ‖((T.sq x : ℂˣ) : ℂ)‖ ^ 4 = 1 := by
    apply mul_left_cancel₀ h3
    linear_combination h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4

theorem continuousOn_of_cover {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q)
    {Y : Type*} [TopologicalSpace Y] (f : Matrix (Fin n) (Fin n) ℂ → Y)
    (hf : Continuous fun x : T.G => f (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))) :
    ContinuousOn f (UJset ε) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  obtain ⟨C, hC, hCe⟩ := (inducing_pair T e).isClosed_iff.1 (ht.preimage hf)
  have hK : CompactSpace (Metric.closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  have hD : IsClosed {z : Matrix (Fin n) (Fin n) ℂ × Metric.closedBall (0 : ℂ) 1 |
      (z.1, (z.2 : ℂ)) ∈ C ∧ (z.2 : ℂ) ^ 2 = z.1.det} := by
    refine IsClosed.inter (hC.preimage (by fun_prop)) (isClosed_eq (by fun_prop) ?_)
    exact continuous_fst.matrix_det
  refine ⟨_, isClosedMap_fst_of_compactSpace _ hD, ?_⟩
  ext g
  constructor
  · rintro ⟨hg, hU⟩
    refine ⟨?_, hU⟩
    obtain ⟨x, rfl⟩ := h.cov_surj T hU
    have hx : x ∈ (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C := by
      rw [hCe]; exact hg
    refine ⟨(_, ⟨((T.sq x : ℂˣ) : ℂ), by simp [norm_sq_eq_one h T x]⟩), ⟨hx, ?_⟩, rfl⟩
    simp only [Matrix.det_reindex_self]
    exact T.sq_sq x
  · rintro ⟨⟨⟨g', w, hw⟩, ⟨h1, h2⟩, rfl⟩, hU⟩
    refine ⟨?_, hU⟩
    obtain ⟨x, hx⟩ := h.cov_surj T hU
    simp only at hx h1 h2
    subst hx
    rw [Matrix.det_reindex_self] at h2
    have hw0 : w ≠ 0 := by
      rintro rfl
      have := T.sq_sq x
      rw [← h2] at this
      simp at this
    obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := T.bij (T.cov x) (T.cov_mem x) (Units.mk0 w hw0) h2
    have hy : y ∈ (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C := by
      simp only [Set.mem_preimage, hy1, hy2]
      exact h1
    rw [hCe] at hy
    simp only [Set.mem_preimage, hy1] at hy
    exact hy

theorem urep_irred : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T)
    (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ →
      IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ := by
  intro p q n e ε T R σ h hF
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · have := hF 1
    rw [map_one, map_one] at this
    rw [this]
    simp
  · intro a ha b hb
    obtain ⟨x, rfl⟩ := h.cov_surj T ha
    obtain ⟨y, rfl⟩ := h.cov_surj T hb
    have := hF (x * y)
    rw [map_mul, map_mul, hF x, hF y] at this
    rw [← ContinuousLinearMap.mul_def, this]
    simp [Matrix.submatrix_mul_equiv]
  · intro g hg v
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    rw [← hF x]
    exact R.U.isom x v
  · intro v
    refine continuousOn_of_cover h T _ ?_
    simpa only [← hF _] using R.U.cont v
  · intro S hS hst
    refine R.irred S hS fun x v hv => ?_
    rw [hF x]
    exact hst _ (h.cov_mem T x) v hv

end GlobalTheory.RealPar.CoverURep

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar

theorem flow_mem_map {V H : Type*} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : V →ₗ[ℂ] H) (a : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, a w ∈ W)
    (U : ℝ → H →L[ℂ] H) (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (hder : ∀ v, HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) 0) (t : ℝ) :
    ∀ x ∈ W.map ι, U t x ∈ W.map ι := by
  classical
  have hd : ∀ v s, HasDerivAt (fun t : ℝ => U t (ι v)) (U s (ι (a v))) s := by
    intro v s
    have h1 : HasDerivAt (fun t : ℝ => U (t - s) (ι v)) (ι (a v)) s := by
      have := (show HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) (s - s) by
        rw [sub_self]; exact hder v)
      exact this.comp_sub_const s s
    have h2 := ((U s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : (fun t : ℝ => U t (ι v)) = ((U s).restrictScalars ℝ) ∘ fun t : ℝ => U (t - s) (ι v) := by
      ext r
      have := hadd s (r - s)
      rw [add_sub_cancel] at this
      simp [this]
    rw [h3]
    exact h2
  rintro _ ⟨w, hw, rfl⟩
  rw [← (W.map ι).orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro y hy
  let b := Module.finBasis ℂ W
  let f : ℝ → Fin (Module.finrank ℂ W) → ℂ := fun s i => inner ℂ y (U s (ι (b i)))
  have hf : ∀ s (u : W), inner ℂ y (U s (ι u)) = ∑ j, b.repr u j * f s j := by
    intro s u
    have h3 : (u : V) = ∑ j, b.repr u j • (b j : V) := by
      have := congrArg W.subtype (b.sum_repr u)

      rw [map_sum] at this
      exact this.symm
    rw [h3]

    simp only [f, map_sum, map_smul, inner_sum, inner_smul_right]
  let M : Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
    fun i j => b.repr ⟨a (b i), hW _ (b i).2⟩ j
  let L := LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  have hfd : ∀ s, HasDerivAt f (L (f s)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have h2 := ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hd (b i) s)
    have := hf s ⟨a (b i), hW _ (b i).2⟩
    have h4 : L (f s) i = ∑ j, b.repr ⟨a (b i), hW _ (b i).2⟩ j * f s j := by
      simp only [L, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
      rfl
    rw [h4, ← this]
    exact h2
  have hf0 : f 0 = 0 := by
    ext i
    simp only [f, h0]
    exact Submodule.inner_left_of_mem_orthogonal (K := W.map ι) ⟨b i, (b i).2, rfl⟩ hy
  have hz : f = fun _ => 0 := by
    refine ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊) (t₀ := 0)
      (fun _ => L.lipschitz.lipschitzOnWith) (fun s => ⟨hfd s, trivial⟩) (fun s => ⟨?_, trivial⟩) hf0
    simpa using hasDerivAt_const s (0 : Fin (Module.finrank ℂ W) → ℂ)
  rw [hf t ⟨w, hw⟩, hz]
  simp

theorem isKStableOn_of_kStable : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → KStable R.HK.act W → IsKStableOn ε σ (W.map R.ι) := by
  intro p q n e ε T R σ hb hF W hfin hK k hk
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective Y
  have hX : X ∈ upq p q := by
    have h1 := hY.1
    unfold Formalism.REAL.inG at h1
    rw [← hb.reindex_Jm, Matrix.conjTranspose_reindex] at h1
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_add]
    exact h1
  have hKC : IsKC X := by
    intro a b hab
    rw [hb.sameBlock_iff] at hab
    have h2 := congrFun (congrFun hY.2 (e a)) (e b)
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at h2
    cases h3 : ε (e a) <;> cases h4 : ε (e b) <;> rw [h3, h4] at hab h2
    · exact (hab rfl).elim
    · simp only [if_true, Bool.false_eq_true, if_false] at h2
      linear_combination (1/2 : ℂ) * h2
    · simp only [if_true, Bool.false_eq_true, if_false] at h2
      linear_combination (-1/2 : ℂ) * h2
    · exact (hab rfl).elim
  have hk' : σ k = R.U.π (T.expt ((1 : ℝ) • X)) := by
    rw [hF, one_smul, T.expt_cov X hX, ← hexp]
    congr 1
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
      exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X).symm
  rw [hk']
  exact flow_mem_map R.ι (R.HK.act X) W (hK X hKC) (fun t => R.U.π (T.expt (t • X)))
    (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add X hX, map_mul]) (R.der X hX) 1

end GlobalTheory.RealPar
end
