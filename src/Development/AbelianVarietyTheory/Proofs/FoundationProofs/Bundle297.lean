module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle289
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle290
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarValueLeMeanSquareGenusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle282
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisTaylorSeriesCanonicalOddThetaAll
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222

@[expose] public section

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_subrep_closure_analytic_vectors : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (πU : URep T) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (E : V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (act Y x)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖E ((act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ (σ : URep T) (j : V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ (∀ g y, J (σ.π g y) = πU.π g (J y)) ∧ (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (act Y x)) 0) := by
  first | exact @GlobalTheory.AnalyticClosure.exists_subrep_closure | exact GlobalTheory.AnalyticClosure.exists_subrep_closure | (intros; apply GlobalTheory.AnalyticClosure.exists_subrep_closure <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  first | exact @GlobalTheory.FockIrr.irreducible_of_weight_line | exact GlobalTheory.FockIrr.irreducible_of_weight_line | (intros; apply GlobalTheory.FockIrr.irreducible_of_weight_line <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.CartanInt.HermChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

def herm {n : Type} (S : n → n → ℝ) : Matrix n n ℂ :=
  Matrix.of fun i j => (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ)

theorem herm_apply {n : Type} (S : n → n → ℝ) (i j : n) :
    herm S i j = (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ) := rfl

theorem herm_conjTranspose {n : Type} (S : n → n → ℝ) : (herm S)ᴴ = herm S := by
  ext i j
  rw [Matrix.conjTranspose_apply, herm_apply, herm_apply]
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]; ring
  · simp only [Complex.star_def, Complex.conj_im]; ring

theorem continuous_herm_entry {X n : Type} [TopologicalSpace X] {f : X → n → n → ℝ}
    (hf : ∀ i j, Continuous fun x => f x i j) (i j : n) : Continuous fun x => herm (f x) i j := by
  have e : (fun x => herm (f x) i j) = fun x => (((f x i j + f x j i) / 2 : ℝ) : ℂ) +
      (((f x i j - f x j i) / 2 : ℝ) : ℂ) * Complex.I := by
    funext x
    rw [herm_apply, Complex.mk_eq_add_mul_I]
  rw [e]
  have h1 := hf i j
  have h2 := hf j i
  fun_prop

theorem sum_norm_sq_herm_sub {n : Type} [Fintype n] (S T : n → n → ℝ) :
    ∑ i, ∑ j, ‖herm S i j - herm T i j‖ ^ 2 = ∑ i, ∑ j, (S i j - T i j) ^ 2 := by
  have h : ∀ i j, ‖herm S i j - herm T i j‖ ^ 2 =
      (S i j - T i j) ^ 2 / 2 + (S j i - T j i) ^ 2 / 2 := by
    intro i j
    rw [Complex.sq_norm, Complex.normSq_apply, herm_apply, herm_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (S j i - T j i) ^ 2 / 2), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem herm_re_add_im {n : Type} (H : n → n → ℂ) (hH : ∀ i j, star (H j i) = H i j) (i j : n) :
    herm (fun i j => (H i j).re + (H i j).im) i j = H i j := by
  have h1 := congrArg Complex.re (hH i j)
  have h2 := congrArg Complex.im (hH i j)
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at h1 h2
  rw [herm_apply]
  apply Complex.ext
  · show _ / (2 : ℝ) = _
    linarith
  · show _ / (2 : ℝ) = _
    linarith

theorem abs_re_add_im_le {z : ℂ} (hz : ‖z‖ ≤ Real.pi) : |z.re + z.im| ≤ 89 / 20 := by
  have h1 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by rw [Complex.sq_norm, Complex.normSq_apply]
  have h2 : ‖z‖ ≤ 3.1416 := hz.trans Real.pi_lt_d4.le
  have h3 : ‖z‖ ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h2 2
  refine abs_le_of_sq_le_sq' ?_ (by norm_num) |> abs_le.2
  nlinarith [sq_nonneg (z.re - z.im)]

theorem exists_chart : ∀ (p q : ℕ), ∃ Φ : ((Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) → Mat p q,
    Continuous Φ ∧ (∀ R, (Φ R)ᴴ = Φ R ∧ IsKC (Φ R)) ∧
    (∀ R R', ∑ a, ∑ b, ‖(Φ R - Φ R') a b‖ ^ 2 = ∑ i, (R i - R' i) ^ 2) ∧
    ∀ H : Mat p q, Hᴴ = H → IsKC H → (∀ a b, ‖H a b‖ ≤ Real.pi) →
      ∃ R, Φ R = H ∧ ∀ i, |R i| ≤ 89 / 20 := by
  intro p q
  refine ⟨fun R => Matrix.fromBlocks (herm fun i j => R (Sum.inl (i, j))) 0 0
    (herm fun i j => R (Sum.inr (i, j))), ?_, fun R => ⟨?_, isKC_fromBlocks _ _⟩, fun R R' => ?_,
    fun H hH hK hb => ?_⟩
  · refine continuous_matrix fun a b => ?_
    rcases a with a | a <;> rcases b with b | b
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inl (i, j))) (fun i j => continuous_apply _) a b
    · exact continuous_const
    · exact continuous_const
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inr (i, j))) (fun i j => continuous_apply _) a b
  · simp only [Matrix.fromBlocks_conjTranspose, herm_conjTranspose, Matrix.conjTranspose_zero]
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type,
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inl (i, j))) (fun i j => R' (Sum.inl (i, j))),
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inr (i, j))) (fun i j => R' (Sum.inr (i, j)))]
    simp [Fintype.sum_sum_type]
  · have hs : ∀ a b, star (H b a) = H a b := fun a b => by
      rw [← Matrix.conjTranspose_apply, hH]
    refine ⟨Sum.elim (fun x => (H (Sum.inl x.1) (Sum.inl x.2)).re + (H (Sum.inl x.1) (Sum.inl x.2)).im)
      (fun x => (H (Sum.inr x.1) (Sum.inr x.2)).re + (H (Sum.inr x.1) (Sum.inr x.2)).im), ?_, ?_⟩
    · ext a b
      rcases a with a | a <;> rcases b with b | b
      · exact herm_re_add_im (fun i j => H (Sum.inl i) (Sum.inl j)) (fun i j => hs _ _) a b
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact herm_re_add_im (fun i j => H (Sum.inr i) (Sum.inr j)) (fun i j => hs _ _) a b
    · rintro (x | x)
      · exact abs_re_add_im_le (hb _ _)
      · exact abs_re_add_im_le (hb _ _)

end GlobalTheory.CartanInt.HermChart
end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.irreducible_completion_of_graded_irreducible_gK : ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → IrrGK M → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IrrU σ := by
  first | exact @GlobalTheory.irrU_of_dense_graded_irrGK | exact GlobalTheory.irrU_of_dense_graded_irrGK | (intros; apply GlobalTheory.irrU_of_dense_graded_irrGK <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open MeasureTheory

noncomputable section

namespace GlobalTheory.MeanSquareConj

theorem mem_conj (Λ : AddSubgroup ℂ) (z : ℂ) :
    z ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ↔ (starRingEnd ℂ) z ∈ Λ := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem area_conj (Λ : AddSubgroup ℂ) : area (Λ.map (starRingEnd ℂ).toAddMonoidHom) = area Λ := by
  unfold area
  congr 1
  ext a
  have e : ∀ x y : ℂ, |((starRingEnd ℂ) ((starRingEnd ℂ) x) * (starRingEnd ℂ) y).im| =
      |((starRingEnd ℂ) x * y).im| := by
    intro x y
    rw [← map_mul, Complex.conj_im, abs_neg]
  simp only [Set.mem_setOf_eq, mem_conj]
  constructor
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, _, hx, _, hy, (e x y).symm⟩
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, (starRingEnd ℂ) x, by simpa using hx, (starRingEnd ℂ) y, by simpa using hy, (e x y).symm⟩

theorem lattice_conj (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧
      Λ.map (starRingEnd ℂ).toAddMonoidHom = AddSubgroup.closure {w₁, w₂} := by
  obtain ⟨w₁, w₂, hli, rfl⟩ := hΛ
  refine ⟨(starRingEnd ℂ) w₁, (starRingEnd ℂ) w₂, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff] at hli ⊢
    intro s t h
    refine hli s t ?_
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  · rw [AddMonoidHom.map_closure, Set.image_pair]
    rfl

theorem thetaTranslate_conjugateLattice (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (t z : ℂ) :
    U1 (Λ.map (starRingEnd ℂ).toAddMonoidHom) t (fun z => (starRingEnd ℂ) (G ((starRingEnd ℂ) z))) z =
      (starRingEnd ℂ) (U1 Λ ((starRingEnd ℂ) t) G ((starRingEnd ℂ) z)) := by
  unfold U1
  rw [area_conj, map_mul, ← Complex.exp_conj]
  simp only [map_add (f := _), map_sub, map_div₀, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj, map_ofNat]

theorem sgStar_conj (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    sgStar (Λ.map (starRingEnd ℂ).toAddMonoidHom) =
      fun z => (starRingEnd ℂ) (sgStar Λ ((starRingEnd ℂ) z)) := by
  obtain ⟨⟨hd, h1, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨-, -, huniq, -⟩ := GlobalTheory.OddTheta.sgStar_laws _ (lattice_conj Λ hΛ)
  have hder : ∀ z, HasDerivAt (fun z => (starRingEnd ℂ) (sgStar Λ ((starRingEnd ℂ) z)))
      ((starRingEnd ℂ) (deriv (sgStar Λ) ((starRingEnd ℂ) z))) z := by
    intro z
    have := (hd ((starRingEnd ℂ) z)).hasDerivAt.conj_conj
    rw [Complex.conj_conj] at this
    exact this
  funext z
  have := huniq _ (fun z => (hder z).differentiableAt) (by
    intro ω hω z
    rw [thetaTranslate_conjugateLattice, hU _ ((mem_conj Λ ω).1 hω), map_mul]
    congr 1
    have e : (starRingEnd ℂ) (ω / 2) = (starRingEnd ℂ) ω / 2 := by
      rw [map_div₀, map_ofNat]
    simp only [mem_conj, e]
    split_ifs <;> simp) z
  rw [(hder 0).deriv, map_zero, h1, map_one, one_mul] at this
  exact this.symm

theorem evenTheta_conjugateLattice (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) (t z : ℂ) :
    GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t) z =
      (starRingEnd ℂ) (GL3Theta.th0 Λ t ((starRingEnd ℂ) z)) := by
  unfold GL3Theta.th0
  rw [sgStar_conj Λ hΛ, thetaTranslate_conjugateLattice, thetaTranslate_conjugateLattice, map_div₀, map_zero, Complex.conj_conj]

theorem evenTheta_weightedNormSq_periodic (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) (t : ℂ)
    (x : ℂ) (hx : x ∈ Λ) (z : ℂ) :
    ‖GL3Theta.th0 Λ t (x + z)‖ ^ 2 * Real.exp (-Real.pi * ‖x + z‖ ^ 2 / area Λ) =
      ‖GL3Theta.th0 Λ t z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
  obtain ⟨⟨-, -, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  have hper : ∀ z, ‖sgStar Λ (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area Λ) =
      ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    intro z
    rw [← GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq, hU x hx, norm_mul]
    split_ifs <;> simp
  unfold GL3Theta.th0
  simp only [norm_div, div_pow, div_mul_eq_mul_div]
  rw [GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq, GlobalTheory.GenusOneSup.thetaTranslation_weighted_normSq,
    show x + z + t = z + t + x by ring, hper]

theorem nrm1Sq_th0_map_conj_eq : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ t : ℂ, nrm1Sq (Λ.map (starRingEnd ℂ).toAddMonoidHom) (GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t)) = nrm1Sq Λ (GL3Theta.th0 Λ t) := by
  intro Λ hΛ t
  have hex : ∀ A : AddSubgroup ℂ,
      (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ A = AddSubgroup.closure {w₁, w₂}) →
      IsAddFundamentalDomain A
        (Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain A Fd volume) volume := by
    rintro A ⟨w₁, w₂, hli, rfl⟩
    obtain ⟨F, hF, -⟩ := GlobalTheory.GenusOneSup.exists_domain hli
    exact Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain _ Fd volume) ⟨F, hF⟩
  have hF := hex Λ hΛ
  have hF' := hex _ (lattice_conj Λ hΛ)
  have hcount : Countable Λ := by
    obtain ⟨w₁, w₂, -, h⟩ := hΛ
    have : (Λ : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => p.1 • w₁ + p.2 • w₂) := by
      intro x hx
      rw [h] at hx
      obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
      exact ⟨(m, n), rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : VAddInvariantMeasure Λ ℂ volume := ⟨fun γ s _ => measure_preimage_add volume (γ : ℂ) s⟩
  unfold nrm1Sq
  simp only
  set F := Classical.epsilon fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume
  set F' := Classical.epsilon fun Fd : Set ℂ =>
    IsAddFundamentalDomain (Λ.map (starRingEnd ℂ).toAddMonoidHom) Fd volume
  have hmp : MeasurePreserving (starRingEnd ℂ) volume volume := Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (starRingEnd ℂ) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hF2 : IsAddFundamentalDomain Λ ((starRingEnd ℂ) ⁻¹' F') volume := by
    refine hF'.preimage_of_equiv (f := starRingEnd ℂ)
      (e := fun y => (⟨(starRingEnd ℂ) y, (mem_conj Λ _).1 y.2⟩ : Λ))
      hmp.quasiMeasurePreserving ⟨?_, ?_⟩ ?_
    · intro x y h
      exact Subtype.ext (star_injective (congrArg Subtype.val h))
    · intro x
      exact ⟨⟨(starRingEnd ℂ) x, (mem_conj Λ _).2 (by simp)⟩, Subtype.ext (by simp)⟩
    · intro y x
      show (starRingEnd ℂ) ((starRingEnd ℂ) y + x) = (y : ℂ) + (starRingEnd ℂ) x
      simp
  rw [setAverage_eq, setAverage_eq, measureReal_def, measureReal_def, hF.measure_eq hF2,
    hF.setIntegral_eq hF2 (fun γ z => evenTheta_weightedNormSq_periodic Λ hΛ t γ γ.2 z), hmp.measure_preimage_emb hemb,
    ← hmp.setIntegral_preimage_emb hemb]
  simp only [evenTheta_conjugateLattice Λ hΛ, area_conj, Complex.conj_conj, Complex.norm_conj]

end GlobalTheory.MeanSquareConj
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.thetaLattice_agree_of_trivialAt_prime : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' q : ℕ) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TrivAt D q (k : GL (Fin N) (AE D)) → TrivAt D q (k' : GL (Fin N') (AE D)) → Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → (∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₂ L₂') ∧ (∀ x ∈ La D (tor0 D cc δ) L₂ L₂', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₁ L₁') := by
  first | exact @GlobalTheory.NormSum.La_agree_of_trivAt | exact GlobalTheory.NormSum.La_agree_of_trivAt | (intros; apply GlobalTheory.NormSum.La_agree_of_trivAt <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.galStar_complexMultiplication_points : ∀ D : D7, galStar D := by
  first | exact @GlobalTheory.ConjPoint.galStar_holds | exact GlobalTheory.ConjPoint.galStar_holds | (intros; apply GlobalTheory.ConjPoint.galStar_holds <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.galois_taylorSeries_canonicalOddTheta_all : ∀ D : D7, galSg D := by
  first | exact @GlobalTheory.SigmaConj.galSg_all | exact GlobalTheory.SigmaConj.galSg_all | (intros; apply GlobalTheory.SigmaConj.galSg_all <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_orthonormal_frame_var : ∀ (D : D7) (N N' : ℕ), ∃ (m r : ℕ) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b := by
  first | exact @GlobalTheory.FourCopies.exists_onB_four | exact GlobalTheory.FourCopies.exists_onB_four | (intros; apply GlobalTheory.FourCopies.exists_onB_four <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.sigmaStar_value_le_meanSquare_genusOne : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t, ‖U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ)) 0‖ ^ 2 ≤ 3 * (2 * D.host.rdE + 1) * nrm1Sq (lamOf D cc δ) (sgStar (lamOf D cc δ)) := by
  first | exact @GlobalTheory.GenusOneSup.value_le_mean_square | exact GlobalTheory.GenusOneSup.value_le_mean_square | (intros; apply GlobalTheory.GenusOneSup.value_le_mean_square <;> assumption)
end
