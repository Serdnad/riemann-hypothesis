module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle001
public import Mathlib.LinearAlgebra.Lagrange
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle533
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle532
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle531
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Polynomial PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagProperProof

local notation "θ" => thetaR (starRingEnd ℂ) _

variable {n : ℕ}

theorem th_val (g : GL (Fin n) ℂ) : (θ g).val = ((g⁻¹ : GL (Fin n) ℂ).val)ᴴ := by
  ext i j
  simp [thetaR_val, Matrix.conjTranspose_apply]

theorem th_inv_val (g : GL (Fin n) ℂ) : ((θ g)⁻¹ : GL (Fin n) ℂ).val = (g.val)ᴴ := by
  rw [← map_inv, th_val, inv_inv]

theorem th_th (g : GL (Fin n) ℂ) : θ (θ g) = g := by
  apply Units.ext
  rw [th_val, th_inv_val, Matrix.conjTranspose_conjTranspose]

theorem th_diag {d : GL (Fin n) ℂ} {z : Fin n → ℂ} (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1) :
    θ d = d := by
  have h : d * (θ d)⁻¹ = 1 := by
    apply Units.ext
    rw [Units.val_mul, th_inv_val, hd, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Units.val_one]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    simp [Complex.mul_conj', hz i]
  exact (mul_inv_eq_one.mp h).symm

theorem continuous_th : Continuous (fun g : GL (Fin n) ℂ => θ g) := by
  rw [Units.continuous_iff]
  constructor
  · have : (Units.val ∘ fun g : GL (Fin n) ℂ => θ g) = fun g => ((g⁻¹ : GL (Fin n) ℂ).val)ᴴ := by
      funext g; exact th_val g
    rw [this]
    exact (Units.continuous_coe_inv).matrix_conjTranspose
  · have : (fun g : GL (Fin n) ℂ => ((θ g)⁻¹ : GL (Fin n) ℂ).val) = fun g => (g.val)ᴴ := by
      funext g; exact th_inv_val g
    show Continuous (fun g : GL (Fin n) ℂ => ((θ g)⁻¹ : GL (Fin n) ℂ).val)
    rw [this]
    exact Units.continuous_val.matrix_conjTranspose

theorem aeval_conj (p : GL (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (f : ℂ[X]) :
    aeval (p.val * A * (p⁻¹ : GL (Fin n) ℂ).val) f = p.val * aeval A f * (p⁻¹ : GL (Fin n) ℂ).val := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add (f := _), hf, hg, mul_add, add_mul]
  | monomial k a =>
    simp only [aeval_monomial, Units.conj_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]

theorem aeval_diag (w : Fin n → ℂ) (f : ℂ[X]) :
    aeval (diagonal w) f = diagonal fun k => f.eval (w k) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add (f := _), hf, hg, eval_add, Matrix.diagonal_add]
  | monomial k a =>
    ext i j
    by_cases h : i = j
    · subst h
      simp [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, eval_monomial]
    · simp [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, h]

def lag (z : Fin n → ℂ) (i : Fin n) : ℂ[X] := Lagrange.basis Finset.univ (fun k => z k ^ 2) i

def tr (z : Fin n → ℂ) (i : Fin n) (y : GL (Fin n) ℂ) : ℂ :=
  trace (aeval ((y * θ y).val) (lag z i) * y.val)

theorem continuous_tr (z : Fin n → ℂ) (i : Fin n) : Continuous (tr z i) := by
  unfold tr
  have h1 : Continuous fun y : GL (Fin n) ℂ => (y * θ y).val :=
    Units.continuous_val.comp (continuous_id.mul continuous_th)
  exact (((Polynomial.continuous_aeval (lag z i)).comp h1).mul Units.continuous_val).matrix_trace

theorem tr_eq {d : GL (Fin n) ℂ} {z : Fin n → ℂ} (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective fun i => z i ^ 2) (p : GL (Fin n) ℂ) (i : Fin n) :
    tr z i (p * d * θ p⁻¹) = z i * ((∑ k, ‖p.val k i‖ ^ 2 : ℝ) : ℂ) := by
  have hθd := th_diag hd hz
  have hy2 : (p * d * θ p⁻¹) * θ (p * d * θ p⁻¹) = p * (d * d) * p⁻¹ := by
    simp only [map_mul, th_th, hθd, map_inv]
    group
  have hdd : (d * d).val = diagonal fun k => z k ^ 2 := by
    rw [Units.val_mul, hd, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    ring
  have hL : (diagonal fun k => (lag z i).eval (z k ^ 2)) = diagonal (Pi.single i 1) := by
    congr 1
    funext k
    by_cases h : k = i
    · subst h
      simpa [lag] using Lagrange.eval_basis_self (s := Finset.univ) (v := fun k => z k ^ 2)
        (hinj.injOn) (Finset.mem_univ k)
    · rw [Pi.single_eq_of_ne h]
      exact Lagrange.eval_basis_of_ne (s := Finset.univ) (v := fun k => z k ^ 2) (Ne.symm h) (Finset.mem_univ k)
  have hA : aeval ((p * d * θ p⁻¹ * θ (p * d * θ p⁻¹)).val) (lag z i) =
      p.val * diagonal (Pi.single i 1) * (p⁻¹ : GL (Fin n) ℂ).val := by
    rw [hy2, Units.val_mul, Units.val_mul, hdd, aeval_conj, aeval_diag, hL]
  have hyv : (p * d * θ p⁻¹).val = p.val * diagonal z * (p.val)ᴴ := by
    rw [Units.val_mul, Units.val_mul, hd, th_val, inv_inv]
  have hpp : (p⁻¹ : GL (Fin n) ℂ).val * p.val = 1 := by
    rw [← Units.val_mul]; simp
  unfold tr
  rw [hA, hyv]
  have e1 : p.val * diagonal (Pi.single i 1) * (p⁻¹ : GL (Fin n) ℂ).val * (p.val * diagonal z * (p.val)ᴴ) =
      p.val * (diagonal (Pi.single i 1) * diagonal z * (p.val)ᴴ) := by
    calc _ = p.val * diagonal (Pi.single i 1) * ((p⁻¹ : GL (Fin n) ℂ).val * p.val) * diagonal z * (p.val)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpp]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [e1, Matrix.trace_mul_comm, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc, Matrix.trace]
  simp only [Matrix.diag_apply]
  simp only [Matrix.diagonal_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (fun h => (h (Finset.mem_univ i)).elim)]
  simp only [Pi.single_eq_same, one_mul, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simpa using Complex.conj_mul' (p.val k i)

def twy (x d : GL (Fin n) ℂ) : GL (Fin n) ℂ := x⁻¹ * d * θ x

theorem isCompact_of_bounded {S : Set (GL (Fin n) ℂ)} (hS : IsClosed S) (R : ℝ)
    (h : ∀ x ∈ S, ∀ i j, ‖x.val i j‖ ≤ R ∧ ‖(x⁻¹ : GL (Fin n) ℂ).val i j‖ ≤ R) : IsCompact S := by
  have hK : IsCompact {M : Matrix (Fin n) (Fin n) ℂ | ∀ i j, ‖M i j‖ ≤ R} := by
    have : {M : Matrix (Fin n) (Fin n) ℂ | ∀ i j, ‖M i j‖ ≤ R} =
        Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) R := by
      ext M
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hemb := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) ℂ)
  rw [hemb.isCompact_iff]
  refine (hK.prod (hK.image MulOpposite.continuous_op)).of_isClosed_subset (hemb.isClosedMap _ hS) ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨fun i j => (h x hx i j).1, (x⁻¹ : GL (Fin n) ℂ).val, fun i j => (h x hx i j).2, rfl⟩

theorem col_bound {d : GL (Fin n) ℂ} {z : Fin n → ℂ} (hd : d.val = diagonal z) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective fun i => z i ^ 2) (p : GL (Fin n) ℂ) {B : ℝ}
    (hB : ∑ i, ‖tr z i (p * d * θ p⁻¹)‖ ≤ B) (k i : Fin n) : ‖p.val k i‖ ≤ B + 1 := by
  have h1 : ‖tr z i (p * d * θ p⁻¹)‖ ≤ B :=
    (Finset.single_le_sum (f := fun i => ‖tr z i (p * d * θ p⁻¹)‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)).trans hB
  rw [tr_eq hd hz hinj, norm_mul, hz, one_mul, Complex.norm_real, Real.norm_of_nonneg
    (Finset.sum_nonneg fun _ _ => by positivity)] at h1
  have h2 : ‖p.val k i‖ ^ 2 ≤ ∑ k, ‖p.val k i‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖p.val k i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
  have h3 : 0 ≤ B := (by positivity : 0 ≤ ‖p.val k i‖ ^ 2).trans (h2.trans h1)
  nlinarith [sq_nonneg (‖p.val k i‖ - 1)]

theorem diagProper : DiagProper := by
  intro n d z hd hz hinj C hC
  have hθd := th_diag hd hz
  set S : Set (GL (Fin n) ℂ) := {x | PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) n) x d ∈ C} with hSdef
  have hcont : Continuous fun x : GL (Fin n) ℂ => PositivityTheory.Rg.Tf.Loc.twConj (thetaR (starRingEnd ℂ) n) x d := by
    unfold PositivityTheory.Rg.Tf.Loc.twConj
    exact (continuous_inv.mul continuous_const).mul continuous_th
  have hcl : IsClosed S := hC.isClosed.preimage hcont
  have hC' : IsCompact (C ∪ (fun g : GL (Fin n) ℂ => θ g) '' C) := hC.union (hC.image continuous_th)
  have hG : Continuous fun y : GL (Fin n) ℂ => ∑ i, ‖tr z i y‖ :=
    continuous_finsetSum _ fun i _ => (continuous_tr z i).norm
  obtain ⟨B, hB⟩ := hC'.exists_bound_of_continuousOn hG.continuousOn
  have hB' : ∀ y ∈ C ∪ (fun g : GL (Fin n) ℂ => θ g) '' C, ∑ i, ‖tr z i y‖ ≤ B :=
    fun y hy => (le_abs_self _).trans (hB y hy)
  refine isCompact_of_bounded hcl (B + 1) fun x hx i j => ⟨?_, ?_⟩
  ·
    have hy : twy x d ∈ C := hx
    have e : θ (twy x d) = (θ x⁻¹) * d * θ (θ x⁻¹)⁻¹ := by
      simp only [twy, map_mul, map_inv, th_th, hθd, inv_inv]
    have := col_bound hd hz hinj (θ x⁻¹) (B := B) (by
      rw [← e]; exact hB' _ (Or.inr ⟨_, hy, rfl⟩)) j i
    rw [th_val, inv_inv, Matrix.conjTranspose_apply, norm_star] at this
    exact this
  · have hy : twy x d ∈ C := hx
    have e : twy x d = x⁻¹ * d * θ (x⁻¹)⁻¹ := by simp [twy]
    exact col_bound hd hz hinj x⁻¹ (B := B) (by rw [← e]; exact hB' _ (Or.inl hy)) i j

end GlobalTheory.CompanionTheory.DiagProperProof
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SmallRatCell

open RestrictedProduct InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

theorem exists_nat_mem (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ v ∈ S, ((N : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hpos : 0 < ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    Finset.prod_pos fun v _ => Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  refine ⟨2 * ∏ v ∈ S, Ideal.absNorm v.asIdeal, by omega, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ : Ideal.absNorm v.asIdeal ∣ 2 * ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    (Finset.dvd_prod_of_mem _ hv).mul_left 2
  rw [hc]
  push_cast
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

def tau (N k : ℕ) : ℚ := (N : ℚ) ^ k / (1 + ((N : ℚ) ^ k) ^ 2)

theorem tau_pos {N : ℕ} (hN : 2 ≤ N) (k : ℕ) : 0 < tau N k := by
  have : (0 : ℚ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold tau
  positivity

theorem tendsto_tau_fin (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (hN : ((N : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Tendsto (fun k => algebraMap F (v.adicCompletion F) ((tau N k : ℚ) : F)) atTop (𝓝 0) := by
  have hv : Valued.v (N : v.adicCompletion F) < 1 := by
    have e : (N : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) (N : 𝓞 F) :=
      (map_natCast _ N).symm
    rw [e]
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)
    have h2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (N : 𝓞 F)).2 hN
    exact h1 ▸ h2
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
  have h2 : Tendsto (fun k : ℕ => 1 + ((N : v.adicCompletion F) ^ k) ^ 2) atTop (𝓝 1) := by
    simpa using (ht.pow 2).const_add 1
  have h3 := ht.div h2 one_ne_zero
  rw [zero_div] at h3
  refine h3.congr fun k => ?_
  simp [tau, map_div₀, map_add (f := _), map_pow, map_natCast]

theorem tendsto_tau_inf (w : InfinitePlace F) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun k => algebraMap F w.Completion ((tau N k : ℚ) : F)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ k, ‖algebraMap F w.Completion ((tau N k : ℚ) : F)‖ = (tau N k : ℝ) := fun k => by
    rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
    have h := map_ratCast ((extensionEmbedding w).comp (algebraMap F w.Completion)) (tau N k)
    rw [RingHom.comp_apply] at h
    rw [h, Complex.norm_ratCast, abs_of_pos (by exact_mod_cast tau_pos hN k)]
  simp only [hnorm]
  have hb : ∀ k, (tau N k : ℝ) ≤ (1 / 2 : ℝ) ^ k := fun k => by
    have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hx : (2 : ℝ) ^ k ≤ (N : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) h2 k
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hxp : (0 : ℝ) < (N : ℝ) ^ k := by linarith
    simp only [tau]
    push_cast
    rw [one_div, inv_pow, div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ k * (N : ℝ) ^ k ≤ 1 + ((N : ℝ) ^ k) ^ 2 := by nlinarith
    rw [← div_eq_inv_mul, le_div_iff₀ hp]
    linarith
  refine squeeze_zero (fun k => by exact_mod_cast (tau_pos hN k).le) hb ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)


open Classical in
def finS (S : Finset (HeightOneSpectrum (𝓞 F))) (q : F) :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  ⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) q else 0, by
    rw [Filter.eventually_principal]
    intro v hv
    have hv' : v ∉ S := by simpa using hv
    simp only [if_neg hv']
    exact zero_mem _⟩

theorem cofinite_le (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  rw [le_principal_iff, mem_cofinite, compl_compl]
  exact S.finite_toSet

def sAd (S : Finset (HeightOneSpectrum (𝓞 F))) (q : F) : AF F :=
  (fun w => algebraMap F w.Completion q,
    RestrictedProduct.inclusion _ _ (cofinite_le S) (finS S q))

theorem tendsto_sAd (S : Finset (HeightOneSpectrum (𝓞 F))) (q : ℕ → F)
    (hi : ∀ w : InfinitePlace F, Tendsto (fun k => algebraMap F w.Completion (q k)) atTop (𝓝 0))
    (hf : ∀ v ∈ S, Tendsto (fun k => algebraMap F (v.adicCompletion F) (q k)) atTop (𝓝 0)) :
    Tendsto (fun k => sAd S (q k)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => finS S (q k)) atTop (𝓝 0) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    by_cases hv : v ∈ S
    · refine (hf v hv).congr fun k => ?_
      exact (if_pos hv).symm
    · refine tendsto_const_nhds.congr fun k => ?_
      show (0 : v.adicCompletion F) = _
      exact (if_neg hv).symm
  have h2 := ((RestrictedProduct.continuous_inclusion (cofinite_le S)).tendsto 0).comp h1
  refine Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hi) h2

theorem one_tmul_algebraMap {A E : Type} [CommRing A] [Algebra F A] [Field E] [Algebra F E] (q : F) :
    (1 : A) ⊗ₜ[F] algebraMap F E q = algebraMap F A q ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

theorem ring_hom_mul_sub_eq_zero {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x e y : A) (c : B)
    (hc : f e = c) (h : f x * c = f y) : f (x * e - y) = 0 := by
  rw [map_sub, map_mul, hc, h, sub_self]


open Classical in
theorem tensor_key {E : Type} [Field E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : AF F ⊗[F] E) (hi : ∀ w, compInf F E w e = 1)
    (hf : ∀ v, compFin F E v e = if v ∈ S then 1 else 0) (q : F) :
    ((1 : AF F) ⊗ₜ[F] algebraMap F E q) * e = sAd S q ⊗ₜ[F] (1 : E) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.CompanionTheory.AdeleComp.tensor_eq_zero _ (fun w => ?_) (fun v => ?_)
  · refine ring_hom_mul_sub_eq_zero (compInf F E w) _ _ _ _ (hi w) ?_
    rw [mul_one]
    exact one_tmul_algebraMap (A := w.Completion) _
  · refine ring_hom_mul_sub_eq_zero (compFin F E v) _ _ _ _ (hf v) ?_
    by_cases hv : v ∈ S
    · rw [if_pos hv, mul_one]
      have h : evFin F v (sAd S q) = algebraMap F (v.adicCompletion F) q := if_pos hv
      show (1 : v.adicCompletion F) ⊗ₜ[F] _ = evFin F v (sAd S q) ⊗ₜ[F] (1 : E)
      rw [h]
      exact one_tmul_algebraMap _
    · rw [if_neg hv, mul_zero]
      have h : evFin F v (sAd S q) = 0 := if_neg hv
      show 0 = evFin F v (sAd S q) ⊗ₜ[F] (1 : E)
      rw [h, TensorProduct.zero_tmul]

theorem incA_mul_idem (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) (q : ℚ) :
    incA D ((q : ℚ) : D.host.E) * e = sAd S ((q : ℚ) : D.host.F) • (1 : AE D) := by
  have hq : ((q : ℚ) : D.host.E) = algebraMap D.host.F D.host.E ((q : ℚ) : D.host.F) :=
    (map_ratCast (algebraMap D.host.F D.host.E) q).symm
  have hs : sAd S ((q : ℚ) : D.host.F) • (1 : AE D) =
      sAd S ((q : ℚ) : D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    show _ • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, hq]
  exact tensor_key S e he.1 he.2 _

theorem smallRat : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Cell.SmallRat := by
  intro _ D S e he V hV M
  obtain ⟨N, hN, hmem⟩ := exists_nat_mem S
  have ht : Tendsto (fun k => sAd S ((tau N k : ℚ) : D.host.F)) atTop (𝓝 0) :=
    tendsto_sAd S _ (fun w => tendsto_tau_inf w hN) (fun v hv => tendsto_tau_fin v (hmem v hv))
  have hz : Tendsto (fun k => incA D ((tau N k : ℚ) : D.host.E) * e) atTop (𝓝 0) := by
    have h := ht.smul_const (1 : AE D)
    rw [zero_smul] at h
    exact h.congr fun k => (incA_mul_idem D S e he _).symm
  have hall : ∀ᶠ k in atTop, ∀ j : Fin M,
      ((j.1 + 1 : ℕ) : AE D) * (incA D ((tau N k : ℚ) : D.host.E) * e) ∈ V := by
    rw [Filter.eventually_all]
    intro j
    have h := hz.const_mul ((j.1 + 1 : ℕ) : AE D)
    rw [mul_zero] at h
    exact h hV
  obtain ⟨k, hk⟩ := hall.exists
  refine ⟨fun j => ((j.1 + 1 : ℕ) : ℚ) * tau N k, fun i j hij => ?_, fun j => ?_⟩
  · have h := mul_right_cancel₀ (tau_pos hN k).ne' hij
    have h2 : i.1 + 1 = j.1 + 1 := by exact_mod_cast h
    exact Fin.ext (by omega)
  · have h := hk j
    have e1 : incA D (((((j.1 + 1 : ℕ) : ℚ) * tau N k : ℚ)) : D.host.E) =
        ((j.1 + 1 : ℕ) : AE D) * incA D ((tau N k : ℚ) : D.host.E) := by
      rw [Rat.cast_mul, map_mul, Rat.cast_natCast, map_natCast]
    show incA D (((((j.1 + 1 : ℕ) : ℚ) * tau N k : ℚ)) : D.host.E) * e ∈ V
    rw [e1, mul_assoc]
    exact h

end GlobalTheory.CompanionTheory.SmallRatCell

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RgTrans

private theorem mul_mul_mul_smul_eq_smul_mul_mul_mul {A : Type*} [CommRing A] {a b c d f : Type*} [Fintype b] [Fintype c]
    [Fintype d] (R : Matrix a b A) (P : Matrix b c A) (G : Matrix c d A) (X : Matrix d f A) (e : A) :
    R * (P * (G * (e • X))) = e • (R * (P * (G * X))) := by
  simp only [Matrix.mul_smul]

private theorem yv_smul_snd {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) (e : AE D)
    (w : Mx D V.rank r × Mx D V.rank t) :
    yv V b₀ (w.1, e • w.2) = e • yv V b₀ w :=
  mul_mul_mul_smul_eq_smul_mul_mul_mul _ _ _ _ e

theorem idemEx_trans : IdemEx → Trans := by
  intro hI D r t V b₀ hb₀ S e he
  have hee : e * e = e := ((hI D S).2 e he).1
  have hce : cA D e = e := ((hI D S).2 e he).2
  refine ⟨GlobalTheory.CompanionTheory.FreeFrames.isOpen_free D r t V.rank e hee
    (GlobalTheory.CompanionTheory.UnitNbhd.exists_open_mul_eq_idem GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps D S e he), ?_⟩
  intro z z' hz hz' hzc hz'c
  obtain ⟨Γ, hΓ, hN⟩ := GlobalTheory.CompanionTheory.FrameComplete.frame_completes D r t V b₀ hb₀ e hee hce
  obtain ⟨N, hNe, hNg, hN1, hN2⟩ := hN z hz hzc
  obtain ⟨N', hN'e, hN'g, hN'1, hN'2⟩ := hN z' hz' hz'c
  obtain ⟨h, hh, hhN⟩ := GlobalTheory.CompanionTheory.WittS.exists_unitary_off_S
    (GlobalTheory.CompanionTheory.SPartTensor.sPart GlobalTheory.CompanionTheory.AdeleComp.eq_zero_of_comps) D V S e he _ Γ hΓ N N'
    hNe hN'e hNg hN'g
  have hy : ∀ w : Mx D V.rank r × Mx D V.rank t, e • w.2 = w.2 → e • yv V b₀ w = yv V b₀ w := by
    intro w hw
    have key : yv V b₀ w = e • yv V b₀ w := by
      calc yv V b₀ w = yv V b₀ (w.1, e • w.2) := by rw [hw]
        _ = e • yv V b₀ w := yv_smul_snd V b₀ e w
    rw [key, smul_smul, hee]
  have h1 : mm (mt V h) z.1 = z'.1 := by
    ext i j
    rw [← hN'1, ← hhN]
    simp only [mm, Matrix.mul_apply, hN1]
  have h2 : mm (mt V h) (z.2 - mm z.1 (yv V b₀ z)) = z'.2 - mm z'.1 (yv V b₀ z') := by
    ext i j
    rw [← hN'2, ← hhN]
    simp only [mm, Matrix.mul_apply, hN2]
  refine ⟨h, yv V b₀ z' - yv V b₀ z, hh, ?_, ?_⟩
  · rw [smul_sub, hy z' hz'c.2.1, hy z hzc.2.1]
  · have h3 : mm (mt V h) (z.2 + mm z.1 (yv V b₀ z' - yv V b₀ z)) =
        mm (mt V h) (z.2 - mm z.1 (yv V b₀ z)) + mm (mm (mt V h) z.1) (yv V b₀ z') := by
      simp only [mm, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]
      abel
    refine Prod.ext h1.symm ?_
    rw [h3, h1, h2]
    simp only [mm, sub_add_cancel]

end GlobalTheory.CompanionTheory.RgTrans
end
