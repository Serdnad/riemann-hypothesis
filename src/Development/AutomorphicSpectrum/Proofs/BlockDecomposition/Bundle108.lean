module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelShift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle090
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle064
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle103
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle104
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.Connected
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

section

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.LinRedFactor

open GlobalTheory.LinRed

variable {n : ℕ}

theorem isCompact_unitary_fin :
    IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := _) hc ?_ ?_
  · have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
        {A | A * Aᴴ = 1} := by
      ext A; exact Matrix.mem_unitaryGroup_iff
    rw [this]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)
      continuous_const
  · intro A hA i _ j _
    simpa using entry_norm_bound_of_unitary hA i j

theorem unitary_mul_star {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : U * Uᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hU

theorem star_mul_unitary {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ * U = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 hU

theorem conj_mul_conj {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (s t : Matrix (Fin n) (Fin n) ℂ) :
    (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * (s * t) * U := by
  calc (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * s * (U * Uᴴ) * t * U := by
        simp only [Matrix.mul_assoc]
    _ = Uᴴ * (s * t) * U := by
        rw [unitary_mul_star hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem tri_mul {U s t : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hs : (Uᴴ * s * U).BlockTriangular id) (ht : (Uᴴ * t * U).BlockTriangular id) :
    (Uᴴ * (s * t) * U).BlockTriangular id := by
  rw [← conj_mul_conj hU]
  exact hs.mul ht

theorem isClosed_tri (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {s : Matrix (Fin n) (Fin n) ℂ | (Uᴴ * s * U).BlockTriangular id} := by
  simp only [Matrix.BlockTriangular, Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)
    continuous_const

theorem isCompact_maxCpt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) :
    IsCompact (maxCpt G) := by
  refine isCompact_unitary_fin.of_isClosed_subset ?_ Set.inter_subset_right
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxU : x ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    closure_minimal Set.inter_subset_right isCompact_unitary_fin.isClosed hx
  exact ⟨hG.closed x (IsUnit.of_mul_eq_one _ (unitary_mul_star hxU))
    (closure_mono Set.inter_subset_left hx), hxU⟩

def Good (G : Set (Matrix (Fin n) (Fin n) ℂ)) (U g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id

theorem good_nhds {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → Good G U g)
    {g₀ : Matrix (Fin n) (Fin n) ℂ} (h₀ : Good G U g₀) :
    ∀ᶠ g in 𝓝 g₀, g ∈ G → Good G U g := by
  obtain ⟨k₀, hk₀, s₀, hs₀, rfl, ht₀⟩ := h₀
  have hkk : k₀ * k₀ᴴ = 1 := unitary_mul_star hk₀.2
  have hkk' : k₀ᴴ * k₀ = 1 := star_mul_unitary hk₀.2
  have hsu : IsUnit s₀ := hG.isUnit s₀ hs₀
  have hss : s₀ * s₀⁻¹ = 1 := Matrix.mul_nonsing_inv s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hss' : s₀⁻¹ * s₀ = 1 := Matrix.nonsing_inv_mul s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hφ : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have e : k₀ᴴ * (k₀ * s₀) * s₀⁻¹ = 1 := by
    rw [← Matrix.mul_assoc, hkk', Matrix.one_mul, hss]
  have ht : Tendsto (fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹) (𝓝 (k₀ * s₀)) (𝓝 1) := by
    have := hφ.tendsto (k₀ * s₀)
    rwa [e] at this
  filter_upwards [ht.eventually h] with g hg hgG
  obtain ⟨k₁, hk₁, s₁, hs₁, e₁, t₁⟩ :=
    hg (hG.mul_mem _ (hG.mul_mem _ (hG.star_mem _ hk₀.1) _ hgG) _ (hG.inv_mem _ hs₀))
  refine ⟨k₀ * k₁, ⟨hG.mul_mem _ hk₀.1 _ hk₁.1, mul_mem hk₀.2 hk₁.2⟩, s₁ * s₀,
    hG.mul_mem _ hs₁ _ hs₀, ?_, tri_mul hU t₁ ht₀⟩
  calc g = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by
        calc g = (k₀ * k₀ᴴ) * g * (s₀⁻¹ * s₀) := by
              rw [hkk, hss', Matrix.one_mul, Matrix.mul_one]
          _ = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by simp only [Matrix.mul_assoc]
    _ = k₀ * k₁ * (s₁ * s₀) := by
        rw [e₁]; simp only [Matrix.mul_assoc]

theorem isClosed_factor {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ |
      ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
  haveI : CompactSpace (maxCpt G) := isCompact_iff_compactSpace.1 (isCompact_maxCpt hG)
  have hC : IsClosed {p : maxCpt G × Matrix (Fin n) (Fin n) ℂ |
      (Uᴴ * ((p.1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * p.2) * U).BlockTriangular id} :=
    (isClosed_tri U).preimage
      ((continuous_subtype_val.comp continuous_fst).matrix_conjTranspose.matrix_mul continuous_snd)
  have := isClosedMap_snd_of_compactSpace _ hC
  convert this using 1
  ext g
  constructor
  · rintro ⟨k, hk, t⟩
    exact ⟨(⟨k, hk⟩, g), t, rfl⟩
  · rintro ⟨⟨k, g'⟩, t, rfl⟩
    exact ⟨k.1, k.2, t⟩

theorem good_iff {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) :
    Good G U g ↔ ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id := by
  constructor
  · rintro ⟨k, hk, s, _, rfl, t⟩
    refine ⟨k, hk, ?_⟩
    rwa [← Matrix.mul_assoc kᴴ, star_mul_unitary hk.2, Matrix.one_mul]
  · rintro ⟨k, hk, t⟩
    refine ⟨k, hk, kᴴ * g, hG.mul_mem _ (hG.star_mem _ hk.1) _ hg, ?_, t⟩
    rw [← Matrix.mul_assoc, unitary_mul_star hk.2, Matrix.one_mul]

theorem factor_of_local : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
    (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G →
      ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) →
    ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  intro n G hG U hU h g hg
  haveI : PreconnectedSpace G := isPreconnected_iff_preconnectedSpace.1 hG.connected
  have hclosed : IsClosed {x : G | Good G U x.1} := by
    have e : {x : G | Good G U x.1} = Subtype.val ⁻¹' {g : Matrix (Fin n) (Fin n) ℂ |
        ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
      ext x
      exact good_iff hG x.2
    rw [e]
    exact (isClosed_factor hG U).preimage continuous_subtype_val
  have hopen : IsOpen {x : G | Good G U x.1} := by
    rw [isOpen_iff_eventually]
    intro x hx
    have := (continuous_subtype_val.tendsto x).eventually (good_nhds hG hU h hx)
    filter_upwards [this] with y hy using hy y.2
  have hone : Good G U 1 := by
    refine ⟨1, ⟨hG.one_mem, one_mem _⟩, 1, hG.one_mem, by simp, ?_⟩
    rw [Matrix.mul_one, star_mul_unitary hU]
    exact Matrix.blockTriangular_one
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨1, hG.one_mem⟩, hone⟩
  have hmem : (⟨g, hg⟩ : G) ∈ {x : G | Good G U x.1} := huniv ▸ Set.mem_univ _
  exact hmem

end GlobalTheory.CompanionTheory.LinRedFactor
end

section

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

theorem isClosed_range_blk (e : Fin a × ι ≃ Fin n) : IsClosed {g | blk e (unblk e g) = g} :=
  isClosed_eq ((continuous_blk e).comp (continuous_unblk e)) continuous_id

theorem blk_unblk_of_mem_closure (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ closure (blkG e)) : blk e (unblk e g) = g :=
  (closure_minimal (fun _ h => ((mem_blkG_iff e).1 h).2) (isClosed_range_blk e)) hg

theorem finite_setOf_det_line_eq_zero {A B : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) :
    {z : ℂ | ((1 - z) • A + z • B).det = 0}.Finite := by
  let P : Polynomial ℂ := Matrix.det ((1 - Polynomial.X : Polynomial ℂ) • A.map Polynomial.C
    + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)
  have hev : ∀ z : ℂ, P.eval z = ((1 - z) • A + z • B).det := by
    intro z
    have := RingHom.map_det (Polynomial.evalRingHom z) ((1 - Polynomial.X : Polynomial ℂ) • A.map Polynomial.C
      + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)
    simp only [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  have hP : P ≠ 0 := by
    intro h
    have := hev 0
    rw [h] at this
    simp only [Polynomial.eval_zero, sub_zero, one_smul, zero_smul, add_zero] at this
    exact ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero this.symm
  refine (P.rootSet_finite ℂ).subset ?_
  intro z hz
  rw [Polynomial.mem_rootSet]
  refine ⟨hP, ?_⟩
  simpa [hev] using hz

theorem isPreconnected_blkG (e : Fin a × ι ≃ Fin n) : IsPreconnected (blkG e) := by
  refine isPreconnected_of_forall_pair ?_
  rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
  have hA : IsUnit (blk e M) := (isUnit_blk_iff e M).2 hM
  have hB : IsUnit (blk e N) := (isUnit_blk_iff e N).2 hN
  set A := blk e M
  set B := blk e N
  let Z : Set ℂ := {z | ((1 - z) • A + z • B).det = 0}
  have hZ : Z.Finite := finite_setOf_det_line_eq_zero hA
  have hconn : IsPathConnected Zᶜ := hZ.countable.isPathConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]; norm_num)
  let γ : ℂ → Matrix (Fin n) (Fin n) ℂ := fun z => (1 - z) • A + z • B
  have hγ : Continuous γ := by fun_prop
  refine ⟨γ '' Zᶜ, ?_, ⟨0, ?_, by simp [γ]⟩, ⟨1, ?_, by simp [γ]⟩, hconn.isConnected.isPreconnected.image _ hγ.continuousOn⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine (mem_blkG_iff e).2 ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hz), ?_⟩
    have : γ z = blk e ((1 - z) • M + z • N) := by simp [γ, A, B]
    rw [this, unblk_blk]
  · simpa [Z] using ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
  · simpa [Z] using ((Matrix.isUnit_iff_isUnit_det B).1 hB).ne_zero

theorem blk_inv (e : Fin a × ι ≃ Fin n) {M : Matrix (Fin a) (Fin a) (ι → ℂ)} (hM : IsUnit M) :
    (blk e M)⁻¹ = blk e M⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← blk_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM), blk_one]

theorem isLinRed_blkG (e : Fin a × ι ≃ Fin n) : GlobalTheory.LinRed.IsLinRed (blkG e) := by
  refine
    { one_mem := ⟨1, isUnit_one, blk_one e⟩
      mul_mem := ?_
      isUnit := fun g hg => ((mem_blkG_iff e).1 hg).1
      inv_mem := ?_
      closed := fun g hg hcl => (mem_blkG_iff e).2 ⟨hg, blk_unblk_of_mem_closure e hcl⟩
      connected := isPreconnected_blkG e
      star_mem := ?_ }
  · rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
    exact ⟨M * N, IsUnit.mul hM hN, blk_mul e M N⟩
  · rintro _ ⟨M, hM, rfl⟩
    refine ⟨M⁻¹, ?_, (blk_inv e hM).symm⟩
    exact (Matrix.isUnit_nonsing_inv_iff).2 hM
  · rintro _ ⟨M, hM, rfl⟩
    refine ⟨Mᴴ, ?_, blk_conjTranspose e M⟩
    have : IsUnit (star M) := IsUnit.star hM
    exact this

end GlobalTheory.CompanionTheory.AdmGL

end
end

section

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem continuous_detW (n : ℕ) : Continuous (fun b : Matrix (Fin n) (Fin n) ℂ => detW b) := by
  unfold detW
  exact Complex.continuous_re.comp (Continuous.matrix_det (by fun_prop))

theorem measurable_term (n : ℕ) (s : ℝ) :
    Measurable (fun b : hermC n => ENNReal.ofReal (detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s))) := by
  have h : Continuous (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ)) :=
    (continuous_detW n).comp continuous_subtype_val
  exact (h.measurable.pow_const _).ennreal_ofReal

theorem inner_eq (n : ℕ) (s : ℝ) (hs : (n : ℝ) + 1 / 2 < s) : ∃ K : ENNReal, K ≠ ⊤ ∧
    ∀ b' : hermC n, ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) =
      K * ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1))) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.lintegral_power_line_scaling s (by linarith)
  have hL := GlobalTheory.T.lintegral_complex_power_finite n (2 * s - 1) (by linarith)
  set L := ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1))) with hLdef
  refine ⟨C * L, ENNReal.mul_ne_top hC hL, fun b' => ?_⟩
  have hB : (b' : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b'.2
  have hw1 := GlobalTheory.T.one_le_detW_of_isHermitian n _ hB
  have hwA := GlobalTheory.T.detW_eq_normSq_det_one_add_I n _ hB
  have hdet : Matrix.det (1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) ≠ 0 := by
    intro h0
    rw [h0] at hwA
    simp at hwA
    linarith
  have hgm : Measurable (fun u : Fin n → ℂ => ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))) := by
    apply Measurable.lintegral_prod_right'
      (f := fun p : (Fin n → ℂ) × ℝ => ENNReal.ofReal (detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)))
    have hc : Continuous (fun p : (Fin n → ℂ) × ℝ => detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
      (continuous_detW _).comp (continuous_blkM.comp
        (by fun_prop : Continuous fun p : (Fin n → ℂ) × ℝ => ((b' : Matrix (Fin n) (Fin n) ℂ), p.1, p.2)))
    exact (hc.measurable.pow_const _).ennreal_ofReal
  rw [GlobalTheory.T.lintegral_linear_change_variables_complex n _ hdet _ hgm, ← hwA]
  have hv : ∀ v : Fin n → ℂ, ∫⁻ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
        (C * ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1)))) := by
    intro v
    have hr : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hterm : ∀ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
        = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
          ENNReal.ofReal (((1 + ∑ i, Complex.normSq (v i)) ^ 2 +
            (d - (star v ⬝ᵥ ((b' : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)).re) ^ 2) ^ (-s)) := by
      intro d
      have hh := mem_hermC.1 (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d).2
      rw [GlobalTheory.T.detW_eq_normSq_det_one_add_I _ _ hh]
      have e : ((blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : hermC (n+1)) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
          = blkM (b' : Matrix (Fin n) (Fin n) ℂ) ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d := rfl
      rw [e, GlobalTheory.T.detW_block_matrix_formula n _ hB hdet v d, ← hwA, Real.mul_rpow (by linarith) (by positivity),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
    simp only [hterm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hD (1 + ∑ i, Complex.normSq (v i)) (by linarith)]
    congr 3
    ring_nf
  simp only [hv]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ hC]
  have e2 : ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ)) *
        ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    rw [show -(s - 1) = 1 + -s by ring, Real.rpow_add (by linarith), Real.rpow_one]
  rw [e2]
  ring

theorem hua_integrable : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro n
  induction n with
  | zero =>
    intro s _ ν hν
    have : IsFiniteMeasure ν := by
      haveI : Finite (hermC 0) := by
        haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := inferInstance
        exact Finite.of_subsingleton
      haveI : CompactSpace (hermC 0) := Finite.compactSpace
      exact ⟨isCompact_univ.measure_lt_top⟩
    have h1 : ∀ b : hermC 0, detW (b : Matrix (Fin 0) (Fin 0) ℂ) ^ (-s) = 1 := by
      intro b
      simp [detW]
    simp only [h1]
    exact integrable_const _
  | succ n ih =>
    intro s hs ν hν
    have hs' : (n : ℝ) + 1 / 2 < s := by push_cast at hs; linarith
    have hpos : ∀ b : hermC (n + 1), 0 ≤ detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have hmeas := measurable_term (n + 1) s
    have hm2 : Measurable (fun b : hermC (n + 1) => detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) :=
      (((continuous_detW (n + 1)).comp continuous_subtype_val).measurable.pow_const _)
    refine ⟨hm2.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
    obtain ⟨c, hc, hF⟩ := GlobalTheory.T.hermitian_haar_block_decomposition n ν (Measure.addHaar) hν inferInstance
    obtain ⟨K, hK, hI⟩ := inner_eq n s hs'
    rw [hF _ hmeas]
    simp only [hI]
    rw [lintegral_const_mul _ (measurable_term n (s - 1))]
    have h3 := ih (s - 1) (by linarith) Measure.addHaar inferInstance
    have hp3 : ∀ b : hermC n, 0 ≤ detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have h4 := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hp3)).1 h3.2
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) h4)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.average_over_maximal_compact_residue : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ f : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ,
      avgK ϖ (fun κ => f (resK κ)) = sumG f / (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res | exact GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res | (intros; apply GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.gauss_sum_hermitian_norm_level_shift : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ (j + 2), ψ (j + 2) (Ideal.Quotient.mk (lev ϖ (j + 2)) a * (barσ σ ϖ hR.fix_ϖ (j + 2) w * w))) = (q : ℂ) ^ 2 * ∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w)) := by
  first | exact @GlobalTheory.CompanionTheory.GaussRec.gauss_recursion | exact GlobalTheory.CompanionTheory.GaussRec.gauss_recursion | (intros; apply GlobalTheory.CompanionTheory.GaussRec.gauss_recursion <;> assumption)
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem inv_bounded_on_tube : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T]
    (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ C : Set (ℝ × ℝ), IsCompact C →
    ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ tube C, ∀ g' ∈ U, ‖inv (fun t => φ t g') l‖ ≤ M := by
  intro X _ _ T _ φ hφ hc C hC g
  choose ε hε U hU M hM using fun x₀ : ℝ × ℝ => hφ x₀ g
  have hnhds : ∀ x ∈ C, {y : ℝ × ℝ | |y.1 - x.1| < ε x ∧ |y.2 - x.2| < ε x} ∈ 𝓝 x := by
    intro x _
    have h1 : Continuous fun y : ℝ × ℝ => |y.1 - x.1| := by fun_prop
    have h2 : Continuous fun y : ℝ × ℝ => |y.2 - x.2| := by fun_prop
    refine ((isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)).mem_nhds ?_
    simpa using hε x
  obtain ⟨s, -, hcov⟩ := hC.elim_nhds_subcover _ hnhds
  refine ⟨⋂ x ∈ s, U x, (Filter.biInter_finset_mem s).2 fun x _ => hU x,
    ‖(((2 * Real.pi) ^ 2 : ℂ)⁻¹)‖ * ∑ x ∈ s, |M x| * (2 / ε x) ^ 2, ?_⟩
  intro l hl g' hg'
  have hlC : ((l.1.re, l.2.re) : ℝ × ℝ) ∈ C := hl
  obtain ⟨x₀, hx₀, h1, h2⟩ := Set.mem_iUnion₂.1 (hcov hlC)
  have hgU : g' ∈ U x₀ := Set.mem_iInter₂.1 hg' x₀ hx₀
  have hb := (GlobalTheory.T.exponential_fourier_integral_bound X (fun t => φ t g') l (ε x₀) (M x₀) (hε x₀) (hc g')
    fun t => hM x₀ (l.1.re, l.2.re) h1.le h2.le g' hgU t).2
  have hterm : M x₀ * (2 / ε x₀) ^ 2 ≤ |M x₀| * (2 / ε x₀) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have hsum : |M x₀| * (2 / ε x₀) ^ 2 ≤ ∑ x ∈ s, |M x| * (2 / ε x) ^ 2 :=
    Finset.single_le_sum (f := fun x => |M x| * (2 / ε x) ^ 2)
      (fun x _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hx₀
  simp only [inv]
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hb.trans (hterm.trans hsum)) (norm_nonneg _)

end GlobalTheory.CompanionTheory.TubeFourier
end
