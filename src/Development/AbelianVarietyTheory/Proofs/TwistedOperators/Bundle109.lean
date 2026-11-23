module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle102
public import Mathlib.Analysis.Matrix.Normed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle105
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle106
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle100
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

section

open Classical MeasureTheory

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame.RatProj

section Form

variable {σ : Type}

def fockQ (f g : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ)

theorem fockQ_eq_sum (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ) := by
  refine Finset.sum_subset hs ?_
  intro m _ hm
  rw [notMem_support_iff.mp hm]
  simp

def fockQL : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ fockQ
    (by
      intro f f' g
      rw [fockQ_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
        fockQ_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
        fockQ_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.coeff_add]; ring)
    (by
      intro c f g
      rw [fockQ_eq_sum (c • f) g f.support support_smul, fockQ, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring)
    (by
      intro f g g'
      simp only [fockQ, MvPolynomial.coeff_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c f g
      simp only [fockQ, MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring)

theorem fockQL_apply (f g : MvPolynomial σ ℚ) : fockQL f g = fockQ f g := rfl

theorem fockS_map (f g : MvPolynomial σ ℚ) :
    Formalism.L2.DIV.fockS (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = (fockQ f g : ℂ) := by
  rw [Formalism.L2.DIV.fockS_eq_sum _ _ f.support (support_map_subset _ _), fockQ]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem eq_zero_of_fockQ_self {f : MvPolynomial σ ℚ} (h : fockQ f f = 0) : f = 0 := by
  by_contra hf
  have hf' : map (algebraMap ℚ ℂ) f ≠ 0 := by
    intro h0
    apply hf
    exact map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])
  have := GlobalTheory.MinorFrame.fockS_self_re_pos hf'
  rw [fockS_map, h] at this
  simp at this

end Form

variable {ι : Type} [Fintype ι]

def prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : MvPolynomial (Var ι d a) ℚ :=
  ∏ τ, ∏ j, (Matrix.of fun i i' : Fin a => (X (τ, (T τ j).1 i, i') : MvPolynomial (Var ι d a) ℚ)).det

theorem map_prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) :
    map (algebraMap ℚ ℂ) (prodMinorsQ T) = prodMinors T := by
  simp only [prodMinorsQ, prodMinors, minorAt, map_prod]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i i'
  simp

theorem exists_rat_proj : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  intro ι _ a d n k
  let PQ : Tup ι a d n → MvPolynomial (Var ι d a) ℚ := fun T => prodMinorsQ T
  let W := Submodule.span ℚ (Set.range PQ)
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range PQ)
  let ψ : W →ₗ[ℚ] Module.Dual ℚ W := (fockQL (σ := Var ι d a)).flip.compl₁₂ W.subtype W.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have h1 : ψ w w = 0 := by rw [LinearMap.mem_ker.mp hw]; rfl
    have h2 : fockQ (w : MvPolynomial (Var ι d a) ℚ) w = 0 := h1
    exact Subtype.ext (eq_zero_of_fockQ_self h2)
  have hsurj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w₀, hw₀⟩ := hsurj ((fockQL.flip (monomial k (1 : ℚ))).comp W.subtype)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 w₀.2
  let e : Fin (Fintype.card (Tup ι a d n)) ≃ Tup ι a d n := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Tup ι a d n), fun p => c (e p), fun p => e p, fun T => ?_⟩
  have hsum : (∑ p, ((c (e p) : ℚ) : ℂ) • prodMinors (e p)) =
      map (algebraMap ℚ ℂ) (w₀ : MvPolynomial (Var ι d a) ℚ) := by

    rw [e.sum_comp (fun T => ((c T : ℚ) : ℂ) • prodMinors T), ← hc, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [PQ]
    rw [smul_eq_C_mul (prodMinorsQ T) (c T), map_mul, map_C, map_prodMinorsQ, smul_eq_C_mul]
    simp
  have hmon : (monomial k (1 : ℂ)) = map (algebraMap ℚ ℂ) (monomial k (1 : ℚ)) := by simp [map_monomial]
  rw [hsum, ← map_prodMinorsQ T, hmon, ← map_sub, fockS_map, ← fockQL_apply, map_sub]
  have h3 := LinearMap.congr_fun hw₀ ⟨PQ T, Submodule.subset_span ⟨T, rfl⟩⟩
  have h4 : fockQL (PQ T) (w₀ : MvPolynomial (Var ι d a) ℚ) = fockQL (PQ T) (monomial k 1) := h3
  simp only [PQ] at h4
  rw [h4, sub_self, Rat.cast_zero]

end GlobalTheory.MinorFrame.RatProj
end
end

section

open Classical MeasureTheory

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

variable {ι : Type} [Fintype ι]

def scalAt {a : ℕ} (τ₀ : ι) (ζ : ℂ) : ι → Matrix (Fin a) (Fin a) ℂ := fun τ => if τ = τ₀ then ζ • 1 else 1

def degAt {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : ℕ := t.sum fun y n => if y.1 = τ₀ then n else 0

theorem colSub_scalAt_X {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (y : Var ι d a) :
    (∑ j' : Fin a, C (scalAt τ₀ ζ y.1 j' y.2.2) * (X (y.1, y.2.1, j') : Pol ι d a)) =
      C (if y.1 = τ₀ then ζ else 1) * X y := by
  obtain ⟨τ, i, j⟩ := y
  by_cases h : τ = τ₀
  · subst h
    rw [Finset.sum_eq_single j]
    · simp [scalAt, Matrix.smul_apply, Matrix.one_apply]
    · intro b _ hb
      simp [scalAt, Matrix.smul_apply, Matrix.one_apply, hb]
    · simp
  · simp [scalAt, h, Matrix.one_apply]

theorem colSub_scalAt_monomial {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (t : Var ι d a →₀ ℕ) (c : ℂ) :
    colSub (scalAt τ₀ ζ) (monomial t c : Pol ι d a) = monomial t (c * ζ ^ degAt τ₀ t) := by
  unfold colSub
  rw [aeval_monomial]
  simp only [colSub_scalAt_X, mul_pow, Finsupp.prod_mul]
  have h1 : (t.prod fun y k => (C (if y.1 = τ₀ then ζ else 1) : Pol ι d a) ^ k) = C (ζ ^ degAt τ₀ t) := by
    unfold Finsupp.prod degAt Finsupp.sum
    rw [← Finset.prod_pow_eq_pow_sum, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    beta_reduce
    split_ifs <;> simp
  rw [h1, ← monomial_eq, algebraMap_eq, C_mul_monomial]

theorem degAt_le {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : degAt τ₀ t ≤ t.sum fun _ e => e := by
  unfold degAt Finsupp.sum
  exact Finset.sum_le_sum fun y _ => by beta_reduce; split_ifs <;> omega

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

variable {ι : Type} [Fintype ι]

theorem colSub_mul {d a : ℕ} (A B : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colSub (fun τ => A τ * B τ) P = colSub A (colSub B P) := by
  have : (colSub (fun τ => A τ * B τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) = (colSub A).comp (colSub B) := by
    apply MvPolynomial.algHom_ext
    intro y

    simp only [AlgHom.comp_apply, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
    Finset.mul_sum, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this

theorem sum_scalAt_eq_zero {d a : ℕ} (τ₀ : ι) (N : ℕ) (hN : 0 < N) (P : Pol ι d a) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (N + P.totalDegree + 1)) :
    ∑ k ∈ Finset.range (N + P.totalDegree + 1), (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P = 0 := by
  generalize hM : N + P.totalDegree + 1 = M at hω ⊢
  conv_lhs => rw [as_sum P]

  simp only [map_sum, colSub_scalAt_monomial, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t ht => ?_
  have hsum : ∑ k ∈ Finset.range M, (ω ^ (N + degAt τ₀ t)) ^ k = 0 := by
    have hne : ω ^ (N + degAt τ₀ t) ≠ 1 := by
      rw [Ne, hω.pow_eq_one_iff_dvd]
      intro hdvd
      have h1 := degAt_le τ₀ t
      have h2 := le_totalDegree ht
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self, zero_div]
  have : ∀ k ∈ Finset.range M,
      (ω ^ k) ^ N • (monomial t (AddMonoidAlgebra.coeff P t * (ω ^ k) ^ degAt τ₀ t) : Pol ι d a) =
        monomial t (AddMonoidAlgebra.coeff P t * (ω ^ (N + degAt τ₀ t)) ^ k) := by
    intro k _
    rw [smul_monomial, smul_eq_mul]
    congr 1
    rw [← pow_mul, ← pow_mul, ← pow_mul, show (N + degAt τ₀ t) * k = k * N + k * degAt τ₀ t by ring, pow_add]
    ring

  rw [Finset.sum_congr rfl this, ← map_sum, ← Finset.mul_sum, hsum, mul_zero, map_zero]

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial

theorem prod_det_scalAt_zpow {ι : Type} [Fintype ι] {a : ℕ} (τ₀ : ι) (ζ : ℂ) (m : ι → ℤ) (n : ℕ)
    (hn : (n : ℤ) = m τ₀) : (∏ τ, (scalAt (a := a) τ₀ ζ τ).det ^ (m τ)) = ζ ^ (a * n) := by
  rw [Finset.prod_eq_single τ₀]
  · simp [scalAt, Matrix.det_smul, ← hn, zpow_natCast, pow_mul]
  · intro τ _ h
    simp [scalAt, h]
  · simp

theorem integral_detZpow_colSub_eq_zero :
    ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K]
      [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
    (∀ u : K, AEMeasurable (fun x => u * x) ν) →
    ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)),
      (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
      Function.Surjective ρ →
    ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
        Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  intro ι _ a d m τ₀ ha hm K _ _ ν hν hinv hmeas ρ _ hρ Λ P
  set B : K → ι → Matrix (Fin a) (Fin a) ℂ := fun g τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) with hB_def
  set c : K → ℂ := fun g => ∏ τ, (B g τ).det ^ (m τ) with hc_def
  set f : K → ℂ := fun g => c g * Λ (colSub (B g) P) with hf_def
  show ∫ g, f g ∂ν = 0
  by_cases hint : Integrable f ν
  swap
  · exact integral_undef hint

  have hinvar : ∀ u : K, Integrable (fun x => f (u * x)) ν ∧ ∫ x, f (u * x) ∂ν = ∫ x, f x ∂ν := by
    intro u
    have hmap : Measure.map (fun x => u * x) ν = ν := map_mul_left_eq_self ν u
    have hae : AEMeasurable (fun x => u * x) ν := hmeas u
    refine ⟨?_, ?_⟩
    · have : Integrable f (Measure.map (fun x => u * x) ν) := by rw [hmap]; exact hint
      exact this.comp_aemeasurable hae
    · have h := integral_map hae (f := f) (by rw [hmap]; exact hint.aestronglyMeasurable)
      rw [hmap] at h
      exact h.symm

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m τ₀ := ⟨(m τ₀).toNat, Int.toNat_of_nonneg hm.le⟩
  have hnpos : 0 < n := by omega
  set N := a * n with hN_def
  have hN : 0 < N := Nat.mul_pos ha hnpos
  set M := N + P.totalDegree + 1 with hM_def
  have hM0 : M ≠ 0 := by omega
  set ω := Complex.exp (2 * Real.pi * Complex.I / M) with hω_def
  have hω : IsPrimitiveRoot ω M := Complex.isPrimitiveRoot_exp M hM0
  have hmemU : ∀ k : ℕ, ((ω ^ k) • (1 : Matrix (Fin a) (Fin a) ℂ)) ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    intro k
    have hnorm : ‖ω ^ k‖ = 1 := by rw [norm_pow, hω.norm'_eq_one hM0, one_pow]
    have hc : ω ^ k * star (ω ^ k) = 1 := by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      hc, one_smul]
  let U : ℕ → ι → Matrix.unitaryGroup (Fin a) ℂ := fun k τ => if τ = τ₀ then ⟨(ω ^ k) • 1, hmemU k⟩ else 1
  have hU : ∀ k τ, (U k τ : Matrix (Fin a) (Fin a) ℂ) = scalAt τ₀ (ω ^ k) τ := by
    intro k τ
    simp only [U, scalAt]
    split_ifs <;> rfl
  choose u hu using fun k => hρ (U k)

  have hpt : ∀ k g, f (u k * g) = c g * Λ ((ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P)) := by
    intro k g
    have hBu : B (u k * g) = fun τ => B g τ * scalAt τ₀ (ω ^ k) τ := by
      funext τ
      simp only [hB_def, map_mul, Pi.mul_apply, hu k]
      rw [Submonoid.coe_mul, hU k τ]
      simp only [scalAt]
      split_ifs <;> simp [Matrix.smul_mul, Matrix.mul_smul]
    simp only [hf_def, hc_def]
    rw [hBu, colSub_mul, map_smul, smul_eq_mul]
    simp only [Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
    rw [prod_det_scalAt_zpow τ₀ (ω ^ k) m n hn]
    ring
  have hsum0 : ∀ g, ∑ k ∈ Finset.range M, f (u k * g) = 0 := by
    intro g

    simp only [hpt, ← Finset.mul_sum, ← map_sum]
    have : ∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (B g) (colSub (scalAt τ₀ (ω ^ k)) P) =
        colSub (B g) (∑ k ∈ Finset.range M, (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P) := by

      rw [map_sum]; simp only [map_smul]
    rw [this, sum_scalAt_eq_zero τ₀ N hN P hω, map_zero, map_zero, mul_zero]
  have hkey : (M : ℂ) * ∫ x, f x ∂ν = 0 := by
    calc (M : ℂ) * ∫ x, f x ∂ν = ∑ k ∈ Finset.range M, ∫ x, f (u k * x) ∂ν := by
          rw [Finset.sum_congr rfl fun k _ => (hinvar (u k)).2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∫ x, ∑ k ∈ Finset.range M, f (u k * x) ∂ν :=
          (MeasureTheory.integral_finsetSum _ fun k _ => (hinvar (u k)).1).symm
      _ = 0 := by simp [hsum0]
  exact (mul_eq_zero.1 hkey).resolve_left (by exact_mod_cast hM0)

end GlobalTheory.MinorFrame
end
end
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_continuousOn_polar_log' : ∀ (p q : ℕ), ∃ L : Mat p q → (Fin p → Fin q → ℂ), ContinuousOn L {g | IsUnit g} ∧ ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B := by
  first | exact @GlobalTheory.PolarLogCont.exists_continuousOn_polar_log | exact GlobalTheory.PolarLogCont.exists_continuousOn_polar_log | (intros; apply GlobalTheory.PolarLogCont.exists_continuousOn_polar_log <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.hasStrictFDerivAt_exp_two_upperRightBlockElementP : ∀ (p q : ℕ) (B : Fin p → Fin q → ℂ), (∀ (V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • V) a b) ((NormedSpace.exp (pY B) * sAd (pY B) V * NormedSpace.exp (pY B)) a b) 0) → ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B) := by
  first | exact @GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY | exact GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY | (intros; apply GlobalTheory.PolarU.hasStrictFDerivAt_exp_two_pY <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem adMat_real_smul {p q : ℕ} (u : ℝ) (Y : Mat p q) : adMat (u • Y) = u • adMat Y := by
  ext i j
  simp only [adMat, Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, smul_sub]
  congr 1
  · rw [smul_mul_assoc]
  · rw [mul_smul_comm]

def sandwichAct {p q : ℕ} (P V Q : Mat p q) :
    Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →ₗ[ℝ] Mat p q where
  toFun M := P * (Matrix.of fun a b => (M *ᵥ vecM V) (a, b)) * Q
  map_add' M N := by
    rw [← add_mul, ← mul_add]
    congr 2
    ext a b; simp [Matrix.add_mulVec]
  map_smul' t M := by
    rw [RingHom.id_apply, ← smul_mul_assoc, ← mul_smul_comm]
    congr 2
    ext a b; simp [Matrix.smul_mulVec]

theorem exp_real_smul_add {p q : ℕ} (Y : Mat p q) (u v : ℝ) :
    NormedSpace.exp ((u + v) • Y) = NormedSpace.exp (u • Y) * NormedSpace.exp (v • Y) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left u).smul_right v)

theorem duhamel_integrand_eq {p q : ℕ} (Y V : Mat p q) (s : ℝ) :
    NormedSpace.exp ((1 - s) • (Y + Y)) * V * NormedSpace.exp (s • (Y + Y)) =
      sandwichAct (NormedSpace.exp Y) V (NormedSpace.exp Y)
        (NormedSpace.exp ((1 - 2 * s) • adMat Y)) := by
  have hl : (1 - s) • (Y + Y) = ((1 : ℝ) + (1 - 2 * s)) • Y := by
    rw [← two_smul ℝ Y, smul_smul]; congr 1; ring
  have hr : s • (Y + Y) = (-(1 - 2 * s) + (1 : ℝ)) • Y := by
    rw [← two_smul ℝ Y, smul_smul]; congr 1; ring
  have hof : ∀ W : Mat p q, (Matrix.of fun a b => vecM W (a, b)) = W := fun W => by
    ext a b; rfl
  rw [hl, hr, exp_real_smul_add, exp_real_smul_add, one_smul, neg_smul]
  simp only [sandwichAct, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← adMat_real_smul, exp_adMat_mulVec, hof]
  simp only [Matrix.mul_assoc]

open scoped Matrix.Norms.Operator in
theorem integral_duhamel_eq_sAd {p q : ℕ} (Y V : Mat p q) :
    ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • (Y + Y)) * V * NormedSpace.exp (s • (Y + Y)) =
      NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y := by
  let L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →L[ℝ] Mat p q :=
    LinearMap.toContinuousLinearMap (sandwichAct (NormedSpace.exp Y) V (NormedSpace.exp Y))
  have hcont : Continuous fun s : ℝ => NormedSpace.exp ((1 - 2 * s) • adMat Y) :=
    NormedSpace.exp_continuous.comp ((by fun_prop : Continuous fun s : ℝ => 1 - 2 * s).smul
      continuous_const)
  have hsin : sinhcAd Y =
      ∑' k : ℕ, (((2 * k + 1).factorial : ℝ)⁻¹) • adMat Y ^ (2 * k) := by
    simp only [sinhcAd]
    congr 1
    funext k
    rw [← Complex.coe_smul]
    push_cast
    rfl
  calc ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • (Y + Y)) * V * NormedSpace.exp (s • (Y + Y))
      = ∫ s in (0 : ℝ)..1, L (NormedSpace.exp ((1 - 2 * s) • adMat Y)) := by
        congr 1
        funext s
        exact duhamel_integrand_eq Y V s
    _ = L (∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • adMat Y)) :=
        L.intervalIntegral_comp_comm (hcont.intervalIntegrable 0 1)
    _ = NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y := by
        have hI : ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • adMat Y) = sinhcAd Y := by
          rw [hsin]
          exact integral_exp_one_sub_two_mul_smul _ (adMat Y)
        rw [hI]
        rfl

theorem hasDerivAt_exp_two_add_smul (p q : ℕ) (Y V : Mat p q) (a b : Ix p q) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + Y + t • V) a b)
      ((NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y) a b) 0 := by
  letI : NormedRing (Mat p q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat p q) := Matrix.linftyOpNormedAlgebra
  have hD0 := GlobalTheory.hasDerivAt_exp_add_smul_duhamel (Mat p q) (Y + Y) V
  have hD : HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + Y + t • V))
      (NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y) 0 := by
    rw [← integral_duhamel_eq_sAd Y V]
    exact hD0
  let e : Mat p q →ₗ[ℝ] ℂ :=
    { toFun := fun M => M a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap e).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD

end GlobalTheory.PolarU
end
end
