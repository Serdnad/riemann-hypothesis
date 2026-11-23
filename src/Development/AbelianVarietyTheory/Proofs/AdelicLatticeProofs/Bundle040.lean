module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsConjHarmOfSpan
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealTranslateIsMinNormTensorInOrbit
public import Mathlib.Order.Filter.Cofinite
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle032
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.TensorProduct.Free
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.minNormTensor_stabilizer_conjTranspose_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsMinVec d v → ∀ g : Matrix ι ι ℂ, g.det = 1 → act d v g = v → act d v gᴴ = v := by
  first | exact @GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec | exact GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec | (intros; apply GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_siegel_decomposition_mul_int_matrix_of_det_eq_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι], ∃ C : ℝ, ∀ g : Matrix ι ι ℝ, g.det = 1 → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ ∃ k a n, IsSiegel C k a n ∧ g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  first | exact @GlobalTheory.ClassFin.siegel_cover | exact GlobalTheory.ClassFin.siegel_cover | (intros; apply GlobalTheory.ClassFin.siegel_cover <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.two_mul_card_places_le_card_over_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → 2 * S.card ≤ SE.card + tFin F δ S := by
  first | exact @GlobalTheory.QNorm.two_mul_card_le_card_over | exact GlobalTheory.QNorm.two_mul_card_le_card_over | (intros; apply GlobalTheory.QNorm.two_mul_card_le_card_over <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem ev_map_complexAut {ι : Type} (f : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι ℂ) (σ : ℂ ≃+* ℂ) : ev f (g.map σ) = σ (ev f g) := by
  unfold ev
  have h := MvPolynomial.comp_aeval (f := fun ij : ι × ι => g ij.1 ij.2) (σ.toRingHom.toRatAlgHom)
  have h2 := DFunLike.congr_fun h f
  simp only [AlgHom.comp_apply, RingHom.toRatAlgHom_apply] at h2
  exact h2.symm

theorem exists_isQGroup_weilRestriction : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ Γ : Set (Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) ℂ), IsQGroup Γ ∧ ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → (∀ y ∈ pts Γ R, ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) ∧ y = emb b g) ∧ (IsReduced R → ∀ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (A)) : Matrix (Fin n) (Fin n) (A)) ij.1 ij.2) P = 0) → emb b g ∈ pts Γ R) := by
  intro F β _ _ _ _ ω n S hS
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_rational_equations_weil_restriction F β ω n S
  letI : Algebra F (ℂ ⊗[ℚ] F) := Algebra.TensorProduct.rightAlgebra
  have hb : ∀ i, Algebra.TensorProduct.basis ℂ ω i = algebraMap F (ℂ ⊗[ℚ] F) (ω i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have hC := hS' ℂ (ℂ ⊗[ℚ] F) (Algebra.TensorProduct.basis ℂ ω) hb
  obtain ⟨h1, hm, hi⟩ := hS (ℂ ⊗[ℚ] F)
  obtain ⟨e1, em, ed, -⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom ℂ (ℂ ⊗[ℚ] F) β (Fin n) (Algebra.TensorProduct.basis ℂ ω)
  refine ⟨{g | ∀ f ∈ S', ev f g = 0}, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact (hC 1).2 ⟨1, h1, e1.symm⟩
  · intro g hg h hh
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    obtain ⟨h', hh', rfl⟩ := (hC h).1 hh
    exact (hC _).2 ⟨g' * h', hm g' h' hg' hh', (em g' h').symm⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (hC _).2 ⟨g'⁻¹, hi g' hg', (ed g').2⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := (hC g).1 hg
    exact (ed g').1
  · intro σ g hg f hf
    rw [ev_map_complexAut, hg f hf, map_zero]
  · intro y hy
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' ℂ y).1 hy
  · intro R A _ _ _ _ _ b hbb
    refine ⟨fun y hy => (hS' R A b hbb y).1 ((GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R y).1 hy), fun hR g hg => ?_⟩
    exact (GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced _ S' R _).2 hR ((hS' R A b hbb _).2 ⟨g, hg, rfl⟩)

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_multiplier_descend_blockDiagPartOfRatIdempotent : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), pts Γ ℂ ⊆ Γ → Γ.Nonempty → ∀ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ f ∈ s, ∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → evC f x = evC f x') → ∃ b : MvPolynomial (ι × ι) ℂ, (∃ x ∈ Γ, evC b (blk e x) ≠ 0) ∧ ∀ f ∈ s, ∃ b' : MvPolynomial (ι × ι) ℂ, ∀ x ∈ Γ, evC b (blk e x) * evC f x = evC b' (blk e x) := by
  first | exact @GlobalTheory.ClassFin.exists_multiplier_descend_blk | exact GlobalTheory.ClassFin.exists_multiplier_descend_blk | (intros; apply GlobalTheory.ClassFin.exists_multiplier_descend_blk <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma ringEquiv_eval_eq_eval_map {σ : Type} (e : ℂ ≃+* ℂ) (x : σ → ℂ)
    (p : MvPolynomial σ ℂ) :
    e (MvPolynomial.eval x p) =
      MvPolynomial.eval (fun i => e (x i)) (MvPolynomial.map (e : ℂ →+* ℂ) p) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
  exact MvPolynomial.hom_eval₂ p (RingHom.id ℂ) (e : ℂ →+* ℂ) x

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma ev_eq_evC_map_algebraMap {ι : Type} (p : MvPolynomial (ι × ι) ℚ)
    (g : Matrix ι ι ℂ) :
    _root_.GlobalTheory.ClassFin.ev p g =
      _root_.GlobalTheory.ClassFin.evC (MvPolynomial.map (algebraMap ℚ ℂ) p) g := by
  unfold _root_.GlobalTheory.ClassFin.ev _root_.GlobalTheory.ClassFin.evC
  rw [MvPolynomial.aeval_def, MvPolynomial.eval_map]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma mem_span_rational_of_vanishing {ι : Type} (Γ : Set (Matrix ι ι ℂ))
    (hΓ : ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : ∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC f g = 0) :
    f ∈ Submodule.span ℂ {w | ∃ p ∈ _root_.GlobalTheory.ClassFin.vanI Γ,
      MvPolynomial.map (algebraMap ℚ ℂ) p = w} := by
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {w | ∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC w g = 0}
      add_mem' := fun {a b} ha hb g hg => by
        simp only [_root_.GlobalTheory.ClassFin.evC, map_add (f := _)] at *
        rw [ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by simp [_root_.GlobalTheory.ClassFin.evC]
      smul_mem' := fun c w hw g hg => by
        simp only [_root_.GlobalTheory.ClassFin.evC, Set.mem_setOf_eq] at *
        rw [MvPolynomial.smul_eval, hw g hg, mul_zero] }
  have hstable : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr w' k =
        σ ((MvPolynomial.basisMonomials (ι × ι) ℂ).repr w k) := by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, fun g hg => ?_, fun k => MvPolynomial.coeff_map _ _ _⟩
    have h := hw (g.map σ.symm) (hΓ σ.symm g hg)
    have h2 := ringEquiv_eval_eq_eval_map σ (fun ij => (g.map σ.symm) ij.1 ij.2) w
    simp only [_root_.GlobalTheory.ClassFin.evC] at h ⊢
    rw [h, map_zero] at h2
    simpa [Matrix.map_apply] using h2.symm
  have hle := _root_.GlobalTheory.ClassFin.GaloisDescent.le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ)
    W hstable
  refine Submodule.span_mono ?_ (hle hf)
  rintro w ⟨hwW, hrat⟩
  have hrange : w ∈ Set.range (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
    obtain ⟨q, hq⟩ := hrat n
    exact ⟨q, hq.symm⟩
  obtain ⟨p, rfl⟩ := hrange
  refine ⟨p, fun g hg => ?_, rfl⟩
  rw [ev_eq_evC_map_algebraMap]
  exact hwW g hg


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.evC_eq_zero_of_mem_pts_of_stable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) →
    ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, _root_.GlobalTheory.ClassFin.evC f g = 0) →
    ∀ y ∈ _root_.GlobalTheory.ClassFin.pts Γ ℂ, _root_.GlobalTheory.ClassFin.evC f y = 0 := by
  intro ι _ _ Γ hΓ f hf y hy
  have hspan := mem_span_rational_of_vanishing Γ hΓ f hf
  clear hf
  induction hspan using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨p, hp, rfl⟩ := hw
    rw [← ev_eq_evC_map_algebraMap]
    exact hy p hp
  | zero => simp [_root_.GlobalTheory.ClassFin.evC]
  | add a b _ _ ha hb =>
    simp only [_root_.GlobalTheory.ClassFin.evC, map_add (f := _)] at *
    rw [ha, hb, add_zero]
  | smul c w _ hw =>
    simp only [_root_.GlobalTheory.ClassFin.evC] at *
    rw [MvPolynomial.smul_eval, hw, mul_zero]

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_conj_harm_of_span' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ) (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ P : Matrix ι ι ℂ, IsUnit P.det ∧ Harm (fun s => P * g s * P⁻¹) := by
  first | exact @GlobalTheory.ClassFin.exists_conj_harm_of_span | exact GlobalTheory.ClassFin.exists_conj_harm_of_span | (intros; apply GlobalTheory.ClassFin.exists_conj_harm_of_span <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_real_translate_isMinNormTensorInOrbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℝ), (∃ w ∈ orb d (fun k => (t k : ℂ)), IsMinVec d w) → ∃ g : Matrix ι ι ℝ, g.det = 1 ∧ IsMinVec d (act d (fun k => (t k : ℂ)) (g.map (fun r : ℝ => (r : ℂ)))) := by
  first | exact @GlobalTheory.ClassFin.exists_real_translate_isMinVec | exact GlobalTheory.ClassFin.exists_real_translate_isMinVec | (intros; apply GlobalTheory.ClassFin.exists_real_translate_isMinVec <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Chain

theorem eventually_quad_ne {E : Type} [Field E] [CharZero E] (a b c : E) (ha : a ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, a + (t : E) * b + (t : E) ^ 2 * c ≠ 0 := by
  classical
  set p : Polynomial E := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h
    have h0 := congrArg (fun q : Polynomial E => q.coeff 0) h
    simp [p] at h0
    exact ha h0
  rw [Filter.eventually_cofinite]
  refine (Set.Finite.preimage (fun _ _ _ _ h => Rat.cast_injective h)
    (Finset.finite_toSet p.roots.toFinset)).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq, not_not] at ht
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hp0]
  show Polynomial.eval (t : E) p = 0
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  linear_combination ht

variable {E : Type} [Field E] [CharZero E] {n : ℕ}

theorem hf_line_left (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G (x + t • w) z = hf σ G x z + t * hf σ G w z := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hf_line_right (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G z (x + t • w) = hf σ G z x + σ t * hf σ G z w := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem eventually_aniso (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w : Fin n → E)
    (hx : hf σ G x x ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) (x + (t : E) • w) ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x x) (hf σ G w x + hf σ G x w) (hf σ G w w) hx]
    with t ht
  have hσ : σ (t : E) = t := map_ratCast σ t
  rw [hf_line_left, hf_line_right, hf_line_right, hσ]
  intro h
  apply ht
  linear_combination h

theorem eventually_pair (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E)
    (hx : hf σ G x z ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) z ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x z) (hf σ G w z) 0 hx] with t ht
  rw [hf_line_left]
  intro h
  apply ht
  linear_combination h

theorem eventually_chain (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    {ι : Type} (z : ι → Fin n → E) (l : ι → E) (x : Fin n → E) (u : E) (hx : hf σ G x x ≠ 0)
    (hu : u * σ u = 1) (hz : ∀ i, hf σ G (z i) (z i) = 0) (hxz : ∀ i, hf σ G x (z i) ≠ 0)
    (S : Finset ι) :
    ∀ᶠ t : ℚ in Filter.cofinite, ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) =
      m * tv σ G (x + (t : E) • ∑ i ∈ S, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ S, l i • z i) (x + (t : E) • ∑ i ∈ S, l i • z i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine Filter.Eventually.of_forall fun t => ⟨1, (TvGen σ G).one_mem, ?_⟩
    simp
  | @insert j S hj ih =>
    have hpair := eventually_pair σ G x (∑ i ∈ S, l i • z i) (z j) (hxz j)
    have ha1 := eventually_aniso σ G x (∑ i ∈ S, l i • z i) hx
    have ha2 := eventually_aniso σ G x (∑ i ∈ insert j S, l i • z i) hx
    filter_upwards [ih, hpair, ha1, ha2] with t hih h1 h2 h3
    obtain ⟨m, hm, hmeq⟩ := hih
    have hsplit : x + (t : E) • ∑ i ∈ insert j S, l i • z i =
        (x + (t : E) • ∑ i ∈ S, l i • z i) + ((t : E) * l j) • z j := by
      rw [Finset.sum_insert hj, smul_add, mul_smul]
      abel
    rw [hsplit] at h3 ⊢
    obtain ⟨m', hm', hm'eq⟩ :=
      GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane E n σ G hG _ (z j) ((t : E) * l j) u (hz j) h1 h2 h3 hu
    exact ⟨m * m', (TvGen σ G).mul_mem hm hm', by rw [hmeq, hm'eq, mul_assoc]⟩

end GlobalTheory.UTrans.Chain

theorem GlobalTheory.UTrans.quasiReflection_eq_tvGen_mul : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ (x y : Fin n → E) (u : E), hf σ G x x ≠ 0 → hf σ G y y ≠ 0 → u * σ u = 1 → ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) = m * tv σ G y ((u - 1) / hf σ G y y) := by
  intro E _ _ n σ G hG hiso x y u hx hy hu
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp [hf])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp [hf])
  obtain ⟨z, hli, hzp⟩ := GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors E n σ G hG hiso x y hx0 hy0
  have : Nonempty (Fin n) := by
    by_contra hne
    exact hx0 (funext fun i => (hne ⟨i⟩).elim)
  have hspan : Submodule.span E (Set.range z) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : y - x ∈ Submodule.span E (Set.range z) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hmem
  have hz : ∀ i, hf σ G (z i) (z i) = 0 := fun i => (hzp i).1
  have hxz : ∀ i, hf σ G x (z i) ≠ 0 := fun i => (hzp i).2.1
  have hyz : ∀ i, hf σ G y (z i) ≠ 0 := fun i => (hzp i).2.2
  have h1 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z l x u hx hu hz hxz Finset.univ
  have h2 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z (fun i => -l i) y u hy hu hz hyz
    Finset.univ
  have hT : Filter.Tendsto (fun t : ℚ => 1 - t) Filter.cofinite Filter.cofinite :=
    (sub_right_injective : Function.Injective fun t : ℚ => 1 - t).tendsto_cofinite
  obtain ⟨t, ⟨m1, hm1, e1⟩, ⟨m2, hm2, e2⟩⟩ := (h1.and (hT.eventually h2)).exists
  have hv : y + (((1 - t : ℚ)) : E) • ∑ i ∈ Finset.univ, (-l i) • z i =
      x + (t : E) • ∑ i ∈ Finset.univ, l i • z i := by
    simp only [neg_smul, Finset.sum_neg_distrib, hl]
    push_cast
    module
  have e2' : tv σ G y ((u - 1) / hf σ G y y) =
      m2 * tv σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
          (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)) := by
    rw [← hv]
    exact e2
  obtain ⟨-, hdet, hinv, -⟩ := (GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one E n σ G hG).2 m2 hm2
  have hunit : IsUnit m2.det := by
    rw [hdet]
    exact isUnit_one
  refine ⟨m1 * m2⁻¹, (TvGen σ G).mul_mem hm1 hinv, ?_⟩
  rw [e1, e2', mul_assoc m1, ← mul_assoc m2⁻¹, Matrix.nonsing_inv_mul _ hunit, one_mul]
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  first | exact @GlobalTheory.QNorm.index_sqSub_adicCompletion_le | exact GlobalTheory.QNorm.index_sqSub_adicCompletion_le | (intros; apply GlobalTheory.QNorm.index_sqSub_adicCompletion_le <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.prime_mul_card_places_le_card_over_kummer : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → p * S.card ≤ SE.card + (p - 1) * tNon p F δ S := by
  first | exact @GlobalTheory.CNorm.prime_mul_card_le_card_over | exact GlobalTheory.CNorm.prime_mul_card_le_card_over | (intros; apply GlobalTheory.CNorm.prime_mul_card_le_card_over <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.subgroupPowRelIndex_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  first | exact @GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | exact GlobalTheory.CNorm.pIdx_units_of_isAdicComplete | (intros; apply GlobalTheory.CNorm.pIdx_units_of_isAdicComplete <;> assumption)
end
