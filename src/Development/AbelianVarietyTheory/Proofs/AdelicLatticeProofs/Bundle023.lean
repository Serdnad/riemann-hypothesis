module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle013
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle014
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle004
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetup
public import Mathlib.Analysis.Complex.Circle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.RingTheory.QuasiFinite.Basic

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational : (∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A) (R₀ : Subring R) (u : GL κ A), (∀ i, b.repr 1 i ∈ R₀) → (∀ p q, emb b u p q ∈ R₀) → ∀ i j k, b.repr ((u : Matrix κ κ A) i j) k ∈ R₀ ∧ b.repr (((u⁻¹ : GL κ A) : Matrix κ κ A) i j) k ∈ R₀) ∧ ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (κ : Type) [Fintype κ] [DecidableEq κ] (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ γ : GL κ F, emb b (Units.map (RingHom.mapMatrix (algebraMap F A)).toMonoidHom γ) = (emb ω γ).map (algebraMap ℚ R) := by
  first | exact @GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational | exact GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational | (intros; apply GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sUnits_over_and_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → (∀ x : Fˣ, Units.map (algebraMap F E : F →* E) x ∈ sUnits E SE ↔ x ∈ sUnits F S) ∧ ∀ y : Eˣ, y ∈ sUnits E SE → Units.map (σ : E →* E) y ∈ sUnits E SE := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hS
  obtain ⟨-, hup, hval⟩ := places_over F E
  obtain ⟨hconj, -⟩ := conj_places_transitive F E δ θ σ hq
  refine ⟨fun x => ⟨fun h => ?_, fun h => ?_⟩, fun y hy => ?_⟩
  · rw [mem_sUnits] at h ⊢
    intro v hv
    obtain ⟨w, rfl⟩ := hup v
    obtain ⟨e, he, hx⟩ := hval w
    have h1 : w.valuation E (algebraMap F E (x : F)) = 1 := h w (fun a => hv ((hS w).1 a))
    rw [hx] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le he.ne').1 h1
  · rw [mem_sUnits] at h ⊢
    intro w hw
    obtain ⟨e, he, hx⟩ := hval w
    change w.valuation E (algebraMap F E (x : F)) = 1
    rw [hx, h _ (fun a => hw ((hS w).2 a)), one_pow]
  · rw [mem_sUnits] at hy ⊢
    intro w hw
    obtain ⟨w', hu, hv⟩ := hconj w
    change w.valuation E (σ (y : E)) = 1
    rw [← hv]
    exact hy w' (fun a => hw ((hS w).2 (hu ▸ (hS w').1 a)))

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_place_valuation_aut (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) ∧
      ∀ y : E, w'.valuation E y = w.valuation E (σ y) := by
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ.toRingEquiv with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = σ (x : E) := fun x => rfl
  have hfix : ∀ a : 𝓞 F, e (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hc]
    exact σ.commutes (a : F)
  refine ⟨w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective, ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    ext a
    change e (algebraMap (𝓞 F) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ w.asIdeal
    rw [hfix]
  · intro y
    exact valuation_of_eq_comap σ.toRingEquiv w _ rfl y

theorem sUnits_over_and_aut : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → (∀ x : Fˣ, Units.map (algebraMap F E : F →* E) x ∈ sUnits E SE ↔ x ∈ sUnits F S) ∧ ∀ (τ : E ≃ₐ[F] E) (y : Eˣ), y ∈ sUnits E SE → Units.map (τ : E →* E) y ∈ sUnits E SE := by
  intro F E _ _ _ _ _ _ S SE hS
  obtain ⟨-, hup, hval⟩ := places_over F E
  refine ⟨fun x => ⟨fun h => ?_, fun h => ?_⟩, fun σ y hy => ?_⟩
  · rw [mem_sUnits] at h ⊢
    intro v hv
    obtain ⟨w, rfl⟩ := hup v
    obtain ⟨e, he, hx⟩ := hval w
    have h1 : w.valuation E (algebraMap F E (x : F)) = 1 := h w (fun a => hv ((hS w).1 a))
    rw [hx] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le he.ne').1 h1
  · rw [mem_sUnits] at h ⊢
    intro w hw
    obtain ⟨e, he, hx⟩ := hval w
    change w.valuation E (algebraMap F E (x : F)) = 1
    rw [hx, h _ (fun a => hw ((hS w).2 a)), one_pow]
  · rw [mem_sUnits] at hy ⊢
    intro w hw
    obtain ⟨w', hu, hv⟩ := exists_place_valuation_aut F E σ w
    change w.valuation E (σ (y : E)) = 1
    rw [← hv]
    exact hy w' (fun a => hw ((hS w).2 (hu ▸ (hS w').1 a)))

end GlobalTheory.CNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_minNormTensor_of_isClosed_tensorSLOrbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsClosed (orb d v) → ∃ w ∈ orb d v, IsMinVec d w := by
  first | exact @GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed | exact GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed | (intros; apply GlobalTheory.ClassFin.MinVec.exists_isMinVec_of_isClosed <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isClosed_image_SL_under_generating_invariants : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ) (κ : Type) [Fintype κ] (Φ : κ → MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → (∀ g ∈ Γ, g.det = 1) → (∀ k, IsInv Γ (Φ k)) → (∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (Set.range Φ)) → IsClosed {z : κ → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧ z = fun k => evC (Φ k) y} := by
  first | exact @GlobalTheory.ClassFin.isClosed_image_invariants | exact GlobalTheory.ClassFin.isClosed_image_invariants | (intros; apply GlobalTheory.ClassFin.isClosed_image_invariants <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.tensorSLOrbit_map_proper_of_isClosed : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsClosed (orb d v) → ∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C → ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C' := by
  first | exact @GlobalTheory.ClassFin.orbit_proper_of_isClosed | exact GlobalTheory.ClassFin.orbit_proper_of_isClosed | (intros; apply GlobalTheory.ClassFin.orbit_proper_of_isClosed <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.ActNorm

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma tpow_apply_eq_prod {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ)
    (a b : Fin n → ι) : _root_.GlobalTheory.ClassFin.tpow n y a b = ∏ k, y (a k) (b k) := by
  simp [_root_.GlobalTheory.ClassFin.tpow]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma tpow_conjTranspose {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ) :
    (_root_.GlobalTheory.ClassFin.tpow n y)ᴴ = _root_.GlobalTheory.ClassFin.tpow n yᴴ := by
  ext a b
  simp [tpow_apply_eq_prod, conjTranspose_apply, star_prod]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma nsq_eq_sum_sum_norm_sq_components {ι : Type} [Fintype ι] {m : ℕ} (d : Fin m → ℕ)
    (x : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) :
    _root_.GlobalTheory.ClassFin.nsq x = ∑ i, ∑ a : Fin (d i) → ι, ‖x ⟨i, a⟩‖ ^ 2 := by
  unfold _root_.GlobalTheory.ClassFin.nsq _root_.GlobalTheory.ClassFin.TIdx at *
  exact Fintype.sum_sigma _

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma act_apply_eq_vecMul_tpow {ι : Type} [Fintype ι] {m : ℕ}
    (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (y : Matrix ι ι ℂ) (i : Fin m)
    (a : Fin (d i) → ι) :
    _root_.GlobalTheory.ClassFin.act d v y ⟨i, a⟩ =
      ((fun b => v ⟨i, b⟩) ᵥ* _root_.GlobalTheory.ClassFin.tpow (d i) y) a := rfl

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma sum_norm_sq_vecMul_eq_of_mul_conjTranspose_eq_one {κ : Type} [Fintype κ] [DecidableEq κ] (w : κ → ℂ)
    (M : Matrix κ κ ℂ) (hM : M * Mᴴ = 1) : ∑ c, ‖(w ᵥ* M) c‖ ^ 2 = ∑ a, ‖w a‖ ^ 2 := by
  have key : ∀ x : κ → ℂ, ((∑ c, ‖x c‖ ^ 2 : ℝ) : ℂ) = x ⬝ᵥ star x := by
    intro x
    push_cast
    simp [dotProduct, Complex.mul_conj']
  apply Complex.ofReal_injective
  rw [key, key, star_vecMul, dotProduct_mulVec, vecMul_vecMul, hM, vecMul_one]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma sum_norm_sq_vecMul_le_card_sq_mul_bound_sq {κ : Type} [Fintype κ] (w : κ → ℂ) (M : Matrix κ κ ℂ)
    (K : ℝ) (hK : ∀ a c, ‖M a c‖ ≤ K) :
    ∑ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ (Fintype.card κ : ℝ) ^ 2 * K ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
  have hc : ∀ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ (Fintype.card κ : ℝ) * K ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
    intro c
    have h1 : ‖(w ᵥ* M) c‖ ≤ ∑ a, ‖w a‖ * K := by
      simp only [vecMul, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hK a c) (norm_nonneg _)
    calc ‖(w ᵥ* M) c‖ ^ 2 ≤ (∑ a, ‖w a‖ * K) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = K ^ 2 * (∑ a, ‖w a‖) ^ 2 := by rw [← Finset.sum_mul]; ring
      _ ≤ K ^ 2 * ((Fintype.card κ : ℝ) * ∑ a, ‖w a‖ ^ 2) := by
          gcongr
          simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖w a‖)
      _ = _ := by ring
  calc ∑ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ ∑ _c : κ, (Fintype.card κ : ℝ) * K ^ 2 * ∑ a, ‖w a‖ ^ 2 :=
        Finset.sum_le_sum fun c _ => hc c
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma norm_tpow_apply_le_pow_of_forall_norm_le {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ) (B : ℝ)
    (hy : ∀ i j, ‖y i j‖ ≤ B) (a b : Fin n → ι) : ‖_root_.GlobalTheory.ClassFin.tpow n y a b‖ ≤ B ^ n := by
  rw [tpow_apply_eq_prod, norm_prod]
  calc ∏ k, ‖y (a k) (b k)‖ ≤ ∏ _k : Fin n, B :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => hy _ _
    _ = B ^ n := by simp


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ), (∀ (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (U : Matrix ι ι ℂ), U * Uᴴ = 1 → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v U) = _root_.GlobalTheory.ClassFin.nsq v) ∧ (∀ C : ℝ, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (y : Matrix ι ι ℂ), (∀ i j, ‖y i j‖ ≤ C) → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v y) ≤ C' * _root_.GlobalTheory.ClassFin.nsq v) ∧ ∀ v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ, Continuous (_root_.GlobalTheory.ClassFin.act d v) := by
  intro ι _ _ m d
  refine ⟨fun v U hU => ?_, fun C => ?_, fun v => ?_⟩
  · have hK : ∀ n, _root_.GlobalTheory.ClassFin.tpow n U * (_root_.GlobalTheory.ClassFin.tpow n U)ᴴ = 1 := by
      intro n
      have h := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).1 n
      rw [tpow_conjTranspose, ← h.2.1, hU, h.1]
    rw [nsq_eq_sum_sum_norm_sq_components, nsq_eq_sum_sum_norm_sq_components]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [act_apply_eq_vecMul_tpow]
    exact sum_norm_sq_vecMul_eq_of_mul_conjTranspose_eq_one _ _ (hK _)
  · set B := max C 0
    refine ⟨∑ i, (Fintype.card (Fin (d i) → ι) : ℝ) ^ 2 * (B ^ d i) ^ 2,
      Finset.sum_nonneg fun _ _ => by positivity, fun v y hy => ?_⟩
    have hyB : ∀ i j, ‖y i j‖ ≤ B := fun i j => (hy i j).trans (le_max_left _ _)
    rw [nsq_eq_sum_sum_norm_sq_components, nsq_eq_sum_sum_norm_sq_components, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [act_apply_eq_vecMul_tpow]
    refine (sum_norm_sq_vecMul_le_card_sq_mul_bound_sq _ _ _ (norm_tpow_apply_le_pow_of_forall_norm_le _ y B hyB)).trans ?_
    gcongr
    exact Finset.single_le_sum
      (f := fun i => (Fintype.card (Fin (d i) → ι) : ℝ) ^ 2 * (B ^ d i) ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  · unfold _root_.GlobalTheory.ClassFin.act
    simp only [vecMul, dotProduct, tpow_apply_eq_prod]
    fun_prop

end GlobalTheory.ClassFin.ActNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isClosed_isHermitianLogOfPosDef : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], IsClosed {p : Matrix ι ι ℂ × Matrix ι ι ℂ | IsLog p.1 p.2} := by
  first | exact @GlobalTheory.ClassFin.isClosed_isLog | exact GlobalTheory.ClassFin.isClosed_isLog | (intros; apply GlobalTheory.ClassFin.isClosed_isLog <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V), SS (Set.range fun g => LinearMap.toMatrix b b (ρ g)) ↔ ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation | exact GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation | (intros; apply GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem finite_det_one_add_smul_eq_zero {E K : Type} [Field E] [Field K] (φ : E →+* K) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) : {l : E | (1 + φ l • G).det = 0}.Finite := by
  let p : Polynomial K := (1 + (Polynomial.X : Polynomial K) • G.map Polynomial.C).det
  have hp : ∀ x : K, p.eval x = (1 + x • G).det := by
    intro x
    have := (Polynomial.evalRingHom x).map_det (1 + (Polynomial.X : Polynomial K) • G.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring
  have hp0 : p ≠ 0 := by
    intro h
    have := hp 0
    rw [h] at this
    simp at this
  have hfin : (p.rootSet K).Finite := p.rootSet_finite K
  refine (hfin.preimage φ.injective.injOn).subset fun l hl => ?_
  simp only [Set.mem_preimage, Polynomial.mem_rootSet]
  refine ⟨hp0, ?_⟩
  rw [Polynomial.coe_aeval_eq_eval, hp]
  exact hl

theorem finite_not_isUnit_det {E R : Type} [Field E] [CommRing R] (φ : E →+* R) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (ε : R) (hε : ε * ε = ε)
    (hfin : {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}.Finite) :
    {l : E | ¬ IsUnit (1 + φ l • (ε • g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R))).det}.Finite := by
  set G := ε • g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) with hG
  have key : ∀ (M : Ideal R) (l : E), Ideal.Quotient.mk M (1 + φ l • G).det =
      (1 + ((Ideal.Quotient.mk M).comp φ) l • G.map (Ideal.Quotient.mk M)).det := by
    intro M l
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h1 : ∀ M ∈ {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}, {l : E | (1 + φ l • G).det ∈ M}.Finite := by
    rintro M ⟨hM, -⟩
    letI := Ideal.Quotient.field M
    refine (finite_det_one_add_smul_eq_zero ((Ideal.Quotient.mk M).comp φ)
      (G.map (Ideal.Quotient.mk M))).subset fun l hl => ?_
    rw [Set.mem_setOf_eq, ← key, Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  refine ((hfin.biUnion h1).union (Set.finite_singleton (-1))).subset fun l hl => ?_
  obtain ⟨M, hM, hl⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hl)
  have h0 : ε * (1 - ε) ∈ M := by
    rw [mul_sub, mul_one, hε, sub_self]; exact M.zero_mem
  rcases hM.isPrime.mem_or_mem h0 with h | h
  · right
    letI := Ideal.Quotient.field M
    have h2 := Ideal.Quotient.eq_zero_iff_mem.2 hl
    have h3 := Ideal.Quotient.eq_zero_iff_mem.2 h
    have h4 : G.map (Ideal.Quotient.mk M) = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hG, hij, Matrix.one_apply, h3]
    rw [key, h4] at h2
    have h5 : (1 + ((Ideal.Quotient.mk M).comp φ) l • (1 : Matrix (Fin n) (Fin n) (R ⧸ M))) =
        ((Ideal.Quotient.mk M).comp φ) (1 + l) • 1 := by
      rw [map_add (f := _), map_one, add_smul, one_smul]
    rw [h5, Matrix.det_smul, Matrix.det_one, mul_one] at h2
    have h6 := (map_eq_zero _).1 (pow_eq_zero_iff (by
      intro h; rw [h] at h2; simp at h2) |>.1 h2)
    exact eq_neg_of_add_eq_zero_right h6
  · left
    exact Set.mem_biUnion (s := {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}) ⟨hM, h⟩ hl

noncomputable def adEval (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
  RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v

theorem adEval_surjective (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Function.Surjective (adEval F v) := by
  classical
  intro x
  refine ⟨⟨Pi.single v x, ?_⟩, ?_⟩
  · filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _
  · exact Pi.single_eq_same v x

theorem finite_primes_one_sub (F : Type) [Field F] [NumberField F] (e : FiniteAdeleRing (𝓞 F) F)
    (he : {v | e v ≠ 0}.Finite) :
    {P : Ideal (FiniteAdeleRing (𝓞 F) F) | P.IsPrime ∧ 1 - e ∈ P}.Finite := by
  refine (he.image fun v => RingHom.ker (adEval F v)).subset ?_
  rintro P ⟨hP, h⟩
  have hle : he.toFinset.inf (fun v => RingHom.ker (adEval F v)) ≤ P := by
    intro a ha
    have h0 : a * e = 0 := by
      refine FiniteAdeleRing.ext F fun v => ?_
      change a v * e v = 0
      by_cases hv : e v = 0
      · rw [hv, mul_zero]
      · have h1 : a ∈ RingHom.ker (adEval F v) :=
          (Finset.inf_le (f := fun v => RingHom.ker (adEval F v)) (he.mem_toFinset.2 hv)) ha
        have h2 : a v = 0 := h1
        rw [h2, zero_mul]
    have : a = a * (1 - e) := by rw [mul_sub, h0, mul_one, sub_zero]
    rw [this]
    exact P.mul_mem_left _ h
  obtain ⟨v, hv, hvP⟩ := (Ideal.IsPrime.inf_le' hP).1 hle
  exact ⟨v, he.mem_toFinset.1 hv,
    (RingHom.ker_isMaximal_of_surjective _ (adEval_surjective F v)).eq_of_le hP.ne_top hvP⟩

theorem infinite_norm_one {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E] (c : E ≃ₐ[F] E)
    (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) : {l : E | l * c l = 1}.Infinite := by
  first
  | exact @_root_.GlobalTheory.NormOneInfinite.normOne_infinite
  | exact _root_.GlobalTheory.NormOneInfinite.normOne_infinite
  | (apply _root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormOneInfinite.normOne_infinite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormOneInfinite.normOne_infinite ..)

theorem exists_norm_one_isUnit_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ x, c (c x) = x) → c ≠ 1 → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) (RA F E)) (e : FiniteAdeleRing (𝓞 F) F), e * e = e → {v | e v ≠ 0}.Finite → ∃ lam : E, lam * c lam = 1 ∧ IsUnit (1 + ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] lam) • ((e ⊗ₜ[F] (1 : E)) • g + ((1 - e) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (RA F E)))).det := by
  intro F E _ _ _ _ _ c hrk hc hc1 n g e he hfin
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hsub : ((1 - e) ⊗ₜ[F] (1 : E) : RA F E) = 1 - e ⊗ₜ[F] (1 : E) := by
    rw [TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
  have hM : {M : Ideal (RA F E) | M.IsMaximal ∧ 1 - e ⊗ₜ[F] (1 : E) ∈ M}.Finite := by
    refine ((finite_primes_one_sub F e hfin).biUnion fun P _ =>
      Algebra.QuasiFinite.finite_primesOver (S := RA F E) P).subset ?_
    rintro M ⟨hM, h⟩
    haveI := hM.isPrime
    refine Set.mem_biUnion (x := M.under (FiniteAdeleRing (𝓞 F) F)) ⟨inferInstance, ?_⟩
      ⟨inferInstance, inferInstance⟩
    rw [← hsub] at h
    exact h
  have hbad := finite_not_isUnit_det
    (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom g (e ⊗ₜ[F] (1 : E))
    (by rw [Algebra.TensorProduct.tmul_mul_tmul, he, mul_one]) hM
  obtain ⟨l, hl, hl'⟩ := (infinite_norm_one c hc hc1).exists_notMem_finite hbad
  refine ⟨l, hl, ?_⟩
  rw [hsub]
  exact not_not.1 hl'

end GlobalTheory.UnRep
end

section

open scoped ContDiff

theorem _root_.GlobalTheory.T.continuous_bicharacter_weil_setup : ∀ (G V : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (Γ U₀ U : AddSubgroup G) (χ : G → ℂ), Continuous p → Continuous ι → (∀ v, p (ι v) = v) → (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ x y, ‖β x y‖ = 1) → Continuous (fun q : G × G => β q.1 q.2) → (∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ))) → (∀ v, om v v = 0) → (∀ v, J (J v) = -v) → (∀ x y, om x (J y) = om y (J x)) → (∀ v, v ≠ 0 → 0 < om v (J v)) → (∀ g ∈ Γ, ∀ g' ∈ Γ, β g g' = 1) → (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ v, ι v ∈ U₀) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite) → (∀ x, x ∉ U₀ → χ x = 0) → (∀ x, ‖χ x‖ ≤ 1) → χ 0 = 1 → (∀ x v, χ (x + ι v) = χ x) → IsOpen (U : Set G) → (∀ u ∈ U, ∀ x, β x (u - ι (p u)) * χ (x + (u - ι (p u))) = χ x) → ∃ f : G → ℂ, f ≠ 0 ∧ Continuous f ∧ (∀ g ∈ Γ, ∀ w, β g w * f (g + w) = f w) ∧ (∀ u, p u = 0 → (∀ x, β x u * χ (x + u) = χ x) → ∀ w, β w u * f (w + u) = f w) ∧ (∀ w, ContDiff ℝ ∞ fun v : V => f (w + ι v)) ∧ ∀ w z, deriv (fun t : ℝ => β w (ι (t • z)) * f (w + ι (t • z))) 0 + Complex.I * deriv (fun t : ℝ => β w (ι (t • J z)) * f (w + ι (t • J z))) 0 = 0 := by
  first | exact @GlobalTheory.HeisenbergGaussianSeries.exists_theta | exact GlobalTheory.HeisenbergGaussianSeries.exists_theta | (intros; apply GlobalTheory.HeisenbergGaussianSeries.exists_theta <;> assumption)
end

section

open scoped Topology BigOperators

theorem _root_.GlobalTheory.T.exists_zpow_prod_div_conj_of_continuous_trivial_on_real : ∀ (ι : Type) [Fintype ι] (f : (ι → ℂˣ) →* Circle), Continuous f → (∀ z : ι → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) → f z = 1) → ∃ k : ι → ℤ, ∀ z, ((f z : Circle) : ℂ) = ∏ i, ((z i : ℂ) / starRingEnd ℂ (z i : ℂ)) ^ k i := by
  first | exact @GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow | exact GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow | (intros; apply GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow <;> assumption)
end
