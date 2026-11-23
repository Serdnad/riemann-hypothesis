module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle038
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Fourier.FourierTransform
public import Formalism.LatticeTheta.ThetaShiftInversion
import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle039
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
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
public import Formalism.LatticeTheta.Statement
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem hilbert90_sUnits_kummer : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → AdmP p F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → ∏ i ∈ Finset.range p, σ^[i] (u : E) = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = σ y / y := by
  classical
  intro p F E _ _ _ _ _ ζ δ θ σ hq S SE hSE hadm hδ u hu hN
  obtain ⟨hfd, -, hgal, -, hgen, -⟩ := kummer_galois p F E ζ δ θ σ hq
  obtain ⟨y, hy0, hy⟩ := (GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p F E ζ δ θ σ hq).2.2.2.2.1 (u : E) hN
  obtain ⟨hact, htrans⟩ := galois_places_transitive F E
  rw [mem_sUnits] at hu
  have hval : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE → w.valuation E (σ y) = w.valuation E y := by
    intro w hw
    have h1 := hu w hw
    rw [hy, map_div₀, div_eq_one_iff_eq (by simpa only [ne_eq, map_eq_zero] using hy0)] at h1
    exact h1
  have hpow : ∀ (k : ℕ) (w : HeightOneSpectrum (𝓞 E)), w ∉ SE →
      w.valuation E ((σ ^ k) y) = w.valuation E y := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨w', hw', hv'⟩ := hact (σ ^ k) w
      have hw'' : w' ∉ SE := fun h => hw ((hSE w).2 (hw' ▸ (hSE w').1 h))
      rw [pow_succ, AlgEquiv.mul_apply, ← hv', hval w' hw'', hv', ih]
  have hall : ∀ (τ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), w ∉ SE →
      w.valuation E (τ y) = w.valuation E y := by
    intro τ w hw
    obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.2 (hgen τ)
    exact hpow k w hw
  choose up hup using (places_over F E).2.1
  obtain ⟨T, -, hT⟩ := exists_superset_mem_sUnits E {Units.mk0 y hy0} ∅
  have hT' := (mem_sUnits E T _).1 (hT T subset_rfl _ (Finset.mem_singleton_self _))
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S (T.image fun w => w.under (𝓞 F))
    (fun v => -WithZero.log ((up v).valuation E y)) hadm.1 (by
      intro v hv
      have : up v ∉ T := fun h => hv (Finset.mem_image.2 ⟨_, h, hup v⟩)
      have h2 : (up v).valuation E y = 1 := hT' _ this
      simp [h2])
  have ha0 : algebraMap F E (a : F) ≠ 0 := by simp
  refine ⟨Units.mk0 (algebraMap F E a * y) (mul_ne_zero ha0 hy0), ?_, ?_⟩
  · rw [mem_sUnits]
    intro w hw
    have hv : w.under (𝓞 F) ∉ S := fun h => hw ((hSE w).2 h)
    have h3 : (up (w.under (𝓞 F))).valuation E y = w.valuation E y := by
      obtain ⟨τ, hτ⟩ := htrans w (up (w.under (𝓞 F))) (hup _)
      rw [hτ, hall τ w hw]
    have h4 : w.valuation E y ≠ 0 := by simpa only [ne_eq, map_eq_zero] using hy0
    rw [Units.val_mk0, map_mul,
      GlobalTheory.T.valuation_unramified_kummer_of_coprime_unit p F E ζ δ θ σ hq w (hadm.2 _ hv) (hδ _ hv), ha _ hv]
    simp only [h3]
    rw [WithZero.exp_neg, WithZero.exp_log h4, inv_mul_cancel₀ h4]
  · rw [Units.val_mk0, map_mul, AlgEquiv.commutes, hy, mul_div_mul_left _ _ ha0]

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.unitaryMatrix_eq_prod_quasiReflections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ γ, IsUnE c G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧ γ = (l.map fun p => refl c G p.1 p.2).prod := by
  first | exact @GlobalTheory.UnRep.isUnE_eq_prod_refl | exact GlobalTheory.UnRep.isUnE_eq_prod_refl | (intros; apply GlobalTheory.UnRep.isUnE_eq_prod_refl <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.herbrand_prime_order' : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), p.Prime → (∀ a, σ^[p] a = a) → pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → (nrm σ p).range.relIndex (fix σ) ≠ 0 ∧ (dif σ).range.relIndex (nrm σ p).ker ≠ 0 ∧ pIdx p (fix σ) ≠ 0 ∧ pTor p (fix σ) ≠ 0 ∧ (nrm σ p).range.relIndex (fix σ) ^ (p - 1) * pIdx p (⊤ : Subgroup A) * pTor p (fix σ) ^ p = (dif σ).range.relIndex (nrm σ p).ker ^ (p - 1) * pTor p (⊤ : Subgroup A) * pIdx p (fix σ) ^ p := by
  first | exact @GlobalTheory.CNorm.herbrand_prime_order | exact GlobalTheory.CNorm.herbrand_prime_order | (intros; apply GlobalTheory.CNorm.herbrand_prime_order <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open scoped FourierTransform RealInnerProductSpace SchwartzMap

namespace GlobalTheory

theorem fourier_comp_smul_of_pos {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (f : V → ℂ) {t : ℝ} (ht : 0 < t)
    (w : V) :
    (𝓕 (fun x => f (t • x)) : V → ℂ) w
      = (((t ^ Module.finrank ℝ V)⁻¹ : ℝ) : ℂ) * (𝓕 f : V → ℂ) (t⁻¹ • w) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have h := Measure.integral_comp_smul (volume : Measure V)
    (fun u : V => cexp (((-2 * Real.pi * ⟪u, t⁻¹ • w⟫ : ℝ) : ℂ) * I) • f u) t
  rw [abs_of_pos (by positivity), Complex.real_smul] at h
  rw [← h]
  congr 1
  ext v
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc t, mul_inv_cancel₀ ht.ne', one_mul]

theorem latticeSum_dilate_sub_integral_le (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (f : V → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (A : ℕ) :
    ∃ C : ℝ, ∀ (x₀ : V) (t : ℝ), 0 < t → t ≤ 1 →
      ‖∑' l : L, f (t • ((l : V) + x₀)) - (∫ x, f x) /
        ((ZLattice.covolume L * t ^ Module.finrank ℝ V : ℝ) : ℂ)‖ ≤ C * t ^ A := by
  obtain ⟨hD, -⟩ := Formalism.H.dualIsLattice V L
  set d := Module.finrank ℝ V with hd
  set k := A + d + Module.finrank ℤ (Formalism.H.dual L) + 1 with hk
  set F : 𝓢(V, ℂ) := hc.toSchwartzMap hf with hF
  have hFf : (F : V → ℂ) = f := rfl
  obtain ⟨C, hC0, hC⟩ := (𝓕 F : 𝓢(V, ℂ)).decay k 0
  have hs := ZLattice.summable_norm_pow_inv (Formalism.H.dual L) k (by omega)
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  refine ⟨(ZLattice.covolume L)⁻¹ * (C * ∑' y : Formalism.H.dual L, ‖y‖⁻¹ ^ k), ?_⟩
  intro x₀ t ht ht1
  have hft : ContDiff ℝ ∞ (fun x : V => f (t • x)) := hf.comp (contDiff_const_smul t)
  have hct : HasCompactSupport (fun x : V => f (t • x)) :=
    hc.comp_homeomorph (Homeomorph.smulOfNeZero t ht.ne')
  obtain ⟨G, hG⟩ : ∃ G : 𝓢(V, ℂ), (G : V → ℂ) = fun x : V => f (t • x) :=
    ⟨hct.toSchwartzMap hft, rfl⟩
  obtain ⟨h1, h2⟩ := Formalism.H.poissonSchwartz V L G x₀
  rw [hG] at h1 h2
  rw [h2.tsum_eq, h1.tsum_eq_add_tsum_ite 0]
  have h0 : (𝓕 (fun x : V => f (t • x)) : V → ℂ) ((0 : Formalism.H.dual L) : V) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪((0 : Formalism.H.dual L) : V), x₀⟫ : ℝ))
      = (((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
    rw [fourier_comp_smul_of_pos f ht, Real.fourier_eq']
    simp [hd]
  rw [h0, mul_add]
  have h3 : ∀ S : ℂ, (ZLattice.covolume L : ℂ)⁻¹ * ((((t ^ d)⁻¹ : ℝ) : ℂ) * ∫ x, f x) + S -
      (∫ x, f x) / ((ZLattice.covolume L * t ^ d : ℝ) : ℂ) = S := by
    intro S
    push_cast
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [h3, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcov.le,
    mul_assoc (ZLattice.covolume L volume)⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hcov.le)
  rw [← tsum_mul_left, ← tsum_mul_right]
  refine tsum_of_norm_bounded (((hs.mul_left C).mul_right (t ^ A)).hasSum) ?_
  intro y
  split_ifs with hy
  · rw [norm_zero]; positivity
  have hn : 0 < ‖(y : V)‖ := norm_pos_iff.2 (fun h => hy (Subtype.ext h))
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * (⟪(y : V), x₀⟫ : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [norm_mul, he, mul_one, fourier_comp_smul_of_pos f ht, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have h4 := hC (t⁻¹ • (y : V))
  rw [norm_iteratedFDeriv_zero, _root_.norm_smul, Real.norm_of_nonneg (by positivity),
    SchwartzMap.fourier_coe, hFf] at h4
  change _ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ A
  have h5 : ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖ ≤ C * ‖(y : V)‖⁻¹ ^ k * t ^ k := by
    rw [mul_comm, ← le_div_iff₀ (by positivity)] at h4
    refine h4.trans_eq ?_
    rw [mul_pow, inv_pow, inv_pow]
    field_simp
  have h6 : t ^ k ≤ t ^ (A + d) := pow_le_pow_of_le_one ht.le ht1 (by omega)
  calc (t ^ d)⁻¹ * ‖(𝓕 f : V → ℂ) (t⁻¹ • (y : V))‖
      ≤ (t ^ d)⁻¹ * (C * ‖(y : V)‖⁻¹ ^ k * t ^ (A + d)) := by
        refine mul_le_mul_of_nonneg_left (h5.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by rw [pow_add t A d]; field_simp

end GlobalTheory
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.galoisStable_submodule_le_span_rational : ∀ (V κ : Type) [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (W : Submodule ℂ V), (∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) → W ≤ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  first | exact @GlobalTheory.ClassFin.GaloisDescent.le_span_rational | exact GlobalTheory.ClassFin.GaloisDescent.le_span_rational | (intros; apply GlobalTheory.ClassFin.GaloisDescent.le_span_rational <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm IsLocalRing
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain IsLocalRing in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (z : v.adicCompletionIntegers F) (hz : Valued.v (z : v.adicCompletion F) = 1)
    (h : IsSquare (residue (v.adicCompletionIntegers F) z)) :
    IsSquare (z : v.adicCompletion F) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨w, rfl⟩ := residue_surjective r
  have hmem : z - w * w ∈ maximalIdeal (v.adicCompletionIntegers F) := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, hr, sub_self]
  have hlt : Valued.v ((z : v.adicCompletion F) - w * w) < 1 := by
    have hnu : ¬ IsUnit (z - w * w) := hmem
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hnu
    have hle := ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (z - w * w).2)
    push_cast at hnu hle
    exact lt_of_le_of_ne hle hnu
  have hw : Valued.v (w : v.adicCompletion F) = 1 := by
    by_contra hne
    have hwle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 w.2
    have hw1 : Valued.v (w : v.adicCompletion F) < 1 := lt_of_le_of_ne hwle hne
    have : Valued.v (z : v.adicCompletion F) < 1 := by
      have hsplit : (z : v.adicCompletion F) = ((z : v.adicCompletion F) - w * w) + w * w := by ring
      rw [hsplit]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hlt ?_)
      rw [map_mul]
      calc Valued.v (w : v.adicCompletion F) * Valued.v (w : v.adicCompletion F)
          ≤ 1 * Valued.v (w : v.adicCompletion F) := by gcongr
        _ < 1 := by rw [one_mul]; exact hw1
    rw [hz] at this
    exact lt_irrefl _ this
  have hw0 : (w : v.adicCompletion F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hw; exact zero_ne_one hw
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, one_mul]
  have hsq : IsSquare ((z : v.adicCompletion F) / (w * w)) := by
    apply _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt
    rw [h4, show (z : v.adicCompletion F) / (w * w) - 1 = ((z : v.adicCompletion F) - w * w) / (w * w) by
      field_simp, map_div₀, map_mul, hw, mul_one, div_one]
    exact hlt
  obtain ⟨s, hs⟩ := hsq
  refine ⟨s * w, ?_⟩
  have : (z : v.adicCompletion F) = (z : v.adicCompletion F) / (w * w) * (w * w) := by
    field_simp
  rw [this, hs]
  ring


open NumberField IsDedekindDomain IsLocalRing in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), Valued.v (2 : v.adicCompletion F) = 1 → ∀ x y : v.adicCompletion F, Valued.v x = 1 → Valued.v y = 1 → ¬ IsSquare x → ¬ IsSquare y → IsSquare (x * y) := by
  intro F _ _ v h2 x y hx hy hnx hny
  classical
  haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) :=
    @Fintype.ofFinite _ (_root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v)
  let x' : v.adicCompletionIntegers F :=
    ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hx.le⟩
  let y' : v.adicCompletionIntegers F :=
    ⟨y, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hy.le⟩
  have hrx : ¬ IsSquare (residue (v.adicCompletionIntegers F) x') :=
    fun h => hnx (_root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 x' hx h)
  have hry : ¬ IsSquare (residue (v.adicCompletionIntegers F) y') :=
    fun h => hny (_root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 y' hy h)
  have hx0 : residue (v.adicCompletionIntegers F) x' ≠ 0 := fun h => hrx (h ▸ ⟨0, by simp⟩)
  have hy0 : residue (v.adicCompletionIntegers F) y' ≠ 0 := fun h => hry (h ▸ ⟨0, by simp⟩)
  have hres : IsSquare (residue (v.adicCompletionIntegers F) (x' * y')) := by
    rw [map_mul, ← quadraticChar_one_iff_isSquare (mul_ne_zero hx0 hy0), map_mul,
      quadraticChar_neg_one_iff_not_isSquare.2 hrx, quadraticChar_neg_one_iff_not_isSquare.2 hry]
    norm_num
  have hxy : Valued.v (((x' * y' : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1 := by
    push_cast
    rw [map_mul]
    simp [x', y', hx, hy]
  simpa [x', y'] using _root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 (x' * y') hxy hres

end GlobalTheory.QNorm
end
