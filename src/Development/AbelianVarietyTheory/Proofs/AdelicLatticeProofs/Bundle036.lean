module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.Order

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma posDef_det_one_exists_unitary_exp_diagonal_sum_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P.PosDef) (hdet : P.det = 1) :
    ∃ (U : Matrix ι ι ℂ) (δ : ι → ℝ), U * Uᴴ = 1 ∧ ∑ i, δ i = 0 ∧
      P = (U * diagonal fun i => ((Real.exp (2 * δ i) : ℝ) : ℂ)) * Uᴴ := by
  refine ⟨(hP.1.eigenvectorUnitary : Matrix ι ι ℂ), fun i => Real.log (hP.1.eigenvalues i) / 2,
    ?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hP.1.eigenvectorUnitary.2
  · have h := hP.1.det_eq_prod_eigenvalues
    rw [hdet] at h
    have hprod' : ((∏ i, hP.1.eigenvalues i : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
    have hprod : ∏ i, hP.1.eigenvalues i = 1 := by exact_mod_cast hprod'
    rw [← Finset.sum_div, ← Real.log_prod (fun i _ => (hP.eigenvalues_pos i).ne'), hprod,
      Real.log_one, zero_div]
  · conv_lhs => rw [hP.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    congr 3
    funext i
    change (hP.1.eigenvalues i : ℂ) = (Real.exp (2 * (Real.log (hP.1.eigenvalues i) / 2)) : ℂ)
    rw [show 2 * (Real.log (hP.1.eigenvalues i) / 2) = Real.log (hP.1.eigenvalues i) by ring,
      Real.exp_log (hP.eigenvalues_pos i)]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_diagonal_conjTranspose {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (δ : ι → ℝ) (s : ℝ) :
    ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ)ᴴ =
      (U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ := by
  simp [conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose, -Complex.ofReal_exp, Pi.star_def]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_diagonal_mul_add_exponents {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (δ : ι → ℝ) (s t : ℝ) :
    ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ) *
        ((U * diagonal fun i => ((Real.exp (t * δ i) : ℝ) : ℂ)) * Uᴴ) =
      (U * diagonal fun i => ((Real.exp ((s + t) * δ i) : ℝ) : ℂ)) * Uᴴ := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
    diagonal_mul_diagonal]
  simp only [← Complex.ofReal_mul, ← Real.exp_add, ← add_mul]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma exists_unitary_exp_diagonal_fixing_of_nsq_eq {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (hv : _root_.GlobalTheory.ClassFin.IsMinVec d v)
    (g : Matrix ι ι ℂ) (hg : g.det = 1)
    (hn : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v g) = _root_.GlobalTheory.ClassFin.nsq v) :
    ∃ (U : Matrix ι ι ℂ) (δ : ι → ℝ), U * Uᴴ = 1 ∧ ∑ i, δ i = 0 ∧
      g * gᴴ = (U * diagonal fun i => ((Real.exp (2 * δ i) : ℝ) : ℂ)) * Uᴴ ∧
      ∀ s : ℝ, _root_.GlobalTheory.ClassFin.act d v
        ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ) = v := by
  have hdetP : (g * gᴴ).det = 1 := by simp [hg]
  have hP : (g * gᴴ).PosDef :=
    (posSemidef_self_mul_conjTranspose g).posDef_iff_isUnit.mpr
      ((isUnit_iff_isUnit_det _).mpr (by rw [hdetP]; exact isUnit_one))
  obtain ⟨U, δ, hU, hδ, hgP⟩ := posDef_det_one_exists_unitary_exp_diagonal_sum_zero _ hP hdetP
  refine ⟨U, δ, hU, hδ, hgP, ?_⟩
  obtain ⟨-, hactmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  have hgu : IsUnit g.det := by rw [hg]; exact isUnit_one
  have hhh : ((U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ) *
      ((U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ)ᴴ = g * gᴴ := by
    rw [unitary_conj_exp_diagonal_conjTranspose, unitary_conj_exp_diagonal_mul_add_exponents hU, hgP]
    norm_num
  set h : Matrix ι ι ℂ := (U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ with hh
  have hk : (g⁻¹ * h) * (g⁻¹ * h)ᴴ = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h, hhh, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hgu, Matrix.one_mul, conjTranspose_nonsing_inv,
      mul_nonsing_inv _ (by simp [hg])]
  have hgk : h = g * (g⁻¹ * h) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hgu, Matrix.one_mul]
  have hnh : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v h) = _root_.GlobalTheory.ClassFin.nsq v := by
    rw [hgk, hactmul, (_root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity ι m d).1 _ _ hk, hn]
  rw [hh] at hnh
  exact _root_.GlobalTheory.ClassFin.act_exp_eq_of_isMinVec ι m d v U δ hv hU hδ (by simpa only [one_mul] using hnh)


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
theorem _root_.GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ)
    (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ), _root_.GlobalTheory.ClassFin.IsMinVec d v → ∀ g : Matrix ι ι ℂ, g.det = 1 →
      _root_.GlobalTheory.ClassFin.act d v g = v → _root_.GlobalTheory.ClassFin.act d v gᴴ = v := by
  intro ι _ _ m d v hv g hg hgv
  obtain ⟨U, δ, -, -, hgP, hfix⟩ := exists_unitary_exp_diagonal_fixing_of_nsq_eq d v hv g hg (by rw [hgv])
  obtain ⟨-, hactmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  calc _root_.GlobalTheory.ClassFin.act d v gᴴ
      = _root_.GlobalTheory.ClassFin.act d (_root_.GlobalTheory.ClassFin.act d v g) gᴴ := by rw [hgv]
    _ = _root_.GlobalTheory.ClassFin.act d v (g * gᴴ) := (hactmul g gᴴ).symm
    _ = v := by rw [hgP]; exact hfix 2

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_not_mem_sq_add_sub (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ρ : 𝓞 F, ∀ a : 𝓞 F, a ^ 2 + a - ρ ∉ v.asIdeal := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  let f : 𝓞 F ⧸ v.asIdeal → 𝓞 F ⧸ v.asIdeal := fun x => x ^ 2 + x
  have hni : ¬ Function.Injective f := by
    intro h
    have h0 : (0 : 𝓞 F ⧸ v.asIdeal) = -1 := h (by simp [f])
    exact one_ne_zero (neg_eq_zero.mp h0.symm)
  have hns : ¬ Function.Surjective f := fun hs => hni (Finite.injective_iff_surjective.mpr hs)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨r, hr⟩ := hns
  obtain ⟨ρ, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨ρ, fun a ha => hr (Ideal.Quotient.mk _ a) ?_⟩
  have h := (Ideal.Quotient.eq_zero_iff_mem).mpr ha
  simp only [map_sub, map_add (f := _), map_pow] at h
  exact sub_eq_zero.mp h

theorem exists_evenNorms_unit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), ∃ Δ : v.adicCompletion F, EvenNorms Valued.v Δ ∧ Valued.v Δ = 1 ∧ Valued.v (Δ - 1) ≤ Valued.v (4 : v.adicCompletion F) := by
  intro F _ _ v
  obtain ⟨_, hval, hrep, -⟩ := GlobalTheory.T.exists_global_uniformizer_residue_representatives F v
  obtain ⟨ρ, hρ⟩ := exists_not_mem_sq_add_sub F v
  set r : v.adicCompletion F := algebraMap F (v.adicCompletion F) (ρ : F) with hr
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have h := (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr (two_ne_zero (α := F))
    rwa [map_ofNat] at h
  have hint : ∀ a : 𝓞 F, Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1 := fun a => by
    rw [hval]; exact v.valuation_le_one a
  have hone : ∀ a : 𝓞 F, a ∉ v.asIdeal →
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 := fun a ha => by
    rw [hval]; exact v.valuation_eq_one_iff_notMem.mpr ha
  have key : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → Valued.v (x ^ 2 + x - r) = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := hrep x hx
    set b : v.adicCompletion F := algebraMap F (v.adicCompletion F) (a : F) with hb_def
    have hb : Valued.v b ≤ 1 := hint a
    have hab : Valued.v (b ^ 2 + b - r) = 1 := by
      have h := hone (a ^ 2 + a - ρ) (hρ a)
      push_cast at h
      simpa [hb_def, hr] using h
    have h3 : Valued.v (x + b + 1) ≤ 1 :=
      Valuation.map_add_le _ (Valuation.map_add_le _ hx hb) (by simp)
    have hsmall : Valued.v ((x - b) * (x + b + 1)) < Valued.v (b ^ 2 + b - r) := by
      rw [hab, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' h3) ha
    have e : x ^ 2 + x - r = (x - b) * (x + b + 1) + (b ^ 2 + b - r) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ hsmall, hab]
  refine ⟨1 + 4 * r, GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root _ Valued.v r h2 (hint ρ) key, ?_, ?_⟩
  · have h2le : Valued.v (2 : v.adicCompletion F) ≤ 1 := by
      rw [← one_add_one_eq_two]
      exact Valuation.map_add_le _ (by simp) (by simp)
    have h4 : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
    by_cases h2v : Valued.v (2 : v.adicCompletion F) = 1
    · have hx : Valued.v (-(2 : v.adicCompletion F)⁻¹) = 1 := by
        rw [Valuation.map_neg, map_inv₀, h2v, inv_one]
      have hk := key (-(2 : v.adicCompletion F)⁻¹) hx.le
      have h22 : (2 : v.adicCompletion F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      have e : 1 + 4 * r = -(2 * 2) *
          ((-(2 : v.adicCompletion F)⁻¹) ^ 2 + (-(2 : v.adicCompletion F)⁻¹) - r) := by
        linear_combination (2 * (2 : v.adicCompletion F)⁻¹ - 1) * h22
      rw [e, map_mul, hk, mul_one, Valuation.map_neg, map_mul, h2v, mul_one]
    · have h2lt : Valued.v (2 : v.adicCompletion F) < 1 := lt_of_le_of_ne h2le h2v
      have h4r : Valued.v (4 * r) < Valued.v (1 : v.adicCompletion F) := by
        rw [map_one, map_mul, h4, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint ρ))
          (lt_of_le_of_lt (mul_le_of_le_one_right' h2le) h2lt)
      rw [Valuation.map_add_eq_of_lt_left _ h4r, map_one]
  · rw [add_sub_cancel_left, map_mul]
    exact mul_le_of_le_one_right' (hint ρ)

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.index_formula_norms_involution : ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index * (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) ^ 2 := by
  first | exact @GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution | exact GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution | (intros; apply GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_mul_card_le_card_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → 2 * S.card ≤ SE.card + tFin F δ S := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hSE
  classical
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tFin F δ S
      = ∑ v ∈ S, if ¬ IsSquare (algebraMap F (v.adicCompletion F) δ) then 1 else 0 := by
    rw [← Finset.card_filter, tFin, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) δ)
  · obtain ⟨w, w', hne, hw, hw'⟩ := GlobalTheory.T.exists_two_places_over_of_isSquare_local F E δ θ σ hq v hs
    have : 1 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.one_lt_card.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩,
        w', Finset.mem_filter.2 ⟨(hSE w').2 (hw' ▸ hv), hw'⟩, hne⟩
    omega
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rational_equations_weil_restriction : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), ∃ S' : Set (MvPolynomial (((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit)) ℚ), ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ y : Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) R, (∀ f ∈ S', ev f y = 0) ↔ ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0) ∧ y = emb b g := by
  first | exact @GlobalTheory.ClassFin.WeilEqs.exists_equations | exact GlobalTheory.ClassFin.WeilEqs.exists_equations | (intros; apply GlobalTheory.ClassFin.WeilEqs.exists_equations <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma le_two_pow_mul_of_consecutive_le {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (h : ∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) (i j : Fin N) (hij : i < j) :
    a i ≤ 2 ^ N * a j := by
  have key : ∀ d : ℕ, ∀ i j : Fin N, (j : ℕ) = i + d → a i ≤ 2 ^ d * a j := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have : i = j := Fin.ext (by simpa using hij.symm)
      subst this
      simp
    | succ d ih =>
      intro i j hij
      have hm : (i : ℕ) + d < N := by have := j.isLt; omega
      have h1 := ih i ⟨i + d, hm⟩ rfl
      have h2 := h ⟨i + d, hm⟩ j (by simp only; omega)
      calc a i ≤ 2 ^ d * a ⟨i + d, hm⟩ := h1
        _ ≤ 2 ^ d * (2 * a j) := by gcongr
        _ = 2 ^ (d + 1) * a j := by ring
  have hlt : (i : ℕ) < j := hij
  have hd := key ((j : ℕ) - i) i j (by omega)
  calc a i ≤ 2 ^ ((j : ℕ) - i) * a j := hd
    _ ≤ 2 ^ N * a j :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by have := j.isLt; omega))
        (ha j).le

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_reduced_iwasawa_decomposition {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (g : Matrix ι ι ℝ) (hg : g.det ≠ 0) :
    ∃ (γ : Matrix ι ι ℤ) (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ),
      (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧
      (∀ i j, j < i → n i j = 0) ∧ (∀ i j, |n i j| ≤ 1) ∧
      (∀ i j, i < j → a i ≤ 2 ^ Fintype.card ι * a j) ∧
      g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  set N := Fintype.card ι
  let e : Fin N ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  let f : Fin N ≃ ι := e.toEquiv
  have hmono : ∀ i j : ι, f.symm i < f.symm j ↔ i < j := by
    intro i j
    have := (e.lt_iff_lt (x := f.symm i) (y := f.symm j))
    simpa [f] using this
  obtain ⟨γ, k, a, n, hγ, hk, ha, hn1, hn0, hnb, hcons, hdec⟩ :=
    _root_.GlobalTheory.ClassFin.HermiteReduction.exists_reduced N (g.submatrix f f)
      (by rw [det_submatrix_equiv_self f g]; exact hg)
  refine ⟨γ.submatrix f.symm f.symm, k.submatrix f.symm f.symm, a ∘ f.symm,
    n.submatrix f.symm f.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]; exact hγ
  · rw [transpose_submatrix, submatrix_mul_equiv, hk, submatrix_one_equiv]
  · exact fun i => ha _
  · exact fun i => hn1 _
  · intro i j hij
    exact hn0 _ _ ((hmono j i).mpr hij)
  · intro i j
    show |n (f.symm i) (f.symm j)| ≤ 1
    rcases lt_trichotomy (f.symm i) (f.symm j) with h | h | h
    · exact (hnb _ _ h).trans (by norm_num)
    · rw [h, hn1]; simp
    · rw [hn0 _ _ h]; simp
  · intro i j hij
    exact le_two_pow_mul_of_consecutive_le a ha hcons _ _ ((hmono i j).mpr hij)
  · have hg' : g = (g.submatrix f f).submatrix f.symm f.symm := by ext i j; simp
    rw [hg', ← submatrix_map, submatrix_mul_equiv, hdec, ← submatrix_diagonal_equiv,
      submatrix_mul_equiv, submatrix_mul_equiv]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma isSiegel_of_reduced {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] {C : ℝ} {g : Matrix ι ι ℝ} {γ : Matrix ι ι ℤ} {k : Matrix ι ι ℝ}
    {a : ι → ℝ} {n : Matrix ι ι ℝ} (hC : 1 ≤ C) (hg : g.det = 1) (hγ : γ.det = 1)
    (hk : kᵀ * k = 1) (ha : ∀ i, 0 < a i) (hn1 : ∀ i, n i i = 1)
    (hn0 : ∀ i j, j < i → n i j = 0) (hnb : ∀ i j, |n i j| ≤ 1)
    (hlt : ∀ i j, i < j → a i ≤ C * a j)
    (hdec : g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n) :
    _root_.GlobalTheory.ClassFin.IsSiegel C k a n := by
  have hn : n.det = 1 := by
    rw [det_of_upperTriangular (by intro i j h; exact hn0 i j h)]
    simp [hn1]
  have hγR : (γ.map (Int.cast : ℤ → ℝ)).det = 1 := by
    rw [show γ.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix γ from rfl,
      ← RingHom.map_det, hγ]
    simp
  have hdet : k.det * ∏ i, a i = 1 := by
    have := congrArg det hdec
    rw [det_mul, det_mul, det_mul, hg, hn, det_diagonal, hγR] at this
    linarith
  have hk2 : k.det * k.det = 1 := by
    have := congrArg det hk
    rwa [det_mul, det_transpose, det_one] at this
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  have hk1 : k.det = 1 := by
    rcases mul_self_eq_one_iff.mp hk2 with h | h
    · exact h
    · exfalso
      rw [h] at hdet
      linarith
  refine ⟨hk, hk1, ha, ?_, hlt, hn1, hn0, fun i j => (hnb i j).trans hC⟩
  rw [hk1, one_mul] at hdet
  exact hdet

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_det_one_of_det_neg_one {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] {g : Matrix ι ι ℝ} {γ : Matrix ι ι ℤ} {k : Matrix ι ι ℝ} {a : ι → ℝ}
    {n : Matrix ι ι ℝ} (hγ : γ.det = -1) (hk : kᵀ * k = 1) (hn1 : ∀ i, n i i = 1)
    (hn0 : ∀ i j, j < i → n i j = 0) (hnb : ∀ i j, |n i j| ≤ 1)
    (hdec : g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n) :
    ∃ (γ' : Matrix ι ι ℤ) (k' n' : Matrix ι ι ℝ), γ'.det = 1 ∧ k'ᵀ * k' = 1 ∧
      (∀ i, n' i i = 1) ∧ (∀ i j, j < i → n' i j = 0) ∧ (∀ i j, |n' i j| ≤ 1) ∧
      g * γ'.map (Int.cast : ℤ → ℝ) = k' * diagonal a * n' := by
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [det_isEmpty] at hγ
    norm_num at hγ
  set d : ι → ℤ := fun i => if i = i₀ then -1 else 1 with hd_def
  have hd : ∀ i, (d i : ℝ) * d i = 1 := by
    intro i; simp only [hd_def]; split_ifs <;> norm_num
  have hda : ∀ i, |(d i : ℝ)| = 1 := by
    intro i; simp only [hd_def]; split_ifs <;> norm_num
  set D : Matrix ι ι ℝ := diagonal (fun i => (d i : ℝ)) with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hd i
  have hcomm : D * diagonal a = diagonal a * D := by
    rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hentry : ∀ i j, (D * n * D) i j = d i * n i j * d j := by
    intro i j
    simp [hD, mul_diagonal, diagonal_mul]
  refine ⟨γ * diagonal d, k * D, D * n * D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_mul, hγ, det_diagonal]
    have : ∏ i, d i = -1 := by
      simp [hd_def, Finset.prod_ite_eq']
    rw [this]; norm_num
  · rw [transpose_mul, hD, diagonal_transpose, ← hD, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ,
      hk, Matrix.one_mul, hDD]
  · intro i
    rw [hentry, hn1, mul_one]
    exact hd i
  · intro i j hij
    rw [hentry, hn0 i j hij]; simp
  · intro i j
    rw [hentry, abs_mul, abs_mul, hda, hda]
    simpa using hnb i j
  · have hmap : (γ * diagonal d).map (Int.cast : ℤ → ℝ) = γ.map (Int.cast) * D := by
      ext i j
      simp [hD, mul_diagonal]
    rw [hmap, ← Matrix.mul_assoc, hdec]
    calc k * diagonal a * n * D = k * (D * D) * diagonal a * n * D := by
          rw [hDD, Matrix.mul_one]
      _ = k * D * diagonal a * (D * n * D) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (diagonal a) D (n * D), ← hcomm]
          simp only [Matrix.mul_assoc]


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.siegel_cover (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] :
    ∃ C : ℝ, ∀ g : Matrix ι ι ℝ, g.det = 1 → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ ∃ k a n, _root_.GlobalTheory.ClassFin.IsSiegel C k a n ∧
      g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  refine ⟨2 ^ Fintype.card ι, fun g hg => ?_⟩
  have hC : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ (by norm_num)
  obtain ⟨γ, k, a, n, hγ, hk, ha, hn1, hn0, hnb, hlt, hdec⟩ :=
    exists_reduced_iwasawa_decomposition g (by rw [hg]; norm_num)
  rcases hγ with hγ | hγ
  · exact ⟨γ, hγ, k, a, n,
      isSiegel_of_reduced hC hg hγ hk ha hn1 hn0 hnb hlt hdec, hdec⟩
  · obtain ⟨γ', k', n', hγ', hk', hn1', hn0', hnb', hdec'⟩ :=
      exists_det_one_of_det_neg_one hγ hk hn1 hn0 hnb hdec
    exact ⟨γ', hγ', k', a, n',
      isSiegel_of_reduced hC hg hγ' hk' ha hn1' hn0' hnb' hlt hdec', hdec'⟩

end GlobalTheory.ClassFin
end
