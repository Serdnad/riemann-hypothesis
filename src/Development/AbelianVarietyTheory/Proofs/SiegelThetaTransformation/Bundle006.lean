module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInvariantIntegralMatrixMul
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariant
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

section

open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
namespace GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}


theorem mem_stdL {x : Fin n → E} : x ∈ stdL E n ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      intro a
      by_cases hab : a = b
      · subst hab
        simpa using isIntegral_one
      · simp [hab, isIntegral_zero]
    | zero => intro a; exact isIntegral_zero
    | add y z _ _ hy hz => intro a; exact (hy a).add (hz a)
    | smul r y _ hy =>
      intro a
      rw [Pi.smul_apply, Algebra.smul_def]
      exact (RingOfIntegers.isIntegral_coe r).mul (hy a)
  · intro hx
    have hsum : x = ∑ a, (⟨x a, hx a⟩ : 𝓞 E) • (Pi.single a 1 : Fin n → E) := by
      ext b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

private theorem cc_zero_siegel_theta_transformation : cc (0 : E) = 0 := map_zero (IsCMField.complexConj E)

private theorem cc_one' : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)

private theorem isIntegral_cc' {t : E} (ht : IsIntegral ℤ t) : IsIntegral ℤ (cc t) :=
  ht.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom

private theorem herm_one_apply (x y : Fin n → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  simp [herm, Matrix.one_apply]

theorem stdL_mem_Vset (M : ℕ) : stdL E n ∈ Vset E n M := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun x => ?_,
    ⟨1, one_pos, Nat.coprime_one_left M, fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩⟩
  constructor
  · intro hx y hy
    rw [herm_one_apply]
    rw [mem_stdL] at hx hy
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc' (hy a))
  · intro h
    rw [mem_stdL]
    intro a
    have ha := h (Pi.single a 1) (Submodule.subset_span ⟨a, rfl⟩)
    rw [herm_one_apply, Finset.sum_eq_single a (fun b _ hb => by simp [hb, cc_zero_siegel_theta_transformation])
      (by simp)] at ha
    simpa [cc_one'] using ha

end
end GlobalTheory.SW
end

section

namespace GlobalTheory.CommonDenominatorExistence

theorem exists_common_denominator {E : Type} [Field E] [NumberField E] {r : ℕ}
    {L : GlobalTheory.SW.Lt E r} (hL : Submodule.FG L) :
    ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∀ v ∈ L, ∀ (a : Fin r), ∃ (c : NumberField.RingOfIntegers E),
        (↑c : E) = (↑d : E) * v a := by
  obtain ⟨s, rfl⟩ := hL
  choose z hz using fun p : (Fin r → E) × Fin r =>
    IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) (p.1 p.2)
  let d : NumberField.RingOfIntegers E := ∏ p ∈ s ×ˢ (Finset.univ : Finset (Fin r)), ((z p).2 : _)
  refine ⟨d, Finset.prod_ne_zero_iff.mpr fun p _ => nonZeroDivisors.ne_zero (z p).2.2, ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem g hg =>
    intro a
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun p => ((z p).2 : NumberField.RingOfIntegers E))
      (show (g, a) ∈ s ×ˢ (Finset.univ : Finset (Fin r)) from
        Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩)
    refine ⟨e * (z (g, a)).1, ?_⟩
    have h := hz (g, a)
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap] at h
    rw [show d = ((z (g, a)).2 : NumberField.RingOfIntegers E) * e from he]
    push_cast
    linear_combination (-(e : E)) * h
  | zero =>
    intro a
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro a
    obtain ⟨c1, h1⟩ := hx a
    obtain ⟨c2, h2⟩ := hy a
    refine ⟨c1 + c2, ?_⟩
    rw [Pi.add_apply, mul_add, ← h1, ← h2]
    push_cast
    ring
  | smul t x _ hx =>
    intro a
    obtain ⟨c1, h1⟩ := hx a
    refine ⟨t * c1, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    push_cast
    linear_combination (t : E) * h1

end GlobalTheory.CommonDenominatorExistence
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

variable {N : ℕ}

theorem im_quad_eq_re_imH (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = (star x ⬝ᵥ imH M *ᵥ x).re := by
  have hq : star x ⬝ᵥ Mᴴ *ᵥ x = star (star x ⬝ᵥ M *ᵥ x) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, dotProduct_mulVec]
  unfold imH
  rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, hq, smul_eq_mul]
  generalize star x ⬝ᵥ M *ᵥ x = q
  rw [Complex.star_def, Complex.sub_conj,
    show ((2 * q.im : ℝ) : ℂ) * I = (2 * I) * (q.im : ℂ) by push_cast; ring,
    inv_mul_cancel_left₀ (mul_ne_zero two_ne_zero I_ne_zero), Complex.ofReal_re]

theorem imH_add_I_smul (Z P : Matrix (Fin N) (Fin N) ℂ) (hP : P.IsHermitian) :
    imH (Z + I • P) = imH Z + P := by
  unfold imH
  rw [conjTranspose_add, conjTranspose_smul, hP.eq]
  have e : Z + I • P - (Zᴴ + star I • P) = (Z - Zᴴ) + (2 * I) • P := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def,
      Complex.conj_I]
    ring
  rw [e, smul_add, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero), one_smul]

theorem imH_mul_denom (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian) :
    imH (C * (C * Z + D)ᴴ) = -(C * imH Z * Cᴴ) := by
  have hDC : D * Cᴴ = C * Dᴴ := by
    have e := h.eq
    rwa [conjTranspose_mul, conjTranspose_conjTranspose] at e
  have e : C * (C * Z + D)ᴴ - (C * (C * Z + D)ᴴ)ᴴ = -(C * (Z - Zᴴ) * Cᴴ) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_add, conjTranspose_mul,
      Matrix.add_mul (C * Z) D Cᴴ, hDC]
    noncomm_ring
  unfold imH
  rw [e, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem im_quad_denom (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (x : Fin N → ℂ) :
    (star x ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ x)).im =
      -(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re := by
  have e : star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x) = star x ⬝ᵥ (C * imH Z * Cᴴ) *ᵥ x := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [e, mulVec_mulVec, im_quad_eq_re_imH, imH_mul_denom C D Z h, neg_mulVec, dotProduct_neg,
    Complex.neg_re]

theorem det_denom_ne_zero (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) : (C * Z + D).det ≠ 0 := by
  intro hdet
  have h0 : ((C * Z + D)ᴴ).det = 0 := by rw [det_conjTranspose, hdet, star_zero]
  obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr h0
  have h1 := im_quad_denom C D Z h x
  rw [hx, mulVec_zero, dotProduct_zero, Complex.zero_im] at h1
  have hCx : Cᴴ *ᵥ x = 0 := by
    by_contra hne
    have h2 := (Complex.pos_iff.mp (hZ.dotProduct_mulVec_pos hne)).1
    linarith
  have hDx : Dᴴ *ᵥ x = 0 := by
    rw [conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec, hCx, mulVec_zero,
      zero_add] at hx
    exact hx
  have h3 := hp.dotProduct_mulVec_pos hx0
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hCx, hDx, mulVec_zero, mulVec_zero, add_zero,
    dotProduct_zero] at h3
  exact lt_irrefl _ h3

theorem norm_det_denom_le_rank_one (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • vecMulVec v (star v)) + D).det‖ := by
  have hW := det_denom_ne_zero C D Z h hp hZ
  have hWh : IsUnit ((C * Z + D)ᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW)
  obtain ⟨y, rfl⟩ : ∃ y, (C * Z + D)ᴴ *ᵥ y = v :=
    ⟨((C * Z + D)ᴴ)⁻¹ *ᵥ v, by rw [mulVec_mulVec, mul_nonsing_inv (A := (C * Z + D)ᴴ) hWh, one_mulVec]⟩
  have hstar : star ((C * Z + D)ᴴ *ᵥ y) = star y ᵥ* (C * Z + D) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  have e1 : I • vecMulVec (C *ᵥ ((C * Z + D)ᴴ *ᵥ y)) (star y ᵥ* (C * Z + D)) =
      vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y) * (C * Z + D) := by
    rw [vecMulVec_mul]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have key : C * (Z + I • vecMulVec ((C * Z + D)ᴴ *ᵥ y) (star ((C * Z + D)ᴴ *ᵥ y))) + D =
      (1 + vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y)) * (C * Z + D) := by
    rw [hstar, Matrix.mul_add C, Matrix.mul_smul C, mul_vecMulVec C, e1,
      Matrix.add_mul (1 : Matrix (Fin N) (Fin N) ℂ), Matrix.one_mul]
    abel
  have hs : (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y)).im ≤ 0 := by
    rw [im_quad_denom C D Z h y]
    have h0 := (Complex.nonneg_iff.mp (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ y))).1
    linarith
  have hone : 1 ≤ ‖1 + I * (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y))‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub]
    linarith
  rw [key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) hone

private theorem exists_eq_sum_vecMulVec_star {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (hP : P.PosSemidef) :
    ∃ w : Fin N → Fin N → ℂ, P = ∑ k, vecMulVec (w k) (star (w k)) := by
  refine ⟨fun k i => (Real.sqrt (hP.1.eigenvalues k) : ℂ) *
    (hP.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i k, ?_⟩
  have hspec := hP.1.spectral_theorem
  ext i j
  conv_lhs => rw [hspec]
  rw [Unitary.conjStarAlgAut_apply, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, star_mul', Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsq : ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) * (Real.sqrt (hP.1.eigenvalues k) : ℂ) =
      (RCLike.ofReal (hP.1.eigenvalues k) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hP.eigenvalues_nonneg k)]
    rfl
  have hs : star ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) = (Real.sqrt (hP.1.eigenvalues k) : ℂ) :=
    Complex.conj_ofReal _
  rw [Matrix.star_apply, hs, ← hsq]
  ring

theorem norm_det_denom_mono :
    ∀ (N : ℕ) (C D Z P : Matrix (Fin N) (Fin N) ℂ), (C * Dᴴ).IsHermitian → (C * Cᴴ + D * Dᴴ).PosDef → (imH Z).PosDef → P.PosSemidef → (C * Z + D).det ≠ 0 ∧ ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • P) + D).det‖ := by
  intro N C D Z P h hp hZ hP
  refine ⟨det_denom_ne_zero C D Z h hp hZ, ?_⟩
  obtain ⟨w, rfl⟩ := exists_eq_sum_vecMulVec_star P hP
  have gen : ∀ s : Finset (Fin N),
      (imH (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k)))).PosDef ∧
        ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k))) + D).det‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, smul_zero, add_zero]
      exact ⟨hZ, le_rfl⟩
    | insert k s hk ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rw [Finset.sum_insert hk, add_comm (vecMulVec _ _) _, smul_add, ← add_assoc]
      refine ⟨?_, ?_⟩
      · rw [imH_add_I_smul _ _ (posSemidef_vecMulVec_self_star (w k)).isHermitian]
        exact ih1.add_posSemidef (posSemidef_vecMulVec_self_star (w k))
      · exact ih2.trans (norm_det_denom_le_rank_one C D _ h hp ih1 (w k))
  exact (gen Finset.univ).2

end GlobalTheory.SW
end

section

open Matrix Complex Unitary
open scoped ComplexOrder

namespace GlobalTheory.PosSemidefShiftByScalar

theorem posSemidef_sub_smul_one {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ δ' : ℝ, δ' ≤ δ → (A - (δ' : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hH := hA.isHermitian
  obtain ⟨δ, hδ, hle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ hH.eigenvalues i := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ :=
        Finset.exists_min_image Finset.univ hH.eigenvalues Finset.univ_nonempty
      exact ⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  refine ⟨δ, hδ, fun δ' hδ' => ?_⟩
  have e : A - (δ' : ℂ) • (1 : Matrix n n ℂ) = conjStarAlgAut ℂ _ hH.eigenvectorUnitary
      (diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ))) := by
    have d : diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ)) =
        diagonal (RCLike.ofReal ∘ hH.eigenvalues) - (δ' : ℂ) • (1 : Matrix n n ℂ) := by
      ext i j; by_cases h : i = j <;> simp [diagonal, one_apply, h]
    conv_lhs => rw [hH.spectral_theorem]
    rw [d, map_sub, map_smul, map_one]
  rw [e, conjStarAlgAut_apply, isUnit_coe.posSemidef_star_right_conjugate_iff]
  exact PosSemidef.diagonal fun i =>
    Complex.zero_le_real.2 (sub_nonneg.2 (hδ'.trans (hle i)))

theorem exists_pos_mem_HnGe {N : ℕ} {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    {Z : GlobalTheory.SW.CM Ψ N N} (hZ : Z ∈ GlobalTheory.SW.Hn Ψ N) :
    ∃ δ : ℝ, (0 : ℝ) < δ ∧ Z ∈ GlobalTheory.SW.HnGe Ψ N δ := by
  choose d hd h using fun τ : Ψ => posSemidef_sub_smul_one (hZ τ)
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
  · obtain ⟨τ0, -, hτ0⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
    exact ⟨d τ0, hd τ0, fun τ => h τ _ (hτ0 τ (Finset.mem_univ τ))⟩

theorem main : ∀ {N : ℕ} {E : Type} [inst : Field E] (Ψ : Finset (E →+* ℂ)) {Z : GlobalTheory.SW.CM Ψ N N},
    Z ∈ GlobalTheory.SW.Hn Ψ N → ∃ (δ : ℝ), (0 : ℝ) < δ ∧ Z ∈ GlobalTheory.SW.HnGe Ψ N δ :=
  fun Ψ _ hZ => exists_pos_mem_HnGe Ψ hZ

end GlobalTheory.PosSemidefShiftByScalar
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem exists_int_div_of_intM {κ ι : Type} (R S : ℕ) (hR : 0 < R) (hS : 0 < S)
    (x : Matrix κ ι ℚ) (h : IntM ((R : ℚ) • x)) :
    ∃ s : κ × ι → ℤ, (Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)) = x := by
  have h' : ∀ p : κ × ι, ∃ n : ℤ, (n : ℚ) = (R : ℚ) * x p.1 p.2 := by
    intro p
    have := h p.1 p.2
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    exact ⟨n, by simpa using hn⟩
  choose n hn using h'
  refine ⟨fun p => n p * S, ?_⟩
  ext k i
  have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hS' : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  simp only [Matrix.of_apply]
  push_cast
  rw [hn (k, i)]
  field_simp

theorem eq_of_thS_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  intro κ ι _ _ _ φ ψ hφ hψ τ hτ h
  obtain ⟨R, hR, hRφ, -⟩ := id hφ
  obtain ⟨S, hS, hSψ, -⟩ := id hψ
  have hN : (((R * S : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  have hNC : (((R * S : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  let e : (κ × ι → ℤ) → Matrix κ ι ℚ := fun s =>
    Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)
  have he : Function.Injective e := by
    intro s t hst
    funext p
    have := congrFun (congrFun hst p.1) p.2
    simp only [e, Matrix.of_apply] at this
    have := (div_left_inj' hN).1 this
    exact_mod_cast this
  have hrange : ∀ x, φ x - ψ x ≠ 0 → x ∈ Set.range e := by
    intro x hx
    by_cases h1 : φ x = 0
    · have h2 : ψ x ≠ 0 := by
        intro h2; exact hx (by rw [h1, h2, sub_zero])
      obtain ⟨s, hs⟩ := exists_int_div_of_intM S R hS hR x (hSψ x h2)
      exact ⟨s, by rw [← hs, Nat.mul_comm S R]⟩
    · exact exists_int_div_of_intM R S hR hS x (hRφ x h1)
  let E : (κ → ι → ℂ) → Matrix κ ι ℚ → ℂ := fun ζ x =>
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))
  have hsφ : ∀ ζ, Summable fun x => φ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ).of_norm
  have hsψ : ∀ ζ, Summable fun x => ψ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι ψ hψ τ hτ ζ).of_norm
  have hs : ∀ ζ, Summable fun x => (φ x - ψ x) * E ζ x := fun ζ => by
    simpa only [sub_mul] using (hsφ ζ).sub (hsψ ζ)
  have hz : ∀ ζ, ∑' x, (φ x - ψ x) * E ζ x = 0 := fun ζ => by
    simp only [sub_mul]
    rw [(hsφ ζ).tsum_sub (hsψ ζ)]
    exact sub_eq_zero.2 (h ζ)
  have key := GlobalTheory.coeff_eq_zero_of_fourier_series_eq_zero (κ × ι)
    (fun s => (φ (e s) - ψ (e s)) * E 0 (e s))
    (((hs 0).comp_injective he).norm) (by
      intro y
      have h0 := hz (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ))
      rw [← he.tsum_eq (f := fun x => (φ x - ψ x) * E (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) x)
        (by
          intro x hx
          exact hrange x (left_ne_zero_of_mul hx))] at h0
      rw [← h0]
      refine tsum_congr fun s => ?_
      rw [mul_assoc]
      congr 1
      simp only [E]
      rw [← Complex.exp_add]
      congr 1
      have : ∀ k, qv (e s k) ⬝ᵥ (fun i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) =
          ∑ i, (s (k, i) : ℂ) * (y (k, i) : ℂ) := by
        intro k
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [qv, e, Matrix.of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
        field_simp
      simp only [this, Pi.zero_apply, dotProduct_zero, mul_zero, add_zero, Finset.sum_add_distrib,
        ← Finset.mul_sum, Fintype.sum_prod_type]
      ring)
  funext x
  by_contra hx
  obtain ⟨s, rfl⟩ := hrange x (sub_ne_zero.2 hx)
  have := key s
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hx (sub_eq_zero.1 h1)
  · exact Complex.exp_ne_zero _ h1

end GlobalTheory.SW
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.schwartzBruhatInvariantIntegral_matrix_mul : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] [DecidableEq ι] [DecidableEq κ] (φ : Matrix κ ι K → ℂ), IsSB φ → (∀ A : Matrix ι ι K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (x * A)) ∧ haar (fun x : Matrix κ ι K => φ (x * A)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card κ * haar φ) ∧ ∀ A : Matrix κ κ K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (A * x)) ∧ haar (fun x : Matrix κ ι K => φ (A * x)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card ι * haar φ := by
  first | exact @GlobalTheory.SW.LinChange.haar_mul | exact GlobalTheory.SW.LinChange.haar_mul | (intros; apply GlobalTheory.SW.LinChange.haar_mul <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.exists_symplectic_action_of_period_lattice_map : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ))), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) → ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm → (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) → τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by
  first | exact @GlobalTheory.SymplecticPeriods.exists_symplectic_action | exact GlobalTheory.SymplecticPeriods.exists_symplectic_action | (intros; apply GlobalTheory.SymplecticPeriods.exists_symplectic_action <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.canonicalThetaExponent_symplectic_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  first | exact @GlobalTheory.SW.canon_exponent_invariant | exact GlobalTheory.SW.canon_exponent_invariant | (intros; apply GlobalTheory.SW.canon_exponent_invariant <;> assumption)
end
