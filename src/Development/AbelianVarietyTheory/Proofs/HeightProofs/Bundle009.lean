module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
import Mathlib.Algebra.GroupWithZero.Torsion
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Pointwise Formalism.L2.Pj.QAt GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.DefectSumCompare

theorem pow_finrank_eq_span_absNorm {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hfix : ∀ σ : E ≃ₐ[ℚ] E, σ • I = I) :
    I ^ Module.finrank ℚ E = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} := by
  classical
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have hprin : (I ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨x, hx⟩ := hprin
  have hx' : I ^ h = Ideal.span {x} := hx
  have hσ : ∀ σ : E ≃ₐ[ℚ] E, Ideal.span {σ • x} = I ^ h := by
    intro σ
    have : σ • (I ^ h) = I ^ h := by rw [smul_pow', hfix]
    rw [← this, hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 E) = ∏ σ : E ≃ₐ[ℚ] E, σ • x := by
    apply RingOfIntegers.ext
    have h1 := Algebra.norm_eq_prod_automorphisms ℚ (x : E)
    rw [← Algebra.coe_norm_int] at h1
    change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [map_prod, map_intCast]
    rw [map_intCast] at h1
    exact h1
  have h2 : Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} ^ h = (I ^ Module.finrank ℚ E) ^ h := by
    rw [Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]
    have h3 : Ideal.span {(((Algebra.norm ℤ x).natAbs : ℕ) : 𝓞 E)} =
        Ideal.span {((Algebra.norm ℤ x : ℤ) : 𝓞 E)} := by
      rcases Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4
      · conv_rhs => rw [h4]
        rw [Int.cast_natCast]
      · conv_rhs => rw [h4]
        rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
    rw [h3, hnorm, ← Ideal.prod_span_singleton]
    simp only [hσ]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      ← pow_mul, ← pow_mul, mul_comm]
  exact (pow_left_injective hpos h2).symm

theorem ord_vw_eq_vla {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : ord_vw la I = vla la I := by
  classical
  unfold ord_vw vla
  rw [Ideal.count_associates_factors_eq hI la.isPrime la.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI]

theorem lrd_eq_lrdOf (E : Type) [Field E] [NumberField E] : lrd E = lrdOf E := by
  unfold lrd lrdOf
  rw [rootDiscr_def, one_div, Int.cast_abs]

theorem log_discr_eq (E : Type) [Field E] [NumberField E] :
    Real.log |((discr E : ℤ) : ℝ)| = (Module.finrank ℚ E : ℝ) * lrd E := by
  have hd : (0 : ℝ) < |((discr E : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [lrd_eq_lrdOf]
  unfold lrdOf
  rw [Real.log_rpow hd]
  field_simp

theorem conjDifferent_pow {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ^ Module.finrank ℚ E = discAt E K := by
  unfold conjDifferent discAt
  rw [← Ideal.map_pow, pow_finrank_eq_span_absNorm _ differentIdeal_ne_bot
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.smul_differentIdeal, absNorm_differentIdeal E, Ideal.map_span,
    Set.image_singleton, map_natCast]

theorem vla_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (k : ℕ) : vla la (I ^ k) = k * vla la I := by
  unfold vla
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr hI) la.associates_irreducible]

section Galois

variable {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]

theorem vla_discAt (σ : E →+* K) (la : HeightOneSpectrum (𝓞 K)) :
    vla la (discAt E K) = Module.finrank ℚ E * ord_vw la (conjDifferent σ) := by
  rw [← conjDifferent_pow σ, vla_pow la (conjDifferent_ne_bot σ), ord_vw_eq_vla la (conjDifferent_ne_bot σ)]

end Galois

end GlobalTheory.DefectSumCompare
end

section

open Matrix

namespace GlobalTheory.MonomialDiag

private theorem star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      if 0 < x then (1 : ℂ) else -1 := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [star_inv₀, hst,
    show ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      ((x / (Real.sqrt |x| * Real.sqrt |x|) : ℝ) : ℂ) by push_cast; ring, hs]
  split_ifs with h
  · rw [abs_of_pos h, div_self hx, Complex.ofReal_one]
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx), div_neg_self hx]
    push_cast
    ring

private theorem star_sqrt_abs_mul_sign_mul_sqrt_abs_eq (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ) * (if 0 < x then (1 : ℂ) else -1) * ((Real.sqrt |x| : ℝ) : ℂ) =
      (x : ℂ) := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [hst]
  split_ifs with h
  · rw [mul_one, ← Complex.ofReal_mul, hs, abs_of_pos h]
  · rw [mul_neg_one, neg_mul, ← Complex.ofReal_mul, hs, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx)]
    push_cast
    ring

private theorem Jpq_equiv_apply_eq_ite_sign {n p q : ℕ} (d : Fin n → ℝ) (e : Fin n ≃ Fin p ⊕ Fin q)
    (he : ∀ i, 0 < d i ↔ (e i).isLeft = true) (i j : Fin n) :
    Formalism.UG.Jpq p q (e i) (e j) = if i = j then (if 0 < d i then (1 : ℂ) else -1) else 0 := by
  unfold Formalism.UG.Jpq
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hi := he i
    revert hi
    generalize e i = x
    rcases x with a | a <;> intro hi <;> simp_all
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    rw [if_neg hij]
    revert hne
    generalize e i = x
    generalize e j = y
    rcases x with a | a <;> rcases y with b | b <;> intro hne <;> simp_all

private theorem conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (C : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (hC : ∀ i a, C i a = if i = e.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) :
    Cᴴ * Matrix.diagonal (fun i => (d i : ℂ)) * C = Formalism.UG.Jpq p q := by
  ext a b
  have key := Jpq_equiv_apply_eq_ite_sign d e he (e.symm a) (e.symm b)
  rw [e.apply_symm_apply, e.apply_symm_apply] at key
  rw [key, Matrix.mul_apply, Finset.sum_eq_single (e.symm b)]
  · rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, hC, hC]
    simp only [↓reduceIte]
    by_cases hab : e.symm a = e.symm b
    · rw [if_pos hab.symm, if_pos hab, hab]
      exact star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign _ (hd _)
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero, zero_mul, zero_mul]
  · intro i _ hi
    rw [hC i b, if_neg hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : ∀ a i, B a i = if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0) :
    Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e i)]
    · rw [Matrix.conjTranspose_apply, hB, hB]
      simp only [↓reduceIte]
      rw [Jpq_equiv_apply_eq_ite_sign d e he, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        exact star_sqrt_abs_mul_sign_mul_sqrt_abs_eq _ (hd _)
      · rw [if_neg hij, if_neg hij, mul_zero, zero_mul]
    · intro b _ hb
      rw [Matrix.conjTranspose_apply, hB, if_neg hb, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    rw [hB a j, if_neg ha, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_monomial : ∀ (n p q : ℕ) (G Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Formalism.UG.HasSignature G p q → Q.det ≠ 0 → (∀ i, d i ≠ 0) → Qᴴ * G * Q = Matrix.diagonal (fun i => (d i : ℂ)) → ∃ A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G ∧ ∀ a i j, (A * Q) a i ≠ 0 → (A * Q) a j ≠ 0 → i = j := by
  intro n p q G Q d hG hQ hd hQG
  classical
  obtain ⟨hcard, Q₁, hQ₁⟩ := Formalism.UG.P.sig_data G p q hG
  rw [Fintype.card_fin] at hcard

  let e₀ : Fin n ≃ Fin (Fintype.card {i // 0 < d i}) ⊕ Fin (Fintype.card {i // ¬ 0 < d i}) :=
    (Equiv.sumCompl (fun i => 0 < d i)).symm.trans
      (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))
  have he₀ : ∀ i, 0 < d i ↔ (e₀ i).isLeft = true := by
    intro i
    by_cases h : 0 < d i
    · simp [e₀, h]
    · simp [e₀, h]
  have hn₀ : n = Fintype.card {i // 0 < d i} + Fintype.card {i // ¬ 0 < d i} := by
    simpa using Fintype.card_congr e₀

  have h₂ : (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
      G * (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0)) =
      Formalism.UG.Jpq _ _ := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
          (Qᴴ * G * Q) * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hQG]
          exact conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq d hd e₀ he₀ _ (fun i a => rfl)
  have i1 := Formalism.UG.P.sig_dim G Q₁ hQ₁ _ h₂
  have i2 := Formalism.UG.P.sig_dim G _ h₂ Q₁ hQ₁
  rw [Fintype.card_fin] at i1 i2
  have hp : Fintype.card {i // 0 < d i} = p := by omega
  have hq : Fintype.card {i // ¬ 0 < d i} = q := by omega
  let e : Fin n ≃ Fin p ⊕ Fin q := e₀.trans (Equiv.sumCongr (finCongr hp) (finCongr hq))
  have he : ∀ i, 0 < d i ↔ (e i).isLeft = true := by
    intro i
    rw [he₀ i]
    simp only [e, Equiv.trans_apply]
    cases e₀ i <;> rfl
  let B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
    Matrix.of (fun a i => if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0)
  have hB : Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) :=
    conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal d hd e he B (fun a i => rfl)
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ
  have hQQ : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQu
  have hQQ' : (Q⁻¹)ᴴ * Qᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
  refine ⟨B * Q⁻¹, ?_, ?_⟩
  · calc (B * Q⁻¹)ᴴ * Formalism.UG.Jpq p q * (B * Q⁻¹) = (Q⁻¹)ᴴ * (Bᴴ * Formalism.UG.Jpq p q * B) * Q⁻¹ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (Q⁻¹)ᴴ * (Qᴴ * G * Q) * Q⁻¹ := by rw [hB, hQG]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * G * (Q * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hQQ', hQQ, Matrix.one_mul, Matrix.mul_one]
  · intro a i j hi hj
    have hBQ : B * Q⁻¹ * Q = B := by
      rw [Matrix.mul_assoc, Q.nonsing_inv_mul hQu, Matrix.mul_one]
    rw [hBQ] at hi hj
    have hai : a = e i := by
      by_contra h
      exact hi (by simp [B, h])
    have haj : a = e j := by
      by_contra h
      exact hj (by simp [B, h])
    exact e.injective (hai.symm.trans haj)

end GlobalTheory.MonomialDiag
end

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.QuadNormBase

theorem norm_of_basis {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (B : Module.Basis (Fin 2) R A) (d : R) (h0 : B 0 = 1) (h1 : B 1 * B 1 = d • B 0) (x y : R) :
    Algebra.norm R (x • B 0 + y • B 1) = x ^ 2 - d * y ^ 2 := by
  have e0 : (x • B 0 + y • B 1) * B 0 = x • B 0 + y • B 1 := by rw [h0, mul_one]
  have e1 : (x • B 0 + y • B 1) * B 1 = (y * d) • B 0 + x • B 1 := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h1, smul_smul, add_comm]
    congr 1
    rw [h0, one_mul]
  rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  simp
  ring

theorem exists_basis (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    ∃ (δ : F) (b : Module.Basis (Fin 2) F E), ¬ IsSquare δ ∧ b 0 = 1 ∧ σ (b 1) = - b 1 ∧
      b 1 * b 1 = algebraMap F E δ := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨x0, hx0⟩ := hne
  have hsm : ∀ (c : F) (e : E), σ (c • e) = c • σ e := fun c e => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
  set θ : E := x0 - σ x0 with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 hx0.symm
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hσ]; ring
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg σ hst
    rw [map_add (f := _), hsm, hsm, map_one, hσθ, map_zero, smul_neg] at h2
    have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hst - h2
    have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
    have ht : t = 0 := (smul_eq_zero.1 h4).resolve_right hθ0
    subst ht
    exact ⟨by simpa using hst, rfl⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = θ := by simp [b]
  have hrep := b.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hb0, hb1] at hrep
  set s := b.repr (θ * θ) 0
  set t := b.repr (θ * θ) 1
  have h2 := congrArg σ hrep
  rw [map_add (f := _), hsm, hsm, map_one, map_mul, hσθ, smul_neg] at h2
  have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hrep - h2
  have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
  have hsq : θ * θ = algebraMap F E s := by
    rw [← hrep, h4, add_zero, Algebra.algebraMap_eq_smul_one]
  refine ⟨s, b, ?_, hb0, by rw [hb1, hσθ], by rw [hb1, hsq]⟩
  rintro ⟨r, hr⟩
  rw [hr, map_mul, mul_self_eq_mul_self_iff] at hsq
  have hfix : σ θ = θ := by
    rcases hsq with h | h
    · rw [h, AlgHom.commutes]
    · rw [h, map_neg, AlgHom.commutes]
  have h5 : (2 : E) * θ = 0 := by linear_combination hσθ - hfix
  exact hθ0 (by simpa only [mul_eq_zero, two_ne_zero, false_or] using h5)

theorem norm_form : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ∃ δ : F, ¬ IsSquare δ ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ z : R ⊗[F] E, ∃ x y : R, Algebra.norm R z = x ^ 2 - algebraMap F R δ * y ^ 2 ∧ z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) ∧ ∀ x y : R, ∃ z : R ⊗[F] E, z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
  intro F E _ _ _ _ σ hr hσ hne
  obtain ⟨δ, b, hδ, hb0, hb1, hsq⟩ := exists_basis F E σ hr hσ hne
  refine ⟨δ, hδ, ?_⟩
  intro R _ _
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have h1 : B 1 * B 1 = algebraMap F R δ • B 0 := by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, one_mul, algebraMap_smul]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) =
      algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
    intro x y
    have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
      rw [map_add (f := _), hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
        map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
    rw [e]
    rw [h0] at h1 ⊢
    generalize algebraMap F R δ = d at h1 ⊢
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢
    linear_combination (-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1
  refine ⟨fun z => ?_, fun x y => ⟨_, key x y⟩⟩
  have hz := B.sum_repr z
  rw [Fin.sum_univ_two] at hz
  refine ⟨B.repr z 0, B.repr z 1, ?_, ?_⟩
  · rw [← norm_of_basis B _ h0 h1, hz]
  · rw [← key, hz]

end GlobalTheory.QuadNormBase
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.commuting_algebras_finite_span : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Finite ι] (A : ι → Subalgebra ℂ (Module.End ℂ M)), (∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) → ∀ m : M, (∀ i, FiniteDimensional ℂ (Submodule.span ℂ {x : M | ∃ a ∈ A i, x = a m})) → ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧ ∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W := by
  first | exact @GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable | exact GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable | (intros; apply GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable <;> assumption)
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ)) (N : Submodule ℂ (Matrix ι ι ℂ)), (∀ x ∈ S, xᴴ ∈ S) → (∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N) → ∀ M : Matrix ι ι ℂ, (∀ x ∈ S, x * M - M * x ∈ N) → ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ x ∈ S, x * M₀ = M₀ * x := by
  first | exact @GlobalTheory.matrix_commutant_lift_mod_stable | exact GlobalTheory.matrix_commutant_lift_mod_stable | (intros; apply GlobalTheory.matrix_commutant_lift_mod_stable <;> assumption)
end
