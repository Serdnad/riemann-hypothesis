module

public import Formalism.CyclotomicNorms.StatementT
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle002
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness

@[expose] public section

section

open Polynomial

noncomputable section

namespace GlobalTheory.TeichGalois

variable {g : ℕ} [Fact g.Prime]

theorem map_zero_eq_zero (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h2 : t 0 * (t 0 - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, mul_zero, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exfalso
    have h1 : t 0 = 1 := sub_eq_zero.1 h
    have hall : ∀ x, t x = 1 := fun x => by
      have : t (x * 0) = t x * t 0 := map_mul t x 0
      rw [mul_zero, h1, mul_one] at this
      exact this.symm
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    exact hy.2 (ht y 1 hy.1 one_ne_zero (by rw [hall, hall]))

theorem exists_coprime_pow_eq_one {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) :
    ∃ m : ℕ, g.Coprime m ∧ x ^ m = 1 := by
  let K := IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g))
  haveI : FiniteDimensional (ZMod g) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  have hxK : (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : K) ≠ 0 := by
    intro h; apply hx; simpa using congrArg Subtype.val h
  let u := Units.mk0 _ hxK
  have hn : x ^ orderOf u = 1 := by
    have h3 : (u : K) ^ orderOf u = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    have h4 : ((u : K) : Formalism.CyclotomicNorms.Fbar g) ^ orderOf u = 1 := by
      rw [← IntermediateField.coe_pow, h3, IntermediateField.coe_one]
    exact h4
  have hpos : 0 < orderOf u := orderOf_pos u
  obtain ⟨a, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' g (Fact.out : g.Prime).ne_one
  refine ⟨m, (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm, ?_⟩
  have h2 : (x ^ m - 1) ^ (g ^ a) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, ← heq, hn, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : g.Prime).ne_zero) |>.1 h2)

theorem exists_common_exponent (s : Finset (Formalism.CyclotomicNorms.Fbar g)) (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ m : ℕ, g.Coprime m ∧ ∀ x ∈ s, x ^ m = 1 := by
  have h := fun x (hx : x ∈ s) => exists_coprime_pow_eq_one (hs x hx)
  choose! e he using h
  refine ⟨∏ x ∈ s, e x, Nat.Coprime.prod_right fun x hx => (he x hx).1, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem e hx
  rw [hc, pow_mul, (he x hx).2, one_pow]

theorem isPrimitiveRoot_map (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) {u : Formalism.CyclotomicNorms.Fbar g} {m : ℕ}
    (hm : 0 < m) (hu : IsPrimitiveRoot u m) : IsPrimitiveRoot (t u) m := by
  have hu0 : u ≠ 0 := hu.ne_zero hm.ne'
  refine ⟨by rw [← map_pow, hu.pow_eq_one, map_one], fun l hl => hu.dvd_of_pow_eq_one l ?_⟩
  exact ht _ _ (pow_ne_zero _ hu0) one_ne_zero (by rw [map_pow, hl, map_one])

theorem lift_apply_eq_sum (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (f : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) :
    MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t f = ∑ x ∈ f.coeff.support, (f.coeff x : ℂ) * t x := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum]
  simp [zsmul_eq_mul]

theorem lift_eq_zero_of_lift_eq_zero (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ht' : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y)
    (f : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) (h : MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t' f = 0) :
    MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t f = 0 := by
  classical
  set s := f.coeff.support.filter (· ≠ 0) with hs
  obtain ⟨m, hmc, hpow⟩ := exists_common_exponent s (fun x hx => (Finset.mem_filter.1 hx).2)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : g.Prime).ne_one (Nat.coprime_zero_right _ |>.1 hmc)
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  haveI : NeZero m := ⟨hm0⟩
  haveI : NeZero (m : Formalism.CyclotomicNorms.Fbar g) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff (Formalism.CyclotomicNorms.Fbar g) g]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hmc⟩
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (cyclotomic m (Formalism.CyclotomicNorms.Fbar g))
    (degree_cyclotomic_pos m _ hm).ne'
  have hu : IsPrimitiveRoot u m := isRoot_cyclotomic_iff.1 hu
  have hk : ∀ x ∈ s, ∃ i : ℕ, u ^ i = x := fun x hx => by
    obtain ⟨i, -, hi⟩ := hu.eq_pow_of_pow_eq_one (hpow x hx)
    exact ⟨i, hi⟩
  choose! k hk using hk
  let P : ℤ[X] := ∑ x ∈ s, C (f.coeff x) * X ^ (k x)
  have heval : ∀ τ : Formalism.CyclotomicNorms.Fbar g →* ℂ, τ 0 = 0 →
      MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) τ f = aeval (τ u) P := by
    intro τ hτ
    rw [lift_apply_eq_sum, ← Finset.sum_filter_of_ne (p := (· ≠ 0)) (fun x _ hx h0 => hx (by rw [h0, hτ, mul_zero]))]

    simp only [P, map_sum, map_mul, aeval_C, map_pow, aeval_X, algebraMap_int_eq, eq_intCast, map_intCast]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← map_pow, hk x hx]
  have hζ := isPrimitiveRoot_map t ht hm hu
  have hζ' := isPrimitiveRoot_map t' ht' hm hu
  have h1 : aeval (t' u) P = 0 := by rw [← heval t' (map_zero_eq_zero t' ht'), h]
  have hdvd : minpoly ℤ (t' u) ∣ P := minpoly.isIntegrallyClosed_dvd (hζ'.isIntegral hm) h1
  rw [← cyclotomic_eq_minpoly hζ' hm, cyclotomic_eq_minpoly hζ hm] at hdvd
  rw [heval t (map_zero_eq_zero t ht)]
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (t u))

instance countable_fbar : Countable (Formalism.CyclotomicNorms.Fbar g) :=
  Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).trans
    (max_le Cardinal.mk_le_aleph0 le_rfl))

theorem exists_ringEquiv_comp_eq : ∀ (g : ℕ) [Fact g.Prime] (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) → ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (t' x) = t x := by
  intro g _ t t' ht ht'
  let α : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) →+* ℂ := (MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t').toRingHom
  let β : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) →+* ℂ := (MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t).toRingHom
  have hker : RingHom.ker α ≤ RingHom.ker β := fun f hf =>
    lift_eq_zero_of_lift_eq_zero t t' ht ht' f hf
  have hker' : RingHom.ker β ≤ RingHom.ker α := fun f hf =>
    lift_eq_zero_of_lift_eq_zero t' t ht' ht f hf
  haveI : (RingHom.ker α).IsPrime := RingHom.ker_isPrime α
  let Q := MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) ⧸ RingHom.ker α
  let α' : Q →+* ℂ := RingHom.kerLift α
  let β' : Q →+* ℂ := Ideal.Quotient.lift (RingHom.ker α) β hker
  have hα' : Function.Injective α' := RingHom.kerLift_injective α
  have hβ' : Function.Injective β' := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    have : β f = 0 := hq
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hker' this)
  haveI : Countable (MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) :=
    Function.Injective.countable (f := MonoidAlgebra.coeff) (fun a b h => by ext x; rw [h])
  haveI : Countable Q := Function.Surjective.countable Ideal.Quotient.mk_surjective
  haveI : Countable (FractionRing Q) :=
    Function.Surjective.countable (IsLocalization.mk'_surjective (nonZeroDivisors Q) (S := FractionRing Q))
  let a : FractionRing Q →+* ℂ := IsFractionRing.lift hα'
  let b : FractionRing Q →+* ℂ := IsFractionRing.lift hβ'
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq a b
  refine ⟨σ, fun x => ?_⟩
  have h := hσ (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1)))
  have ha : a (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1))) = t' x := by
    simp only [a]
    rw [IsFractionRing.lift_algebraMap]
    simp only [α']
    rw [RingHom.kerLift_mk]
    simp [α, MonoidAlgebra.lift_single]
  have hb : b (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1))) = t x := by
    simp only [b]
    rw [IsFractionRing.lift_algebraMap]
    show β (MonoidAlgebra.single x 1) = t x
    simp [β, MonoidAlgebra.lift_single]
  rw [ha, hb] at h
  exact h

end GlobalTheory.TeichGalois
end
end

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.HaarDensityUpq

def toL1 (P Q : ℕ) : lieU P Q →ₗ[ℝ] PiLp 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) where
  toFun X := WithLp.toLp 1 (entries (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toL1_injective (P Q : ℕ) : Function.Injective (toL1 P Q) := by
  intro X Y h
  ext i j
  exact congrFun (congrArg WithLp.ofLp h) (i, j)

theorem isInducing_toL1 (P Q : ℕ) : IsInducing (toL1 P Q) := by
  have h1 : IsInducing (entries : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → _) :=
    (Homeomorph.piCurry (X := Fin P ⊕ Fin Q) (Y := Fin P ⊕ Fin Q) (Z := ℂ)).symm.isInducing
  exact (PiLp.homeomorph 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ)).symm.isInducing.comp
    (h1.comp IsInducing.subtypeVal)

@[reducible] def sumNorm (P Q : ℕ) : NormedAddCommGroup (lieU P Q) :=
  let N := NormedAddCommGroup.induced (lieU P Q) _ (toL1 P Q) (toL1_injective P Q)
  { toNorm := N.toNorm
    toAddCommGroup := inferInstance
    toMetricSpace := N.toMetricSpace.replaceTopology (isInducing_toL1 P Q).eq_induced
    dist_eq := N.dist_eq }

theorem mat_mul {P Q : ℕ} (g h : UpqT P Q) : (g * h).mat = g.mat * h.mat := rfl

end GlobalTheory.HaarDensityUpq
end
end

section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory

theorem Jpq_zero_left_eq_neg_one (q : ℕ) : Formalism.UG.Jpq 0 q = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact i.elim0
  · exact i.elim0
  · exact j.elim0
  · simp [Formalism.UG.Jpq, Matrix.one_apply]

theorem isCompact_Upq_zero_left (q : ℕ) :
    IsCompact (Formalism.UG.Upq 0 q : Set (GL (Fin 0 ⊕ Fin q) ℂ)) := by
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Fin 0 ⊕ Fin q)
    (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const) (fun _ h => h)
  convert hc using 1
  ext g
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  rw [Formalism.UG.P.mem_Upq_iff, Jpq_zero_left_eq_neg_one, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, neg_inj]

theorem compactSpace_UpqT_definite :
    ∀ N : ℕ, CompactSpace (UpqT N 0) ∧ CompactSpace (UpqT 0 N) := fun N =>
  ⟨(isCompact_iff_compactSpace.1 (Formalism.UG.P.indefinite_unitary_compact N) :
      CompactSpace (Formalism.UG.Upq N 0 : Set (GL (Fin N ⊕ Fin 0) ℂ))),
    (isCompact_iff_compactSpace.1 (isCompact_Upq_zero_left N) :
      CompactSpace (Formalism.UG.Upq 0 N : Set (GL (Fin 0 ⊕ Fin N) ℂ)))⟩

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory.DefiniteFrame

theorem exists_frame {n p q : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature J p q) :
    ∃ (e : Fin n ≃ Fin p ⊕ Fin q) (B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det ∧
      J = Bᴴ * (Formalism.UG.Jpq p q).submatrix e e * B := by
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e J) * P.val = Formalism.UG.Jpq p q := hP
  refine ⟨e, (P⁻¹).val.submatrix e e, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  · have h1 := Units.mul_inv P
    have h2 : (P⁻¹).valᴴ * P.valᴴ = 1 := by
      rw [← conjTranspose_mul, h1, conjTranspose_one]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, ← hP']
    have h3 : (P⁻¹).valᴴ *
        (P.valᴴ * (reindex e e J) * P.val) *
        (P⁻¹).val = reindex e e J := by
      calc _ = ((P⁻¹).valᴴ * P.valᴴ) * (reindex e e J) *
          (P.val * (P⁻¹).val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rw [h3]
    ext i j
    simp

theorem isCompact_UH_gram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hB : IsUnit B.det) :
    IsCompact (Formalism.QuantumDeterminants.UH (Bᴴ * B)) := by
  have hc : Continuous fun u : Matrix (Fin n) (Fin n) ℂ => B⁻¹ * u * B :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hB
  have h1' : B⁻¹ * B = 1 := nonsing_inv_mul B hB
  have h2 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h2' : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1', conjTranspose_one]
  convert (GlobalTheory.isCompact_unitaryGroup (Fin n) ℂ).image hc using 1
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe,
    Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  constructor
  · intro hg
    refine ⟨B * g * B⁻¹, ?_, ?_⟩
    · calc (B * g * B⁻¹)ᴴ * (B * g * B⁻¹) = (B⁻¹)ᴴ * (gᴴ * (Bᴴ * B) * g) * B⁻¹ := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) := by rw [hg]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, h2, Matrix.one_mul]
    · calc B⁻¹ * (B * g * B⁻¹) * B = (B⁻¹ * B) * g * (B⁻¹ * B) := by
            simp only [Matrix.mul_assoc]
        _ = g := by rw [h1', Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨u, hu, rfl⟩
    calc (B⁻¹ * u * B)ᴴ * (Bᴴ * B) * (B⁻¹ * u * B)
        = Bᴴ * (uᴴ * ((B⁻¹)ᴴ * Bᴴ) * (B * B⁻¹) * u) * B := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ * B := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hu, Matrix.mul_one]

theorem UH_neg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp [Formalism.QuantumDeterminants.UH]

theorem definite_frame (n p q : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (h : Formalism.UG.HasSignature J p q) (hpq : p = 0 ∨ q = 0) :
    (∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ (J = Bᴴ * B ∨ J = -(Bᴴ * B))) ∧
      IsCompact (Formalism.QuantumDeterminants.UH J) := by
  obtain ⟨e, B, hB, hJ⟩ := exists_frame h
  rcases hpq with rfl | rfl
  · have h1 : Formalism.UG.Jpq 0 q = -1 := by
      ext i j
      rcases i with i | i
      · exact i.elim0
      rcases j with j | j
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = -(Bᴴ * B) := by
      rw [hJ, h1, submatrix_neg]
      simp
    refine ⟨⟨B, hB, Or.inr h2⟩, ?_⟩
    rw [h2, UH_neg]
    exact isCompact_UH_gram B hB
  · have h1 : Formalism.UG.Jpq p 0 = 1 := by
      ext i j
      rcases i with i | i
      swap
      · exact i.elim0
      rcases j with j | j
      swap
      · exact j.elim0
      simp [Formalism.UG.Jpq, Matrix.one_apply]
    have h2 : J = Bᴴ * B := by
      rw [hJ, h1]
      simp
    refine ⟨⟨B, hB, Or.inl h2⟩, ?_⟩
    rw [h2]
    exact isCompact_UH_gram B hB

end GlobalTheory.DefiniteFrame
end

section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob Formalism.MainNotions.S

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

theorem ptEntry_inj : ∀ (bs cs : List (E × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (∀ b ∈ cs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    (bs.map Prod.snd).sum = (cs.map Prod.snd).sum →
    (∀ a < (bs.map Prod.snd).sum, ∀ b < (bs.map Prod.snd).sum, ptEntry bs a b = ptEntry cs a b) → bs = cs
  | [], [], _, _, _, _ => rfl
  | [], (t, s) :: cs, _, h, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: bs, [], h, _, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: bs, (t', s') :: cs, h, h', e, k => by
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    have hs : 1 ≤ s := (h (t, s) (by simp)).2
    have hs' : 1 ≤ s' := (h' (t', s') (by simp)).2
    simp only [List.map_cons, List.sum_cons] at e k
    have k0 := k 0 (by omega) (s - 1) (by omega)
    simp only [ptEntry] at k0
    rw [ite_eq_left (by omega), ite_eq_left (by omega)] at k0
    have hss : s = s' ∧ t = t' := by
      split_ifs at k0
      · exact ⟨by omega, k0⟩
      · exact absurd k0 ht
      · omega
      · exact absurd k0 ht
    rcases hss with ⟨rfl, rfl⟩
    apply congrArg (List.cons (t, s))
    refine ptEntry_inj bs cs (fun b hb => h b (by simp [hb])) (fun b hb => h' b (by simp [hb])) (by omega)
      fun a ha b hb => ?_
    have shifted := k (a + s) (by omega) (b + s) (by omega)
    have outside : ¬ (a + s < s ∧ b + s < s) := by omega
    have inside : s ≤ a + s ∧ s ≤ b + s := by omega
    simpa only [ptEntry, ite_eq_right outside, ite_eq_left inside, Nat.add_sub_cancel] using shifted

theorem ptMat_injective {m : ℕ} : Function.Injective (ptMat : Point E m → Matrix (Fin m) (Fin m) E) := by
  intro w w' h
  refine Subtype.ext (ptEntry_inj _ _ w.2.1 w'.2.1 (w.2.2.trans w'.2.2.symm) fun a ha b hb => ?_)
  rw [w.2.2] at ha hb
  exact congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E} {T' : E}
  {P : Matrix (Fin n) (Fin (r + 1)) E}

end GlobalTheory.IntTerm
end
end

section


theorem _root_.GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero : ∀ {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ} (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R), (∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) → M.charpolyRev * N.charpolyRev = 1 := by
  first | exact @GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | exact GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | (intros; apply GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory.AdicNoeth

theorem isNoetherianRing_adicCompletion : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsNoetherianRing (AdicCompletion I R) := by
  intro R _ _ I
  have fg : I.FG := I.fg_of_isNoetherianRing
  have hc := AdicCompletion.isAdicComplete_self I fg
  have e : (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) ≃+* R ⧸ I := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I)
  exact isNoetherianRing_of_isAdicComplete _ _ (fg.map _) hc
    (isNoetherianRing_of_ringEquiv _ e.symm)

end GlobalTheory.AdicNoeth
end
