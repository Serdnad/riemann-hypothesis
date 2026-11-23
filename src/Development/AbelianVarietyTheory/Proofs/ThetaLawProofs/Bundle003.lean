module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.SetTheory.Cardinal.Subfield

@[expose] public section

section

namespace GlobalTheory

theorem exists_eval_ne_zero_of_countable {σ : Type} [Finite σ] (T : Set (MvPolynomial σ ℂ))
    (hT : T.Countable) (h0 : (0 : MvPolynomial σ ℂ) ∉ T) :
    ∃ c : σ → ℂ, ∀ p ∈ T, MvPolynomial.eval c p ≠ 0 := by
  classical
  have := Fintype.ofFinite σ
  have hd : Dense (⋂ p ∈ T, {c : σ → ℂ | MvPolynomial.eval c p ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun p _ => ?_) hT (fun p hp => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const
    · intro c
      by_contra hc
      have hev : (fun c : σ → ℂ => MvPolynomial.eval c p) =ᶠ[nhds c] 0 := by
        have h1 : (closure {c : σ → ℂ | MvPolynomial.eval c p ≠ 0})ᶜ ∈ nhds c :=
          isClosed_closure.isOpen_compl.mem_nhds hc
        filter_upwards [h1] with x hx
        by_contra hx'
        exact hx (subset_closure hx')
      have hz := (AnalyticOnNhd.eval_mvPolynomial p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ c) hev
      have : p = 0 := MvPolynomial.funext fun x => by
        simpa using hz (Set.mem_univ x)
      exact h0 (this ▸ hp)
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun p hp => Set.mem_iInter₂.1 hc p hp⟩

theorem exists_algHom_ne_zero_of_countable (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ s : E →ₐ[ℂ] ℂ, ∀ r ∈ T, s r ≠ 0 := by
  classical
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) E := hfin
  have hn : ∀ r : E, r ≠ 0 → ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap (MvPolynomial (Fin d) ℂ) E n ∈ Ideal.span {r} := by
    intro r hr
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ)
      (I := Ideal.span {r}) hr (Ideal.mem_span_singleton_self r)
      (Algebra.IsIntegral.isIntegral r)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose! n hn0 hnr using hn
  have hne : ∀ r ∈ T, r ≠ 0 := fun r hr h => h0 (h ▸ hr)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero_of_countable (n '' T) (hT.image n) (by
    rintro ⟨r, hr, h⟩
    exact hn0 r (hne r hr) h)
  have hsurj : Function.Surjective (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ) :=
    fun z => ⟨MvPolynomial.C z, by simp⟩
  haveI hmax : (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := E)
    (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)) (by
      have : RingHom.ker (algebraMap (MvPolynomial (Fin d) ℂ) E) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).1 hinj
      rw [this]
      exact bot_le)
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  haveI : Module.Finite ℂ (E ⧸ Q) := finite_of_finite_type_of_isJacobsonRing ℂ (E ⧸ Q)
  have hbij : Function.Bijective (Algebra.ofId ℂ (E ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃ₐ[ℂ] (E ⧸ Q) := AlgEquiv.ofBijective _ hbij
  refine ⟨(e.symm : (E ⧸ Q) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ Q), fun r hr h => ?_⟩
  have h1 : Ideal.Quotient.mk Q r = 0 := by
    apply e.symm.injective
    rw [map_zero]
    exact h
  have h2 : r ∈ Q := Ideal.Quotient.eq_zero_iff_mem.1 h1
  have h3 : n r ∈ Q.under (MvPolynomial (Fin d) ℂ) :=
    (Ideal.mem_under (MvPolynomial (Fin d) ℂ) Q).2
      ((Ideal.span_singleton_le_iff_mem Q).2 h2 (hnr r (hne r hr)))
  rw [hQp] at h3
  exact hc (n r) ⟨r, hr, rfl⟩ h3

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem exists_nat_mul_quadratic_lt (N : ℕ) (hN : 1 ≤ N) (a b q c : ℚ) (hq : q < 0) :
    ∃ k : ℕ, a + ((N : ℚ) * k) * b + ((N : ℚ) * k) ^ 2 * q < c := by
  set B : ℚ := (|b| + |a - c| + 1) / (-q) with hB
  have hq' : 0 < -q := by linarith
  have hBpos : 0 < B := div_pos (by positivity) hq'
  obtain ⟨k, hk⟩ := exists_nat_gt B
  refine ⟨k, ?_⟩
  have hk1 : (1 : ℚ) ≤ k := by
    have : (0 : ℚ) < k := lt_trans hBpos hk
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at this)
  have hN1 : (1 : ℚ) ≤ N := by exact_mod_cast hN
  set m : ℚ := (N : ℚ) * k with hm
  have hm1 : 1 ≤ m := by nlinarith
  have hmk : (k : ℚ) ≤ m := by nlinarith
  have hmB : B < m := lt_of_lt_of_le hk hmk
  have h1 : |b| + |a - c| + 1 < m * (-q) := by
    rw [hB, div_lt_iff₀ hq'] at hmB; linarith
  have h2 : m * (|b| + |a - c| + 1) < m * (m * (-q)) := mul_lt_mul_of_pos_left h1 (by linarith)
  have h3 : m * b ≤ m * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) (by linarith)
  have h4 : a - c ≤ |a - c| := le_abs_self _
  have h5 : 0 ≤ (m - 1) * (|a - c| + 1) := mul_nonneg (by linarith) (by positivity)
  nlinarith

private theorem trace_mul_vecMulVec {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℚ) (u w : n → ℚ) : (T * vecMulVec u w).trace = w ⬝ᵥ T.mulVec u := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_transvection_conj {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℚ) (x y : n → ℚ) (t : ℚ) :
    ((1 + t • vecMulVec x y)ᵀ * T * (1 + t • vecMulVec x y)).trace =
      T.trace + t * (x ⬝ᵥ T.mulVec y + y ⬝ᵥ T.mulVec x) +
        t ^ 2 * ((y ⬝ᵥ y) * (x ⬝ᵥ T.mulVec x)) := by
  have hP : (1 + t • vecMulVec x y)ᵀ = 1 + t • vecMulVec y x := by
    rw [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]
  rw [hP]
  have e : (1 + t • vecMulVec y x) * T * (1 + t • vecMulVec x y) =
      T + t • (T * vecMulVec x y) + t • (vecMulVec y x * T) + (t * t) • (vecMulVec y x * T * vecMulVec x y) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [e, trace_add, trace_add, trace_add, trace_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, Matrix.trace_mul_comm (vecMulVec y x) T]
  simp only [trace_mul_vecMulVec]
  rw [← Matrix.mulVec_mulVec]
  have hv : ∀ w : n → ℚ, vecMulVec y x *ᵥ w = (x ⬝ᵥ w) • y := by
    intro w
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hv, dotProduct_smul, smul_eq_mul]
  ring

theorem exists_congruence_trace_lt :
    ∀ (g N : ℕ), 2 ≤ g → 1 ≤ N → ∀ T : Matrix (Fin g) (Fin g) ℚ, T.IsSymm →
      (∃ v : Fin g → ℚ, v ⬝ᵥ T.mulVec v < 0) →
      ∀ c : ℚ, ∃ U : Matrix (Fin g) (Fin g) ℤ, U.det = 1 ∧
        (∀ i j, (N : ℤ) ∣ U i j - (1 : Matrix (Fin g) (Fin g) ℤ) i j) ∧
        ((U.map (Int.cast : ℤ → ℚ)).transpose * T * U.map (Int.cast : ℤ → ℚ)).trace < c := by
  intro g N hg hN T _ hv c
  obtain ⟨v, hv⟩ := hv
  set D : ℕ := ∏ i, (v i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (v i).den_pos
  have hden : ∀ i, (v i).den ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set xz : Fin g → ℤ := fun i => ((D / (v i).den : ℕ) : ℤ) * (v i).num with hxz
  have hx : ∀ i, ((xz i : ℤ) : ℚ) = (D : ℚ) * v i := by
    intro i
    have hne : ((v i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (v i).den_nz
    simp only [hxz]
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (hden i) hne, ← Rat.mul_den_eq_num (v i)]
    field_simp
  set x : Fin g → ℚ := fun i => (xz i : ℚ) with hxdef
  have hxv : x = (D : ℚ) • v := funext fun i => by simp [hxdef, hx]
  have hxT : x ⬝ᵥ T *ᵥ x < 0 := by
    rw [hxv, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have : (0 : ℚ) < D := by exact_mod_cast hDpos
    exact mul_neg_of_pos_of_neg (by positivity) hv
  obtain ⟨i0, hi0⟩ : ∃ i0, xz i0 ≠ 0 := by
    by_contra h
    push Not at h
    have : x = 0 := funext fun i => by simp [hxdef, h i]
    rw [this] at hxT
    simp at hxT
  obtain ⟨i1, hi1⟩ := Fintype.exists_ne_of_one_lt_card (by simp; omega) i0
  set yz : Fin g → ℤ := Pi.single i0 (xz i1) - Pi.single i1 (xz i0) with hyz
  have hyx : yz ⬝ᵥ xz = 0 := by
    rw [hyz, sub_dotProduct, single_dotProduct, single_dotProduct]; ring
  set y : Fin g → ℚ := fun j => (yz j : ℚ) with hydef
  have hy1 : y i1 = -(xz i0 : ℚ) := by
    simp [hydef, hyz, Pi.single_apply, hi1]
  have hyy : 0 < y ⬝ᵥ y := by
    have hle : y i1 * y i1 ≤ y ⬝ᵥ y :=
      Finset.single_le_sum (f := fun j => y j * y j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ i1)
    have hpos : 0 < y i1 * y i1 := by
      rw [hy1]
      have : (xz i0 : ℚ) ≠ 0 := by exact_mod_cast hi0
      exact mul_self_pos.mpr (neg_ne_zero.mpr this)
    linarith
  have hq : (y ⬝ᵥ y) * (x ⬝ᵥ T *ᵥ x) < 0 := mul_neg_of_pos_of_neg hyy hxT
  obtain ⟨k, hk⟩ := exists_nat_mul_quadratic_lt N hN T.trace (x ⬝ᵥ T.mulVec y + y ⬝ᵥ T.mulVec x)
    ((y ⬝ᵥ y) * (x ⬝ᵥ T.mulVec x)) c hq
  refine ⟨1 + ((N : ℤ) * k) • vecMulVec xz yz, ?_, ?_, ?_⟩
  · rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
      hyx, smul_zero, add_zero]
  · intro i j
    refine ⟨k * (xz i * yz j), ?_⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  · have hmap : (1 + ((N : ℤ) * k) • vecMulVec xz yz).map (Int.cast : ℤ → ℚ) =
        1 + ((N : ℚ) * k) • vecMulVec x y := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
        Matrix.one_apply, hxdef, hydef]
      split_ifs <;> push_cast <;> ring
    rw [hmap, trace_transvection_conj]
    exact hk

end GlobalTheory
end

section

namespace GlobalTheory

theorem natAbs_det_of_transpose_mul_self (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (h : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    al.det.natAbs = m ^ 2 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one] at h1
  have h2 := congrArg Int.natAbs h1
  simp only [Int.natAbs_mul, Fintype.card_fin, mul_one, Int.natAbs_pow, Int.natAbs_natCast] at h2
  have h3 : al.det.natAbs ^ 2 = (m ^ 2) ^ 2 := by rw [sq, h2]; ring
  exact Nat.pow_left_injective (by norm_num) h3

theorem card_quotient_range_mulVecLin {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hA : A.det ≠ 0) :
    Nat.card ((ι → ℤ) ⧸ LinearMap.range (Matrix.toLin' A)) = A.det.natAbs := by
  have hinj : Function.Injective (Matrix.toLin' A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hA (by simpa using hv)
  rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj)]
  congr 1
  rw [← LinearMap.det_toLin' A]
  congr 1

theorem exists_representatives_mod_similitude_transpose :
    ∀ (g m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ k n : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, ∀ k' n' : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, (∀ I I', I ≠ I' → ¬ ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k' I' c + ∑ r, al r c • d r ∧ n' I c = n' I' c + ∑ r, al r c • e r) → ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ g)), ∀ I, ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k (σ I) c + ∑ r, al r c • d r ∧ n' I c = n (σ I) c + ∑ r, al r c • e r := by
  intro g m al hm h
  classical
  have hdet := natAbs_det_of_transpose_mul_self m al h
  have hne : al.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    intro h0
    rw [h0] at hdet
    have : 0 < m ^ 2 := by positivity
    simp at hdet
    omega
  set L := LinearMap.range (Matrix.toLin' al.transpose) with hL
  have hQ : Nat.card ((Fin 4 → ℤ) ⧸ L) = m ^ 2 := by
    rw [hL, card_quotient_range_mulVecLin _ hne, Matrix.det_transpose, hdet]
  haveI : Finite ((Fin 4 → ℤ) ⧸ L) := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  let cl : (Fin 4 → Fin g → ℤ) → Fin g → ((Fin 4 → ℤ) ⧸ L) :=
    fun x j => Submodule.Quotient.mk (fun c => x c j)
  have hsurj : Function.Surjective cl := by
    intro q
    choose f hf using fun j => Submodule.Quotient.mk_surjective L (q j)
    exact ⟨fun c j => f j c, funext hf⟩
  have hrel : ∀ x y, cl x = cl y → ∃ d : Fin 4 → Fin g → ℤ,
      ∀ c, x c = y c + ∑ r, al r c • d r := by
    intro x y hxy
    have : ∀ j, ∃ v : Fin 4 → ℤ, Matrix.toLin' al.transpose v
        = (fun c => x c j) - (fun c => y c j) := fun j =>
      (Submodule.Quotient.eq L).1 (congrFun hxy j)
    choose v hv using this
    refine ⟨fun r j => v j r, fun c => ?_⟩
    funext j
    have := congrFun (hv j) c
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.sub_apply] at this
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]; ring
  have hcard : Nat.card (Fin 4 → Fin (m ^ g)) =
      Nat.card ((Fin g → ((Fin 4 → ℤ) ⧸ L)) × (Fin g → ((Fin 4 → ℤ) ⧸ L))) := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, hQ]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    ring
  obtain ⟨β⟩ := Finite.card_eq.1 hcard
  choose s hs using hsurj
  refine ⟨fun I => s (β I).1, fun I => s (β I).2, fun k' n' hkn => ?_⟩
  let f : (Fin 4 → Fin (m ^ g)) → (Fin 4 → Fin (m ^ g)) :=
    fun I => β.symm (cl (k' I), cl (n' I))
  have hf : Function.Injective f := by
    intro I I' hI
    by_contra hne'
    have h1 := β.symm.injective hI
    obtain ⟨d, hd⟩ := hrel _ _ (congrArg Prod.fst h1)
    obtain ⟨e, he⟩ := hrel _ _ (congrArg Prod.snd h1)
    exact hkn I I' hne' ⟨d, e, fun c => ⟨hd c, he c⟩⟩
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun I => ?_⟩
  obtain ⟨d, hd⟩ := hrel (k' I) (s (β (f I)).1) (by rw [hs]; simp [f])
  obtain ⟨e, he⟩ := hrel (n' I) (s (β (f I)).2) (by rw [hs]; simp [f])
  exact ⟨d, e, fun c => ⟨hd c, he c⟩⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_countable_local_pid_subring (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsPrincipalIdealRing R] (S : Set R) (hS : S.Countable) :
    ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀),
      Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R := by
  classical
  let K := FractionRing R
  let K₀ : Subfield K := Subfield.closure (algebraMap R K '' S)
  let R₀ : Subring R := K₀.toSubring.comap (algebraMap R K)
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ x : R, x ∈ R₀ ↔ algebraMap R K x ∈ K₀ := fun x => Iff.rfl
  have hdvd : ∀ a b : R₀, (a : R) ∣ (b : R) → a ∣ b := by
    rintro a b ⟨c, hc⟩
    by_cases ha : (a : R) = 0
    · have : b = 0 := Subtype.ext (by rw [hc, ha]; simp)
      rw [this]; exact dvd_zero _
    · have ha' : algebraMap R K a ≠ 0 := fun h => ha (hinj (by simpa using h))
      have hcm : c ∈ R₀ := by
        rw [hmem]
        have : algebraMap R K c = algebraMap R K b / algebraMap R K a := by
          rw [hc, map_mul, mul_div_cancel_left₀ _ ha']
        rw [this]
        exact K₀.div_mem ((hmem _).1 b.2) ((hmem _).1 a.2)
      exact ⟨⟨c, hcm⟩, Subtype.ext hc⟩
  have hloc : IsLocalHom R₀.subtype := ⟨fun a ha => by
    rw [isUnit_iff_dvd_one] at ha ⊢
    exact hdvd a 1 ha⟩
  have hlr : IsLocalRing R₀ := RingHom.domain_isLocalRing R₀.subtype
  have hpid : IsPrincipalIdealRing R₀ := ⟨fun I => by
    obtain ⟨M, ⟨a, haI, rfl⟩, hM⟩ := set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian R R)
      {J : Ideal R | ∃ a : R₀, a ∈ I ∧ Ideal.span {(a : R)} = J} ⟨_, 0, I.zero_mem, rfl⟩
    refine ⟨⟨a, le_antisymm (fun b hb => ?_) ?_⟩⟩
    · change b ∈ Ideal.span {a}
      rw [Ideal.mem_span_singleton]
      apply hdvd
      rcases ValuationRing.dvd_total (a : R) (b : R) with h | h
      · exact h
      · have h1 : Ideal.span {(a : R)} ≤ Ideal.span {(b : R)} :=
          Ideal.span_singleton_le_span_singleton.mpr h
        have h2 := hM _ ⟨b, hb, rfl⟩
        exact Ideal.span_singleton_le_span_singleton.mp (eq_of_le_of_not_lt h1 h2).ge
    · exact (Ideal.span_singleton_le_iff_mem I).mpr haI⟩
  have hK : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max _).trans (max_le ?_ le_rfl)
    rw [Cardinal.mk_le_aleph0_iff]
    exact (hS.image _).to_subtype
  have hc : Countable R₀ := by
    let f : R₀ → K₀ := fun x => ⟨algebraMap R K x, (hmem _).1 x.2⟩
    have : Function.Injective f := fun x y h =>
      Subtype.ext (hinj (congrArg Subtype.val h))
    exact this.countable
  refine ⟨R₀, hlr, hpid, hc, fun x hx => Subfield.subset_closure ⟨x, hx, rfl⟩, hloc, ?_⟩
  have : IsLocalHom (algebraMap R₀ R) := hloc
  have : Module.Flat R₀ R := inferInstance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end GlobalTheory
end
