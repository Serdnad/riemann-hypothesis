module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

section

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem finite_le_of_posDef {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (hS : ∀ x y, B x y = B y x) (hpos : ∀ v, v ≠ 0 → 0 < B v v)
    (A : Submodule ℤ V) (hA : A.FG) (c : ℚ) : {v | v ∈ A ∧ B v v ≤ c}.Finite := by
  classical
  obtain ⟨S, hS'⟩ := hA
  have hnn : ∀ v, 0 ≤ B v v := fun v => by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos v hv).le

  have cs : ∀ v w, B v w ^ 2 ≤ B v v * B w w := by
    intro v w
    by_cases hw : w = 0
    · simp [hw]
    · have hww := hpos w hw
      have key := hnn (B w w • v - B v w • w)
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hS w v] at key
      have h2 : B w w * B v w ^ 2 ≤ B w w * (B v v * B w w) := by nlinarith [key]
      exact le_of_mul_le_mul_left h2 hww
  let b := Module.finBasis ℚ V
  have hinj : ∀ v w, (∀ i, B v (b i) = B w (b i)) → v = w := by
    intro v w h
    have h0 : B (v - w) = 0 := b.ext fun i => by simp [map_sub, h i]
    by_contra hne
    have h1 := hpos (v - w) (sub_ne_zero.2 hne)
    rw [h0] at h1
    simp at h1
  let N : ℕ := ∏ s ∈ S, ∏ i, (B s (b i)).den
  have hNpos : 0 < N :=
    Finset.prod_pos fun s _ => Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (Rat.den_nz _)

  have hint : ∀ v ∈ A, ∀ i, ∃ z : ℤ, (z : ℚ) = N * B v (b i) := by
    intro v hv
    rw [← hS'] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      intro i
      have hd : (B x (b i)).den ∣ N :=
        (Finset.dvd_prod_of_mem (fun i => (B x (b i)).den) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun s => ∏ i, (B s (b i)).den) hx)
      obtain ⟨k, hk⟩ := hd
      refine ⟨k * (B x (b i)).num, ?_⟩
      have e := Rat.mul_den_eq_num (B x (b i))
      rw [hk]
      push_cast
      linear_combination (-(k : ℚ)) * e
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨z1, h1⟩ := hx i
      obtain ⟨z2, h2⟩ := hy i
      refine ⟨z1 + z2, ?_⟩
      rw [map_add (f := _), LinearMap.add_apply]
      push_cast
      rw [h1, h2]
      ring
    | smul a x _ hx =>
      intro i
      obtain ⟨z, hz⟩ := hx i
      refine ⟨a * z, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℚ a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [hz]
      ring
  have hbd : ∀ v, B v v ≤ c → ∀ i, |B v (b i)| ≤ 1 + |c| * B (b i) (b i) := by
    intro v hv i
    have h1 := cs v (b i)
    have h2 : B v v * B (b i) (b i) ≤ |c| * B (b i) (b i) :=
      mul_le_mul_of_nonneg_right (hv.trans (le_abs_self c)) (hnn _)
    have h3 : |B v (b i)| ≤ 1 + B v (b i) ^ 2 := by
      nlinarith [sq_nonneg (|B v (b i)| - 1), sq_abs (B v (b i))]
    linarith
  let g : V → Fin (Module.finrank ℚ V) → ℤ := fun v i => round ((N : ℚ) * B v (b i))
  have hg : ∀ v ∈ A, ∀ i, ((g v i : ℤ) : ℚ) = N * B v (b i) := by
    intro v hv i
    obtain ⟨z, hz⟩ := hint v hv i
    simp only [g]
    rw [← hz, round_intCast]
  apply Set.Finite.of_finite_image (f := g)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun i =>
      Set.Icc (-⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉) ⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉)
      fun i => Set.finite_Icc _ _) ?_
    rintro _ ⟨v, ⟨hvA, hvc⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have e := hg v hvA i
    have hb : |((g v i : ℤ) : ℚ)| ≤ N * (1 + |c| * B (b i) (b i)) := by
      rw [e, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hbd v hvc i) (Nat.cast_nonneg _)
    have hK := Int.le_ceil ((N : ℚ) * (1 + |c| * B (b i) (b i)))
    have l1 := neg_abs_le ((g v i : ℤ) : ℚ)
    have l2 := le_abs_self ((g v i : ℤ) : ℚ)
    constructor
    · have : ((-⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉ : ℤ) : ℚ) ≤ ((g v i : ℤ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast this
    · have : ((g v i : ℤ) : ℚ) ≤ ((⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉ : ℤ) : ℚ) := by
        linarith
      exact_mod_cast this
  · rintro v ⟨hvA, -⟩ w ⟨hwA, -⟩ hvw
    apply hinj
    intro i
    have e : (N : ℚ) * B v (b i) = N * B w (b i) := by
      rw [← hg v hvA i, ← hg w hwA i, congrFun hvw i]
    exact mul_left_cancel₀ (by exact_mod_cast hNpos.ne') e

end PI.UnitaryGroupMassFormula.CntFormula
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem isInt_O (o : 𝓞 K) : IsIntegral ℤ (algebraMap (𝓞 K) K o) := o.2

theorem O_of_isInt {x : K} (h : IsIntegral ℤ x) : ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = x := ⟨⟨x, h⟩, rfl⟩

theorem isInt_intCast (n : ℤ) : IsIntegral ℤ (n : K) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K n))

theorem isInt_star [StarRing K] {x : K} (h : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  h.map (starRingEnd K).toIntAlgHom

theorem commonDen (s : Finset K) : ∃ d : ℕ, 0 < d ∧ ∀ x ∈ s, IsIntegral ℤ ((d : K) * x) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hy) 2, fun x hx => ?_⟩
  have e0 : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by rw [Nat.cast_pow, Int.natAbs_sq]
  have e1 : ((y.natAbs ^ 2 : ℕ) : K) = (y : K) ^ 2 := by rw [← Int.cast_natCast, e0, Int.cast_pow]
  rw [e1, pow_two, mul_assoc, ← zsmul_eq_mul x y]
  exact (isInt_intCast y).mul (h x hx)

theorem reduceRep (N : ℕ) (hN : 0 < N) : ∃ Rep : Set K, Rep.Finite ∧ (∀ ρ ∈ Rep, IsIntegral ℤ ρ) ∧
    ∀ o : K, IsIntegral ℤ o → ∃ t ρ : K, IsIntegral ℤ t ∧ ρ ∈ Rep ∧ o = (N : K) * t + ρ := by
  set I : Ideal (𝓞 K) := Ideal.span {(N : 𝓞 K)} with hI
  have hIne : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have := I.finiteQuotientOfFreeOfNeBot hIne
  set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) with hσ
  refine ⟨Set.range (fun q : 𝓞 K ⧸ I => algebraMap (𝓞 K) K (σ q)), Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩; exact isInt_O _
  · intro o ho
    obtain ⟨oo, rfl⟩ := O_of_isInt ho
    set q := Ideal.Quotient.mk I oo
    have hq : Ideal.Quotient.mk I (σ q) = q := Function.surjInv_eq _ q
    have hmem : oo - σ q ∈ I := Ideal.Quotient.eq.1 hq.symm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨algebraMap (𝓞 K) K t, algebraMap (𝓞 K) K (σ q), isInt_O _, ⟨q, rfl⟩, ?_⟩
    have e : oo = t * N + σ q := by rw [ht]; ring
    rw [e, map_add (f := _), map_mul, map_natCast]
    ring

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaB

open Polynomial

variable {R K A : Type} [CommRing R] [Field K] [CommRing A] [Algebra R K] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A]

theorem trace_isIntegral_rank2 (b : Module.Basis (Fin 2) K A) {y : A} (hy : IsIntegral R y) :
    IsIntegral R (Algebra.trace K A y) := by
  classical
  obtain ⟨p, hpm, hp⟩ := hy
  let L := AlgebraicClosure K
  let M : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix b y
  let M' : Matrix (Fin 2) (Fin 2) L := M.map (algebraMap K L)
  have hpy : Polynomial.aeval y p = 0 := hp
  have hpM : Polynomial.aeval M p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.leftMulMatrix b).restrictScalars R) y p
    rw [hpy, map_zero] at h1
    exact h1
  have hpM' : Polynomial.aeval M' p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply
      (((Algebra.ofId K L).mapMatrix : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) L).restrictScalars R) M p
    rw [hpM, map_zero] at h1
    exact h1
  have hroot : ∀ μ ∈ M'.charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have h1 : μ ∈ spectrum L M' := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots'.mp hμ).2
    have h2 := spectrum.subset_polynomial_aeval M' (p.map (algebraMap R L)) ⟨μ, h1, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hpM', spectrum.zero_eq] at h2
    refine ⟨p, hpm, ?_⟩
    have h3 : Polynomial.eval μ (p.map (algebraMap R L)) = 0 := h2
    rwa [Polynomial.eval_map] at h3
  have htr : algebraMap K L (Algebra.trace K A y) = M'.charpoly.roots.sum := by
    rw [Algebra.trace_eq_matrix_trace b y, ← Matrix.trace_eq_sum_roots_charpoly]
    simp [M', M, Matrix.trace, Matrix.map_apply]
  have hint : IsIntegral R (algebraMap K L (Algebra.trace K A y)) := by
    rw [htr]
    exact IsIntegral.multiset_sum hroot
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint

end PI.UnitaryGroupMassFormula.CntFormula.DeltaB
end
end
