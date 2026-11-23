module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem unit_add_mem {R : Type} [CommRing R] [IsLocalRing R] {a b : R} (ha : IsUnit a)
    (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : a ∈ maximalIdeal R := by simpa using (maximalIdeal R).sub_mem h1 hb
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 ha

private theorem two_kill {R : Type} [CommRing R] [IsLocalRing R] {p q r s a b : R} (hp : IsUnit p) (hs : IsUnit s)
    (hq : q ∈ maximalIdeal R) (e1 : p * a + q * b = 0) (e2 : r * a + s * b = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨s', hs'⟩ := hs.exists_right_inv
  have hb : b = -(s' * r) * a := by linear_combination s' * e2 - b * hs'
  have hm : q * s' * r ∈ maximalIdeal R :=
    (maximalIdeal R).mul_mem_right _ ((maximalIdeal R).mul_mem_right _ hq)
  have hu : IsUnit (p + -(q * s' * r)) := unit_add_mem hp ((maximalIdeal R).neg_mem hm)
  have ha : a = 0 := (hu.mul_right_eq_zero).mp (by linear_combination e1 - q * hb)
  refine ⟨ha, ?_⟩
  rw [hb, ha]
  ring

private theorem cols {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X) (hs : Sep X)
    (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    ∃ y, u 0 1 = y * u 0 0 ∧ u 2 1 = y * u 2 0 := by
  have h01 : IsUnit (X 0 0 - X 1 1) := hs.unit 0 1 (by decide)
  have h21 : IsUnit (X 2 2 - X 1 1) := hs.unit 2 1 (by decide)
  have p0 : IsUnit (X 0 0 - U 1 1) := by
    have := unit_add_mem h01 (neg_mem (hc 1))
    convert this using 1; ring
  have p2 : IsUnit (X 2 2 - U 1 1) := by
    have := unit_add_mem h21 (neg_mem (hc 1))
    convert this using 1; ring
  have pU : IsUnit (U 0 0 - U 1 1) := by
    have := unit_add_mem p0 (hc 0)
    convert this using 1; ring
  obtain ⟨w, hw⟩ := pU.exists_left_inv
  have z01 := hb 0 1 (by decide)
  have z03 := hb 0 3 (by decide)
  have z21 := hb 2 1 (by decide)
  have z23 := hb 2 3 (by decide)
  have y10 := hU 1 0 (by decide)
  have y20 := hU 2 0 (by decide)
  have y30 := hU 3 0 (by decide)
  have y21 := hU 2 1 (by decide)
  have y31 := hU 3 1 (by decide)
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z21, z23, y10, y20, y30, y21, y31, zero_mul, mul_zero,
    add_zero] at e00 e01 e20 e21
  have := two_kill (a := u 0 1 - U 0 1 * w * u 0 0) (b := u 2 1 - U 0 1 * w * u 2 0) (r := X 2 0) p0 p2
    (hs.off 0 2 (by decide))
    (by linear_combination e01 - U 0 1 * w * e00 - U 0 1 * u 0 0 * hw)
    (by linear_combination e21 - U 0 1 * w * e20 - U 0 1 * u 2 0 * hw)
  exact ⟨U 0 1 * w, sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

private theorem entries_one_three_zero_eq_zero_of_intertwine_up {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X)
    (hs : Sep X) (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    u 1 0 = 0 ∧ u 3 0 = 0 := by
  have X10 : X 1 0 = 0 := hb 1 0 (by simp [lamW])
  have coord_mul_inv_coord_eq_one : X 1 2 = 0 := hb 1 2 (by simp [lamW])
  have X30 : X 3 0 = 0 := hb 3 0 (by simp [lamW])
  have X32 : X 3 2 = 0 := hb 3 2 (by simp [lamW])
  have U10 : U 1 0 = 0 := hU 1 0 (by decide)
  have U20 : U 2 0 = 0 := hU 2 0 (by decide)
  have U30 : U 3 0 = 0 := hU 3 0 (by decide)
  have r10 := congrFun (congrFun e 1) 0
  have r30 := congrFun (congrFun e 3) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_four, X10, coord_mul_inv_coord_eq_one, X30, X32, U10, U20, U30,
    zero_mul, mul_zero, add_zero, zero_add] at r10 r30
  have hc0 := hc 0
  have hp : IsUnit (X 1 1 - U 0 0) := by
    have e' : X 1 1 - U 0 0 = (X 1 1 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 1 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hs' : IsUnit (X 3 3 - U 0 0) := by
    have e' : X 3 3 - U 0 0 = (X 3 3 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 3 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hq : X 1 3 ∈ maximalIdeal R := hs.off 1 3 (by decide)
  exact two_kill (r := X 3 1) (a := u 1 0) (b := u 3 0) hp hs' hq
    (by linear_combination r10) (by linear_combination r30)

theorem UpperTheory.V.Ws.Bl.flagVec :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X u : M4 R), IsBlock X → Sep X → IsGSp 1 u → IsUp (adj u * X * u) → (∀ i, (adj u * X * u) i i - X i i ∈ maximalIdeal R) → uPlus u ≠ ⊥ := by
  intro R _ _ X u hb hs hg hup hc
  have hinv : adj u * u = 1 := by simpa [IsGSp] using hg
  have e : X * u = u * (adj u * X * u) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp hinv, Matrix.one_mul]
  obtain ⟨y, hy1, hy2⟩ := cols X u _ hb hs e hup hc
  obtain ⟨h10, h30⟩ := entries_one_three_zero_eq_zero_of_intertwine_up X u _ hb hs e hup hc
  have I10 := congrFun (congrFun hinv 1) 0
  have I11 := congrFun (congrFun hinv 1) 1
  have I00 := congrFun (congrFun hinv 0) 0
  have I31 := congrFun (congrFun hinv 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev] at I10 I11 I00 I31
  have iso : u 0 0 * u 3 1 = u 2 0 * u 1 1 := by
    linear_combination I31 - u 2 1 * h10 + u 0 1 * h30
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → R, w = ![0, u 1 1, 0, u 3 1] := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin 4 → R, φ = ![u 2 0, 0, -u 0 0, 0] := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : M4 R, Y = Matrix.vecMulVec w φ := ⟨_, rfl⟩
  have hYm : Y ∈ uM R := by
    show Y ∈ hAB R ⊓ sp4 R
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · show ∀ i j, ¬ lamW i < lamW j → Y i j = 0
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [lamW, Matrix.vecMulVec_apply]
    · show adj Y = -Y
      ext i j
      fin_cases i <;> fin_cases j <;>
        (try simp [hYd, hw, hφ, adj_apply, sgn, Fin.rev, Matrix.vecMulVec_apply]) <;>
        first
          | linear_combination iso
          | linear_combination (-1 : R) * iso
  have hv : w = Matrix.mulVec u ![-y, 1, 0, 0] := by
    funext i
    fin_cases i <;> simp [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      first
        | linear_combination (-1 : R) * hy1
        | linear_combination y * h10
        | linear_combination (-1 : R) * hy2
        | linear_combination y * h30
        | linear_combination hy1
        | linear_combination hy2
        | linear_combination (-y) * h10
        | linear_combination (-y) * h30
  have hA : Matrix.mulVec (adj u) w = ![-y, 1, 0, 0] := by
    rw [hv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hB0 : Matrix.vecMul φ u 0 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;> ring
  have hB1 : Matrix.vecMul φ u 1 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;>
      linear_combination u 2 0 * hy1 - u 0 0 * hy2
  have hN : adj u * Y * u = Matrix.vecMulVec ![-y, 1, 0, 0] (Matrix.vecMul φ u) := by
    rw [hYd, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hA]
  have hsup : IsSUp (adj u * Y * u) := by
    intro i j hji
    rw [hN, Matrix.vecMulVec_apply]
    fin_cases i <;> fin_cases j <;>
      first
        | (simp [hB0, hB1]; done)
        | (exfalso; simp at hji; done)
        | (exfalso; revert hji; decide)
  rw [Submodule.ne_bot_iff]
  refine ⟨⟨Y, hYm⟩, ?_, ?_⟩
  · exact hsup
  · intro hY0
    have hY : Y = 0 := congrArg Subtype.val hY0
    have f1 : u 1 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 1) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f2 : u 1 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 1) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f3 : u 3 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 3) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f4 : u 3 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 3) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have J : u 2 2 * u 1 1 - u 0 2 * u 3 1 = 1 := by
      linear_combination I11 - u 3 2 * hy1 + u 1 2 * hy2 - y * I10 + y * u 2 2 * h10 -
        y * u 0 2 * h30
    have z00 : u 0 0 = 0 := by linear_combination (-u 0 0) * J + u 2 2 * f2 - u 0 2 * f4
    have z20 : u 2 0 = 0 := by linear_combination (-u 2 0) * J + u 2 2 * f1 - u 0 2 * f3
    have h1 : (1 : R) = 0 := by
      linear_combination (-1 : R) * I00 + u 3 3 * z00 + u 2 3 * h10 - u 1 3 * z20 - u 0 3 * h30
    exact one_ne_zero h1
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem eq_diag_of_square_eq_one_of_near_sign {R : Type} [CommRing R] [IsLocalRing R] (s a b c d : R)
    (hs : s * s = 1) (h2 : IsUnit (2 : R)) (ha : a - s ∈ maximalIdeal R)
    (hd : d - s ∈ maximalIdeal R) (e1 : a * a + b * c = 1) (e2 : a * b + b * d = 0)
    (e3 : c * a + d * c = 0) (e4 : c * b + d * d = 1) : a = s ∧ b = 0 ∧ c = 0 ∧ d = s := by
  have hunit : ∀ u : R, u - 2 * s ∈ maximalIdeal R → IsUnit u := by
    intro u hu
    have h2s : IsUnit (2 * s) := h2.mul ⟨⟨s, s, hs, hs⟩, rfl⟩
    by_contra hnu
    have hum : u ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2m : 2 * s ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem hum hu
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).mp h2m h2s
  have hsum : IsUnit (a + d) := hunit _ (by
    have e : a + d - 2 * s = (a - s) + (d - s) := by ring
    rw [e]
    exact (maximalIdeal R).add_mem ha hd)
  have hb : b = 0 := (hsum.mul_left_eq_zero).mp (by linear_combination e2)
  have hc : c = 0 := (hsum.mul_left_eq_zero).mp (by linear_combination e3)
  subst hb hc
  have hpa : IsUnit (a + s) := hunit _ (by
    have e : a + s - 2 * s = a - s := by ring
    rw [e]
    exact ha)
  have hpd : IsUnit (d + s) := hunit _ (by
    have e : d + s - 2 * s = d - s := by ring
    rw [e]
    exact hd)
  refine ⟨?_, rfl, rfl, ?_⟩
  · have h : (a - s) * (a + s) = 0 := by linear_combination e1 - hs
    exact sub_eq_zero.mp ((hpa.mul_left_eq_zero).mp h)
  · have h : (d - s) * (d + s) = 0 := by linear_combination e4 - hs
    exact sub_eq_zero.mp ((hpd.mul_left_eq_zero).mp h)

theorem UpperTheory.V.Ws.Bl.ccNeg :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : M4 R), IsUnit (2 : R) → IsBlock X → X * X = 1 → (∀ i j, X i j - eAB R i j ∈ maximalIdeal R) → X = eAB R := by
  intro R _ _ X h2 hB hX hm
  have sq : ∀ i j, ∑ k, X i k * X k j = (1 : M4 R) i j := fun i j => by
    rw [← Matrix.mul_apply, hX]
  have hm' : ∀ i, X i i - ![-1, 1, -1, 1] i ∈ maximalIdeal R := fun i => by
    simpa [eAB] using hm i i
  have z01 : X 0 1 = 0 := hB 0 1 (by simp [lamW])
  have z03 : X 0 3 = 0 := hB 0 3 (by simp [lamW])
  have z10 : X 1 0 = 0 := hB 1 0 (by simp [lamW])
  have z12 : X 1 2 = 0 := hB 1 2 (by simp [lamW])
  have z21 : X 2 1 = 0 := hB 2 1 (by simp [lamW])
  have z23 : X 2 3 = 0 := hB 2 3 (by simp [lamW])
  have z30 : X 3 0 = 0 := hB 3 0 (by simp [lamW])
  have z32 : X 3 2 = 0 := hB 3 2 (by simp [lamW])
  have q : ∀ i j, (∑ k, X i k * X k j) = X i 0 * X 0 j + X i 1 * X 1 j + X i 2 * X 2 j + X i 3 * X 3 j :=
    fun i j => Fin.sum_univ_four _
  obtain ⟨a0, b0, c0, d0⟩ := eq_diag_of_square_eq_one_of_near_sign (-1) (X 0 0) (X 0 2) (X 2 0) (X 2 2) (by ring) h2
    (by simpa using hm' 0) (by simpa using hm' 2)
    (by have h := sq 0 0; rw [q] at h; simp [z01, z03, z10, z30] at h; linear_combination h)
    (by have h := sq 0 2; rw [q] at h; simp [z01, z03, z12, z32] at h; linear_combination h)
    (by have h := sq 2 0; rw [q] at h; simp [z21, z23, z10, z30] at h; linear_combination h)
    (by have h := sq 2 2; rw [q] at h; simp [z21, z23, z12, z32] at h; linear_combination h)
  obtain ⟨a1, b1, c1, d1⟩ := eq_diag_of_square_eq_one_of_near_sign 1 (X 1 1) (X 1 3) (X 3 1) (X 3 3) (by ring) h2
    (by simpa using hm' 1) (by simpa using hm' 3)
    (by have h := sq 1 1; rw [q] at h; simp [z10, z12, z01, z21] at h; linear_combination h)
    (by have h := sq 1 3; rw [q] at h; simp [z10, z12, z03, z23] at h; linear_combination h)
    (by have h := sq 3 1; rw [q] at h; simp [z30, z32, z01, z21] at h; linear_combination h)
    (by have h := sq 3 3; rw [q] at h; simp [z30, z32, z03, z23] at h; linear_combination h)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eAB, z01, z03, z10, z12, z21, z23, z30, z32, a0, b0, c0, d0, a1, b1, c1, d1]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem mem_lev_iff {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {T : Type} [AddCommGroup T]
    [Module A T] {t : A} (ht : Irreducible t) (n : ℕ) (x : T) : x ∈ lev A T n ↔ ∃ w, t ^ n • w = x := by
  have hm : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht
  show x ∈ maximalIdeal A ^ n • (⊤ : Submodule A T) ↔ _
  rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem mem_of_bij {A : Type} [CommRing A] {T : Type} [AddCommGroup T] [Module A T] [Module.Finite A T]
    (f : T →ₗ[A] T) (hf : Function.Surjective f) (Q : Submodule A T) (hQ : Q ≤ Q.comap f) {y : T} (hy : f y ∈ Q) :
    y ∈ Q := by
  let g := Q.mapQ Q f hQ
  have hs : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨w, rfl⟩ := hf x
    exact ⟨Q.mkQ w, by simp [g]⟩
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hs
  have h0 : g (Q.mkQ y) = g 0 := by
    simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply, map_zero]
    exact (Submodule.Quotient.mk_eq_zero Q).2 hy
  have h1 := hi h0
  simpa using h1

theorem UpperTheory.V.Ws.Bl.divStep :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → ∀ t : A, Irreducible t → ∀ n, ∀ z ∈ Zn ρ c N H P (n + 1), ¬ Prim z →
          ∃ z' ∈ Zn ρ c N H P n, ∀ g x, (lev A T n).mkQ x = z' g → (lev A T (n + 1)).mkQ (t • x) = z g := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL t ht n z hz hnp
  obtain ⟨y, hzy⟩ := hz
  have ht0 : t ≠ 0 := ht.ne_zero
  have hinjt : Function.Injective (fun x : T => t • x) := smul_right_injective T ht0
  have hlev := fun k x => mem_lev_iff (T := T) ht k x
  have hφ : lev A T n ≤ (lev A T (n + 1)).comap (t • LinearMap.id) := by
    intro x hx
    obtain ⟨w, rfl⟩ := (hlev n x).1 hx
    rw [Submodule.mem_comap]
    refine (hlev (n + 1) _).2 ⟨w, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]
  let φ := (lev A T n).mapQ (lev A T (n + 1)) (t • LinearMap.id) hφ
  have hφmk : ∀ x, φ ((lev A T n).mkQ x) = (lev A T (n + 1)).mkQ (t • x) := fun x => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [hφmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha
    obtain ⟨w, hw⟩ := (hlev (n + 1) _).1 ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (hlev n x).2 ⟨w, hinjt ?_⟩
    simp only
    rw [← hw, pow_succ', mul_smul]
  have hφP : ∀ a, φ a ∈ Submodule.map (lev A T (n + 1)).mkQ P →
      a ∈ Submodule.map (lev A T n).mkQ P := by
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    obtain ⟨q, hq, hqe⟩ := Submodule.mem_map.1 ha
    rw [hφmk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hqe
    obtain ⟨v, hv⟩ := (hlev (n + 1) _).1 hqe
    have hq' : t • (x + t ^ n • v) ∈ P := by
      have e : t • (x + t ^ n • v) = q := by
        rw [smul_add, ← mul_smul, ← pow_succ', hv]
        abel
      rw [e]
      exact hq
    have hxP := hL.sat t _ ht0 hq'
    refine Submodule.mem_map.2 ⟨x + t ^ n • v, hxP, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact (hlev n _).2 ⟨v, by abel⟩
  have hφρ : ∀ g a, φ (modRep ρ n g a) = modRep ρ (n + 1) g (φ a) := by
    intro g a
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [modRep_mk, hφmk, hφmk, modRep_mk, LinearMap.map_smul (ρ g) t x]
  have hz1 : ∀ g, z g ∈ Submodule.map (lev A T (n + 1)).mkQ (lev A T 1) := by
    intro g
    by_contra hc
    exact hnp ⟨g, hc⟩
  have hrange : ∀ g, ∃ a, φ a = z g := by
    intro g
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 g)
    obtain ⟨w, rfl⟩ := (hlev 1 u).1 hu
    refine ⟨(lev A T n).mkQ w, ?_⟩
    rw [hφmk, ← hue, pow_one]
  choose z' hz' using hrange
  obtain ⟨s, hsH, hsb⟩ := hL.fr
  obtain ⟨y0, rfl⟩ := (lev A T (n + 1)).mkQ_surjective y
  have hle1 : lev A T (n + 1) ≤ lev A T 1 :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
  have hy0 : y0 ∈ P ⊔ lev A T 1 := by
    let f : T →ₗ[A] T := ρ s - LinearMap.id
    have hfs : Function.Surjective f := hsb.2
    apply mem_of_bij f hfs
    · intro x hx
      rw [Submodule.mem_comap]
      show ρ s x - x ∈ _
      apply Submodule.sub_mem _ _ hx
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
      refine Submodule.mem_sup.2 ⟨ρ s p, hL.stab s hsH p hp, ρ s q, ?_, (map_add _ _ _).symm⟩
      obtain ⟨w, rfl⟩ := (hlev 1 q).1 hq
      exact (hlev 1 _).2 ⟨ρ s w, (map_smul _ _ _).symm⟩
    · show ρ s y0 - y0 ∈ _
      have hloc : z s - (modRep ρ (n + 1) s ((lev A T (n + 1)).mkQ y0) - (lev A T (n + 1)).mkQ y0)
          ∈ Submodule.map (lev A T (n + 1)).mkQ P := hzy.loc s hsH
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hloc
      obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 s)
      rw [modRep_mk, ← hue, ← map_sub, ← map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at hpe
      have e : ρ s y0 - y0 = ((p - (u - (ρ s y0 - y0))) + u) - p := by abel
      rw [e]
      apply Submodule.sub_mem _ _ (Submodule.mem_sup_left hp)
      apply Submodule.add_mem _ (Submodule.mem_sup_right (hle1 hpe)) (Submodule.mem_sup_right hu)
  obtain ⟨p0, hp0, q0, hq0, hpq⟩ := Submodule.mem_sup.1 hy0
  obtain ⟨w0, rfl⟩ := (hlev 1 q0).1 hq0
  subst hpq
  have hcomp : ⇑φ ∘ z' = z := funext hz'
  refine ⟨z', ⟨(lev A T n).mkQ w0, ?_⟩, ?_⟩
  · refine ⟨IsLocallyConstant.desc z' φ (by rw [hcomp]; exact hzy.lc) hφinj, ?_, ?_, ?_, ?_⟩
    · intro g h
      show z' (g * h) = z' g + modRep ρ n g (z' h)
      apply hφinj
      rw [hz', map_add (f := _), hφρ, hz', hz']
      exact hzy.coc g h
    · apply hφinj
      rw [hz', map_zero]
      exact hzy.cz
    · intro g hg
      apply hφinj
      rw [hz', map_zero]
      exact hzy.kill g hg
    · intro h hh
      show z' h - (modRep ρ n h ((lev A T n).mkQ w0) - (lev A T n).mkQ w0)
        ∈ Submodule.map (lev A T n).mkQ P
      apply hφP
      rw [map_sub, map_sub, hφρ, hz', hφmk]
      have hloc : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
          - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0)) ∈ Submodule.map (lev A T (n + 1)).mkQ P :=
        hzy.loc h hh
      have e : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (t • w0)) - (lev A T (n + 1)).mkQ (t • w0))
          = (z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
            - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))) + (lev A T (n + 1)).mkQ (ρ h p0 - p0) := by
        simp only [pow_one, map_add (f := _), map_sub, modRep_mk]
        abel
      rw [e]
      exact Submodule.add_mem _ hloc
        (Submodule.mem_map_of_mem (Submodule.sub_mem _ (hL.stab h hh p0 hp0) hp0))
  · intro g x hx
    rw [← hφmk, hx, hz']
end
