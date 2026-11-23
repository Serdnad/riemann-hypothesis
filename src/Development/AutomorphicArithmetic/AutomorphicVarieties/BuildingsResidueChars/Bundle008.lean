module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
public import Formalism.GradedWeylDivisibility.StatementA
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
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

namespace UpperTheory.V.Z.Sym.Glob

variable {K : Type} [Field K] {Δ τ : K}

private def hh (x y : Fin 3 → Lsq K Δ) : Lsq K Δ := ∑ i, x i * star (y i)

private theorem hh_star (x y : Fin 3 → Lsq K Δ) : star (hh x y) = hh y x := by
  simp only [hh, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem hh_unitary {N : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (hN : N ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ))
    (x y : Fin 3 → Lsq K Δ) : hh (N *ᵥ x) (N *ᵥ y) = hh x y := by
  change (N *ᵥ x) ⬝ᵥ star (N *ᵥ y) = x ⬝ᵥ star y
  rw [Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    (Matrix.mem_unitaryGroup_iff').1 hN, Matrix.one_mulVec, dotProduct_comm]

private theorem hh_right (x y z : Fin 3 → Lsq K Δ) (r : Lsq K Δ) :
    hh x (r • y - z) = star r * hh x y - hh x z := by
  simp only [hh, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_sub, star_mul']
  ring

private theorem hh_left (x y z : Fin 3 → Lsq K Δ) (r : Lsq K Δ) :
    hh (r • y - z) x = r * hh y x - hh z x := by
  simp only [hh, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem hh_expand (e v w : Fin 3 → Lsq K Δ) (x0 p q y0 r s : Lsq K Δ) :
    hh (x0 • e + p • v + q • w) (y0 • e + r • v + s • w) =
      x0 * star y0 * hh e e + x0 * star r * hh e v + x0 * star s * hh e w +
      p * star y0 * hh v e + p * star r * hh v v + p * star s * hh v w +
      q * star y0 * hh w e + q * star r * hh w v + q * star s * hh w w := by
  simp only [hh, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul']
  ring

private theorem trace_form (m x y : EL Δ τ) :
    QuadraticAlgebra.trace (m * x * star (sigL y)) =
      x.re * star y.re * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) +
      x.re * star y.im * (algebraMap K (Lsq K Δ) τ * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im)
        - (algebraMap K (Lsq K Δ) τ * m.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * m.im)) +
      x.im * star y.re * (algebraMap K (Lsq K Δ) τ * m.re + (algebraMap K (Lsq K Δ) τ ^ 2 - 2) * m.im) +
      x.im * star y.im * (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) := by
  simp only [QuadraticAlgebra.trace_def, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL]
  ring

private theorem gram_unit {M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (h : IsUnit M.det) :
    IsUnit (M * Mᴴ).det := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  exact h.mul (h.star)

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.exists_hermitian_form_of_unitary_rotation_basis :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K), τ ^ 2 - 4 ≠ 0 → ∀ N : Matrix (Fin 3) (Fin 3) (Lsq K Δ), N ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) →
        ∀ e v : Fin 3 → Lsq K Δ, N *ᵥ e = e → N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v →
        IsUnit (Matrix.of ![e, v, N *ᵥ v]).det →
        ∃ (c : Kˣ) (m : EL Δ τ), IsUnit m ∧ star (sigL m) = m ∧ ∀ x y : Sp Δ τ,
          herm (c : K) m x y = ∑ i, (x.1 • e + x.2.re • v + x.2.im • (N *ᵥ v)) i * star ((y.1 • e + y.2.re • v + y.2.im • (N *ᵥ v)) i) := by
  intro K _ _ Δ τ hτ N hN e v hNe hNv hdet
  obtain ⟨w, hw⟩ : ∃ w, w = N *ᵥ v := ⟨_, rfl⟩
  rw [← hw] at hNv hdet ⊢
  obtain ⟨t, ht⟩ : ∃ t, t = algebraMap K (Lsq K Δ) τ := ⟨_, rfl⟩
  have hst : star t = t := by
    rw [ht]; ext <;> simp
  obtain ⟨u, hu⟩ : ∃ u, u = algebraMap K (Lsq K Δ) (τ ^ 2 - 4)⁻¹ := ⟨_, rfl⟩
  have hsu : star u = u := by
    rw [hu]; ext <;> simp
  have hut : u * (t ^ 2 - 4) = 1 := by
    have : algebraMap K (Lsq K Δ) ((τ ^ 2 - 4)⁻¹ * (τ ^ 2 - 4)) = 1 := by
      rw [inv_mul_cancel₀ hτ, map_one]
    rw [map_mul, map_sub, map_pow, map_ofNat] at this
    rw [hu, ht]; exact this
  have h2t : IsUnit (2 - t) := by
    refine IsUnit.of_mul_eq_one (-(2 + t) * u) ?_
    linear_combination hut

  have hvw : hh e v = hh e w := by
    conv_lhs => rw [← hh_unitary hN e v, hNe, ← hw]
  have hew0 : hh e w = hh e (t • w - v) := by
    conv_lhs => rw [← hh_unitary hN e w, hNe, hNv, ← ht]
  rw [hh_right, hst] at hew0
  have hew : hh e w = 0 := by
    have : (2 - t) * hh e w = 0 := by linear_combination hew0 - hvw
    exact (h2t.mul_right_eq_zero).1 this
  have hev : hh e v = 0 := hvw.trans hew
  have hwe : hh w e = 0 := by rw [← hh_star, hew, star_zero]
  have hve : hh v e = 0 := by rw [← hh_star, hev, star_zero]
  have hww : hh w w = hh v v := by rw [hw, hh_unitary hN]
  have hsa : star (hh v v) = hh v v := hh_star _ _
  have hsc : star (hh e e) = hh e e := hh_star _ _
  have hb : hh w v = t * hh w w - hh v w := by
    have h := hh_unitary hN w v
    rw [← hw, hNv, ← ht, hh_left] at h
    exact h.symm

  have hG : IsUnit (hh e e * (hh v v * hh v v - hh v w * hh w v)) := by
    have h := gram_unit hdet
    have e1 : (Matrix.of ![e, v, w] * (Matrix.of ![e, v, w])ᴴ) =
        !![hh e e, hh e v, hh e w; hh v e, hh v v, hh v w; hh w e, hh w v, hh w w] := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, hh, Fin.sum_univ_three, Matrix.conjTranspose_apply]
    rw [e1, Matrix.det_fin_three] at h
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.cons_val_fin_one, hev, hew, hve, hwe, hww] at h
    convert h using 1
    ring
  have hc : IsUnit (hh e e) := isUnit_of_mul_isUnit_left hG
  have hq : IsUnit (hh v v * hh v v - hh v w * hh w v) := isUnit_of_mul_isUnit_right hG

  have him : (hh e e).im = 0 := by
    have h := congrArg QuadraticAlgebra.im hsc
    rw [QuadraticAlgebra.im_star] at h
    have h2 : (2 : K) * (hh e e).im = 0 := by linear_combination -h
    simpa using h2
  have hce : hh e e = algebraMap K (Lsq K Δ) (hh e e).re := by
    ext <;> simp [him]
  have hc0 : (hh e e).re ≠ 0 := by
    intro h0
    rw [hce, h0, map_zero] at hc
    exact not_isUnit_zero hc
  obtain ⟨a, ha⟩ : ∃ a, a = hh v v := ⟨_, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b, b = hh w v := ⟨_, rfl⟩
  have hvw' : hh v w = t * a - b := by
    rw [hww, ← ha, ← hb'] at hb
    linear_combination hb
  have hsb : star b = t * a - b := by
    rw [hb', hh_star, ← hb', hvw']
  have hsa' : star a = a := by rw [ha, hsa]
  obtain ⟨m, hm⟩ : ∃ m : EL Δ τ, m = ⟨u * ((t ^ 2 - 2) * a - t * b), u * (2 * b - t * a)⟩ := by
    rw [ht]; exact ⟨_, rfl⟩
  subst ht
  have hm0 : m.re = u * (((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * a - algebraMap K (Lsq K Δ) τ * b) := by rw [hm]
  have hm1 : m.im = u * (2 * b - algebraMap K (Lsq K Δ) τ * a) := by rw [hm]
  have hT0 : 2 * m.re + algebraMap K (Lsq K Δ) τ * m.im = a := by
    rw [hm0, hm1]; linear_combination a * hut
  have hT1 : algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im = b := by
    rw [hm0, hm1]; linear_combination b * hut
  have hs0 : star m.re = u * (algebraMap K (Lsq K Δ) τ * b - 2 * a) := by
    rw [hm0]
    simp only [star_mul', star_sub, star_pow, hsu, hst, hsa', hsb, star_ofNat]
    ring
  have hs1 : star m.im = u * (algebraMap K (Lsq K Δ) τ * a - 2 * b) := by
    rw [hm1]
    simp only [star_mul', star_sub, hsu, hst, hsa', hsb, star_ofNat]
    ring
  refine ⟨Units.mk0 _ hc0, m, ?_, ?_, ?_⟩
  · rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
    have hn : (4 - (algebraMap K (Lsq K Δ) τ) ^ 2) * QuadraticAlgebra.norm m = a * a - (algebraMap K (Lsq K Δ) τ * a - b) * b := by
      rw [QuadraticAlgebra.norm_def, hm0, hm1]
      linear_combination (u * ((algebraMap K (Lsq K Δ) τ) ^ 2 - 4) + 1) * (a * a - (algebraMap K (Lsq K Δ) τ * a - b) * b) * hut
    rw [hvw', ← hb', ← ha] at hq
    rw [← hn] at hq
    exact isUnit_of_mul_isUnit_right hq
  · refine QuadraticAlgebra.ext ?_ ?_
    · rw [QuadraticAlgebra.re_star]
      change star m.re + algebraMap K (Lsq K Δ) τ * star m.im = m.re
      rw [hs0, hs1, hm0]
      ring
    · rw [QuadraticAlgebra.im_star]
      change -star m.im = m.im
      rw [hs1, hm1]
      ring
  · intro x y
    change herm _ m x y = hh _ _
    rw [hh_expand, herm, trace_form, hT0, hT1, hev, hew, hve, hwe, hww, hvw', ← ha, ← hb', Units.val_mk0, ← hce]
    ring
end

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {Δ τ : K}

private theorem sigL_mul' (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL]

private theorem sigL_sigL' (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sigL_one' : sigL (1 : EL Δ τ) = 1 := by
  ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem trace_sigL (x : EL Δ τ) : QuadraticAlgebra.trace (sigL x) = star (QuadraticAlgebra.trace x) := by
  have e : star (algebraMap K (Lsq K Δ) τ) = algebraMap K (Lsq K Δ) τ := by
    ext <;> simp
  simp [QuadraticAlgebra.trace_def, sigL, e]

private theorem eq_zero_of_trace (hτ : τ ^ 2 - 4 ≠ 0) {w : EL Δ τ}
    (h : ∀ x, QuadraticAlgebra.trace (w * x) = 0) : w = 0 := by
  have h1 := h 1
  have h2 := h QuadraticAlgebra.omega
  simp [QuadraticAlgebra.trace_def] at h1 h2
  have hu : IsUnit (algebraMap K (Lsq K Δ) (τ ^ 2 - 4)) := (IsUnit.mk0 _ hτ).map _
  rw [map_sub, map_pow, map_ofNat] at hu
  refine QuadraticAlgebra.ext ?_ ?_
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * h1 - (algebraMap K (Lsq K Δ) τ) * h2
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination 2 * h2 - (algebraMap K (Lsq K Δ) τ) * h1

end SlopeTestRemainingChoices

theorem UpperTheory.sigL_eq_of_herm_semilinear_eq_star :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ c : K) (d m : EL Δ τ), τ ^ 2 - 4 ≠ 0 →
        (∀ x y : Sp Δ τ, herm c m (semi d x) (semi d y) = star (herm c m x y)) → sigL m = m * d * star (sigL d) := by
  intro K _ _ Δ τ c d m hτ h
  have key : ∀ a : EL Δ τ, QuadraticAlgebra.trace ((m * d * star (sigL d) - sigL m) * a) = 0 := fun a => by
    have e := h (0, sigL a) (0, 1)
    simp only [herm, semi, star_zero, mul_zero, zero_mul, zero_add, sigL_sigL', sigL_one', mul_one, star_one,
      sigL_mul'] at e
    rw [← trace_sigL, sigL_mul', sigL_sigL'] at e
    rw [sub_mul, map_sub, sub_eq_zero, ← e]
    congr 1
    ring
  exact (sub_eq_zero.1 (eq_zero_of_trace hτ key)).symm
end

section

open MvPolynomial Formalism.GradedWeylDivisibility

theorem UpperTheory.bideterminant_antidiag_eval_weight_unit_support :
    ∀ (R : Type) [CommRing R] (n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n), (∀ x : Matrix (Fin n) (Fin n) R, (∀ i j, j < i → x i j = 0) → eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (rowAct R x.transpose (bideterminant R sz hsz I)) = (∏ i, x i i ^ shapeDeg sz (Fin.rev i)) * eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I)) ∧ ((∀ k p, (I k p : ℕ) + sz k = n + p) → IsUnit (eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I))) ∧ ((∀ k, StrictMono (I k)) → eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I) ≠ 0 → ∀ k p, (I k p : ℕ) + sz k = n + p) := by
  intro R _ n K sz hsz I
  have hrev : ∀ {s : ℕ} (hs : s ≤ n) (a : Fin n) (r : Fin s),
      a = Fin.rev (Fin.castLE hs r) ↔ (a : ℕ) + r + 1 = n := by
    intro s hs a r
    rw [Fin.ext_iff, Fin.val_rev, Fin.coe_castLE]
    have := a.isLt
    have := r.isLt
    omega
  have key : ∀ φ : MvPolynomial (Fin n × Fin n) R →+* R, φ (bideterminant R sz hsz I) =
      ∏ k, (Matrix.of fun p q : Fin (sz k) => φ (X (I k p, Fin.castLE (hsz k) q))).det := by
    intro φ
    simp only [bideterminant, initMinor, map_prod, RingHom.map_det]
    rfl
  have hE : eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0) (bideterminant R sz hsz I)
      = ∏ k, (Matrix.of fun p q : Fin (sz k) => if (I k p : ℕ) + q + 1 = n then (1 : R) else 0).det := by
    rw [key]
    congr 1
    ext k
    congr 1
    ext p q
    simp [hrev]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hR : eval (fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0)
        (rowAct R x.transpose (bideterminant R sz hsz I)) =
        ∏ k, (Matrix.of fun p q : Fin (sz k) => x (Fin.rev (Fin.castLE (hsz k) q)) (I k p)).det := by
      refine (key ((eval fun v : Fin n × Fin n => if v.1 = Fin.rev v.2 then (1 : R) else 0).comp
        (rowAct R x.transpose).toRingHom)).trans ?_
      congr 1
      ext k
      congr 1
      ext p q
      simp [rowAct, Matrix.transpose_apply, mul_ite, Finset.sum_ite_eq']
    have hk : ∀ (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n),
        (Matrix.of fun p q : Fin s => x (Fin.rev (Fin.castLE hs q)) (J p)).det =
        (Matrix.of fun p q : Fin s => if (J p : ℕ) + q + 1 = n then (1 : R) else 0).det *
          ∏ q : Fin s, x (Fin.rev (Fin.castLE hs q)) (Fin.rev (Fin.castLE hs q)) := by
      intro s hs J
      have hU : (Matrix.of fun r q : Fin s =>
          x (Fin.rev (Fin.castLE hs q)) (Fin.rev (Fin.castLE hs r))).IsUpperTriangular := by
        intro r q hqr
        simp only [id, Matrix.of_apply] at hqr ⊢
        apply hx
        rw [Fin.lt_iff_val_lt_val] at hqr ⊢
        simp only [Fin.val_rev, Fin.coe_castLE]
        have := r.isLt
        omega
      have hdU := Matrix.det_of_upperTriangular hU
      simp only [Matrix.of_apply] at hdU
      rw [← hdU, ← Matrix.det_mul]
      congr 1
      ext p q
      simp only [Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
      have hJ := (J p).isLt
      have hq := q.isLt
      by_cases h : (J p : ℕ) + s < n
      · rw [Finset.sum_eq_zero]
        · apply hx
          rw [Fin.lt_iff_val_lt_val]
          simp only [Fin.val_rev, Fin.coe_castLE]
          omega
        · intro r _
          rw [if_neg]
          have := r.isLt
          omega
      · rw [Finset.sum_eq_single (⟨n - 1 - (J p : ℕ), by omega⟩ : Fin s)]
        · rw [if_pos (by simp only; omega)]
          congr 1
          ext
          simp only [Fin.val_rev, Fin.coe_castLE]
          omega
        · intro b _ hb
          rw [if_neg]
          intro h'
          apply hb
          ext
          simp only
          omega
        · intro h'
          exact absurd (Finset.mem_univ _) h'
    have hreg : ∀ k, ∏ q : Fin (sz k), x (Fin.rev (Fin.castLE (hsz k) q)) (Fin.rev (Fin.castLE (hsz k) q))
        = ∏ i : Fin n, if ((Fin.rev i : Fin n) : ℕ) < sz k then x i i else 1 := by
      intro k
      rw [← Finset.prod_filter]
      refine Finset.prod_bij (fun q _ => Fin.rev (Fin.castLE (hsz k) q)) ?_ ?_ ?_ ?_
      · intro q _
        simp
        have := q.isLt
        have := hsz k
        omega
      · intro a _ b _ h
        simpa using h
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        refine ⟨⟨(Fin.rev b : ℕ), hb⟩, Finset.mem_univ _, ?_⟩
        ext
        simp only [Fin.val_rev, Fin.coe_castLE]
        have := b.isLt
        omega
      · intro q _
        rfl
    rw [hR, hE, Finset.prod_congr rfl (fun k _ => hk (sz k) (hsz k) (I k)),
      Finset.prod_mul_distrib, mul_comm]
    congr 1
    rw [Finset.prod_congr rfl (fun k _ => hreg k), Finset.prod_comm]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rfl
  · intro hI
    rw [hE]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro k _
    have hP : (Matrix.of fun p q : Fin (sz k) => if (I k p : ℕ) + q + 1 = n then (1 : R) else 0)
        = (Fin.revPerm).permMatrix R := by
      ext p q
      have h1 := hI k p
      have h2 := p.isLt
      have h3 := q.isLt
      have h4 := hsz k
      have hiff : ((I k p : ℕ) + q + 1 = n) ↔ q ∈ (Fin.revPerm : Equiv.Perm (Fin (sz k))).toPEquiv p := by
        simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply,
          Fin.ext_iff, Fin.val_rev]
        constructor <;> intro <;> omega
      rw [Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      exact if_congr hiff rfl rfl
    rw [hP, Matrix.det_permutation]
    exact (Units.isUnit _).map (Int.castRingHom R)
  · intro hmono hne k p
    rw [hE] at hne
    have hdet : (Matrix.of fun p q : Fin (sz k) =>
        if (I k p : ℕ) + q + 1 = n then (1 : R) else 0).det ≠ 0 :=
      fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ k) h0)
    have hlow : ∀ p : Fin (sz k), n ≤ (I k p : ℕ) + sz k := by
      intro p
      by_contra hlt
      push_neg at hlt
      apply hdet
      apply Matrix.det_eq_zero_of_row_eq_zero p
      intro q
      simp only [Matrix.of_apply]
      rw [if_neg]
      have := q.isLt
      omega
    have hA : ∀ d : ℕ, ∀ a b : Fin (sz k), (b : ℕ) = a + d → (I k a : ℕ) + d ≤ I k b := by
      intro d
      induction d with
      | zero =>
        intro a b h
        have : a = b := Fin.ext (by omega)
        subst this
        simp
      | succ d ih =>
        intro a b h
        have hb' : (a : ℕ) + d < sz k := by
          have := b.isLt
          omega
        have h1 := ih a ⟨a + d, hb'⟩ rfl
        have h2 : I k ⟨a + d, hb'⟩ < I k b := hmono k (by rw [Fin.lt_iff_val_lt_val]; simp only; omega)
        rw [Fin.lt_iff_val_lt_val] at h2
        omega
    have hs : 0 < sz k := by
      have := p.isLt
      omega
    have h0 := hA p ⟨0, hs⟩ p (by simp)
    have hl := hlow ⟨0, hs⟩
    have h1 := hA (sz k - 1 - p) p ⟨sz k - 1, by omega⟩ (by simp only; have := p.isLt; omega)
    have := (I k ⟨sz k - 1, by omega⟩).isLt
    omega
end
