module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Polynomial
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
public import Mathlib.Data.Nat.Choose.Cast
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finsupp.Fin

@[expose] public section

section

open MvPolynomial

namespace GlobalTheory.ReesHomogeneous

variable {σ : Type} {R : Type} [CommRing R]

theorem homogeneousComponent_mul_of_homogeneous_left {S : Type} [CommRing S] {k : ℕ} (n : ℕ)
    {P : MvPolynomial σ S} (hP : P.IsHomogeneous k) (Q : MvPolynomial σ S) :
    homogeneousComponent n (P * Q) = if k ≤ n then P * homogeneousComponent (n - k) Q else 0 := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := S)
  have h := DirectSum.coe_decompose_mul_of_left_mem (homogeneousSubmodule σ S) (a := P) (b := Q) n
    ((mem_homogeneousSubmodule k P).2 hP)
  have e : ∀ (m : ℕ) (T : MvPolynomial σ S),
      ((DirectSum.decompose (homogeneousSubmodule σ S) T m : homogeneousSubmodule σ S m) :
        MvPolynomial σ S) = homogeneousComponent m T :=
    fun m T => MvPolynomial.decomposition.decompose'_apply T m
  rw [e, e] at h
  exact h

noncomputable def piece (I : Ideal R) (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (((AddMonoidAlgebra.coeff F m : reesAlgebra I) : Polynomial R).coeff e)

variable {I : Ideal R}

@[simp] theorem coeff_piece (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (piece I e F) m = (AddMonoidAlgebra.coeff F m).1.coeff e := by
  classical
  simp only [piece, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h]; rfl

@[simp] theorem piece_zero (e : ℕ) : piece I e (0 : MvPolynomial σ (reesAlgebra I)) = 0 := by
  ext m; simp

@[simp] theorem piece_add (e : ℕ) (F G : MvPolynomial σ (reesAlgebra I)) :
    piece I e (F + G) = piece I e F + piece I e G := by
  ext m; simp

theorem piece_X_mul (e : ℕ) (i : σ) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (X i * F) = X i * piece I e F := by
  classical
  ext m
  rw [coeff_piece, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp

theorem piece_C_mul (e : ℕ) (r : reesAlgebra I) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (C r * F) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal e, C ((r : Polynomial R).coeff p.1) * piece I p.2 F := by
  ext m
  simp [coeff_sum, coeff_C_mul, Polynomial.coeff_mul]

theorem piece_isHomogeneous (e : ℕ) {d : ℕ} {F : MvPolynomial σ (reesAlgebra I)}
    (hF : F.IsHomogeneous d) : (piece I e F).IsHomogeneous d := by
  intro m hm
  apply hF
  intro h
  apply hm
  rw [coeff_piece, h]
  simp

theorem coeff_piece_mem (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (piece I e F) m ∈ I ^ e := by
  rw [coeff_piece]
  exact (mem_reesAlgebra_iff I _).1 (AddMonoidAlgebra.coeff F m).2 e

end GlobalTheory.ReesHomogeneous

namespace GlobalTheory.ReesHomogeneous

variable {σ : Type} {R : Type} [CommRing R] {I : Ideal R}

theorem C_mul_mem_of_pow (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    ∀ (k : ℕ) (b : R), b ∈ I ^ k → ∀ (l t : ℕ) (P : MvPolynomial σ R), P.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff P m ∈ I ^ l) → P ∈ J l → C b * P ∈ J (l + k) := by
  intro k
  induction k with
  | zero =>
    intro b _ l t P _ _ hP
    simpa using (J l).mul_mem_left (C b) hP
  | succ k ih =>
    intro b hb l t P hPh hPc hP
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro x hx y hy
      have h1 := ih x hx l t P hPh hPc hP
      have h2 : ∀ m, AddMonoidAlgebra.coeff (C x * P) m ∈ I ^ (l + k) := by
        intro m
        rw [coeff_C_mul, pow_add, mul_comm (I ^ l)]
        exact Ideal.mul_mem_mul hx (hPc m)
      have h3 := H (l + k) t y (C x * P) hy (hPh.C_mul x) h2 h1
      rw [show C (x * y) * P = C y * (C x * P) by rw [C_mul]; ring]
      simpa [add_assoc] using h3
    · intro x y hx hy
      rw [C_add, add_mul]
      exact add_mem hx hy

def reesIdeal (I : Ideal R) (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    Ideal (MvPolynomial σ (reesAlgebra I)) where
  carrier := {F | ∀ d e, piece I e (homogeneousComponent d F) ∈ J e}
  zero_mem' := by intro d e; simp
  add_mem' := by
    intro F G hF hG d e
    rw [map_add (f := _), piece_add]
    exact add_mem (hF d e) (hG d e)
  smul_mem' := by
    intro c F hF
    rw [smul_eq_mul]
    revert F
    induction c using MvPolynomial.induction_on with
    | C r =>
      intro F hF d e
      rw [homogeneousComponent_C_mul, piece_C_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      have hpe : p.2 + p.1 = e := by rw [add_comm]; exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      rw [← hpe]
      exact C_mul_mem_of_pow J H p.1 _ ((mem_reesAlgebra_iff I _).1 r.2 p.1) p.2 d _
        (piece_isHomogeneous p.2 (homogeneousComponent_isHomogeneous d F))
        (coeff_piece_mem p.2 _) (hF d p.2)
    | add p q hp hq =>
      intro F hF d e
      rw [add_mul, map_add (f := _), piece_add]
      exact add_mem (hp hF d e) (hq hF d e)
    | mul_X p i hp =>
      intro F hF
      rw [mul_assoc]
      apply hp
      intro d e
      rw [homogeneousComponent_mul_of_homogeneous_left d (isHomogeneous_X _ i)]
      split_ifs
      · rw [piece_X_mul]
        exact (J e).mul_mem_left _ (hF _ e)
      · simp

end GlobalTheory.ReesHomogeneous

namespace GlobalTheory.ReesHomogeneous

theorem exists_homogeneous_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ 𝔞 : Ideal (MvPolynomial (Fin (n + 1)) (reesAlgebra I)), (∀ F ∈ 𝔞, ∀ d, homogeneousComponent d F ∈ 𝔞) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) (reesAlgebra I)), F.IsHomogeneous t → (F ∈ 𝔞 ↔ ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R), (∀ m, AddMonoidAlgebra.coeff G m = (AddMonoidAlgebra.coeff F m).1.coeff e) → G ∈ J e) := by
  intro R _ I n J H
  refine ⟨reesIdeal I J H, ?_, ?_⟩
  · intro F hF d d' e
    show piece I e (homogeneousComponent d' (homogeneousComponent d F)) ∈ J e
    rw [homogeneousComponent_of_mem (homogeneousComponent_mem d F)]
    split_ifs
    · exact hF d e
    · simp
  · intro t F hFt
    have hG : ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R),
        (∀ m, AddMonoidAlgebra.coeff G m = (AddMonoidAlgebra.coeff F m).1.coeff e) → G = piece I e F := by
      intro e G hG
      ext m
      rw [hG, coeff_piece]
    constructor
    · intro hF e G hGc
      rw [hG e G hGc]
      have := hF t e
      rwa [homogeneousComponent_eq_self hFt] at this
    · intro h d e
      show piece I e (homogeneousComponent d F) ∈ J e
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule t F).2 hFt)]
      split_ifs
      · exact h e _ fun m => coeff_piece e F m
      · simp

end GlobalTheory.ReesHomogeneous
end

section

open MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DPEval2

def bv (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • (X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)

def ex (p : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p.1 + Finsupp.single 1 p.2

theorem ex_injective : Function.Injective ex := by
  intro p q h
  have h0 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) h
  have h1 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 1) h
  simp [ex] at h0 h1
  exact Prod.ext h0 h1

theorem bv_eq (p : ℕ × ℕ) :
    bv p = ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • monomial (ex p) (1 : ℚ) := by
  rw [bv, ex, X_pow_eq_monomial, X_pow_eq_monomial, smul_monomial, smul_monomial,
    monomial_mul_monomial, smul_monomial]
  simp

theorem bv_li : LinearIndependent ℚ bv := by
  have h := ((basisMonomials (Fin 2) ℚ).linearIndependent.comp ex ex_injective).units_smul
    (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity))
  have e : bv = (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity)) •
      (⇑(basisMonomials (Fin 2) ℚ) ∘ ex) := by
    funext p
    simp [bv_eq, Units.smul_def, coe_basisMonomials]
  rw [e]; exact h

theorem ex_add (p q : ℕ × ℕ) : ex (p + q) = ex p + ex q := by
  simp only [ex, Prod.fst_add, Prod.snd_add, Finsupp.single_add]; abel

theorem bv_mul (p q : ℕ × ℕ) :
    bv p * bv q = ((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ) • bv (p + q) := by
  rw [bv_eq, bv_eq, bv_eq, smul_mul_smul, monomial_mul_monomial, ← ex_add,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_one]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul, Nat.cast_add_choose]
  field_simp

def D : Submodule ℤ (MvPolynomial (Fin 2) ℚ) := Submodule.span ℤ (Set.range bv)

theorem bv_mem (p : ℕ × ℕ) : bv p ∈ D := Submodule.subset_span ⟨p, rfl⟩

def β : Module.Basis (ℕ × ℕ) ℤ D := Module.Basis.span (bv_li.restrict_scalars' ℤ)

theorem β_eq (p : ℕ × ℕ) : β p = ⟨bv p, bv_mem p⟩ :=
  Module.Basis.span_apply _ p

theorem mul_mem {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) : x * y ∈ D := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [bv_mul]
    exact Submodule.smul_of_tower_mem _ _ (bv_mem _)
  · intro y _; simp
  · intro y _; simp
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro r x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  · intro r x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

variable {B : Type} [CommRing B] (u v : ℕ → B)

def ψ : D →ₗ[ℤ] B := β.constr ℤ fun p ↦ u p.1 * v p.2


open Classical in
def φ (q : MvPolynomial (Fin 2) ℚ) : B := by
  classical
  exact if h : q ∈ D then ψ u v ⟨q, h⟩ else 0

theorem φ_of_mem {q : MvPolynomial (Fin 2) ℚ} (h : q ∈ D) :
    φ u v q = ψ u v ⟨q, h⟩ := dite_eq_left h

theorem φ_bv (p : ℕ × ℕ) : φ u v (bv p) = u p.1 * v p.2 := by
  rw [φ_of_mem u v (bv_mem p), ← β_eq, ψ, Module.Basis.constr_basis]

theorem φ_add {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x + y) = φ u v x + φ u v y := by
  rw [φ_of_mem u v hx, φ_of_mem u v hy, φ_of_mem u v (add_mem hx hy), ← map_add (f := _)]; rfl

theorem φ_zsmul (z : ℤ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (z • x) = z • φ u v x := by
  rw [φ_of_mem u v hx, φ_of_mem u v (Submodule.smul_mem _ z hx), ← map_zsmul]; rfl

theorem φ_nsmul (n : ℕ) {x : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) : φ u v (n • x) = n • φ u v x := by
  rw [← Nat.cast_smul_eq_nsmul ℤ n x, φ_zsmul u v _ hx, Nat.cast_smul_eq_nsmul]

theorem φ_zero : φ u v 0 = 0 := by
  rw [φ_of_mem u v (zero_mem _)]; exact map_zero (ψ u v)

theorem φ_mul (hu : ∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n))
    (hv : ∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n))
    {x y : MvPolynomial (Fin 2) ℚ} (hx : x ∈ D) (hy : y ∈ D) :
    φ u v (x * y) = φ u v x * φ u v y := by
  refine Submodule.span_induction₂ (p := fun x y hx hy ↦ φ u v (x * y) = φ u v x * φ u v y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    rw [bv_mul, φ_nsmul u v _ (bv_mem _), φ_bv, φ_bv, φ_bv, nsmul_eq_mul]
    calc ((((p.1 + q.1).choose p.1 * (p.2 + q.2).choose p.2 : ℕ)) : B) * (u (p + q).1 * v (p + q).2)
        = (((p.1 + q.1).choose p.1 : B) * u (p.1 + q.1)) * (((p.2 + q.2).choose p.2 : B) * v (p.2 + q.2)) := by
          simp only [Prod.fst_add, Prod.snd_add, Nat.cast_mul]; ring
      _ = u p.1 * v p.2 * (u q.1 * v q.2) := by rw [← hu, ← hv]; ring
  · intro y _; simp [φ_zero]
  · intro y _; simp [φ_zero]
  · intro x y z hx hy hz h1 h2
    rw [add_mul, φ_add u v (mul_mem hx hz) (mul_mem hy hz), φ_add u v hx hy, h1, h2, add_mul]
  · intro x y z hx hy hz h1 h2
    rw [mul_add, φ_add u v (mul_mem hx hy) (mul_mem hx hz), φ_add u v hy hz, h1, h2, mul_add]
  · intro r x y hx hy h
    rw [smul_mul_assoc, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hx, h, smul_mul_assoc]
  · intro r x y hx hy h
    rw [mul_smul_comm, φ_zsmul u v r (mul_mem hx hy), φ_zsmul u v r hy, h, mul_smul_comm]

end GlobalTheory.DPEval2

namespace GlobalTheory


open DPEval2 in
theorem dpEval_two :
    ∀ (B : Type) [CommRing B] (u v : ℕ → B), u 0 = 1 → v 0 = 1 →
    (∀ m n, u m * u n = ((m + n).choose m : B) * u (m + n)) →
    (∀ m n, v m * v n = ((m + n).choose m : B) * v (m + n)) →
    ∃ φ : MvPolynomial (Fin 2) ℚ → B,
      (∀ a c : ℕ, φ (((a.factorial : ℚ)⁻¹ • MvPolynomial.X 0 ^ a) * ((c.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ c)) = u a * v c) ∧
      (∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        ∀ e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
          φ (d + e) = φ d + φ e ∧
          d * e ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)) ∧
          φ (d * e) = φ d * φ e) ∧
      (∀ z : ℤ, ∀ d ∈ Submodule.span ℤ (Set.range fun p : ℕ × ℕ ↦ ((p.1.factorial : ℚ)⁻¹ • (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • MvPolynomial.X 1 ^ p.2)),
        φ (z • d) = z • φ d) := by
  intro B _ u v _ _ hu hv
  refine ⟨DPEval2.φ u v, fun a c ↦ DPEval2.φ_bv u v (a, c), fun d hd e he ↦ ?_,
    fun z d hd ↦ DPEval2.φ_zsmul u v z hd⟩
  exact ⟨DPEval2.φ_add u v hd he, DPEval2.mul_mem hd he, DPEval2.φ_mul u v hu hv hd he⟩

end GlobalTheory
end
end

section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem isRegularLocalRing_atPrime_of_ringEquiv_isLocalization {B T T' : Type} [CommRing B]
    [IsRegularRing B] [CommRing T] [CommRing T'] [Algebra B T'] (M : Submonoid B)
    [IsLocalization M T'] (e : T ≃+* T') (𝔫 : Ideal T) [𝔫.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  letI : Algebra B T := ((e.symm : T' →+* T).comp (algebraMap B T')).toAlgebra
  let e' : T' ≃ₐ[B] T := AlgEquiv.ofRingEquiv (f := e.symm) (fun x => rfl)
  haveI : IsLocalization M T := IsLocalization.isLocalization_of_algEquiv M e'
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔫) (𝔫.comap (algebraMap B T)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime 𝔫) 𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime (𝔫.comap (algebraMap B T))) :=
    IsRegularRing.isRegularLocalRing_localization _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (𝔫.comap (algebraMap B T)).primeCompl
      (Localization.AtPrime (𝔫.comap (algebraMap B T))) (Localization.AtPrime 𝔫)).toRingEquiv

theorem isRegularLocalRing_atPrime_localization_tensor : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin r) k)) [𝔪.IsPrime] (𝔫 : Ideal (Localization.AtPrime 𝔪 ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫) := by
  intro k K _ _ _ r 𝔪 _ 𝔫 _
  letI : Algebra (MvPolynomial (Fin r) k ⊗[k] K)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    IsLocalization.tensorRight (Localization.AtPrime 𝔪) 𝔪.primeCompl
  let h : (MvPolynomial (Fin r) k ⊗[k] K) ≃+* MvPolynomial (Fin r) K :=
    (Algebra.TensorProduct.comm k (MvPolynomial (Fin r) k) K).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv
  haveI := IsLocalization.isLocalization_of_base_ringEquiv
    (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl)
    (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) h
  letI : Algebra (MvPolynomial (Fin r) K)
      (Localization.AtPrime 𝔪 ⊗[MvPolynomial (Fin r) k] (MvPolynomial (Fin r) k ⊗[k] K)) :=
    ((algebraMap (MvPolynomial (Fin r) k ⊗[k] K) _).comp h.symm.toRingHom).toAlgebra
  exact isRegularLocalRing_atPrime_of_ringEquiv_isLocalization
    (Submonoid.map h (Algebra.algebraMapSubmonoid (MvPolynomial (Fin r) k ⊗[k] K) 𝔪.primeCompl))
    (Algebra.TensorProduct.cancelBaseChange k (MvPolynomial (Fin r) k) (Localization.AtPrime 𝔪)
      (Localization.AtPrime 𝔪) K).symm.toRingEquiv 𝔫

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory

theorem exists_weightedHomogenisation {L : Type} [Field L] (Q : Subring L) (r : ℕ)
    (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ) (hwt : wt 0 = 1) (hz : (z 0 : L) ≠ 0)
    (P : MvPolynomial (Fin r) Q) :
    ∃ (N : ℕ) (F : MvPolynomial (Fin (r + 1)) Q), F.IsWeightedHomogeneous wt N ∧
      ((MvPolynomial.eval z F : Q) : L) = (z 0 : L) ^ N *
        MvPolynomial.eval₂ Q.subtype (fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ) P ∧
      ∀ α, ∃ β, F.coeff β = P.coeff α := by
  classical
  let d : (Fin r →₀ ℕ) → ℕ := fun α => ∑ i, α i * wt i.succ
  let N : ℕ := P.support.sup d
  let e : (Fin r →₀ ℕ) → (Fin (r + 1) →₀ ℕ) := fun α => Finsupp.cons (N - d α) α
  have he : Function.Injective e := fun a b h => by
    have := congrArg Finsupp.tail h
    simpa [e] using this
  have hd : ∀ α ∈ P.support, d α ≤ N := fun α h => Finset.le_sup (f := d) h
  refine ⟨N, ∑ α ∈ P.support, monomial (e α) (P.coeff α), ?_, ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun α hα => ?_
    refine isWeightedHomogeneous_monomial _ _ _ ?_
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ]
    have := hd α hα
    simp only [e, Finsupp.cons_zero, Finsupp.cons_succ, hwt, smul_eq_mul, mul_one]
    change N - d α + d α = N
    omega
  · rw [eval₂_eq', Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
    have h1 : (z 0 : L) ^ N = (z 0 : L) ^ (N - d α) * (z 0 : L) ^ d α := by
      rw [← pow_add, Nat.sub_add_cancel (hd α hα)]
    have h2 : (z 0 : L) ^ d α * ∏ i, ((z i.succ : L) / (z 0 : L) ^ wt i.succ) ^ α i
        = ∏ i, (z i.succ : L) ^ α i := by
      simp only [d]
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_comm (α i), pow_mul, ← mul_pow, mul_div_cancel₀ _ (pow_ne_zero _ hz)]
    simp only [e, Finsupp.cons_zero, Finsupp.cons_succ]
    push_cast
    rw [h1, ← h2, Subring.coe_subtype]
    ring
  · intro α
    refine ⟨e α, ?_⟩
    rw [coeff_sum]
    simp only [coeff_monomial, he.eq_iff]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (notMem_support_iff.mp h).symm

end GlobalTheory
end
