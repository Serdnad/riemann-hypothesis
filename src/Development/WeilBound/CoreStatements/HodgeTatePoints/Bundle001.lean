module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

section

open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Ra

theorem carry : ∀ (p f : ℕ), 2 ≤ p → 0 < f → ∀ (y : ℕ → NNReal), (∀ n, y (n + f) = y n) → (∀ n, y n ≤ 1) → (∀ n, y n ^ p ≤ y (n + 1)) → ∀ (e : Fin f → ℕ) (j : ℕ), 2 ≤ ∑ n, e n → (∑ n : Fin f, e n * p ^ (n : ℕ)) ≡ p ^ (j + 1) [MOD (p ^ f - 1)] → ∏ n : Fin f, y n ^ e n ≤ y j ^ p := by
  intro p f hp hf y hper hle1 hstep e j he hcong
  have hperm : ∀ a c, y (a + f * c) = y a := by
    intro a c
    induction c with
    | zero => simp
    | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have hiter : ∀ a k, y a ^ (p ^ k) ≤ y (a + k) := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ← Nat.add_assoc]
      exact (pow_le_pow_left₀ zero_le ih p).trans (hstep _)
  obtain ⟨q, s, hs, hj⟩ : ∃ q s, s < f ∧ j = s + f * q :=
    ⟨j / f, j % f, Nat.mod_lt _ hf, (Nat.mod_add_div j f).symm⟩
  have hk : ∀ n : Fin f, ∃ k c m c', k + m = f - 1 ∧ (n : ℕ) + k = s + f * c ∧
      m + (j + 1) = n + f * c' := by
    intro n
    have hn := n.isLt
    by_cases h : (n : ℕ) ≤ s
    · refine ⟨s - n, 0, f - 1 - (s - n), q + 1, by omega, by omega, ?_⟩
      rw [hj, Nat.mul_succ]
      omega
    · refine ⟨s + f - n, 1, f - 1 - (s + f - n), q, by omega, by omega, ?_⟩
      rw [hj]
      omega
  choose k c m c' hkm hkc hmc using hk
  have hyk : ∀ n : Fin f, y n ^ (p ^ k n) ≤ y j := by
    intro n
    have := hiter n (k n)
    rw [hkc, hperm] at this
    rw [hj, hperm]
    exact this
  have hpos : 1 ≤ p := by omega
  have hN : p ^ f - 1 + 1 = p ^ f := Nat.sub_add_cancel (Nat.one_le_pow _ _ hpos)
  have hT1 : (∑ n : Fin f, e n * p ^ m n) ≡ 1 [MOD (p ^ f - 1)] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have hc := (ZMod.natCast_eq_natCast_iff _ _ _).2 hcong
    push_cast at hc ⊢
    set u : ZMod (p ^ f - 1) := (p : ZMod (p ^ f - 1)) with hu
    have huf : u ^ f = 1 := by
      rw [hu, ← Nat.cast_pow, ← hN, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    have hper' : ∀ a c, u ^ (a + f * c) = u ^ a := by
      intro a c
      rw [pow_add, pow_mul, huf, one_pow, mul_one]
    have hunit : IsUnit (u ^ (j + 1)) := by
      refine IsUnit.pow _ (isUnit_iff_exists_inv.2 ⟨u ^ (f - 1), ?_⟩)
      rw [← pow_succ', Nat.sub_add_cancel hf, huf]
    have hmul : (∑ n : Fin f, (e n : ZMod (p ^ f - 1)) * u ^ m n) * u ^ (j + 1) = u ^ (j + 1) := by
      refine (Finset.sum_mul _ _ _).trans ((Finset.sum_congr rfl fun n _ => ?_).trans hc)
      rw [mul_assoc, ← pow_add, hmc, hper']
    have h0 : ((∑ n : Fin f, (e n : ZMod (p ^ f - 1)) * u ^ m n) - 1) * u ^ (j + 1) = 0 := by
      rw [sub_mul, hmul, one_mul, sub_self]
    exact sub_eq_zero.1 (hunit.mul_left_eq_zero.1 h0)
  have hT2 : 2 ≤ ∑ n : Fin f, e n * p ^ m n :=
    le_trans he (Finset.sum_le_sum fun n _ => Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have hTf : p ^ f ≤ ∑ n : Fin f, e n * p ^ m n := by
    have hd := (Nat.modEq_iff_dvd' (by omega : 1 ≤ ∑ n : Fin f, e n * p ^ m n)).1 hT1.symm
    have hle := Nat.le_of_dvd (by omega) hd
    generalize p ^ f = P at *
    generalize ∑ n : Fin f, e n * p ^ m n = T at *
    omega
  have hP : 0 < p ^ (f - 1) := pow_pos (by omega) _
  refine (pow_le_pow_iff_left₀ zero_le zero_le hP.ne').1 ?_
  calc (∏ n : Fin f, y n ^ e n) ^ p ^ (f - 1)
      = ∏ n : Fin f, (y n ^ p ^ k n) ^ (e n * p ^ m n) := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun n _ => ?_
        rw [← pow_mul, ← pow_mul]
        congr 1
        rw [← hkm n, pow_add]
        ring
    _ ≤ ∏ n : Fin f, y j ^ (e n * p ^ m n) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le) fun n _ => pow_le_pow_left₀ zero_le (hyk n) _
    _ = y j ^ (∑ n : Fin f, e n * p ^ m n) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ y j ^ p ^ f := pow_le_pow_of_le_one zero_le (hle1 j) hTf
    _ = (y j ^ p) ^ p ^ (f - 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 2
        omega

end PositivityTheory.HtPt.Ra
end

section

open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Pmono

lemma prod_digits_sq (p f : ℕ) (P : NNReal) (y : Fin f → NNReal) (hy : ∀ n, y n ^ (p - 1) = P) :
    (∏ d : Fin f → Fin p, ∏ n, y n ^ (d n : ℕ)) ^ 2 = P ^ (f * p ^ f) := by
  have hrev : ∏ d : Fin f → Fin p, ∏ n, y n ^ ((Fin.rev (d n) : Fin p) : ℕ) =
      ∏ d : Fin f → Fin p, ∏ n, y n ^ (d n : ℕ) :=
    Fintype.prod_equiv (Equiv.piCongrRight fun _ => Fin.revPerm) _ _ (fun d => rfl)
  rw [sq]
  nth_rewrite 2 [← hrev]
  rw [← Finset.prod_mul_distrib]
  have hterm : ∀ d : Fin f → Fin p,
      (∏ n, y n ^ (d n : ℕ)) * ∏ n, y n ^ ((Fin.rev (d n) : Fin p) : ℕ) = P ^ f := by
    intro d
    rw [← Finset.prod_mul_distrib]
    have h : ∀ n, y n ^ (d n : ℕ) * y n ^ ((Fin.rev (d n) : Fin p) : ℕ) = P := by
      intro n
      rw [← pow_add, Fin.val_rev, ← hy n]
      congr 1
      have := (d n).isLt
      omega
    rw [Finset.prod_congr rfl (fun n _ => h n)]
    simp
  rw [Finset.prod_congr rfl (fun d _ => hterm d)]
  simp [← pow_mul, mul_comm]

lemma eq_of_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → NNReal) (ha : ∀ i, 0 < a i)
    (hab : ∀ i, a i ≤ b i) (h : ∏ i, b i = ∏ i, a i) (i : ι) : b i = a i := by
  refine le_antisymm ?_ (hab i)
  have hQ : 0 < ∏ j ∈ Finset.univ.erase i, a j := Finset.prod_pos (fun j _ => ha j)
  have h1 : ∏ j ∈ Finset.univ.erase i, a j ≤ ∏ j ∈ Finset.univ.erase i, b j :=
    Finset.prod_le_prod' (fun j _ => hab j)
  have h2 : b i * ∏ j ∈ Finset.univ.erase i, a j ≤ a i * ∏ j ∈ Finset.univ.erase i, a j :=
    calc b i * ∏ j ∈ Finset.univ.erase i, a j ≤ b i * ∏ j ∈ Finset.univ.erase i, b j :=
          mul_le_mul' le_rfl h1
      _ = ∏ j, b j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
      _ = ∏ j, a j := h
      _ = a i * ∏ j ∈ Finset.univ.erase i, a j := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  exact le_of_mul_le_mul_right h2 hQ

theorem count : ∀ (p f : ℕ), 2 ≤ p → ∀ (P : NNReal), P ≠ 0 → ∀ (x xD : Fin f → NNReal) (X XD : (Fin f → Fin p) → NNReal), (∀ n, (x n * xD n) ^ (p - 1) = P) → (∀ d, ∏ n, x n ^ (d n : ℕ) ≤ X d) → (∀ d, ∏ n, xD n ^ (d n : ℕ) ≤ XD d) → (∏ d, X d * XD d) ^ 2 = P ^ (f * p ^ f) → ∀ d, X d = ∏ n, x n ^ (d n : ℕ) ∧ XD d = ∏ n, xD n ^ (d n : ℕ) := by
  intro p f hp P hP x xD X XD hxy hX hXD hprod d
  have hne : ∀ n, x n ≠ 0 ∧ xD n ≠ 0 := by
    intro n
    have hmul : x n * xD n ≠ 0 := by
      intro h0
      have h := hxy n
      rw [h0, zero_pow (by omega)] at h
      exact hP h.symm
    exact ⟨left_ne_zero_of_mul hmul, right_ne_zero_of_mul hmul⟩
  have hApos : ∀ d : Fin f → Fin p, 0 < ∏ n, x n ^ (d n : ℕ) :=
    fun d => Finset.prod_pos (fun n _ => pow_pos (pos_iff_ne_zero.mpr (hne n).1) _)
  have hBpos : ∀ d : Fin f → Fin p, 0 < ∏ n, xD n ^ (d n : ℕ) :=
    fun d => Finset.prod_pos (fun n _ => pow_pos (pos_iff_ne_zero.mpr (hne n).2) _)
  have hsq : (∏ d : Fin f → Fin p, (∏ n, x n ^ (d n : ℕ)) * ∏ n, xD n ^ (d n : ℕ)) ^ 2 =
      P ^ (f * p ^ f) := by
    rw [← PositivityTheory.HtPt.Pmono.prod_digits_sq p f P (fun n => x n * xD n) hxy]
    congr 1
    refine Finset.prod_congr rfl fun d _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun n _ => (mul_pow _ _ _).symm
  have heq : ∏ d, X d * XD d = ∏ d : Fin f → Fin p, (∏ n, x n ^ (d n : ℕ)) * ∏ n, xD n ^ (d n : ℕ) :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp (hprod.trans hsq.symm)
  have hd := PositivityTheory.HtPt.Pmono.eq_of_prod_eq
    (fun d : Fin f → Fin p => (∏ n, x n ^ (d n : ℕ)) * ∏ n, xD n ^ (d n : ℕ))
    (fun d => X d * XD d) (fun d => mul_pos (hApos d) (hBpos d))
    (fun d => mul_le_mul' (hX d) (hXD d)) heq d
  have hXDpos : 0 < XD d := lt_of_lt_of_le (hBpos d) (hXD d)
  have hXpos : 0 < X d := lt_of_lt_of_le (hApos d) (hX d)
  constructor
  · refine le_antisymm ?_ (hX d)
    have h1 : X d * XD d ≤ (∏ n, x n ^ (d n : ℕ)) * XD d :=
      hd.le.trans (mul_le_mul' le_rfl (hXD d))
    exact le_of_mul_le_mul_right h1 hXDpos
  · refine le_antisymm ?_ (hXD d)
    have h1 : X d * XD d ≤ X d * ∏ n, xD n ^ (d n : ℕ) :=
      hd.le.trans (mul_le_mul' (hX d) le_rfl)
    exact le_of_mul_le_mul_left h1 hXpos

end PositivityTheory.HtPt.Pmono
end

section

noncomputable section

namespace PositivityTheory.HtPt.Htat.Lie

open TensorProduct

theorem bijective_of_cover {R M N J : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : J → R) (hf : Ideal.span (Set.range f) = ⊤) (φ : M →ₗ[R] N)
    (h : ∀ i, ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Module R Q) (a : N →ₗ[R] Q),
      IsLocalizedModule (Submonoid.powers (f i)) a ∧ IsLocalizedModule (Submonoid.powers (f i)) (a ∘ₗ φ)) :
    Function.Bijective φ := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hf m ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨Q, _, _, a, -, h2⟩ := h i
    have h0 : (a ∘ₗ φ) m = (a ∘ₗ φ) 0 := by
      rw [LinearMap.comp_apply, LinearMap.mem_ker.1 hm, map_zero, map_zero]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0
    refine ⟨k, ?_⟩
    simpa [Submonoid.smul_def] using hk
  · intro n
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (LinearMap.range φ) _ hf n ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨Q, _, _, a, h1, h2⟩ := h i
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hk⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (a ∘ₗ φ) (a n)
    have h0 : a (f i ^ k • n) = a (φ m) := by
      rw [map_smul]
      exact hk
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0
    refine ⟨l + k, f i ^ l • m, ?_⟩
    have hl' : f i ^ l • f i ^ k • n = f i ^ l • φ m := hl
    show φ (f i ^ l • m) = f i ^ (l + k) • n
    rw [map_smul, pow_add, mul_smul, hl']

theorem isBaseChange_hom {R A C P : Type} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    [Algebra A C] [IsScalarTower R A C] [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    [Module.Finite A P] [Module.Projective A P]
    (hA : ∀ (φ : P →ₗ[R] A) (a : A) p, φ (a • p) = a * φ p)
    (hC : ∀ (φ : P →ₗ[R] C) (a : A) p, φ (a • p) = algebraMap A C a * φ p)
    (g : (P →ₗ[R] A) →ₗ[A] (P →ₗ[R] C)) (hg : ∀ φ p, g φ p = algebraMap A C (φ p)) : IsBaseChange C g := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let b : Fin n → P := fun k => π (fun j => if k = j then 1 else 0)
  have hexp : ∀ p : P, ∑ k, s p k • b k = p := by
    intro p
    have h1 := LinearMap.congr_fun hs p
    have h2 := LinearMap.pi_apply_eq_sum_univ π (s p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [h1] at h2
    exact h2.symm
  let co : Fin n → (P →ₗ[R] A) := fun k => (LinearMap.proj k ∘ₗ s).restrictScalars R
  have hco : ∀ k p, co k p = s p k := fun _ _ => rfl
  have hsum : ∀ φ : P →ₗ[R] A, ∑ k, φ (b k) • co k = φ := by
    intro φ
    ext p
    conv_rhs => rw [← hexp p]

    simp [map_sum, hA, hco, mul_comm]
  let θ : C ⊗[A] (P →ₗ[R] A) →ₗ[C] (P →ₗ[R] C) := g.liftBaseChange C
  have hθ : ∀ c φ, θ (c ⊗ₜ φ) = c • g φ := fun c φ => LinearMap.liftBaseChange_tmul _ _ _ _
  let inv : (P →ₗ[R] C) → C ⊗[A] (P →ₗ[R] A) := fun ψ => ∑ k, ψ (b k) ⊗ₜ co k
  have hl : ∀ z, inv (θ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [inv]
    | add x y hx hy =>
      have : inv (θ (x + y)) = inv (θ x) + inv (θ y) := by
        simp [inv, add_tmul, Finset.sum_add_distrib]
      rw [this, hx, hy]
    | tmul c φ =>
      rw [hθ]
      conv_rhs => rw [← hsum φ, tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.smul_apply, hg, tmul_smul, smul_tmul', Algebra.smul_def (φ (b k)), smul_eq_mul, mul_comm]
  have hr : ∀ ψ, θ (inv ψ) = ψ := by
    intro ψ
    ext p
    conv_rhs => rw [← hexp p]

    simp only [inv, map_sum, hθ, LinearMap.sum_apply, LinearMap.smul_apply, hg, hco, hC, smul_eq_mul, mul_comm]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective θ
    ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩) fun φ => ?_
  exact (hθ 1 φ).trans (one_smul _ _)

end PositivityTheory.HtPt.Htat.Lie
end
end

section

namespace PositivityTheory.HtPt.Siua

open Filter Topology

theorem expand {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℤ) :
    f (fun i => x i • μ + y i • e) =
      ∑ s : Finset (Fin n), (∏ i, if i ∈ s then x i else y i) * f (fun i => if i ∈ s then μ else e) := by
  have hsum := f.map_add_univ (fun i => x i • μ) (fun i => y i • e)
  rw [show (fun i => x i • μ + y i • e) = (fun i => x i • μ) + (fun i => y i • e) from rfl, hsum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : s.piecewise (fun i => x i • μ) (fun i => y i • e) =
      fun i => (if i ∈ s then x i else y i) • (if i ∈ s then μ else e) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  simp only [hpw, f.map_smul_univ, RingHom.id_apply, smul_eq_mul]

noncomputable def form {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ)
    (μ e : M) (x y : Fin n → ℚ) : ℚ :=
  ∑ s : Finset (Fin n), (∏ i, if i ∈ s then x i else y i) * (f (fun i => if i ∈ s then μ else e) : ℚ)

theorem form_cast {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℤ) :
    (f (fun i => x i • μ + y i • e) : ℚ) = form f μ e (fun i => x i) (fun i => y i) := by
  rw [PositivityTheory.HtPt.Siua.expand]
  simp only [PositivityTheory.HtPt.Siua.form]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1

theorem form_smul {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℚ) (a : ℚ) :
    form f μ e (fun i => a * x i) (fun i => a * y i) = a ^ n * form f μ e x y := by
  simp only [PositivityTheory.HtPt.Siua.form, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hprod : ∏ i, (if i ∈ s then a * x i else a * y i) = a ^ n * ∏ i, (if i ∈ s then x i else y i) := by
    calc ∏ i, (if i ∈ s then a * x i else a * y i)
        = ∏ i, a * (if i ∈ s then x i else y i) :=
          Finset.prod_congr rfl fun i _ => (mul_ite _ _ _ _).symm
      _ = (∏ _i : Fin n, a) * ∏ i, (if i ∈ s then x i else y i) := Finset.prod_mul_distrib
      _ = a ^ n * ∏ i, (if i ∈ s then x i else y i) := by simp
  rw [hprod, mul_assoc]

theorem form_cont {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ) (μ e : M)
    (x : Fin n → ℚ) (y : Fin n → ℚ) : Continuous fun t : ℚ => form f μ e x (fun i => y i * t) := by
  simp only [PositivityTheory.HtPt.Siua.form]
  refine continuous_finsetSum _ fun s _ => ?_
  refine Continuous.mul (continuous_finsetProd _ fun i _ => ?_) continuous_const
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    exact continuous_const
  · simp only [hi, ↓reduceIte]
    exact continuous_const.mul continuous_id

theorem siu_num : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e) := by
  intro M _ d f μ e hf
  obtain ⟨x2, hx2⟩ : ∃ x2 : Fin (d + 1) → ℚ, x2 = Fin.snoc (α := fun _ => ℚ) (fun _ : Fin d => (1 : ℚ)) 0 :=
    ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ y2 : Fin (d + 1) → ℚ, y2 = Fin.snoc (α := fun _ => ℚ) (fun _ : Fin d => (1 : ℚ)) 2 :=
    ⟨_, rfl⟩
  have hc1 : Continuous fun t : ℚ =>
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) :=
    PositivityTheory.HtPt.Siua.form_cont f μ e _ (fun _ => 1)
  have hc2 : Continuous fun t : ℚ => PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) :=
    PositivityTheory.HtPt.Siua.form_cont f μ e x2 y2
  have hc : Continuous fun t : ℚ =>
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) -
        ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) :=
    hc1.sub (continuous_const.mul hc2)
  have h10 : PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * 0) = (f (fun _ => μ) : ℚ) := by
    have h := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => 1) (fun _ => 0)
    simp only [one_smul, zero_smul, add_zero, Int.cast_one, Int.cast_zero] at h
    simp only [mul_zero]
    exact h.symm
  have h20 : PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * 0) = 0 := by
    simp only [PositivityTheory.HtPt.Siua.form, mul_zero]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [Finset.prod_eq_zero (f := fun i => if i ∈ s then x2 i else 0) (Finset.mem_univ (Fin.last d))
      (by simp [hx2]), zero_mul]
  have hG0 : (0 : ℚ) < PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * 0) -
      ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * 0) := by
    rw [h10, h20]
    simpa using hf
  have hev := (hc.tendsto 0).eventually (lt_mem_nhds hG0)
  obtain ⟨t, hGt, ht⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℚ) ∈ 𝓝[>] 0)).exists
  have hGt' : (0 : ℚ) < PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) -
      ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) := hGt
  refine ⟨t, ht, ?_⟩
  intro a m ha hm
  have hR : (f (fun _ => a • μ + m • e) : ℚ) =
      (a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) := by
    have h := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => (a : ℤ)) (fun _ => m)
    rw [← PositivityTheory.HtPt.Siua.form_smul]
    simp only [natCast_zsmul] at h
    rw [h]
    congr 1
    · funext i
      simp
    · funext i
      simp [hm]
  have hfun : (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) =
      fun i => (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => (a : ℤ)) 0 i) • μ +
        (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => m) (2 * m) i) • e := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [natCast_zsmul]
  have hL : (f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) : ℚ) =
      (a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) := by
    have h := PositivityTheory.HtPt.Siua.form_cast f μ e
      (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => (a : ℤ)) 0)
      (Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => m) (2 * m))
    rw [← PositivityTheory.HtPt.Siua.form_smul, hfun, h]
    congr 1
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [hx2]
      · simp [hx2]
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hy2]
        simp only [Fin.snoc_last, Int.cast_mul, Int.cast_ofNat, hm]
        ring
      · simp [hy2, hm]
  have hpos : (0 : ℚ) < (a : ℚ) ^ (d + 1) := pow_pos (by exact_mod_cast (show 0 < a by omega)) _
  have hlt : ((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t) <
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) := by
    linarith
  rw [← Int.cast_lt (R := ℚ), Int.cast_mul, hL, hR]
  calc (((d + 1 : ℕ) : ℤ) : ℚ) * ((a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t))
      = (a : ℚ) ^ (d + 1) * (((d : ℚ) + 1) * PositivityTheory.HtPt.Siua.form f μ e x2 (fun i => y2 i * t)) := by
        push_cast
        ring
    _ < (a : ℚ) ^ (d + 1) * PositivityTheory.HtPt.Siua.form f μ e (fun _ => (1 : ℚ)) (fun _ => 1 * t) :=
        mul_lt_mul_of_pos_left hlt hpos

end PositivityTheory.HtPt.Siua
end
