module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

section
end

section

namespace GlobalTheory.CompanionTheory.HermitianForm

theorem re_pairing_eq_zero_of_psd {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hpos : ∀ v, 0 ≤ (B v v).re) (v : V) (hv : B v v = 0) (u : V) : (B v u).re = 0 := by
  have hb : 0 ≤ (B u u).re := hpos u
  have key : ∀ t : ℝ, 0 ≤ 2 * t * (B v u).re + t ^ 2 * (B u u).re := by
    intro t
    have h := hpos (v + (t : ℂ) • u)
    have e : B (v + (t : ℂ) • u) (v + (t : ℂ) • u)
        = B v v + (t : ℂ) * B v u + (t : ℂ) * B u v + (t : ℂ) * (t : ℂ) * B u u := by
      simp only [map_add (f := _), LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Complex.conj_ofReal]
      ring
    rw [e, hv, hB v u] at h
    simp only [zero_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.mul_im, zero_mul, sub_zero, add_zero] at h
    nlinarith [h]
  set a := (B v u).re with ha
  set b := (B u u).re with hb'
  have hb1 : 0 < b + 1 := by linarith
  have h := key (-a / (b + 1))
  have e2 : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b
      = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    field_simp
    ring
  rw [e2] at h
  have h3 : 0 ≤ -(a ^ 2 * (b + 2)) := by
    by_contra hc
    push Not at hc
    have : -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 < 0 := div_neg_of_neg_of_pos hc (by positivity)
    linarith
  have h4 : a ^ 2 * (b + 2) ≤ 0 := by linarith
  have h5 : a ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < a ^ 2 * (b + 2) := mul_pos hc (by linarith)
    linarith
  have h6 : a ^ 2 = 0 := le_antisymm h5 (sq_nonneg a)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h6

theorem pairing_eq_zero_of_psd : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) →
    (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  intro V _ _ B hB hpos v hv w
  have hre := re_pairing_eq_zero_of_psd B hB hpos v hv w
  have him := re_pairing_eq_zero_of_psd B hB hpos v hv (Complex.I • w)
  have e : B v (Complex.I • w) = -Complex.I * B v w := by
    simp only [map_smulₛₗ, smul_eq_mul, Complex.conj_I]
  rw [e] at him
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at him
  apply Complex.ext
  · simpa using hre
  · simpa using him

end GlobalTheory.CompanionTheory.HermitianForm
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Herm

theorem apply_eq_zero_of_isotropic {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hs : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hp : ∀ v, 0 ≤ (B v v).re) (x : V) (hx : (B x x).re = 0) (w : V) : B x w = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = B x w := ⟨_, rfl⟩
  have hwx : B w x = starRingEnd ℂ c := by rw [hc]; exact hs x w
  have key : ∀ t : ℝ, 0 ≤ -2 * t * Complex.normSq c
      + t ^ 2 * Complex.normSq c * (B w w).re := by
    intro t
    have h := hp (x - ((t : ℂ) * c) • w)
    have e : B (x - ((t : ℂ) * c) • w) (x - ((t : ℂ) * c) • w)
        = B x x - starRingEnd ℂ ((t : ℂ) * c) * c - ((t : ℂ) * c) * starRingEnd ℂ c
          + ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c) * B w w := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.map_smulₛₗ, smul_eq_mul, ← hc, hwx]
      ring
    have e1 : starRingEnd ℂ ((t : ℂ) * c) * c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, mul_comm (starRingEnd ℂ c) c,
        Complex.mul_conj]
      push_cast; ring
    have e2 : ((t : ℂ) * c) * starRingEnd ℂ c = ((t * Complex.normSq c : ℝ) : ℂ) := by
      rw [mul_assoc, Complex.mul_conj]
      push_cast; ring
    have e3 : ((t : ℂ) * c) * starRingEnd ℂ ((t : ℂ) * c)
        = ((t ^ 2 * Complex.normSq c : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_mul, Complex.normSq_ofReal]
      push_cast; ring
    rw [e, e1, e2, e3] at h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, hx] at h
    linarith
  by_contra hne
  have hc0 : c ≠ 0 := by rw [hc]; exact hne
  have hN : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc0
  have hr : 0 ≤ (B w w).re := hp w
  obtain ⟨r, hrdef⟩ : ∃ r, r = (B w w).re := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have hk := key (1 / (r + 1))
  rw [← hrdef] at hk
  have hr1 : 0 < r + 1 := by linarith
  have hid : -2 * (1 / (r + 1)) * Complex.normSq c
      + (1 / (r + 1)) ^ 2 * Complex.normSq c * r
      = -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 := by
    field_simp
    ring
  rw [hid] at hk
  have : -(Complex.normSq c * (r + 2)) / (r + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  linarith

end GlobalTheory.CompanionTheory.Herm
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Sesquilinear

theorem eq_zero_of_diag_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (h : ∀ v, B v v = 0) : B = 0 := by
  ext v w
  have h1 := h (v + w)
  have h2 := h (v + Complex.I • w)
  simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    h v, h w, smul_eq_mul, zero_add, add_zero, Complex.conj_I, RingHom.id_apply,
    mul_zero] at h1 h2
  have h3 : B v w = B w v := by
    have : Complex.I * (B w v - B v w) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h4 | h4
    · exact absurd h4 Complex.I_ne_zero
    · exact (sub_eq_zero.mp h4).symm
  have h5 : (2 : ℂ) * B v w = 0 := by linear_combination h1 + h3
  simpa using h5

end GlobalTheory.CompanionTheory.Sesquilinear
end

section

namespace GlobalTheory.CompanionTheory.FiniteDuality

private theorem card_dual_zmod_le_card' (n : ℕ) [NeZero n] (M : Type) [AddCommGroup M]
    [Module (ZMod n) M] [Finite M] :
    Nat.card (M →ₗ[ZMod n] ZMod n) ≤ Nat.card M := by
  classical
  have := Fintype.ofFinite M
  let φ : (M →ₗ[ZMod n] ZMod n) → AddChar M ℂ := fun f =>
    Circle.coeHom.compAddChar ((ZMod.toCircle (N := n)).compAddMonoidHom f.toAddMonoidHom)
  have hφ : Function.Injective φ := by
    intro f g h
    ext x
    have hx := congrArg (fun ψ : AddChar M ℂ => ψ x) h
    have hx' : Circle.coeHom (ZMod.toCircle (f x)) = Circle.coeHom (ZMod.toCircle (g x)) := hx
    exact ZMod.injective_toCircle (Circle.ext hx')
  calc Nat.card (M →ₗ[ZMod n] ZMod n) ≤ Nat.card (AddChar M ℂ) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card M := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

private theorem card_le_of_injective_pairing_zmod (n : ℕ) [NeZero n] (Z W : Type) [AddCommGroup Z]
    [Module (ZMod n) Z] [AddCommGroup W] [Module (ZMod n) W] [Finite W]
    (g : Z →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n) (hg : Function.Injective g) :
    Nat.card Z ≤ Nat.card W := by
  have : Finite (W →ₗ[ZMod n] ZMod n) :=
    Finite.of_injective (fun f : W →ₗ[ZMod n] ZMod n => (f : W → ZMod n)) DFunLike.coe_injective
  exact (Nat.card_le_card_of_injective g hg).trans (card_dual_zmod_le_card' n W)

theorem double_annihilator (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X]
    [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (U : Submodule (ZMod n) X) :
    (⨅ y ∈ (⨅ x ∈ U, LinearMap.ker (B.flip x)), LinearMap.ker (B y)) = U := by
  set A : Submodule (ZMod n) Y := ⨅ x ∈ U, LinearMap.ker (B.flip x) with hAdef
  set W : Submodule (ZMod n) X := ⨅ y ∈ A, LinearMap.ker (B y) with hWdef
  have memA : ∀ y, y ∈ A ↔ ∀ x ∈ U, B y x = 0 := by
    intro y
    simp [hAdef, Submodule.mem_iInf]
  have memW : ∀ x, x ∈ W ↔ ∀ y ∈ A, B y x = 0 := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker]
  have hUW : U ≤ W := by
    intro x hx
    rw [memW]
    intro y hy
    exact (memA y).1 hy x hx
  let f1 : Y →ₗ[ZMod n] U →ₗ[ZMod n] ZMod n := B.compl₂ U.subtype
  have hA1 : A ≤ LinearMap.ker f1 := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext u
    simp [f1, (memA y).1 hy u u.2]
  have hA1' : LinearMap.ker f1 ≤ A := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [memA]
    intro x hx
    have := LinearMap.congr_fun hy ⟨x, hx⟩
    simpa [f1] using this
  let P1 : (Y ⧸ A) →ₗ[ZMod n] U →ₗ[ZMod n] ZMod n := A.liftQ f1 hA1
  have hP1 : Function.Injective P1 :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot A f1 hA1 hA1')
  let f2 : Y →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n := B.compl₂ W.subtype
  have hA2 : A ≤ LinearMap.ker f2 := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext w
    simp [f2, (memW w).1 w.2 y hy]
  let P2 : (Y ⧸ A) →ₗ[ZMod n] W →ₗ[ZMod n] ZMod n := A.liftQ f2 hA2
  have hP2 : Function.Injective P2.flip := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    have hz : B.flip (w : X) = 0 := by
      ext y
      have := LinearMap.congr_fun hw (Submodule.Quotient.mk y)
      simpa [P2, f2] using this
    have : (w : X) = 0 := hB' (by rw [hz, map_zero])
    exact Subtype.ext this
  have : Finite (Y ⧸ A) := Finite.of_surjective _ (Submodule.mkQ_surjective A)
  have c1 : Nat.card (Y ⧸ A) ≤ Nat.card U := card_le_of_injective_pairing_zmod n _ _ P1 hP1
  have c2 : Nat.card W ≤ Nat.card (Y ⧸ A) := card_le_of_injective_pairing_zmod n _ _ P2.flip hP2
  have hle : Nat.card (W.toAddSubgroup) ≤ Nat.card (U.toAddSubgroup) := c2.trans c1
  exact (Submodule.toAddSubgroup_injective
    (AddSubgroup.eq_of_le_of_card_ge (show U.toAddSubgroup ≤ W.toAddSubgroup from hUW) hle)).symm

end GlobalTheory.CompanionTheory.FiniteDuality
end

section

namespace GlobalTheory.CompanionTheory.Pairing

theorem sum_perfect_apply {R : Type} [CommRing R] {ι : Type} [Fintype ι] {X Y : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] [∀ i, AddCommGroup (Y i)]
    [∀ i, Module R (Y i)] (B : ∀ i, Y i →ₗ[R] X i →ₗ[R] R)
    (y : ∀ i, Y i) (x : ∀ i, X i) :
    (∑ i, (B i).compl₁₂ (LinearMap.proj i : (∀ i, Y i) →ₗ[R] Y i)
      (LinearMap.proj i : (∀ i, X i) →ₗ[R] X i)) y x = ∑ i, B i (y i) (x i) := by
  simp [LinearMap.sum_apply]

theorem sum_perfect : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] (X Y : ι → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)] (B : ∀ i, Y i →ₗ[R] X i →ₗ[R] R), (∀ i, Function.Injective (B i)) → (∀ i, Function.Injective (B i).flip) → Function.Injective (∑ i, (B i).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)) ∧ Function.Injective (∑ i, (B i).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)).flip := by
  intro R _ ι _ X Y _ _ _ _ B hB hBf
  classical
  constructor
  · rw [← LinearMap.coe_sum, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    funext j
    have hj : B j (y j) = 0 := by
      ext x₀
      have h := LinearMap.congr_fun hy (Pi.single j x₀)
      rw [sum_perfect_apply, Fintype.sum_eq_single j (fun i hi => by rw [Pi.single_eq_of_ne hi, map_zero]),
        Pi.single_eq_same] at h
      simpa using h
    exact hB j (hj.trans (map_zero _).symm)
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    funext j
    have hj : (B j).flip (x j) = 0 := by
      ext y₀
      have h := LinearMap.congr_fun hx (Pi.single j y₀)
      rw [LinearMap.flip_apply, sum_perfect_apply, Fintype.sum_eq_single j (fun i hi => by
        rw [Pi.single_eq_of_ne hi, map_zero, LinearMap.zero_apply]), Pi.single_eq_same] at h
      simpa using h
    exact hBf j (hj.trans (map_zero _).symm)

end GlobalTheory.CompanionTheory.Pairing
end

section

open Polynomial

namespace GlobalTheory.CompanionTheory.KillSum

theorem prod_map_add_eq {R α : Type*} [CommRing R] (P : Multiset α) (f : α → R) (w : R) :
    ∃ q, (P.map fun a => f a + w).prod = (P.map f).prod + w * q := by
  induction P using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a s ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(s.map f).prod + f a * q + w * q, ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, hq]
    ring

theorem add_killed {R : Type*} [CommRing R] [Algebra ℂ R] (x y : R) (P Q : Multiset ℂ)
    (hP : (P.map fun c => x - algebraMap ℂ R c).prod = 0)
    (hQ : (Q.map fun c => y - algebraMap ℂ R c).prod = 0) :
    ((Q.bind fun b => P.map fun a => a + b).map fun c => (x + y) - algebraMap ℂ R c).prod = 0 := by
  have key : ∀ b : ℂ, ∃ q, (P.map fun a => (x + y) - algebraMap ℂ R (a + b)).prod
      = (y - algebraMap ℂ R b) * q := by
    intro b
    obtain ⟨q, hq⟩ := prod_map_add_eq P (fun c => x - algebraMap ℂ R c) (y - algebraMap ℂ R b)
    refine ⟨q, ?_⟩
    rw [hP, zero_add] at hq
    rw [← hq]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp only [map_add (f := _)]
    ring
  choose q hq using key
  rw [Multiset.map_bind, Multiset.prod_bind]
  simp only [Multiset.map_map, Function.comp_def]
  simp only [hq]
  rw [Multiset.prod_map_mul, hQ, zero_mul]

theorem sum_killed {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ) :
    ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨{0}, by simp, fun R _ _ h _ => by simp⟩
  | insert τ s hτ ih =>
    obtain ⟨l0, hc, hk⟩ := ih
    refine ⟨l0.bind fun b => (l τ).map fun a => a + b, ?_, ?_⟩
    · rw [Finset.prod_insert hτ, ← hc]
      simp [Multiset.card_bind, mul_comm]
    · intro R _ _ h hh
      rw [Finset.sum_insert hτ]
      exact add_killed _ _ _ _ (hh τ (Finset.mem_insert_self _ _))
        (hk R h fun t ht => hh t (Finset.mem_insert_of_mem ht))

end GlobalTheory.CompanionTheory.KillSum
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Transversal

theorem sum_add_eq_sum_of_transversal : ∀ {X : Type} [AddCommGroup X] {M : Type} [AddCommMonoid M] {A H : AddSubgroup X}, H ≤ A → ∀ {T : Finset X}, (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) → ∀ (F : X → M), (∀ a, ∀ h ∈ H, F (a + h) = F a) → ∀ {a : X}, a ∈ A → ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  intro X _ M _ A H hHA T hTA huniq F hF a ha
  classical
  have hex : ∀ t ∈ T, ∃ t', t' ∈ T ∧ (t + a) - t' ∈ H := fun t ht =>
    (huniq (t + a) (A.add_mem (hTA t ht) ha)).exists
  choose! g hgT hgH using hex
  have uniq : ∀ x ∈ A, ∀ t₁ t₂, t₁ ∈ T → x - t₁ ∈ H → t₂ ∈ T → x - t₂ ∈ H → t₁ = t₂ :=
    fun x hx t₁ t₂ h1 h1' h2 h2' => (huniq x hx).unique ⟨h1, h1'⟩ ⟨h2, h2'⟩
  refine Finset.sum_bij (fun t _ => g t) (fun t ht => hgT t ht) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ heq
    have hd : t₁ - t₂ ∈ H := by
      have h3 := H.sub_mem (hgH t₁ h₁) (hgH t₂ h₂)
      have e : t₁ + a - g t₁ - (t₂ + a - g t₂) = t₁ - t₂ := by rw [heq]; abel
      rwa [e] at h3
    exact uniq t₁ (hTA t₁ h₁) t₁ t₂ h₁ (by rw [sub_self]; exact H.zero_mem) h₂ hd
  · intro t' ht'
    obtain ⟨t, ⟨htT, htH⟩, -⟩ := huniq (t' - a) (A.sub_mem (hTA t' ht') ha)
    refine ⟨t, htT, ?_⟩
    have h1 : t + a - t' ∈ H := by
      have h3 := H.neg_mem htH
      have e : -(t' - a - t) = t + a - t' := by abel
      rwa [e] at h3
    exact uniq (t + a) (A.add_mem (hTA t htT) ha) (g t) t' (hgT t htT) (hgH t htT) ht' h1
  · intro t ht
    have h3 := hF (g t) _ (hgH t ht)
    have e : g t + (t + a - g t) = t + a := by abel
    rw [e] at h3
    exact h3

end GlobalTheory.CompanionTheory.Transversal
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

variable {n : ℕ}

def mon (e : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := ∏ a, z a ^ e a

def dl (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def prs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

def score (T : Finset (Fin n × Fin n)) : Fin n → ℤ := fun c =>
  ((T.filter fun p => p.1 = c).card : ℤ) + (((prs n \ T).filter fun p => p.2 = c).card : ℤ)

def tZero (lev : Fin n → ℕ) : Finset (Fin n × Fin n) := (prs n).filter fun p => lev p.1 < lev p.2

end GlobalTheory.CompanionTheory.CoefId
end
end

section

namespace GlobalTheory.CompanionTheory.Inequalities

theorem weighted_antitone_last_nonpos : ∀ (h : ℕ) (d e : Fin h → ℝ), 2 ≤ h → (∀ i, 0 < d i) →
    Antitone e → ∑ i, d i * e i = 0 →
    ∃ j : Fin h, 0 < j.val ∧ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i ≤ 0 := by
  intro h d e hh hd he hs
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
  refine ⟨Fin.last (n + 1), by simp, ?_⟩
  have hf : Finset.univ.filter (fun i : Fin (n + 2) => Fin.last (n + 1) ≤ i)
      = {Fin.last (n + 1)} := by
    ext i
    simp [Fin.last_le_iff]
  rw [hf, Finset.sum_singleton]
  have hle : (∑ i, d i) * e (Fin.last (n + 1)) ≤ 0 := by
    rw [Finset.sum_mul, ← hs]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (he (Fin.le_last i)) (hd i).le
  have hpos : 0 < ∑ i, d i :=
    Finset.sum_pos (fun i _ => hd i) ⟨Fin.last _, Finset.mem_univ _⟩
  have hel : e (Fin.last (n + 1)) ≤ 0 := by
    by_contra hc
    exact absurd (mul_pos hpos (not_le.mp hc)) (not_lt.mpr hle)
  exact mul_nonpos_of_nonneg_of_nonpos (hd _).le hel

end GlobalTheory.CompanionTheory.Inequalities
end
