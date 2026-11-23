module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle023
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootFFiniteGaloisIsPGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle103
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle105
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle085
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004

@[expose] public section

section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.LevGroup

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

theorem isUp_one : IsUp g N 1 :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩

theorem isUp_mul {u v : GG g N} (hu : IsUp g N u) (hv : IsUp g N v) : IsUp g N (u * v) := by
  refine ⟨fun a => ?_, fun a c h => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hu.1, hv.1, mul_one]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hu.2 a b h, zero_mul]
      · rw [hv.2 b a h, mul_zero]
    · simp
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b a with h' | h'
    · rw [hu.2 a b h', zero_mul]
    · rw [hv.2 b c (lt_of_lt_of_le h h'), mul_zero]

theorem mul_entry {u v : GG g N} (hu : IsUp g N u) (hv : IsUp g N v) {a c : Fin N} (hac : a < c)
    (h : ∀ b, a < b → b < c → u.val a b * v.val b c = 0) : (u * v).val a c = u.val a c + v.val a c := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a c (Finset.mem_univ _) (Finset.mem_univ _) hac.ne]
  · rw [hu.1, hv.1, one_mul, mul_one, add_comm]
  · rintro b _ ⟨h1, h2⟩
    rcases lt_or_gt_of_ne h1 with h1 | h1
    · rw [hu.2 a b h1, zero_mul]
    rcases lt_or_gt_of_ne h2 with h2 | h2
    · exact h b h1 h2
    · rw [hv.2 b c h2, mul_zero]

theorem isNilpotent_of_isUp {u : GG g N} (hu : IsUp g N u) : IsNilpotent (u.val - 1) := by
  have ht : (u.val - 1).BlockTriangular id := by
    intro a b h
    have h' : b < a := h
    simp [Matrix.sub_apply, hu.2 a b h', Matrix.one_apply_ne h'.ne']
  have hc := Matrix.aeval_self_charpoly (u.val - 1)
  rw [Matrix.charpoly_of_upperTriangular _ ht] at hc
  refine ⟨N, ?_⟩
  simpa [Matrix.sub_apply, hu.1] using hc

theorem edge_lt (L : Lev g N) {a b : Fin N} (h : L.Edge a b) : a < b := by
  unfold Lev.Edge at h
  rw [Fin.lt_def]
  split_ifs at h <;> omega

theorem mem_one (L : Lev g N) : L.Mem 1 := by
  refine ⟨isUp_one, fun _ a b _ h2 h3 => ?_⟩
  have : a ≠ b := fun h => by subst h; omega
  simp [Matrix.one_apply_ne this]

theorem mem_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) : L.Mem (u * v) := by
  refine ⟨isUp_mul hu.1 hv.1, fun hs a c h1 h2 h3 => ?_⟩
  rw [mul_entry hu.1 hv.1 (by rw [Fin.lt_def]; omega), hu.2 hs a c h1 h2 h3, hv.2 hs a c h1 h2 h3, add_zero]
  intro b hb hc
  rw [Fin.lt_def] at hb hc
  rw [hv.2 hs b c (by omega) (by omega) h3, mul_zero]

theorem edge_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) {a c : Fin N} (h : L.Edge a c) :
    (u * v).val a c = u.val a c + v.val a c := by
  refine mul_entry hu.1 hv.1 (edge_lt L h) fun b hb hc => ?_
  rw [Fin.lt_def] at hb hc
  unfold Lev.Edge at h
  split_ifs at h with hs
  · rcases h with h | h
    · omega
    · rw [hv.2 hs b c (by omega) (by omega) h.2, mul_zero]
  · omega

theorem chi_one (L : Lev g N) : L.chi 1 = 1 := by
  unfold Lev.chi
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one]
  refine fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · simp [Matrix.one_apply_ne (edge_lt L h).ne]
  · rfl

theorem chi_mul (L : Lev g N) {u v : GG g N} (hu : L.Mem u) (hv : L.Mem v) : L.chi (u * v) = L.chi u * L.chi v := by
  unfold Lev.chi
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [edge_mul L hu hv h, mul_add]
  · simp

theorem lev_group : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N, L.Mem 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.Mem (u * v)) ∧ L.chi 1 = 1 ∧ (∀ u v, L.Mem u → L.Mem v → L.chi (u * v) = L.chi u * L.chi v) ∧ ∀ u, L.Mem u → IsNilpotent (u.val - 1) :=
  fun _ _ _ L => ⟨mem_one L, fun _ _ => mem_mul L, chi_one L, fun _ _ => chi_mul L, fun _ hu => isNilpotent_of_isUp hu.1⟩

end GlobalTheory.BadShare.LevGroup
end

section

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

section
variable {G : Type} [Group G] [Fintype G]

theorem convCalc_assoc (a b c : G → ℂ) : conv (conv a b) c = conv a (conv b c) := by
  funext x
  simp only [conv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft z)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_assoc]

theorem convCalc_sub_left (a b c : G → ℂ) : conv (a - b) c = conv a c - conv b c := by
  funext x
  simp [conv, sub_mul, Finset.sum_sub_distrib]

theorem convCalc_sub_right (a b c : G → ℂ) : conv c (a - b) = conv c a - conv c b := by
  funext x
  simp [conv, mul_sub, Finset.sum_sub_distrib]

theorem convCalc_dirac_left (a : G → ℂ) : conv dirac a = a := by
  funext x
  simp [conv, dirac]

theorem convCalc_dirac_right (a : G → ℂ) : conv a dirac = a := by
  funext x
  simp [conv, dirac, inv_mul_eq_one]

theorem convCalc_star (a b : G → ℂ) (ha : ∀ x, a x⁻¹ = (starRingEnd ℂ) (a x))
    (hb : ∀ x, b x⁻¹ = (starRingEnd ℂ) (b x)) (x : G) :
    conv a b x⁻¹ = (starRingEnd ℂ) (conv b a x) := by

  simp only [conv, map_sum, map_mul, ← ha, ← hb]
  rw [← Equiv.sum_comp (Equiv.mulLeft x⁻¹)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_comm, mul_assoc]

theorem convCalc_isProj_conv (a b : G → ℂ) (ha : IsProj a) (hb : IsProj b) (h : conv a b = conv b a) :
    IsProj (conv a b) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [convCalc_assoc, ← convCalc_assoc b a b, ← h, convCalc_assoc a b b, hb.1, ← convCalc_assoc, ha.1]
  · rw [convCalc_star a b ha.2 hb.2, h]

theorem convCalc_isProj_compl (a : G → ℂ) (ha : IsProj a) : IsProj (dirac - a) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [convCalc_sub_left, convCalc_sub_right, convCalc_sub_right, convCalc_dirac_left, convCalc_dirac_left,
      convCalc_dirac_right, ha.1]
    simp
  · simp only [Pi.sub_apply, map_sub, ha.2, dirac, inv_eq_one]
    split_ifs <;> simp

variable {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)

theorem convCalc_op_conv (a b : G → ℂ) : op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op, conv, Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [smul_smul, mul_comm]

theorem convCalc_op_sub (a b : G → ℂ) : op ρ (a - b) = op ρ a - op ρ b := by
  simp [op, sub_smul, Finset.sum_sub_distrib]

theorem convCalc_op_add (a b : G → ℂ) : op ρ (a + b) = op ρ a + op ρ b := by
  simp [op, add_smul, Finset.sum_add_distrib]

theorem convCalc_op_dirac : op ρ dirac = 1 := by
  simp [op, dirac]

theorem convCalc_rk [FiniteDimensional ℂ M] (e : G → ℂ) (he : conv e e = e) :
    (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  have h1 : op ρ e * op ρ e = op ρ e := by rw [← convCalc_op_conv, he]
  have hp : LinearMap.IsProj (LinearMap.range (op ρ e)) (op ρ e) :=
    ⟨fun x => LinearMap.mem_range_self _ x, by
      rintro x ⟨y, rfl⟩
      exact LinearMap.congr_fun h1 y⟩
  rw [rk, ← hp.trace]

  simp [op, map_sum]

end

theorem convCalc : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), (∀ a b : G → ℂ, op ρ (conv a b) = op ρ a * op ρ b ∧ op ρ (a - b) = op ρ a - op ρ b ∧ op ρ (a + b) = op ρ a + op ρ b) ∧ op ρ dirac = 1 ∧ (∀ a b c : G → ℂ, conv (conv a b) c = conv a (conv b c) ∧ conv (a - b) c = conv a c - conv b c ∧ conv c (a - b) = conv c a - conv c b) ∧ (∀ a : G → ℂ, conv dirac a = a ∧ conv a dirac = a) ∧ (∀ a b : G → ℂ, IsProj a → IsProj b → conv a b = conv b a → IsProj (conv a b)) ∧ (∀ a : G → ℂ, IsProj a → IsProj (dirac - a)) ∧ ∀ e : G → ℂ, conv e e = e → (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  intro G _ _ M _ _ _ ρ
  exact ⟨fun a b => ⟨convCalc_op_conv ρ a b, convCalc_op_sub ρ a b, convCalc_op_add ρ a b⟩, convCalc_op_dirac ρ,
    fun a b c => ⟨convCalc_assoc a b c, convCalc_sub_left a b c, convCalc_sub_right a b c⟩,
    fun a => ⟨convCalc_dirac_left a, convCalc_dirac_right a⟩, convCalc_isProj_conv, convCalc_isProj_compl,
    convCalc_rk ρ⟩

end GlobalTheory.BadShare
end
end

section

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

def levMat {g N : ℕ} (S : Finset (Fin N × Fin N)) (f : S → ZMod g) : Matrix (Fin N) (Fin N) (ZMod g) :=
  fun a b => if h : (a, b) ∈ S then f ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem levMat_det {g N : ℕ} (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) (f : S → ZMod g) :
    (levMat S f).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro a _
    have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
    simp [levMat, this]
  · intro a b hab
    have hab' : b < a := hab
    have : (a, b) ∉ S := fun h => lt_asymm hab' (hS _ h)
    simp [levMat, this, hab'.ne']

theorem card_up_supp (g : ℕ) [Fact g.Prime] (N : ℕ) (S : Finset (Fin N × Fin N)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} = g ^ S.card := by
  have e : {u : GG g N // (∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ S → u.val a b = 0} ≃ (S → ZMod g) :=
    { toFun := fun u p => u.1.val p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (levMat S f) (by rw [levMat_det S hS]; exact one_ne_zero), by
        refine ⟨fun a => ?_, fun a b hab h => ?_⟩
        · have : (a, a) ∉ S := fun h => lt_irrefl _ (hS _ h)
          show levMat S f a a = 1
          simp [levMat, this]
        · show levMat S f a b = 0
          simp [levMat, h, hab]⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        ext a b
        show levMat S (fun p => u.1.val p.1.1 p.1.2) a b = u.1.val a b
        unfold levMat
        split_ifs with h1 h2
        · rfl
        · subst h2; exact (u.2.1 a).symm
        · exact (u.2.2 a b h2 h1).symm
      right_inv := fun f => by
        funext p
        show levMat S f p.1.1 p.1.2 = f p
        simp [levMat, p.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod]
  simp

theorem lev_card : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ L : Lev g N,
    Nat.card {u // L.Mem u} * g ^ (if L.sharp = true then L.k else 0) = g ^ (N * (N - 1) / 2) := by
  intro g _ N L
  set U : Finset (Fin N × Fin N) := (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2) with hU
  set R : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun p => L.sharp = true ∧ L.s ≤ p.1 ∧ (p.1 : ℕ) < L.s + L.k ∧ (p.2 : ℕ) = L.s + L.k) with hR
  have hUc : U.card = N * (N - 1) / 2 := by
    rw [hU, Finset.card_product_filter_lt, Nat.choose_two_right]
    simp
  have hRU : R ⊆ U := by
    intro p hp
    simp only [hR, hU, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
    rw [Fin.lt_def]
    omega
  have hRc : R.card = if L.sharp = true then L.k else 0 := by
    split_ifs with h
    · have hk := L.hk
      symm
      rw [← Finset.card_range L.k]
      refine Finset.card_bij (fun i hi => (⟨L.s + i, by have := Finset.mem_range.1 hi; omega⟩, ⟨L.s + L.k, hk⟩)) ?_ ?_ ?_
      · intro i hi
        have := Finset.mem_range.1 hi
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h]
        exact ⟨by omega, by omega, trivial⟩
      · intro i hi j hj hij
        have := congrArg (fun p : Fin N × Fin N => (p.1 : ℕ)) hij
        simp only at this
        omega
      · intro p hp
        simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and, h] at hp
        refine ⟨p.1 - L.s, Finset.mem_range.2 (by omega), ?_⟩
        apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
    · simp [hR, h]
  have hM : ∀ u : GG g N, L.Mem u ↔
      ((∀ a, u.val a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ U \ R → u.val a b = 0) := by
    intro u
    simp only [Lev.Mem, IsUp, hU, hR, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, not_and, not_not]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun a b hab h => ?_⟩
      rcases lt_or_gt_of_ne hab with h' | h'
      · by_contra hne
        exact h h' (fun x1 x2 x3 x4 => hne (h3 x1 a b x2 x3 x4))
      · exact h2 a b h'
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun a b h => h2 a b h.ne' (fun h' => absurd h' (lt_asymm h))⟩, fun x1 a b x2 x3 x4 => ?_⟩
      refine h2 a b (fun h => ?_) (fun _ h => h x1 x2 x3 x4)
      subst h
      omega
  rw [Nat.card_congr (Equiv.subtypeEquivRight hM), card_up_supp g N (U \ R) (fun p hp => by
    have := (Finset.mem_sdiff.1 hp).1
    exact (Finset.mem_filter.1 this).2), ← hRc, ← pow_add, Finset.card_sdiff_add_card_eq_card hRU, hUc]

end GlobalTheory.BadShare
end
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem perm_apply_eq_of_le {N : ℕ} (τ : Equiv.Perm (Fin N)) (h : ∀ b, τ b ≤ b) (b : Fin N) : τ b = b := by
  have hs : ∑ i : Fin N, (τ i : ℕ) = ∑ i : Fin N, (i : ℕ) := Equiv.sum_comp τ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin N => (τ i : ℕ))
    (g := fun i : Fin N => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)
  exact Fin.ext this

theorem monomial_eq_of_unipotent_double_coset : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (w w' u u' : GG g N), (∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) → (∃ σ : Equiv.Perm (Fin N), ∀ a b, w'.val a b ≠ 0 → a = σ b) → IsUp g N u → IsUp g N u' → u * w = w' * u' → w = w' := by
  intro g _ N w w' u u' ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hu hu' h
  have hz : ∀ a b, a ≠ σ b → w.val a b = 0 := fun a b hab => by
    by_contra hne; exact hab (hσ a b hne)
  have hz' : ∀ a b, a ≠ σ' b → w'.val a b = 0 := fun a b hab => by
    by_contra hne; exact hab (hσ' a b hne)
  have hne : ∀ b, w.val (σ b) b ≠ 0 := by
    intro b h0
    have h1 : ((w⁻¹).val * w.val) b b = 1 := by
      rw [Units.inv_mul, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : k = σ b
      · rw [hk, h0, mul_zero]
      · rw [hz k b hk, mul_zero]
  have key : ∀ b, w.val (σ b) b = w'.val (σ b) (σ'.symm (σ b)) * u'.val (σ'.symm (σ b)) b := by
    intro b
    have h1 : (u.val * w.val) (σ b) b = (w'.val * u'.val) (σ b) b := by
      rw [← Units.val_mul, ← Units.val_mul, h]
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ b),
      Finset.sum_eq_single (σ'.symm (σ b)), hu.1, one_mul] at h1
    · exact h1
    · intro k _ hk
      rw [hz' (σ b) k, zero_mul]
      intro hh
      apply hk
      rw [hh, Equiv.symm_apply_apply]
    · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro k _ hk
      rw [hz k b hk, mul_zero]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  have hle : ∀ b, (σ.trans σ'.symm) b ≤ b := by
    intro b
    by_contra hlt
    have hlt' : b < σ'.symm (σ b) := not_le.1 hlt
    apply hne b
    rw [key b, hu'.2 _ _ hlt', mul_zero]
  have hfix : ∀ b, σ'.symm (σ b) = b := fun b => perm_apply_eq_of_le _ hle b
  have hσσ : ∀ b, σ b = σ' b := fun b => by
    have := congrArg σ' (hfix b)
    rwa [Equiv.apply_symm_apply] at this
  apply Units.ext
  ext a b
  by_cases hab : a = σ b
  · rw [hab, key b, hfix b, hu'.1, mul_one]
  · rw [hz a b hab, hz' a b (by rwa [← hσσ])]

end GlobalTheory.BadShare
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.rootF_finiteDimensional_isGalois_isPGroup : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l M₀ k n : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∀ U : X.K, Lev X (M₀ * l ^ k) U → FiniteDimensional (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧ IsGalois (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧ IsPGroup l (rootF X M₀ (M₀ * l ^ k) (l ^ n) U ≃ₐ[levF X M₀] rootF X M₀ (M₀ * l ^ k) (l ^ n) U) := by
  first | exact @GlobalTheory.KZ.ES.RootGal.rootF_finite_galois_isPGroup | exact GlobalTheory.KZ.ES.RootGal.rootF_finite_galois_isPGroup | (intros; apply GlobalTheory.KZ.ES.RootGal.rootF_finite_galois_isPGroup <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.heckeTranslateNormProduct_eq_of_dvd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (M M' q : ℕ) (f : X.K), 0 < q → M ∣ M' → Nat.Coprime q M' → Lev X M f → Nq X M q f = Nq X M' q f := by
  first | exact @GlobalTheory.KZ.ES.Nq_eq_of_dvd | exact GlobalTheory.KZ.ES.Nq_eq_of_dvd | (intros; apply GlobalTheory.KZ.ES.Nq_eq_of_dvd <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.reducesToSmallerOddWeight_of_leadingCoeffMatrix_det_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det = 0 → Reduces Γ w F := by
  first | exact @GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero | exact GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero | (intros; apply GlobalTheory.OddFrame.reduces_of_det_leadM_eq_zero <;> assumption)
end

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det ≠ 0 → ∃ U : ℍ → Matrix (Fin r) (Fin r) ℂ, Tendsto (fun τ => evM s w F τ * U τ) atImInfty (𝓝 (leadM M s w F)) ∧ Tendsto (fun τ => ModularForm.discriminant τ • U τ) atImInfty (𝓝 0) := by
  first | exact @GlobalTheory.OddFrame.exists_tendsto_evM_mul | exact GlobalTheory.OddFrame.exists_tendsto_evM_mul | (intros; apply GlobalTheory.OddFrame.exists_tendsto_evM_mul <;> assumption)
end

section

open scoped Matrix
open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_lattice_adelicMatrix_integral_translate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E :=
  @GlobalTheory.AdelicMatLat.exists_lattice_integral
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_differentiableOn_quotient_of_integral : ∀ (U : Set ℂ) (n : ℕ) (A D : ℂ → ℂ) (s : Fin n → ℂ → ℂ), IsOpen U → IsPreconnected U → DifferentiableOn ℂ A U → DifferentiableOn ℂ D U → (∀ j, DifferentiableOn ℂ (s j) U) → (∃ z ∈ U, D z ≠ 0) → (∀ z ∈ U, A z ^ n + ∑ j, s j z * A z ^ (j : ℕ) * D z ^ (n - j) = 0) → ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ (∀ z ∈ U, A z = h z * D z) ∧ ∀ z ∈ U, h z ^ n + ∑ j, s j z * h z ^ (j : ℕ) = 0 := by
  first | exact @GlobalTheory.quotient_integral_holomorphic | exact GlobalTheory.quotient_integral_holomorphic | (intros; apply GlobalTheory.quotient_integral_holomorphic <;> assumption)
end
