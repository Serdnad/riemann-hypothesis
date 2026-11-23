module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle001
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
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.pair_character_eq_finrank : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), _root_.GlobalTheory.BI.pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  intro K L _ _ _ _ _ G _ _ V _ _ _ W _ _ _ ρ σ
  classical
  haveI := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  unfold _root_.GlobalTheory.BI.pair
  rw [finsum_eq_sum_of_fintype]

  simpa only [map_mul, map_sum, map_inv₀, map_natCast] using h

end GlobalTheory.BI
end

section

open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type} [Group G] {n : ℕ}
    (ρ : Representation K G (Fin n → K)) : Representation L G (Fin n → L) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L))
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem character_extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type}
    [Group G] {n : ℕ} (ρ : Representation K G (Fin n → K)) (g : G) :
    (extendScalarsRep K L ρ).character g = algebraMap K L (ρ.character g) := by
  have h1 : (extendScalarsRep K L ρ).character g
      = ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L)).trace := by
    change LinearMap.trace L _ (Matrix.toLin' _) = _
    exact Matrix.trace_toLin'_eq _
  have h2 : ρ.character g = (LinearMap.toMatrix' (ρ g)).trace := by
    change LinearMap.trace K _ (ρ g) = _
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  rw [h1, h2]

  simp [Matrix.trace, map_sum]

theorem isChar_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G]
    (χ : G → L), IsChar K L χ → IsChar L L χ := by
  intro K L _ _ _ G _ χ ⟨n, ρ, h⟩
  refine ⟨n, extendScalarsRep K L ρ, fun g => ?_⟩
  rw [h g, character_extendScalarsRep]
  rfl

end GlobalTheory.BI
end
end

section

open Polynomial

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F]

theorem mangoldtConv_eq_of_dvd_pow {f g : F[X]} (hf : f.Monic) (hf' : Irreducible f) (hg : g.Monic)
    (hg' : Irreducible g) {n : ℕ} (h : g ∣ f ^ n) : g = f :=
  eq_of_monic_of_associated hg hf (hg'.associated_of_dvd hf' (hg'.prime.dvd_of_dvd_pow h))

theorem mangoldt_pow (s : F[X] → ℂ) (f : F[X]) (m : ℕ) (hf : f.Monic) (hf' : Irreducible f) (hm : 0 < m) :
    mangoldt s (f ^ m) = s f := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ f ^ m = g ^ k} = {f} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hg, hg', k, hk, h⟩
      exact mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := m) (h ▸ dvd_pow_self g hk.ne')
    · rintro rfl
      exact ⟨hf, hf', m, hm, rfl⟩
  rw [mangoldt, this, finsum_mem_singleton]

theorem mangoldt_eq_zero (s : F[X] → ℂ) (P : F[X])
    (h : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) : mangoldt s P = 0 := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ P = g ^ k} = ∅ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hg, hg', k, hk, h'⟩
    exact h ⟨g, k, hg, hg', hk, h'⟩
  rw [mangoldt, this, finsum_mem_empty]

theorem conv_const_one_eq_divisorSum (a : F[X] → ℂ) (P : F[X]) (hP : P.Monic) :
    conv a (fun _ => 1) P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, a D := by
  unfold conv
  refine finsum_mem_eq_of_bijOn (fun x => x.1) ⟨?_, ?_, ?_⟩ ?_
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩
    exact ⟨hD, E, h.symm⟩
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩ ⟨D', E'⟩ ⟨_, _, h'⟩ h''
    simp only at h h' h'' hD
    subst h''
    rw [mul_left_cancel₀ hD.ne_zero (h.trans h'.symm)]
  · rintro D ⟨hD, E, h⟩
    exact ⟨(D, E), ⟨hD, hD.of_mul_monic_left (h ▸ hP), h.symm⟩, rfl⟩
  · intro x _
    simp

theorem mangoldtConv_finite_monicDivisors (P : F[X]) (hP : P.Monic) :
    {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by
  have := Polynomial.fintypeSubtypeMonicDvd P hP.ne_zero
  exact Set.finite_coe_iff.mp (Finite.of_fintype {g : F[X] // g.Monic ∧ g ∣ P})

theorem mangoldt_divisorSum_mul (s : F[X] → ℂ) (f Q : F[X]) (hf : f.Monic) (hf' : Irreducible f)
    (hQ : Q.Monic) :
    ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ f * Q}, mangoldt s D =
      s f + ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ Q}, mangoldt s D := by
  obtain ⟨n, R, hR, hQR⟩ := WfDvdMonoid.max_power_factor hQ.ne_zero hf'
  have hnot : f ^ (n + 1) ∉ {D : F[X] | D.Monic ∧ D ∣ Q} := by
    rintro ⟨_, h⟩
    rw [hQR, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n hf.ne_zero)] at h
    exact hR h
  rw [← mangoldt_pow s f (n + 1) hf hf' n.succ_pos,
    ← finsum_mem_insert _ hnot (mangoldtConv_finite_monicDivisors Q hQ)]
  refine finsum_mem_inter_support_eq _ _ _ ?_
  ext D
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Function.mem_support]
  refine and_congr_left fun hD => ?_
  constructor
  · rintro ⟨hDm, hd⟩
    obtain ⟨g, m, hg, hg', hm, rfl⟩ := not_not.mp (mt (mangoldt_eq_zero s D) hD)
    by_cases hgf : g = f
    · subst hgf
      rcases lt_trichotomy m (n + 1) with h | h | h
      · exact Or.inr ⟨hDm, hQR ▸ (pow_dvd_pow g (by omega)).mul_right R⟩
      · exact Or.inl (by rw [h])
      · exfalso
        have h2 : g ^ (n + 1) * g ∣ g ^ (n + 1) * R := by
          have h3 : g ^ (n + 1 + 1) ∣ g * Q := (pow_dvd_pow g (by omega)).trans hd
          rw [hQR, ← mul_assoc, ← pow_succ', pow_succ g (n + 1)] at h3
          exact h3
        exact hR ((mul_dvd_mul_iff_left (pow_ne_zero _ hf.ne_zero)).mp h2)
    · refine Or.inr ⟨hDm, ?_⟩
      have hc : IsCoprime g f := by
        rw [hg'.coprime_iff_not_dvd]
        intro h
        exact hgf (mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := 1) (by simpa using h))
      exact (hc.pow_left (m := m)).dvd_of_dvd_mul_left hd
  · rintro (rfl | ⟨hDm, hd⟩)
    · refine ⟨hf.pow _, ?_⟩
      rw [hQR, ← mul_assoc, ← pow_succ']
      exact dvd_mul_right _ _
    · exact ⟨hDm, hd.mul_left f⟩

theorem IsAdditive.eq_divisorSum_mangoldt {s : F[X] → ℂ} (hs : IsAdditive s) (P : F[X]) (hP : P.Monic) :
    s P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, mangoldt s D := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases hu : IsUnit P
    · have h1 : P = 1 := hP.isUnit_iff.mp hu
      subst h1
      have h0 : s 1 = 0 := by
        have := hs 1 1 monic_one monic_one
        rw [mul_one] at this
        exact left_eq_add.mp this
      rw [h0]
      symm
      refine finsum_mem_of_eqOn_zero fun D hD => ?_
      refine mangoldt_eq_zero s D ?_
      rintro ⟨g, m, _, hg', hm, rfl⟩
      exact hg'.not_isUnit (isUnit_of_dvd_one ((dvd_pow_self g hm.ne').trans hD.2))
    · obtain ⟨f, hf, hf', Q, rfl⟩ := Polynomial.exists_monic_irreducible_factor P hu
      have hQ : Q.Monic := hf.of_mul_monic_left hP
      have hlt : Q.natDegree < n := by
        rw [← hn, hf.natDegree_mul hQ]
        have := hf'.natDegree_pos
        omega
      rw [mangoldt_divisorSum_mul s f Q hf hf' hQ, hs f Q hf hQ, ih _ hlt Q hQ rfl]

theorem mangoldt_conv_spec : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s →
    (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧
    (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧
    ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) →
      mangoldt s P = 0 := by
  intro F _ s hs
  refine ⟨fun P hP => ?_, mangoldt_pow s, mangoldt_eq_zero s⟩
  rw [conv_const_one_eq_divisorSum _ P hP]
  exact hs.eq_divisorSum_mangoldt P hP

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL.PrimOrth

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem neg_mem_nilRad {A : Submodule F V} {h : Module.End F V} (hh : h ∈ nilRad A) : -h ∈ nilRad A :=
  ⟨fun x => by simpa using hh.1 x, fun x hx => by simpa using hh.2 x hx⟩

theorem add_preserves {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) : ∀ x ∈ A, (g + h) x ∈ A :=
  fun x hx => A.add_mem (hg x hx) (hh.1 x)

theorem add_preserves_iff {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A) :
    (∀ x ∈ A, (g + h) x ∈ A) ↔ ∀ x ∈ A, g x ∈ A := by
  refine ⟨fun H => ?_, add_preserves hh⟩
  have := add_preserves (neg_mem_nilRad hh) H
  simpa using this

theorem isUnit_add [FiniteDimensional F V] {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) (hu : IsUnit g) : IsUnit (g + h) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot] at hu
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hinj : Function.Injective (g.restrict hg) := by
    intro a b hab
    exact Subtype.ext (hu (congrArg Subtype.val hab))
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  have hx' : g x + h x = 0 := hx
  have hgx : g x ∈ A := by
    rw [eq_neg_of_add_eq_zero_left hx']
    exact A.neg_mem (hh.1 x)
  obtain ⟨w, hw⟩ := hsurj ⟨g x, hgx⟩
  have hwx : (w : V) = x := hu (congrArg Subtype.val hw)
  have hxA : x ∈ A := hwx ▸ w.2
  rw [hh.2 x hxA, add_zero] at hx'
  exact hu (by rw [hx', map_zero])

theorem isUnit_add_iff [FiniteDimensional F V] {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) : IsUnit (g + h) ↔ IsUnit g := by
  refine ⟨fun H => ?_, isUnit_add hh hg⟩
  have := isUnit_add (neg_mem_nilRad hh) (add_preserves hh hg) H
  simpa using this

theorem sum_mul_eq_zero [Fintype (Module.End F V)] {φ : Module.End F V → ℂ} (hφ : IsPrimitive φ)
    {A : Submodule F V} (h0 : A ≠ ⊥) (h1 : A ≠ ⊤) (f : Module.End F V → ℂ)
    (hf : ∀ g, ∀ h ∈ nilRad A, f (g + h) = f g) (hf0 : ∀ g, ¬ (∀ x ∈ A, g x ∈ A) → f g = 0) :
    ∑ g, φ g * f g = 0 := by
  classical
  have hfin : (nilRad A).Finite := Set.toFinite _
  have hne : (hfin.toFinset.card : ℂ) ≠ 0 := by
    have : hfin.toFinset.Nonempty := ⟨0, by
      rw [Set.Finite.mem_toFinset]
      exact ⟨fun x => by simp, fun x _ => by simp⟩⟩
    exact_mod_cast this.card_pos.ne'
  have key : ∑ h ∈ hfin.toFinset, ∑ g, φ g * f g = 0 := by
    have : ∀ h ∈ hfin.toFinset, ∑ g, φ g * f g = ∑ g, φ (g + h) * f g := by
      intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      rw [← Equiv.sum_comp (Equiv.addRight h)]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Equiv.coe_addRight, hf g h hh]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [← Finset.sum_mul]
    by_cases hg : ∀ x ∈ A, g x ∈ A
    · have := hφ A h0 h1 g hg
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at this
      rw [this, zero_mul]
    · rw [hf0 g hg, mul_zero]
  rw [Finset.sum_const, nsmul_eq_mul] at key
  exact (mul_eq_zero.mp key).resolve_left hne

theorem psi_bot {s : F[X] → ℂ} (hs : IsAdditive s) (U : Type) [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] [Subsingleton U] (g : Module.End F U) : psi s U g = 0 := by
  have h1 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    simpa using this
  have hc : LinearMap.charpoly g = 1 := by
    have hm := LinearMap.charpoly_monic g
    rw [← hm.natDegree_eq_zero, LinearMap.charpoly_natDegree]
    exact Module.finrank_zero_of_subsingleton
  haveI : IsEmpty {W : Submodule F U // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} :=
    ⟨fun W => W.2.1 (Subsingleton.elim _ _)⟩
  rw [psi_eq, hc, h1, finsum_of_isEmpty, sub_zero]


open Classical in
theorem ipGL_psi_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (hs : IsAdditive s) (φ : Module.End F V → ℂ)
    (hφ : IsPrimitive φ) : ipGL φ (psi s V) = ipGL φ (fun g => s (LinearMap.charpoly g)) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[F] V))
  haveI : Finite (Submodule F V) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule F V))
  letI := Fintype.ofFinite (Module.End F V)
  letI := Fintype.ofFinite (Submodule F V)
  let R : Submodule F V → Module.End F V → ℂ := fun W g =>
    if h : W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W then psi s W (g.restrict h.2) else 0
  have hR : ∀ g, psi s V g = s (LinearMap.charpoly g) - ∑ W, R W g := by
    intro g
    rw [psi_eq, finsum_eq_sum_of_fintype]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun W : Submodule F V => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun W : Submodule F V => ¬ (W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W)), add_zero,
      Finset.sum_subtype (p := fun W : Submodule F V => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) _ (by simp)]
    · refine Finset.sum_congr rfl fun W _ => ?_
      simp only [R, dif_pos W.2]
    · intro W hW
      simp only [R, dif_neg (Finset.mem_filter.mp hW).2]
  have hW : ∀ W, ∑ g, φ g * (if IsUnit g then star (R W g) else 0) = 0 := by
    intro W
    by_cases h1 : W = ⊤
    · refine Finset.sum_eq_zero fun g _ => ?_
      have : R W g = 0 := dif_neg (fun h => h.1 h1)
      simp [this]
    by_cases h0 : W = ⊥
    · refine Finset.sum_eq_zero fun g _ => ?_
      have : R W g = 0 := by
        subst h0
        simp only [R]
        split_ifs
        · exact psi_bot hs _ _
        · rfl
      simp [this]
    refine sum_mul_eq_zero hφ h0 h1 _ ?_ ?_
    · intro g h hh
      by_cases hg : ∀ x ∈ W, g x ∈ W
      · have e : R W (g + h) = R W g := by
          simp only [R]
          rw [dif_pos ⟨h1, add_preserves hh hg⟩, dif_pos ⟨h1, hg⟩]
          congr 1
          ext x
          simp [LinearMap.restrict_apply, hh.2 x x.2]
        simp only [e, isUnit_add_iff hh hg]
      · have e1 : R W g = 0 := dif_neg (fun H => hg H.2)
        have e2 : R W (g + h) = 0 := dif_neg (fun H => hg ((add_preserves_iff hh).mp H.2))
        simp [e1, e2]
    · intro g hg
      have e1 : R W g = 0 := dif_neg (fun H => hg H.2)
      simp [e1]
  have hsum : ∀ ψ : Module.End F V → ℂ,
      ipGL φ ψ = ∑ g, φ g * (if IsUnit g then star (ψ g) else 0) := by
    intro ψ
    rw [ipGL, finsum_mem_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : IsUnit g
    · simp [Set.indicator, hg]
    · simp [Set.indicator, hg]
  rw [hsum, hsum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have h2 : ∑ W, ∑ g, φ g * (if IsUnit g then star (R W g) else 0) = 0 :=
    Finset.sum_eq_zero fun W _ => hW W
  rw [Finset.sum_comm, ← neg_eq_zero, ← Finset.sum_neg_distrib] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : IsUnit g
  · simp only [if_pos hg, hR g, star_sub, star_sum, ← Finset.mul_sum]
    ring
  · simp [hg]

end GlobalTheory.CuspGL.PrimOrth
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL.ConvCancel

theorem finite_pairs {F : Type} [Field F] (P : F[X]) (hP : P ≠ 0) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  classical
  have hfin : {g : F[X] | g.Monic ∧ g ∣ P}.Finite := by
    have h := Polynomial.fintypeSubtypeMonicDvd P hP
    exact @Finite.of_fintype _ h
  refine (hfin.prod hfin).subset ?_
  rintro ⟨D, E⟩ ⟨hD, hE, h⟩
  exact ⟨⟨hD, Dvd.intro _ h⟩, ⟨hE, Dvd.intro_left _ h⟩⟩

theorem conv_cancel : ∀ (F : Type) [Field F] (a b m : F[X] → ℂ), m 1 = 1 →
    (∀ P : F[X], P.Monic → conv a m P = conv b m P) → ∀ P : F[X], P.Monic → a P = b P := by
  intro F _ a b m hm h P
  classical
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    have hfin := finite_pairs P hP.ne_zero
    have h1 := h P hP
    unfold conv at h1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
    have hmem : ((P, 1) : F[X] × F[X]) ∈ hfin.toFinset := by
      simp [hP]
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at h1
    have h2 : ∑ x ∈ hfin.toFinset.erase (P, 1), a x.1 * m x.2
        = ∑ x ∈ hfin.toFinset.erase (P, 1), b x.1 * m x.2 := by
      refine Finset.sum_congr rfl ?_
      rintro ⟨D, E⟩ hx
      rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hx
      obtain ⟨hne, hD, hE, hDE⟩ := hx
      simp only at hD hE hDE ⊢
      have hE1 : E ≠ 1 := by
        rintro rfl
        apply hne
        rw [← hDE, mul_one]
      have hdeg : D.natDegree < n := by
        rw [← hn, ← hDE, hD.natDegree_mul hE]
        have : E.natDegree ≠ 0 := fun h0 => hE1 (hE.natDegree_eq_zero.mp h0)
        omega
      rw [ih _ hdeg D rfl hD]
    rw [h2] at h1
    simpa [hm] using h1

end GlobalTheory.CuspGL.ConvCancel
end

section


theorem _root_.GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy : ∀ (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X] (x : G) (p k : ℕ), p.Prime → Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  first | exact @GlobalTheory.card_fixedBy_pow_prime_pow_modEq | exact GlobalTheory.card_fixedBy_pow_prime_pow_modEq | (intros; apply GlobalTheory.card_fixedBy_pow_prime_pow_modEq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex : ∀ (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ), p.Prime → ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧ ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by
  first | exact @GlobalTheory.exists_sylow_over_subgroup | exact GlobalTheory.exists_sylow_over_subgroup | (intros; apply GlobalTheory.exists_sylow_over_subgroup <;> assumption)
end
