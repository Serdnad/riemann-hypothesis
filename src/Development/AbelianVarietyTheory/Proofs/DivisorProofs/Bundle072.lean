module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section

namespace GlobalTheory

open IsLocalRing

theorem maxIdeal_pow_dvd_natCast_of_integers :
    ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type)
      [CommRing O] [Algebra O C], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A]
      [Module.Finite O A] [IsLocalRing A] (a : A), a ∈ IsLocalRing.maximalIdeal A →
      ∃ N : ℕ, (p : A) ∣ a ^ N := by
  intro p hp C _ _ v O _ _ hv A _ _ _ _ a ha

  set J : Ideal O := (maximalIdeal A).comap (algebraMap O A) with hJdef
  haveI : J.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal A)

  have hJp : ∀ c ∈ J, ∃ k : ℕ, (p : O) ∣ c ^ k := by
    intro c hc
    have hlt : v (algebraMap O C c) < 1 := by
      refine lt_of_le_of_ne (hv.map_le_one c) ?_
      intro h1
      have hu : IsUnit c := hv.isUnit_of_one' h1
      have : IsUnit (algebraMap O A c) := hu.map _
      exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ hc this)
    have hp0 : 0 < v (algebraMap O C (p : O)) := by
      rw [map_natCast]
      exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 hp)
    obtain ⟨k, hk⟩ := NNReal.exists_pow_lt_of_lt_one hp0 hlt
    refine ⟨k, hv.dvd_of_le ?_⟩
    rw [map_pow, map_pow]
    exact hk.le

  have hI : J.map (algebraMap O A) ≤ (Ideal.span {(p : A)}).radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    obtain ⟨k, d, hd⟩ := hJp c hc
    refine ⟨k, ?_⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨algebraMap O A d, ?_⟩
    rw [← map_pow, hd, map_mul, map_natCast]

  have ha' : a ∈ (J.map (algebraMap O A)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQ, hQp⟩
    have hle : J ≤ Q.comap (algebraMap O A) := Ideal.map_le_iff_le_comap.1 hQ
    have hQc : Q.comap (algebraMap O A) = J :=
      ((inferInstance : J.IsMaximal).eq_of_le (Ideal.IsPrime.comap (algebraMap O A)).ne_top hle).symm
    haveI : (Q.comap (algebraMap O A)).IsMaximal := by rw [hQc]; infer_instance
    haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap O A) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) Q this
    rw [IsLocalRing.eq_maximalIdeal this]
    exact ha
  have h2 : a ∈ (Ideal.span {(p : A)}).radical := by
    have := Ideal.radical_mono hI ha'
    rwa [Ideal.radical_idem] at this
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, Ideal.mem_span_singleton.1 hN⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem cone_ratio_bounded (a : ℕ) (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      ∀ p q : Fin a, p ≤ q → r q / r p ≤ C := by
  have hM : (1 : ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max 1 t⁻¹ := le_trans zero_le_one hM
  refine ⟨(max 1 t⁻¹) ^ a, pow_nonneg hM0 _, fun r hr hstep p q hpq => ?_⟩
  have key : ∀ (n : ℕ) (h : (p : ℕ) + n < a), r ⟨p + n, h⟩ ≤ (max 1 t⁻¹) ^ n * r p := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih =>
      intro h
      have h' : (p : ℕ) + n < a := by omega
      have h1 := hstep ⟨p + n, h'⟩ ⟨p + (n + 1), h⟩ (by simp [add_assoc])
      have h2 : r ⟨p + (n + 1), h⟩ ≤ t⁻¹ * r ⟨p + n, h'⟩ := by
        rw [inv_mul_eq_div, le_div_iff₀ ht, mul_comm]; exact h1
      calc r ⟨p + (n + 1), h⟩ ≤ t⁻¹ * r ⟨p + n, h'⟩ := h2
        _ ≤ max 1 t⁻¹ * r ⟨p + n, h'⟩ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hr _).le
        _ ≤ max 1 t⁻¹ * ((max 1 t⁻¹) ^ n * r p) := mul_le_mul_of_nonneg_left (ih h') hM0
        _ = (max 1 t⁻¹) ^ (n + 1) * r p := by ring
  have hpq' : (p : ℕ) ≤ q := hpq
  have hlt : (p : ℕ) + (q - p) < a := by have := q.2; omega
  have hq : (⟨p + (q - p), hlt⟩ : Fin a) = q := Fin.ext (by simp only; omega)
  have h3 := key (q - p) hlt
  rw [hq] at h3
  rw [div_le_iff₀ (hr p)]
  refine h3.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM ?_) (hr p).le)
  have := q.2; omega

end GlobalTheory
end

section

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem choose_mul_one_sub_le_choose (N M D : ℕ) (x : ℝ) (hx : 0 ≤ x) (hDM : D ≤ M) (hMN : M ≤ N)
    (h : (N : ℝ) - M ≤ x * ((N : ℝ) - D + 1)) :
    ∀ k ≤ D, ((N.choose k : ℕ) : ℝ) * (1 - k * x) ≤ ((M.choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hkD : k ≤ D := by omega
    have ih' := ih hkD
    have hkM : k ≤ M := by omega
    have hkN : k ≤ N := by omega
    have eN : ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq N k
      rw [← Nat.cast_sub hkN]
      exact_mod_cast h
    have eM : ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq M k
      rw [← Nat.cast_sub hkM]
      exact_mod_cast h
    have hk1 : (k : ℝ) + 1 ≤ D := by exact_mod_cast hk
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
    have hA : (0 : ℝ) ≤ ((N.choose k : ℕ) : ℝ) := by positivity
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity

    have hbr : (0 : ℝ) ≤ x * ((N : ℝ) - k) + x * k * ((N : ℝ) - M) - ((N : ℝ) - M) := by
      have h1 : x * ((N : ℝ) - D + 1) ≤ x * ((N : ℝ) - k) := by
        apply mul_le_mul_of_nonneg_left _ hx
        linarith
      have h2 : 0 ≤ x * k * ((N : ℝ) - M) := by
        have : (0 : ℝ) ≤ (N : ℝ) - M := by linarith
        positivity
      linarith
    have hstep : ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x)
        ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h3 : ((N.choose k : ℕ) : ℝ) * (1 - k * x) * ((M : ℝ) - k)
          ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) :=
        mul_le_mul_of_nonneg_right ih' (by linarith)
      have h4 := mul_nonneg hA hbr
      nlinarith [h3, h4]
    have goal' : ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
        ≤ ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      rw [eM]
      calc ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
          = ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) * (1 - ((k : ℝ) + 1) * x) := by ring
        _ = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x) := by rw [eN]
        _ ≤ _ := hstep
    push_cast
    exact le_of_mul_le_mul_right goal' hpos

theorem share_bound_of_jet_count :
    ∀ (D T a : ℕ) (ρ δ d : ℝ), 2 ≤ D → D + 1 ≤ T → 0 ≤ ρ → ρ ≤ 1 / 2 → T + D + 3 ≤ a → (a : ℝ) ≤ ((T : ℝ) + D + 3) / (1 - ρ) → 0 ≤ δ → 0 ≤ d → d ≤ (((a + D).choose D : ℕ) : ℝ) * δ → (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by
  intro D T a ρ δ d hD hDT hρ0 hρ hTa ha hδ hd0 hd
  have hT1 : 1 ≤ T := by omega
  have hT : (0 : ℝ) < T := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    linarith
  have hTr : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub hT1]
    simp
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hTa' : (T : ℝ) + D + 3 ≤ a := by exact_mod_cast hTa
  have hxnn : 0 ≤ 4 * (D : ℝ) / T + ρ := by positivity

  have key := choose_mul_one_sub_le_choose (a + D) (T - 1) D (4 * (D : ℝ) / T + ρ) hxnn
    (by omega) (by omega) (by
      push_cast
      rw [hTr]
      have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
      have hamul : (a : ℝ) * (1 - ρ) ≤ (T : ℝ) + D + 3 := (le_div_iff₀ h1ρ).mp ha
      have h4 : 4 * (D : ℝ) ≤ 4 * (D : ℝ) / T * ((a : ℝ) + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hT]
        have : (0 : ℝ) ≤ 4 * D := by positivity
        nlinarith
      nlinarith [h4, hamul, hρ0, hD2]) D le_rfl
  have hc : 1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ) ≤ 1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ) := by
    have e : (D : ℝ) * (4 * (D : ℝ) / T + ρ) = 4 * ((D : ℝ) ^ 2 / T) + D * ρ := by ring
    have h1 : 0 ≤ (D : ℝ) ^ 2 / T := by positivity
    have h2 : 0 ≤ (D : ℝ) * ρ := by positivity
    rw [e]
    linarith
  have hB : (0 : ℝ) ≤ (((a + D).choose D : ℕ) : ℝ) * δ := by positivity
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by positivity
  rcases le_or_gt (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) 0 with h | h
  · have : (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hd0
    linarith
  · calc (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d
        ≤ (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_left hd h.le
      _ ≤ (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_right hc hB
      _ = ((((a + D).choose D : ℕ) : ℝ) * (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ))) * δ := by ring
      _ ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := mul_le_mul_of_nonneg_right key hδ

end GlobalTheory
end

section

namespace GlobalTheory

theorem addValuation_natCast_eq_padicValNat :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime →
      v (p : C) = 1 → ∀ n : ℕ, n ≠ 0 →
        v (n : C) = (((padicValNat p n : ℕ) : ℝ) : WithTop ℝ) := by
  intro C _ _ v p hp hvp n hn
  have h1 : v (1 : C) = 0 := v.map_one

  have hnat : ∀ m : ℕ, 0 ≤ v (m : C) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h := v.map_add (k : C) 1
      rw [h1] at h
      push_cast
      exact le_trans (le_min ih le_rfl) h
  have hint : ∀ a : ℤ, 0 ≤ v (a : C) := by
    intro a
    obtain ⟨m, rfl | rfl⟩ := a.eq_nat_or_neg
    · simpa using hnat m
    · simpa [v.map_neg] using hnat m

  have hcop : ∀ m : ℕ, Nat.Coprime m p → v (m : C) = 0 := by
    intro m hm
    by_contra hne
    have hpos : 0 < v (m : C) := lt_of_le_of_ne (hnat m) (Ne.symm hne)
    have hbez : ((1 : ℤ)) = (m : ℤ) * Nat.gcdA m p + (p : ℤ) * Nat.gcdB m p := by
      have := Nat.gcd_eq_gcd_ab m p
      rw [hm] at this
      simpa using this
    have hC : (1 : C) = (m : C) * ((Nat.gcdA m p : ℤ) : C) + (p : C) * ((Nat.gcdB m p : ℤ) : C) := by
      have := congrArg (fun z : ℤ => (z : C)) hbez
      simpa using this
    have ha : 0 < v ((m : C) * ((Nat.gcdA m p : ℤ) : C)) := by
      rw [v.map_mul]
      exact lt_of_lt_of_le hpos (le_add_of_nonneg_right (hint _))
    have hb : 0 < v ((p : C) * ((Nat.gcdB m p : ℤ) : C)) := by
      rw [v.map_mul, hvp]
      exact lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_add_of_nonneg_right (hint _))
    have h := v.map_add ((m : C) * ((Nat.gcdA m p : ℤ) : C)) ((p : C) * ((Nat.gcdB m p : ℤ) : C))
    rw [← hC, h1] at h
    exact absurd (lt_of_lt_of_le (lt_min ha hb) h) (lt_irrefl _)

  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (fun {p n : ℕ} => _root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat p n)) (p := p) (n := n)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by simpa using hm)
  have hnd : ¬ p ∣ m := by
    intro hd
    obtain ⟨c, rfl⟩ := hd
    have : p ^ (padicValNat p n + 1) ∣ n := ⟨c, by rw [pow_succ, mul_assoc, ← hm]⟩
    rw [Nat.padicValNat_def] at this
    exact pow_succ_multiplicity_not_dvd (p := p) hn this
  have hcm : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
  have hcast : (n : C) = (p : C) ^ (padicValNat p n) * (m : C) := by
    conv_lhs => rw [hm]
    push_cast
    ring
  rw [hcast, v.map_mul, v.map_pow, hvp, hcop m hcm, add_zero]
  simp

end GlobalTheory
end

section

namespace GlobalTheory.EmbeddingMean

theorem card_fibre {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] [DecidableEq (A →ₐ[K] C)]
    (f : A →ₐ[K] C) :
    (Finset.univ.filter (fun g : B →ₐ[K] C => g.comp (IsScalarTower.toAlgHom K A B) = f)).card
      = Module.finrank A B := by
  letI : Algebra A C := f.toRingHom.toAlgebra
  haveI : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : FiniteDimensional A B := Module.Finite.of_restrictScalars_finite K A B
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  rw [← AlgHom.card A B C, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun g => { g.1.toRingHom with
        commutes' := fun a => by
          have := DFunLike.congr_fun g.2 a
          exact this }
      invFun := fun h => ⟨h.restrictScalars K, AlgHom.ext fun a => h.commutes a⟩
      left_inv := fun g => Subtype.ext (AlgHom.ext fun _ => rfl)
      right_inv := fun h => AlgHom.ext fun _ => rfl }

theorem tower {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] :
    (∀ f : A →ₐ[K] C, ∃ g : B →ₐ[K] C, g.comp (IsScalarTower.toAlgHom K A B) = f) ∧
    ∀ F : (A →ₐ[K] C) → ℝ,
      (∑ g : B →ₐ[K] C, F (g.comp (IsScalarTower.toAlgHom K A B))) / (Module.finrank K B : ℝ)
        = (∑ f : A →ₐ[K] C, F f) / (Module.finrank K A : ℝ) := by
  classical
  haveI : FiniteDimensional A B := Module.Finite.of_restrictScalars_finite K A B
  have hpos : 0 < Module.finrank A B := Module.finrank_pos
  refine ⟨fun f => ?_, fun F => ?_⟩
  · have h := card_fibre (B := B) f
    obtain ⟨g, hg⟩ := Finset.card_pos.mp (h ▸ hpos)
    exact ⟨g, (Finset.mem_filter.mp hg).2⟩
  · have hsum : (∑ g : B →ₐ[K] C, F (g.comp (IsScalarTower.toAlgHom K A B)))
        = (Module.finrank A B : ℝ) * ∑ f : A →ₐ[K] C, F f := by
      rw [← Finset.sum_fiberwise Finset.univ
        (fun g : B →ₐ[K] C => g.comp (IsScalarTower.toAlgHom K A B)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => F f)
        (fun g hg => by rw [(Finset.mem_filter.mp hg).2]),
        Finset.sum_const, nsmul_eq_mul]
      congr 2
      convert card_fibre (B := B) f
    have hA : (Module.finrank K A : ℝ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := K) (M := A)).ne'
    have hB : (Module.finrank A B : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [hsum, ← Module.finrank_mul_finrank K A B]
    push_cast
    field_simp

end GlobalTheory.EmbeddingMean
end

section

noncomputable section

namespace GlobalTheory.StdLoc

def rowBlockIndicatorFrom (a : ℕ) {d : ℕ} (i : Fin d) : ℕ := if a ≤ i.1 then 1 else 0

def blockPar (R : Type) [CommRing R] (a d : ℕ) : Subgroup (GL (Fin d) R) where
  carrier := {g | (g : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)}
  mul_mem' := fun {x y} hx hy => by
    show ((x * y : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_mul]; exact hx.mul hy
  one_mem' := by
    show ((1 : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_one]; exact Matrix.blockTriangular_one
  inv_mem' := fun {x} hx => by
    show ((x⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    letI : Invertible (x : Matrix (Fin d) (Fin d) R) := Units.invertible x
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hx

theorem _root_.GlobalTheory.StdLoc.mem_blockPar {R : Type} [CommRing R] {a d : ℕ} (g : GL (Fin d) R) :
    g ∈ _root_.GlobalTheory.StdLoc.blockPar R a d ↔ ∀ i j : Fin d, j.1 < a → a ≤ i.1 → (g : Matrix (Fin d) (Fin d) R) i j = 0 := by
  show (g : Matrix (Fin d) (Fin d) R).BlockTriangular (_root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom a) ↔ _
  unfold Matrix.BlockTriangular _root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom
  constructor
  · intro h i j hj hi
    apply h
    simp [hi, not_le.mpr hj]
  · intro h i j hlt
    refine h i j ?_ ?_ <;> split_ifs at hlt <;> omega

def glVol (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)

def blockIdx (q : ℝ) (c a a' : ℕ) : ℝ := q ^ (c * a * a') * glVol q (a + a') / (glVol q a * glVol q a')

end GlobalTheory.StdLoc
end
end

section

open Filter Topology

namespace GlobalTheory

theorem lowerBound_along_residues : ∀ (d n : ℕ) (u : ℕ → ℝ) (γ : ℝ), 0 < n → (∀ r < n, ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop, (γ - ε) * (q : ℝ) ^ d ≤ u (n * q + r)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (γ / (n : ℝ) ^ d - ε) * (M : ℝ) ^ d ≤ u M := by
  intro d n u γ hn h ε hε
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnd : (0:ℝ) < (n:ℝ)^d := pow_pos hnR d
  set ε' := ε * (n:ℝ)^d / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have h1 : ∀ᶠ q : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * (q:ℝ)^d ≤ u (n*q + r) :=
    (Filter.eventually_all_finite (Set.finite_Iio n)).2 (fun r hr => h r hr ε' hε'pos)
  have h2 : ∀ᶠ M : ℕ in atTop, ∀ r ∈ Set.Iio n, (γ - ε') * ((M / n : ℕ):ℝ)^d ≤ u (n*(M/n) + r) :=
    (Nat.tendsto_div_const_atTop hn.ne').eventually h1
  have hf : Tendsto (fun M : ℕ => ((M / n : ℕ):ℝ) / M) atTop (𝓝 (1 / n)) := by
    have hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n)) := by
      simpa using (tendsto_const_nhds (x := 1/(n:ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with M hM
      have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
      have key : (n:ℝ) * ((M/n : ℕ):ℝ) + ((M % n : ℕ):ℝ) = M := by exact_mod_cast Nat.div_add_mod M n
      have hmod : ((M % n : ℕ):ℝ) < n := by exact_mod_cast Nat.mod_lt M hn
      have hq : (M:ℝ) - n ≤ n * ((M/n : ℕ):ℝ) := by linarith
      rw [div_sub_div _ _ hnR.ne' hMR.ne', div_le_div_iff₀ (by positivity) hMR]
      nlinarith [mul_le_mul_of_nonneg_right hq hMR.le]
    · filter_upwards [eventually_gt_atTop 0] with M hM
      have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
      rw [div_le_div_iff₀ hMR hnR]
      have h0 : ((M / n : ℕ):ℝ) ≤ (M:ℝ) / n := Nat.cast_div_le
      rw [le_div_iff₀ hnR] at h0
      linarith
  have hg : Tendsto (fun M : ℕ => (γ - ε') * (((M / n : ℕ):ℝ) / M)^d) atTop (𝓝 ((γ - ε') * (1/(n:ℝ))^d)) :=
    (hf.pow d).const_mul _
  have hlim : (γ - ε') * (1/(n:ℝ))^d = γ / (n:ℝ)^d - ε/2 := by
    rw [one_div_pow, hε']; field_simp
  have h3 : ∀ᶠ M : ℕ in atTop, γ / (n:ℝ)^d - ε < (γ - ε') * (((M / n : ℕ):ℝ) / M)^d := by
    rw [hlim] at hg
    exact hg.eventually (lt_mem_nhds (by linarith))
  filter_upwards [h2, h3, eventually_gt_atTop 0] with M hM2 hM3 hM
  have hMR : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hMd : (0:ℝ) < (M:ℝ)^d := pow_pos hMR d
  have e1 := hM2 (M % n) (Nat.mod_lt M hn)
  rw [Nat.div_add_mod] at e1
  rw [div_pow, ← mul_div_assoc, lt_div_iff₀ hMd] at hM3
  linarith

end GlobalTheory
end
