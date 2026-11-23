module

public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle007
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open Formalism.UG

noncomputable section

namespace Formalism.UG.P

theorem finsum_mul_eq_sum_over_classes {X Y : Type} (S : Finset X) (g φv : X → ℂ) (c : Y → ℂ) (φ1 : ℂ)
    (P : Y → X → Prop) {_ : ∀ y x, Decidable (P y x)}
    (hS : ∀ x, g x ≠ 0 → x ∈ S) (huniq : ∀ x y y', P y x → P y' x → y = y')
    (hφ : ∀ x y, P y x → φv x = c y * φ1) (hnone : ∀ x, (∀ y, ¬ P y x) → φv x = 0) :
    ∑ᶠ x, g x * φv x = (∑ᶠ y, c y * ∑ᶠ x, if P y x then g x else 0) * φ1 := by
  classical
  have hsl : Function.support (fun x => g x * φv x) ⊆ (S : Set X) :=
    fun x hx => hS x (left_ne_zero_of_mul hx)
  have hin : ∀ y, (∑ᶠ x, if P y x then g x else 0) = ∑ x ∈ S, if P y x then g x else 0 := by
    intro y
    apply finsum_eq_sum_of_support_subset
    intro x hx
    by_cases hP : P y x
    · exact hS x (by simpa [hP] using hx)
    · exact absurd (by simp [hP]) hx
  have hTfin : (⋃ x ∈ (S : Set X), {y | P y x}).Finite :=
    S.finite_toSet.biUnion fun x _ => Set.Subsingleton.finite fun y hy y' hy' => huniq x y y' hy hy'
  have hout : (∑ᶠ y, c y * ∑ x ∈ S, if P y x then g x else 0) =
      ∑ y ∈ hTfin.toFinset, c y * ∑ x ∈ S, if P y x then g x else 0 := by
    apply finsum_eq_sum_of_support_subset
    intro y hy
    rw [Set.Finite.coe_toFinset]
    have hne : (∑ x ∈ S, if P y x then g x else 0) ≠ 0 := right_ne_zero_of_mul hy
    obtain ⟨x, hxS, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine Set.mem_biUnion (Finset.mem_coe.mpr hxS) ?_
    by_contra hP
    exact hx (if_neg hP)
  rw [finsum_eq_sum_of_support_subset _ hsl]
  simp only [hin]
  rw [hout, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hxS => ?_
  by_cases hex : ∃ y, P y x
  · obtain ⟨y0, hy0⟩ := hex
    have hy0T : y0 ∈ hTfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact Set.mem_biUnion (Finset.mem_coe.mpr hxS) hy0
    rw [Finset.sum_eq_single y0, if_pos hy0, hφ x y0 hy0]
    · ring
    · intro y _ hy
      rw [if_neg (fun h => hy (huniq x y y0 h hy0))]
      ring
    · intro h
      exact absurd hy0T h
  · push_neg at hex
    rw [hnone x hex, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg (hex y)]
    ring

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem fSatake_chiDelta_one {q m : ℕ} (α : Fin m → ℂ) :
    chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs with h
  · simp [fSatake_ord_one]
  · rfl

theorem fSatake_key (hSph : SphericalExistsU) [CompleteSpace L] {ϖ : L} {q m : ℕ}
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) {α : Fin m → ℂ}
    (hα : ∀ i, α i ≠ 0) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) {φ : GU σ n → ℂ}
    (hφ : IsSphericalU q α φ) :
    ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out * φ x.out = SatU ϖ q h α * φ 1 := by
  classical
  have hfin := finite_supp (KU σ n) (isCommensurated_integral_unitary_of_unramified hU n) h hh
  unfold SatU
  exact finsum_mul_eq_sum_over_classes (S := hfin.toFinset) (g := fun x => h x.out) (φv := fun x => φ x.out)
    (c := fun a : Fin m → ℤ =>
      ∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))))
    (φ1 := φ 1)
    (P := fun a x => ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      (((x.out : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
    (fun x hx => hfin.mem_toFinset.mpr hx)
    (fun x a a' ⟨u, hu, k, hk, e⟩ ⟨u', hu', k', hk', e'⟩ =>
      fSatake_cell_unique hU hm hu hu' hk hk' (e.symm.trans e'))
    (fun x a ⟨u, hu, k, hk, e⟩ => fSatake_phi_cell hU hm hφ hu hk e)
    (fun x hx => fSatake_vanish hSph hU hm hm' hα hφ x.out (by
      rintro ⟨b, k, hb, hk, e⟩
      obtain ⟨a, u, hu, k', hk', e'⟩ := fSatake_cell_exists (m := m) hU hm hm' hb hk
      exact hx a ⟨u, hu, k', hk', e ▸ e'⟩))

theorem fSatake_hAct_sph {q m : ℕ} {α : Fin m → ℂ} {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n))
    {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) : IsSphericalU q α (hAct (KU σ n) h φ) := by
  intro b g k hb hk
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hr : ∀ (y κ : GU σ n), κ ∈ KU σ n → φ (y * κ) = φ y := fun y κ hκ => by
    have := hφ 1 y κ hb1 hκ
    simpa [fSatake_chiDelta_one] using this
  have hl : ∀ y : GU σ n, φ (b * y) = chiDeltaU q α b * φ y := fun y => by
    have := hφ b y 1 hb (KU σ n).one_mem
    simpa using this
  obtain ⟨hbi, -⟩ := hh
  unfold hAct
  calc ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (b * g * k * x.out)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, chiDeltaU q α b * (h x.out • φ (g * (k * x.out))) := by
        refine finsum_congr fun x => ?_
        rw [show b * g * k * x.out = b * (g * (k * x.out)) by group, hl, smul_eq_mul, smul_eq_mul]
        ring
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * (k * x.out)) :=
        (mul_finsum _ _).symm
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * x.out) := by
        congr 1
        symm
        rw [← finsum_comp_equiv (MulAction.toPerm k : (GU σ n ⧸ KU σ n) ≃ (GU σ n ⧸ KU σ n))]
        refine finsum_congr fun x => ?_
        obtain ⟨κ, hκ⟩ := out_smul (KU σ n) k x
        simp only [MulAction.toPerm_apply]
        rw [hκ]
        have e1 : h (k * x.out * κ) = h x.out := hbi ⟨k, hk⟩ κ x.out
        rw [e1, show g * (k * x.out * κ) = g * (k * x.out) * κ by group, hr _ _ κ.2]

theorem satake_transform_inert_prime (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatakeInert := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h hh φ hφ
  obtain ⟨φ0, -, -, huniq⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have h1 := huniq _ (fSatake_hAct_sph hh hφ)
  have h2 := huniq _ hφ
  have hv : hAct (KU σ n) h φ 1 = SatU ϖ q h α * φ 1 := by
    unfold hAct
    simp only [one_mul, smul_eq_mul]
    exact fSatake_key hSphericalExistsU hU hm hm' hα hh hφ
  rw [h1, hv]
  conv_rhs => rw [h2]
  funext g
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem satake_transform_multiplicative (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatMul := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h₁ hh₁ h₂ hh₂
  obtain ⟨φ0, hφ0, hφ01, -⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hSI := satake_transform_inert_prime hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hh₁' := hh₁
  have hh₂' := hh₂
  obtain ⟨hb₁, hs₁⟩ := hh₁'
  obtain ⟨hb₂, hs₂⟩ := hh₂'
  have hconv : conv (KU σ n) h₁ h₂ ∈ Hecke ℂ (KU σ n) := by
    show _ ∧ _
    exact ⟨conv_biInv _ _ _ hb₁ hb₂, conv_finDosetSupp (isCommensurated_integral_unitary_of_unramified hU n) _ _ hs₁ hs₂⟩
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hamf : φ0 ∈ AMF ℂ (⊥ : Subgroup (GU σ n)) (KU σ n)
      (1 : Representation ℂ (⊥ : Subgroup (GU σ n)) ℂ) := by
    intro γ g κ
    have hγ : (γ : GU σ n) = 1 := Subgroup.mem_bot.mp γ.2
    rw [hγ, one_mul]
    have := hφ0 1 g κ hb1 κ.2
    simpa [fSatake_chiDelta_one] using this
  have hmul := hecke_act_mul (GU σ n) ⊥ (KU σ n) ℂ ℂ 1 (isCommensurated_integral_unitary_of_unramified hU n) h₁ hh₁ h₂ hh₂ φ0 hamf
  have hs2 : IsSphericalU q α (SatU ϖ q h₂ α • φ0) := fun b g k hb hk => by
    simp only [Pi.smul_apply, smul_eq_mul, hφ0 b g k hb hk]
    ring
  rw [hSI _ hconv _ hφ0, hSI _ hh₂ _ hφ0, hSI _ hh₁ _ hs2] at hmul
  have := congrFun hmul 1
  simp only [Pi.smul_apply, smul_eq_mul, hφ01, mul_one] at this
  rw [this]

end Formalism.UG.P
end
end

section

namespace Formalism.UG.P

theorem hecke_algebra_GL_commutative : Formalism.UG.HeckeCommGL := hecke_algebra_GL_comm_of_cartan cartan_decomposition_holds

theorem satake_transform_hecke_operator_Tj : Formalism.UG.SatakeTj := satake_Tj_of_spherical_cosets exists_spherical_function Tj_double_coset_decomposition

end Formalism.UG.P
end

section

noncomputable section
namespace Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

section CsApprox

variable {F : Type} [Field F] [NumberField F]

theorem csApprox_val_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  first
  | (rw [valuedAdicCompletion_eq_valuation' v]; exact valuation_of_algebraMap v r)
  | simp [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  | (erw [valuedAdicCompletion_eq_valuation']; exact valuation_of_algebraMap v r)

theorem csApprox_local (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ s : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) s) < v.intValuation D := by
  set c := algebraMap (𝓞 F) (v.adicCompletion F) D with hcdef
  have hc : c ≠ 0 := levelaf_algebraMap_ne_zero v D hD
  have hrc : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).restrict c ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hc
  have hs : {y : v.adicCompletion F | Valued.v (y - x) < Valued.v c} ∈ nhds x := by
    refine Valued.mem_nhds.2 ⟨Units.mk0 _ hrc, fun y hy => ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0] at hy ⊢
    exact lt_of_not_ge fun h => (not_le.2 hy) ((Valuation.restrict_le_iff _).2 h)
  obtain ⟨b, hb⟩ := (denseRange_algebraMap (K := F) v).mem_nhds hs
  simp only [Set.mem_ofPred_eq] at hb
  have hcv : Valued.v c = v.intValuation D := csApprox_val_int v D
  rw [hcv] at hb
  have hb1 : v.valuation F b ≤ 1 := by
    rw [← levelaf_valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) b = (algebraMap F (v.adicCompletion F) b - x) + x := by
      ring
    rw [e]
    exact Valuation.map_add_le _ (hb.le.trans (v.intValuation_le_one D)) hx
  obtain ⟨s, hs⟩ := exists_valuation_sub_lt_of_integer v hb1
    (Units.mk0 (v.intValuation D) (v.intValuation_ne_zero D hD))
  simp only [Units.val_mk0] at hs
  refine ⟨s, ?_⟩
  have hs' : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b)
      < v.intValuation D := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub,
      levelaf_valued_algebraMap]
    exact hs
  have e2 : x - algebraMap (𝓞 F) (v.adicCompletion F) s =
      -(algebraMap F (v.adicCompletion F) b - x) +
        -(algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b) := by
    ring
  rw [e2]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [Valuation.map_neg]; exact hb
  · rw [Valuation.map_neg]; exact hs'

theorem csApprox_global (D : 𝓞 F) (hD : D ≠ 0) (a : FiniteAdeleRing (𝓞 F) F) (ha : a ∈ intAd F) :
    ∃ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  classical
  have hP := levelaf_finite_places D hD
  choose s hs using fun v : HeightOneSpectrum (𝓞 F) => csApprox_local v D hD (a v) (ha v)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hP.toFinset)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {D})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => s v)
  refine ⟨r, fun v => ?_⟩
  by_cases hv : v ∈ hP.toFinset
  · have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
    rw [← v.intValuation_eq_exp_neg_multiplicity hD] at h1
    have e1 : a v - algebraMap (𝓞 F) (v.adicCompletion F) r =
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) (s v)) +
          -(algebraMap (𝓞 F) (v.adicCompletion F) (r - s v)) := by
      rw [map_sub]; ring
    rw [e1, csApprox_val_int]
    refine Valuation.map_add_le _ (hs v).le ?_
    rw [Valuation.map_neg, csApprox_val_int]
    exact h1
  · have hv' : ¬ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by simpa using hv
    have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = 1 :=
      le_antisymm ((mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v v D)) (not_lt.1 hv')
    rw [h1]
    exact (mem_adicCompletionIntegers _ _ _).1 (sub_mem (ha v) (levelaf_int_mem_v v r))

end CsApprox

theorem integral_adele_approximation_holds : Formalism.UG.CS.IntAdApprox := by
  intro F _ _ D hD a ha
  obtain ⟨r, hle⟩ := csApprox_global D hD a ha
  set y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F D)⁻¹ *
    (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) with hy
  refine ⟨r, y, fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ *
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ∈ _
    have hne : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (levelaf_algebraMap_ne_zero v D hD)
    rw [mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀,
      ← IsScalarTower.algebraMap_apply]
    calc _ ≤ (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D))⁻¹ *
          Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := mul_le_mul_right (hle v) _
      _ = 1 := inv_mul_cancel₀ hne
  · have hD' : algebraMap (𝓞 F) F D ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
    rw [hy, IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ hD', map_one, one_mul]
    ring

end Formalism.UG.P
end
end

section

noncomputable section

open NumberField

namespace Formalism.UG.P

theorem csTrace_trace_pos {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F)
    (hb : ∀ ι : F →+* ℝ, 0 < ι b) : 0 < Algebra.trace ℚ F b := by
  have key : algebraMap ℚ ℂ (Algebra.trace ℚ F b) = ∑ σ : F →ₐ[ℚ] ℂ, σ b :=
    trace_eq_sum_embeddings ℂ
  have hre : ∀ σ : F →ₐ[ℚ] ℂ, 0 < (σ b).re := by
    intro σ
    have hr : NumberField.ComplexEmbedding.IsReal (σ : F →+* ℂ) :=
      NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    have e := hr.coe_embedding_apply b
    have e' : (σ : F →+* ℂ) b = σ b := rfl
    rw [← e', ← e, Complex.ofReal_re]
    exact hb _
  have hne : Nonempty (F →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have h2 := congrArg Complex.re key
  rw [Complex.re_sum] at h2
  have h3 : 0 < ∑ σ : F →ₐ[ℚ] ℂ, (σ b).re :=
    Finset.sum_pos (fun σ _ => hre σ) Finset.univ_nonempty
  rw [← h2] at h3
  simpa using h3

theorem csTrace_trace_algebraMap_pos {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] (b : F) (hb : ∀ ι : F →+* ℝ, 0 < ι b) :
    0 < Algebra.trace ℚ E (algebraMap F E b) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [← Algebra.trace_trace (S := F), Algebra.trace_algebraMap, map_nsmul]
  exact nsmul_pos (csTrace_trace_pos b hb) Module.finrank_pos.ne'

theorem trace_form_positive : Formalism.UG.CS.TracePos := by
  intro F E _ _ _ _ _ n _ _ σ J hJ
  obtain ⟨hF, hdef⟩ := hJ
  haveI : IsTotallyReal F := hF

  let φ0 : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  let ι0 : F →+* ℝ :=
    (NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (NumberField.InfinitePlace.mk φ0))).embedding
  have hval : ∀ x : n → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x := by
    intro x hx
    rcases hdef ι0 with h | h
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩

  have same : ∀ x y : n → E, x ≠ 0 → y ≠ 0 → ∀ a b : F,
      algebraMap F E a = hform (σ : E →+* E) J x x →
      algebraMap F E b = hform (σ : E →+* E) J y y → ∀ ι : F →+* ℝ, 0 < ι a * ι b := by
    intro x y hx hy a b ha hb ι
    rcases hdef ι with h | h
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos hap hbp
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos_of_neg_of_neg hap hbp
  by_cases hx : ∃ x0 : n → E, x0 ≠ 0
  · obtain ⟨x0, hx0⟩ := hx
    obtain ⟨a0, ha0⟩ := hval x0 hx0
    have ha0ne : a0 ≠ 0 := by
      intro h0
      have := same x0 x0 hx0 hx0 a0 a0 ha0 ha0 ι0
      rw [h0, map_zero, zero_mul] at this
      exact lt_irrefl _ this
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a0
    have hqF : algebraMap (𝓞 F) F q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (nonZeroDivisors.ne_zero hq)
    have hp : algebraMap (𝓞 F) F p = a0 * algebraMap (𝓞 F) F q := by
      rw [← hpq, div_mul_cancel₀ _ hqF]
    have hc : ((p * q : 𝓞 F) : F) = a0 * algebraMap (𝓞 F) F q * algebraMap (𝓞 F) F q := by
      have : ((p * q : 𝓞 F) : F) = algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F q := by
        rw [← map_mul]
      rw [this, hp]
    refine ⟨p * q, ?_, ?_⟩
    · intro h0
      have : ((p * q : 𝓞 F) : F) = 0 := by simp [h0]
      rw [hc] at this
      exact mul_ne_zero (mul_ne_zero ha0ne hqF) hqF this
    · intro x hx
      obtain ⟨a, ha⟩ := hval x hx
      rw [← ha, ← map_mul]
      apply csTrace_trace_algebraMap_pos
      intro ι
      have hs := same x0 x hx0 hx a0 a ha0 ha ι
      have hq2 : 0 < ι (algebraMap (𝓞 F) F q) * ι (algebraMap (𝓞 F) F q) :=
        mul_self_pos.mpr ((map_ne_zero_iff _ ι.injective).mpr hqF)
      rw [hc, map_mul, map_mul, map_mul]
      nlinarith [mul_pos hs hq2]
  · push_neg at hx
    refine ⟨1, one_ne_zero, fun x hx' => absurd (hx x) hx'⟩

end Formalism.UG.P
end
end
