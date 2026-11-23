module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Bundle001
public import Formalism.CoboundaryTransfers.GammaStableTransfers.Bundle001
public import Formalism.CoboundaryTransfers.GammaStableTransfers.Transfer
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.Bundle003
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.MemSpanOfFrobeniusMemSpan
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.PhiOnto
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

section

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℤ_[ℓ] A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A D']

def gbase (B : Base ℤ_[ℓ] A) (u : ℤ_[ℓ]ˣ) (h : B.GammaX (u : ℤ_[ℓ])) : GBase ℓ A :=
  { γ := B.γ, X := B.X, u := u, γX := h }

def pairOfHom {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) : GPair (gbase B u h) D' :=
  { N := W'.N
    N' := W.N.map F.f
    le := by rintro _ ⟨x, hx, rfl⟩; exact F.N_le x hx
    γ := W'.γ
    γ_smul := W'.γ_smul
    X_inj := W'.X_inj
    γ_N := W'.γ_N
    γ_N' := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨x', hx', h⟩ := W.γ_N x hx
      exact ⟨F.f x', ⟨x', hx', rfl⟩, by rw [← F.γ_comm, ← map_sub, h, map_smul]; rfl⟩ }

theorem kills_iff {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) (a : A) :
    (pairOfHom F u h).Kills a ↔ ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = a • n := by
  constructor
  · intro hk n hn
    obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.1 (hk n hn)
    exact ⟨x, hx, hfx⟩
  · intro h' n hn
    obtain ⟨x, hx, hfx⟩ := h' n hn
    exact Submodule.mem_map.2 ⟨x, hx, hfx⟩

theorem natCast_pow_smul (e : ℕ) (n : D) : ((ℓ : A) ^ e) • n = ((ℓ : ℤ_[ℓ]) ^ e) • n := by
  rw [← map_natCast (algebraMap ℤ_[ℓ] A), ← map_pow, algebraMap_smul]

theorem homKillsB {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) (s a : ℕ) (hs : 1 ≤ s) (h2 : ℓ = 2 → 2 ≤ s)
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s) (hK : XKills F a) :
    ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = ((ℓ : ℤ_[ℓ]) ^ eWB ℓ a s) • n := by
  have := unit_lemma_case_b_holds ℓ A (gbase B u h) D' (pairOfHom F u h) s a hs h2 hv ((kills_iff F u h _).2 hK)
  intro n hn
  obtain ⟨n₁, hn₁, e⟩ := (kills_iff F u h _).1 this n hn
  exact ⟨n₁, hn₁, by rw [e, natCast_pow_smul]⟩

theorem aeval_mem (N : Submodule ℤ_[ℓ] D) (γ : D →ₗ[ℤ_[ℓ]] D) (h : ∀ n ∈ N, γ n ∈ N)
    (R : ℤ_[ℓ][X]) : ∀ n ∈ N, aeval γ R n ∈ N := by
  induction R using Polynomial.induction_on with
  | C a =>
    intro n hn
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact N.smul_mem a hn
  | add p q hp hq =>
    intro n hn
    rw [map_add (f := _), LinearMap.add_apply]
    exact N.add_mem (hp n hn) (hq n hn)
  | monomial k a ih =>
    intro n hn
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (h n hn)

theorem zero_notMem_JSet (jumps : Finset ℤ) (M : ℕ) : (0 : ℤ) ∉ JSet jumps M := by
  simp [JSet]

theorem eigSet_subset (jumps : Finset ℤ) (M : ℕ) : eigSet jumps M ⊆ insert 0 (JSet jumps M) := by
  intro x hx
  by_cases h0 : x = 0
  · exact Finset.mem_insert.2 (Or.inl h0)
  · exact Finset.mem_insert.2 (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_erase.2 ⟨h0, hx⟩))))

theorem prod_eig_dvd (jumps : Finset ℤ) (M : ℕ) (f : ℤ → ℤ_[ℓ][X]) :
    (∏ j ∈ eigSet jumps M, f j) ∣ f 0 * ∏ j ∈ JSet jumps M, f j := by
  have h := Finset.prod_dvd_prod_of_subset _ _ f (eigSet_subset jumps M)
  rwa [Finset.prod_insert (zero_notMem_JSet jumps M)] at h

end

theorem lift_exists_second_case : StatLiftB := by
  intro ℓ _ A _ _ B M u s H jumps hp hφX hγX hγQ hs h2 hv D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S
    H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g I _ hQI hφI hRX hRL hNT hXK hSemi hNat hC1 hC2 hInj hE1 hE2 hRO
  set eW := eWB ℓ H s with heW

  have hCK : CokerKilled S eW := by
    intro n hn
    rw [hp]
    exact homKillsB S.π u hγX s H hs h2 hv hXK n hn

  have hInt₁ : ∀ κ ∈ Hf₁, ∃ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 ∧
      cl₁ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE1 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₁ W₁ H₁ cl₁ κ E eW hED (homKillsB E.S.π u hγX s H hs h2 hv hEK)
  have hInt₂ : ∀ κ ∈ Hf₂, ∃ pr : W₂.Z1, W₂.Cocycle (pr : D₂ × D₂).1 (pr : D₂ × D₂).2 ∧
      cl₂ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE2 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₂ W₂ H₂ cl₂ κ E eW hED (homKillsB E.S.π u hγX s H hs h2 hv hEK)

  have hRS : RatSurj S :=
    rational_points_map_surjective ℓ A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW hp hNat hC2 hInj hRO hInt₁

  have h1 := phi_map_surjective ℤ_[ℓ] A B M D₀ W₀ I 1 (M + 1) ⟨1, by rw [hφX]; ring⟩ (by omega) hQI hφI

  have hstab : ∀ n ∈ W₀.N.restrictScalars ℤ_[ℓ], W₀.γ n ∈ W₀.N.restrictScalars ℤ_[ℓ] := by
    intro n hn
    obtain ⟨x', hx', h⟩ := W₀.γ_N n hn
    have : W₀.γ n = n + B.X • x' := by rw [← h]; abel
    rw [this]
    exact W₀.N.add_mem hn (W₀.N.smul_mem _ hx')
  have h3 : ∀ y, W₀.QInv y → aeval W₀.γ ((X - 1) *
      ∏ j ∈ JSet jumps M, (X - C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W₀.N := by
    intro y hy
    obtain ⟨R, hR⟩ := prod_eig_dvd jumps M (fun j => (X - C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))))
    have e0 : (X - C (((u ^ (-(0 : ℤ)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) : ℤ_[ℓ][X]) = X - 1 := by simp
    simp only [e0] at hR
    rw [hR, mul_comm, map_mul, Module.End.mul_apply]
    exact aeval_mem _ W₀.γ hstab R _ (hSemi y hy)
  have hL : Lifts S ((ℓ : ℤ_[ℓ]) ^ (eW + Formalism.LIFT.eU ℓ M s (JSet jumps M))) :=
    wachLatticeUnramified_statement ℓ A B M u hp hφX hγX hγQ D₀ D₁ D₂ W₀ W₁ W₂ S eW s (JSet jumps M) hs h2 hv
      (zero_notMem_JSet jumps M) h1 (regulator_bound_for_x ℓ A B M D₀ W₀ hRX) h3
      (regulator_bound_for_l ℓ A B M D₀ W₀ hRL hNT) hCK hRS
  intro κ hκ
  obtain ⟨κ₁, hκ₁, h⟩ := finiteClassesLift_holds ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW _
    hNat hC1 ⟨hC2, by rw [hp]; exact hInt₂⟩ hL κ hκ
  refine ⟨κ₁, hκ₁, ?_⟩
  rw [h, hp, ← pow_add]
  congr 2
  simp only [eUB, Formalism.LIFT.eU]
  ring

end Formalism.RepresentationBoundsCohomology.N2
end
end

section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial

theorem aH_le_eWA (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (H : ℕ) :
    (H + (ℓ - 2)) / (ℓ - 1) + padicValNat ℓ ((H + (ℓ - 2)) / (ℓ - 1)).factorial ≤ eWA ℓ H := by
  set a := (H + (ℓ - 2)) / (ℓ - 1) with ha
  have hp := (Fact.out : ℓ.Prime)
  have hℓ3 : 3 ≤ ℓ := by have := hp.two_le; omega
  have hv : (ℓ - 1) * padicValNat ℓ a.factorial ≤ a := by
    rw [Nat.padicValNat_def, hp.sub_one_mul_multiplicity_factorial]
    exact Nat.sub_le _ _
  have haH : (ℓ - 1) * a ≤ H + (ℓ - 2) := Nat.mul_div_le (H + (ℓ - 2)) (ℓ - 1)
  have hcast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hcast2 : ((ℓ - 2 : ℕ) : ℝ) = (ℓ : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hvR : ((ℓ : ℝ) - 1) * (padicValNat ℓ a.factorial : ℝ) ≤ a := by
    rw [← hcast]; exact_mod_cast hv
  have haR : ((ℓ : ℝ) - 1) * (a : ℝ) ≤ (H : ℝ) + ((ℓ : ℝ) - 1) - 1 := by
    have h0 : ((ℓ - 1 : ℕ) : ℝ) * (a : ℝ) ≤ (H : ℝ) + ((ℓ - 2 : ℕ) : ℝ) := by exact_mod_cast haH
    rw [hcast, hcast2] at h0
    linarith
  have hL : (0 : ℝ) < (ℓ : ℝ) - 1 := by
    have : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ3
    linarith
  have hlog : 0 ≤ Real.logb ℓ ((H : ℝ) + 1) :=
    Real.logb_nonneg (by exact_mod_cast hp.one_lt) (by linarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)])
  have key : ((ℓ : ℝ) - 1) ^ 2 * ((a : ℝ) + (padicValNat ℓ a.factorial : ℝ)) ≤
      (H : ℝ) * ℓ + ((ℓ : ℝ) - 1) ^ 2 - 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hvR hL.le, mul_le_mul_of_nonneg_left haR (by linarith : (0 : ℝ) ≤ ℓ)]
  have hL2 : 0 < ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have h1 : (a : ℝ) + (padicValNat ℓ a.factorial : ℝ) ≤
      ((H : ℝ) * ℓ + ((ℓ : ℝ) - 1) ^ 2 - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [le_div_iff₀ hL2]; linarith [key]
  have h2 : ((H : ℝ) * ℓ + ((ℓ : ℝ) - 1) ^ 2 - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ (H : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by
    rw [div_le_iff₀ hL2, add_mul, div_mul_cancel₀ _ hL2.ne']
    linarith
  unfold eWA
  apply Nat.le_floor
  push_cast
  linarith

theorem prod_sub_one_dvd (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (u : ℤ_[ℓ]ˣ)
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1) (a : ℕ) :
    (∏ i ∈ Finset.Icc 1 a, (1 - (u : ℤ_[ℓ]) ^ i)) ∣ (ℓ : ℤ_[ℓ]) ^ (a + padicValNat ℓ a.factorial) := by
  have hπ : Prime (ℓ : ℤ_[ℓ]) := PadicInt.prime_p
  have hp := (Fact.out : ℓ.Prime)
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ
  have hnd_unit : ∀ w : ℤ_[ℓ], IsUnit w → ¬ (ℓ : ℤ_[ℓ]) ∣ w := fun w hw hd =>
    hπ.not_unit (isUnit_of_dvd_unit hd hw)
  have hunit_of : ∀ w : ℤ_[ℓ], ¬ (ℓ : ℤ_[ℓ]) ∣ w → IsUnit w := by
    intro w hw
    by_contra hnu
    apply hw
    have hm : w ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] := (IsLocalRing.mem_maximalIdeal w).2 (mem_nonunits_iff.2 hnu)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
    exact hm
  have hne : (u : ℤ_[ℓ]) - 1 ≠ 0 := by
    intro h0
    rw [h0, PadicInt.valuation_zero] at hv
    exact absurd hv (by norm_num)
  have hspec := PadicInt.unitCoeff_spec hne
  rw [hv, pow_one] at hspec
  have hdiv1 : (ℓ : ℤ_[ℓ]) ∣ (u : ℤ_[ℓ]) - 1 := by
    rw [hspec]
    exact dvd_mul_left _ _
  have hA : emultiplicity (ℓ : ℤ_[ℓ]) ((u : ℤ_[ℓ]) - 1) = ((1 : ℕ) : ℕ∞) := by
    rw [emultiplicity_eq_coe]
    refine ⟨by rw [pow_one]; exact hdiv1, fun h2 => ?_⟩
    rw [hspec, pow_succ, pow_one] at h2
    exact hnd_unit _ (Units.isUnit _) ((mul_dvd_mul_iff_right hπ.ne_zero).1 h2)
  have hnu : ¬ (ℓ : ℤ_[ℓ]) ∣ (u : ℤ_[ℓ]) := hnd_unit _ u.isUnit
  have hnat : ∀ m : ℕ, ¬ ℓ ∣ m → ¬ (ℓ : ℤ_[ℓ]) ∣ (m : ℤ_[ℓ]) := by
    intro m hm hd
    have hcop : Nat.Coprime ℓ m := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm)
    have hg : Int.gcd (ℓ : ℤ) (m : ℤ) = 1 := by
      have := Int.gcd_natCast_natCast ℓ m
      rw [this]
      exact hcop
    have hz : (1 : ℤ) = ℓ * Int.gcdA ℓ m + m * Int.gcdB ℓ m := by
      rw [← Int.gcd_eq_gcd_ab, hg]
      rfl
    have h1 := congrArg (Int.cast : ℤ → ℤ_[ℓ]) hz
    push_cast at h1
    apply hπ.not_unit
    apply isUnit_of_dvd_one
    rw [h1]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hd _)
  have hB : ∀ i : ℕ, 1 ≤ i → emultiplicity (ℓ : ℤ_[ℓ]) ((u : ℤ_[ℓ]) ^ i - 1) = ((1 + padicValNat ℓ i : ℕ) : ℕ∞) := by
    intro i hi
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := i) (by omega) ℓ hp.ne_one
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm (dvd_zero ℓ)
    have hval : padicValNat ℓ i = k := by
      rw [hkm, Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hp.ne_zero) hm0,
        Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
    have hdivk : (ℓ : ℤ_[ℓ]) ∣ (u : ℤ_[ℓ]) ^ (ℓ ^ k) - 1 := by
      have := sub_dvd_pow_sub_pow (u : ℤ_[ℓ]) 1 (ℓ ^ k)
      rw [one_pow] at this
      exact dvd_trans hdiv1 this
    have hnuk : ¬ (ℓ : ℤ_[ℓ]) ∣ (u : ℤ_[ℓ]) ^ (ℓ ^ k) := hnd_unit _ (u.isUnit.pow _)
    have e1 := emultiplicity_pow_sub_pow_of_prime hπ (x := (u : ℤ_[ℓ]) ^ (ℓ ^ k)) (y := 1) (by simpa using hdivk)
      hnuk (n := m) (hnat m hm)
    have e2 := emultiplicity_pow_prime_pow_sub_pow_prime_pow (y := (1 : ℤ_[ℓ])) (by simpa using hπ) hodd
      (by simpa using hdiv1) hnu k
    have e3 : (u : ℤ_[ℓ]) ^ i - 1 = ((u : ℤ_[ℓ]) ^ (ℓ ^ k)) ^ m - 1 ^ m := by
      rw [hkm, pow_mul, one_pow]
    rw [one_pow] at e2
    rw [hval, e3, e1, e2, hA]
    norm_cast
  have hF : ∀ i : ℕ, 1 ≤ i → (1 - (u : ℤ_[ℓ]) ^ i) ∣ (ℓ : ℤ_[ℓ]) ^ (1 + padicValNat ℓ i) := by
    intro i hi
    have hE : emultiplicity (ℓ : ℤ_[ℓ]) (1 - (u : ℤ_[ℓ]) ^ i) = ((1 + padicValNat ℓ i : ℕ) : ℕ∞) := by
      rw [← neg_sub, emultiplicity_neg, hB i hi]
    obtain ⟨hd, hnd⟩ := (emultiplicity_eq_coe.1 hE)
    obtain ⟨w, hw⟩ := hd
    have hwu : IsUnit w := by
      apply hunit_of
      rintro ⟨c, rfl⟩
      apply hnd
      rw [hw, pow_succ]
      exact mul_dvd_mul_left _ (dvd_mul_right _ _)
    refine ⟨(hwu.unit⁻¹ : ℤ_[ℓ]ˣ), ?_⟩
    rw [hw, mul_assoc, IsUnit.mul_val_inv, mul_one]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) (Nat.factorial_ne_zero a)]
    have e : a + 1 + (padicValNat ℓ (a + 1) + padicValNat ℓ a.factorial) =
        (a + padicValNat ℓ a.factorial) + (1 + padicValNat ℓ (a + 1)) := by ring
    rw [e, pow_add (ℓ : ℤ_[ℓ]) (a + padicValNat ℓ a.factorial) (1 + padicValNat ℓ (a + 1))]
    exact mul_dvd_mul ih (hF (a + 1) (by omega))

theorem unit_lemma_case_a_level_zero : StatWA0 := by
  intro ℓ _ hℓ A _ _ G D _ _ _ _ P H hv hK
  set a := (H + (ℓ - 2)) / (ℓ - 1) with ha
  have h1 := mem_span_of_frobenius_mem_span ℓ A G D P a 0 (Nat.zero_le _) hK
  have hdvd : (∏ k ∈ Finset.Ioc 0 a, ((G.u : ℤ_[ℓ]) ^ k - 1)) ∣
      (ℓ : ℤ_[ℓ]) ^ (a + padicValNat ℓ a.factorial) := by
    have h2 := prod_sub_one_dvd ℓ hℓ G.u hv a
    have e : ∏ k ∈ Finset.Ioc 0 a, ((G.u : ℤ_[ℓ]) ^ k - 1) =
        (-1) ^ a * ∏ i ∈ Finset.Icc 1 a, (1 - (G.u : ℤ_[ℓ]) ^ i) := by
      have hI : Finset.Ioc 0 a = Finset.Icc 1 a := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hI]
      have hneg : ∀ i ∈ Finset.Icc 1 a, ((G.u : ℤ_[ℓ]) ^ i - 1) = -(1 - (G.u : ℤ_[ℓ]) ^ i) :=
        fun i _ => by ring
      rw [Finset.prod_congr rfl hneg, Finset.prod_neg, Nat.card_Icc, Nat.add_sub_cancel]
    rw [e]
    exact (isUnit_neg_one.pow a).mul_left_dvd.2 h2
  have h3 := P.kills_pow_of_dvd hdvd h1
  simp only [pow_zero, mul_one] at h3
  exact ⟨h3, P.kills_of_dvd (pow_dvd_pow _ (aH_le_eWA ℓ hℓ H)) h3⟩

end Formalism.RepresentationBoundsCohomology.N2
end
end
