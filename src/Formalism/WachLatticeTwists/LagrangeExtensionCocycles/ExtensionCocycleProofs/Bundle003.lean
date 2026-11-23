module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Bundle001
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SecondDescentFreePartHolds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

theorem lift_to_subgroup_exists : StatLiftSub := by
  unfold StatLiftSub
  intro ℓ _ H₁ H₂ H₁' H₂' _ _ _ _ _ _ _ _ Hf₁ Hf₂ Hf₁' Hf₂' h h' res₂ cor₁ cor₂ g E hg hcr hcomm hres hcor hlift κ' hκ'
  obtain ⟨κ₁, hκ₁, he⟩ := hlift (res₂ κ') (hres κ' hκ')
  set v := padicValNat ℓ g with hv
  obtain ⟨m, hm⟩ : ℓ ^ v ∣ g := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hcop : ¬ ℓ ∣ m := by
    intro hdvd
    have h5 : ℓ ^ (v + 1) ∣ g := by
      rw [hm, pow_succ]
      exact mul_dvd_mul_left _ hdvd
    exact pow_succ_multiplicity_not_dvd (p := ℓ) (n := g) (Nat.ne_of_gt hg) (by simpa [hv, Nat.padicValNat_def] using h5)
  have hu : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖((m : ℤ) : ℤ_[ℓ])‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : ¬ ‖((m : ℤ) : ℤ_[ℓ])‖ < 1 := by
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      exact_mod_cast hcop
    have h3 : ((m : ℤ) : ℤ_[ℓ]) = (m : ℤ_[ℓ]) := Int.cast_natCast m
    rw [← h3]
    exact le_antisymm h1 (not_lt.1 h2)
  refine ⟨(↑hu.unit⁻¹ : ℤ_[ℓ]) • cor₁ κ₁, Hf₁'.smul_mem _ (hcor κ₁ hκ₁), ?_⟩
  rw [map_smul, hcomm, he, map_smul, hcr, smul_smul, smul_smul]
  congr 1
  have hg' : (g : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ v * (m : ℤ_[ℓ]) := by
    rw [hm]
    push_cast
    ring
  have hum : (↑hu.unit⁻¹ : ℤ_[ℓ]) * (m : ℤ_[ℓ]) = 1 := hu.val_inv_mul
  rw [hg', pow_add]
  linear_combination (ℓ : ℤ_[ℓ]) ^ E * (ℓ : ℤ_[ℓ]) ^ v * hum

theorem regulator_bound_for_x : StatRegX := by
  unfold StatRegX
  intro ℓ _ A _ _ B M D _ _ _ _ W hreg y hy hX
  unfold RegXQ at hreg
  have hy' : B.Q ^ M • y ∈ W.N := hy
  have key : ∀ z : D, B.Q • z ∈ W.N → B.X • z ∈ W.N → z ∈ W.N := by
    intro z hQ hXz
    obtain ⟨m', hm', he⟩ := hreg (B.X • z) hXz ⟨B.Q • z, hQ, by rw [smul_smul, smul_smul, mul_comm]⟩
    have h0 : B.X • (z - m') = 0 := by rw [smul_sub, he, sub_self]
    have hz : z - m' = 0 := W.X_inj _ h0
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hm'
  suffices h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply key
    · rw [smul_smul, ← pow_succ']
      exact h
    · rw [smul_comm]
      exact W.N.smul_mem _ hX

theorem regulator_bound_for_l : StatRegL := by
  unfold StatRegL
  intro ℓ _ A _ _ B M D _ _ _ _ W hreg htor y hy hX
  unfold RegLQ at hreg
  unfold NoTors at htor
  have hy' : B.Q ^ M • y ∈ W.N := hy
  have key : ∀ z : D, B.Q • z ∈ W.N → (ℓ : ℤ_[ℓ]) • z ∈ W.N → z ∈ W.N := by
    intro z hQ hXz
    obtain ⟨m', hm', he⟩ := hreg ((ℓ : ℤ_[ℓ]) • z) hXz ⟨B.Q • z, hQ, smul_comm _ _ _⟩
    have h0 : (ℓ : ℤ_[ℓ]) • (z - m') = 0 := by rw [smul_sub, he, sub_self]
    have hz : z - m' = 0 := htor _ h0
    rw [sub_eq_zero] at hz
    rw [hz]
    exact hm'
  suffices h : ∀ j : ℕ, B.Q ^ j • y ∈ W.N → y ∈ W.N from h M hy'
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    apply key
    · rw [smul_smul, ← pow_succ']
      exact h
    · rw [smul_comm]
      exact W.N.smul_mem _ hX

theorem extension_class_is_cocycle : StatExtCocycle := by
  unfold StatExtCocycle
  intro ℓ _ A _ _ B M D _ _ _ _ W H _ _ cl κ E e hD hlift
  obtain ⟨x, hxN, hx⟩ := hlift E.e E.e_mem
  have hπφ : E.S.π.f (E.Wp.φ x - x) = 0 := by
    rw [map_sub, E.S.π.φ_comm, hx, map_smul, E.φe, sub_self]
  have hπγ : E.S.π.f (E.Wp.γ x - x) = 0 := by
    rw [map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]
  obtain ⟨y, hy⟩ := (E.S.exact _).1 hπφ
  obtain ⟨z, hz⟩ := (E.S.exact _).1 hπγ
  have hd : (W.γ y - y) - (W.φ z - z) = 0 := by
    apply E.S.ι_inj
    simp only [map_sub, map_zero, E.S.ι.γ_comm, E.S.ι.φ_comm, hy, hz, E.Wp.comm]
    abel
  have hZ : ((y, z) : D × D) ∈ W.Z1 := by
    show ((y, z) : D × D) ∈ LinearMap.ker ((W.γ - LinearMap.id).coprod (-(W.φ - LinearMap.id)))
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.neg_apply]
    calc _ = (W.γ y - y) - (W.φ z - z) := by abel
      _ = 0 := hd
  have hQ : B.Q ^ M • y ∈ W.N := by
    apply E.S.sat
    rw [map_smul, hy, smul_sub]
    exact E.Wp.N.sub_mem (E.Wp.φ_N x hxN) (E.Wp.N.smul_mem _ hxN)
  obtain ⟨x', hx'N, hx'⟩ := E.Wp.γ_N x hxN
  have hπx' : E.S.π.f x' = 0 := by
    apply E.Wt.X_inj
    rw [← map_smul, ← hx', map_sub, E.S.π.γ_comm, hx, map_smul, E.γe, sub_self]
  obtain ⟨x₀, hx₀⟩ := (E.S.exact x').1 hπx'
  have hx₀N : x₀ ∈ W.N := E.S.sat x₀ (by rw [hx₀]; exact hx'N)
  have hzX : z = B.X • x₀ := by
    apply E.S.ι_inj
    rw [map_smul, hx₀, hz, hx']
  refine ⟨⟨(y, z), hZ⟩, ?_, ?_⟩
  · unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1
    exact ⟨⟨hQ, x₀, hx₀N, hzX⟩, hd⟩
  · exact hD ((ℓ : ℤ_[ℓ]) ^ e) x ⟨(y, z), hZ⟩ hx hy hz

theorem rational_points_map_surjective : StatRatSurj := by
  unfold StatRatSurj
  intro ℓ _ A _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g e₁ hp hnat hcoc hherr honto hlift
  unfold Formalism.CoboundaryTransfers.RatSurj
  intro y z hyz
  have memZ : ∀ a b : D₂, W₂.γ a - a - (W₂.φ b - b) = 0 → ((a, b) : D₂ × D₂) ∈ W₂.Z1 := by
    intro a b h
    show ((a, b) : D₂ × D₂) ∈ LinearMap.ker ((W₂.γ - LinearMap.id).coprod (-(W₂.φ - LinearMap.id)))
    simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.neg_apply]
    calc _ = W₂.γ a - a - (W₂.φ b - b) := by abel
      _ = 0 := h
  have hyz' := hyz
  unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hyz'
  obtain ⟨⟨hQ₂, n₂, hn₂, hz₂⟩, hd₂⟩ := hyz'
  have hκ : cl₂ ⟨(y, z), memZ y z hd₂⟩ ∈ Hf₂ := hcoc _ hyz
  obtain ⟨k, κ₁, hκ₁, hgk⟩ := honto _ hκ
  obtain ⟨⟨⟨y₁, z₁⟩, hZ₁⟩, hpr₁c, hpr₁⟩ := hlift κ₁ hκ₁
  have hc₁ := hpr₁c
  unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1 at hc₁
  obtain ⟨⟨hQ₁', n₁, hn₁, hz₁'⟩, hd₁'r⟩ := hc₁
  have hz₁ : z₁ = B.X • n₁ := hz₁'
  have hd₁ : W₁.γ y₁ - y₁ - (W₁.φ z₁ - z₁) = 0 := hd₁'r
  have hQ₁ : B.Q ^ M • y₁ ∈ W₁.N := hQ₁'
  have hd₁' : W₂.γ (S.π.f y₁) - S.π.f y₁ - (W₂.φ (S.π.f z₁) - S.π.f z₁) = 0 := by
    have h := congrArg S.π.f hd₁
    simpa [map_sub, S.π.γ_comm, S.π.φ_comm] using h
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[ℓ], c = (ℓ : ℤ_[ℓ]) ^ (e₁ + k) := ⟨_, rfl⟩
  have hcP : W₂.Cocycle (S.π.f y₁ - c • y) (S.π.f z₁ - c • z) := by
    unfold WachMod.Cocycle WachMod.C1 WachMod.QInv WachMod.XN WachMod.d1
    refine ⟨⟨?_, S.π.f n₁ - c • n₂, W₂.N.sub_mem (S.π.N_le _ hn₁) (W₂.N.smul_of_tower_mem c hn₂), ?_⟩, ?_⟩
    · rw [smul_sub, ← map_smul, smul_comm (B.Q ^ M) c y]
      exact W₂.N.sub_mem (S.π.N_le _ hQ₁) (W₂.N.smul_of_tower_mem c hQ₂)
    · rw [hz₁, hz₂, map_smul, smul_sub, smul_comm c B.X n₂]
    · calc W₂.γ (S.π.f y₁ - c • y) - (S.π.f y₁ - c • y) - (W₂.φ (S.π.f z₁ - c • z) - (S.π.f z₁ - c • z))
          = (W₂.γ (S.π.f y₁) - S.π.f y₁ - (W₂.φ (S.π.f z₁) - S.π.f z₁)) -
              c • (W₂.γ y - y - (W₂.φ z - z)) := by
            rw [map_sub, map_sub, map_smul, map_smul]
            simp only [smul_sub]
            abel
        _ = 0 := by rw [hd₁', hd₂, smul_zero, sub_zero]
  have hcl : cl₂ (⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩ - c • ⟨(y, z), memZ y z hd₂⟩) = 0 := by
    rw [map_sub, map_smul, ← hnat ⟨(y₁, z₁), hZ₁⟩ ⟨(S.π.f y₁, S.π.f z₁), memZ _ _ hd₁'⟩
      (by first | rfl | simp [Formalism.CoboundaryTransfers.Hom.f2]), hpr₁, map_smul, hgk, hc, pow_add, mul_smul, sub_self]
  have hcob := hherr _ hcP hcl
  unfold WachMod.IsCob1 at hcob
  obtain ⟨x, hxN, hx1, hx2⟩ := hcob
  change S.π.f y₁ - c • y = W₂.φ x - x at hx1
  change S.π.f z₁ - c • z = W₂.γ x - x at hx2
  refine ⟨e₁ + k, y₁, z₁, hpr₁c, x, hxN, ?_, ?_⟩
  · rw [hp, ← hc, ← hx1]
    abel
  · rw [hp, ← hc, ← hx2]
    abel

end Formalism.RepresentationBoundsCohomology.N2
end
end

section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem cost_formula_holds : StatCostFormula := by
  intro ℓ _ hℓ2 j s hjs
  have hℓ : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hd : 0 < ℓ - 1 := by omega
  induction s, hjs using Nat.le_induction with
  | base => simp [cost]
  | succ s hjs ih =>
    have hI : Finset.Ioc j (s + 1) = insert (s + 1) (Finset.Ioc j s) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hnot : s + 1 ∉ Finset.Ioc j s := by simp
    have hc : cost ℓ j (s + 1) =
        cost ℓ j s + (if (ℓ - 1) ∣ (s + 1) then 1 + padicValNat ℓ (s + 1) else 0) := by
      unfold cost
      rw [hI, Finset.sum_insert hnot, add_comm]
    rw [hc]
    by_cases hdv : (ℓ - 1) ∣ (s + 1)
    · rw [if_pos hdv]
      have hq : (s + 1) / (ℓ - 1) = s / (ℓ - 1) + 1 := Nat.succ_div_of_dvd hdv
      have hjq : j / (ℓ - 1) ≤ s / (ℓ - 1) := Nat.div_le_div_right hjs
      have hmul : s + 1 = (ℓ - 1) * (s / (ℓ - 1) + 1) := by
        rw [← hq]
        exact (Nat.mul_div_cancel' hdv).symm
      have hv0 : padicValNat ℓ (ℓ - 1) = 0 := by
        rw [Nat.padicValNat_def]
        exact padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd hd h; omega)
      have hv : padicValNat ℓ (s + 1) = padicValNat ℓ (s / (ℓ - 1) + 1) := by
        rw [hmul, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.pos_iff_ne_zero.1 hd) (Nat.succ_ne_zero _), hv0, zero_add]
      have hf : padicValNat ℓ (s / (ℓ - 1) + 1).factorial =
          padicValNat ℓ (s / (ℓ - 1) + 1) + padicValNat ℓ (s / (ℓ - 1)).factorial := by
        rw [Nat.factorial_succ, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
      rw [hq, hv, hf]
      omega
    · rw [if_neg hdv, add_zero, Nat.succ_div_of_not_dvd hdv]
      exact ih

theorem cost_bound : StatCostBound := by
  intro ℓ _ hℓ j s H hjs hsH
  have hprime : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by have := hprime.two_le; omega
  have hform := cost_formula_holds ℓ hℓ j s hjs
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hform
  have hL2 : 2 ≤ L := by omega
  set k0 := j / L with hk0
  set k1 := s / L with hk1
  have hk01 : k0 ≤ k1 := Nat.div_le_div_right hjs
  obtain ⟨n', hn'⟩ : ∃ n', k1 = k0 + n' := ⟨k1 - k0, by omega⟩
  have hch := Nat.choose_mul_factorial_mul_factorial hk01
  have hvch : padicValNat (L + 1) k1.factorial = padicValNat (L + 1) (k1.choose k0) +
      padicValNat (L + 1) k0.factorial + padicValNat (L + 1) n'.factorial := by
    rw [← hch, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.mul_ne_zero (Nat.choose_pos hk01).ne' (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _), (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.choose_pos hk01).ne' (Nat.factorial_ne_zero _),
      show k1 - k0 = n' by omega]
  have hcost : cost (L + 1) j s = n' + padicValNat (L + 1) n'.factorial +
      padicValNat (L + 1) (k1.choose k0) := by omega
  have hLr : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
  have hsub : (((L + 1 : ℕ) : ℝ) - 1) = L := by push_cast; ring
  have hb1 : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hHr : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) := Real.logb_nonneg hb1 (by linarith)
  have hjsr : (j : ℝ) ≤ s := by exact_mod_cast hjs
  rw [hsub]
  have hpos : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos n' with h0 | hpos'
  · have : cost (L + 1) j s = 0 := by
      rw [hcost, h0, hn', h0]; simp [Nat.padicValNat_def]
    rw [this]
    have : 0 ≤ ((s : ℝ) - j) * ((L + 1 : ℕ) : ℝ) / (L : ℝ) ^ 2 := by
      apply div_nonneg _ hpos.le
      apply mul_nonneg (by linarith) (by linarith)
    push_cast at this hlog0 ⊢
    linarith
  ·
    have hw : L * padicValNat (L + 1) n'.factorial < n' := by
      have := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := L + 1) (n := n') hpos'.ne'
      simpa [Nat.padicValNat_def] using this
    have hc : padicValNat (L + 1) (k1.choose k0) ≤ Nat.log (L + 1) k1 := by
      rw [Nat.padicValNat_def, ← Nat.factorization_def _ hprime]
      exact Nat.factorization_choose_le_log
    have hk1pos : 1 ≤ k1 := by
      rw [hn']; exact le_trans hpos' (Nat.le_add_left _ _)
    have hk1H : k1 ≤ H := le_trans (Nat.div_le_self _ _) hsH
    have hlog : (Nat.log (L + 1) k1 : ℝ) ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) := by
      refine le_trans (Real.natLog_le_logb _ _) ?_
      apply Real.logb_le_logb_of_le hb1
      · exact_mod_cast hk1pos
      · have : (k1 : ℝ) ≤ H := by exact_mod_cast hk1H
        linarith
    have h1 : L * k1 ≤ s := Nat.mul_div_le s L
    have h2 : j < L * k0 + L := by
      have := Nat.lt_mul_div_succ j (show 0 < L by omega)
      rw [← hk0] at this
      nlinarith
    have hA : L * n' + j + 1 ≤ s + L := by
      have : L * k1 = L * k0 + L * n' := by rw [hn']; ring
      omega
    set w := padicValNat (L + 1) n'.factorial with hwdef
    set c := padicValNat (L + 1) (k1.choose k0) with hcdef
    have rA : (L : ℝ) * n' + j + 1 ≤ s + L := by exact_mod_cast hA
    have rB : (L : ℝ) * w + 1 ≤ n' := by exact_mod_cast hw
    have rC : (c : ℝ) ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) :=
      le_trans (by exact_mod_cast hc) hlog
    have key : ((n' : ℝ) + w) < ((s : ℝ) - j) * ((L + 1 : ℕ) : ℝ) / (L : ℝ) ^ 2 + 1 := by
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ hpos]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left rA (by linarith : (0 : ℝ) ≤ L),
        mul_le_mul_of_nonneg_left rB (by linarith : (0 : ℝ) ≤ L)]
    rw [hcost]
    push_cast at key rC ⊢
    linarith

theorem unconditional_first_statement : Stat1 := first_descent_of_cost_bound cost_bound

theorem unit_lemma_case_a_unconditional : StatWA := wA_of unconditional_first_statement

end Formalism.RepresentationBoundsCohomology.N2
end
end
