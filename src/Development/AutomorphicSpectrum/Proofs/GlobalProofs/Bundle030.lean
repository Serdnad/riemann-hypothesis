module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle028
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle022
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle017

@[expose] public section

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem series_value_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (N p : ℕ), Fintype.card ι * p < N →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∃ q : ℚ, ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) := by
  intro ι _ r a b u cs N p hN hcase hval
  by_cases hex : ∃ i, cs.count i = N
  · obtain ⟨i, hi⟩ := hex
    refine ⟨0, ?_⟩
    have h0 := GlobalTheory.T.high_difference_vanishes_negative_integer ι r a b cs i N p hi hN
    simp [h0]
  · have hsupp : ∀ m : Fin r → ℕ, m ≠ 0 → u m = 0 := by
      intro m hm
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hm (funext hcon)
      rcases hcase i with h | h
      · exact absurd ⟨i, h⟩ hex
      · exact h m hi
    obtain ⟨ρ, hρ⟩ := GlobalTheory.T.cone_values_negative_integer_rational ι r a b p hval cs
    refine ⟨u 0 * ρ 0, ?_⟩
    rw [tsum_eq_single 0 (fun m hm => by simp [hsupp m hm]), hρ 0]
    push_cast
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem expansion_on_finset (r l N : ℕ) (w : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hw : GoodWeight l w)
    (I : Finset (Fin r)) :
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ),
      (∀ q, BddW (u q)) ∧ (∀ q i, i ∉ I → GoodAt l i (u q) ∧ (cs q).count i = 0) ∧
      (∀ q i, i ∈ I → (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => w,
      fun _ => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic r l w hl (fun i m => hw.1 m i),
      fun _ i _ => ⟨⟨fun m => hw.1 m i, fun m => hw.2 m i⟩, by simp⟩,
      fun _ i hi => absurd hi (by simp), fun g _ => by simp [DL]⟩
  | insert a I ha ih =>
    obtain ⟨Q, _, cs, u, hb, hg, hs, hid⟩ := ih
    choose u' h1 h2 h3 h4 h5 using
      fun q => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OneVar.abel_oneVar r l N a (u q) hl (hg q a ha).1 (hb q)
    refine ⟨Q × Fin (N + 1), inferInstance, fun p => List.replicate (p.2 : ℕ) a ++ cs p.1,
      fun p => u' p.1 p.2, fun p => h1 p.1 p.2, ?_, ?_, ?_⟩
    · rintro ⟨q, c⟩ k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkI : k ∉ I := fun h => hk (Finset.mem_insert_of_mem h)
      refine ⟨h3 q c k hka (hg q k hkI).1, ?_⟩
      simp [List.count_append, List.count_replicate, (hg q k hkI).2, hka.symm]
    · rintro ⟨q, c⟩ k hk
      by_cases hka : k = a
      · subst hka
        have h0 : (cs q).count k = 0 := (hg q k ha).2
        rcases h2 q c with h | h
        · left
          simp [List.count_append, h0, h]
        · exact Or.inr h
      · have hkI : k ∈ I := (Finset.mem_insert.1 hk).resolve_left hka
        have hak : a ≠ k := fun h => hka h.symm
        rcases hs q k hkI with h | h
        · left
          simp [List.count_append, List.count_replicate, hak, h]
        · exact Or.inr (h4 q c k hka h)
    · intro g hgs
      rw [hid g hgs, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [h5 q _ (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r (cs q) g hgs)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [DL, List.foldr_append]

theorem expansion_all_variables : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w →
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ),
      (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  intro r l N w hl hw
  obtain ⟨Q, iQ, cs, u, hb, -, hs, hid⟩ := expansion_on_finset r l N w hl hw Finset.univ
  exact ⟨Q, iQ, cs, u, hb, fun q i => hs q i (Finset.mem_univ i), hid⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance

theorem abs_le_of_sum_eq_zero {F : Type} [Field F] [NumberField F] (f : InfinitePlace F → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hs : ∑ w, f w = 0) (hf : ∀ w, w ≠ w₀ → |f w| ≤ C) (w : InfinitePlace F) :
    |f w| ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := by
  classical
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨w⟩
  by_cases hw : w = w₀
  · subst hw
    have h1 : f w₀ = -∑ v ∈ Finset.univ.erase w₀, f v := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hs
      linarith
    rw [h1, abs_neg]
    calc |∑ v ∈ Finset.univ.erase w₀, f v| ≤ ∑ v ∈ Finset.univ.erase w₀, |f v| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ Finset.univ.erase w₀, C :=
          Finset.sum_le_sum fun v hv => hf v (Finset.ne_of_mem_erase hv)
      _ = ((Finset.univ.erase w₀).card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := by
          refine mul_le_mul_of_nonneg_right ?_ hC
          exact_mod_cast (Finset.card_erase_le).trans (Finset.card_le_univ _)
  · calc |f w| ≤ C := hf w hw
      _ = 1 * C := (one_mul C).symm
      _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := mul_le_mul_of_nonneg_right hcard hC

theorem place_apply {F : Type} [Field F] [NumberField F] (σ : F →+* ℝ) (y : F) :
    (InfinitePlace.mk (Complex.ofRealHom.comp σ)) y = |σ y| := by
  rw [InfinitePlace.apply]
  simp

theorem balance : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ M : ℝ, ∀ x : F, TotPos F x → ∃ u : (𝓞 F)ˣ, u ∈ congUnits 𝔣 ∧
      ∀ σ τ : F →+* ℝ, σ (((u : 𝓞 F) : F) * x) ≤ M * τ (((u : 𝓞 F) : F) * x) := by
  intro F _ _ _ 𝔣 h𝔣
  obtain ⟨e, he, hpow⟩ := GlobalTheory.T.exists_unit_power_in_congruence F 𝔣 h𝔣
  obtain ⟨C, hC, hbound⟩ := GlobalTheory.T.unit_log_lattice_bounded_translate F e he
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (Fintype.card (InfinitePlace F) : ℝ) := ⟨_, rfl⟩
  refine ⟨Real.exp (2 * (n * C)), fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    intro h0
    have h := hx (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (w₀ : InfinitePlace F)))
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hwx : ∀ w : InfinitePlace F, 0 < w x := fun w => InfinitePlace.pos_iff.mpr hx0
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(w₀ : InfinitePlace F)⟩).ne'
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ∑ w : InfinitePlace F, Real.log (w x) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := hbound (fun w => Real.log (w.1 x) - s / n)
  have hv := hpow u
  refine ⟨u ^ e, hv, fun σ τ => ?_⟩
  obtain ⟨-, hvpos⟩ := hv
  have hpowc : (((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) = (algebraMap (𝓞 F) F (u : 𝓞 F)) ^ e := by
    rw [Units.val_pow_eq_pow_val]
    exact map_pow (algebraMap (𝓞 F) F) _ _
  have hξpos : ∀ ρ : F →+* ℝ, 0 < ρ ((((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) * x) := by
    intro ρ
    rw [map_mul]
    exact mul_pos (hvpos ρ) (hx ρ)
  generalize hξ : (((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) * x = ξ at hξpos ⊢
  have hlog : ∀ w : InfinitePlace F,
      Real.log (w ξ) = e * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) + Real.log (w x) := by
    intro w
    have hwu : w (algebraMap (𝓞 F) F (u : 𝓞 F)) ≠ 0 :=
      (InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero u)).ne'
    rw [← hξ, hpowc, map_mul, map_pow, Real.log_mul (pow_ne_zero _ hwu) (hwx w).ne', Real.log_pow]
  set f : InfinitePlace F → ℝ := fun w => Real.log (w ξ) - s / n with hf
  have hsumu : ∑ w : InfinitePlace F, Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) = 0 := by
    have h := NumberField.Units.sum_mult_mul_log u
    simpa only [IsTotallyReal.mult_eq, Nat.cast_one, one_mul] using h
  have hsum : ∑ w, f w = 0 := by
    have h1 : ∀ w, f w = (e : ℝ) * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) + Real.log (w x) - s / n :=
      fun w => by
        show Real.log (w ξ) - s / n = _
        rw [hlog w]
    rw [Finset.sum_congr rfl (fun w _ => h1 w), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsumu, ← hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
    have h2 : n * (s / n) = s := by field_simp
    rw [h2]
    ring
  have hfC : ∀ w, w ≠ w₀ → |f w| ≤ C := by
    intro w hw
    have h := hu ⟨w, hw⟩
    simp only [logEmbedding_component, IsTotallyReal.mult_eq, Nat.cast_one, one_mul] at h
    have h2 : f w = Real.log (w x) - s / n + e * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) := by
      show Real.log (w ξ) - s / n = _
      rw [hlog w]
      ring
    rw [h2]
    exact h
  have hbd : ∀ w, |f w| ≤ n * C := fun w => by
    rw [hn]
    exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.abs_le_of_sum_eq_zero f C hC hsum hfC w
  have hρ : ∀ ρ : F →+* ℝ, Real.log (ρ ξ) = f (InfinitePlace.mk (Complex.ofRealHom.comp ρ)) + s / n := by
    intro ρ
    rw [hf]
    simp only []
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.place_apply, abs_of_pos (hξpos ρ)]
    ring
  have key : Real.log (σ ξ) ≤ 2 * (n * C) + Real.log (τ ξ) := by
    rw [hρ σ, hρ τ]
    have h1 := abs_le.mp (hbd (InfinitePlace.mk (Complex.ofRealHom.comp σ)))
    have h2 := abs_le.mp (hbd (InfinitePlace.mk (Complex.ofRealHom.comp τ)))
    linarith [h1.2, h2.1]
  calc σ ξ = Real.exp (Real.log (σ ξ)) := (Real.exp_log (hξpos σ)).symm
    _ ≤ Real.exp (2 * (n * C) + Real.log (τ ξ)) := Real.exp_le_exp.mpr key
    _ = Real.exp (2 * (n * C)) * τ ξ := by rw [Real.exp_add, Real.exp_log (hξpos τ)]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance
end
end

section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens

theorem map_sum_ratSmul {F κ : Type} [Field F] [Fintype κ] (σ : F →+* ℝ) (q : κ → ℚ) (v : κ → F) :
    σ (∑ i, q i • v i) = ∑ i, σ (v i) * (q i : ℝ) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]

theorem exists_totPos_basis : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : ℝ),
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) ∧
      ∀ x : F, TotPos F x → (∀ σ τ : F →+* ℝ, σ x ≤ M * τ x) → ∀ i, 0 < b.repr x i := by
  intro F _ _ _ M
  classical
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.card_real_embeddings_eq_finrank F
  letI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  obtain ⟨ε, hε, hW⟩ := GlobalTheory.T.near_identity_matrix_positive_solution (κ := F →+* ℝ) M
  have hex : ∀ i : F →+* ℝ, ∃ v : F, ∀ σ : F →+* ℝ,
      |σ v - ((if σ = i then 1 else 0) + ε / 2)| < ε / 2 :=
    fun i => GlobalTheory.T.totally_real_field_dense_embeddings F (fun σ => (if σ = i then 1 else 0) + ε / 2) (ε / 2) (by positivity)
  choose v hv using hex
  have hclose : ∀ σ i : F →+* ℝ, |σ (v i) - if σ = i then 1 else 0| < ε := by
    intro σ i
    have h := abs_lt.mp (hv i σ)
    rw [abs_lt]
    constructor <;> linarith [h.1, h.2]
  have hpos : ∀ σ i : F →+* ℝ, 0 < σ (v i) := by
    intro σ i
    have h := (abs_lt.mp (hv i σ)).1
    split_ifs at h <;> linarith
  obtain ⟨h1, h2⟩ := hW (fun σ i => σ (v i)) hclose
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro q hq i
    have hz : (fun i => (q i : ℝ)) = 0 := h1 _ fun σ => by
      rw [← map_sum_ratSmul σ q v, hq, map_zero]
    have hi : (q i : ℝ) = 0 := congrFun hz i
    exact_mod_cast hi
  have hcardκ : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : Nonempty (F →+* ℝ) := by
    apply Fintype.card_pos_iff.mp
    rw [hcardκ]
    exact Module.finrank_pos
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcardκ
  have hb : ∀ i, b i = v i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨F →+* ℝ, inferInstance, b, fun i σ => ?_, fun x hx hM i => ?_⟩
  · rw [hb]; exact hpos σ i
  · have hrep : ∀ σ : F →+* ℝ, σ x = ∑ i, σ (v i) * ((b.repr x i : ℚ) : ℝ) := by
      intro σ
      rw [← map_sum_ratSmul σ (fun i => b.repr x i) v]
      congr 1
      conv_lhs => rw [← b.sum_repr x]
      exact Finset.sum_congr rfl fun j _ => by rw [hb]
    have hc := h2 (fun i => ((b.repr x i : ℚ) : ℝ))
      (fun σ => by rw [← hrep σ]; exact hx σ)
      (fun σ τ => by rw [← hrep σ, ← hrep τ]; exact hM σ τ) i
    exact_mod_cast hc

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens
end
