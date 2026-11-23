module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle018
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle017
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle004
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_monomial_basis_of_isCompl {k : Type} [Field k] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (U U' : Submodule k V) (h : IsCompl U U')
    (hU : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V))
    (hU' : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U'), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  obtain ⟨n, b, hb⟩ := hU
  obtain ⟨n', b', hb'⟩ := hU'
  let B := (b.prod b').map (Submodule.prodEquivOfIsCompl U U' h)
  have h1 : ∀ i, B (Sum.inl i) = (b i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  have h2 : ∀ i, B (Sum.inr i) = (b' i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  refine ⟨n + n', B.reindex finSumFinEquiv, fun g i => ?_⟩
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · obtain ⟨j, c, hj⟩ := hb g i
    refine ⟨finSumFinEquiv (Sum.inl j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h1, hj]
  · obtain ⟨j, c, hj⟩ := hb' g i
    refine ⟨finSumFinEquiv (Sum.inr j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h2, hj]

theorem exists_monomial_basis_of_abByP : ∀ (k : Type) [Field k] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k], AbByP G → (Nat.card G : k) ≠ 0 → ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n), ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  intro k _
  have key : ∀ (m : ℕ) (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] (ρ : Representation k G V) [IsAlgClosed k],
      Nat.card G + Module.finrank k V = m → AbByP G → (Nat.card G : k) ≠ 0 →
      ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
        ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro G _ _ V _ _ _ ρ _ hm hG hcard
    by_cases h0 : Module.finrank k V = 0
    · exact ⟨0, Module.finBasisOfFinrankEq k V h0, fun g i => i.elim0⟩
    by_cases hirr : ρ.IsIrreducible
    · rcases finrank_eq_one_or_imprimitive k G V ρ hG hirr with h1 | ⟨T, W, hT, hW, hind, hsup⟩
      · let b := Module.finBasisOfFinrankEq k V h1
        refine ⟨1, b, fun g i => ⟨0, b.repr (ρ g (b i)) 0, ?_⟩⟩
        have := b.sum_repr (ρ g (b i))
        rw [Fin.sum_univ_one] at this
        exact this.symm
      · refine exists_monomial_basis_of_imprimitive k G V ρ T W hind hsup ?_
        let σ : Subrepresentation (ρ.comp T.subtype : Representation k T V) :=
          ⟨W, fun t w hw => hW t t.2 w hw⟩
        have hlt : Nat.card T < Nat.card G := by
          have := T.card_le_card_group
          have h2 : Nat.card T ≠ Nat.card G := fun H => hT (Subgroup.eq_top_of_card_eq T H)
          omega
        have hle : Module.finrank k W ≤ Module.finrank k V := Submodule.finrank_le W
        have hc : (Nat.card T : k) ≠ 0 := by
          intro H
          obtain ⟨d, hd⟩ := T.card_subgroup_dvd_card
          apply hcard
          rw [hd, Nat.cast_mul, H, zero_mul]
        obtain ⟨n, b, hb⟩ := ih _ (by omega) T W σ.toRepresentation rfl (AbByP.subgroup G T hG) hc
        refine ⟨n, b, fun t ht i => ?_⟩
        obtain ⟨j, c, hj⟩ := hb ⟨t, ht⟩ i
        exact ⟨j, c, congrArg Subtype.val hj⟩
    · haveI : NeZero (Nat.card G : k) := ⟨hcard⟩
      haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero h0)
      haveI : Nontrivial (Subrepresentation ρ) :=
        ⟨⊥, ⊤, fun H => (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤)
          (congrArg Subrepresentation.toSubmodule H)⟩
      have hex : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
        by_contra H
        push Not at H
        exact hirr ⟨fun U => by
          by_cases hU : U = ⊥
          · exact Or.inl hU
          · exact Or.inr (H U hU)⟩
      obtain ⟨U, hU0, hU1⟩ := hex
      obtain ⟨U', hUU'⟩ := exists_isCompl U
      have hcompl : IsCompl U.toSubmodule U'.toSubmodule :=
        ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.inf_eq_bot),
          codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hUU'.sup_eq_top)⟩
      have hsub : ∀ S : Subrepresentation ρ, S ≠ ⊤ →
          ∃ (n : ℕ) (b : Module.Basis (Fin n) k S.toSubmodule), ∀ (g : G) (i : Fin n),
            ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V) := by
        intro S hS
        have hlt : Module.finrank k S.toSubmodule < Module.finrank k V :=
          Submodule.finrank_lt (fun H => hS (Subrepresentation.ext H))
        obtain ⟨n, b, hb⟩ := ih _ (by omega) G S.toSubmodule S.toRepresentation rfl hG hcard
        refine ⟨n, b, fun g i => ?_⟩
        obtain ⟨j, c, hj⟩ := hb g i
        exact ⟨j, c, congrArg Subtype.val hj⟩
      refine exists_monomial_basis_of_isCompl ρ _ _ hcompl (hsub U hU1) (hsub U' ?_)
      rintro rfl
      exact hU0 (by simpa using hUU'.inf_eq_bot)
  intro G _ _ V _ _ _ ρ _ hG hc
  exact key _ G V ρ rfl hG hc

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.LogDeriv

variable {F : Type} [Field F]

theorem conv_congr_monic {a a' b b' : F[X] → ℂ} (ha : ∀ P : F[X], P.Monic → a P = a' P)
    (hb : ∀ P : F[X], P.Monic → b P = b' P) (P : F[X]) : conv a b P = conv a' b' P := by
  unfold conv
  refine finsum_mem_congr rfl fun x hx => ?_
  rw [ha _ hx.1, hb _ hx.2.1]

theorem conv_eq_sum (a b : F[X] → ℂ) {P : F[X]} (hP : P.Monic) :
    conv a b P = ∑ x ∈ (GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F P hP).1.toFinset, a x.1 * b x.2 := by
  unfold conv
  rw [finsum_mem_eq_finite_toFinset_sum]

theorem pow_mul_conv (q : ℂ) (a b : F[X] → ℂ) {P : F[X]} (hP : P.Monic) :
    q ^ P.natDegree * conv a b P =
      conv (fun D => q ^ D.natDegree * a D) (fun D => q ^ D.natDegree * b D) P := by
  rw [conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  rw [← h3, h1.natDegree_mul h2, pow_add]
  ring

theorem additive_mul_conv {s : F[X] → ℂ} (hs : IsAdditive s) (a b : F[X] → ℂ) {P : F[X]}
    (hP : P.Monic) :
    s P * conv a b P = conv (fun D => s D * a D) b P + conv a (fun D => s D * b D) P := by
  rw [conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  rw [← h3, hs _ _ h1 h2]
  ring

theorem pow_natDegree_ne_one {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : n ≠ 0) : (q : ℂ) ^ n - 1 ≠ 0 := by
  rw [sub_ne_zero]
  have : q ^ n ≠ 1 := (Nat.one_lt_pow hn (by omega)).ne'
  exact_mod_cast this

theorem eq_zero_of_rec {q : ℕ} (hq : 2 ≤ q) {E : F[X] → ℂ} (h1 : E 1 = 0)
    (hE : ∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * E P = conv (fun _ => 1) E P) :
    ∀ P : F[X], P.Monic → E P = 0 := by
  intro P
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    by_cases hn : n = 0
    · rw [hP.natDegree_eq_zero.mp (h.trans hn)]; exact h1
    have key : conv (fun _ => 1) E P = E P := by
      rw [conv_eq_sum _ _ hP, Finset.sum_eq_single ((1 : F[X]), P)]
      · simp
      · intro x hx hne
        rw [Set.Finite.mem_toFinset] at hx
        obtain ⟨h1, h2, h3⟩ := hx
        have hd : x.1.natDegree ≠ 0 := by
          intro h0
          have := h1.natDegree_eq_zero.mp h0
          apply hne
          rw [this, one_mul] at h3
          exact Prod.ext this h3
        have hdeg := h1.natDegree_mul h2
        rw [h3, h] at hdeg
        rw [ih x.2.natDegree (by omega) x.2 rfl h2, mul_zero]
      · intro hx
        exact absurd (by simp [hP]) hx
    have h2 := hE P hP
    rw [key, h] at h2
    have h3 : ((q : ℂ) ^ n - 1) * E P = 0 := by linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_left (pow_natDegree_ne_one hq hn)

theorem mangoldt_one (s : F[X] → ℂ) : mangoldt s 1 = 0 := by
  unfold mangoldt
  refine finsum_mem_eq_zero_of_forall_eq_zero ?_
  rintro f ⟨_, hf, m, hm, h⟩
  exact absurd (IsUnit.of_pow_eq_one h.symm hm.ne') hf.not_isUnit

theorem conv_at_one (a b : F[X] → ℂ) : conv a b 1 = a 1 * b 1 := by
  unfold conv
  have : {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = 1} = {(1, 1)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hdeg := h1.natDegree_mul h2
      rw [h3, natDegree_one] at hdeg
      exact Prod.ext (h1.natDegree_eq_zero.mp (by omega)) (h2.natDegree_eq_zero.mp (by omega))
    · rintro rfl
      simp
  rw [this, finsum_mem_singleton]

theorem additive_mul_eq_conv (F : Type) [Field F] (q : ℕ) (hq : 2 ≤ q) (s m : F[X] → ℂ)
    (hs : IsAdditive s) (_hm1 : m 1 = 1)
    (hm : ∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * m P = conv (fun _ => 1) m P)
    (P : F[X]) (hP : P.Monic) :
    s P * m P = conv (fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1)) m P := by
  set L : F[X] → ℂ := fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1) with hL
  set o : F[X] → ℂ := fun _ => 1 with ho
  have hs1 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    rw [mul_one] at this
    linear_combination -this
  have hσL : ∀ D : F[X], D.Monic → (q : ℂ) ^ D.natDegree * L D = (L + mangoldt s) D := by
    intro D hD
    by_cases h0 : D.natDegree = 0
    · rw [hD.natDegree_eq_zero.mp h0]
      simp [hL, mangoldt_one]
    · have := pow_natDegree_ne_one hq h0
      simp only [hL, Pi.add_apply]
      field_simp
      ring
  have hA : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * (s Q * m Q) =
      conv (conv (mangoldt s) o) m Q + conv o (fun D => s D * m D) Q := by
    intro Q hQ
    rw [mul_left_comm, hm Q hQ, additive_mul_conv hs _ _ hQ]
    congr 1
    refine conv_congr_monic (fun D hD => ?_) (fun _ _ => rfl) Q
    rw [← (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F s hs).1 D hD]
    simp [ho]
  have hB : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * conv L m Q =
      conv (conv (mangoldt s) o) m Q + conv o (conv L m) Q := by
    intro Q hQ
    have H := (GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F Q hQ).2
    rw [pow_mul_conv _ _ _ hQ, conv_congr_monic hσL hm Q, (H L (mangoldt s) (conv o m)).2.2.1,
      (H (mangoldt s) o m).2.1, add_comm, ← (H L o m).2.1, ← (H o L m).2.1]
    congr 1
    exact conv_congr_monic (fun D hD => ((GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F D hD).2 L o o).1) (fun _ _ => rfl) Q
  have hE := eq_zero_of_rec hq (E := (fun D => s D * m D) - conv L m)
    (by simp [hs1, conv_at_one, hL, mangoldt_one]) (fun Q hQ => by
      have H := (GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F Q hQ).2
      rw [(H _ _ o).1, (H _ _ _).2.2.2, ← (H o _ o).1, ← (H o _ o).1, Pi.sub_apply, mul_sub,
        hA Q hQ, hB Q hQ]
      ring) P hP
  exact sub_eq_zero.mp hE

end GlobalTheory.CuspGL.LogDeriv
end
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem exists_conj_of_aeval'_equiv {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (g g' : Module.End F V) (φ : Module.AEval' g ≃ₗ[F[X]] Module.AEval' g') :
    ∃ e : V ≃ₗ[F] V, e.conj g = g' := by
  let e : V ≃ₗ[F] V := (Module.AEval'.of g).trans
    ((φ.restrictScalars F).trans (Module.AEval'.of g').symm)
  have h : ∀ v, e (g v) = g' (e v) := by
    intro v
    have h1 : Module.AEval'.of g (g v) = (X : F[X]) • Module.AEval'.of g v :=
      (Module.AEval'.X_smul_of g v).symm
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, h1, map_smul]
    exact Module.AEval'.of_symm_X_smul g' _
  refine ⟨e, ?_⟩
  ext v
  simp [LinearEquiv.conj_apply, h]

theorem primary_conj_of_finrank_ker_eq : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g g' : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → aeval g' (f ^ m) = 0 → (∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval g' (f ^ j)))) → ∃ e : V ≃ₗ[F] V, e.conj g = g' := by
  intro F _ V _ _ _ g g' f m hf hg hg' hk
  obtain ⟨d, e, he, ⟨φ⟩, hd⟩ := GlobalTheory.T.primary_endomorphism_cyclic_decomposition_finrank_ker F V g f m hf hg
  obtain ⟨d', e', he', ⟨φ'⟩, hd'⟩ := GlobalTheory.T.primary_endomorphism_cyclic_decomposition_finrank_ker F V g' f m hf hg'
  have hpos : 0 < f.natDegree := hf.natDegree_pos
  have hs : ∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i) := by
    intro j
    have := hk j
    rw [hd j, hd' j] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_perm_of_sum_min_eq_positive_family d d' e e' he he' hs
  obtain rfl : e = fun i => e' (σ i) := funext fun i => (hσ i).symm
  exact exists_conj_of_aeval'_equiv g g' (φ.trans
    ((LinearEquiv.piCongrLeft F[X] (fun i => F[X] ⧸ Ideal.span {f ^ e' i}) σ).trans φ'.symm))

end GlobalTheory.CuspGL
end
