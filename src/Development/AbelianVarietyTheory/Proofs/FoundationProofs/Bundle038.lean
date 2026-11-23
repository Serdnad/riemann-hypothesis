module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Presheaf
public import Formalism.CyclotomicNorms.Bundle001
public import Formalism.JacquetSubsetSums.JacquetSubsetSum
public import Formalism.PairingDivisors.StatementN
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle002
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.PGroup
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
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
public import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.GroupTheory.Sylow

@[expose] public section

section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame

def frameMap (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ)
    (hF : ∀ j, IsMF Γ (w j) (F j)) :
    (Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) →ₗ[ℂ] ModularForm Γ k where
  toFun g := (IsMF.sum (f := fun j => ⇑(g j) * F j) Finset.univ
    (fun j _ => ((isMF_coe_top (g j)).mono le_top).mul (hF j) (by ring))).toMF
  map_add' g h := by
    ext τ
    simp [add_mul, Finset.sum_add_distrib, Finset.sum_apply]
  map_smul' c g := by
    ext τ
    simp [Finset.mul_sum, mul_assoc, Finset.sum_apply]

theorem frameMap_apply (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)
    (k : ℤ) (hF : ∀ j, IsMF Γ (w j) (F j)) (g : Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) :
    ⇑(frameMap Γ w F k hF g) = ∑ j, ⇑(g j) * F j := rfl

theorem mul_slash_levelOne {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ)
    (g : Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) (j : Fin r) (x : SL(2, ℤ)) :
    (⇑(g j) * F j) ∣[k] x = ⇑(g j) * (F j ∣[w j] x) := by
  have h := ModularForm.mul_slash_SL2 (k - w j) (w j) x (⇑(g j)) (F j)
  rw [sub_add_cancel] at h
  rw [h, IsMF.slash_top (isMF_coe_top (g j)) x]

theorem frameMap_injective (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {r : ℕ} (s : Fin r → SL(2, ℤ))
    (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ) (hF : ∀ j, IsMF Γ (w j) (F j))
    (hdet : ∀ τ, (evM s w F τ).det ≠ 0) : Function.Injective (frameMap Γ w F k hF) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  have hsum : ∑ j, ⇑(g j) * F j = 0 := by
    rw [← frameMap_apply Γ w F k hF g, hg]
    rfl
  have hrow : ∀ i τ, ∑ j, (g j) τ * (F j ∣[w j] s i) τ = 0 := by
    intro i τ
    have h1 : (∑ j, ⇑(g j) * F j) ∣[k] s i = 0 := by
      rw [hsum]
      exact SlashAction.zero_slash _ _
    rw [SlashAction.sum_slash] at h1
    simp only [mul_slash_levelOne w F k g _ (s i)] at h1
    have h2 := congrFun h1 τ
    simpa [Finset.sum_apply] using h2
  have hv : ∀ τ, (fun j => (g j) τ) = 0 := by
    intro τ
    apply Matrix.eq_zero_of_mulVec_eq_zero (hdet τ)
    funext i
    simp only [Matrix.mulVec, dotProduct, evM, Matrix.of_apply, Pi.zero_apply]
    rw [← hrow i τ]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  funext j
  ext τ
  exact congrFun (hv τ) j

theorem finrank_sum_le_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (ModularForm Γ k) →
    (∀ j, IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) →
    ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (ModularForm Γ k) := by
  intro Γ r s w F k hΓ hfin hF hdet
  have hinj := frameMap_injective Γ s w F k hF hdet
  have : Module.Finite ℂ (Π j : Fin r, ModularForm 𝒮ℒ (k - w j)) :=
    Module.Finite.of_injective (frameMap Γ w F k hF) hinj
  have : ∀ j, Module.Finite ℂ (ModularForm 𝒮ℒ (k - w j)) := fun j =>
    Module.Finite.of_surjective (LinearMap.proj (R := ℂ)
      (φ := fun j : Fin r => ModularForm 𝒮ℒ (k - w j)) j)
      (fun y => ⟨Pi.single j y, by simp⟩)
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_injective hinj

end GlobalTheory.OddFrame
end
end

section

open Finset

namespace GlobalTheory

theorem exceptional_primes_finite_card_le (n m : ℕ) (hn : n ≠ 0) (hm : n < m) :
    Set.Finite {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ∧
      Set.ncard {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} ≤ 3 := by
  classical
  set F : Finset ℕ := n.primeFactors.filter (fun ℓ => m < ℓ ^ (4 * padicValNat ℓ n)) with hF
  have hS : {ℓ : ℕ | ℓ.Prime ∧ m < ℓ ^ (4 * padicValNat ℓ n)} = (F : Set ℕ) := by
    ext ℓ
    simp only [hF, Set.mem_ofPred_eq, coe_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨⟨hp, ?_, hn⟩, h⟩
      by_contra hd
      rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hd] at h
      simp at h
      omega
    · rintro ⟨⟨hp, -, -⟩, h⟩
      exact ⟨hp, h⟩
  rw [hS]
  refine ⟨F.finite_toSet, ?_⟩
  rw [Set.ncard_coe_finset]
  by_contra hc
  have hc4 : 4 ≤ F.card := by omega
  have h1 : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ≤ n := by
    have e : ∏ ℓ ∈ n.primeFactors, ℓ ^ padicValNat ℓ n = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.padicValNat_def, Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
    have hd : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n ∣ n := by
      conv_rhs => rw [← e]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h2 : m ^ F.card ≤ ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) :=
    Finset.pow_card_le_prod F _ m fun ℓ hℓ => ((Finset.mem_filter.1 hℓ).2).le
  have h3 : ∏ ℓ ∈ F, ℓ ^ (4 * padicValNat ℓ n) = (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm]
  have h4 : m ^ 4 ≤ m ^ F.card := Nat.pow_le_pow_right (by omega) hc4
  have h5 : (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ n) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left h1 4
  have h6 : n ^ 4 < m ^ 4 := Nat.pow_lt_pow_left hm (by norm_num)
  omega

theorem exceptional_set_count : Formalism.CyclotomicNorms.BBCount := by
  intro g hg
  have key : ∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ∧
      Set.ncard {ℓ | Formalism.CyclotomicNorms.Exc g d ℓ} ≤ 3 := by
    intro d hd
    have h1 : 1 < g ^ d := Nat.one_lt_pow (by omega) (by omega)
    exact exceptional_primes_finite_card_le (g ^ d - 1) (g ^ d) (by omega) (by omega)
  refine ⟨key, fun N => ?_⟩
  induction N with
  | zero =>
    have : Formalism.CyclotomicNorms.BB 0 g = {g} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, -⟩)
        · exact h
        · omega
      · exact Or.inl
    rw [this]
    simp
  | succ N ih =>
    have : Formalism.CyclotomicNorms.BB (N + 1) g = Formalism.CyclotomicNorms.BB N g ∪ {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ} := by
      ext ℓ
      simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | ⟨d, h1, h2, h3⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_ge N d with h | h
          · obtain rfl : d = N + 1 := by omega
            exact Or.inr h3
          · exact Or.inl (Or.inr ⟨d, h1, h, h3⟩)
      · rintro ((h | ⟨d, h1, h2, h3⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨d, h1, by omega, h3⟩
        · exact Or.inr ⟨N + 1, by omega, le_rfl, h⟩
    rw [this]
    obtain ⟨hf, hc⟩ := key (N + 1) (by omega)
    refine ⟨ih.1.union hf, ?_⟩
    have := Set.ncard_union_le (Formalism.CyclotomicNorms.BB N g) {ℓ | Formalism.CyclotomicNorms.Exc g (N + 1) ℓ}
    have := ih.2
    omega

end GlobalTheory
end

section

namespace GlobalTheory

private lemma card_pow_eq_one_le_of_isCyclic {α : Type*} [Group α] [Finite α] [IsCyclic α] {n : ℕ}
    (hn : 0 < n) : Nat.card {a : α // a ^ n = 1} ≤ n := by
  classical
  let _ := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert IsCyclic.card_pow_eq_one_le (α := α) hn

theorem card_pow_eq_one_le_index_mul {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G)
    [IsCyclic H] {d : ℕ} (hd : 0 < d) : Nat.card {x : G // x ^ d = 1} ≤ H.index * d := by
  classical

  set K : Subgroup G := (powMonoidHom d : G →* G).ker with hKdef
  have hK : Nat.card {x : G // x ^ d = 1} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp [hKdef]))
  have hsplit := (H.subgroupOf K).card_mul_index
  have hidx : (H.subgroupOf K).index ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.relIndex_dvd_index_of_normal (H := H) (K := K))
  have hsmall : Nat.card (H.subgroupOf K) ≤ d := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : H.subgroupOf K => (⟨⟨(x.1 : G), Subgroup.mem_subgroupOf.mp x.2⟩, ?_⟩ :
        {h : H // h ^ d = 1})) ?_) (card_pow_eq_one_le_of_isCyclic hd)
    · apply Subtype.ext
      have hx : (x.1 : G) ^ d = 1 := x.1.2
      simpa using hx
    · intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg (fun z : {h : H // h ^ d = 1} => ((z.1 : H) : G)) hxy
  rw [hK, ← hsplit]
  calc Nat.card (H.subgroupOf K) * (H.subgroupOf K).index ≤ d * H.index :=
        Nat.mul_le_mul hsmall hidx
    _ = H.index * d := Nat.mul_comm _ _

theorem card_pow_eq_one_le_units {M : Type*} [Monoid M] [Finite M] {d : ℕ} (hd : 0 < d) :
    Nat.card {x : M // x ^ d = 1} ≤ Nat.card {x : Mˣ // x ^ d = 1} := by
  refine Nat.card_le_card_of_injective
    (fun x => ⟨Units.ofPowEqOne x.1 d x.2 hd.ne', Units.pow_ofPowEqOne _ _⟩) ?_
  intro x y hxy
  apply Subtype.ext
  have := congrArg (fun z : {u : Mˣ // u ^ d = 1} => ((z.1 : Mˣ) : M)) hxy
  simpa using this

theorem card_pow_eq_one_le_of_isCyclic_units (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] {d : ℕ}
    (hd : 0 < d) : Nat.card {x : ZMod n // x ^ d = 1} ≤ d :=
  (card_pow_eq_one_le_units hd).trans (card_pow_eq_one_le_of_isCyclic hd)

theorem card_pow_eq_one_two_pow_le (w : ℕ) (hw : 1 ≤ w) {d : ℕ} (hd : 0 < d) :
    Nat.card {x : ZMod (2 ^ w) // x ^ d = 1} ≤ 2 * d := by
  have : NeZero (2 ^ w) := ⟨by positivity⟩
  obtain _ | _ | n := w
  · omega
  ·
    have : IsCyclic (ZMod (2 ^ 1))ˣ := (ZMod.isCyclic_units_two_pow_iff 1).mpr (by norm_num)
    exact (card_pow_eq_one_le_of_isCyclic_units _ hd).trans (by omega)
  ·
    let u : (ZMod (2 ^ (n + 2)))ˣ :=
      ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right _ (by norm_num))
    have hu : orderOf u = 2 ^ n := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, ZMod.orderOf_five]
    have hG : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ n * 2 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp [pow_succ]
    have hidx : (Subgroup.zpowers u).index = 2 := by
      have h := (Subgroup.zpowers u).card_mul_index
      rw [Nat.card_zpowers, hu, hG] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    calc Nat.card {x : ZMod (2 ^ (n + 2)) // x ^ d = 1}
        ≤ Nat.card {x : (ZMod (2 ^ (n + 2)))ˣ // x ^ d = 1} := card_pow_eq_one_le_units hd
      _ ≤ (Subgroup.zpowers u).index * d := card_pow_eq_one_le_index_mul _ hd
      _ = 2 * d := by rw [hidx]

theorem rootsOfUnityCount : Formalism.CyclotomicNorms.RootsOfUnityCount := by
  intro ℓ w d hℓ hw hd
  have : NeZero (ℓ ^ w) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  by_cases h2 : ℓ = 2
  · subst h2
    exact ⟨fun h => absurd rfl h, card_pow_eq_one_two_pow_le w hw hd⟩
  ·
    have := ZMod.isCyclic_units_of_prime_pow ℓ hℓ h2 w
    have h := card_pow_eq_one_le_of_isCyclic_units (ℓ ^ w) (d := d) hd
    exact ⟨fun _ => h.trans (Nat.le_mul_of_pos_right _ (pow_pos hℓ.pos _)), h.trans (by omega)⟩

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.NoFixedCharSum

theorem sum_rep_subgroup_eq_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N]
    (h : ∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) : ∑ n : N, τ (n : G) = 0 := by
  ext v
  simp only [LinearMap.sum_apply, LinearMap.zero_apply]
  apply h
  intro m hm

  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨m, hm⟩ : N)) _ _ ?_
  intro n
  simp [map_mul]

theorem noFixedSum : Formalism.PacketSums.NoFixedSum := by
  intro G V _ _ _ _ τ N _ h x y
  have h0 := sum_rep_subgroup_eq_zero τ N h
  have : ∑ n : N, τ (x * (n : G) * y) = τ x * (∑ n : N, τ (n : G)) * τ y := by
    simp [Finset.mul_sum, Finset.sum_mul, map_mul]

  rw [← map_sum, this, h0]
  simp

end GlobalTheory.NoFixedCharSum
end
end

section

namespace GlobalTheory

open Formalism.PairingDivisionLocalBalance

theorem exists_pow_ne_one_mod (l n : ℕ) (hl : l.Prime) (hn : ¬ (l - 1) ∣ n) :
    ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ ¬ l ∣ a ^ n - 1 := by
  haveI := Fact.mk hl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hord : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hl]
  refine ⟨(g : ZMod l).val, ?_, ZMod.val_coe_unit_coprime g, ?_⟩
  · by_contra h
    push_neg at h
    interval_cases hv : (g : ZMod l).val
    · have : (g : ZMod l) = 0 := (ZMod.val_eq_zero _).mp hv
      exact (Units.ne_zero g) this
    · have h1 : (g : ZMod l) = 1 := by
        rw [← ZMod.natCast_zmod_val (g : ZMod l), hv, Nat.cast_one]
      have : g = 1 := Units.ext h1
      rw [this, orderOf_one] at hord
      exact hn (by rw [← hord]; exact one_dvd n)
  · intro hdvd
    have hpos : 1 ≤ (g : ZMod l).val ^ n := by
      apply Nat.one_le_pow
      rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
      exact Units.ne_zero g
    have h0 : (((g : ZMod l).val ^ n - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hpos, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, sub_eq_zero] at h0
    have hgn : g ^ n = 1 := Units.ext (by simpa using h0)
    exact hn (hord ▸ orderOf_dvd_of_pow_eq_one hgn)

theorem cmValues_minPadicVal_bound : MinVal := by
  intro l n hl hn2 hne
  haveI := Fact.mk hl
  have hn0 : n ≠ 0 := by omega
  unfold mE
  simp only [Nat.padicValNat_def]
  by_cases h2 : l = 2
  · subst h2
    refine ⟨3, by norm_num, by norm_num, ?_⟩
    have h := padicValNat.pow_two_sub_one (x := 3) (n := n) (by norm_num) (by norm_num) hn0 hne
    have h4 : multiplicity 2 (3 + 1) = 2 := by
      norm_num
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have h2' : multiplicity 2 (3 - 1) = 1 := by
      norm_num
    rw [h4, h2'] at h
    simp only [if_true]
    omega
  · simp only [h2, if_false]
    have hodd : Odd l := hl.odd_of_ne_two h2
    by_cases hd : (l - 1) ∣ n
    · simp only [hd, if_true]
      refine ⟨l + 1, by have := hl.two_le; omega, ?_, ?_⟩
      · first
          | exact (Nat.coprime_succ_self l)
          | exact (Nat.coprime_self_succ l)
          | simp
      · have h := padicValNat.pow_sub_pow (p := l) (x := l + 1) (y := 1) hodd (by have := hl.one_lt; omega)
          (by simp) (by
            intro hdv
            have : l ∣ 1 := (Nat.dvd_add_right (dvd_refl l)).mp hdv
            exact hl.one_lt.ne' (Nat.dvd_one.mp this)) hn0
        rw [one_pow] at h
        rw [h, show l + 1 - 1 = l by omega, padicValNat_self]
    · simp only [hd, if_false]
      obtain ⟨a, ha2, hac, hnd⟩ := exists_pow_ne_one_mod l n hl hd
      exact ⟨a, ha2, hac, padicValNat.eq_zero_of_not_dvd hnd⟩

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.laurent_finite_of_triangular_signed_indicators : ∀ (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ))), (∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧ ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) → Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by
  first | exact @GlobalTheory.LaurentFinite.finite_of_triangular | exact GlobalTheory.LaurentFinite.finite_of_triangular | (intros; apply GlobalTheory.LaurentFinite.finite_of_triangular <;> assumption)
end

section


theorem _root_.GlobalTheory.T.isField_and_pthRoots_of_localAlg_frobenius_fixed : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
  (T : Finset A) (f : ℕ), 0 < f → Algebra.adjoin k (T : Set A) = ⊤ → (∀ t ∈ T, t ^ p ^ f = t) →
  IsField A ∧ ∀ (y : A) (a : k), y ^ p = algebraMap k A a → ∃ b : k, y = algebraMap k A b := by
  first | exact @GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots | exact GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots | (intros; apply GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_surj_hom_zmod_of_isPGroup :
    ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G],
      IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  intro p hp G _ _ _ hG
  obtain ⟨n, hn, hc⟩ := hG.nontrivial_iff_card.1 inferInstance
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p (n := m)
    (by rw [hc]; exact pow_dvd_pow p (Nat.le_succ m))
  have hi : K.index = p := by
    have := K.card_mul_index
    rw [hK, hc, pow_succ] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos m) this
  haveI : K.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hi, hc, hp.out.pow_minFac (Nat.succ_ne_zero m)])
  let e : (G ⧸ K) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq (p := p) (by rw [← hi]; rfl) (by simp)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_⟩
  exact e.surjective.comp (QuotientGroup.mk'_surjective K)

end GlobalTheory.AlmostEt
end
