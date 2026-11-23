module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle002
public import Mathlib.RepresentationTheory.Character
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle051
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle059
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
public import Mathlib.GroupTheory.GroupAction.Ring
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle031
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle035
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle036
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

@[expose] public section

section

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspIff

def stdRadical (K : Type) [Field K] [Fintype K] [DecidableEq K] (d a : ℕ) : Subgroup (GL (Fin d) K) :=
  have hmul : ∀ u v : GL (Fin d) K,
      (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      (∀ i j : Fin d, (v : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      ∀ i j : Fin d, ((u * v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
        ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
    intro u v hu hv i j
    by_cases hij : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr hij
    left
    rw [Units.val_mul, Matrix.mul_apply]
    by_cases hi : (i : ℕ) < a
    · have hk : ∀ k, (v : Matrix (Fin d) (Fin d) K) k j = if k = j then 1 else 0 :=
        fun k => (hv k j).resolve_right (by omega)
      simp only [hk]
      simpa using (hu i j).resolve_right hij
    · have hk : ∀ k, (u : Matrix (Fin d) (Fin d) K) i k = if i = k then 1 else 0 :=
        fun k => (hu i k).resolve_right (by omega)
      simp only [hk]
      simpa using (hv i j).resolve_right hij
  have hone : ∀ i j : Fin d, ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := fun i j => Or.inl (by simp [Matrix.one_apply])
  { carrier := {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ))}
    one_mem' := hone
    mul_mem' := fun {u v} hu hv => hmul u v hu hv
    inv_mem' := by
      intro u hu
      have hpow : ∀ n : ℕ, ∀ i j : Fin d, ((u ^ n : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
          (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
        intro n
        induction n with
        | zero => simpa using hone
        | succ n ih => rw [pow_succ]; exact hmul _ _ ih hu
      have hinv : u⁻¹ = u ^ (orderOf u - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
      show ∀ i j : Fin d, ((u⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = _ ∨ _
      rw [hinv]
      exact hpow _ }

theorem mem_stdRadical {K : Type} [Field K] [Fintype K] [DecidableEq K] {d a : ℕ} {u : GL (Fin d) K} :
    u ∈ stdRadical K d a ↔ ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := Iff.rfl

theorem pm_conj {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (g : GL ι K) : pm (K := K) σ * g * (pm (K := K) σ)⁻¹ = glEquiv K σ g := by
  have hp : ∀ i j, (pm (K := K) σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
    intro i j
    show (Equiv.toPEquiv σ⁻¹).toMatrix i j = _
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    exact if_congr Equiv.Perm.inv_eq_iff_eq rfl rfl
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  have hg : ∀ x : GL ι K, ((glEquiv K σ x : GL ι K) : Matrix ι ι K) = (x : Matrix ι ι K).submatrix σ.symm σ.symm :=
    fun _ => rfl
  simp only [Units.val_mul, Matrix.mul_apply, hp, hg, Matrix.submatrix_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm i) (fun x _ hx => if_neg (fun h => hx (by simp [h]))) (by simp)]
  simp

theorem eq_zero_of_sum_char {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) [DecidablePred (· ∈ U)]
    (h : (∑ u : G, if u ∈ U then ρ.character u else 0) = 0) (v : V) (hv : ∀ u ∈ U, ρ u v = v) : v = 0 := by
  have hc : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have h1 := Representation.card_inv_mul_sum_char_eq_finrank (ρ.comp U.subtype : Representation ℂ U V)
  have hs : (∑ u : G, if u ∈ U then ρ.character u else 0) =
      ∑ g : U, Representation.character (ρ.comp U.subtype : Representation ℂ U V) g := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) (fun g => ρ.character g)
  rw [hs] at h
  rw [h, mul_zero] at h1
  have h2 : Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← Nat.cast_eq_zero (R := ℂ)]
    exact h1.symm
  have hm : v ∈ Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) := by
    rw [Representation.mem_invariants]
    exact fun u => hv u.1 u.2
  rw [h2] at hm
  simpa using hm

theorem isCuspidal_of_sum_char : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  classical
  intro K _ _ _ d τ h s b hb hs v hv
  let c0 : Fin s := ⟨0, by omega⟩
  let c1 : Fin s := ⟨1, by omega⟩
  have hc : c0 ≠ c1 := by simp [c0, c1, Fin.ext_iff]
  obtain ⟨i0, hi0⟩ := hb c0
  obtain ⟨i1, hi1⟩ := hb c1
  set a := Fintype.card {i // b i = c0} with ha
  have ha0 : 0 < a := Fintype.card_pos_iff.2 ⟨⟨i0, hi0⟩⟩
  have had : a < d := by
    have := Fintype.card_subtype_lt (p := fun i => b i = c0) (x := i1) (by rw [hi1]; exact hc.symm)
    simpa using this
  have hcard : Fintype.card {i // b i = c0} = Fintype.card {i : Fin d // (i : ℕ) < a} := by
    rw [← ha]
    exact (Fintype.card_fin a).symm.trans (Fintype.card_congr
      { toFun := fun k => ⟨⟨k, by omega⟩, k.2⟩
        invFun := fun i => ⟨i.1, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
  let e := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm (Fin d) := e.extendSubtype
  have hσ : ∀ i, (σ i : ℕ) < a ↔ b i = c0 := by
    intro i
    by_cases hi : b i = c0
    · exact ⟨fun _ => hi, fun _ => e.extendSubtype_mem i hi⟩
    · exact ⟨fun h' => absurd h' (e.extendSubtype_not_mem i hi), fun h' => absurd h' hi⟩
  have hfix : ∀ w : τ, (∀ u ∈ stdRadical K d a, τ.ρ u w = w) → w = 0 := by
    refine eq_zero_of_sum_char τ.ρ (stdRadical K d a) ?_
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) (h a ha0 had)
    by_cases hu : u ∈ stdRadical K d a
    · rw [if_pos hu, if_pos (mem_stdRadical.1 hu)]; rfl
    · rw [if_neg hu, if_neg (fun h' => hu (mem_stdRadical.2 h'))]

  have hent : ∀ (x : GL (Fin d) K) (i j : Fin d),
      ((pm (K := K) σ * x * (pm (K := K) σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (σ i) (σ j) =
        (x : Matrix (Fin d) (Fin d) K) i j := by
    intro x i j
    rw [pm_conj]
    show (x : Matrix (Fin d) (Fin d) K) (σ.symm (σ i)) (σ.symm (σ j)) = _
    simp
  have key : ∀ x : GL (Fin d) K, pm (K := K) σ * x * (pm (K := K) σ)⁻¹ ∈ stdRadical K d a → ∀ i j,
      (x : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ (b i = c0 ∧ b j ≠ c0) := by
    intro x hx i j
    have := hx (σ i) (σ j)
    rw [hent] at this
    rcases this with h1 | ⟨h1, h2⟩
    · left; simpa [σ.injective.eq_iff] using h1
    · right
      refine ⟨(hσ i).1 h1, fun h3 => ?_⟩
      have := (hσ j).2 h3
      omega
  have hut : ∀ x : GL (Fin d) K, pm (K := K) σ * x * (pm (K := K) σ)⁻¹ ∈ stdRadical K d a →
      IsBlockUT K b (x : Matrix (Fin d) (Fin d) K) := by
    intro x hx i j hij
    rcases key x hx i j with h1 | ⟨h1, -⟩
    · have : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
      simpa [this] using h1
    · rw [h1] at hij
      exact absurd hij (by simp [c0, Fin.lt_def])
  have hun : ∀ x : GL (Fin d) K, pm (K := K) σ * x * (pm (K := K) σ)⁻¹ ∈ stdRadical K d a → x ∈ unip K b := by
    intro x hx
    refine ⟨⟨hut x hx, hut x⁻¹ ?_⟩, ?_⟩
    · have : pm (K := K) σ * x⁻¹ * (pm (K := K) σ)⁻¹ = (pm (K := K) σ * x * (pm (K := K) σ)⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
    · intro i j hij
      rcases key x hx i j with h1 | ⟨h1, h2⟩
      · exact h1
      · exact absurd (hij ▸ h1) h2
  have hw := hfix (τ.ρ (pm (K := K) σ) v) (by
    intro u hu
    have hx : (pm (K := K) σ)⁻¹ * u * pm (K := K) σ ∈ unip K b := by
      apply hun
      have : pm (K := K) σ * ((pm (K := K) σ)⁻¹ * u * pm (K := K) σ) * (pm (K := K) σ)⁻¹ = u := by group
      rw [this]
      exact hu
    have hh : u * pm (K := K) σ = pm (K := K) σ * ((pm (K := K) σ)⁻¹ * u * pm (K := K) σ) := by group
    rw [← Module.End.mul_apply, ← map_mul, hh, map_mul, Module.End.mul_apply, hv _ hx])
  have h3 := congrArg (τ.ρ (pm (K := K) σ)⁻¹) hw
  simpa [← Module.End.mul_apply, ← map_mul] using h3

end GlobalTheory.CompanionTheory.TyFin.CuspIff
end
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.section_orthogonal_idempotent_sum : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := by
  first | exact @GlobalTheory.CompanionTheory.SecAdd.secOn_add | exact GlobalTheory.CompanionTheory.SecAdd.secOn_add | (intros; apply GlobalTheory.CompanionTheory.SecAdd.secOn_add <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.DichMod

variable {S : Type} [CommRing S]

theorem isUnit_one_sub_mul {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (w : S) :
    IsUnit (1 - w * ϖ) := by
  have h := Ideal.mem_jacobson_bot.mp hJ (-w)
  have e : ϖ * -w + 1 = 1 - w * ϖ := by ring
  rwa [e] at h

theorem dvd_or_dvd {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) (f : S) :
    ϖ ∣ f ∨ f ∣ ϖ := by
  rcases hc f ϖ with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    exact ⟨c + d * ϖ, by rw [← e]; ring⟩
  · right
    obtain ⟨c, w, e⟩ := Ideal.mem_span_pair.mp h
    have hu := isUnit_one_sub_mul hJ w
    have key : (1 - w * ϖ) * ϖ = c * f := by
      have : c * f = ϖ - w * ϖ ^ 2 := by linear_combination e
      rw [this]; ring
    exact hu.dvd_mul_left.mp (key ▸ dvd_mul_left f c)

theorem comparable {ϖ : S}
    (hc : ∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) {f g : S}
    (hf : f ∣ ϖ) (hg : g ∣ ϖ) : g ∣ f ∨ f ∣ g := by
  rcases hc f g with h | h
  · left
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left g c) ((hg.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)
  · right
    obtain ⟨c, d, e⟩ := Ideal.mem_span_pair.mp h
    rw [← e]
    exact dvd_add (dvd_mul_left f c) ((hf.trans (dvd_pow_self ϖ two_ne_zero)).mul_left d)

theorem dvd_of_high {ϖ : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) {f g a b : S} {N : ℕ}
    (e : a * f + b * g = ϖ ^ N) (h : ϖ ^ (N + 1) ∣ f) : g ∣ f := by
  obtain ⟨t, ht⟩ := h
  have hu := isUnit_one_sub_mul hJ (a * t)
  have key : (1 - a * t * ϖ) * ϖ ^ N = b * g := by
    have : b * g = ϖ ^ N - a * f := by linear_combination e
    rw [this, ht]; ring
  have hg : g ∣ ϖ ^ N := hu.dvd_mul_left.mp (key ▸ dvd_mul_left g b)
  exact hg.trans ⟨ϖ * t, by rw [ht]; ring⟩

theorem dvd_of_lt {ϖ f g f' g' : S} {i j : ℕ} (hf : f = ϖ ^ i * f') (hg : g = ϖ ^ j * g')
    (hf' : f' ∣ ϖ) (hij : i < j) : f ∣ g := by
  have h1 : f ∣ ϖ ^ (i + 1) := by
    rw [hf, pow_succ]
    exact mul_dvd_mul_left _ hf'
  have h2 : ϖ ^ (i + 1) ∣ g := by
    rw [hg]
    exact (pow_dvd_pow ϖ hij).mul_right g'
  exact h1.trans h2

theorem dich_of_mod : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  intro S _ ϖ hJ hc f g hN
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, b, e⟩ := Ideal.mem_span_pair.mp hN
  have hd := dvd_or_dvd hJ hc
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd f (N + 1) with hf | ⟨i, f', hf, hf'⟩
  · exact Or.inl (dvd_of_high hJ e hf)
  rcases GlobalTheory.CompanionTheory.NormalForm.normal_form_of_dichotomy ϖ hd g (N + 1) with hg | ⟨j, g', hg, hg'⟩
  · exact Or.inr (dvd_of_high hJ (by rw [add_comm]; exact e) hg)
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inr (dvd_of_lt hf hg hf' hij)
  · subst hij
    rw [hf, hg]
    rcases comparable hc hf' hg' with h | h
    · exact Or.inl (mul_dvd_mul_left _ h)
    · exact Or.inr (mul_dvd_mul_left _ h)
  · exact Or.inl (dvd_of_lt hg hf hg' hij)

end GlobalTheory.CompanionTheory.DichMod
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.Idem

theorem val_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S),
    (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := by
  intro S _ ϖ hD f g hfg
  obtain ⟨N, hN⟩ := hfg
  let Q : S → Prop := fun e => ∃ d, IsIdempotentElem d ∧ d * e = d ∧ d * f ∈ Ideal.span {g} ∧
    (e - d) * g ∈ Ideal.span {f}
  have hQ1 : Q 1 := by
    apply GlobalTheory.CompanionTheory.Idem.glue_idempotent_property Q
    · exact ⟨0, IsIdempotentElem.zero, by simp, by simp, by simp⟩
    · rintro e e' he he' ⟨d, hd, hde, hdf, hdg⟩
      refine ⟨d * e', hd.mul he', ?_, ?_, ?_⟩
      · calc d * e' * (e * e') = (d * e) * (e' * e') := by ring
          _ = d * e' := by rw [hde, he'.eq]
      · rw [mul_comm d e', mul_assoc]
        exact Ideal.mul_mem_left _ _ hdf
      · have h3 : (e * e' - d * e') * g = e' * ((e - d) * g) := by ring
        rw [h3]
        exact Ideal.mul_mem_left _ _ hdg
    · rintro e e' he he' hee ⟨d, hd, hde, hdf, hdg⟩ ⟨d', hd', hde', hdf', hdg'⟩
      have hdd : d * d' = 0 := by
        calc d * d' = (d * e) * (d' * e') := by rw [hde, hde']
          _ = (d * d') * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h1 : d * e' = 0 := by
        calc d * e' = (d * e) * e' := by rw [hde]
          _ = d * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h2 : d' * e = 0 := by
        calc d' * e = (d' * e') * e := by rw [hde']
          _ = d' * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      refine ⟨d + d', ?_, ?_, ?_, ?_⟩
      · show (d + d') * (d + d') = d + d'
        calc (d + d') * (d + d') = d * d + d' * d' + 2 * (d * d') := by ring
          _ = d + d' := by rw [hd.eq, hd'.eq, hdd, mul_zero, add_zero]
      · calc (d + d') * (e + e') = d * e + d * e' + (d' * e + d' * e') := by ring
          _ = d + d' := by rw [hde, hde', h1, h2]; ring
      · rw [add_mul]
        exact Ideal.add_mem _ hdf hdf'
      · have h3 : (e + e' - (d + d')) * g = (e - d) * g + (e' - d') * g := by ring
        rw [h3]
        exact Ideal.add_mem _ hdg hdg'
    · intro m hm
      have hprime := hm.isPrime
      have hspan : (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) ϖ) ^ N ∈
          Ideal.span {Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) f, Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) g} := by
        rw [← map_pow]
        have h4 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m)) hN
        rwa [Ideal.map_span, Set.image_pair] at h4
      rcases hD m hm _ _ ⟨N, hspan⟩ with hgf | hfg'
      · obtain ⟨c, hc⟩ := hgf
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : f - g * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have hef : e * f = e * (g * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, e, he, he.eq, ?_, by simp⟩
        rw [hef]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
      · obtain ⟨c, hc⟩ := hfg'
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : g - f * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have heg : e * g = e * (f * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, 0, IsIdempotentElem.zero, by simp, by simp, ?_⟩
        rw [sub_zero, heg]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
  obtain ⟨d, hd, -, hdf, hdg⟩ := hQ1
  exact ⟨d, hd, hdf, hdg⟩

end GlobalTheory.CompanionTheory.Idem
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.divided_power_morphism_compatible : ∀ {S : Type} [CommRing S] {S' E E' : Type} [CommRing S'] [CommRing E] [CommRing E'] (π : S →+* E) (π' : S' →+* E') (I : Ideal S) (I' : Ideal S') {J : Ideal E} {J' : Ideal E'} (δ : DividedPowers J) (δ' : DividedPowers J') (F₀ : S →+* S') (F : E →+* E'), Function.Surjective π → PdI I → IsPd π I δ → IsPd π' I' δ' → (∀ x ∈ I, F₀ x ∈ I') → (∀ x, F (π x) = π' (F₀ x)) → DividedPowers.IsDPMorphism δ δ' F := by
  first | exact @GlobalTheory.CompanionTheory.PdMor.isDPMorphism_of_isPd | exact GlobalTheory.CompanionTheory.PdMor.isDPMorphism_of_isPd | (intros; apply GlobalTheory.CompanionTheory.PdMor.isDPMorphism_of_isPd <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_smul_dual : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk (x • f) z = k x * T c k hk f z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPsi.T_ksmul | exact GlobalTheory.CompanionTheory.FrobPsi.T_ksmul | (intros; apply GlobalTheory.CompanionTheory.FrobPsi.T_ksmul <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_basis_eval : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {B : Type} [Field B] (ι : C₀ →+* B) (i : A →+* B), (∀ a, ι (c a) = i a) → ∀ (h : L →+ B), (∀ (w : W) y, h (w • y) = i (algebraMap W A w) * h y) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)), ∃ E : K₀ ⊗[W] L →+ B, (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) ∧ ∀ G : A ⊗[W] L →+ B, (∀ a y, G (a ⊗ₜ y) = i a * h y) → ∀ z, G z = ∑ s, ι (T c k hk (b.coord s) z) * E (b s) := by
  first | exact @GlobalTheory.CompanionTheory.FrobFac.T_fac | exact GlobalTheory.CompanionTheory.FrobFac.T_fac | (intros; apply GlobalTheory.CompanionTheory.FrobFac.T_fac <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_frobenius_compat : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ {F : W →+* W} (φA : A →+* A) (φC : C₀ →+* C₀) (φL : L →ₛₗ[F] L) (fr : K₀ →+* K₀) (φD : K₀ ⊗[W] L →+ K₀ ⊗[W] L), (∀ x y, φD (x ⊗ₜ y) = fr x ⊗ₜ φL y) → ∀ (pT : A ⊗[W] L →+ A ⊗[W] L), (∀ a y, pT (a ⊗ₜ y) = φA a ⊗ₜ φL y) → (∀ a, φC (c a) = c (φA a)) → (∀ x, φC (k x) = k (fr x)) → ∀ {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk f (pT z) = ∑ s, φC (T c k hk (b.coord s) z) * k (f (φD (b s))) := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand | exact GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_phi_expand <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_lTensor_naturality : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)) {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L'), T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPsi.T_lTensor | exact GlobalTheory.CompanionTheory.FrobPsi.T_lTensor | (intros; apply GlobalTheory.CompanionTheory.FrobPsi.T_lTensor <;> assumption)
end

section

open CrystallineSemistableComparison.Pb.Kap

theorem _root_.GlobalTheory.T.realization_add : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.rho_add | exact GlobalTheory.CompanionTheory.KapRho.rho_add | (intros; apply GlobalTheory.CompanionTheory.KapRho.rho_add <;> assumption)
end

section

open CrystallineSemistableComparison.Pb.Kap

theorem _root_.GlobalTheory.T.exists_realization_of_compatible : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j), C.Comp x → ∃ f : Module.Dual K (C.V j) →+ B, C.Rho x f := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.exists_rho | exact GlobalTheory.CompanionTheory.KapRho.exists_rho | (intros; apply GlobalTheory.CompanionTheory.KapRho.exists_rho <;> assumption)
end

section

open CrystallineSemistableComparison.Pb.Kap

theorem _root_.GlobalTheory.T.realization_cup_product : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ {i j : ℕ} (x : ∀ n, C.S n i) (y : ∀ n, C.S n j) (f : Module.Dual K (C.V i) →+ B) (g : Module.Dual K (C.V j) →+ B) (h : Module.Dual K (C.V (i + j)) →+ B), C.Rho x f → C.Rho y g → C.Rho (fun n => P.cS n i j (x n) (y n)) h → ∀ {m m' : ℕ} (bs : Module.Basis (Fin m) K (C.V i)) (bs' : Module.Basis (Fin m') K (C.V j)) (φ : Module.Dual K (C.V (i + j))), h φ = ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') * C.o (φ (P.cV i j (bs s) (bs' s'))) := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.rho_cup | exact GlobalTheory.CompanionTheory.KapRho.rho_cup | (intros; apply GlobalTheory.CompanionTheory.KapRho.rho_cup <;> assumption)
end
