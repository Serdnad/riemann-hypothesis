module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle446
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open PositivityTheory.RgBcC.RealD (alg kF)

namespace GlobalTheory.CompanionTheory.ModelS.LocFin

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι κ : Type}

def stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : Submodule ℂ V := S ⊔ ⨆ i, S.map (L i)

def fil (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) : Submodule ℂ V := (stp L)^[k] S₀

theorem fil_succ (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) :
    fil L S₀ (k + 1) = stp L (fil L S₀ k) :=
  Function.iterate_succ_apply' _ _ _

theorem le_stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : S ≤ stp L S := le_sup_left

theorem letter_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S) (i : ι) :
    L i u ∈ stp L S :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hu))

theorem span_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S)
    {C : Module.End ℂ V} (hC : C ∈ Submodule.span ℂ (Set.range L)) : C u ∈ stp L S := by
  induction hC using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact letter_mem_stp L hu i
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem fil_mono (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) : Monotone (fil L S₀) :=
  monotone_nat_of_le_succ fun k => by
    rw [fil_succ]
    exact le_stp L _

theorem fil_finite [Finite ι] (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) [h₀ : FiniteDimensional ℂ S₀] (k : ℕ) :
    FiniteDimensional ℂ (fil L S₀ k) := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    have : ∀ i, FiniteDimensional ℂ ((fil L S₀ k).map (L i)) := fun i => inferInstance
    have : FiniteDimensional ℂ ↥(⨆ i, (fil L S₀ k).map (L i) : Submodule ℂ V) := Submodule.finiteDimensional_iSup _
    exact Submodule.finiteDimensional_sup _ _

theorem stp_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S : Submodule ℂ V}
    (hS : ∀ w ∈ S, K w ∈ S) : ∀ w ∈ stp L S, K w ∈ stp L S := by
  have key : stp L S ≤ (stp L S).comap K := by
    refine sup_le (fun w hw => le_stp L S (hS w hw)) (iSup_le fun i => ?_)
    rintro _ ⟨u, hu, rfl⟩
    have h1 : L i (K u) ∈ stp L S := letter_mem_stp L (hS u hu) i
    have h2 : (K * L i - L i * K) u ∈ stp L S := span_mem_stp L hu (hK i)
    have h3 : K (L i u) = (K * L i - L i * K) u + L i (K u) := by simp
    change K (L i u) ∈ stp L S
    rw [h3]
    exact add_mem h2 h1
  exact fun w hw => key hw

theorem fil_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S₀ : Submodule ℂ V}
    (h₀ : ∀ w ∈ S₀, K w ∈ S₀) (k : ℕ) : ∀ w ∈ fil L S₀ k, K w ∈ fil L S₀ k := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    exact stp_stable L K hK ih

theorem mem_fil_of_adjoin (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) {T : Module.End ℂ V}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range L)) {f : V} (hf : f ∈ S₀) : ∃ k, T f ∈ fil L S₀ k := by
  have key : ∀ w, (∃ k, w ∈ fil L S₀ k) → ∃ k, T w ∈ fil L S₀ k := by
    induction hT using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rintro w ⟨k, hk⟩
      exact ⟨k + 1, by rw [fil_succ]; exact letter_mem_stp L hk i⟩
    | algebraMap r =>
      rintro w ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ r hk
    | add x y _ _ hx hy =>
      intro w hw
      obtain ⟨k, hk⟩ := hx w hw
      obtain ⟨m, hm⟩ := hy w hw
      refine ⟨max k m, ?_⟩
      simpa using add_mem (fil_mono L S₀ (le_max_left k m) hk) (fil_mono L S₀ (le_max_right k m) hm)
    | mul x y _ _ hx hy =>
      intro w hw
      simpa using hx (y w) (hy w hw)
  exact key f ⟨0, hf⟩

end Abstract

section Pair

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) : Bool × Fin n × Fin n → Module.End ℂ V
  | (true, a, b) => F1 a b
  | (false, a, b) => F2 a b

theorem range_letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) :
    Set.range (letters F1 F2) = {x | ∃ a b, x = F1 a b ∨ x = F2 a b} := by
  ext x
  constructor
  · rintro ⟨⟨_ | _, a, b⟩, rfl⟩
    · exact ⟨a, b, Or.inr rfl⟩
    · exact ⟨a, b, Or.inl rfl⟩
  · rintro ⟨a, b, rfl | rfl⟩
    · exact ⟨(true, a, b), rfl⟩
    · exact ⟨(false, a, b), rfl⟩

theorem gl_span (F1 F2 : Fin n → Fin n → Module.End ℂ V) (e : Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : ∀ a b, E a b = letters F1 F2 (e, a, b)) (a b c d : Fin n) :
    (if b = c then E a d else 0) - (if d = a then E c b else 0) ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  have hm : ∀ a b, E a b ∈ Submodule.span ℂ (Set.range (letters F1 F2)) := fun a b =>
    Submodule.subset_span ⟨(e, a, b), (hE a b).symm⟩
  refine sub_mem ?_ ?_
  · split_ifs
    · exact hm _ _
    · exact zero_mem _
  · split_ifs
    · exact hm _ _
    · exact zero_mem _

theorem comm_letters {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h1 : Formalism.REAL.GlRel F1) (h2 : Formalism.REAL.GlRel F2)
    (hc : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) (a b : Fin n) (i : Bool × Fin n × Fin n) :
    kF F1 F2 a b * letters F1 F2 i - letters F1 F2 i * kF F1 F2 a b ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  obtain ⟨_ | _, c, d⟩ := i
  · have h : kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b =
        (if b = c then F2 a d else 0) - (if d = a then F2 c b else 0) := by
      rw [← h2 a b c d]
      delta kF
      simp only [add_mul, mul_add, hc a b c d]
      abel
    change kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 false F2 (fun _ _ => rfl) a b c d
  · have h : kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b =
        (if b = c then F1 a d else 0) - (if d = a then F1 c b else 0) := by
      rw [← h1 a b c d]
      delta kF
      simp only [add_mul, mul_add, hc c d a b]
      abel
    change kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 true F1 (fun _ _ => rfl) a b c d

end Pair

theorem cyclic_locFin : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 →
    (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V, (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) →
    ∀ S₀ : Submodule ℂ V, FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) →
    ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
  intro n V _ _ F1 F2 h1 h2 hc f hgen S₀ hfin hf hst x
  obtain ⟨T, hT, rfl⟩ := hgen x
  have hT' : T ∈ Algebra.adjoin ℂ (Set.range (letters F1 F2)) := by
    rw [range_letters]
    exact hT
  obtain ⟨k, hk⟩ := mem_fil_of_adjoin (letters F1 F2) S₀ hT' hf
  exact ⟨fil (letters F1 F2) S₀ k, fil_finite _ _ k, hk, fun a b =>
    fil_stable _ _ (comm_letters h1 h2 hc a b) (hst a b) k⟩

end GlobalTheory.CompanionTheory.ModelS.LocFin
end
end

section

open Finset

namespace GlobalTheory.CompanionTheory.LevelCompress

open PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def lowCount (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

theorem lowCount_lt (lev : Fin n → ℕ) (a : Fin n) : lowCount lev a < n := by
  have h : (univ.filter fun b => lev b < lev a).card < (univ : Finset (Fin n)).card :=
    Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, Finset.mem_univ a, lt_irrefl (lev a)⟩)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem lowCount_le_of_le {lev : Fin n → ℕ} {a b : Fin n} (h : lev a ≤ lev b) :
    lowCount lev a ≤ lowCount lev b := by
  unfold lowCount
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_lt_of_le hc.2 h⟩

theorem lowCount_lt_of_lt {lev : Fin n → ℕ} {a b : Fin n} (h : lev a < lev b) :
    lowCount lev a < lowCount lev b := by
  unfold lowCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ a, h⟩
    · simp only [Finset.mem_filter, lt_irrefl, and_false, not_false_eq_true]
  · intro c hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.trans h⟩

theorem lowCount_lt_iff {lev : Fin n → ℕ} {a b : Fin n} :
    lowCount lev a < lowCount lev b ↔ lev a < lev b := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.2 (lowCount_le_of_le (not_lt.1 h')))
  · exact lowCount_lt_of_lt

theorem rhoU_lowCount (lev : Fin n → ℕ) : rhoU (lowCount lev) = rhoU lev := by
  funext a
  simp only [rhoU, lowCount_lt_iff]

theorem muQ_lowCount (lam : Fin n → ℤ) (lev : Fin n → ℕ) : muQ lam (lowCount lev) = muQ lam lev := by
  unfold muQ
  rw [rhoU_lowCount]

theorem isLev_lowCount {lam : Fin n → ℤ} {lev : Fin n → ℕ} (h : IsLev lam lev) :
    IsLev lam (lowCount lev) := by
  refine ⟨fun a b hab => lowCount_le_of_le (h.1 hab), fun a b hab => h.2 a b ?_⟩
  rcases lt_trichotomy (lev a) (lev b) with h1 | h1 | h1
  · exact absurd hab (ne_of_lt (lowCount_lt_of_lt h1))
  · exact h1
  · exact absurd hab (ne_of_gt (lowCount_lt_of_lt h1))

theorem exists_compress (lam : Fin n → ℤ) (lev : Fin n → ℕ) (h : IsLev lam lev) :
    ∃ l : Fin n → Fin n, (IsLev lam fun a => (l a : ℕ)) ∧ (muQ lam fun a => (l a : ℕ)) = muQ lam lev := by
  exact ⟨fun a => ⟨lowCount lev a, lowCount_lt lev a⟩, isLev_lowCount h, muQ_lowCount lam lev⟩

theorem muQ_mem_harmSet {lam : Fin n → ℤ} {lev : Fin n → ℕ} (h : IsLev lam lev) :
    muQ lam lev ∈ harmSet lam := by
  obtain ⟨l, hl, he⟩ := exists_compress lam lev h
  unfold harmSet
  rw [Finset.mem_image]
  refine ⟨l, ?_, he⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hl

end GlobalTheory.CompanionTheory.LevelCompress
end

section

namespace GlobalTheory.CompanionTheory.PairMult

section Powers

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem epowLeft_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    PositivityTheory.RgBcC.RealD.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [PositivityTheory.RgBcC.RealD.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [PositivityTheory.RgBcC.RealD.epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem epowRight_eq_pow (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    Formalism.REAL.epow E m a b =
      ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ m ih =>
    simp only [Formalism.REAL.epow, pow_succ, Matrix.mul_apply, Matrix.of_apply, ih]

theorem etr_eq_gelA (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) :
    Formalism.REAL.etr E m = PositivityTheory.RgBcC.RealD.gelA E m := by
  simp only [Formalism.REAL.etr, PositivityTheory.RgBcC.RealD.gelA, epowLeft_eq_pow, epowRight_eq_pow]

end Powers

end GlobalTheory.CompanionTheory.PairMult
end

section

open scoped BigOperators
open PositivityTheory.RgBcC.RealD (epow gelA)

namespace GlobalTheory.CompanionTheory.ModelS

theorem commute_epow_of_units {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V)
    (hT : ∀ a b, T * E a b = E a b * T) (m : ℕ) (a b : Fin n) :
    Commute T (epow E m a b) := by
  induction m generalizing a b with
  | zero =>
    change Commute T (if a = b then 1 else 0)
    split_ifs
    · exact Commute.one_right T
    · exact Commute.zero_right T
  | succ m ih =>
    change Commute T (∑ c, E a c * epow E m c b)
    exact Commute.sum_right _ _ _ fun c _ => Commute.mul_right (hT a c) (ih c b)

theorem gelA_commute_of_units : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V),
    (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m := by
  intro n V _ _ E T hT m
  have h : Commute T (gelA E m) :=
    Commute.sum_right _ _ _ fun a _ => commute_epow_of_units E T hT m a a
  exact h.eq.symm

end GlobalTheory.CompanionTheory.ModelS
end

section

open Finset
open PositivityTheory.RgBcC.RealD (epow gelA)

noncomputable section

namespace GlobalTheory.CompanionTheory.EvGel

section Dual

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def dualFam (E : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ (Module.Dual ℂ V) :=
  fun a b => (E b a).dualMap

theorem dualFam_apply (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    dualFam E a b φ v = φ (E b a v) := rfl

theorem glRel_dualFam {E : Fin n → Fin n → Module.End ℂ V} (hE : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (dualFam E) := by
  intro a b c d
  refine LinearMap.ext fun φ => LinearMap.ext fun v => ?_
  have h2 := congrArg (fun T : Module.End ℂ V => φ (T v)) (hE d c b a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dualFam_apply]
  by_cases h1 : b = c <;> by_cases h3 : d = a
  · subst h1; subst h3; simpa [dualFam_apply] using h2
  · subst h1; simpa [dualFam_apply, h3, Ne.symm h3] using h2
  · subst h3; simpa [dualFam_apply, h1, Ne.symm h1] using h2
  · simpa [dualFam_apply, h1, h3, Ne.symm h1, Ne.symm h3] using h2

theorem pow_dualFam (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    ((Matrix.of (dualFam E) : Matrix (Fin n) (Fin n) (Module.End ℂ (Module.Dual ℂ V))) ^ m) a b φ v =
      φ (((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) b a v) := by
  induction m generalizing a b φ v with
  | zero =>
    by_cases h : a = b
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  | succ m ih =>

    rw [pow_succ', pow_succ, Matrix.mul_apply, Matrix.mul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Module.End.mul_apply, Matrix.of_apply, dualFam_apply, ih]

end Dual

theorem epow_eq_pow {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp only [epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem ev_gelA : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ),
    (∀ a b, b < a → ∀ v, ev (E a b v) = 0) → (∀ a v, ev (E a a v) = x a * ev v) →
    ∀ (m : ℕ) (v : V), ev (gelA E m v) =
      GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v := by
  intro n V _ _ E hE ev x hlow hdiag m v
  have hHW : Formalism.REAL.IsHW (dualFam E) x ev :=
    ⟨fun a => LinearMap.ext fun w => by simp [dualFam_apply, hdiag],
      fun a b hab => LinearMap.ext fun w => by simpa [dualFam_apply] using hlow b a hab w⟩
  have h1 := GlobalTheory.PhiEigenfun.trace_pow_hw (dualFam E) x ev (glRel_dualFam hE) hHW m
  have h2 := congrArg (fun φ : Module.Dual ℂ V => φ v) h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pow_dualFam, smul_eq_mul] at h2
  have hval : GlobalTheory.Dec.gelfVal (fun a : Fin n => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m =
      ∑ a, ∑ b, (Formalism.REAL.Amat (Formalism.REAL.lsh x) ^ m) a b := by
    have : (fun c : Fin n => x c + ((n : ℂ) - 1) / 2 - ((c : ℕ) : ℂ) + ((n : ℂ) - 1) / 2) = Formalism.REAL.lsh x := by
      funext c
      simp only [Formalism.REAL.lsh]
      ring
    rw [GlobalTheory.Dec.gelfVal, this]

  rw [hval, ← h2, gelA, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [epow_eq_pow]

end GlobalTheory.CompanionTheory.EvGel
end
end

section

open Matrix Finset
open PositivityTheory.RgBcC.RealD (epow gelA)

namespace GlobalTheory.CompanionTheory.ModelS

theorem epow_eq_pow_of {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero =>
      change (if a = b then 1 else 0) = _
      simp only [pow_zero, Matrix.one_apply]
  | succ m ih =>
      change (∑ c, E a c * epow E m c b) = _
      simp only [pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem gelA_central : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E →
    ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  intro n V _ _ E hE m a b
  rw [eq_comm, ← sub_eq_zero]
  delta gelA
  simp only [epow_eq_pow_of]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [GlobalTheory.SmoothForms.comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, sub_self]

end GlobalTheory.CompanionTheory.ModelS
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.jacquet_fixed_first_condition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | exact GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul | (intros; apply GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul <;> assumption)
end
