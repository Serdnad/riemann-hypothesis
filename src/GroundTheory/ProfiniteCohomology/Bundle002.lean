module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Instances.AddCircle.Defs
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

def Supernatural : Type := Nat.Primes → ℕ∞

namespace Supernatural

def mk (f : Nat.Primes → ℕ∞) : Supernatural := f

def exp (a : Supernatural) (p : Nat.Primes) : ℕ∞ := a p

private theorem exp_ext {a b : Supernatural} (h : ∀ p, a.exp p = b.exp p) : a = b :=
  funext h

noncomputable instance : CompleteLattice Supernatural := inferInstanceAs (CompleteLattice (Nat.Primes → ℕ∞))

theorem le_def {a b : Supernatural} : a ≤ b ↔ ∀ p, a.exp p ≤ b.exp p := Iff.rfl

@[simp] theorem exp_iSup {ι : Sort*} (f : ι → Supernatural) (p : Nat.Primes) :
    (⨆ i, f i).exp p = ⨆ i, (f i).exp p :=
  iSup_apply (f := fun i => (f i : Nat.Primes → ℕ∞)) (a := p)

instance : One Supernatural := ⟨mk fun _ => 0⟩

instance : Mul Supernatural := ⟨fun a b => mk fun p => a.exp p + b.exp p⟩

@[simp] theorem exp_mul (a b : Supernatural) (p : Nat.Primes) :
    (a * b).exp p = a.exp p + b.exp p := rfl

instance : CommMonoid Supernatural where
  mul_assoc a b c := by exact exp_ext fun p => add_assoc (a.exp p) (b.exp p) (c.exp p)
  one_mul a := by exact exp_ext fun p => zero_add (a.exp p)
  mul_one a := by exact exp_ext fun p => add_zero (a.exp p)
  mul_comm a b := by exact exp_ext fun p => add_comm (a.exp p) (b.exp p)

theorem dvd_iff_le {a b : Supernatural} : a ∣ b ↔ a ≤ b := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [le_def]
    intro p
    simp
  · intro h
    refine ⟨mk fun p => b.exp p - a.exp p, ?_⟩
    exact exp_ext fun p => (add_tsub_cancel_of_le (le_def.mp h p)).symm

def ofNat (n : ℕ) : Supernatural := mk fun p => (n.factorization p : ℕ∞)

@[simp] theorem exp_ofNat (n : ℕ) (p : Nat.Primes) : (ofNat n).exp p = n.factorization p := rfl

theorem ofNat_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat (m * n) = ofNat m * ofNat n := by
  refine exp_ext fun p => ?_
  simp [Nat.factorization_mul hm hn]

theorem ofNat_dvd_ofNat {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat m ∣ ofNat n ↔ m ∣ n := by
  rw [dvd_iff_le, le_def, ← Nat.factorization_le_iff_dvd hm hn, Finsupp.le_def]
  constructor
  · intro h q
    by_cases hq : q.Prime
    · have h' : ((m.factorization q : ℕ) : ℕ∞) ≤ n.factorization q := h ⟨q, hq⟩
      exact_mod_cast h'
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  · intro h p
    show ((m.factorization p : ℕ) : ℕ∞) ≤ n.factorization p
    exact_mod_cast h p

theorem ofNat_prime_dvd_iff (p : Nat.Primes) (a : Supernatural) :
    ofNat p ∣ a ↔ 1 ≤ a.exp p := by
  have h1 : (ofNat p).exp p = 1 := by
    rw [exp_ofNat]
    simp [p.prop.factorization_self]
  rw [dvd_iff_le, le_def]
  constructor
  · intro h
    exact h1 ▸ h p
  · intro h q
    by_cases hq : q = p
    · subst hq
      exact h1 ▸ h
    · have hq' : (p : ℕ) ≠ q := fun e => hq (Subtype.ext e.symm)
      simp [p.prop.factorization, hq']

theorem ofNat_prime_dvd_iSup_iff (p : Nat.Primes) {ι : Sort*} (f : ι → Supernatural) :
    ofNat p ∣ ⨆ i, f i ↔ ∃ i, ofNat p ∣ f i := by
  simp only [ofNat_prime_dvd_iff p, Order.one_le_iff_ne_zero]
  rw [exp_iSup]
  constructor
  · intro h
    by_contra h'
    simp only [not_exists, ne_eq, not_not] at h'
    exact h (le_antisymm (iSup_le fun i => (h' i).le) zero_le)
  · rintro ⟨i, hi⟩ h
    exact hi (le_antisymm (h ▸ le_iSup (fun i => (f i).exp p) i) zero_le)

theorem iSup_mul_iSup {ι : Sort*} {f g : ι → Supernatural}
    (h : ∀ i j, ∃ k, f i ≤ f k ∧ g j ≤ g k) :
    (⨆ i, f i) * (⨆ i, g i) = ⨆ i, f i * g i := by
  refine exp_ext fun p => ?_
  simp only [exp_mul, exp_iSup]
  exact ENat.iSup_add_iSup fun i j => (h i j).imp fun k hk =>
    add_le_add (le_def.mp hk.1 p) (le_def.mp hk.2 p)

end Supernatural

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsProPGroup (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ (U : Subgroup G))

theorem isProPGroup_iff {p : ℕ} :
    IsProPGroup p G ↔ ∀ U : OpenNormalSubgroup G, ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ U := by
  refine forall_congr' fun U => ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ (U : Subgroup G))
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    exact hk
  · induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := h g
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩


omit [TopologicalSpace G] in
theorem isPGroup_map_mk_iff {p : ℕ} (H U : Subgroup G) [U.Normal] :
    IsPGroup p (H.map (QuotientGroup.mk' U)) ↔ ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ U := by
  constructor
  · intro hp h hh
    obtain ⟨k, hk⟩ := hp ⟨QuotientGroup.mk' U h, Subgroup.mem_map_of_mem _ hh⟩
    refine ⟨k, ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply] at hk'
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk'
  · rintro h ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, hk⟩ := h g hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_subgroupOf_le {H : Subgroup G} (V : OpenNormalSubgroup H) :
    ∃ U : OpenNormalSubgroup G, (U : Subgroup G).subgroupOf H ≤ (V : Subgroup H) := by
  obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp V.toOpenSubgroup.isOpen
  have h1W : (1 : G) ∈ W := by
    have : (1 : H) ∈ Subtype.val ⁻¹' W := hWV ▸ V.one_mem
    simpa using this
  obtain ⟨U, hUW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
  refine ⟨U, fun x hx => ?_⟩
  have : (x : G) ∈ W := hUW hx
  have : x ∈ Subtype.val ⁻¹' W := this
  rw [hWV] at this
  exact this

theorem isProPGroup_subgroup_iff {p : ℕ} {H : Subgroup G} :
    IsProPGroup p H ↔ ∀ U : OpenNormalSubgroup G, ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ U := by
  rw [isProPGroup_iff]
  constructor
  · intro hH U h hh
    let U' : OpenNormalSubgroup H :=
      { toSubgroup := (U : Subgroup G).subgroupOf H
        isOpen' := Subgroup.subgroupOf_isOpen H (U : Subgroup G) U.toOpenSubgroup.isOpen
        isNormal' := inferInstance }
    obtain ⟨k, hk⟩ := hH U' ⟨h, hh⟩
    exact ⟨k, hk⟩
  · intro hH V g
    obtain ⟨U, hU⟩ := exists_subgroupOf_le V
    obtain ⟨k, hk⟩ := hH U g g.2
    exact ⟨k, hU (show (g ^ p ^ k : H) ∈ (U : Subgroup G).subgroupOf H from hk)⟩

theorem isProPGroup_subgroup_iff_isPGroup_map {p : ℕ} {H : Subgroup G} :
    IsProPGroup p H ↔
      ∀ U : OpenNormalSubgroup G, IsPGroup p (H.map (QuotientGroup.mk' (U : Subgroup G))) := by
  rw [isProPGroup_subgroup_iff]
  exact forall_congr' fun U => (isPGroup_map_mk_iff H (U : Subgroup G)).symm

theorem isProPGroup_bot (p : ℕ) : IsProPGroup p (⊥ : Subgroup G) := by
  rw [isProPGroup_subgroup_iff]
  intro U h hh
  rw [Subgroup.mem_bot.mp hh]
  exact ⟨0, by simp⟩

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Topology

def QZ : Type := AddCircle (1 : ℚ)

namespace QZ

instance : AddCommGroup QZ := inferInstanceAs (AddCommGroup (AddCircle (1 : ℚ)))

instance : TopologicalSpace QZ := ⊥

instance : DiscreteTopology QZ := ⟨rfl⟩

instance : IsTopologicalAddGroup QZ where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def toAddCircle : QZ ≃+ AddCircle (1 : ℚ) := AddEquiv.refl _

def mk (q : ℚ) : QZ := toAddCircle.symm (q : AddCircle (1 : ℚ))

theorem mk_surjective : Function.Surjective mk := fun x =>
  QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) (toAddCircle x)

@[simp] theorem mk_add (p q : ℚ) : mk (p + q) = mk p + mk q := by
  simp [mk]

@[simp] theorem mk_zero : mk 0 = 0 := by simp [mk]

theorem mk_eq_zero_iff (q : ℚ) : mk q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  simp only [mk, AddEquivClass.map_eq_zero_iff, AddCircle.coe_eq_zero_iff, zsmul_eq_mul, mul_one]

end QZ

abbrev QZDual (A : Type*) [AddCommGroup A] [TopologicalSpace A] : Type _ := A →ₜ+ QZ

namespace QZDual

variable {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
  [TopologicalSpace B] [AddCommGroup C] [TopologicalSpace C]


end QZDual

end GroundTheory.ProfCoh
end
