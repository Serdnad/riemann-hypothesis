module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle037
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle556
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.LevCrt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {Q : Type} [CommGroup Q]

theorem mulle1 {A : Type} [CommRing A] (I J : Ideal A) : I * J ≤ I := Ideal.mul_le_inf.trans inf_le_left

theorem mulle2 {A : Type} [CommRing A] (I J : Ideal A) : I * J ≤ J := Ideal.mul_le_inf.trans inf_le_right

def iSub (D : Datum p) (I : Ideal (𝓞 D.F)) : Submodule D.O D.La :=
  Submodule.span D.O {z | ∃ c ∈ I, ∃ z' : D.La, z = algebraMap (𝓞 D.F) D.O c • z'}

theorem smul_mem_iSub {I : Ideal (𝓞 D.F)} {c : 𝓞 D.F} (hc : c ∈ I) (z : D.La) :
    algebraMap (𝓞 D.F) D.O c • z ∈ iSub D I :=
  Submodule.subset_span ⟨c, hc, z, rfl⟩

theorem iSub_mono {I J : Ideal (𝓞 D.F)} (h : I ≤ J) : iSub D I ≤ iSub D J :=
  Submodule.span_mono (by rintro _ ⟨c, hc, z, rfl⟩; exact ⟨c, h hc, z, rfl⟩)

theorem smul_mem_iSub_mul {I J : Ideal (𝓞 D.F)} {a : 𝓞 D.F} (ha : a ∈ I) {y : D.La} (hy : y ∈ iSub D J) :
    algebraMap (𝓞 D.F) D.O a • y ∈ iSub D (I * J) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z, rfl⟩ := hx
    rw [smul_smul, ← map_mul]
    exact smul_mem_iSub (Ideal.mul_mem_mul ha hc) z
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [smul_smul, Algebra.commutes, ← smul_smul]
    exact Submodule.smul_mem _ _ hx

theorem mem_iSub_span_nat (n : ℕ) (x : D.La) :
    x ∈ iSub D (Ideal.span {(n : 𝓞 D.F)}) ↔ ∃ y, x = n • y := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, z, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1 hc
      exact ⟨algebraMap (𝓞 D.F) D.O d • z, by
        rw [map_mul, map_natCast, ← smul_smul, Nat.cast_smul_eq_nsmul]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by rw [smul_add]⟩
    | smul o x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨o • a, by rw [smul_comm]⟩
  · rintro ⟨y, rfl⟩
    have := smul_mem_iSub (D := D) (Ideal.mem_span_singleton_self (n : 𝓞 D.F)) y
    rwa [map_natCast, Nat.cast_smul_eq_nsmul] at this

def IsIdealLev (D : Datum p) (act : D.O → Q → Q) (I : Ideal (𝓞 D.F)) (f : D.La → Q) : Prop :=
  (∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
    (∀ x, f x = 1 ↔ x ∈ iSub D I) ∧
    ∀ g, (∀ c ∈ I, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, f y = g

theorem lev_top (act : D.O → Q → Q) (hm : ∀ c a b, act c (a * b) = act c a * act c b)
    (h1 : ∀ a, act 1 a = a) : IsIdealLev D act ⊤ (fun _ => 1) := by
  refine ⟨fun _ _ => by simp, fun c _ => ?_, fun x => ?_, fun g hg => ⟨0, ?_⟩⟩
  · exact Eq.symm (by simpa using hm c 1 1)
  · have := smul_mem_iSub (D := D) (I := ⊤) (c := 1) trivial x
    rw [map_one, one_smul] at this
    simpa using this
  · have := hg 1 trivial
    rw [map_one, h1] at this
    exact this.symm

theorem lev_mul (act : D.O → Q → Q) (hm : ∀ c a b, act c (a * b) = act c a * act c b)
    (h1 : ∀ a, act 1 a = a) (hc : ∀ b c a, act (b * c) a = act b (act c a))
    (hadd : ∀ b c a, act (b + c) a = act b a * act c a) {I J : Ideal (𝓞 D.F)} (hIJ : I ⊔ J = ⊤)
    {f g : D.La → Q} (hf : IsIdealLev D act I f) (hg : IsIdealLev D act J g) :
    IsIdealLev D act (I * J) (fun x => f x * g x) := by
  obtain ⟨fa, fs, fk, fo⟩ := hf
  obtain ⟨ga, gs, gk, go⟩ := hg
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hIJ)
  have hone : ∀ c, act c 1 = 1 := fun c => by simpa using hm c 1 1
  have hsplit : ∀ u, act (algebraMap (𝓞 D.F) D.O a) u * act (algebraMap (𝓞 D.F) D.O b) u = u := fun u => by
    rw [← hadd, ← map_add (f := _), hab, map_one, h1]
  have fI : ∀ c ∈ I, ∀ x, act (algebraMap (𝓞 D.F) D.O c) (f x) = 1 := fun c hc x => by
    rw [← fs]; exact (fk _).2 (smul_mem_iSub hc x)
  have gJ : ∀ c ∈ J, ∀ x, act (algebraMap (𝓞 D.F) D.O c) (g x) = 1 := fun c hc x => by
    rw [← gs]; exact (gk _).2 (smul_mem_iSub hc x)
  refine ⟨fun x y => ?_, fun c x => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun u hu => ?_⟩
  · simp only [fa, ga]; exact mul_mul_mul_comm _ _ _ _
  · simp only [fs, gs, hm]
  · have hx' : f x * g x = 1 := hx
    have e1 : f x = 1 := by
      have h := congrArg (act (algebraMap (𝓞 D.F) D.O b)) hx'
      rw [hm, gJ b hb, _root_.mul_one, hone] at h
      rw [← hsplit (f x), fI a ha, h, _root_.mul_one]
    have e2 : g x = 1 := by rwa [e1, _root_.one_mul] at hx'
    have hxx : x = algebraMap (𝓞 D.F) D.O a • x + algebraMap (𝓞 D.F) D.O b • x := by
      rw [← add_smul, ← map_add (f := _), hab, map_one, one_smul]
    rw [hxx]
    refine Submodule.add_mem _ (smul_mem_iSub_mul ha ((gk x).1 e2)) ?_
    rw [_root_.mul_comm I J]
    exact smul_mem_iSub_mul hb ((fk x).1 e1)
  · show f x * g x = 1
    have l1 : I * J ≤ I := mulle1 I J
    have l2 : I * J ≤ J := mulle2 I J
    rw [(fk x).2 (iSub_mono l1 hx), (gk x).2 (iSub_mono l2 hx), _root_.mul_one]
  · have k1 : ∀ c ∈ I, ∀ d ∈ J, act (algebraMap (𝓞 D.F) D.O c) (act (algebraMap (𝓞 D.F) D.O d) u) = 1 :=
      fun c hc' d hd => by rw [← hc, ← map_mul]; exact hu _ (Ideal.mul_mem_mul hc' hd)
    have k2 : ∀ c ∈ I, ∀ d ∈ J, act (algebraMap (𝓞 D.F) D.O d) (act (algebraMap (𝓞 D.F) D.O c) u) = 1 :=
      fun c hc' d hd => by rw [← hc, ← map_mul, _root_.mul_comm]; exact hu _ (Ideal.mul_mem_mul hc' hd)
    obtain ⟨z, hz⟩ := fo (act (algebraMap (𝓞 D.F) D.O b) u) fun c hc' => k1 c hc' b hb
    obtain ⟨y, hy⟩ := go (act (algebraMap (𝓞 D.F) D.O a) u) fun d hd => k2 a ha d hd
    refine ⟨algebraMap (𝓞 D.F) D.O a • y + algebraMap (𝓞 D.F) D.O b • z, ?_⟩
    show f _ * g _ = u
    rw [fa, ga, fs, fs, gs, gs, fI a ha, gJ b hb, _root_.one_mul, _root_.mul_one, hz, hy]
    have s1 := hsplit (act (algebraMap (𝓞 D.F) D.O a) u)
    have s2 := hsplit (act (algebraMap (𝓞 D.F) D.O b) u)
    rw [k2 a ha b hb, _root_.mul_one] at s1
    rw [k1 a ha b hb, _root_.one_mul] at s2
    rw [s1, s2, _root_.mul_comm, hsplit]

theorem exists_lev_of_pow_mem (act : D.O → Q → Q) (hm : ∀ c a b, act c (a * b) = act c a * act c b)
    (h1 : ∀ a, act 1 a = a) (hc : ∀ b c a, act (b * c) a = act b (act c a))
    (hadd : ∀ b c a, act (b + c) a = act b a * act c a)
    (H : ∀ (w : Ideal (𝓞 D.F)) (r : ℕ), w.IsMaximal → (p : 𝓞 D.F) ∈ w → ∃ l, IsIdealLev D act (w ^ r) l)
    (r : ℕ) (I : Ideal (𝓞 D.F)) : (p : 𝓞 D.F) ^ r ∈ I → ∃ l, IsIdealLev D act I l := by
  induction I using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 =>
    intro h
    have h0 : (p : 𝓞 D.F) ^ r = 0 := by simpa using h
    exact absurd (pow_eq_zero_iff'.1 h0).1 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  | h1 hu =>
    intro _
    rw [Ideal.isUnit_iff.1 hu]
    exact ⟨_, lev_top act hm h1⟩
  | @hpr q i hq =>
    intro h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, Ideal.one_eq_top]
      exact ⟨_, lev_top act hm h1⟩
    · have hp : q.IsPrime := Ideal.isPrime_of_prime hq
      exact H q i (hp.isMaximal hq.ne_zero) (hp.mem_of_pow_mem r (Ideal.pow_le_self hi.ne' h))
  | @hcp x y hxy hx hy =>
    intro h
    obtain ⟨f, hf⟩ := hx (mulle1 x y h)
    obtain ⟨g, hg⟩ := hy (mulle2 x y h)
    have : x ⊔ y = ⊤ :=
      Ideal.isUnit_iff.1 (hxy (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))
    exact ⟨_, lev_mul act hm h1 hc hadd this hf hg⟩

theorem exists_pLevel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (Q : Type) [CommGroup Q] (act : D.O → Q → Q), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ a, act 1 a = a) → (∀ b c a, act (b * c) a = act b (act c a)) → (∀ b c a, act (b + c) a = act b a * act c a) → (∀ (w : Ideal (𝓞 D.F)) (r : ℕ), w.IsMaximal → (p : 𝓞 D.F) ∈ w → ∃ l : D.La → Q, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = act c (l x)) ∧ (∀ x, l x = 1 ↔ x ∈ wSub D w r) ∧ ∀ g, (∀ c ∈ w ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g) → ∀ r : ℕ, ∃ f : D.La → Q, (∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g) := by
  intro p _ D Q _ act hm h1 hc hadd H r
  obtain ⟨f, fa, fs, fk, fo⟩ := exists_lev_of_pow_mem act hm h1 hc hadd H r
    (Ideal.span {((p ^ r : ℕ) : 𝓞 D.F)}) (by
      rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _)
  have hone : ∀ c, act c 1 = 1 := fun c => by simpa using hm c 1 1
  have hnat : ∀ (n : ℕ) a, act (n : D.O) a = a ^ n := fun n a => by
    induction n with
    | zero => simpa using hadd 0 0 a
    | succ n ih => rw [Nat.cast_succ, hadd, ih, h1, pow_succ]
  refine ⟨f, fa, fs, fun x => (fk x).trans (mem_iSub_span_nat _ x), fun g => ⟨fun hg => fo g ?_, ?_⟩⟩
  · intro c hc'
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1 hc'
    rw [_root_.mul_comm, map_mul, hc, map_natCast, hnat, hg, hone]
  · rintro ⟨x, rfl⟩
    rw [← hnat, ← fs, Nat.cast_smul_eq_nsmul]
    exact (fk _).2 ((mem_iSub_span_nat _ _).2 ⟨x, rfl⟩)

end GlobalTheory.UPel.HT.EtLev.LevCrt
end
end

section

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem isEtPlace_of_isUnit (b : Base D R) (hp : IsUnit (p : R)) (w0 : Ideal (𝓞 D.F)) (h : w0.IsMaximal)
    (hw : (p : 𝓞 D.F) ∈ w0) : IsEtPlace b w0 := by
  refine ⟨h, hw, fun i => ?_, fun k _ _ β φ _ => ?_⟩
  · refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, hw, by simp⟩) hp
  · exfalso
    have := hp.map β
    simp at this

end GlobalTheory.UPel.HT.EtLev
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.KS

namespace GlobalTheory.KS.PowPB

theorem powMap_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) :
    powMap f φ hφ m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem powMap_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) :
    powMap f φ hφ m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _

theorem pow_left_hom_ext {S : Scheme.{0}} {A : Over S} {m : ℕ} {T : Scheme.{0}} (g₁ g₂ : T ⟶ (pow A m).left)
    (hh : g₁ ≫ (pow A m).hom = g₂ ≫ (pow A m).hom) (hi : ∀ i, g₁ ≫ (pr A i).left = g₂ ≫ (pr A i).left) :
    g₁ = g₂ := by
  let u₁ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₁ rfl
  let u₂ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₂ (by simpa using hh.symm)
  have : u₁ = u₂ := Pi.hom_ext _ _ (fun i => by
    ext
    simpa [u₁, u₂] using hi i)
  exact congrArg CommaMorphism.left this

noncomputable def liftPow {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : T ⟶ (pow A' m).left :=
  (Pi.lift (fun i : Fin m => (Over.homMk (H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w))
    (H.lift_snd _ _ _) : Over.mk b ⟶ A')) : Over.mk b ⟶ pow A' m).left

theorem liftPow_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : liftPow H m a b w ≫ (pow A' m).hom = b := by
  unfold liftPow
  exact Over.w _

theorem liftPow_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) (i : Fin m) :
    liftPow H m a b w ≫ (pr A' i).left = H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w) := by
  unfold liftPow
  rw [← Over.comp_left, Pi.lift_comp_π]
  rfl

theorem powMap_isPullback : ∀ (S S' : Scheme.{0}) (A : Over S) (A' : Over S') (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f), IsPullback φ A'.hom A.hom f →
    ∀ m : ℕ, IsPullback (powMap f φ hφ m) (pow A' m).hom (pow A m).hom f := by
  intro S S' A A' f φ hφ H m
  refine ⟨⟨powMap_w f φ hφ m⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => liftPow H m s.fst s.snd s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    apply pow_left_hom_ext
    · rw [Category.assoc, powMap_w, ← Category.assoc, liftPow_w, s.condition]
    · intro i
      rw [Category.assoc, powMap_pr, ← Category.assoc, liftPow_pr, H.lift_fst]
  · intro s
    exact liftPow_w H m _ _ _
  · intro s u h₁ h₂
    apply pow_left_hom_ext
    · rw [h₂, liftPow_w]
    · intro i
      rw [liftPow_pr]
      apply H.hom_ext
      · rw [H.lift_fst, Category.assoc, ← powMap_pr f φ hφ, ← Category.assoc, h₁]
      · rw [H.lift_snd, Category.assoc, Over.w, h₂]

end GlobalTheory.KS.PowPB
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

def secPush (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) : Over.mk (T.hom ≫ f) ⟶ o.A :=
  Over.homMk (u.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]; rfl)

theorem secPush_left (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) :
    (secPush m T u).left = u.left ≫ m.φ := rfl

theorem secPush_inj (m : ObjMap o' o f) (T : Over S') {u v : T ⟶ o'.A}
    (h : secPush m T u = secPush m T v) : u = v := by
  have h' := congrArg CommaMorphism.left h
  exact Over.OverMorphism.ext (m.cart.1.hom_ext h' (by rw [Over.w, Over.w]))

theorem secPush_mul (m : ObjMap o' o f) (T : Over S') (u v : T ⟶ o'.A) :
    secPush m T (u * v) = secPush m T u * secPush m T v := by
  apply Over.OverMorphism.ext
  rw [secPush_left]
  exact (m.cart.2 T u v (secPush m T u) (secPush m T v) rfl rfl).symm

theorem secPush_one (m : ObjMap o' o f) (T : Over S') :
    secPush m T 1 = 1 := by
  have h := secPush_mul m T 1 1
  rw [_root_.mul_one] at h
  exact (_root_.mul_eq_left.mp h.symm)

theorem secPush_act (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) (c : D.O) :
    secPush m T (u ≫ o'.act.act c) = secPush m T u ≫ o.act.act c := by
  apply Over.OverMorphism.ext
  simp only [secPush_left, Over.comp_left, Category.assoc, m.act]

theorem isEtLev_exists_pull : ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S} (m : ObjMap o' o f) {w0 : Ideal (𝓞 D.F)} {r : ℕ} {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}, IsEtLev o w0 r lv → ∃ lv' : D.La → (𝟙_ (Over S') ⟶ o'.A), IsEtLev o' w0 r lv' ∧ ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := by
  intro p _ D R _ b N S S' s s' o o' f m w0 r lv hlv
  have hu : ∀ {X : Scheme.{0}} (T : Over X), (toUnit T).left = T.hom := fun T =>
    (Category.comp_id _).symm.trans (Over.w (toUnit T))
  have wα : ∀ y, (f ≫ (lv y).left) ≫ o.A.hom = 𝟙 S' ≫ f := fun y => by
    rw [Category.assoc, Over.w]; simp
  let lv' : D.La → (𝟙_ (Over S') ⟶ o'.A) := fun y =>
    Over.homMk (m.cart.1.lift (f ≫ (lv y).left) (𝟙 S') (wα y)) (m.cart.1.lift_snd _ _ _)
  have hα : ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := fun y => m.cart.1.lift_fst _ _ _
  have hP1 : ∀ y, secPush m (𝟙_ (Over S')) (lv' y) =
      toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ lv y := fun y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, hα, Over.comp_left, hu]; simp
  have hP : ∀ (T : Over S') y, secPush m T (toUnit T ≫ lv' y) =
      toUnit (Over.mk (T.hom ≫ f)) ≫ lv y := fun T y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, Over.comp_left, Category.assoc, hα, Over.comp_left, hu, hu]; simp
  refine ⟨lv', ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x' => ?_⟩, hα⟩
  · apply secPush_inj m
    rw [secPush_mul, hP1, hP1, hP1, hlv.1, MonObj.comp_mul]
  · apply secPush_inj m
    rw [secPush_act, hP1, hP1, hlv.2.1, Category.assoc]
  · apply secPush_inj m
    rw [hP1, secPush_one, hlv.2.2.1 x hx, MonObj.comp_one]
  · obtain ⟨hinj, hsurj⟩ := hlv.2.2.2 k (x' ≫ f)
    refine ⟨fun y hy => hinj y ?_, fun g hg => ?_⟩
    · have h := congrArg (secPush m (Over.mk x')) hy
      rw [hP, secPush_one] at h
      exact h
    · obtain ⟨y, hy⟩ := hsurj (secPush m (Over.mk x') g) (fun c hc => by
        rw [← secPush_act, hg c hc, secPush_one])
      refine ⟨y, secPush_inj m _ ?_⟩
      rw [hP]
      exact hy

end GlobalTheory.UPel.HT.EtLev
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def IsEtLevOver {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : Prop :=
  (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) ∧
    (∀ x ∈ wSub D w0 r, l x = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = 1 → y ∈ wSub D w0 r) ∧
      ∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
        ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = g

def ptOf {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {T : Scheme.{0}} {t : T ⟶ S} {s₁ : T ⟶ Sp R} {o : Obj b N s}
    {o₁ : Obj b N s₁} (m : ObjMap o₁ o t) (l : 𝟙_ (Over T) ⟶ o₁.A) : Over.mk t ⟶ o.A :=
  Over.homMk (l.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w l]
    exact Category.id_comp t)

def levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) : D.La :=
  Function.surjInv (Submodule.mkQ_surjective (wSub D w0 r)) (g ((wSub D w0 r).mkQ y))

theorem mkQ_levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) :
    (wSub D w0 r).mkQ (levAct g y) = g ((wSub D w0 r).mkQ y) :=
  Function.surjInv_eq _ _

end GlobalTheory.UPel.HT.EtLev
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtC GlobalTheory.UPel.HT GlobalTheory.PELU GlobalTheory.KS
open scoped TensorProduct Matrix

namespace GlobalTheory.KS.Leray

theorem isProper_pow_hom {S : Scheme.{0}} (A : Over S) (hA : IsProper A.hom) (m : ℕ) :
    IsProper (GlobalTheory.KS.pow A m).hom :=
  GlobalTheory.FibrePowerProper.isProper_fan_pt m (fun _ => A) (fun _ => hA) (limit.cone _) (limit.isLimit _)

end GlobalTheory.KS.Leray
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (M : Matrix ι ι (Ainf p O)), IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) M → (∀ c : ι → Ainf p O, ∃ v : ι → Ainf p O, ∀ i, v i - M.mulVec (fun j => WittVector.frobenius (v j)) i = c i) ∧ ∀ v : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ v i - M.mulVec (fun j => WittVector.frobenius (v j)) i) → ∀ i, Sandwich.mu ε ∣ v i := by
  first | exact @GlobalTheory.WSolve.main | exact GlobalTheory.WSolve.main | (intros; apply GlobalTheory.WSolve.main <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_unit_matrix_lift_mod_tau_ainf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι F.B), IsUnit U → ∃ V : Matrix ι ι (Ainf p O), IsUnit V ∧ ∀ i j, F.τ ∣ U i j - F.a (V i j) := by
  first | exact @GlobalTheory.WinLift.exists_unit_lift_mod_tau | exact GlobalTheory.WinLift.exists_unit_lift_mod_tau | (intros; apply GlobalTheory.WinLift.exists_unit_lift_mod_tau <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.frobenius_lift_solves_mod_frobXi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (F0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), IsUnit V → (∀ i m, Sandwich.mu ε ∣ (F0.map WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m) → (∀ i m, WittVector.fontaineTheta O p (F0 (Sum.inl i) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε)) * F0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * F0 i m := by
  first | exact @GlobalTheory.WinLift.frob_lift_dvd | exact GlobalTheory.WinLift.frob_lift_dvd | (intros; apply GlobalTheory.WinLift.frob_lift_dvd <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.frobenius_xi_eq_p_mul_unit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∃ u : F.B, IsUnit u ∧ F.τ ∣ u - 1 ∧ F.a (WittVector.frobenius (xi ε)) = p * u := by
  first | exact @GlobalTheory.QLog.BFrame.frobenius_xi_unit | exact GlobalTheory.QLog.BFrame.frobenius_xi_unit | (intros; apply GlobalTheory.QLog.BFrame.frobenius_xi_unit <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.isNilpotent_blockFrobeniusXi_ainf_of_frameBlockP : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := by
  first | exact @GlobalTheory.WinLift.isNil_V_blk_frob_xi | exact GlobalTheory.WinLift.isNil_V_blk_frob_xi | (intros; apply GlobalTheory.WinLift.isNil_V_blk_frob_xi <;> assumption)
end
