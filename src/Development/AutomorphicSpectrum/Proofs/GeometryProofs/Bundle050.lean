module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc

open Mdl

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem mem_of_isLocAt {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω} (hq : q.IsPrime)
    (hR : IsLocAt A q R) {a : Ω} (ha : a ∈ A) : a ∈ R :=
  (hR a).2 ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simpa using ha⟩

theorem unit_of_not_mem {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω}
    (hR : IsLocAt A q R) {a : A} (ha : a ∉ q) : (a : Ω) ≠ 0 ∧ (a : Ω)⁻¹ ∈ R := by
  have h0 : (a : Ω) ≠ 0 := fun h => ha (by
    have e : a = 0 := Subtype.ext h
    rw [e]
    exact q.zero_mem)
  exact ⟨h0, (hR _).2 ⟨a, ha, by rw [mul_inv_cancel₀ h0]; exact A.one_mem⟩⟩

theorem not_mem_of_unit {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω}
    (hR : IsLocAt A q R) {b : A} (h0 : (b : Ω) ≠ 0) (hi : (b : Ω)⁻¹ ∈ R) : b ∉ q := by
  obtain ⟨s, hs, hsb⟩ := (hR _).1 hi
  intro hb
  apply hs
  have e : s = ⟨_, hsb⟩ * b := Subtype.ext (by
    rw [Subalgebra.coe_mul]
    exact (inv_mul_cancel_right₀ h0 _).symm)
  rw [e]
  exact q.mul_mem_left _ hb

theorem invAdj_le_of {A C : Subalgebra ℚ Ω} {h : Ω} (hA : A ≤ C) (hh : h⁻¹ ∈ C) : invAdj A h ≤ C :=
  Algebra.adjoin_le (by
    rintro x (rfl | hx)
    · exact hh
    · exact hA hx)

theorem invAdj_le_mul {A : Subalgebra ℚ Ω} {g s : Ω} (hs : s ∈ A) (h0 : g * s ≠ 0) :
    invAdj A g ≤ invAdj A (g * s) := by
  refine invAdj_le_of (le_invAdj _ _) ?_
  have hs0 : s ≠ 0 := right_ne_zero_of_mul h0
  have hg0 : g ≠ 0 := left_ne_zero_of_mul h0
  have e : g⁻¹ = s * (g * s)⁻¹ := by field_simp
  rw [e]
  exact Subalgebra.mul_mem _ (le_invAdj _ _ hs) (inv_mem_invAdj _ _)

theorem exists_den {A B : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω} (hq : q.IsPrime)
    (hR : IsLocAt A q R) (hB : B.FG) (hBR : ∀ b ∈ B, b ∈ R) : ∃ g : A, g ∉ q ∧ B ≤ invAdj A g := by
  classical
  have key : ∀ T : Finset Ω, (∀ b ∈ T, b ∈ R) → ∃ g : A, g ∉ q ∧ ∀ b ∈ T, b ∈ invAdj A g := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
    | insert b T _ ih =>
      intro hT
      obtain ⟨g₁, hg₁, hg₁T⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨s, hs, hsb⟩ := (hR b).1 (hT b (Finset.mem_insert_self _ _))
      have hmul : g₁ * s ∉ q := fun h => (hq.mem_or_mem h).elim hg₁ hs
      have h0 : (g₁ : Ω) * s ≠ 0 := (unit_of_not_mem hR hmul).1
      have hs0 : (s : Ω) ≠ 0 := right_ne_zero_of_mul h0
      have hg0 : (g₁ : Ω) ≠ 0 := left_ne_zero_of_mul h0
      refine ⟨g₁ * s, hmul, ?_⟩
      rw [Subalgebra.coe_mul]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : x = ((s : Ω) * x) * g₁ * ((g₁ : Ω) * s)⁻¹ := by field_simp
        rw [e]
        exact Subalgebra.mul_mem _
          (Subalgebra.mul_mem _ (le_invAdj _ _ hsb) (le_invAdj _ _ g₁.2)) (inv_mem_invAdj _ _)
      · exact invAdj_le_mul s.2 h0 (hg₁T x hx)
  obtain ⟨S, rfl⟩ := hB
  obtain ⟨g, hg, hgS⟩ := key S fun b hb => hBR b (Algebra.subset_adjoin hb)
  exact ⟨g, hg, Algebra.adjoin_le fun b hb => hgS b hb⟩

theorem exists_clear {A B : Subalgebra ℚ Ω} {q : Ideal A} {q' : Ideal B} {R : Subring Ω}
    (hR : IsLocAt A q R) (hR' : IsLocAt B q' R) {g : A} {h : B} (hg : g ∉ q) (hh : h ∉ q')
    (hgh : (g : Ω) ∈ invAdj B h) : ∃ (a : B) (m : ℕ), a ∉ q' ∧ (a : Ω) = g * (h : Ω) ^ m := by
  obtain ⟨gn, gi⟩ := unit_of_not_mem hR hg
  obtain ⟨hn, hi⟩ := unit_of_not_mem hR' hh
  obtain ⟨m, hm⟩ := exists_mul_pow_mem h.2 hn hgh
  refine ⟨⟨_, hm⟩, m, not_mem_of_unit hR' (mul_ne_zero gn (pow_ne_zero _ hn)) ?_, rfl⟩
  show ((g : Ω) * (h : Ω) ^ m)⁻¹ ∈ R
  rw [mul_inv, ← inv_pow]
  exact R.mul_mem gi (R.pow_mem hi _)

theorem exists_common_loc : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A B : Subalgebra ℚ Ω) (q : Ideal A) (q' : Ideal B)
    (R : Subring Ω), A.FG → B.FG → q.IsPrime → q'.IsPrime → IsLocAt A q R → IsLocAt B q' R →
    ∃ (g : A) (h : B), g ∉ q ∧ h ∉ q' ∧ Mdl.invAdj A g = Mdl.invAdj B h := by
  intro Ω _ _ A B q q' R hA hB hq hq' hR hR'
  obtain ⟨g₀, hg₀, hBg⟩ := exists_den hq hR hB fun b hb => mem_of_isLocAt hq' hR' hb
  obtain ⟨h₀, hh₀, hAh⟩ := exists_den hq' hR' hA fun b hb => mem_of_isLocAt hq hR hb
  obtain ⟨a, m, ha, ea⟩ := exists_clear hR hR' hg₀ hh₀ (hAh g₀.2)
  obtain ⟨h, hh, eh⟩ : ∃ h : B, h ∉ q' ∧ (h : Ω) = h₀ * a :=
    ⟨h₀ * a, fun hm => (hq'.mem_or_mem hm).elim hh₀ ha, rfl⟩
  obtain ⟨a', l, ha', ea'⟩ := exists_clear hR' hR hh hg₀ (hBg h.2)
  obtain ⟨g, hg, eg⟩ : ∃ g : A, g ∉ q ∧ (g : Ω) = g₀ * a' :=
    ⟨g₀ * a', fun hm => (hq.mem_or_mem hm).elim hg₀ ha', rfl⟩
  have g0n := (unit_of_not_mem hR hg₀).1
  have h0n := (unit_of_not_mem hR' hh₀).1
  have gn := (unit_of_not_mem hR hg).1
  have hn := (unit_of_not_mem hR' hh).1
  have an := (unit_of_not_mem hR' ha).1
  have an' := (unit_of_not_mem hR ha').1
  refine ⟨g, h, hg, hh, ?_⟩

  have hAh' : invAdj B (h₀ : Ω) ≤ invAdj B h := by
    rw [eh]
    exact invAdj_le_mul a.2 (eh ▸ hn)
  have hBg' : invAdj A (g₀ : Ω) ≤ invAdj A g := by
    rw [eg]
    exact invAdj_le_mul a'.2 (eg ▸ gn)
  have g0inv : (g₀ : Ω)⁻¹ ∈ invAdj B h := by
    have e : (g₀ : Ω)⁻¹ = (h₀ : Ω) ^ m * h₀ * (h : Ω)⁻¹ := by
      rw [eh, ea]
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (le_invAdj _ _ (B.pow_mem h₀.2 _)) (le_invAdj _ _ h₀.2)) (inv_mem_invAdj _ _)
  have C1 : invAdj A (g₀ : Ω) ≤ invAdj B h := invAdj_le_of (hAh.trans hAh') g0inv
  have hinv : (h : Ω)⁻¹ ∈ invAdj A g := by
    have e : (h : Ω)⁻¹ = (g₀ : Ω) ^ l * g₀ * (g : Ω)⁻¹ := by
      rw [eg, ea']
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (le_invAdj _ _ (A.pow_mem g₀.2 _)) (le_invAdj _ _ g₀.2)) (inv_mem_invAdj _ _)
  have ginv : (g : Ω)⁻¹ ∈ invAdj B h := by
    have e : (g : Ω)⁻¹ = (g₀ : Ω)⁻¹ * ((h : Ω)⁻¹ * ((g₀ : Ω)⁻¹) ^ l) := by
      rw [eg, ea', mul_inv, mul_inv, inv_pow]
    rw [e]
    exact Subalgebra.mul_mem _ g0inv
      (Subalgebra.mul_mem _ (inv_mem_invAdj _ _) (Subalgebra.pow_mem _ g0inv _))
  exact le_antisymm (invAdj_le_of ((le_invAdj A _).trans C1) ginv)
    (invAdj_le_of (hBg.trans hBg') hinv)

end GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep

section Forms

variable {Ω : Type} [Field Ω] {N : ℕ}

theorem aeval_eq_pow_mul {σ : Type} [Fintype σ] {v w : σ → Ω} {t : Ω} (h : ∀ i, w i = t * v i)
    {G : MvPolynomial σ ℤ} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.aeval w G = t ^ d * MvPolynomial.aeval v G := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i, m i = d := by
    have := hG (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [h, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem ratEval_eq_pow_mul (x : Fin (N + 1) → Ω) {c c' : Fin (N + 1)} (hc : x c ≠ 0)
    {G : MRing (fun _ : Unit => Fin (N + 1))} {d : ℕ} (hG : G.IsHomogeneous d) :
    ratEval x c' G = (x c / x c') ^ d * ratEval x c G := by
  refine aeval_eq_pow_mul (fun i => ?_) hG
  field_simp

theorem ratEval_C (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (n : ℤ) :
    ratEval x c (MvPolynomial.C n) = (n : Ω) :=
  (MvPolynomial.aeval_C _ n).trans (eq_intCast _ n)

theorem ratEval_X_mul (x : Fin (N + 1) → Ω) (c c' : Fin (N + 1)) (H : MRing (fun _ : Unit => Fin (N + 1))) :
    ratEval x c' (MvPolynomial.X ⟨(), c⟩ * H) = x c / x c' * ratEval x c' H := by
  simp only [map_mul, MvPolynomial.aeval_X]

theorem isHomogeneous_X_mul (c : Fin (N + 1)) {H : MRing (fun _ : Unit => Fin (N + 1))} {d : ℕ}
    (hH : H.IsHomogeneous d) : (MvPolynomial.X ⟨(), c⟩ * H : MRing (fun _ : Unit => Fin (N + 1))).IsHomogeneous (d + 1) := by
  rw [add_comm d 1]
  exact (MvPolynomial.isHomogeneous_X ℤ (⟨(), c⟩ : Σ _ : Unit, Fin (N + 1))).mul hH

theorem exists_form [Algebra ℚ Ω] (x : Fin (N + 1) → Ω) {c : Fin (N + 1)} (hc : x c ≠ 0) {a : Ω}
    (ha : a ∈ chartQ x c) :
    ∃ (m d : ℕ) (H : MRing (fun _ : Unit => Fin (N + 1))),
      m ≠ 0 ∧ H.IsHomogeneous d ∧ ratEval x c H = m * a := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    exact ⟨1, 1, MvPolynomial.X ⟨(), j⟩, one_ne_zero, MvPolynomial.isHomogeneous_X _ _, by simp⟩
  | algebraMap r =>
    refine ⟨r.den, 0, MvPolynomial.C r.num, r.den_nz, MvPolynomial.isHomogeneous_C _ _, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    rw [eq_ratCast (algebraMap ℚ Ω) r, Rat.cast_def]
    rw [ratEval_C]
    field_simp
  | add a b _ _ ha hb =>
    obtain ⟨m₁, d₁, H₁, hm₁, hH₁, hv₁⟩ := ha
    obtain ⟨m₂, d₂, H₂, hm₂, hH₂, hv₂⟩ := hb
    have hX : (MvPolynomial.X ⟨(), c⟩ : MRing (fun _ : Unit => Fin (N + 1))).IsHomogeneous 1 :=
      MvPolynomial.isHomogeneous_X _ _
    refine ⟨m₁ * m₂, d₁ + d₂,
      MvPolynomial.C (m₂ : ℤ) * H₁ * MvPolynomial.X ⟨(), c⟩ ^ d₂ +
        MvPolynomial.C (m₁ : ℤ) * H₂ * MvPolynomial.X ⟨(), c⟩ ^ d₁,
      mul_ne_zero hm₁ hm₂, ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · simpa using ((MvPolynomial.isHomogeneous_C _ (m₂ : ℤ)).mul hH₁).mul (hX.pow d₂)
      · simpa [add_comm] using ((MvPolynomial.isHomogeneous_C _ (m₁ : ℤ)).mul hH₂).mul (hX.pow d₁)
    · simp only [map_add (f := _), map_mul, map_pow, MvPolynomial.aeval_X, ratEval_C, hv₁, hv₂, div_self hc]
      push_cast
      ring
  | mul a b _ _ ha hb =>
    obtain ⟨m₁, d₁, H₁, hm₁, hH₁, hv₁⟩ := ha
    obtain ⟨m₂, d₂, H₂, hm₂, hH₂, hv₂⟩ := hb
    refine ⟨m₁ * m₂, d₁ + d₂, H₁ * H₂, mul_ne_zero hm₁ hm₂, hH₁.mul hH₂, ?_⟩
    simp only [map_mul, hv₁, hv₂]
    push_cast
    ring

end Forms

section Pts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}

theorem ratEval_regular {x : Fin (N + 1) → Ω} {c : Fin (N + 1)} {p : Cpt ξ} (hc : InChart ξ x c p)
    (g : MRing (fun _ : Unit => Fin (N + 1))) : ratEval x c g ∈ regAt ξ p := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (regAt ξ p) a
  | add a b ha hb => simpa using (regAt ξ p).add_mem ha hb
  | mul_X a i ha => simpa using (regAt ξ p).mul_mem ha (hc.2 i.2)

theorem inChart_of_unitAt {x : Fin (N + 1) → Ω} {c c' : Fin (N + 1)} {q : Cpt ξ} (hc : x c ≠ 0)
    (hc' : InChart ξ x c' q) (ht : unitAt ξ q (x c / x c')) : InChart ξ x c q := by
  refine ⟨hc, fun j => ?_⟩
  have e : x j / x c = x j / x c' * (x c / x c')⁻¹ := by
    have := hc'.1
    field_simp
  rw [e]
  exact (regAt ξ q).mul_mem (hc'.2 j) ht.2.2

theorem not_unitAt_form [CharZero Ω] {x : Fin (N + 1) → Ω} {c c' : Fin (N + 1)} {q : Cpt ξ} {a : Ω}
    (hc : x c ≠ 0) (hq0 : Char0 ξ q) (hc' : InChart ξ x c' q) (har : InChart ξ x c q → a ∈ regAt ξ q)
    (hnon : InChart ξ x c q → ¬ unitAt ξ q a) {m d : ℕ} {H : MRing (fun _ : Unit => Fin (N + 1))} (hm : m ≠ 0)
    (hH : H.IsHomogeneous d) (hv : ratEval x c H = m * a) :
    ¬ unitAt ξ q (ratEval x c' (MvPolynomial.X ⟨(), c⟩ * H)) := by
  intro hunit
  have ht : x c / x c' ∈ regAt ξ q := hc'.2 c
  have h₁ := hunit
  rw [ratEval_X_mul] at h₁
  have htu : unitAt ξ q (x c / x c') := unitAt_of_mul_left h₁ ht (ratEval_regular hc' H)
  have hcq : InChart ξ x c q := inChart_of_unitAt hc hc' htu
  have hr : a ∈ regAt ξ q := har hcq
  have hmu := Char0.unitAt_natCast hq0 hm
  have h₂ := hunit
  rw [ratEval_eq_pow_mul x hc (isHomogeneous_X_mul c hH), ratEval_X_mul, div_self hc, _root_.one_mul, hv] at h₂
  have hma : unitAt ξ q ((m : Ω) * a) :=
    unitAt_of_mul_right h₂ ((regAt ξ q).pow_mem ht _) ((regAt ξ q).mul_mem hmu.2.1 hr)
  exact hnon hcq (unitAt_of_mul_right hma hmu.2.1 hr)

end Pts

section Sep

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}

theorem exists_form_sep {x : Fin (N + 1) → Ω} {c : Fin (N + 1)} {B : Set (Cpt ξ)} {p : Cpt ξ} {a : Ω}
    (hB : ∀ q ∈ B, Char0 ξ q) (hp : Char0 ξ p) (hc : InChart ξ x c p)
    (hreg : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → a ∈ regAt ξ q) (hu : unitAt ξ p a)
    (hnon : ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a) {m d : ℕ}
    {H : MRing (fun _ : Unit => Fin (N + 1))} (hm : m ≠ 0) (hH : H.IsHomogeneous d)
    (hv : ratEval x c H = m * a) : ∃ G ∈ bdGens ξ x B, unitAt ξ p (ratEval x c G) := by
  have hmem : MvPolynomial.X ⟨(), c⟩ * H ∈ bdGens ξ x B :=
    ⟨d + 1, isHomogeneous_X_mul c hH, fun c' q hq hc' =>
      not_unitAt_form hc.1 (hB q hq) hc' (hreg q (hB q hq)) (hnon q hq) hm hH hv⟩
  refine ⟨_, hmem, ?_⟩
  rw [ratEval_X_mul, div_self hc.1, _root_.one_mul, hv]
  exact unitAt_mul (Char0.unitAt_natCast hp hm) hu

end Sep

theorem exists_bdGens_unitAt : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (B : Set (Cpt ξ)) (p : Cpt ξ) (a : Ω), (∀ q ∈ B, Char0 ξ q) → Char0 ξ p → InChart ξ x c p → a ∈ Mdl.chartQ x c → unitAt ξ p a → (∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a) → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G) := by
  intro Ω _ _ X ξ N x c B p a hB hp hc ha hu hnon
  obtain ⟨m, d, H, hm, hH, hv⟩ := exists_form x hc.1 ha
  exact exists_form_sep hB hp hc (fun q hq hcq => chartQ_le hq hcq ha) hu hnon hm hH hv

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep
end
end
