module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.RingTheory.Ideal.BigOperators
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions
  _root_.Formalism.L2.DIV _root_.Formalism.L2.Col _root_.Formalism.L2.Ker
  GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.MovedDatum

section Gen

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem norm_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (h : IsUnit (redP P a)) (σ : K →+* ℂ) :
    ‖σ (LocE.unitV χ a)‖ = 1 := by
  unfold LocE.unitV
  rw [dite_eq_left h]
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hc : 0 < Nat.card (𝓞 E ⧸ P.asIdeal)ˣ := Nat.card_pos
  have h1 : ((χ h.unit : Kˣ) : K) ^ Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h2 : ‖σ ((χ h.unit : Kˣ) : K)‖ ^ Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hc.ne').1 h2

variable [StarRing E]

theorem locSmall_om {a b : ℕ} {e e' : ℕ → ℤ} (cq sq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {g : Sp E a ≃ₗ[E] Sp E a} {g' : Sp E b ≃ₗ[E] Sp E b}
    (hg : g ∈ stabL E a (LocE.sclLat P (qOf P) a e)) (hg' : g' ∈ stabL E b (LocE.sclLat P (qOf P) b e'))
    {Φ : HomE E a b → K} {β : ℝ}
    (hΦ : LocSmall (qOf P) (LocE.sclLat P (qOf P) a e) (LocE.sclLat P (qOf P) b e') Φ β) :
    LocSmall (qOf P) (LocE.sclLat P (qOf P) a e) (LocE.sclLat P (qOf P) b e')
      (Loc.om (LocE.locChar (qOf P) cq χ) (LocE.vP P (qOf P)) sq g g' Φ) β := by
  have hu := GlobalTheory.LastSteps.isUnit_det_of_stab hg
  have hu' := GlobalTheory.LastSteps.isUnit_det_of_stab hg'
  obtain ⟨h1, h2, h3⟩ := hΦ
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · unfold Loc.om at hx
    have h4 := h1 _ (right_ne_zero_of_mul hx) (g.symm y) ((hg _).1 (by simpa using hy))
    have h5 := (hg' _).2 h4
    simpa using h5
  · unfold Loc.om
    congr 1
    have h4 := h2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) (g'.symm.toLinearMap ∘ₗ z ∘ₗ g.toLinearMap) fun y hy =>
      (hg' _).1 (by simpa using hz _ ((hg y).2 hy))
    rw [← h4]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul]
  · have locChar_eq_unitV {x : E} (hx : IsUnit (redP P x)) :
        LocE.locChar (qOf P) cq χ x = LocE.unitV χ x := by
      simp [LocE.locChar, GlobalTheory.LastSteps.vP_unit hx]
    unfold Loc.om
    rw [locChar_eq_unitV hu, locChar_eq_unitV hu', GlobalTheory.LastSteps.vP_unit hu,
      GlobalTheory.LastSteps.vP_unit hu']
    simp only [neg_zero, zero_mul, zpow_zero, mul_one, map_mul, map_inv₀, norm_mul, norm_inv, norm_unitV χ hu,
      norm_unitV χ hu', inv_one, one_mul]
    exact h3 σ _

end Gen

end GlobalTheory.ColNorms.MovedDatum
end

section

noncomputable section

namespace GlobalTheory.ColNorms.CplCS

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions
  _root_.Formalism.L2.DIV _root_.Formalism.L2.Col _root_.Formalism.L2.Ker
  GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder Matrix

theorem diag_sum_le {V ι : Type} [AddCommGroup V] (B : V →+ V →+ ℝ) (hB : ∀ x, 0 ≤ B x x) (s : Finset ι) (x : ι → V) :
    B (∑ i ∈ s, x i) (∑ i ∈ s, x i) ≤ s.card * ∑ i ∈ s, B (x i) (x i) := by
  have h1 : ∀ a b, B a b + B b a ≤ B a a + B b b := by
    intro a b
    have := hB (a - b)
    simp only [map_sub, AddMonoidHom.sub_apply] at this
    linarith
  have e : B (∑ i ∈ s, x i) (∑ i ∈ s, x i) = ∑ i ∈ s, ∑ j ∈ s, B (x i) (x j) := by

    rw [map_sum B x s, AddMonoidHom.finsetSum_apply]
    exact Finset.sum_congr rfl fun i _ => map_sum _ _ _
  have e' : ∑ i ∈ s, ∑ j ∈ s, B (x j) (x i) = ∑ i ∈ s, ∑ j ∈ s, B (x i) (x j) := Finset.sum_comm
  have h2 : ∑ i ∈ s, ∑ j ∈ s, (B (x i) (x j) + B (x j) (x i)) ≤ ∑ i ∈ s, ∑ j ∈ s, (B (x i) (x i) + B (x j) (x j)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 _ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h2
  rw [e]
  linarith

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def reForm (S : GSD K) (v : InfinitePlace K) : S.V →+ S.V →+ ℝ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => (S.pairAt v x y).re) (by
      intro y z
      simp only [GSD.pairAt, map_add (f := _), Finsupp.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]))
    (by
      intro x y
      ext z
      simp only [GSD.pairAt, map_add (f := _), Finsupp.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re,
        AddMonoidHom.mk'_apply, AddMonoidHom.add_apply])

theorem sq_nonneg' {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) (x : S.V) : 0 ≤ (S.pairAt v x x).re := by
  have e : S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      S.gramV.map v.embedding *ᵥ fun i => v.embedding (S.bV.repr x i) := by
    simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, starRingEnd_apply,
      mul_assoc]
  rw [e]
  exact (Complex.nonneg_iff.1 (Matrix.PosSemidef.dotProduct_mulVec_nonneg h _)).1

theorem sq_sum_le {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) {ι : Type} (s : Finset ι) (x : ι → S.V) {m : ℝ}
    (hm : (s.card : ℝ) ≤ m) :
    (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re ≤ m * ∑ i ∈ s, (S.pairAt v (x i) (x i)).re :=
  (diag_sum_le (reForm S v) (sq_nonneg' h) s x).trans
    (mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg fun _ _ => sq_nonneg' h _))

theorem inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := Nat.cast_inv_le_one n

theorem sq_smul_le {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) (n : ℕ) (x : S.V) :
    (S.pairAt v ((n : K)⁻¹ • x) ((n : K)⁻¹ • x)).re ≤ (n : ℝ)⁻¹ * (S.pairAt v x x).re := by
  have e : S.pairAt v ((n : K)⁻¹ • x) ((n : K)⁻¹ • x) = (((n : ℝ)⁻¹ * (n : ℝ)⁻¹ : ℝ) : ℂ) * S.pairAt v x x := by
    simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, mul_assoc]
  have h0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ * (S.pairAt v x x).re := mul_nonneg (by positivity) (sq_nonneg' h x)
  exact mul_le_of_le_one_left h0 (inv_nat_le_one n)

theorem ipAt_re (S : GSD K) (h : S.Ok) (v : InfinitePlace K) (φ : S.D → S.V) :
    (S.ipAt h v φ φ).re = letI := h.fintypeCl
      ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re := by
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.re_ofReal_mul]
  push_cast
  rfl

theorem comp_opLe {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (hS : S.Ok) (v : InfinitePlace K)
    {t₁ t₂ h ny : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hh : 0 ≤ h) (hny : 0 ≤ ny) (p₀ : PosAt S₀ v) (p₁ : PosAt S₁ v)
    (hc : (Nat.card S.Cl : ℝ) ≤ h) (hy : ∀ d, ((Y.ys d).ncard : ℝ) ≤ ny)
    (h1 : ∀ d₀ d, ∀ y ∈ Y.ys d, OpLe S₀ S v (A.k1 d₀ d y) t₁) (h2 : ∀ d d₁, ∀ y ∈ Y.ys d, OpLe S S₁ v (A.k2 d y d₁) t₂)
    (d₀ : S₀.D) (d₁ : S₁.D) : OpLe S₀ S₁ v ((A.comp hS S.outSec).k d₀ d₁) (h ^ 2 * ny ^ 2 * t₁ * t₂) := by
  intro x
  letI := hS.fintypeCl
  have hc' : ((Finset.univ : Finset S.Cl).card : ℝ) ≤ h := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hx := sq_nonneg' p₀ x
  have e : (A.comp hS S.outSec).k d₀ d₁ x = ∑ c : S.Cl, (((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x) := by
    simp only [CplKer.comp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [e]
  refine (sq_sum_le p₁ _ _ hc').trans ?_
  have key : ∀ c : S.Cl, (S₁.pairAt v ((((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x))
      ((((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x))).re ≤
      ny * (ny * (t₂ * (t₁ * (S₀.pairAt v x x).re))) := by
    intro c
    have hy' : (((Y.fin (S.outSec.rep c)).toFinset.card : ℕ) : ℝ) ≤ ny := by
      rw [← Set.ncard_eq_toFinset_card _ (Y.fin _)]
      exact hy _
    refine (sq_smul_le p₁ _ _).trans ((mul_le_of_le_one_left (sq_nonneg' p₁ _) (inv_nat_le_one _)).trans ?_)
    refine (sq_sum_le p₁ _ _ hy').trans (mul_le_mul_of_nonneg_left ?_ hny)
    refine (Finset.sum_le_card_nsmul _ _ (t₂ * (t₁ * (S₀.pairAt v x x).re)) fun y hy => ?_).trans ?_
    · have hy0 : y ∈ Y.ys (S.outSec.rep c) := (Set.Finite.mem_toFinset _).1 hy
      exact (h2 _ _ y hy0 _).trans (mul_le_mul_of_nonneg_left (h1 _ _ y hy0 _) ht₂)
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hy' (by positivity)
  have h3 := Finset.sum_le_card_nsmul Finset.univ _ _ fun c _ => key c
  rw [nsmul_eq_mul] at h3
  calc _ ≤ h * (h * (ny * (ny * (t₂ * (t₁ * (S₀.pairAt v x x).re))))) :=
        mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right hc' (by positivity))) hh
    _ = _ := by ring

theorem appOf_le {S S' : GSD K} (A : ClsKer S S') (hS : S.Ok) (v : InfinitePlace K) {t h : ℝ} (hh : 0 ≤ h)
    (p' : PosAt S' v) (hc : (Nat.card S.Cl : ℝ) ≤ h) (hA : ∀ d d', OpLe S S' v (A.k d d') t) (φ : S.D → S.V) (d' : S'.D) :
    (S'.pairAt v (A.appOf hS S.outSec φ d') (A.appOf hS S.outSec φ d')).re ≤ h * (t * (S.ipAt hS v φ φ).re) := by
  letI := hS.fintypeCl
  have hc' : ((Finset.univ : Finset S.Cl).card : ℝ) ≤ h := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  unfold ClsKer.appOf
  refine (sq_sum_le p' _ _ hc').trans (mul_le_mul_of_nonneg_left ?_ hh)
  rw [ipAt_re, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => (sq_smul_le p' _ _).trans ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hA _ _ _) (by positivity)

theorem cpl_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (v : InfinitePlace K) (t₁ t₂ h₀ h h₁ ny : ℝ), 0 ≤ t₁ → 0 ≤ t₂ → 0 ≤ h₀ → 0 ≤ h → 0 ≤ h₁ → 0 ≤ ny → (∀ b, PosAt ((Q.F Q.n).mem b) v) → PosAt Q.S v → PosAt Q.S₁ v → (∀ b, (Nat.card ((Q.F Q.n).mem b).Cl : ℝ) ≤ h₀) → (Nat.card Q.S.Cl : ℝ) ≤ h → (Nat.card Q.S₁.Cl : ℝ) ≤ h₁ → (∀ d, ((Q.Y.ys d).ncard : ℝ) ≤ ny) → (∀ b d₀ d, ∀ y ∈ Q.Y.ys d, OpLe ((Q.F Q.n).mem b) Q.S v ((Q.cp b).k1 d₀ d y) t₁) → (∀ b d d₁, ∀ y ∈ Q.Y.ys d, OpLe Q.S Q.S₁ v ((Q.cp b).k2 d y d₁) t₂) → ∀ φ : (Q.F Q.n).Forms, (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤ (Fintype.card (Q.F Q.n).β : ℝ) * h₀ * h ^ 2 * h₁ * ny ^ 2 * t₁ * t₂ * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
  intro K _ _ _ Q v t₁ t₂ h₀ h h₁ ny ht₁ ht₂ hh₀ hh hh₁ hny p₀ _ p₁ c₀ c c₁ hy k1 k2 φ
  letI := Q.hS₁.fintypeCl
  have hc' : ((Finset.univ : Finset Q.S₁.Cl).card : ℝ) ≤ h₁ := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  set M : ℝ := (Fintype.card (Q.F Q.n).β : ℝ) * (h₀ * (h ^ 2 * ny ^ 2 * t₁ * t₂ *
    (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re)) with hM
  have key : ∀ d : Q.S₁.D, (Q.S₁.pairAt v ((Q.cpl φ : Q.S₁.D → Q.S₁.V) d) ((Q.cpl φ : Q.S₁.D → Q.S₁.V) d)).re ≤ M := by
    intro d
    have e : (Q.cpl φ : Q.S₁.D → Q.S₁.V) d = ∑ b : (Q.F Q.n).β,
        ((Q.cp b).comp Q.hS Q.S.outSec).appOf (Q.hF Q.n b) ((Q.F Q.n).mem b).outSec (φ b) d := by
      simp only [KerChain.cpl, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      rfl
    rw [e]
    refine (sq_sum_le p₁ _ _ (le_of_eq (by rw [Finset.card_univ]))).trans
      (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    unfold famIpAt
    rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => appOf_le _ _ v hh₀ p₁ (c₀ b)
      (comp_opLe (Q.cp b) Q.hS v ht₁ ht₂ hh hny (p₀ b) p₁ c hy (k1 b) (k2 b)) _ _
  have hF : 0 ≤ (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
    unfold famIpAt
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b _ => ?_
    rw [ipAt_re]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sq_nonneg' (p₀ b) _)
  have hM0 : 0 ≤ M := by positivity
  rw [ipAt_re]
  refine (Finset.sum_le_card_nsmul _ _ M fun c _ =>
    (mul_le_of_le_one_left (sq_nonneg' p₁ _) (inv_nat_le_one _)).trans (key _)).trans ?_
  rw [nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right hc' hM0).trans (le_of_eq ?_)
  rw [hM]
  ring

end GlobalTheory.ColNorms.CplCS
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem isUnit_add_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {u m : R}
    (hu : IsUnit u) (hm : ¬ IsUnit m) : IsUnit (u + m) := by
  by_contra h
  have h1 : u + m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hm
  have h3 : u ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ h1 h2
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 hu

theorem secFam_unit_at_finite : ∀ (X : Scheme.{0}) (L : LB X) (W : X.Opens) (J : Type) (D : J → X.Opens), (∀ j, D j ≤ W) → ∀ (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (F : Set X), F.Finite → ∀ (a : X → Γ(X, W)), (∀ x ∈ F, x ∈ X.basicOpen (a x)) → (∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x)) → ∀ (E : X → ∀ j, Γ(X, D j)), (∀ x ∈ F, GlobalTheory.Pinch.IsSecFam L D k hD (E x)) → (∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (E x j))) → ∃ e : ∀ j, Γ(X, D j), GlobalTheory.Pinch.IsSecFam L D k hD e ∧ ∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) := by
  intro X L W J D hDW k hD F hF a ha hsep E hE hEu
  classical
  let r : ∀ j, Γ(X, W) →+* Γ(X, D j) := fun j => (X.presheaf.map (homOfLE (hDW j)).op).hom
  refine ⟨fun j => ∑ x ∈ hF.toFinset, r j (a x) * E x j, ?_, ?_⟩
  ·
    have hr : ∀ j z (hz : z ∈ D j) (s : Γ(X, W)),
        (X.presheaf.germ (D j) z hz).hom (r j s) = (X.presheaf.germ W z (hDW j hz)).hom s := by
      intro j z hz s
      exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hDW j)) z hz s
    intro j j' z hz hz'

    simp only [map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hr, hr, hE x (hF.mem_toFinset.mp hx) j j' z hz hz']
    ring
  · intro y hy j hyj
    have hyW : y ∈ W := hDW j hyj
    have hyF : y ∈ hF.toFinset := hF.mem_toFinset.mpr hy

    simp only [map_sum, map_mul]
    rw [← Finset.add_sum_erase _ _ hyF]
    have hr : ∀ s : Γ(X, W),
        (X.presheaf.germ (D j) y hyj).hom (r j s) = (X.presheaf.germ W y hyW).hom s :=
      fun s => TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hDW j)) y hyj s
    apply isUnit_add_of_not_isUnit
    · rw [hr]
      exact ((X.mem_basicOpen (a y) y hyW).mp (ha y hy)).mul (hEu y hy j hyj)
    · intro hu
      have hmem : ∑ x ∈ hF.toFinset.erase y,
          (X.presheaf.germ (D j) y hyj).hom (r j (a x)) * (X.presheaf.germ (D j) y hyj).hom (E x j)
            ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        refine Ideal.sum_mem _ fun x hx => ?_
        have hxy : x ≠ y := (Finset.mem_erase.mp hx).1
        have hxF : x ∈ F := hF.mem_toFinset.mp (Finset.mem_erase.mp hx).2
        refine Ideal.mul_mem_right _ _ ?_
        rw [hr, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu'
        exact hsep x hxF y hy (Ne.symm hxy) ((X.mem_basicOpen (a x) y hyW).mpr hu')
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

end GlobalTheory.Pinch
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.baseChange_integralClosure_etale_height_one : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
      (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁)),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      (∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
        GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
        GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (Localization.AtPrime QA₁) DA₁ ρ₁) ∧
      (∀ (P₁ : Ideal (Localization.AtPrime QA₁)) [P₁.IsPrime], P₁.height ≤ 1 →
        GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (Localization.AtPrime QA₁) DA₁ P₁) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β := by
  first | (exact @GlobalTheory.KeyOriginBC.etale_bc) | (exact GlobalTheory.KeyOriginBC.etale_bc) | (intros; apply GlobalTheory.KeyOriginBC.etale_bc  <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LBDescent

theorem twist_frame_descent : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∀ (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) →
    ∀ (V' : Y.Opens), V' ≤ V → ∀ u : Γ(X, f ⁻¹ᵁ V')ˣ, (∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u) →
    ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V' ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V' → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V' → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j) := by
  intro X Y f L φ V t ht c hc V' hV' u hu
  have h1 : ∀ i, f ⁻¹ᵁ V' ⊓ L.U i ≤ f ⁻¹ᵁ V' := fun i => inf_le_left
  have h2 : ∀ i, f ⁻¹ᵁ V' ⊓ L.U i ≤ f ⁻¹ᵁ V ⊓ L.U i := fun i =>
    inf_le_inf_right _ (fun x hx => hV' hx)
  refine ⟨fun i => res (h1 i) u * res (h2 i) (t i), ?_, ?_⟩
  · intro i j x hx hi hj
    have mi : (𝟙 X) x ∈ f ⁻¹ᵁ V' ⊓ L.U i := ⟨hx, hi⟩
    have mj : (𝟙 X) x ∈ f ⁻¹ᵁ V' ⊓ L.U j := ⟨hx, hj⟩
    rw [map_mul, map_mul, gm_res _ x _ mi, gm_res _ x _ mi, gm_res _ x _ mj, gm_res _ x _ mj,
      ht i j x (hV' hx) hi hj]
    exact mul_left_comm _ _ _
  · intro z i j hz hi hj
    have hfz : f (pullback.snd f f z) = f (pullback.fst f f z) := by
      have := congrArg (fun g => g z) (congrArg (fun g => g.base) (pullback.condition (f := f) (g := f)))
      simpa using this.symm
    have mi : pullback.fst f f z ∈ f ⁻¹ᵁ V' ⊓ L.U i := ⟨hz, hi⟩
    have mj : pullback.snd f f z ∈ f ⁻¹ᵁ V' ⊓ L.U j := ⟨show f (pullback.snd f f z) ∈ V' by rw [hfz]; exact hz, hj⟩
    rw [map_mul, map_mul, gm_res _ z _ mi, gm_res _ z _ mi, gm_res _ z _ mj, gm_res _ z _ mj, ← hu z hz,
      hc z i j (hV' hz) hi hj]
    group

end GlobalTheory.LBDescent
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hyper_cohomology_flat_base_change : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → Function.Bijective (liftSemi (pullHH1 h.w)) := by
  first | exact @GlobalTheory.Div.HypFlatBaseChange.main | exact GlobalTheory.Div.HypFlatBaseChange.main | (intros; apply GlobalTheory.Div.HypFlatBaseChange.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.vanishingForms_iff_proportional_pullbacks : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → φ ≫ f = p ≫ t → GlobalTheory.HomFixUniv.Generates a φ p c → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p t c ↔ ∃ Ψ : X ⟶ B₀, Ψ ≫ fB = p ≫ t ∧ GlobalTheory.HomFixUniv.Proport a b φ p Ψ c) := by
  first | (exact @GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (exact GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (intros; apply GlobalTheory.HomFixUniv.formsOK_iff_exists_proport  <;> assumption)
end
