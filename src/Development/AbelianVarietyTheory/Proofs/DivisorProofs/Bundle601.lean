module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle549
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle559
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

private def reHermBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).re)
    (fun a b c => by simp [hermForm, add_dotProduct])
    (fun r a b => by simp [hermForm, smul_dotProduct])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun r a b => by
      simp only [hermForm, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul]
      simp)

private theorem hermForm_swap' {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, star_star, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

private theorem form_eq_zero_of_im_span' {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (B : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w)
    (h2 : ∀ (r : ℂ) z w, B (r • z) w = r * B z w) (h3 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h4 : ∀ (r : ℝ) z w, B z (r • w) = r * B z w) (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : Fin g → ℂ) :
    B z w = 0 := by
  have hA : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simpa using congrArg Complex.im (h4 0 z 0)
    | add w w' _ _ e e' => rw [h3, Complex.add_im, e, e', add_zero]
    | smul r w _ e => rw [h4, Complex.im_ofReal_mul, e, mul_zero]
  have hB : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact hA z hz w
    | zero => simpa using congrArg Complex.im (h2 0 0 w)
    | add z z' _ _ e e' => rw [h1, Complex.add_im, e, e', add_zero]
    | smul r z _ e =>
      have : r • z = (r : ℂ) • z := by ext k; simp
      rw [this, h2, Complex.im_ofReal_mul, e, mul_zero]
  apply Complex.ext
  · have := hB (Complex.I • z) w
    rw [h2] at this
    simpa using this
  · simpa using hB z w

private theorem hermForm_adj_of_im_span' {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (A A' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (A z) w).im = (hermForm Hm z (A' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (A z) w = hermForm Hm z (A' w) := by
  have hr : ∀ (r : ℝ) (w : Fin g → ℂ), r • w = (r : ℂ) • w := fun r w => by ext k; simp
  have l1 : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp only [hermForm, add_dotProduct]
  have l2 : ∀ (r : ℂ) z w, hermForm Hm (r • z) w = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have l3 : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have l4 : ∀ (r : ℝ) z w, hermForm Hm z ((r : ℂ) • w) = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  refine sub_eq_zero.mp (form_eq_zero_of_im_span' s hs
    (fun z w => hermForm Hm (A z) w - hermForm Hm z (A' w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [map_add (f := _), l1]; ring
  · intro r z w
    simp only [map_smul, l2]; ring
  · intro z w w'
    simp only [map_add (f := _), l3]; ring
  · intro r z w
    simp only [hr, map_smul, l4]; ring
  · intro z hz w hw
    simp only [Complex.sub_im, h0 z hz w hw, sub_self]

theorem gram_re_posdef_adj : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D : PLat O bar) (P : D.La →+ (Fin g → ℂ)) (r : ℕ) (e : Module.Basis (Fin r) ℤ D.La), IsPeriod D ρ P →
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.IsHermitian ∧ (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) ∧
      ∀ a : O, Q * actM D e ℂ (bar a) = (actM D e ℂ a)ᴴ * Q := by
  intro O _ bar g ρ D P r e hP
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, hE⟩ := hP
  set B := reHermBilin Hm with hBdef
  have hB : ∀ z w, B z w = (hermForm Hm z w).re := fun _ _ => rfl
  have hind : LinearIndependent ℝ (fun i => P (e i)) := by
    haveI : DiscreteTopology (LinearMap.range P.toIntLinearMap) := hdisc
    haveI : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨hspan⟩
    let bL := e.map (LinearEquiv.ofInjective P.toIntLinearMap hinj)
    have hfun : (fun i => P (e i)) = ⇑(bL.ofZLatticeBasis ℝ (LinearMap.range P.toIntLinearMap)) := by
      funext i
      rw [Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply]
      rfl
    rw [hfun]
    exact (bL.ofZLatticeBasis ℝ (LinearMap.range P.toIntLinearMap)).linearIndependent
  have hBpos : ∀ v, v ≠ 0 → 0 < B v v := fun v hv => hpos v hv
  have hBnn : ∀ v, 0 ≤ B v v := fun v => by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (hBpos v hv).le
  have hBsymm : ∀ v w, B v w = B w v := fun v w => by
    rw [hB, hB, hermForm_swap' hH v w]; simp
  refine ⟨Matrix.of fun i j => ((B (P (e i)) (P (e j)) : ℝ) : ℂ), ?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, hBsymm]
  · intro z hz
    have hexp : ∀ x : Fin r → ℝ, B (∑ j, x j • P (e j)) (∑ j, x j • P (e j)) =
        ∑ i, ∑ j, B (P (e i)) (P (e j)) * (x i * x j) := by
      intro x

      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hBsymm (P (e j))]
      ring
    have hq : (star z ⬝ᵥ (Matrix.of (fun i j => ((B (P (e i)) (P (e j)) : ℝ) : ℂ)) *ᵥ z)).re =
        ∑ i, ∑ j, B (P (e i)) (P (e j)) * ((z i).re * (z j).re) +
          ∑ i, ∑ j, B (P (e i)) (P (e j)) * ((z i).im * (z j).im) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Complex.re_sum, Finset.mul_sum, Pi.star_apply,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [hq, ← hexp, ← hexp]
    have hor : (fun i => (z i).re) ≠ 0 ∨ (fun i => (z i).im) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hz
      funext i
      exact Complex.ext (congrFun h.1 i) (congrFun h.2 i)
    rcases hor with h | h
    · have hv : ∑ j, (z j).re • P (e j) ≠ 0 := fun h0 =>
        h (funext fun i => Fintype.linearIndependent_iff.1 hind _ h0 i)
      exact add_pos_of_pos_of_nonneg (hBpos _ hv) (hBnn _)
    · have hv : ∑ j, (z j).im • P (e j) ≠ 0 := fun h0 =>
        h (funext fun i => Fintype.linearIndependent_iff.1 hind _ h0 i)
      exact add_pos_of_nonneg_of_pos (hBnn _) (hBpos _ hv)
  · intro a
    have hadj : ∀ z w, hermForm Hm (ρ a *ᵥ z) w = hermForm Hm z (ρ (bar a) *ᵥ w) :=
      hermForm_adj_of_im_span' (Set.range P) hspan Hm (Matrix.mulVecLin (ρ a)) (Matrix.mulVecLin (ρ (bar a))) (by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        simp only [Matrix.mulVecLin_apply]
        rw [← hlin, ← hlin, hE, hE, D.adj])
    have hexpand : ∀ v : D.La, P v = ∑ k, e.repr v k • P (e k) := fun v => by
      conv_lhs => rw [← e.sum_repr v]

      simp only [map_sum, map_zsmul]
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, actM, Matrix.conjTranspose_apply, star_intCast]
    have h1 : B (P (e i)) (P (bar a • e j)) = ∑ k, B (P (e i)) (P (e k)) * (e.repr (bar a • e j) k : ℝ) := by

      rw [hexpand (bar a • e j), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, mul_comm]
    have h2 : B (P (a • e i)) (P (e j)) = ∑ k, (e.repr (a • e i) k : ℝ) * B (P (e k)) (P (e j)) := by

      rw [hBsymm, hexpand (a • e i), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hBsymm]
    have h3 : B (P (e i)) (P (bar a • e j)) = B (P (a • e i)) (P (e j)) := by
      rw [hB, hB, hlin, hlin, hadj]
    have := congrArg (fun t : ℝ => (t : ℂ)) (h1.symm.trans (h3.trans h2))
    push_cast at this
    exact this

end GlobalTheory.PELU
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CechDR

open CatCoh

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem pairRes_bijective (φ : X' ⟶ X) (s' : X' ⟶ Sp R') :
    Function.Bijective (pairRes φ s').pull1 ∧ Function.Bijective (pullGlob1 (pairRes φ s')) ∧
      Function.Bijective (pullHyp1 (pairRes φ s')) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  have b1 : Function.Bijective (pairRes φ s').pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg, _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  exact ⟨b1, bg, _root_.GlobalTheory.CechDR.pullHyp1_restrict_injective _ _ b1.1 (_root_.GlobalTheory.compat_family_extend _ _ hs hg) bg.1,
    _root_.GlobalTheory.CechDR.pullHyp1_restrict_surjective _ _ b1.2 (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2⟩

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

theorem existsUnique_isPull1 (c : HH1 s) : ∃! c', IsPull1 h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective φ s').2.2.existsUnique (pullHyp1 (pairPull h) c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

theorem existsUnique_isPullO (c : HO1 s) : ∃! c', IsPullO h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective φ s').1.existsUnique ((pairPull h).pull1 c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

theorem existsUnique_isPullForm (ω : GlobForm s) : ∃! ω', IsPullForm h ω ω' := by
  obtain ⟨ω', hω, hu⟩ := (pairRes_bijective φ s').2.1.existsUnique (pullGlob1 (pairPull h) ω)
  exact ⟨ω', hω.symm, fun y hy ↦ hu y hy.symm⟩

def pairResEquiv1 (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HH1 s' ≃ₗ[R'] Hyp1 (OPair φ s') :=
  LinearEquiv.ofBijective (pullHyp1 (pairRes φ s')) (pairRes_bijective φ s').2.2

def pairResEquivO (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HO1 s' ≃ₗ[R'] CatCoh.H1 (OPair φ s') :=
  LinearEquiv.ofBijective (pairRes φ s').pull1 (pairRes_bijective φ s').1

def pairResEquivForm (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : GlobForm s' ≃ₗ[R'] Glob1 (OPair φ s') :=
  LinearEquiv.ofBijective (pullGlob1 (pairRes φ s')) (pairRes_bijective φ s').2.1

def pullHH1 : HH1 s →ₛₗ[σ] HH1 s' :=
  (pairResEquiv1 φ s').symm.toLinearMap.comp (pullHyp1 (pairPull h))

def pullHO1 : HO1 s →ₛₗ[σ] HO1 s' :=
  (pairResEquivO φ s').symm.toLinearMap.comp (pairPull h).pull1

def pullForm : GlobForm s →ₛₗ[σ] GlobForm s' :=
  (pairResEquivForm φ s').symm.toLinearMap.comp (pullGlob1 (pairPull h))

theorem isPull1_pullHH1 (c : HH1 s) : IsPull1 h c (pullHH1 h c) :=
  ((pairResEquiv1 φ s').apply_symm_apply _).symm

theorem isPullO_pullHO1 (c : HO1 s) : IsPullO h c (pullHO1 h c) :=
  ((pairResEquivO φ s').apply_symm_apply _).symm

theorem isPullForm_pullForm (ω : GlobForm s) : IsPullForm h ω (pullForm h ω) :=
  ((pairResEquivForm φ s').apply_symm_apply _).symm

theorem IsPull1.eq_pullHH1 {c : HH1 s} {c' : HH1 s'} (e : IsPull1 h c c') : c' = pullHH1 h c :=
  (existsUnique_isPull1 h c).unique e (isPull1_pullHH1 h c)

theorem IsPullO.eq_pullHO1 {c : HO1 s} {c' : HO1 s'} (e : IsPullO h c c') : c' = pullHO1 h c :=
  (existsUnique_isPullO h c).unique e (isPullO_pullHO1 h c)

theorem IsPullForm.eq_pullForm {ω : GlobForm s} {ω' : GlobForm s'} (e : IsPullForm h ω ω') :
    ω' = pullForm h ω :=
  (existsUnique_isPullForm h ω).unique e (isPullForm_pullForm h ω)

end GlobalTheory.CechDR
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}

theorem exists_cob_of_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (f : Z1 (OAff s'))
    (g : ∀ p : Pair φ, (OAff s').obj (op p.1.1))
    (hg : ∀ (p q : Pair φ) (hqp : q ≤ p), f.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
      g q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g p)) :
    ∃ G : C0 (OAff s'), d0 (OAff s') G = f.1 ∧ ∀ (W : X'.affineOpens) (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op (G (op W)) = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
  have ex : ∀ W : X'.affineOpens, ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op G = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
    intro W
    refine GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs φ s' W _ fun p q hp hq hqp ↦ ?_
    have e := Z1.comp f (homOfLE hp).op (homOfLE (Pair.le_fst hqp)).op
    rw [show (homOfLE hp).op ≫ (homOfLE (Pair.le_fst hqp)).op = (homOfLE hq).op from rfl, hg p q hqp] at e
    rw [map_sub, e]
    ring
  choose G hG using ex
  refine ⟨fun T ↦ G T.unop, ?_, hG⟩
  funext T T' a
  refine sec_eq_of_pair φ s' T'.unop _ _ fun p hp ↦ ?_
  have e1 := Z1.comp f a (homOfLE hp).op
  have e2 : a ≫ (homOfLE hp).op = (homOfLE (hp.trans (leOfHom a.unop))).op := rfl
  rw [e2] at e1
  rw [amitsur_d0_apply, map_sub, ← mp_comp, e2, hG, hG]
  linear_combination e1

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential

theorem pairRes_injective : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧
      Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by
  intro R' _ X X' φ s'
  refine ⟨?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    obtain ⟨G, hG, -⟩ := exists_cob_of_pair φ s' f (fun p ↦ g (op p)) fun p q hqp ↦
      (congrFun (congrFun (congrFun hg (op p)) (op q)) (homOfLE hqp).op).symm
    exact H1.mk_eq_zero.2 ⟨G, hG⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    have h0 : ∀ p : Pair φ, ω.1 (op p.1.1) = 0 := fun p ↦
      (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) (op p) _).symm.trans
        (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 (op p)) hω)
    refine Subtype.ext (funext fun W ↦ GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop _ fun p hp ↦ ?_)
    rw [← ω.2 (homOfLE hp).op]
    exact h0 p
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := Hyp1.mk_surjective _ c
    rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let g' : ∀ p : Pair φ, (OAff s').obj (op p.1.1) := fun p ↦ g (op p)
    have hf : ∀ (p q : Pair φ) (hqp : q ≤ p), z.1.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
        g' q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g' p) := fun p q hqp ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.1 (op p) (op q) (homOfLE hqp).op) hg).symm
    have hω : ∀ p : Pair φ, D R' _ (g' p) = z.1.2 (op p.1.1) := fun p ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.2 (op p)) hg).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor _ _ _ _)
    obtain ⟨G, hG, hGp⟩ := exists_cob_of_pair φ s' (cechDeRhamTotalCocyclesOne.fn _ z) g' hf
    refine Hyp1.mk_eq_zero.2 ⟨G, Tot1.ext (fun T T' a ↦ congrFun (congrFun (congrFun hG T) T') a)
      fun W ↦ ?_⟩
    refine (sub_eq_zero.1 (GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop (D R' _ (G W) - z.1.2 W) fun p hp ↦ ?_))
    have e := cechDeRhamTotalCocyclesOne.conn z (homOfLE hp).op
    rw [map_sub, p1_D, hGp, map_sub, hω]
    change _ - (p1 _ _ _) = _
    rw [e, show ((cechDeRhamTotalCocyclesOne.fn (OAff s') z : Z1 (OAff s')) : C1 (OAff s')) = z.1.1 from rfl]
    abel

end GlobalTheory.CechDR
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.LevelCmp

variable {R : Type} [CommRing R]

theorem cpull_comp_fun {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (I : Cx R) (n : ℤ) :
    ⇑(cpull (a ≫ b) I n) = ⇑(cpull a I n) ∘ ⇑(cpull b I n) :=
  funext fun x => (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 a b I n x

theorem cpull_bij_of_heq {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  obtain ⟨hid, -, -, -, hhom⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have h1 := (hhom _ _ ⟨e.homotopyHomInvId⟩ I n).1
  have h2 := (hhom _ _ ⟨e.homotopyInvHomId⟩ I n).1
  have l1 : ∀ y, cpull e.hom I n (cpull e.inv I n y) = y := fun y => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.hom e.inv I n y, h1]; exact (hid _ _ _ _).1
  have l2 : ∀ x, cpull e.inv I n (cpull e.hom I n x) = x := fun x => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.inv e.hom I n x, h2]; exact (hid _ _ _ _).1
  exact ⟨Function.LeftInverse.injective l2, Function.RightInverse.surjective l1⟩

theorem cpull_bij_of_iso {K L : Cx R} (f : K ⟶ L) [IsIso f] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull f I n) :=
  cpull_bij_of_heq (HomotopyEquiv.ofIso (asIso f)) I n

end GlobalTheory.EtC.LevelCmp


open GlobalTheory.EtC.LevelCmp in
theorem GlobalTheory.EtC.levelwise_eqv : GlobalTheory.EtC.A3 := by
  intro R _ E E' f F hlev
  obtain ⟨hle, hnat, -⟩ := GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  obtain ⟨-, hinj, hge, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  haveI := hle E; haveI := hle E'; haveI := hge
  intro n
  refine GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective R (res R F) hinj ((chains R).map f) ?_ n
  intro p k
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ) := ⟨(-p).toNat, by omega⟩
    set φ := f.app (op (SimplexCategory.mk m))

    have hfree : Function.Bijective
        (cpull ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map φ)) (res R F) k) := by
      have hc := congrArg (fun g => ⇑(cpull g (res R F) k)) (he φ)
      simp only [cpull_comp_fun] at hc
      have hr : Function.Bijective (⇑(cpull (e _).hom (res R F) k) ∘
          ⇑(cpull ((chains R).map (disc.map φ)) (res R F) k)) :=
        (cpull_bij_of_heq (e _) _ k).comp (hlev (op (SimplexCategory.mk m)) k)
      rw [hc] at hr
      exact (Function.Bijective.of_comp_iff _ (cpull_bij_of_heq (e _) _ k)).1 hr
    have hg : ((chains R).map f).f (-(m : ℤ)) =
        (chainsXIso R E m).hom ≫ (free R).map φ ≫ (chainsXIso R E' m).inv := by
      rw [← Category.assoc, ← hnat f m]; simp
    rw [hg, Functor.map_comp, Functor.map_comp, cpull_comp_fun, cpull_comp_fun]
    exact (cpull_bij_of_iso _ _ k).comp (hfree.comp (cpull_bij_of_iso _ _ k))
  · have h1 : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    have h2 : IsZero (((chains R).obj E').X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    haveI : IsIso (((chains R).map f).f p) := ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩
    exact cpull_bij_of_iso _ _ k
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_top_formalLog_constOne : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q] (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 → DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  first | exact @GlobalTheory.QLog.dIn_top_formalLog_map | exact GlobalTheory.QLog.dIn_top_formalLog_map | (intros; apply GlobalTheory.QLog.dIn_top_formalLog_map <;> assumption)
end
