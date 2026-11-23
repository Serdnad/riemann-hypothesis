module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExponentialConjugate
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.CountSpanSingletonAlgebraMapEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle033
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ArchConj

section Diff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt.Arch GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
open GlobalTheory.ArchMetricCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem fderiv_star_star_zero {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (star ∘ F ∘ star) 0 (star w) = star (fderiv ℂ F 0 w) := by
  apply _root_.GlobalTheory.CompanionTheory.Ar.Flat.ConjExp.fderiv_conj_zero <;> assumption

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)
variable {X : Scheme.{0}} {L : LB X} {φ : A.left ⟶ X} {g : ℕ} (u : HolUnif A (L.pull φ) g)

theorem cj_isDiff' {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'}
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    (cjUnif h u).IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := fun q _ => by
    have := subsingleton_dual ℂ
    have hq := hU (show q ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rw [e2] at hq
    rw [Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) q (spMap (dualMap (starRingEnd ℂ)) q)]
    exact hq
  have e1 : (fun z => valAt' ((cjUnif h u).ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => cj_val h _ U f
  rw [e1, fderiv_star_star_zero]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg (starRingEnd ℂ) e3

theorem isLieNormAt_conjugate {K : Type} [Field K] {P : Out.PolAV (Sp K)} {σ : K →+* ℂ} {t : epsR K ⟶ P.A} {v : ℝ}
    (H : IsLieNormAt P t σ v) : IsLieNormAt P t (ComplexEmbedding.conjugate σ) v := by
  obtain ⟨P', φ, w, t', h, hw, e, u, Hm, χ, z, hAH, hd, rfl⟩ := H
  have hg := g_eq h
  obtain ⟨A', _, ψ, hc⟩ : ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (ψ : A'.left ⟶ P'.A.left),
      IsGrpPullback A' P'.A cj ψ := ⟨_, _, _, isGrpPullback_pullback P'.A cj⟩
  have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ t'.left) ≫ P'.A.hom = (epsR ℂ).hom ≫ cj := by
    rw [Category.assoc, Over.w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let t'' : epsR ℂ ⟶ A' := Over.homMk (hc.1.lift _ _ sq) (hc.1.lift_snd _ _ _)
  have e' : t''.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left := hc.1.lift_fst _ _ _
  have h' : IsGrpPullback A' P.A (spMap (ComplexEmbedding.conjugate σ)) (ψ ≫ φ) :=
    (hc.comp h).congr (spMap_conjugate σ) rfl
  have e'' : t''.left ≫ ψ ≫ φ = spMap (dualMap (ComplexEmbedding.conjugate σ)) ≫ t.left := by
    rw [← Category.assoc, e', Category.assoc]
    refine (congrArg _ e).trans ?_
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap]
  have hM := pull_isLB P.isLB φ
  have hAH' := cj_isAH hc (carry u P'.isLB hM hw) (carry_isAH _ _ hw hAH)
  have hd' := cj_isDiff' hc (carry u P'.isLB hM hw) e' (w := z) hd
  have hz : (z ⬝ᵥ Hm.mulVec (star z)).re = (star z ⬝ᵥ (Hm.map star).mulVec (star (star z))).re := by
    have := hermSq_star Hm (star z)
    rw [star_star] at this
    exact this.symm
  obtain ⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩ := P
  obtain rfl : P'.g = g := hg
  exact ⟨pullPol _ h', ψ ≫ φ, idIso _, t'', h', idIso_isGen (pull_isLB isLB _), e'',
    cjUnif hc (carry u P'.isLB hM hw), _, _, star z, hAH', hd', by rw [hz]; rfl⟩

end Diff

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem norms_conj : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th ((starRingEnd ℂ).comp σ) v) ∧ ∀ η' : epsR K ⟶ P.A, Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' ((starRingEnd ℂ).comp σ) v :=
  fun _ _ _ P σ v => ⟨fun rig th H => (ArchMetricCompare.isL2Sq_iff_isThNormAt P rig _ th v).1
    (ArchMetricCompare.isL2Sq_conjugate_embedding ((ArchMetricCompare.isL2Sq_iff_isThNormAt P rig σ th v).2 H)),
    fun _ H => isLieNormAt_conjugate H⟩

end GlobalTheory.ArchConj
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem nfac_of_add {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la l₁ l₂ : Wt X.Ψ r) (h : ∀ τ i, la τ i = l₁ τ i + l₂ τ i) :
    X.nfac la x = X.nfac l₁ x * X.nfac l₂ x := by
  simp only [Data.nfac, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_add (norm_pos_iff.mpr
    (div_ne_zero (FlowCoefficientBounds.dmin_ne X hx τ _) (FlowCoefficientBounds.dmin_ne X hx τ _))), h]
  congr 1
  push_cast
  ring

theorem arch_bound_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : (U.X k).dom) (C ep xi : ℝ) (κ : ℂ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → 0 < C → 0 < ep → Even n → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 → ∃ hx : (U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1 ∈ (U.X k).dom, (∀ τ, (U.X k).tt ξ' ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1) τ = ep) ∧ (∀ (P : Frame (U.X k).Ψ r → ℂ) (ν : (U.X k).Ψ → ℝ), (U.X k).IsBddSec (laU U a' n k) P → ‖(U.X k).fj (laU U a' n k) ξ' ν P x.1‖ = Real.exp (4 * Real.pi * ∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ)) * ‖(U.X k).fj (laU U a' n k) ξ' ν P ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1)‖) ∧ ∀ Hm, IsRiem Uw.F (Uw.ik k) (Uw.Pm k ⟨_, hx⟩) Hm → ‖κ‖ / (lieFac Dw xi a' * (U.X k).nfac (laU U a' n k) ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1)) ≤ (C * (ep⁻¹) ^ (U.X k).Ψ.card) ^ ((n : ℝ) / 2) * ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U Uw k ξ' x C ep xi κ a' n hσ hU hξ hC hep hn hxi hκ
  have him : ∀ τ, (U.X k).tt ξ' x.1 τ +
      ((((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I)).im = ep := by
    intro τ; simp
  have hd := GlobalTheory.FjCauchy.flow_mem_dom (U.X k) hξ x.2
    (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) (fun τ => by rw [him]; exact hep)
  have ht : ∀ τ, (U.X k).tt ξ' ((U.X k).flow ξ'
      (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1) τ = ep := fun τ => by
    rw [GlobalTheory.FjCauchy.tt_flow (U.X k) hξ x.2 _ hd, him]
  refine ⟨hd, ht, ?_, ?_⟩
  · intro P ν hP
    rw [GlobalTheory.FjCauchy.fj_flow (U.X k) hP hξ ν x.2 _ hd, norm_mul, ← mul_assoc, Complex.norm_exp,
      ← Real.exp_add]
    have hs : ∑ τ, (ν τ : ℂ) * (((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) =
        ((∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Complex.ofReal_mul, mul_assoc]
    rw [hs]
    generalize (∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ) : ℝ) = S
    have : (4 * (Real.pi : ℂ) * Complex.I * ((S : ℂ) * Complex.I)).re = -(4 * Real.pi * S) := by
      simp
    rw [this, add_neg_cancel, Real.exp_zero, one_mul]
  · intro Hm hH
    have hb := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k ⟨_, hd⟩ Hm hσ hU hH).2.2 xi a' hxi
    have hf := nfac_parallel_flow E H Dw l Xo c σ r U k n ξ' hn hξ x.1 x.2 _ hd
    have hadd := nfac_of_add (U.X k) hd (laU U a' n k) (laU U a' 0 k) (laU U 0 n k) (by
      intro τ j
      simp only [laU]
      split_ifs <;> simp <;> ring)
    have hN := FlowCoefficientBounds.nfac_pos (U.X k) hd (laU U 0 n k)
    have hA := FlowCoefficientBounds.nfac_pos (U.X k) hd (laU U a' 0 k)
    have hL := lieFac_pos Dw xi a'
    simp only [ht, Finset.prod_const, Finset.card_univ, Fintype.card_coe] at hf
    have hp : 0 ≤ ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹ :=
      Finset.prod_nonneg fun τ _ => (inv_pos.mpr (GlobalTheory.FjCauchy.tt_pos (U.X k) hξ x.2 τ)).le
    have he : 0 ≤ (ep⁻¹) ^ (U.X k).Ψ.card := by positivity
    rw [hκ, hadd, Real.mul_rpow hC.le hp, mul_assoc, mul_comm _ ((U.X k).nfac (laU U 0 n k) x.1), ← hf,
      Real.mul_rpow hC.le he]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hb (by positivity))
    dsimp only
    generalize (U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1 = y at hN hA ⊢
    field_simp

end GlobalTheory.ArcQ
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.theta_l2_family_uniform_compare : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Pm' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (s : CAt σ) (v v' : ℝ), IsPeriod (Fu.Di i) ty Pm → IsPeriod (Fu.Di i') ty Pm' → y.x = Fu.u i Pm → y'.x = Fu.u i' Pm' → FrChg G s y y' → IsThetaL2NormSquared Fu i Pm y v → IsThetaL2NormSquared Fu i' Pm' y' v' → 0 < v ∧ v' = ‖toC s‖ ^ 2 * v := by
  first | exact @GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling | exact GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling | (intros; apply GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

theorem _root_.GlobalTheory.T.constantTangent_eq_formalPoint_transported : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W ex₀ z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left := by
  first | exact @GlobalTheory.ConstTanFormal.main | exact GlobalTheory.ConstTanFormal.main | (intros; apply GlobalTheory.ConstTanFormal.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

theorem _root_.GlobalTheory.T.constantTangent_reduction_eq_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : _root_.GlobalTheory.ArcPts.GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (Ξ : ConstPts W Λ) (v : epsR ℂ⟦X⟧ ⟶ W.t.G) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)), DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → TanRel W ν g₁ → FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v.left → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v.left = (Ξ.x 0).left := by
  first | exact @GlobalTheory.ConstTanRed.main | exact GlobalTheory.ConstTanRed.main | (intros; apply GlobalTheory.ConstTanRed.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TauCanPull

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TauTwist GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem cPoint_unit (D : DegPre R) (y : D.X) : cP D (𝟙_ (Over (Sp R))) y = D.c y := by
  rw [cP, toUnit_unit, Category.id_comp]

theorem c_pow_eq_one_iff (D : DegPre R) (n : ℕ) (y : D.X) : D.c y ^ n = 1 ↔ D.c (n • y) = D.c 0 := by
  rw [← cPoint_unit D (n • y), ← cPoint_unit D 0, cPoint_nsmul, cPoint_zero, cPoint_unit]

theorem c_eq_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (x x' : D'.X) :
    D.c (hD.xe x) = D.c (hD.xe x') ↔ D'.c x = D'.c x' := by
  constructor
  · intro h
    refine Over.OverMorphism.ext ((pull_grp hD).1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hD.c_pr, h]
  · intro h
    haveI : IsDominant (spMap φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)⟩
    haveI : IsProper D.P.A.hom := D.P.isAb.proper
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) D.P.A.hom
      ((Over.w _).trans (Over.w _).symm) (spMap φ)
      ((hD.c_pr x).symm.trans ((congrArg (fun q => q.left ≫ _) h).trans (hD.c_pr x'))))

theorem torsion_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (n : ℕ) :
    (∀ y, D.c y ^ n = 1) ↔ ∀ y, D'.c y ^ n = 1 := by
  rw [hD.xe.surjective.forall]
  refine forall_congr' fun y => ?_
  rw [c_pow_eq_one_iff, c_pow_eq_one_iff, ← c_eq_iff hD hφ, map_nsmul, map_zero]

theorem val_tau_kappa {n : ℕ} (hc : ∀ y, D.c y ^ n = 1) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val (D.tau (n • a) (n • b)) r z J = unitAt r z (kappa hc a b) := by
  have h : LB.Gen.Corr D.P.L _ _ _ _ (D.tau (n • a) (n • b)) (scaleGen (unitOn (kappa hc a b)) (LB.oneGen D.P.L)) :=
    corr_of_val D.P.isLB fun y I hI => (unitAt_kappa hc a b hI).symm.trans
      ((val_scale _ _ _ hI).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))).symm
  exact (val_corr hJ h r).trans ((val_scale _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans
    (_root_.mul_one _)))

theorem kappa_pull (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) {n : ℕ} (hc : ∀ y, D.c y ^ n = 1)
    (hc' : ∀ y, D'.c y ^ n = 1) (a b : D'.X) :
    kappa hc' a b = Units.map (fracMap hφ).toMonoidHom (kappa hc (hD.xe a) (hD.xe b)) := by
  let z : (TK R').left := IsLocalRing.closedPoint (FractionRing R')
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  have e := tau_val hD _ _ (fracMap_sq hφ) hJ hJ' (n • a) (n • b)
  have a₁ : ∀ w : D'.X, D'.xK (n • w) = (1 : TK R' ⟶ D'.P.A).left := fun w =>
    congrArg (fun q => q.left) (cPoint_nsmul_eq_one hc' (TK R') w)
  rw [map_nsmul, map_nsmul, val_tau_kappa hc _ _ _ hJ, val_tau_kappa hc' _ _ _ hJ', ← nsmul_add, a₁, a₁, a₁,
    inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at e
  refine unitAt_injective z (e.symm.trans ?_)
  exact (congrArg (fun q => unitAt q z _) (Category.id_comp (genMap hφ)).symm).trans
    (unitAt_spMap (𝟙 _) (fracMap hφ) z _)

theorem tauCan_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (n : ℕ) :
    ArcCM.TauCan D n ↔ ArcCM.TauCan D' n := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨(torsion_iff hD hφ n).1 hc, fun y y' => ?_⟩
    rw [kappa_pull hD hφ hc, h, map_one]
  · rintro ⟨hc', h⟩
    refine ⟨(torsion_iff hD hφ n).2 hc', fun y y' => ?_⟩
    obtain ⟨y, rfl⟩ := hD.xe.surjective y
    obtain ⟨y', rfl⟩ := hD.xe.surjective y'
    apply Units.map_injective (f := (fracMap hφ).toMonoidHom) (fracMap hφ).injective
    rw [← kappa_pull hD hφ _ hc', h, map_one]

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem tauCan_iff_of_isPullDeg : Known → ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (D₀ : Out.DegPre R) (D₁ : Out.DegPre R') (p : Out.IsPullDeg f D₀ D₁) (n : ℕ), Function.Injective f → D₀.TauBimult → D₁.TauBimult → (TauCan D₀ n ↔ TauCan D₁ n) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ p n hf _ _ => tauCan_iff p hf n

end GlobalTheory.TauCanPull
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem modelsAt_of_good_level : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ModelsAt Xo c := by
  intro hK E _ _ _ H Dw l Xo c hr hg
  classical
  have key : ∀ Xs : ∀ l' : Level H, Moduli Dw l', ModelsAt (Xs l) c := by
    intro Xs p W hp hW
    obtain ⟨Y, hY, -⟩ := hK.models.2 E H Dw hr Xs
    obtain ⟨h2, h4⟩ := hY p W hp hW
    exact ⟨Y p W hp hW ⟨l, c, hg p hp⟩, (h4 _).2.2, (h2.1 ⟨l, c, hg p hp⟩).2.2.1⟩
  have h := key (Function.update (fun l' => Classical.choice (hK.n1ab E H Dw l' hr)) l Xo)
  rwa [Function.update_self] at h

end GlobalTheory.ArcCM
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

section

variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

theorem ordAt_eq_count (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    ordAt v x = FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) := by
  rw [ordAt, valuation_eq_exp_neg_count v hx, WithZero.log_exp, neg_neg]

theorem ordAt_algebraMap_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {v : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w v) (x : K) :
    ordAt w (algebraMap K K₁ x) = (w.asIdeal.ramificationIdx (𝓞 K) : ℤ) * ordAt v x := by
  have : w.asIdeal.LiesOver v.asIdeal := ⟨h.symm⟩
  rw [ordAt, ordAt, ← HeightOneSpectrum.valuation_liesOver K₁ v w x, WithZero.log_pow,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  simp

theorem count_bcI_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {v : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w v) (N : MLine K) (hN : N.I ≠ 0) :
    FractionalIdeal.count K₁ w (bcI (K1 := K₁) N.I) =
      (w.asIdeal.ramificationIdx (𝓞 K) : ℤ) * FractionalIdeal.count K v N.I := by
  obtain ⟨c, hc⟩ := v.valuation_surjective K (WithZero.exp (-FractionalIdeal.count K v N.I))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have h1 : ordAt v c = FractionalIdeal.count K v N.I := by
    rw [ordAt, hc, WithZero.log_exp, neg_neg]
  have hg : IsLocGen v c N.I := ⟨hc0, by rw [← ordAt_eq_count v hc0, h1]⟩
  have h2 := local_generator_base_change K K₁ N ⟨bcI N.I, fun σ => N.n (σ.comp (algebraMap K K₁))⟩ v w c hN
    ⟨coe_bcI N.I, fun _ => rfl⟩ (fun a => by rw [← h]; rfl) hg
  rw [← h1, ← ordAt_algebraMap_of_liesOver h, ordAt_eq_count w h2.1]
  exact h2.2.symm

end

theorem numGood_comp : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (M : Set V) (S : (K →+* ℂ) → V → ℝ) (be : HeightOneSpectrum (𝓞 K) → ℝ) (Carch Bdeg : ℝ) (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁] [Algebra K K₁] (f : K' →ₐ[K] K₁) (φ : V →ₗ[K] K'), NumGood M S be Carch Bdeg K' φ → NumGood M S be Carch Bdeg K₁ (f.toLinearMap.comp φ) := by
  intro K V _ _ _ _ M S be Carch Bdeg K' K₁ _ _ _ _ _ _ f φ ⟨N, hG, hd, hc, hf, ha⟩
  letI : Algebra K' K₁ := f.toRingHom.toAlgebra
  haveI : IsScalarTower K K' K₁ := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hap : ∀ F, (f.toLinearMap.comp φ) F = algebraMap K' K₁ (φ F) := fun _ => rfl
  have hne : ∀ F, (f.toLinearMap.comp φ) F ≠ 0 → φ F ≠ 0 := fun F h h0 => h (by rw [hap, h0, map_zero])
  have hb := nondegenerate_base_change K' K₁ N ⟨bcI N.I, fun σ => N.n (σ.comp (algebraMap K' K₁))⟩ hG
    ⟨coe_bcI N.I, fun _ => rfl⟩
  refine ⟨⟨bcI N.I, fun σ => N.n (σ.comp (algebraMap K' K₁))⟩, hb.1, hb.2.le.trans hd, fun σ => ?_, ?_, ?_⟩
  · exact hc (σ.comp (algebraMap K' K₁))
  · intro la w hw F hF h0
    let v : HeightOneSpectrum (𝓞 K') := w.under (𝓞 K')
    have hwv : LiesOver w v := rfl
    have hv : LiesOver v la := by
      have hw' : w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁)) = la.asIdeal := hw
      rw [IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 K') (𝓞 K₁), ← Ideal.comap_comap] at hw'
      exact hw'
    have : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
    have h1 := hf la v hv F hF (hne F h0)
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (w.asIdeal.ramificationIdx (𝓞 K')))
    rw [hap, ordAt_algebraMap_of_liesOver hwv, count_bcI_of_liesOver hwv N hG.1,
      Ideal.ramificationIdx_tower (R := 𝓞 K) v.asIdeal w.asIdeal]
    push_cast
    linarith
  · intro σ F hF h0
    have h1 := ha (σ.comp (algebraMap K' K₁)) F hF (hne F h0)
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at h1
    exact h1

end GlobalTheory.ArcCM
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.framedPoint_eval_natural_weight_scaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∀ (S : Type) [CommRing S] [Algebra c.F S] [IsReduced S], (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c F z = φ (evR Xo c F y)) ∧ (IsDomain S → (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y) ∧ ∀ (s : S) (y y' : FrPt Xo c S), FrChg (fun _ => 1) s y y' → evR Xo c F y' = s ^ n * evR Xo c F y) := by
  first | exact @GlobalTheory.ArcQ.evR_natural_weight_scaling | exact GlobalTheory.ArcQ.evR_natural_weight_scaling | (intros; apply GlobalTheory.ArcQ.evR_natural_weight_scaling <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.triple_iso_respects_level_ratio_points : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ) (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)) (k : ℕ) (ψ : I k → V → F) (p₁ : Over.mk (𝟙 (Sp F)) ⟶ o₁.t.G) (p₂ : Over.mk (𝟙 (Sp F)) ⟶ o₂.t.G), 1 ≤ k → w.IsGen → (∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j') → Θ₁.Lev k p₁ ψ → Θ₂.Lev k p₂ ψ → p₁.left ≫ m.φ = p₂.left := by
  first | exact @GlobalTheory.LevelRespect.level_pt_eq | exact GlobalTheory.LevelRespect.level_pt_eq | (intros; apply GlobalTheory.LevelRespect.level_pt_eq <;> assumption)
end
