module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsProperCurveThroughPoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle050
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.WithLp
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefCurveTest

theorem smoothOfRelativeDimension_one {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (s : C ⟶ Sp k) [Smooth s]
    (hd : topologicalKrullDim C = 1) : SmoothOfRelativeDimension 1 s := by
  obtain ⟨n, hn⟩ : ∃ n, SmoothOfRelativeDimension n s := exists_dim_of_preconnected s (genericPoint C)
  obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have e := (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).symm.trans
    (SmoothDim.ringKrullDim_affineOpen k _ _ _ hn U hU ⟨x, hxU⟩)
  obtain rfl : 1 = n := by exact_mod_cast e
  exact hn

theorem exists_smooth_finite {k : Type} [Field k] [IsAlgClosed k] {D : Scheme.{0}} [IsIntegral D] (s : D ⟶ Sp k)
    [IsProper s] (hd : topologicalKrullDim D = 1) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (f : C ⟶ D), IsFinite f ∧ f (genericPoint C) = genericPoint D ∧
      topologicalKrullDim C = 1 ∧ Smooth (f ≫ s) := by
  let f := D.fromSpecResidueField (genericPoint D)
  let c := f.fromNormalization
  haveI : IsFinite c := NormCurve.isFinite_fromNormalization f s
  have htr : letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
      Algebra.trdeg k Γ(Spec (D.residueField (genericPoint D)), ⊤) ≤ 1 := by
    obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    have e : ⊤ ≤ f ⁻¹ᵁ U := fun z _ => by
      change f z ∈ U
      rw [Scheme.fromSpecResidueField_apply]
      exact VB.genericPoint_mem hxU
    letI := (NormCurve.constHom s U).toAlgebra
    haveI : Algebra.FiniteType k Γ(D, U) := NormCurve.finiteType_constHom s hU
    haveI : Nonempty (⊤ : (Spec (D.residueField (genericPoint D))).Opens) :=
      ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
    letI := (NormCurve.isField_sections (⊤ : (Spec (D.residueField (genericPoint D))).Opens)).toField
    letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
    letI := (f.appLE U ⊤ e).hom.toAlgebra
    haveI : IsScalarTower k Γ(D, U) Γ(Spec (D.residueField (genericPoint D)), ⊤) :=
      .of_algebraMap_eq' (NormCurve.appLE_comp_constHom s f U ⊤ e).symm
    exact (NormCurve.finite_integralClosure k (NormCurve.surjectiveOnStalks_appLE f hU ⊤ e)).2
      ((ringKrullDim_quotient_le _).trans (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).le)
  have hξ : genericPoint D ∈ Set.range c := by
    refine ⟨f.toNormalization (Nonempty.some inferInstance), ?_⟩
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization, Scheme.fromSpecResidueField_apply]
  have hs : Function.Surjective c := fun y =>
    (genericPoint_specializes y).mem_closed c.isClosedMap.isClosed_range hξ
  have hη : c (genericPoint _) = genericPoint D := by
    obtain ⟨y, hy⟩ := hξ
    refine ((genericPoint_specializes _).antisymm ?_).eq.symm
    exact ((genericPoint_specializes y).map c.continuous).trans (specializes_of_eq hy)
  exact ⟨f.normalization, inferInstance, c, inferInstance, hη,
    ((Published.dim_le_of_isIntegralHom c).antisymm (PosBaseChange.dim_le_of_isClosedMap c.isClosedMap hs)).trans hd,
    CurveThrough.smooth_of_dedekind_charts k _ _ (NormCurve.isDedekindDomain_sections f s htr)⟩

def CurveTest (K : Type) [Field K] {X : Scheme.{0}} (L : LB X) : Prop :=
  ∀ (C : Scheme.{0}) [Algebra K Γ(C, ⊤)], SmoothOfRelativeDimension 1 (strHom K (X := C)) → IsProjOver (strHom K (X := C)) →
    GeometricallyConnected (strHom K (X := C)) → ∀ g : C ⟶ X, 0 ≤ interNum K (structureModule C) ![L.pull g]

theorem CurveTest.pull {K : Type} [Field K] {X Y : Scheme.{0}} {L : LB X} (h : CurveTest K L) (hL : L.IsLB)
    (π : Y ⟶ X) : CurveTest K (L.pull π) := fun C _ hs hp hc g => by
  refine (h C hs hp hc (g ≫ π)).trans_eq (interNum_congr_cls K _ (isLB_vecOne (LB.isLB_pull hL _))
    (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hL _) _)) fun j => ?_)
  fin_cases j
  exact pull_comp g π (cls L hL)

theorem CurveTest.isNef_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)]
    {L : LB X} (h : CurveTest K L) (hL : L.IsLB) : IsNef K L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong K i
  have hi := appTop_algebraMap_along K i
  rw [comp_strHom hi] at hp
  obtain ⟨C, _, f, _, hη, hdC, hs⟩ := exists_smooth_finite (strHom K D) hd
  letI := algebraΓAlong K f
  have hf := appTop_algebraMap_along K f
  have hpC : IsProper (f ≫ strHom K D) := inferInstance
  rw [comp_strHom hf] at hs hpC
  have hM := LB.isLB_pull hL i
  have h₀ := h.pull hL i C (smoothOfRelativeDimension_one _ hdC) (ProperCurve.isProjOver_of_isProper _ hdC)
    (geometricallyConnected_of_isAlgClosed _) f
  have e₁ := ProjFin.interNumOn_eq_residueDegree_mul K D C f (ProperCurve.isProjOver_of_isProper _ hd) hd hη _ hM
  rw [interNumOn_eq_interNum_pull hf (isLB_vecOne hM)] at e₁
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL)]
  have hdeg : 0 < f.residueDegree (genericPoint C) := Nat.pos_of_ne_zero
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite f _).2 (residueFieldMap_finite_of_locallyQuasiFinite f _))
  have e₂ : (fun j => ((![L.pull i] : Fin 1 → LB D) j).pull f) = ![(L.pull i).pull f] :=
    funext fun j => by fin_cases j; rfl
  have e₃ : (fun j => ((![L] : Fin 1 → LB X) j).pull i) = ![L.pull i] := funext fun j => by fin_cases j; rfl
  rw [e₂] at e₁
  rw [e₃]
  rw [e₁] at h₀
  exact nonneg_of_mul_nonneg_right h₀ (by exact_mod_cast hdeg)

theorem CurveTest.isNef (hN : Published.NefProductNonneg) {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    {L : LB X} (h : CurveTest (AlgebraicClosure k) L) (hL : L.IsLB) : IsNef k L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong k i
  have hi := appTop_algebraMap_along k i
  rw [comp_strHom hi] at hp
  have hM := LB.isLB_pull hL i
  obtain ⟨D', _, π, hp', hd', -, -, he⟩ :=
    Published.exists_algClosed_baseChange (ProperCurve.isProjOver_of_isProper (strHom k D) hd)
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL), ← he 1 _ fun j => LB.isLB_pull (isLB_vecOne hL j) i]
  refine hN _ D' 1 hp' (hd'.trans hd) _ fun j => ?_
  fin_cases j
  exact ((h.pull hL i).pull hM π).isNef_of_isAlgClosed (LB.isLB_pull hM π)

end GlobalTheory.NefCurveTest
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_descent_mumfordBundle_quotient : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → (∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x) → ∀ (B : Over (Sp R)) [GrpObj B] (q : A ⟶ B), IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q → ∃ (P : LB (A ⊗ B).left) (hP : P.IsLB), ∀ (Y : Over (Sp R)) (a x : Y ⟶ A), evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
  first | exact @GlobalTheory.QuotDesc.exists_descent_lam | exact GlobalTheory.QuotDesc.exists_descent_lam | (intros; apply GlobalTheory.QuotDesc.exists_descent_lam <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.hasGenerator_lambdaPullback_complexPoint_of_eqOnOpen : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A) (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (t : T.left), t ∈ U →
      U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) := by
  first | exact @GlobalTheory.PointDesc.hasGen_lam_pull_of_eq_on_open | exact GlobalTheory.PointDesc.hasGen_lam_pull_of_eq_on_open | (intros; apply GlobalTheory.PointDesc.hasGen_lam_pull_of_eq_on_open <;> assumption)
end
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.PullSmooth

theorem repr_mul {m : ℕ} (a b : Alt m) (S : Finset (Fin (m + m))) :
    (bas m).repr (a * b) S = ∑ S₁, ∑ S₂, (bas m).repr a S₁ * (bas m).repr b S₂ *
      (bas m).repr (bas m S₁ * bas m S₂) S := by
  conv_lhs => rw [← (bas m).sum_repr a, ← (bas m).sum_repr b]

  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]

theorem entries_smooth {m n : ℕ} {τ : V m → V n} {U : Set (V m)} (hU : IsOpen U) (hτ : DifferentiableOn ℂ τ U)
    (v : V m) (a : Fin n) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U ∧ ContDiffOn ℝ ∞ (fun x => conj (fderiv ℂ τ x v a)) U := by
  have h₁ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x) U :=
    ContDiffOn.fderiv_of_isOpen (n := ω) (m := ∞)
      (((GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn hU).2 hτ).contDiffOn hU.uniqueDiffOn) hU le_top
  have h₂ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x v a) U :=
    (EuclideanSpace.proj a : V n →L[ℂ] ℂ).contDiff.comp_contDiffOn (h₁.clm_apply contDiffOn_const)
  have h₃ : ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U := h₂.restrict_scalars ℝ
  exact ⟨h₃, Complex.conjCLE.contDiff.comp_contDiffOn h₃⟩

theorem contDiffOn_repr_pull_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U →
    DifferentiableOn ℂ τ U → ∀ S, ContDiffOn ℝ ∞ (fun x => (bas m).repr (pull (fderiv ℂ τ x) γ) S) U := by
  intro m n τ U γ hU hτ
  induction γ using ExteriorAlgebra.induction with
  | algebraMap r =>
    intro S
    simp only [AlgHom.commutes]
    exact contDiffOn_const
  | ι u =>
    intro S
    have hcoef : ∀ x, (bas m).repr (pull (fderiv ℂ τ x) (ExteriorAlgebra.ι ℂ u)) S =
        ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)
          (Matrix.toLin' (Matrix.fromBlocks (Matrix.of fun b a => fderiv ℂ τ x (coordVec b) a) 0 0
            (Matrix.of fun b a => conj (fderiv ℂ τ x (coordVec b) a))) u) := by
      intro x
      simp [pull, ExteriorAlgebra.map_apply_ι]
    simp_rw [hcoef]
    refine (LinearMap.toContinuousLinearMap ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)).contDiff.restrict_scalars ℝ
      |>.comp_contDiffOn ?_
    refine contDiffOn_pi.2 fun i => ?_
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ contDiffOn_const
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).1
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).2
  | mul a b ha hb =>
    intro S
    have e : (fun x => (bas m).repr (pull (fderiv ℂ τ x) (a * b)) S) = fun x => ∑ S₁, ∑ S₂,
        (bas m).repr (pull (fderiv ℂ τ x) a) S₁ * (bas m).repr (pull (fderiv ℂ τ x) b) S₂ *
          (bas m).repr (bas m S₁ * bas m S₂) S := funext fun x => by rw [map_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun S₁ _ => ContDiffOn.sum fun S₂ _ =>
      ((ha S₁).mul (hb S₂)).mul contDiffOn_const
  | add a b ha hb =>
    intro S
    simp only [map_add (f := _), Finsupp.add_apply]
    exact (ha S).add (hb S)

end GlobalTheory.PullSmooth
end

section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem contDiffOn_real_transition (i j : A.ι) :
    ContDiffOn ℝ ∞ (A.e j ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' (A.e j).source) :=
  (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real
    ((A.e i).isOpen_inter_preimage_symm (A.e j).open_source) (differentiableOn_euclidean.1 (A.holo i j) a)

theorem exists_smooth_bump [T2Space M] (x : M) :
    ∃ (i : A.ι) (ψ : M → ℝ), A.SmoothOn univ (fun y => (ψ y : ℂ)) ∧ tsupport ψ ⊆ (A.e i).source ∧
      ∀ᶠ y in 𝓝 x, ψ y = 1 := by
  classical
  obtain ⟨i, hxe⟩ := A.cover x
  set e := A.e i with he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxe)
  let β : ContDiffBump (e x) := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hcb : Metric.closedBall (e x) (ε / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set C := e.symm '' Metric.closedBall (e x) (ε / 2) with hC
  have hCc : IsCompact C := (isCompact_closedBall (e x) (ε / 2)).image_of_continuousOn
    (e.continuousOn_symm.mono fun y hy => hcb hy)
  have hCsub : C ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hcb hy)
  let ψ : M → ℝ := fun w => if w ∈ e.source then β (e w) else 0
  have hsupp : Function.support ψ ⊆ C := by
    intro w hw
    simp only [Function.mem_support, ψ] at hw
    split_ifs at hw with hws
    · have : e w ∈ Metric.ball (e x) (ε / 2) := by
        rw [← β.support_eq]; exact hw
      exact ⟨e w, Metric.ball_subset_closedBall this, e.left_inv hws⟩
    · exact absurd rfl hw
  have hts : tsupport ψ ⊆ C := closure_minimal hsupp hCc.isClosed
  refine ⟨i, ψ, ?_, hts.trans hCsub, ?_⟩
  · intro k
    rw [preimage_univ, inter_univ]
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    by_cases hys : (A.e k).symm y ∈ e.source
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' e.source,
        (A.e k).isOpen_inter_preimage_symm e.open_source, ⟨hy, hys⟩, ?_⟩
      have hβ : ContDiff ℝ ∞ (fun y : V n => ((β y : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp β.contDiff
      refine ((hβ.comp_contDiffOn (A.contDiffOn_real_transition k i)).mono inter_subset_right).congr
        fun v hv => ?_
      have hv1 : (A.e k).symm v ∈ e.source := hv.2.2
      simp only [Function.comp, ψ, if_pos hv1]
      rfl
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' Cᶜ,
        (A.e k).isOpen_inter_preimage_symm hCc.isClosed.isOpen_compl,
        ⟨hy, fun h => hys (hCsub h)⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun v hv => ?_
      have : ψ ((A.e k).symm v) = 0 := by
        by_contra h
        exact hv.2.2 (hsupp h)
      simp [Function.comp, this]
  · have ho : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e x) (ε / 4)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [ho.mem_nhds ⟨hxe, Set.mem_preimage.mpr (Metric.mem_ball_self (by linarith))⟩] with w hw
    simp only [ψ, if_pos hw.1]
    exact β.one_of_mem_closedBall (Metric.ball_subset_closedBall hw.2)

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory

theorem exists_finite_smooth_partition_holAtlas {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] {n : ℕ}
    (A : GlobalTheory.CxForm.HolAtlas M n) :
    ∃ (N : ℕ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧
      (∀ j, tsupport (χ j) ⊆ (A.e (c j)).source) ∧ ∀ y, ∑ j, χ j y = 1 := by
  classical
  choose E Ψ hΨs hΨt hΨ1 using A.exists_smooth_bump
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => interior {y | Ψ x y = 1})
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hΨ1 y)⟩)
  let p : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  let ψ : Fin t.card → M → ℝ := fun i => Ψ (p i)
  have hsum : ∀ x, ∑ i, ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x) =
      1 - ∏ i, (1 - ψ i x) := fun x => by
    rw [Finset.prod_one_sub_ordered]; ring
  refine ⟨t.card, fun i => E (p i), fun i x => ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x),
    fun i k => ?_, fun i => (tsupport_mul_subset_left).trans (hΨt (p i)), fun x => ?_⟩
  · refine ((hΨs (p i) k).mul (contDiffOn_prod (t := Finset.univ.filter (· < i))
      fun j _ => (contDiffOn_const (c := (1 : ℂ))).sub (hΨs (p j) k))).congr fun v _ => ?_
    simp [Function.comp, ψ]
  · rw [hsum]
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 : ψ (t.equivFin ⟨u, hu⟩) x = 1 := by
      have : p (t.equivFin ⟨u, hu⟩) = u := by simp [p]
      simp only [ψ, this]
      exact (interior_subset hxu : x ∈ {y | Ψ u y = 1})
    rw [Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨u, hu⟩)) (by rw [h1]; ring)]
    ring

end GlobalTheory
end

section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.SmoothCoef

theorem contDiffOn_del_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => del f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [del_apply]
  exact ((h.clm_apply contDiffOn_const).sub ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_dbar_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => dbar f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [dbar_apply]
  exact ((h.clm_apply contDiffOn_const).add ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_coef : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧
      ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  intro n s F hs hF U
  constructor

  · simp only [delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul]
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_del_dir hs (hF S) _).mul contDiffOn_const

  · simp only [dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul]
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_dbar_dir hs (hF S) _).mul contDiffOn_const

end GlobalTheory.CxForm.SmoothCoef
end

section

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem coefwise_dbar_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) (w : V n) :
    coefwise (fun f => GlobalTheory.dbar f v w) (fun x => ∑ i, c i x • F i x) =
      ∑ i, (GlobalTheory.dbar (c i) v w • F i v + c i v • coefwise (fun f => GlobalTheory.dbar f v w) (F i)) := by
  have h (S : Finset (Fin (n + n))) :
      GlobalTheory.dbar (fun x => (bas n).repr (∑ i, c i x • F i x) S) v w =
        ∑ i, (c i v * GlobalTheory.dbar (fun x => (bas n).repr (F i x) S) v w +
          GlobalTheory.dbar (c i) v w * (bas n).repr (F i v) S) := by
    have e : (fun x => (bas n).repr (∑ i, c i x • F i x) S) =
        fun x => ∑ i, c i x * (bas n).repr (F i x) S := by
      funext x

      simp [map_sum, Finsupp.finsetSum_apply]
    rw [e, GlobalTheory.dbar_sum (A := fun i x => c i x * (bas n).repr (F i x) S) (fun i _ => (hc i).mul (hF i S)),
      ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.dbar_mul (hc i) (hF i S) w
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (bas n).sum_repr (F i v)]
  simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  rw [add_comm]

theorem dbarAt_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) :
    dbarAt (fun x => ∑ i, c i x • F i x) v =
      ∑ i, ((∑ a, GlobalTheory.dbar (c i) v (coordVec a) • dzb a) * F i v + c i v • dbarAt (F i) v) := by
  simp only [dbarAt, coefwise_dbar_sum_smul hc hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_add, mul_smul_comm, smul_mul_assoc, Finset.sum_mul, Finset.sum_add_distrib, Finset.smul_sum]

end GlobalTheory.CxForm
end

section

set_option autoImplicit false

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.LocFub.TopDens

theorem dens_smul {n : ℕ} (c : ℂ) (α : Alt n) : dens (c • α) = c * dens α := by
  simp [dens, mul_div_assoc]

theorem dens_add {n : ℕ} (α β : Alt n) : dens (α + β) = dens α + dens β := by
  simp [dens, add_div]

theorem dens_zero {n : ℕ} : dens (0 : Alt n) = 0 := by simp [dens]

end GlobalTheory.LocFub.TopDens
end
