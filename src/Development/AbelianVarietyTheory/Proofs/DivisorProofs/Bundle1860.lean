module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSobolevInequalityAdelicUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedSectionOfBoundedHolomorphicForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualInj

theorem mono_of_points_tangents {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h₁ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y')
    (h₂ : ∀ (k : Type) [Field k] [IsAlgClosed k] (w : Sp (DualNumber k) ⟶ X),
      w ≫ f = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w ≫ f →
        w = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w) : Mono f := by
  have hu : FormallyUnramified f := TangentCrit.formallyUnramified_of_tangent f h₂
  have hs : Surjective (pullback.diagonal f) := by
    apply ((tfae_universallyInjective f).out 2 4).1
    intro k _ y y' e
    let x : Sp (AlgebraicClosure k) ⟶ Sp k := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    have : Surjective x :=
      ⟨fun z => ⟨(default : PrimeSpectrum (AlgebraicClosure k)), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Epi x := Flat.epi_of_flat_of_surjective x
    refine (cancel_epi x).1 (h₁ _ _ _ ?_)
    rw [Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

variable {S : Scheme.{0}} {A U : Over S} [GrpObj A]

theorem fam_ev {M : LB (A ⊗ U).left} (hM : Fam A M) {T : Over S} (t : T ⟶ U) :
    Fam A (ev M (fst A T) (snd A T ≫ t)) := by
  have hPull : (ev M (fst A T) (snd A T ≫ t)).IsLB := pull_isLB hM.isLB _
  refine ⟨hPull, (isAdditive_iff hPull).2 ?_⟩
  intro Y a a' y
  simpa only [evc_ev hM.isLB, lift_fst, lift_snd_assoc] using
    (isAdditive_iff hM.isLB).1 hM.add Y a a' (y ≫ t)


omit [GrpObj A] in
theorem same_ev_iff {M M' : LB (A ⊗ U).left} (hM : M.IsLB) (hM' : M'.IsLB) {T Y : Over S} (t t' : T ⟶ U)
    (y : Y ⟶ T) :
    Same A (ev M (fst A T) (snd A T ≫ t)) (ev M' (fst A T) (snd A T ≫ t')) y y ↔ Same A M M' (y ≫ t) (y ≫ t') := by
  rw [same_iff (pull_isLB hM _) (pull_isLB hM' _), same_iff hM hM', evc_ev hM, evc_ev hM']
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

end GlobalTheory.DualInj

namespace GlobalTheory.DualInj

theorem inj_of_fibInj : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), LocallyOfFiniteType U.hom → Fam A M →
      FibInj A M → Inj A M := by
  intro R _ _ A _ hA U M hU hM hF
  have : LocallyOfFiniteType (U ⊗ U).hom := by
    show LocallyOfFiniteType (pullback.fst U.hom U.hom ≫ U.hom)
    infer_instance
  have : IsLocallyNoetherian (U ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (U ⊗ U).hom
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree (Sp R) A (U ⊗ U) hA
    (ev M (fst A (U ⊗ U)) (snd A (U ⊗ U) ≫ fst U U)) (ev M (fst A (U ⊗ U)) (snd A (U ⊗ U) ≫ snd U U))
    (fam_ev hM _) (fam_ev hM _)
  have key : ∀ (Y : Over (Sp R)) (y : Y ⟶ U ⊗ U),
      Same A M M (y ≫ fst U U) (y ≫ snd U U) ↔ ∃ z : Y ⟶ G, z ≫ i = y :=
    fun Y y => (same_ev_iff hM.isLB hM.isLB _ _ y).symm.trans (hG Y y)
  obtain ⟨δ, hδ⟩ := (key U (lift (𝟙 U) (𝟙 U))).1 (by
    rw [lift_fst, lift_snd]
    exact (same_iff hM.isLB hM.isLB _ _).2 rfl)
  let p : G.left ⟶ U.left := (i ≫ fst U U).left
  have hp : p ≫ U.hom = G.hom := Over.w (i ≫ fst U U)
  have : Mono i.left := inferInstance
  have pt : ∀ (Z : Scheme.{0}) (a b : Z ⟶ G.left) (K : Type) [Field K] [IsAlgClosed K] (t : Z ⟶ Sp K)
      (s : Sp K ⟶ Sp R), a ≫ p = b ≫ p → a ≫ G.hom = t ≫ s → a = b := by
    intro Z a b K _ _ t s e es
    let Y : Over (Sp R) := Over.mk (a ≫ G.hom)
    let α : Y ⟶ G := Over.homMk a rfl
    let β : Y ⟶ G := Over.homMk b (by
      show b ≫ G.hom = a ≫ G.hom
      rw [← hp, ← Category.assoc, ← e, Category.assoc])
    let τ : Y ⟶ Over.mk s := Over.homMk t es.symm
    have h1 : ∀ c0 : Y ⟶ G, c0 ≫ i ≫ fst U U = c0 ≫ i ≫ snd U U := fun c0 => by
      refine hF K s Y τ _ _ ?_
      have := (key Y (c0 ≫ i)).2 ⟨c0, rfl⟩
      simpa only [Category.assoc] using this
    have e1 : α ≫ i ≫ fst U U = β ≫ i ≫ fst U U := by
      refine Over.OverMorphism.ext ?_
      simpa only [Over.comp_left, Over.homMk_left, α, β, p] using e
    have e2 : α ≫ i = β ≫ i := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simpa only [Category.assoc] using e1
      · simpa only [Category.assoc, ← h1 α, ← h1 β] using e1
    have e3 := congrArg CommaMorphism.left e2
    simp only [Over.comp_left, Over.homMk_left, α, β] at e3
    exact (cancel_mono i.left).1 e3
  have : LocallyOfFiniteType p := by
    show LocallyOfFiniteType (i.left ≫ pullback.fst U.hom U.hom)
    infer_instance
  have hmono : Mono p := mono_of_points_tangents p
    (fun k _ _ y y' e => pt _ y y' k (𝟙 _) (y ≫ G.hom) e (Category.id_comp _).symm)
    (fun k _ _ w hw => pt _ w _ k (TangentCrit.dualBase k) (TangentCrit.dualPt k ≫ w ≫ G.hom) hw (by
      have := congrArg (· ≫ U.hom) hw
      simpa only [Category.assoc, hp] using this))
  intro Y u u' hs
  obtain ⟨z, hz⟩ := (key Y (lift u u')).1 (by rw [lift_fst, lift_snd]; exact hs)
  have hz1 : z ≫ i ≫ fst U U = u := by rw [← Category.assoc, hz, lift_fst]
  have hzδ : z = u ≫ δ := by
    refine Over.OverMorphism.ext ((cancel_mono p).1 ?_)
    have e1 : (z ≫ i ≫ fst U U).left = (u ≫ δ ≫ i ≫ fst U U).left := by
      rw [hz1, reassoc_of% hδ, lift_fst, Category.comp_id]
    simpa only [p, Over.comp_left, Category.assoc] using e1
  symm
  calc u' = lift u u' ≫ snd U U := (lift_snd _ _).symm
    _ = u ≫ δ ≫ i ≫ snd U U := by rw [← hz, hzδ]; simp only [Category.assoc]
    _ = u := by rw [reassoc_of% hδ, lift_snd, Category.comp_id]

end GlobalTheory.DualInj
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ → ZCusp V φ → IsCuspFun V φ := by
  first | exact @GlobalTheory.TransvCusp.isCuspFun_of_zCusp | exact GlobalTheory.TransvCusp.isCuspFun_of_zCusp | (intros; apply GlobalTheory.TransvCusp.isCuspFun_of_zCusp <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inner_rho_eq_normSq_mul_prod_of_holForm : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ) F, HolForm θ M w J χ φ → Repr V μ 𝓕 F φ → ∀ u ∈ GinfC V, ⟪F, ρ u F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.HolDict.inner_reg_eq_coef_extremal | exact GlobalTheory.HolDict.inner_reg_eq_coef_extremal | (intros; apply GlobalTheory.HolDict.inner_reg_eq_coef_extremal <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_sobolev_inequality_adelic_unitary : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ μ : Measure (GA D V), μ.IsHaarMeasure → ∃ (S : List (List (D.what₂.Tau × Mt V.rank))) (Ω : Set (GA D V)) (C : ℝ), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ ∀ ψ : GA D V → ℂ, Continuous ψ → (∀ k ∈ U, k ∈ GfC V → ∀ g, ψ (g * k) = ψ g) → (∀ l : List (D.what₂.Tau × Mt V.rank), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → Continuous (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ)) → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) → ∀ y, ‖ψ y‖ ^ 2 ≤ C * (S.map fun l => ∫ x in Ω, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) (y * x)‖ ^ 2 ∂μ).sum := by
  first | exact @GlobalTheory.SobLoc.local_sobolev | exact GlobalTheory.SobLoc.local_sobolev | (intros; apply GlobalTheory.SobLoc.local_sobolev <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transvectionCuspidal_of_rapidDecay_holomorphicType : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → ∀ φ : GA D V → ℂ, IsAutFun V φ → HolAd θ M w φ → GlobalTheory.CuspDecay.IsRapidDecay θ V φ → ZCusp V φ := by
  first | exact @GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay | exact GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay | (intros; apply GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_boundedSection_of_boundedHolomorphicForm : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ φ, HolForm θ M w (Kf : Set (GA D V)) (fun _ => 1) φ → ∃ P : FDSec X, P ∈ offZero X ∧ (∀ k, (X k).IsBddSec (la k) (P k)) ∧ adel V dict (muPin V dict mu c) P = φ := by
  first | exact @GlobalTheory.HolDict.IntoSec.exists_bddSec_adel_eq | exact GlobalTheory.HolDict.IntoSec.exists_bddSec_adel_eq | (intros; apply GlobalTheory.HolDict.IntoSec.exists_bddSec_adel_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem log_add_log_le_of_mul_le_mul (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ c * d) (hce : c ≤ e) :
    Real.log a + Real.log b ≤ Real.log e + Real.log d := by
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcd : 1 ≤ c * d := hab.trans h
  have hc : c ≠ 0 := by rintro rfl; simp at hcd
  have hd : d ≠ 0 := by rintro rfl; simp at hcd
  have he : e ≠ 0 := by omega
  have h1 : Real.log ((a : ℝ) * b) ≤ Real.log ((e : ℝ) * d) := by
    apply Real.log_le_log
    · have : (1 : ℝ) ≤ (a : ℝ) * b := by exact_mod_cast hab
      linarith
    · have : a * b ≤ e * d := h.trans (Nat.mul_le_mul_right d hce)
      exact_mod_cast this
  rwa [Real.log_mul (by exact_mod_cast (by omega : a ≠ 0)) (by exact_mod_cast (by omega : b ≠ 0)),
    Real.log_mul (by exact_mod_cast he) (by exact_mod_cast hd)] at h1

theorem lc_add_div_sub_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c →
    Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
    P.lc M ((M / n : ℕ) - c) 1 ≤ P.lc M (-c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hD P b s t hG c hgen hreg ε hε
  have hfin : ∀ (a c : ℤ) (R : ℝ), (P.Bl a c R).Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hD P
  have hball : ∀ a c : ℤ, IsBallFam (P.H a c) (P.Bl a c) := GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P
  have hpos : ∀ (a c : ℤ) (R : ℝ), 0 ≤ R → 1 ≤ (P.Bl a c R).ncard := fun a c R hR =>
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (hfin a c R)).mpr ⟨0, (hball a c).zero_mem R hR⟩).ne'
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.log_count_twist_exp_radius_le_pow_succ k X p D hD P b s t hG c hreg
  obtain ⟨δ, hδ, hrad⟩ := GlobalTheory.T.exists_log_ncard_seminormBall_exp_small_le X.functionField (fun N => P.H (N : ℤ) (-c)) (fun N => P.Bl (N : ℤ) (-c))
    (D + 1) (Nat.succ_pos D) (fun N => hball N _) (fun N R => hfin N _ R) C0 hC0 (ε / 2) (by positivity)
  obtain ⟨C, hC, hdiv⟩ := GlobalTheory.T.mem_sectionBall_of_mul_smallSection_pow_twist k X p D hD P c hgen s hG.s_mem.1 hG.s_ne (δ / 3) (by positivity)
  have hdA := GlobalTheory.T.log_count_nearby_powers_second_bundle_le k X p D hD P b c hG.pos hreg (ε / 2) (by positivity)
  have hn : ∀ᶠ n : ℕ in atTop, 3 * C / δ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hdA, hn] with n hdAn hnC
  filter_upwards [hdAn, hrad, hn] with M hdm hradm hMC
  have hnδ : 3 * C ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnC
  have hMδ : 3 * C ≤ (M : ℝ) * δ := (div_le_iff₀ hδ).mp hMC
  have hmn : ((M / n : ℕ) : ℝ) * n ≤ M := by exact_mod_cast Nat.div_mul_le_self M n
  generalize M / n = m at *
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m

  have hrad_le : Real.exp (δ / 3 * (M : ℝ) + C * m + C) ≤ Real.exp (δ * (M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hnδ hm0, mul_le_mul_of_nonneg_right hmn hδ.le]
  have hSsub : {f | f ∈ P.H M (-c) ∧ f * s ^ m ∈ P.Bl M (m - c) 2} ⊆ P.Bl M (-c) (Real.exp (δ * (M : ℝ))) := by
    rintro f ⟨hf1, hf2⟩
    have hf := hdiv M m f hf1 hf2
    exact ⟨hf.1, fun σ y => (hf.2 σ y).trans hrad_le⟩
  have hEfin := hfin M (-c) (Real.exp (δ * (M : ℝ)))
  have hSfin := hEfin.subset hSsub
  have hlev := GlobalTheory.T.encard_small_sections_mul_le_quotient_power_twist k X p D hD P b s t hG c M m
  rw [← (hfin _ _ _).cast_ncard_eq, ← (hfin _ _ _).cast_ncard_eq, ← hSfin.cast_ncard_eq,
    ← (hfin _ _ _).cast_ncard_eq] at hlev
  have hnat : ∀ x y z w : ℕ, (x : ℕ∞) * y ≤ z * w → x * y ≤ z * w := fun x y z w h => by exact_mod_cast h
  have hkey := log_add_log_le_of_mul_le_mul _ _ _ _ _ (hpos _ _ _ zero_le_one) (hpos _ _ _ zero_le_one)
    (hnat _ _ _ _ hlev)
    (Set.ncard_le_ncard hSsub hEfin)
  simp only [Pair.lc] at hdm ⊢
  linarith

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → P.L.SemiPos D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  intro hAr hHS k _ X _ p D hX P hamp hsp J _ e x he hx hbox
  have hxb := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).2 x hx
  have hmono := (GlobalTheory.VolBr.isBallFam_mono_neg_add _ _ _ (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0)).1
  have hb : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ P.Bl 1 0 (Real.exp u) := fun c =>
    GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX P 1 0 _ (hbox c)
  choose u hu0 hu using hb
  have hall : ∀ c, boxFam e x c ∈ P.Bl 1 0 (Real.exp (∑ c, u c)) := fun c =>
    hmono _ _ (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c))) (hu c)
  apply GlobalTheory.T.factorial_mul_rank_le_degree_of_indep_small_sections hAr hHS k X p D hX P 1 0 P.L (GlobalTheory.VolBr.Pair.rep_base k X p P).1 hamp hsp
    (Fintype.card J) (∑ c, u c)
  intro m hm
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j⟩⟩
  · have h0 : Fintype.card J = 0 := Fintype.card_eq_zero
    haveI : IsEmpty (Fin (Fintype.card J * m ^ D)) := by rw [h0, zero_mul]; exact Fin.isEmpty'
    exact ⟨isEmptyElim, linearIndependent_empty_type, isEmptyElim⟩
  · haveI : CharZero X.functionField := charZero_of_inj_zero fun n hn => by
      have h := he.smul_left_injective j (a₁ := (n : ℤ)) (a₂ := 0) (by simp [hn])
      exact_mod_cast h
    obtain ⟨v, hv, hvs⟩ := GlobalTheory.T.exists_linearIndependent_products_function_field X.functionField D x hxb J e he m hm
    refine ⟨v, hv, fun s => ?_⟩
    obtain ⟨w, n, hn, hvs'⟩ := hvs s
    rw [hvs']
    have h := GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt k X p P D J e x 1 0 (Real.exp (∑ c, u c)) (Real.exp_pos _).le hall m w n hn
    rw [← Real.exp_nat_mul, mul_comm (m : ℝ)] at h
    exact h
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integral_polarisedTopForm_dbarExact_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (θ : Fin n → Fin n → V n → Matrix r r ℂ) (j : Fin n) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v) → (∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ∀ a p q, ‖θ j a v p q‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q, ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ c) → IntegrableOn (fun v => mixTop fun i a b => mdbar (θ i a) v (coordVec b)) (offHyp S U) ∧ ∫ v in offHyp S U, (mixTop fun i a b => mdbar (θ i a) v (coordVec b)) = 0 := by
  first | exact @GlobalTheory.GoodTop.integral_mixTop_mdbar_eq_zero | exact GlobalTheory.GoodTop.integral_mixTop_mdbar_eq_zero | (intros; apply GlobalTheory.GoodTop.integral_mixTop_mdbar_eq_zero <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSAmpDet

theorem chInt_smul {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (D : ℕ) (c : ℝ) (u : SmFn p) :
    chInt L D (u.smul c).u = c * chInt L D u.u := by
  simp only [chInt, SmFn.smul, Weight.chernInt_const_mul, mul_finsum]

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem vals_smul (P : Pair p) (u : SmFn p) (t : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul t)) a b g = fun σ y i => vals P a b g σ y i * (Real.exp (-(a * (t * u.u σ y)) / 2) : ℝ) := by
  funext σ y i
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul t) a b).2.2 σ y (g i)).1

theorem vals_zero (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 0)) a b g = vals P a b g := by
  rw [vals_smul]
  funext σ y i
  simp

theorem vals_one (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 1)) a b g = vals (upperParabolic P u) a b g := by
  rw [vals_smul]
  funext σ y i
  rw [one_mul]
  exact ((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u a b).2.2 σ y (g i)).1.symm

theorem vals_two (P : Pair p) (u : SmFn p) (t t' : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic (upperParabolic P (u.smul t)) (u.smul (t' - t))) a b g = vals (upperParabolic P (u.smul t')) a b g := by
  rw [vals_smul, vals_smul, vals_smul]
  funext σ y i
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

end

theorem tendsto_logDet_gram_sub : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  intro hA k _ X _ p D hX hG P hP ω r f hf hli hr u a a' hsp ha ha'
  obtain ⟨s, hs0, hs1, hsd⟩ := GlobalTheory.T.self_intersection_metric_segment_polynomial hA k X p D hX P.L u a a' ha ha'
  set c : ℝ := 2 / ((D + 1).factorial : ℝ) with hc
  let ℓ : ℚ → ℕ → ℝ := fun t m =>
    Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P (u.smul (t : ℝ))) m 1 (f m))).det.re / (m : ℝ) ^ (D + 1)
  have hR := GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative (Polynomial.C c * s) ℓ ?_
  · have hfun : (fun m => ℓ 0 m - ℓ 1 m) = fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1) := by
      funext m
      simp only [ℓ, Rat.cast_zero, Rat.cast_one, vals_zero, vals_one, sub_div]
    have hval : (Polynomial.C c * s).eval 1 - (Polynomial.C c * s).eval 0 = 2 * (a' - a) / (D + 1).factorial := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C, hs0, hs1, hc]
      ring
    rw [hfun, hval] at hR
    exact hR
  · intro t t' ht0 ht1 ht0' ht1' ε hε
    have hsemi : (upperParabolic P (u.smul (t : ℝ))).L.SemiPos D :=
      GlobalTheory.T.semiPos_raiseWeight_segment_smul k X p D P.L u t (by exact_mod_cast ht0) (by exact_mod_cast ht1) hP hsp
    have hH : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P (u.smul (t : ℝ))).H m 1 := fun m i => by
      rw [(GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P (u.smul (t : ℝ)) m 1).1]
      exact hf m i
    have hrk : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
        (𝓝 (gdeg (upperParabolic P (u.smul (t : ℝ))).L D / D.factorial)) := by
      rw [show (upperParabolic P (u.smul (t : ℝ))).L = up P.L (u.smul (t : ℝ)) from rfl,
        GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L (u.smul (t : ℝ))]
      exact hr
    have hstep := GlobalTheory.T.gramDeterminant_weightShift_asymptotic_le k X p D hX hG (upperParabolic P (u.smul (t : ℝ))) hsemi ω r f hH hli hrk
      (u.smul ((t' : ℝ) - t)) ε hε
    have hch : chInt (upperParabolic P (u.smul (t : ℝ))).L D (u.smul ((t' : ℝ) - t)).u / D.factorial =
        ((t' : ℝ) - t) * (Polynomial.C c * s).derivative.eval (t : ℝ) := by
      rw [chInt_smul, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, ← hsd t, hc,
        Nat.factorial_succ]
      have hf0 : (D.factorial : ℝ) ≠ 0 := by positivity
      show ((t' : ℝ) - t) * chInt (up P.L (u.smul (t : ℝ))) D u.u / D.factorial = _
      push_cast
      field_simp
    filter_upwards [hstep, eventually_ge_atTop 1] with m hm hm1
    have hpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      positivity
    rw [vals_two, hch] at hm
    simp only [ℓ]
    rw [← sub_div, div_le_iff₀ hpos]
    linarith

end GlobalTheory.HSAmpDet
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∃ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x := by
  first | exact @GlobalTheory.HSAmp.NoethGens.exists_gens | exact GlobalTheory.HSAmp.NoethGens.exists_gens | (intros; apply GlobalTheory.HSAmp.NoethGens.exists_gens <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β →
    ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ S : Finset ℕ, ∀ (y : grp G β) (g : G.GAf), f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 →
    ∀ c : G.Cˣ, (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
      inC G ℚ_[ℓ] (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C)) := by
  first | exact @GlobalTheory.CxRegLoc.local_class_scalar_norm_sep | exact GlobalTheory.CxRegLoc.local_class_scalar_norm_sep
end
