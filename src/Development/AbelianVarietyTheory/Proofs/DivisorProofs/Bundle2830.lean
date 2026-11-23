module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPtCompClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeAffineFrameCoverTwoEigenParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.de_rham_pairing_pullback : GlobalTheory.CovTop.Hypotheses₂ → ∃ s : ℚ, s ≠ 0 ∧ ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A), GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A L ψ → ∀ (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → GlobalTheory.CechKS.IsCechKS A A' i L u θ → ∀ (hb : Fin n → GlobalTheory.DeRham.HdR A), (∀ b, GlobalTheory.DeRham.IsLieImage (hb b) (u b)) → ∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w : epsR K ⟶ A, IsLieComb (fun a => (s : K) * ∑ b, θ a b * ψ f (hb b)) u w → GlobalTheory.DeRham.IsKSValue h f w := by
  first | exact @GlobalTheory.CechKS.exists_const_isKSValue | exact GlobalTheory.CechKS.exists_const_isKSValue | (intros; apply GlobalTheory.CechKS.exists_const_isKSValue <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigDiv

theorem exists_eigFrame_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (R : Type) [CommRing R] [IsLocalRing R] (p : Sp R ⟶ X₀ TF.Y Z), ∃ (φ : c.F →+* R) (_ : GlobalTheory.ShFam.EigFrame TF.Y φ (p ≫ (barComp TF.Y Z).ι)), p ≫ s₀ TF.Y Z = spMap φ := by
  intro E _ _ _ H Dw l Xo c TF Z R _ _ p
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [hid]; infer_instance
  haveI : IsIso (GlobalTheory.Toroidal.genι TF.Y) := inferInstanceAs (IsIso (pullback.fst TF.Y.s (spMap (RingHom.id c.F))))
  have hs : inv (GlobalTheory.Toroidal.genι TF.Y) ≫ GlobalTheory.Toroidal.genStr TF.Y = TF.Y.s := by
    rw [IsIso.inv_comp_eq]
    calc GlobalTheory.Toroidal.genStr TF.Y = GlobalTheory.Toroidal.genStr TF.Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = GlobalTheory.Toroidal.genι TF.Y ≫ TF.Y.s := pullback.condition.symm
  let x : Sp R ⟶ GlobalTheory.Toroidal.gen TF.Y := (p ≫ (barComp TF.Y Z).ι) ≫ inv (GlobalTheory.Toroidal.genι TF.Y)
  let φ : c.F →+* R := (Spec.preimage (p ≫ s₀ TF.Y Z)).hom
  have hφ : spMap φ = p ≫ s₀ TF.Y Z := Spec.map_preimage _
  have hx : x ≫ GlobalTheory.Toroidal.genStr TF.Y = spMap φ := by
    rw [hφ, Category.assoc, hs, Category.assoc]
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y R φ x hx
  have e : x ≫ GlobalTheory.Toroidal.genι TF.Y = p ≫ (barComp TF.Y Z).ι := by
    simp only [x, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨φ, e ▸ f, hφ.symm⟩

theorem ratio_mem {K : Type} [Field K] (S : Subgroup Kˣ) {ι : Type} [Fintype ι] (u v w : ι → Kˣ)
    (h : ∀ τ, (v τ : K) = w τ * u τ) (hw : ∀ τ, w τ ∈ S) (a : ι → ℤ) :
    (∏ τ, u τ ^ (-a τ)) / (∏ τ, v τ ^ (-a τ)) ∈ S := by
  have hv : ∀ τ, v τ = w τ * u τ := fun τ => Units.ext (by rw [Units.val_mul]; exact h τ)
  rw [← Finset.prod_div_distrib]
  refine S.prod_mem fun τ _ => ?_
  have e : u τ / v τ = (w τ)⁻¹ := by rw [hv, div_mul_eq_div_div_swap, div_self', one_div]
  rw [← div_zpow, e]
  exact S.zpow_mem (S.inv_mem (hw τ)) _

theorem exists_div {X : Scheme.{0}} [IsIntegral X] (g : X → X.functionFieldˣ)
    (h : ∀ x, ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, UnitAt y ((g x : X.functionField) / g y)) :
    ∃ D : CartierDiv X, ∀ x, D.IsEqn x (g x) :=
  ⟨show cartierGroup X from ⟨fun x => germOf x (g x), fun x => by
    obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, hx, g x, fun y hy => germOf_eq_iff.2 (hU y hy)⟩⟩, fun _ => rfl⟩

theorem exists_detDiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)], ∃ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ ∧ ∀ a : (E →+* ℂ) → ℤ, ∃ D : CartierDiv (X₀ TF.Y Z), CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) ∧ ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-a τ)) := by
  intro E _ _ _ H Dw l Xo c TF Z _
  have hloc : ∀ x : X₀ TF.Y Z, IsLocalRing ((X₀ TF.Y Z).presheaf.stalk x) := fun x => inferInstance
  obtain ⟨φ₀, f₀, h₀⟩ := @exists_eigFrame_stalk E _ _ _ H Dw l Xo c TF Z ((X₀ TF.Y Z).presheaf.stalk (genericPoint (X₀ TF.Y Z))) _ (hloc _) ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)))
  refine ⟨φ₀, f₀, h₀, fun a => ?_⟩
  choose φx fx hx using fun x : X₀ TF.Y Z => @exists_eigFrame_stalk E _ _ _ H Dw l Xo c TF Z ((X₀ TF.Y Z).presheaf.stalk x) _ (hloc x) ((X₀ TF.Y Z).fromSpecStalk x)
  have hpt : ∀ x : X₀ TF.Y Z, spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) ≫
      (X₀ TF.Y Z).fromSpecStalk x = (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) := fun x =>
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  have hφ : ∀ x, φ₀ = (algebraMap _ (X₀ TF.Y Z).functionField).comp (φx x) := fun x =>
    GlobalTheory.ShFam.EigLoc.spMap_inj (by rw [← h₀, ← hpt x, Category.assoc, hx x]; exact (Spec.map_comp _ _).symm)
  have hFK : ∀ x : X₀ TF.Y Z, ∃ fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀
      ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι),
      (fx x).IsMap (algebraMap _ (X₀ TF.Y Z).functionField) fK := fun x =>
    (fx x).exists_isMap (algebraMap _ (X₀ TF.Y Z).functionField) (hφ x)
      (by rw [← hpt x]; exact Category.assoc _ _ _)
  let fK := fun x => Classical.choose (hFK x)
  have hfK := fun x => Classical.choose_spec (hFK x)
  let g : ∀ fK : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι),
    (X₀ TF.Y Z).functionFieldˣ := fun fK => ∏ τ, (fK.isUnit_det_co f₀ τ).unit ^ (-a τ)
  have key : ∀ (y : X₀ TF.Y Z) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φ₀
      ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)),
      (∀ τ, UnitAt y (fK'.co fK τ).det) → UnitAt y ((g fK : (X₀ TF.Y Z).functionField) / g fK') := by
    intro y fK fK' hu
    have := ratio_mem (unitsAt y) (fun τ => (fK.isUnit_det_co f₀ τ).unit) (fun τ => (fK'.isUnit_det_co f₀ τ).unit)
      (fun τ => (fK'.isUnit_det_co fK τ).unit) (fun τ => by
        simp only [IsUnit.unit_spec]
        rw [← Matrix.det_mul, GlobalTheory.ShFam.EigFrame.co_mul]) (fun τ => hu τ) a
    rw [← Units.val_div_eq_div_val (g fK) (g fK')]
    exact this
  obtain ⟨D, hD⟩ := exists_div (fun x => g (fK x)) fun x => by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.T.eigenFrameCoordinates_locallyConstant_upToUnits E H Dw l Xo c TF Z x (φx x) (fx x) (hx x)
    exact ⟨U, hxU, fun y hy => key y _ _ (hU y hy (φx y) (fx y) φ₀ (fK x) (fK y) (hx y) h₀ (hfK x) (hfK y))⟩
  refine ⟨D, ?_, fun x => ⟨φx x, fx x, fun τ => (fK x |>.co f₀ τ).transpose,
    fun τ => (fK x |>.isUnit_det_co f₀ τ).unit, hx x, fun τ => (IsUnit.unit_spec _).trans (Matrix.det_transpose _).symm, fun τ i => ?_, hD x⟩⟩
  · refine GlobalTheory.T.flagSpacePullback_eigenDeterminantDivisor_eq_gradedLines E H Dw l Xo c TF Z φ₀ f₀ a D h₀ fun x φ f fK' hs hm => ?_
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.T.eigenFrameCoordinates_locallyConstant_upToUnits E H Dw l Xo c TF Z x φ f hs
    exact (hD x).iff_unitAt.2 (key x _ _ (hU x hxU (φx x) (fx x) φ₀ fK' (fK x) (hx x) h₀ hm (hfK x)))
  · have e : (fK x).v τ = fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x)
        (X₀ TF.Y Z).functionField)) ≫ (fx x).v τ k := funext (hfK x τ)
    rw [← e]
    exact (fK x).co_spec f₀ τ i

end GlobalTheory.EigDiv
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitArcMatch

open GlobalTheory.TraitArc GlobalTheory.TauTwist GlobalTheory.ArcBuild GlobalTheory.ArcOfPoint Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {T : CDVR}

theorem genRel_psi_twist (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
    (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing T.V) F] (y : D.toPre.X) :
    GenRel (isoPullId (idIso D.toPre.P.L) rfl)
      (LB.pullGen _ _ _ (D.toPre.psi y) (jFK (R := T.V) F))
      (LB.pullGen _ _ _ ((D0 (H := H) D hϖ).psi y) (jFK (R := T.V) F))
      ((algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2)) := by
  have h0 : algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)
  have hq : beF D hϖ y y / 2 = qv D hϖ y := by rw [beF_self]; omega
  let u : Fˣ := Units.mk0 _ h0 ^ (beF D hϖ y y / 2)
  have hu : ((u : Fˣ) : F) = (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2) := by
    simp only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [← hu]
  refine ArcOfPoint.genRel_id_of_val D.toPre.P.isLB (DVR.pullGen_isGen _ _ _ _ (D.toPre.psi_gen y) _) fun z J hJ => ?_
  have ht : Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (TraitArc.tF D hϖ y (H.w0 • y)) = u⁻¹ := by
    apply Units.ext
    simp only [u, TraitArc.tF, beF_w0 D oD, hq, Units.coe_map, map_zpow, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, zpow_neg]
    show (algebraMap (FractionRing T.V) F) ((((piK hϖ : (FractionRing T.V)ˣ) : FractionRing T.V) ^ qv D hϖ y)⁻¹) = _
    rw [map_inv₀, map_zpow₀]; rfl
  letI := H.starRing
  rw [val_pull hJ, val_pull hJ, Category.id_comp]
  erw [val_psi_twist H.w0 (TraitArc.tF D hϖ) y (jFK (R := T.V) F) hJ]
  rw [show jFK (R := T.V) F = 𝟙 _ ≫ spMap (algebraMap (FractionRing T.V) F) from (Category.id_comp _).symm,
    unitAt_spMap, ht, map_inv, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

theorem exists_isPullDeg_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) (ϖ : T.V) (hϖ : Irreducible ϖ) (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.TraitArc.beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : GlobalTheory.TraitArc.LieCl D oD Dm β b) (hTate : GlobalTheory.TraitArc.TateCl D oD hϖ Dm β b hdiv pA pM) (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp T.V ⟶ Y.X), Y.HasArcData (GlobalTheory.TraitArc.arc D oD hϖ β b hX hw hdiv pA pM hLie hTate) (maximalIdeal T.V) (RingHom.id T.V) ϖ y → ∃ (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), Nonempty (IsPullDeg (RingHom.id T.V) D.toPre P.D.toPre) := by
  intro E _ _ _ H Dm l c O _ β T b D _ oD ϖ hϖ hX hw hdiv pA pM hLie hTate Xo Y y hY
  obtain ⟨t, m, P, φ, he, w, e, h1, h2, h3, -, h5, h6⟩ := hY
  refine ⟨t, m, P, ?_⟩
  have hid : spMap (RingHom.id T.V) = 𝟙 _ := Spec.map_id _
  have he0 : eSec D.toPre.P.A ≫ 𝟙 _ = spMap (RingHom.id T.V) ≫ eSec D.toPre.P.A := by
    rw [hid, Category.comp_id]; exact (Category.id_comp _).symm
  have p : IsGrpPullback D.toPre.P.A D.toPre.P.A (spMap (RingHom.id T.V)) (𝟙 _) := by
    have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
    exact (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr hid.symm rfl
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  let F := AlgebraicClosure (FractionRing T.V)
  have k6 := (h6 F (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) (fun _ => rfl) rfl).1
  have r := (maps_iff (idW D.toPre.P.L) _ (fun _ => eSec D.toPre.P.A) _ D.toPre.rig D.toPre.rig _ _
    (rigPull_le (𝟙 _) _ he0 D.toPre.P.L) (fun _ => rfl)).1 (maps_rig_id D.toPre he0)
  have r' := (maps_iff w _ (fun _ => eSec D.toPre.P.A) _ P.D.toPre.rig D.toPre.rig _ _
    (rigPull_le φ _ he D.toPre.P.L) (fun _ => rfl)).1 h3
  let xe : P.D.toPre.X ≃+ D.toPre.X := e.symm.toAddEquiv
  have hxe : ∀ y, xe (e y) = y := fun y => e.symm_apply_apply y
  obtain ⟨hD, -⟩ := GlobalTheory.ArcData.exists_isPullDeg_id D.toPre P.D.toPre (A₀ := D.toPre.P.A) (M₀ := D.toPre.P.L)
    D.toPre.P.isLB D.toPre.rig p h1 (idW D.toPre.P.L) w
    ((isGen_iff _).1 ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.toPre.P.isLB) rfl))) ((isGen_iff _).1 h2)
    r r' xe (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      refine (h5 y).trans ?_
      rw [hid, Category.id_comp, Category.comp_id, hxe]; rfl)
    Wo hWo ψW (jFK (R := T.V) F) (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hxe]
      exact ⟨_, _, _, genRel_psi_twist D oD hϖ F y, k6 y⟩)
  exact ⟨hD⟩

end GlobalTheory.TraitArcMatch
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.ExtendNormal

open FromGeneric

theorem valR_eq_one {X : Scheme.{0}} [IsReduced X] {U : X.Opens} {K : Type} [Field K] (x : Sp K ⟶ X)
    (hx : Set.range x ⊆ U) (hd : ∀ z ∈ U, x (IsLocalRing.closedPoint K) ⤳ z) {f : Γ(X, U)} (hf : valR x U f = 1)
    {R : Type} [CommRing R] (x' : Sp R ⟶ X) (hx' : Set.range x' ⊆ U) : valR x' U f = 1 := by
  have h : ⊤ ≤ x ⁻¹ᵁ U := fun z _ => hx ⟨z, rfl⟩
  have h' : ⊤ ≤ x' ⁻¹ᵁ U := fun z _ => hx' ⟨z, rfl⟩
  have h0 : (x.appLE U ⊤ h).hom (f - 1) = 0 := by
    rw [valR, dite_eq_left h] at hf
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
    rw [map_sub, map_sub, map_one, map_one, map_zero]
    exact sub_eq_zero.2 hf
  have h1 : f - 1 = 0 := by
    refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun z hz => ?_)
    have h2 : x (IsLocalRing.closedPoint K) ∈ X.basicOpen (f - 1) :=
      (hd z (X.basicOpen_le _ hz)).mem_open (X.basicOpen _).isOpen hz
    have h3 := Scheme.basicOpen_appLE x ⊤ U h (f - 1)
    rw [show (x.appLE U ⊤ h) (f - 1) = 0 from h0, Scheme.basicOpen_zero] at h3
    have h4 : IsLocalRing.closedPoint K ∈ (⊤ ⊓ x ⁻¹ᵁ X.basicOpen (f - 1) : (Sp K).Opens) := ⟨trivial, h2⟩
    rw [← h3] at h4
    exact h4.elim
  rw [sub_eq_zero.1 h1, valR, dite_eq_left h', map_one, map_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem exists_frame_local {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X}
    {τ : E →+* ℂ} {p q : ℕ} (hcov : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {R : Type} [CommRing R] [IsLocalRing R]
    (x : Sp R ⟶ X) (hx : x (IsLocalRing.closedPoint R) ∈ V) :
    ∃ (j : c.F →+* R) (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G)),
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w := by
  obtain ⟨W, hW, j, v, w, hz, h⟩ := hcov _ hx
  have : IsOpenImmersion (show Sp Γ(X, W) ⟶ X from hW.fromSpec) := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨m, hm⟩ := exists_lift (show Sp Γ(X, W) ⟶ X from hW.fromSpec) x (range_subset _
    (show Sp Γ(X, W) ⟶ X from hW.fromSpec).isOpenEmbedding.isOpen_range (by
      rw [show Set.range _ = _ from hW.range_fromSpec]; exact hz))
  obtain ⟨v', w', h', -⟩ := exists_pull m h hm
  exact ⟨_, v', w', h'⟩

theorem unitAtPt_of_dvr {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X}
    {τ : E →+* ℂ} {p q : ℕ} (hcov : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {B : Scheme.{0}} [IsIntegral B]
    [IsLocallyNoetherian B] (hB : ∀ y : B, IsIntegrallyClosed (B.presheaf.stalk y)) (io : B ⟶ X)
    (hio : ∀ y, io y ∈ V) {j₀ : c.F →+* B.functionField} {v₀ w₀}
    (h₀ : IsFrame t π s V (HermitianCompactForm.chi c τ) (p := p) (q := q) j₀ (genPt B ≫ io) v₀ w₀) {δ : B.functionField} (hδ : δ ≠ 0)
    (hdvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R B.functionField]
      [IsFractionRing R B.functionField] (j : c.F →+* R) (x : Sp R ⟶ X) v w M N,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w →
      IsChg t π (algebraMap R B.functionField) x v w (genPt B ≫ io) v₀ w₀ M N →
      ∃ u : Rˣ, N.det * algebraMap R B.functionField u = M.det * δ) (y : B) :
    UnitAtPt t π s V (HermitianCompactForm.chi c τ) io v₀ w₀ δ y := by
  obtain ⟨j, v, w, h⟩ := exists_frame_local hcov (locPt B y ≫ io) (by rw [locPt_comp_closedPoint]; exact hio y)
  obtain ⟨-, M, N, hc⟩ := exists_chg (algebraMap (B.presheaf.stalk y) B.functionField) h h₀
    (by rw [genPt_eq y, Category.assoc])
  obtain ⟨hM, hN⟩ := chg_isUnit h h₀ hc
  have hφ : M.det * δ / N.det ≠ 0 := div_ne_zero (mul_ne_zero hM.ne_zero hδ) hN.ne_zero
  have key : ∀ z : B, z ⤳ y → IsDiscreteValuationRing (B.presheaf.stalk z) →
      ∃ u : (B.presheaf.stalk z)ˣ, algebraMap _ B.functionField (u : B.presheaf.stalk z) = M.det * δ / N.det := by
    intro z hz _
    let g : B.presheaf.stalk y →+* B.presheaf.stalk z := (B.presheaf.stalkSpecializes hz).hom
    have hg : (algebraMap (B.presheaf.stalk z) B.functionField).comp g =
        algebraMap (B.presheaf.stalk y) B.functionField :=
      congrArg CommRingCat.Hom.hom (B.presheaf.stalkSpecializes_comp ((genericPoint_spec B).specializes trivial) hz)
    obtain ⟨v', w', h', a, b⟩ := exists_pull g h rfl
    obtain ⟨u, hu⟩ := hdvr _ _ _ v' w' M N h' ⟨by
      rw [← Category.assoc, ← DetExtendZero.spMap_comp, hg]; exact hc.1, fun i => by
      simp only [a, ← Category.assoc, ← DetExtendZero.dual_comp, hg]; exact hc.2.1 i, fun i => by
      simp only [b, ← Category.assoc, ← DetExtendZero.dual_comp, hg]; exact hc.2.2 i⟩
    exact ⟨u, by rw [← hu, mul_div_cancel_left₀ _ hN.ne_zero]⟩
  obtain ⟨a, ha⟩ := GlobalTheory.Hartogs.regAt_of_forall_dvr B hB (M.det * δ / N.det) y fun z hz hz' => by
    obtain ⟨u, hu⟩ := key z hz hz'
    exact ⟨u, hu⟩
  obtain ⟨b, hb⟩ := GlobalTheory.Hartogs.regAt_of_forall_dvr B hB (M.det * δ / N.det)⁻¹ y fun z hz hz' => by
    obtain ⟨u, hu⟩ := key z hz hz'
    exact ⟨(u⁻¹ : (B.presheaf.stalk z)ˣ), by rw [← hu, map_units_inv]⟩
  have hab : a * b = 1 := IsFractionRing.injective (B.presheaf.stalk y) B.functionField (by
    rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hφ])
  refine ⟨j, v, w, M, N, Units.mkOfMulEqOne a b hab, h, hc, ?_⟩
  rw [Units.val_mkOfMulEqOne, ha, mul_div_cancel₀ _ hN.ne_zero]

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → τ (H.rt : E) = H.rt0 → SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → SecU Xo c U τ σ → Restricts Z U τ σZ σ → ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' Z U τ σZ σ hn hcl hU hτ hσZ hZ hσ hres
  obtain ⟨V, hV, hint⟩ := GlobalTheory.T.genericFibre_componentClosure_open_isIntegral E H D l Xo c O β Y U hn hcl hU
  have := Y.jQ_open
  have : IsProper (genStr Y) := isProper_genStr Y
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have : IsReduced (gen Y) := by
    have := fun y => (hn y).1
    exact isReduced_of_isReduced_stalk _
  have : IsReduced (Xo.XF c) := isReduced_of_isOpenImmersion Y.jQ
  have hB : ∀ y : V.toScheme, IsIntegrallyClosed (V.toScheme.presheaf.stalk y) := fun y =>
    haveI := (hn (V.ι y)).2
    IsIntegrallyClosed.of_equiv (asIso (V.ι.stalkMap y)).commRingCatIsoToRingEquiv
  have hcov := frameCover_gen E H D l Xo c O β Y V τ hτ
  rw [hV] at hcov
  have hio : ∀ y, V.ι y ∈ compactOf Y U := fun y => hV ▸ y.2
  have hpt : (genPt V.toScheme ≫ V.ι) (IsLocalRing.closedPoint _) = V.ι (genericPoint V.toScheme) :=
    locPt_comp_closedPoint V.ι _
  have hsp : ∀ z ∈ compactOf Y U, V.ι (genericPoint V.toScheme) ⤳ z := fun z hz =>
    (genericPoint_specializes (α := V.toScheme) (⟨z, (hV ▸ hz : z ∈ (V : Set (gen Y)))⟩ : V.toScheme)).map V.ι.continuous
  have hgen : V.ι (genericPoint V.toScheme) ∈ Y.jQ '' (U : Set (Xo.XF c)) := by
    obtain ⟨z, hz⟩ := closure_nonempty_iff.1 ⟨_, hio (genericPoint V.toScheme)⟩
    exact (hsp z (subset_closure hz)).mem_open (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen) hz
  obtain ⟨j₀, v₀, w₀, h₀⟩ := exists_frame_local hcov (genPt V.toScheme ≫ V.ι) (by rw [hpt]; exact hio _)
  have main : ∀ (K : Type) [Field K] (xb : Sp K ⟶ gen Y) (j₀ : c.F →+* K) v₀ w₀,
      xb (IsLocalRing.closedPoint K) = V.ι (genericPoint V.toScheme) → FrY Y (compactOf Y U) τ j₀ xb v₀ w₀ →
      ∃ δ : K, δ ≠ 0 ∧ (∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K]
        [IsFractionRing R K] (j : c.F →+* R) (x : Sp R ⟶ gen Y) v w M N, FrY Y (compactOf Y U) τ j x v w →
        IsChg Y.t (genι Y) (algebraMap R K) x v w xb v₀ w₀ M N → ∃ u : Rˣ, N.det * algebraMap R K u = M.det * δ) ∧
        ∀ σb : RuleY Y, SecY Y (compactOf Y U) τ σb → NzY Y (compactOf Y U) τ σb → σb K xb v₀ w₀ = δ →
          Restricts Y U τ σb σ := by
    intro K _ xb j₀ v₀ w₀ hxb h₀
    obtain ⟨x, rfl⟩ : ∃ x : Sp K ⟶ Xo.XF c, x ≫ Y.jQ = xb :=
      ⟨IsOpenImmersion.lift Y.jQ xb (range_subset _ Y.jQ.isOpenEmbedding.isOpen_range
        (hxb ▸ Set.image_subset_range _ _ hgen)), IsOpenImmersion.lift_fac _ _ _⟩
    have hxb' : Y.jQ (x (IsLocalRing.closedPoint K)) = V.ι (genericPoint V.toScheme) :=
      (Scheme.Hom.comp_apply _ _ _).symm.trans hxb
    have hxU : Set.range x ⊆ U := range_subset _ U.isOpen (by
      obtain ⟨z, hz, e⟩ := hgen
      rwa [Y.jQ.isOpenEmbedding.injective (hxb'.trans e.symm)])
    obtain ⟨v, w, h, sv, sw⟩ := (frame_transfer E H D l Xo c O β Y U τ K j₀ x).2 _ v₀ w₀ hxU h₀
    refine ⟨σ K x v w, ?_, fun R _ _ _ _ _ j xR vR wR M N hR hc => ?_, fun σb hb hnz e => ?_⟩
    · obtain ⟨vz, wz, hz, a, b⟩ := (frame_transfer E H D l Xo c O' β' Z U τ K j₀ x).1 v w h
      rw [← hres K j₀ x v w vz wz h hz a b]
      exact (hZ K j₀ _ vz wz hz).ne_zero
    · obtain ⟨vb, wb, hb, a, b⟩ := exists_pull (algebraMap R K) hR hc.1
      obtain ⟨v', w', h', sv', sw'⟩ := (frame_transfer E H D l Xo c O β Y U τ K _ x).2 _ vb wb hxU hb
      obtain ⟨u, hu⟩ := GlobalTheory.T.determinantSection_unit_integral_frames_dvr E H D l Xo c O β Y O' β' Z U τ σZ σ hσZ hZ hres R K j xR x _ vR wR v' w' vb wb
        hR h' hc.1 sv' sw' a b
      have hid : x = spMap (RingHom.id K) ≫ x := by rw [DetExtendZero.spMap_id, Category.id_comp]
      refine ⟨u, ?_⟩
      rw [← hu]
      refine sec_chg (g := RingHom.id K) hσ h' h ⟨hid, fun i => ?_, fun i => ?_⟩
      · refine (isCombination_iff_of_sameVecs E H D l Xo c O β Y K K _ x x _ v' vb v v₀ hid sv' sv _ i).2 ?_
        simp only [DetExtendZero.dual_id, Category.id_comp, a]
        exact hc.2.1 i
      · refine (isCombination_iff_of_sameVecs E H D l Xo c O β Y K K _ x x _ w' wb w w₀ hid sw' sw _ i).2 ?_
        simp only [DetExtendZero.dual_id, Category.id_comp, b]
        exact hc.2.2 i
    · obtain ⟨σ₁, h1, h2, h3⟩ := GlobalTheory.T.exists_determinantLine_section_restriction E H D l Xo c O β Y U τ σb hb
      obtain ⟨f, hf⟩ := GlobalTheory.detLine_exists_ratio E H l c _ _ _ _ _ τ _ _ U σ₁ σ
        (frameCover_univ E H D l Xo c U τ hτ) h1 (h3 hnz) hσ
      have e1 : valR x U f = 1 := by
        have e2 := hf K j₀ x v w h
        rw [← e, h2 K j₀ x v w v₀ w₀ h h₀ sv sw] at e2
        exact ((h3 hnz K j₀ x v w h).mul_right_cancel ((_root_.one_mul _).trans e2)).symm
      intro R _ j x' v' w' vb wb h' hb' a b
      rw [h2 R j x' v' w' vb wb h' hb' a b, hf R j x' v' w' h',
        valR_eq_one x hxU (fun z hz => ?_) e1 x' h'.2.1, _root_.one_mul]
      rw [← Y.jQ.isOpenEmbedding.isInducing.specializes_iff, hxb']
      exact hsp _ (subset_closure ⟨z, hz, rfl⟩)
  obtain ⟨δ, hδ, hdvr, hfin⟩ := main _ _ j₀ v₀ w₀ hpt h₀
  obtain ⟨σb, h1, h2, h3⟩ := exists_section E H l c _ _ _ _ _ τ _ _ V.toScheme V.ι _ inferInstance
    (V.range_ι.trans hV) hcov j₀ v₀ w₀ δ h₀ (unitAtPt_of_dvr hcov hB V.ι hio h₀ hδ hdvr)
  exact ⟨σb, h1, h2, hfin σb h1 h2 h3⟩

end GlobalTheory.DetLine.ExtendNormal
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete


theorem _root_.GlobalTheory.T.hodge_tate_map_open_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ (p ^ n) = 1), IsOpenImmersion (jH P' x0 hu hg.1 h).left := by
  first | exact @GlobalTheory.FinPartOpen.isOpenImmersion_jH | exact GlobalTheory.FinPartOpen.isOpenImmersion_jH | (intros; apply GlobalTheory.FinPartOpen.isOpenImmersion_jH <;> assumption)
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isRaynaudTorusWeight_pullback_pointTranslation : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (α : Q.X) (U U' : Y.H.left.Opens), U' ≤ GlobalTheory.HeatTrans.tr Y.H x ⁻¹ᵁ U → ∀ f : Γ(Y.H.left, U), IsWt Y α U f → IsWt Y α U' (pbT (GlobalTheory.HeatTrans.tr Y.H x) f U') := by
  first | exact @GlobalTheory.HeatTransWt.isWt_pbT_tr | exact GlobalTheory.HeatTransWt.isWt_pbT_tr | (intros; apply GlobalTheory.HeatTransWt.isWt_pbT_tr <;> assumption)
end
