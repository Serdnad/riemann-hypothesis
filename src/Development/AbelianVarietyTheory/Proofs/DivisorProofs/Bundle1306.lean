module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyMemberTangentValueEqFirstJet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorOfDualPointAdditiveLieComb
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosed
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  first | exact @GlobalTheory.MBLow.JetGeo.jet_geo | exact GlobalTheory.MBLow.JetGeo.jet_geo | (intros; apply GlobalTheory.MBLow.JetGeo.jet_geo <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.tensor_product_sections_zeros_multiplicities_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (M A : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a), ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ (∀ z, (divOfSec (M.tens A).φ.isLB s₁ h₁).mult z = (divOfSec M.φ.isLB s hs).mult z + (divOfSec A.φ.isLB a ha).mult z) ∧ ∀ y ∈ ptsIn p σ (nonzeroLocus s₁), (M.tens A).logSec s₁ y = M.logSec s y + A.logSec a y := by
  first | exact @GlobalTheory.Mix.exists_sec_tens | exact GlobalTheory.Mix.exists_sec_tens | (intros; apply GlobalTheory.Mix.exists_sec_tens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torusExtensionTangent_of_additiveMap : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (l : D.X →+ R), ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  first | exact @GlobalTheory.MBLow.TorVec.exists_torus_tangent | exact GlobalTheory.MBLow.TorVec.exists_torus_tangent | (intros; apply GlobalTheory.MBLow.TorVec.exists_torus_tangent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.modelTangentVector_torusPoint_reduces_to_origin : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → GtTan gm₀ := by
  first | exact @GlobalTheory.MBLow.TanRed.main | exact GlobalTheory.MBLow.TanRed.main | (intros; apply GlobalTheory.MBLow.TanRed.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.sectionValue_tangentLift_eq_firstJet : ∀ (g : ℕ) (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) (v : epsR ℂ ⟶ P.A) (W : Fin g → ℂ) (i : P.L.ι), FnT u k t f → Differentiable ℂ f → IsTangent v → u.IsDiff W v → ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i → valR (epsLift v) ((LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))).U fun _ => i) (t.f fun _ => i) = TrivSqZeroExt.inl (u.fr i 0 ^ k) * (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr (fderiv ℂ f 0 W + (k * fderiv ℂ (u.fr i) 0 W / u.fr i 0) * f 0)) := by
  first | exact @GlobalTheory.MBLow.EpsVal.valR_epsLift | exact GlobalTheory.MBLow.EpsVal.valR_epsLift | (intros; apply GlobalTheory.MBLow.EpsVal.valR_epsLift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.thetaChar_blockPeriodMatrix_fourierJacobiExpansion : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → ∀ Z, (Summable fun χ => ‖d.fj σ S χ Z‖) ∧ ∑' χ, d.fj σ S χ Z = thetaChar (d.full σ S) (d.aF σ) (d.bF σ) Z := by
  first | exact @GlobalTheory.MBLow.Cl.fj_expansion | exact GlobalTheory.MBLow.Cl.fj_expansion | (intros; apply GlobalTheory.MBLow.Cl.fj_expansion <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torusExtensionTangent_characterValues_additive : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (gm : GtPt D (epsR R)), GtTan gm → gm.b = DegPre.zeroT D (epsR R) → ∃ l : D.X →+ R, ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  first | exact @GlobalTheory.MBLow.GtTanClass.main | exact GlobalTheory.MBLow.GtTanClass.main | (intros; apply GlobalTheory.MBLow.GtTanClass.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanPull


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel in

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (N : NumD C) (ν : NumOf D C N) (gm₀ : GtPt D (epsR V)), GtTan gm₀ → ∃ gm : GtPt D (TE V C), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm ∧ (∃ o : GtPtF D C, o.IsZero ∧ GtPt.IsPullF C (redE C) gm o) ∧ (gm₀.b = DegPre.zeroT D (epsR V) → gm.b = DegPre.zeroT D (TE V C)) ∧ ∀ (a : V) (χ : D.X), (∀ (Z : Scheme.{0}) (q : Z ⟶ (epsR V).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm₀.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))) → vE (gm.s χ) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr (toF V C a) := by
  intro V _ _ D C _ _ N ν gm₀ htan
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := TorusModel.exists_isGt hG (TorusModel.splitExt D)
  obtain ⟨Φ, hp, ha⟩ := TorusModel.exists_points hG hH
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  have hTF : spMap (toF V C) = (TF (R := V) C).hom := by
    simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hTE : spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TE V C).hom := by
    rw [TanLift.dualMap_over, hTF]; rfl
  let hh : TE V C ⟶ epsR V := Over.homMk (spMap (dualMap (toF V C))) hTE
  obtain ⟨x₀, rfl⟩ := (Φ (epsR V)).surjective gm₀
  refine ⟨Φ _ (hh ≫ x₀), hp _ _ hh x₀, ?_, ?_, ?_⟩
  · obtain ⟨o₀, ho₀, hpo⟩ := htan
    let r : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) (TanLift.redE_over V)
    have e₀ : o₀ = Φ _ (r ≫ x₀) := by
      have hpo' : GtPt.IsPull (redE V) (Φ _ x₀) (Φ _ (r ≫ x₀)) := hp _ _ r x₀
      generalize hg : Φ _ (r ≫ x₀) = g at hpo' ⊢
      obtain ⟨b, s, h, hs, hm⟩ := o₀
      obtain ⟨b', s', h', hs', hm'⟩ := g
      have hb : b = b' := Over.OverMorphism.ext (hpo.1.trans hpo'.1.symm)
      subst b'
      have he : s = s' := funext fun χ =>
        GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (h χ) (h' χ)
          (corr_of_val D.P.isLB fun y J hJ =>
            (val_corr hJ (hpo.2 χ) _).trans (val_corr hJ (hpo'.2 χ) _).symm)
      subst s'
      rfl
    have e₁ : r ≫ x₀ = 1 := (Φ _).injective ((e₀.symm.trans (GtVec.isZero_unique ho₀ (hz _))))
    let k : TF (R := V) C ⟶ TE V C := Over.homMk (redE C) (by
      show redE C ≫ spMap (algebraMap C (DualNumber C)) ≫ (TF (R := V) C).hom = (TF (R := V) C).hom
      rw [← Category.assoc, GtVec.red_comp, Category.id_comp])
    let tf : TF (R := V) C ⟶ baseOver (Sp V) := Over.homMk (TF (R := V) C).hom (Category.comp_id _)
    have e₂ : k ≫ hh = tf ≫ r := by
      ext
      show redE C ≫ spMap (dualMap (toF V C)) = (TF (R := V) C).hom ≫ redE V
      rw [← hTF]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have e₃ : k ≫ hh ≫ x₀ = 1 := by
      rw [← Category.assoc, e₂, Category.assoc, e₁, MonObj.comp_one]
    have hpk := hp _ _ k (hh ≫ x₀)
    rw [e₃] at hpk
    let g := Φ (TF (R := V) C) 1
    refine ⟨⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩, ⟨(hz _).1, (hz _).2⟩, hpk⟩
  · intro hb
    have e := ((TorusModel.isPull_iff _ _ _).1 (hp _ _ hh x₀)).1
    rw [e, hb]
    simp
  · intro a χ hval
    have hloc : IsLocalRing (DualNumber C) := TanLift.isLocalRing_dualNumber C
    have hlocH : IsLocalHom (TrivSqZeroExt.fstHom C C C).toRingHom :=
      ⟨fun x hx => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 hx⟩
    set gm := Φ _ (hh ≫ x₀)
    let J' : (Sp (DualNumber C) ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (redE C ≫ ψ)
    have hJ' : Good D.P.L (cpt (DualNumber C)) J' := fun ψ => by
      have h1 := ν.good (redE C ≫ ψ) (show cpt C ∈ (⊤ : (Sp C).Opens) from trivial)
      have hc : (redE C) (cpt C) = cpt (DualNumber C) :=
        IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom C C C).toRingHom
      have h2 : ψ ((redE C) (cpt C)) ∈ D.P.L.U (J' ψ) := h1
      rw [hc] at h2
      exact h2
    have ht := (top_le_iff_cpt (𝟙 (Sp (DualNumber C))) _).2 (hJ'.mem (DegPre.gtφT D (TE V C) gm.b χ) (𝟙 _))
    apply toStkA_injective (A := DualNumber C)
    have toStkA_valR {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
        (U : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
        toStkA z (valR x U a.val) = (Geo.Tor.gm x z U a).val := by
      have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp A).Opens) from trivial)
      rw [valR, dif_pos ht, Geo.Tor.gm, dif_pos hz]
      show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ ht).hom a.val))) = _
      rw [Iso.hom_inv_id_apply]
      exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial _
    have l1 := toStkA_valR (𝟙 (Sp (DualNumber C))) _ (cpt (DualNumber C)) ht ((gm.s χ).s _)
    have l2 := (val_corr hJ' ((hp _ _ hh x₀).2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
    have l3 := hval _ (𝟙 _ ≫ hh.left) _ _ hJ'
    have hv1 : valR (𝟙 (Sp (DualNumber V))) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom
        (1 + TrivSqZeroExt.inr a)) = 1 + TrivSqZeroExt.inr a := by
      have h0 : ⊤ ≤ 𝟙 (Sp (DualNumber V)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
      rw [valR, dite_eq_left h0]
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
      erw [show (homOfLE h0) = 𝟙 (⊤ : (Sp (DualNumber V)).Opens) from rfl]
      simp
    have l4 := FormalValue.toStkA_map_valR (dualMap (toF V C)) (𝟙 (Sp (DualNumber V))) ⊤ (cpt (DualNumber C))
      (fun _ _ => trivial) ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber V))).inv.hom (1 + TrivSqZeroExt.inr a))
    rw [hv1, Category.comp_id] at l4
    have hd : dualMap (toF V C) (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (toF V C a) := by
      ext <;> simp [dualMap]
    rw [hd] at l4
    rw [l4]
    refine l1.trans ?_
    refine (congrArg Units.val l2).trans ?_
    refine l3.trans ?_
    rw [Category.id_comp]
    rfl

end GlobalTheory.MBLow.TanPull

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.WpK

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

theorem ex_zero : d.ex 0 = 1 := by
  have h := d.ex_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem ex_nsmul (i : ℕ) (z : Fin g' → ℂ) : d.ex (i • z) = d.ex z ^ i := by
  induction i with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ i ih => rw [succ_nsmul, d.ex_add, ih, pow_succ]

theorem cubN_frame (k : ℕ) (x' x : Fin g' → ℂ) :
    cubN N.θ k 1 (d.ex x') (d.ex x) * d.fr (k • x') * d.fr x * d.fr (x' + x) ^ k =
      d.fr (k • x' + x) * (d.fr x' * d.fr x) ^ k := by
  induction k with
  | zero => simp [cubN, d.fr_zero]
  | succ k ih =>
    have h := d.cub (k • x') x' x
    rw [ex_nsmul] at h
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]
    replace h := congrArg Additive.ofMul h
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [pow_succ, ofMul_mul] at h ih ⊢
    linear_combination (norm := abel) h + ih

theorem full_transpose : (d.full σ 0)ᵀ = d.full σ 0 := by
  simp [CD.full, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, d.symm.eq, d.toricPeriodBlock_isSymm.eq]

theorem dot_split' (u v : Fin g → ℂ) : u ⬝ᵥ v = zP σ u ⬝ᵥ zP σ v + tP σ u ⬝ᵥ tP σ v := by
  simp only [dotProduct, zP, tP]
  rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]

end GlobalTheory.MBLow.Cl.WpK
end

noncomputable section
namespace GlobalTheory.MBLow.Cl.WpK
variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

theorem tk_frame {k : ℕ} (hk : 0 < k) {M Nn M' Nn' : Fin g → ℤ} {p p' : N.QT k} (h : d.Rep σ k M Nn p)
    (h' : d.Rep σ k M' Nn' p') :
    (N.tk p p' : ℂ) * (d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') + zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) : ℂ) ^ k =
      Complex.exp (2 * Real.pi * Complex.I * (cv Nn' ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) *
        ((d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn')) : ℂ) * d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn))) ^ k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set Z := (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn with hZ
  set Z' := (k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn' with hZ'
  set z := zP σ Z
  set z' := zP σ Z'
  set y' := p'.1.1.toAdd with hy'
  have hco : co bX y' = cv (tP σ Nn') := by rw [hy', h'.1]; exact Exp.co_sum _
  set cy := d.t12 *ᵥ co bX y' with hcy
  set per' := perV d.τ (zP σ M') (zP σ Nn') with hper
  have e : k • z' = cy + per' := by
    have : k • z' = zP σ (perV (d.full σ 0) M' Nn') := by
      funext i
      simp only [z', Z', zP, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
      rw [← _root_.mul_assoc, mul_inv_cancel₀ hk', _root_.one_mul]
    rw [this, Exp.leftComponent_periodVector, hcy, hco, add_comm]
  have e2 : k • z' + z = (cy + z) + per' := by rw [e]; abel
  have c := congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k z' z)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c
  rw [e2] at c
  have s := h.2.2 y'
  have f1 := Exp.fr_shift d (zP σ M') (zP σ Nn') (cy + z)
  have f2 := Exp.fr_shift d (zP σ M') (zP σ Nn') cy
  rw [e] at c
  rw [dotProduct_add, Exp.exp_two_pi_add] at f1
  have hT : cv Nn' ⬝ᵥ Z = cv (zP σ Nn') ⬝ᵥ z + co bX y' ⬝ᵥ tP σ Z := by
    rw [dot_split' σ, hco]; rfl
  rw [hT, Exp.exp_two_pi_add, NumD.tk, h.2.1, h'.2.1, Units.val_mul]
  set E1 := Complex.exp (2 * Real.pi * Complex.I * (co bX y' ⬝ᵥ tP σ Z))
  set E2 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn') ⬝ᵥ z))
  set E3 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn') ⬝ᵥ cy))
  have nA := (d.fr (cy + z)).ne_zero
  have nB := (d.fr (cy + per')).ne_zero
  have nC := (d.fr z).ne_zero
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero nA nB) nC)
  linear_combination (((cubN N.θ k 1 (d.ex z') (d.ex z) : ℂˣ) : ℂ) * d.fr (cy + per') * d.fr z * (d.fr (z' + z) : ℂ) ^ k) * s +
    (E1 * d.fr cy * d.fr z) * c + (E1 * d.fr cy * d.fr z * ((d.fr z' : ℂ) * d.fr z) ^ k) * f1 -
    (E2 * E1 * ((d.fr z' : ℂ) * d.fr z) ^ k * d.fr (cy + z) * d.fr z) * f2

end GlobalTheory.MBLow.Cl.WpK
end

namespace GlobalTheory.MBLow.Cl

theorem wp_classical : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p →
    d.Rep σ k M' Nn' p' → (N.wp p p' : ℂ) =
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv M ⬝ᵥ cv Nn' - cv Nn ⬝ᵥ cv M') / k) := by
  intro N g' r g bX d σ k hk M Nn M' Nn' p p' h h'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have a := WpK.tk_frame d σ hk h h'
  have b := WpK.tk_frame d σ hk h' h
  rw [add_comm, mul_comm (d.fr _ : ℂ)] at b
  have n1 := pow_ne_zero k (d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') +
    zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn))).ne_zero
  have hs : cv Nn' ⬝ᵥ d.full σ 0 *ᵥ cv Nn = cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn' := by
    rw [Exp.dotProduct_mulVec_eq_transpose_mulVec, WpK.full_transpose]
  have key : Complex.exp (2 * Real.pi * Complex.I * (cv Nn' ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) =
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv M ⬝ᵥ cv Nn' - cv Nn ⬝ᵥ cv M') / k) *
      Complex.exp (2 * Real.pi * Complex.I * (cv Nn ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn')) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [perV, dotProduct_smul, dotProduct_add, smul_eq_mul]
    rw [hs, dotProduct_comm (cv M) (cv Nn')]
    field_simp
    ring
  rw [NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]
  apply mul_right_cancel₀ n1
  rw [a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]

end GlobalTheory.MBLow.Cl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.familyMember_tangentValue_eq_firstJet : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g) (G : Geo ν d) (b : TE R ℂ ⟶ D.P.A) (W : Fin g → ℂ), redE ℂ ≫ b.left = (DegPre.zeroF D ℂ).left → IsD ν d W b → ∀ (k : ℕ) (s : Fam D ℂ k) (f : N.X → N.A → ℂ) (α : N.X) (ct : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ), ν.FamV s f → N.c α = d.ex ct → Differentiable ℂ φ → (∀ z, f α (d.ex z) * d.fr ct * d.fr z = φ z * (d.fr z : ℂ) ^ k * d.fr (ct + z)) → sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) b).left ν.J * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) = (TrivSqZeroExt.inl (φ 0) + TrivSqZeroExt.inr (fderiv ℂ φ 0 W)) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) ^ k * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) := by
  first | exact @GlobalTheory.MBLow.Cl.sE_fam_eq_jet | exact GlobalTheory.MBLow.Cl.sE_fam_eq_jet | (intros; apply GlobalTheory.MBLow.Cl.sE_fam_eq_jet <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.tangentVectorOfDualPoint_additive_lieComb : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (n : ℕ) (c : Fin n → R) (v : Fin n → (epsR R ⟶ D.P.A)) (w : epsR R ⟶ D.P.A) (W : Fin n → Fin g → ℂ) (b : Fin n → (TE R ℂ ⟶ D.P.A)) (bw : TE R ℂ ⟶ D.P.A), (∀ j, IsTangent (v j)) → IsLieComb c v w → (∀ j, (b j).left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (v j).left) → bw.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ w.left → (∀ j, IsD ν d (W j) (b j)) → IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (c j)) • W j) bw := by
  intro R _ _ D _ N ν g d n c v w W b bw hv hw hb hbw hW
  exact GlobalTheory.isD_lieComb R D N ν g d n c v w W b bw hv hw hb hbw hW
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ e : Multiplicative (AF D.host.F) ≃ₜ* ZI V ξ, (∀ a, ((e a : ZI V ξ) : GA D V) ∈ GQ V ↔ Multiplicative.toAdd a ∈ Set.range (algebraMap D.host.F (AF D.host.F)))) ∧ IsClosed (ZI V ξ : Set (GA D V)) ∧ (∀ z ∈ ZI V ξ, ∀ τ, InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (archM V (θ τ) z)) ∧ (∀ m : D.what₂.Tau → Mt V.rank, (∀ τ, InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (m τ)) → ∃ z ∈ ZI V ξ, z ∈ GinfC V ∧ ∀ τ, archM V (θ τ) z = m τ) ∧ ∀ z ∈ ZI V ξ, (matHom V z).1.mulVec (fun i => incA D (ξ i)) = fun i => incA D (ξ i) := by
  first | exact @GlobalTheory.HolDict.TransvGroup.transvection_group | exact GlobalTheory.HolDict.TransvGroup.transvection_group | (intros; apply GlobalTheory.HolDict.TransvGroup.transvection_group <;> assumption)
end
