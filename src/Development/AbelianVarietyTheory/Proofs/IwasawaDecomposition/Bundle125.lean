module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle002
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Formalism.LocalRingCardinality.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle123
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.SetTheory.Cardinal.Rat
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

set_option autoImplicit false

namespace GlobalTheory.AlgClosedIsoOverNumberField

open Cardinal

theorem exists_ringEquiv_commutes (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  apply GlobalTheory.PadicComplexIso.exists_ringEquiv_over <;> assumption

theorem exists_ringEquiv_comp_eq :
    ∀ (K Ω₁ Ω₂ : Type) [Field K] [NumberField K] [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁]
      [IsAlgClosed Ω₂] [CharZero Ω₁] [CharZero Ω₂] (a : K →+* Ω₁) (b : K →+* Ω₂),
      Cardinal.mk Ω₁ = Cardinal.mk Ω₂ → Cardinal.aleph0 < Cardinal.mk Ω₁ →
        ∃ ι : Ω₁ ≃+* Ω₂, ∀ x, ι (a x) = b x := by
  intro K Ω₁ Ω₂ _ _ _ _ _ _ _ _ a b hcard hbig
  let : Algebra K Ω₁ := a.toAlgebra
  let : Algebra K Ω₂ := b.toAlgebra

  have hK : #K ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
    rwa [Cardinal.mkRat, max_self] at this
  obtain ⟨e, he⟩ := exists_ringEquiv_commutes K Ω₁ Ω₂ hK hbig hcard
  exact ⟨e, he⟩

end GlobalTheory.AlgClosedIsoOverNumberField
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiTauCoordRel

open GlobalTheory.PeriodBalance GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

def kst (ξ : Spec (CommRingCat.of (FractionRing R))) :
    FractionRing R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ :=
  ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

theorem kst_algebraMap (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) :
    kst ξ (algebraMap R (FractionRing R) r) = cst ξ r := rfl

theorem kst_injective (ξ : Spec (CommRingCat.of (FractionRing R))) : Function.Injective (kst (R := R) ξ) :=
  RingHom.injective _

theorem gm_genVal (ξ : Spec (CommRingCat.of (FractionRing R))) {M : LB (TK R).left} (t : LB.Gen M) (j : M.ι)
    (h : ⊤ ≤ M.U j) :
    (gm (𝟙 _) ξ (M.U j) (t.s j)).val = kst ξ (genVal t j h).val := by
  rw [gm_val _ ξ _ (h trivial)]
  simp only [kst, genVal, RingHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, RingHom.toMonoidHom_eq_coe]
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h) ξ trivial _).symm

theorem gm_mulGen {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (y : Y) (j : K ⊕ K' → L.ι) (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    gm (𝟙 Y) y (LB.wchart L (Sum.elim φ φ') j) ((LB.mulGen L φ ε φ' ε' t t').s j) =
      gm (𝟙 Y) y (LB.wchart L φ (j ∘ Sum.inl)) (t.s (j ∘ Sum.inl)) *
        gm (𝟙 Y) y (LB.wchart L φ' (j ∘ Sum.inr)) (t'.s (j ∘ Sum.inr)) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) (gm_res _ y _ hy _))

theorem gm_invGen {Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (y : Y) (j : K → L.ι) :
    gm (𝟙 Y) y (LB.wchart L φ j) ((LB.invGen L φ ε t).s j) = (gm (𝟙 Y) y (LB.wchart L φ j) (t.s j))⁻¹ :=
  map_inv _ _

theorem mem_inl {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {φ' : K' → (Y ⟶ X)} {y : Y} {j : K ⊕ K' → L.ι} (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    y ∈ LB.wchart L φ (j ∘ Sum.inl) :=
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)

theorem mem_inr {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {φ' : K' → (Y ⟶ X)} {y : Y} {j : K ⊕ K' → L.ι} (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    y ∈ LB.wchart L φ' (j ∘ Sum.inr) :=
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)

variable [IsLocalRing R]

theorem val_psi_chart (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (χ : D.X) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D (D.c χ) (j PUnit.unit))
    (hm : ξ ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) :
    ∃ u : Rˣ, val (D.psi χ) (𝟙 _) ξ J = Units.map (cst ξ).toMonoidHom u *
      gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := by
  have hx : D.xK χ = jK R ≫ (D.c χ).left := DVR.QForm.ptK_eq D χ
  have t := gen_trans (D.psi_gen χ) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
    (hJ.mem (fun _ : PUnit => D.xK χ) (𝟙 _)) hm
  obtain ⟨u, hu⟩ := unit_gm' ξ (D.c χ).left (D.P.L.U (J (jK R ≫ (D.c χ).left)) ⊓ D.P.L.U (j PUnit.unit))
    ⟨hJc _ (Over.w _), hj trivial⟩ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit))
  have h2 : trF (L := D.P.L) (fun _ : PUnit => D.xK χ) (fun _ => -1) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (fun _ => J (𝟙 _ ≫ D.xK χ)) j =
        (gm (jK R ≫ (D.c χ).left) ξ _ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, hx]
  refine ⟨u⁻¹, t.trans ?_⟩
  rw [h2, map_inv]
  congr 2
  exact Units.ext hu

theorem val_int {A : Over (Spec (CommRingCat.of R))} {L : LB A.left} (ξ : Spec (CommRingCat.of (FractionRing R)))
    {J : ((Spec (CommRingCat.of (FractionRing R))) ⟶ A.left) → L.ι}
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)))
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (p : Spec (CommRingCat.of R) ⟶ Y) (hp : ∀ k, (p ≫ φ k) ≫ A.hom = 𝟙 _) :
    ∃ w : Rˣ, val t (jK R ≫ p) ξ J = Units.map (cst ξ).toMonoidHom w := by
  obtain ⟨w, hw⟩ := unit_gm' ξ p (LB.wchart L φ (fun k => J ((jK R ≫ p) ≫ φ k)))
    (Set.mem_iInter.2 fun k => by
      have := hJc (p ≫ φ k) (hp k)
      rw [← Category.assoc] at this
      exact this) (t.s _)
  exact ⟨w, Units.ext hw⟩

theorem toUnit_left : (toUnit (TK R)).left = jK R := by
  simpa using Over.w (toUnit (TK R))

theorem gm_rigK (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D η[D.P.A] (j PUnit.unit))
    (hm : ξ ∈ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j) :
    ∃ w : Rˣ, gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j) (D.rigK.s j) =
      Units.map (cst ξ).toMonoidHom w := by
  have e1 := gm_res (𝟙 _) ξ (show LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j ≤
      (toUnit (TK R)).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j from
      fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) hm
    (pullU (toUnit (TK R)).left _ (D.rig.s j))
  have e2 := gm_pull (𝟙 _) (toUnit (TK R)).left ξ (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) (D.rig.s j)
  have e3 : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
  rw [e3] at e2
  obtain ⟨w, hw⟩ := unit_gm' ξ (𝟙 _) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j)
    (Set.mem_iInter.2 fun _ => hj trivial) (D.rig.s j)
  exact ⟨w, (e1.trans e2).trans (Units.ext hw)⟩

theorem alg {G : Type} [CommGroup G] (T G1 G2 G3 c1 c2 c3 c4 c5 c6 c7 Vab Va Vb Vr Vu Kr : G)
    (h1 : T = G1 * G2⁻¹ * G3⁻¹ * c4⁻¹) (h2 : Vab = c1 * G1) (h3 : Va = c2 * G2) (h4 : Vb = c3 * G3)
    (h7 : Vr = c5) (h8 : Vu = c6)
    (h5 : Vab * Va⁻¹ * Vb⁻¹ * Vr⁻¹ * Vu = Va * Vr) (h6 : Va = c7 * Kr) :
    Kr = c1 * c2⁻¹ * c3⁻¹ * c4 * c5⁻¹ * c5⁻¹ * c6 * c7⁻¹ * T := by
  subst h1 h2 h4 h3 h7 h8
  have hK : Kr = c7⁻¹ * (c2 * G2) := by rw [h6]; group
  subst hK
  apply Additive.ofMul.injective
  have h5' := congrArg Additive.ofMul h5
  simp only [ofMul_mul, ofMul_inv] at h5' ⊢
  rw [← sub_eq_zero] at h5' ⊢
  refine Eq.trans ?_ (congrArg Neg.neg h5' |>.trans neg_zero)
  abel

theorem final (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) (h0 : r ≠ 0) (X : (FractionRing R)ˣ) (c : Rˣ)
    (key : Units.map (kst ξ).toMonoidHom (toUnitK r h0) =
      Units.map (cst ξ).toMonoidHom c * Units.map (kst ξ).toMonoidHom X) :
    algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (c : R) * (X : FractionRing R) := by
  have k3 : toUnitK r h0 = Units.map (algebraMap R (FractionRing R)).toMonoidHom c * X := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    rw [key, map_mul]
    rfl
  exact congrArg Units.val k3

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D.X] (oa : D.OAct O) (w0 : O), TraceFormTwistIso D oa w0 → ∀ (y : D.X) (r : R) (x : (FractionRing R)ˣ),
    PsiCoord D y r → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D y (w0 • y) x →
    ∃ u : Rˣ, algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u : R) * (x : FractionRing R) := by
  intro R _ _ _ D O _ _ _ oa w0 hW y r x hr hx
  obtain ⟨u, -, -, hrel⟩ := hW
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := Units.map (cst ξ).toMonoidHom
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom

  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hrel y) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [val_pull hJ] at e
  have e' := (congrArg (· * val u (𝟙 _ ≫ D.xK y) ξ J) (PeriodBalance.val_tau D ξ hJ y (w0 • y))).symm.trans e
  obtain ⟨c6, h6⟩ : ∃ w : Rˣ, val u (𝟙 _ ≫ D.xK y) ξ J = cU w := by
    have : 𝟙 _ ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact DVR.QForm.ptK_eq D y
    rw [this]
    refine val_int ξ hJc u (D.c y).left fun k => ?_
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A, (![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left,
        (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left] : Fin 4 → _) k = q.left := by
      fin_cases k
      · exact ⟨_, rfl⟩
      · exact ⟨𝟙 _, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    rw [hq, Category.assoc, Over.w q, Over.w]; rfl
  obtain ⟨c5, h5⟩ : ∃ w : Rˣ, val D.rigK (𝟙 _) ξ J = cU w := by
    unfold DegPre.rigK
    rw [val_pull hJ]
    have : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
    rw [this]
    exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]

  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau y (w0 • y)) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau y (w0 • y)).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc (y + w0 • y) _ i1 (mem_inl (mem_inl (mem_inl hm)))
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc y _ i2 (mem_inr (mem_inl (mem_inl hm)))
  obtain ⟨c3, g3⟩ := val_psi_chart D ξ hJ hJc (w0 • y) _ i3 (mem_inr (mem_inl hm))
  obtain ⟨c4, g4⟩ := gm_rigK D ξ _ i4 (mem_inr hm)

  have h0 := PsiCoordLocal.ne_zero_of_coord hr
  obtain ⟨jp, hp, ip, ep⟩ := GlobalTheory.PeriodFormCompare.isPsiCoord_toUnitK hr h0
  obtain ⟨c7, g7⟩ := val_psi_chart D ξ hJ hJc y jp ip (hp trivial)
  have eP := gm_genVal ξ (D.psi y) jp hp
  rw [← ep] at eP
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau y (w0 • y)).s j) =
      kU (genVal (D.tau y (w0 • y)) j h) := Units.ext eT
  have eP' : gm (𝟙 _) ξ (LB.wchart D.P.L _ jp) ((D.psi y).s jp) = kU (toUnitK r h0) := Units.ext eP
  have key := alg (h1 := eT'.symm.trans (dT.trans (by rw [g4]))) (h2 := g1) (h3 := g2) (h4 := g3) (h7 := h5)
    (h8 := h6) (h5 := e') (h6 := g7.trans (congrArg (cU c7 * ·) eP'))
  refine ⟨c1 * c2⁻¹ * c3⁻¹ * c4 * c5⁻¹ * c5⁻¹ * c6 * c7⁻¹, final ξ r h0 _ _ (key.trans ?_)⟩
  simp only [cU, kU, map_mul, map_inv]

end GlobalTheory.PsiTauCoordRel
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.heckeChar_exponent_of_infinityType : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E), (∀ n : (E →+* ℂ) → ℤ, χ.IsAlg n → ∀ τ, expo χ τ = n τ) ∧ (∀ s : ℝ, χ.IsAbsPow s → ∀ τ, expo χ τ = s) ∧ ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ), Function.Injective (fun i => InfinitePlace.mk (φ i)) → χ.HasInf φ n → ∀ i, expo χ (φ i) = (n i : ℂ) / 2 ∧ expo χ (ComplexEmbedding.conjugate (φ i)) = -(n i : ℂ) / 2 := by
  first | exact @GlobalTheory.CuspRep.InfType.expo_of_infType | exact GlobalTheory.CuspRep.InfType.expo_of_infType | (intros; apply GlobalTheory.CuspRep.InfType.expo_of_infType <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem mem_FilD_iff_xi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ ∃ y : Per.BdRp l, x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ (-a).toNat = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e) ^ a.toNat * y) := by
  intro l _ e he a x
  have h := (GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he).1
  have hg : ∀ (n : ℕ) (x : Per.BdR l), x ∈ Per.FilD l (-(n : ℤ)) ↔ ∃ y : Per.BdRp l,
      x * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi e)) ^ n = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    GlobalTheory.CrisLoc.mem_fil_neg l _ (GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he)
  generalize aDp l (xi e) = ξ at h hg ⊢
  have hn : ∀ (n : ℕ) (w : Per.BdR l), w ∈ Per.FilD l (n : ℤ) ↔
      ∃ y : Per.BdRp l, w = algebraMap (Per.BdRp l) (Per.BdR l) (ξ ^ n * y) := by
    intro n w
    constructor
    · intro hw
      obtain ⟨z, hz, ez⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l hw
      obtain ⟨y, rfl⟩ := (h _ _).1 hz
      exact ⟨y, ez.symm⟩
    · rintro ⟨y, rfl⟩
      exact GlobalTheory.RingIface.alg_mem_FilD_nat l ((h _ _).2 (dvd_mul_right _ _))
  rcases le_total 0 a with ha | ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [hn, Int.toNat_neg_natCast, Int.toNat_natCast, pow_zero, mul_one]
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat ha
    rw [hg, neg_neg, Int.toNat_neg_natCast, Int.toNat_natCast]
    simp only [pow_zero, one_mul]

end GlobalTheory.MemLoc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_maxUnramified_embedding_into_Bcris : ∀ (l : ℕ) [Fact l.Prime], ∀ (o : Om l →+* Per.BdRp l) (ι : Per.Bcris l →+* Per.BdR l), IsSec o → Function.Injective ι → (∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a)) → IsUnit (l : Per.Bcris l) → ∃ u : ↥(MaximalUnramifiedExtension l) →+* Per.Bcris l, ∀ c : ↥(MaximalUnramifiedExtension l), ι (u c) = algebraMap (Per.BdRp l) (Per.BdR l) (o (c : Om l)) := by
  first | exact @GlobalTheory.MemLoc.exists_unram_to_cris | exact GlobalTheory.MemLoc.exists_unram_to_cris | (intros; apply GlobalTheory.MemLoc.exists_unram_to_cris <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → (∀ j' : Per.Acris l →+* Per.BdRp l, IsCrisP j' → j' = j) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), j (sigA g x) = Per.σDp g (j x)) ∧ ∀ (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l), (∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧ Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) = Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) → Per.ev l n (j x) = Per.ev l n y := by
  first | exact @GlobalTheory.MemLoc.crisP_unique_equivariant | exact GlobalTheory.MemLoc.crisP_unique_equivariant | (intros; apply GlobalTheory.MemLoc.crisP_unique_equivariant <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_canonical_acris_to_bdRPlus : ∀ (l : ℕ) [Fact l.Prime], ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j := by
  first | exact @GlobalTheory.MemLoc.exists_isCrisP | exact GlobalTheory.MemLoc.exists_isCrisP | (intros; apply GlobalTheory.MemLoc.exists_isCrisP <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.uniformisationTorus_mono_and_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (a : R →+* A) (e : ℕ) (ha : ∀ x ∈ I ^ (e + 1), a x = 0)
    (G₀ : Over (Sp A)) [GrpObj G₀] (φ : G₀.left ⟶ t.G.left) (h : IsGrpPullback G₀ t.G (spMap a) φ),
    Mono (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h) ∧
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
      ∃ ρ : P.D.toPre.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h := by
  first | exact @GlobalTheory.TorusPart.mono_gtTorus_unif_and_factor | exact GlobalTheory.TorusPart.mono_gtTorus_unif_and_factor | (intros; apply GlobalTheory.TorusPart.mono_gtTorus_unif_and_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical


theorem _root_.GlobalTheory.T.functionFieldIntegralModel_exists_isHom_of_map_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') → ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | exact GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | (intros; apply GlobalTheory.ZH.RatModel.exists_isHom_of_map_O <;> assumption)
end

section

open NumberField Formalism.BasicNotions

namespace GlobalTheory.AutLattice

section
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_int_smul_mem (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulMemLattice.exists_int_smul_mem ..)

theorem finrank_int_eq (L : Submodule (𝓞 E) V) (hL : Submodule.span E (L : Set V) = ⊤) :
    Module.finrank ℤ L = Module.finrank ℚ E * Module.finrank E V := by
  let _i : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have : IsScalarTower ℚ E V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  rw [Module.finrank_mul_finrank ℚ E V,
    IsLocalization.finrank_eq ℚ (N := V) (nonZeroDivisors ℤ) le_rfl]
  let f : L →ₗ[ℤ] V := L.subtype.toAddMonoidHom.toIntLinearMap
  have : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    { map_units := fun s =>
        (isLocalizedModule_id (nonZeroDivisors ℤ) V ℚ).map_units s
      surj := fun v => by
        obtain ⟨n, hn, h⟩ := exists_int_smul_mem L hL v
        exact ⟨(⟨n • v, h⟩, ⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩), rfl⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        have : x = y := Subtype.ext h
        rw [this]⟩ }
  exact (IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) f le_rfl).symm

end

theorem card_dvd_minkM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V), L.FG → Submodule.span E (L : Set V) = ⊤ → ∀ G : Subgroup (V ≃ₗ[E] V), Finite G → (∀ g ∈ G, ∀ x ∈ L, g x ∈ L) → Nat.card G ∣ minkM (Module.finrank ℚ E * Module.finrank E V) := by
  intro hM E V _ _ _ _ _ _ _ L hfg hL G hG hGL
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have : HasUniqueDiv V := HasUniqueDiv.of_isTorsionFree E V
  have : Module.Free ℤ L := inferInstance
  rw [← finrank_int_eq L hL]
  let b := Module.finBasis ℤ L
  let r : G →* Module.End ℤ L :=
    { toFun := fun g => AddMonoidHom.toIntLinearMap
        { toFun := fun x => ⟨g.1 x.1, hGL g.1 g.2 x.1 x.2⟩
          map_zero' := Subtype.ext (by simp)
          map_add' := fun x y => Subtype.ext (by simp) }
      map_one' := by ext x; rfl
      map_mul' := fun g h => by ext x; rfl }
  have hr : Function.Injective r := by
    intro g h hgh
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hL
    intro x hx
    exact congrArg Subtype.val (LinearMap.congr_fun hgh ⟨x, hx⟩)
  let φ : G →* GL (Fin (Module.finrank ℤ L)) ℤ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := by
    intro g h hgh
    apply hr
    apply (LinearMap.toMatrixAlgEquiv b).injective
    exact congrArg Units.val hgh
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM _ φ.range (Finite.of_equiv _ e.toEquiv)

end GlobalTheory.AutLattice
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_inertiaFixed_integral_of_separating_element : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (σ : G E Ω), σ ∈ Ine (F := E) A' → ∀ (e₀ c : Ω), IsIntegral ℤ e₀ → A.valuation e₀ < A.valuation c → A'.valuation (1 - e₀) < 1 → ∃ e : Ω, IsIntegral ℤ e ∧ σ e = e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  first | exact @GlobalTheory.exists_fixed_of_separating | exact GlobalTheory.exists_fixed_of_separating | (intros; apply GlobalTheory.exists_fixed_of_separating <;> assumption)
end
