module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Poinc.FrameIndep

theorem ratio_indep {X H Y Z B B' : Scheme.{0}} {L : LB X} {M : LB H} {f : Y ⟶ H} {ψ : Y ⟶ X}
    (w : LB.Iso (L.pull ψ) (M.pull f)) (hw : w.IsGen) {e : B ⟶ X} {e' : B' ⟶ H}
    {a : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => e) (fun _ => 1))}
    {a' : LB.Gen (LB.LinComb M (K := Fin 1) (fun _ => e') (fun _ => 1))} (ha : a.IsGen)
    (ha' : a'.IsGen) (r : Z ⟶ Y) (t : Z ⟶ B) (t' : Z ⟶ B') (p : Z ⟶ X) (p' : Z ⟶ H)
    (h : r ≫ ψ = p) (h' : r ≫ f = p') (k : t ≫ e = p) (k' : t' ≫ e' = p') (z : Z)
    {J J' I I'} (hJ : Good L z J) (hJ' : Good M z J') (hI : Good L z I) (hI' : Good M z I') :
    Geo.Tor.gw w r z (J' p') (fun _ => J p) * val a t z J * (val a' t' z J')⁻¹ =
      Geo.Tor.gw w r z (I' p') (fun _ => I p) * val a t z I * (val a' t' z I')⁻¹ := by
  subst h h'
  have e₁ : val a t z J = _ * val a t z I := gen_trans ha t z (hJ.mem _ t) (hI.mem _ t)
  have e₂ : val a' t' z J' = _ * val a' t' z I' := gen_trans ha' t' z (hJ'.mem _ t') (hI'.mem _ t')
  have e₃ : Geo.Tor.gw w r z (J' (r ≫ f)) (fun _ => J (r ≫ ψ)) =
      _ * Geo.Tor.gw w r z (I' (r ≫ f)) (fun _ => I (r ≫ ψ)) :=
    (Geo.Tor.isGen_iff w).1 hw Z r z _ _ _ _ (hJ' (r ≫ f)) (hI' (r ≫ f))
      (mem_pull.2 (hJ (r ≫ ψ))) (mem_pull.2 (hI (r ≫ ψ)))
  rw [Geo.Tor.gm_pull_g L ψ r z _ _ (mem_pull.2 (hJ (r ≫ ψ))) (mem_pull.2 (hI (r ≫ ψ)))] at e₃
  rw [Geo.Tor.trF, Fintype.prod_unique, zpow_one] at e₁ e₂
  rw [k] at e₁
  rw [k'] at e₂
  rw [e₁, e₂, e₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem frame_ratio_indep : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x), e.IsGen → ∀ (h : 𝟙_ (Over (Sp V)) ⟶ G) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), f.IsGen → GlobalTheory.Poinc.IntTerm.Ext U x h → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA JA' : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG JG' : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → Good A.L z JA' → Good U.LG.L z JG' → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG)⁻¹ = Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG' (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA' x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA' * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG')⁻¹ := by
  intro V _ _ I D A G _ _ U w₀ hw₀ x e he h f hf hx z JA JA' JG JG' hJA hJG hJA' hJG'
  refine ratio_indep w₀ hw₀ he hf (x.left ≫ U.gen.inv.left) (𝟙 _) (toUnit (TF (R := V) (FractionRing V))).left
    x.left (toUnit (TF (R := V) (FractionRing V)) ≫ h).left ?_ ?_ (Category.id_comp _) rfl z hJA hJG hJA' hJG'
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (x.left ≫ ·) (congrArg (·.left) U.gen.inv_hom_id)).trans (Category.comp_id _)
  · exact (Category.assoc _ _ _).trans hx

end GlobalTheory.Poinc.FrameIndep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Tors

theorem ext_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (x x' : TFK (R := V) (FractionRing V) ⟶ A.A) (h h' h'' : (𝟙_ (Over (Sp V))) ⟶ G), IntTerm.Ext U.toUnifPre x h → IntTerm.Ext U.toUnifPre x' h' → IntTerm.Ext U.toUnifPre (x * x') h'' → h'' = h * h' := by
  intro V _ _ _ _ D A G _ _ _ U x x' h h' h'' hx hx' hx''
  have := U.gen_hom
  have := U.separated
  have hmon : IsMonHom U.gen.inv := inferInstance
  have hpb := isGrpPullback_pullback G (jK V)
  have e₁ := hpb.2 (TFK (R := V) (FractionRing V)) (x ≫ U.gen.inv) (x' ≫ U.gen.inv)
    (toUnit (TF (R := V) (FractionRing V)) ≫ h) (toUnit (TF (R := V) (FractionRing V)) ≫ h')
    (hx.symm.trans (Category.assoc _ _ _).symm) (hx'.symm.trans (Category.assoc _ _ _).symm)
  have e₂ : (x * x') ≫ U.gen.inv = (x ≫ U.gen.inv) * (x' ≫ U.gen.inv) := MonObj.mul_comp _ _ _
  have e₃ : toUnit (TF (R := V) (FractionRing V)) ≫ (h * h') =
      (toUnit (TF (R := V) (FractionRing V)) ≫ h) * (toUnit (TF (R := V) (FractionRing V)) ≫ h') :=
    MonObj.comp_mul _ _ _
  have e : (toUnit (TF (R := V) (FractionRing V)) ≫ h'').left =
      (toUnit (TF (R := V) (FractionRing V)) ≫ (h * h')).left := by
    rw [e₃]
    refine Eq.trans ?_ e₁.symm
    rw [← e₂]
    exact hx''.symm.trans (Category.assoc _ _ _).symm
  have hj : (toUnit (TF (R := V) (FractionRing V))).left = jK V := by
    have h₁ : jFK (R := V) (FractionRing V) = 𝟙 _ := Spec.map_id _
    have h₂ : (toUnit (TF (R := V) (FractionRing V))).left ≫ 𝟙 _ = jFK (R := V) (FractionRing V) ≫ jK V :=
      Over.w (toUnit (TF (R := V) (FractionRing V)))
    rw [Category.comp_id, h₁] at h₂
    exact h₂.trans (Category.id_comp _)
  have hd : IsDominant (jK V) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap V (FractionRing V))).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))]; exact bot_le)
  refine Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp V) G.hom ((Over.w h'').trans (Over.w (h * h')).symm) (jK V) ?_)
  rw [← hj]
  exact e

end GlobalTheory.Poinc.Tors
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.Poinc.IntTerm.IntPoint

theorem cst_toUnit (V : Type) [CommRing V] [IsDomain V] (z : (TF (R := V) (FractionRing V)).left) (a : V) :
    Geo.Tor.cst (toUnit (TF (R := V) (FractionRing V))).left z a =
      GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  have hx : (toUnit (TF (R := V) (FractionRing V))).left = jFK (R := V) (FractionRing V) ≫ jK V := by
    simpa using Over.w (toUnit (TF (R := V) (FractionRing V)))
  rw [hx]
  erw [GlobalTheory.ExpansionValueZero.cst_comp]
  erw [H1.gs_spec]
  rfl

theorem formEq_prod {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (g : GtPt D (𝟙_ (Over (Sp V)))) (mu : D.X) :
    FormEq (fun k => (D.c mu * g.b).left ≫ D.famφB 0 k) (DegPre.famε 1)
      (Sum.elim (Sum.elim (fun _ : PUnit => (D.c mu).left) (DegPre.gtφT D (𝟙_ _) g.b mu)) ![(η[D.P.A]).left, g.b.left])
      (fun k => -(Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) DegPre.gtε) (DegPre.lineε 1)) k) := by
    have hu : toUnit (𝟙_ (Over (Sp V))) = 𝟙 _ := toUnit_unique _ _
    have c0 := ThetaOne.c_zero D
    have e2 : (toUnit D.P.A ≫ D.c 0) = toUnit D.P.A ≫ η[D.P.A] := by
      rw [c0, MonObj.comp_one, Hom.one_def]
    have e1 : (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ η[D.P.A])) = 𝟙 D.P.A := by
      rw [← e2, c0, MonObj.comp_one, padd, ← Hom.mul_def, _root_.mul_one]
    have e3 : padd D.P.A (DegPre.cT D (𝟙_ _) mu) g.b = D.c mu * g.b := by
      rw [padd, ← Hom.mul_def, DegPre.cT, hu, Category.id_comp]
    have e4 : DegPre.cT D (𝟙_ _) mu = D.c mu := by rw [DegPre.cT, hu, Category.id_comp]
    have e5 : DegPre.zeroT D (𝟙_ (Over (Sp V))) = η[D.P.A] := by rw [DegPre.zeroT, hu, Category.id_comp]
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two, DegPre.famφB, DegPre.gtφT, DegPre.famε, DegPre.gtε,
      DegPre.lineε, e1, e2, e3, e4, e5]
    have e6 : padd D.P.A (D.c mu) g.b = D.c mu * g.b := by rw [padd, ← Hom.mul_def]
    rw [e6]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1))), gam.IsGen → ∃ a : V, (∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z l * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a)) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a)) := by
  intro V _ _ _ D θ g g' w l hP hI mu gam hgam
  obtain ⟨t, ht, htv⟩ := hI
  have hL := D.P.isLB
  have hp := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hgam (g.isGen mu)) ht
  obtain ⟨a, ha⟩ := GlobalTheory.ExpansionValueZero.exists_coeff (A := V) hL θ (D.c mu * g.b).left _ (invGen_isGen _ _ _ _ hp)
    (formEq_prod D g mu)
  refine ⟨a, fun z J hJ => ?_, fun ⟨J, hJ, hU⟩ => ?_⟩
  · have hg' : g'.b = toUnit (TF (R := V) (FractionRing V)) ≫ g.b := Over.OverMorphism.ext hP.1
    have hb : (padd D.P.A (DegPre.cT D _ mu) g'.b).left =
        (toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu * g.b).left := by
      rw [← Over.comp_left, hg', Hom.mul_def, padd, ← Category.assoc, comp_lift]
    have hs : Geo.Tor.val (g'.s mu) (𝟙 _) z J = Geo.Tor.val (g.s mu) (toUnit (TF (R := V) (FractionRing V))).left z J :=
      (val_corr hJ (hP.2 mu) (𝟙 _)).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have e₁ := ha _ (toUnit (TF (R := V) (FractionRing V))).left z J hJ
    rw [hb, e₁, hs, cst_toUnit, val_inv, val_mul hJ, val_mul hJ]
    have h₁ := htv z J hJ
    generalize GlobalTheory.UT.cst (FractionRing V) z l = c₁ at h₁ ⊢
    generalize GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a) = c₂
    generalize Geo.Tor.val w (𝟙 _) z J = u₁ at h₁ ⊢
    generalize Geo.Tor.val t (toUnit (TF (R := V) (FractionRing V))).left z J = u₂ at h₁ ⊢
    generalize Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J = u₃
    generalize Geo.Tor.val (g.s mu) (toUnit (TF (R := V) (FractionRing V))).left z J = u₄
    calc c₁ * u₃.val * (c₂ * ((u₃ * u₄ * u₂)⁻¹).val) * u₄.val * u₁.val
        = c₂ * ((c₁ * u₁.val) * (u₃.val * u₄.val) * ((u₃ * u₄ * u₂)⁻¹).val) := by ring
      _ = c₂ := by
        rw [h₁, mul_comm u₂.val, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          _root_.mul_one]
  · have e₁ := ha (Sp V) (𝟙 _) (closedPoint V) J hJ
    rw [Category.id_comp] at e₁
    rw [e₁] at hU
    exact isUnit_of_mul_isUnit_left hU

end GlobalTheory.Poinc.IntTerm.IntPoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.IntEval
open GlobalTheory.UT.CoefBasic GlobalTheory.BoxExpansion GlobalTheory.UT.EvalZero

theorem alg_value_at {M K : Type} [CommRing M] [Fintype K] {k : ℕ} {P E Fv : Mˣ} {Sσ sA cv cl : M} {u d : K → M}
    (h₁ : Sσ = (P ^ k).val * sA) (h₂ : Sσ = ∑ i, u i) (h₃ : sA = cv * (E ^ k).val) (h₄ : P.val * E.val = cl * Fv.val)
    (h₅ : ∀ i, u i = d i * (Fv ^ k).val) : cv * cl ^ k = ∑ i, d i := by
  refine (Fv ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_congr rfl fun i _ => h₅ i, ← h₂, h₁, h₃]
  simp only [Units.val_pow_eq_pow_val]
  calc cv * cl ^ k * Fv.val ^ k = cv * (cl * Fv.val) ^ k := by ring
    _ = cv * (P.val * E.val) ^ k := by rw [h₄]
    _ = _ := by ring

theorem value_at_section : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp R)) ⟶ G) (l : FractionRing R) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), IntTerm.Ext U x h → (∀ (z : (TF (R := R) (FractionRing R)).left) (JA : ((TF (R := R) (FractionRing R)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := R) (FractionRing R)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := R) (FractionRing R)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := R) (FractionRing R)) ≫ h).left) (fun _ => JA x.left)).val * (val (Z := (TF (R := R) (FractionRing R)).left) e (𝟙 _) z JA).val = GlobalTheory.UT.cst (FractionRing R) z l * (val f (toUnit (TF (R := R) (FractionRing R))).left z JG).val) → ∀ (k : ℕ) (s : SecA A (FractionRing R) k) (σ' : U.SecGF (FractionRing R) k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) (FractionRing R)) A.A).left (U.genF (FractionRing R)).left s (UnifPre.gFK (G := G) (FractionRing R)) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → FractionRing R) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) (FractionRing R)) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) (FractionRing R)) (fun i => scal (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left (c i)) → ∀ xs : Fin n → R, (∀ (i : Fin n) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val) → ∀ v : FractionRing R, ValAt s x e v → v * l ^ k = ∑ i, c i * algebraMap R (FractionRing R) (xs i) := by
  intro R _ _ I D A G _ _ U w₀ x e h l f hExt hF k s σ' hR n c σ hσ xs hxs v hv
  obtain ⟨z⟩ := exists_pt (R := R) (F := FractionRing R)
  obtain ⟨JA, hA⟩ := exists_good' (Z := (TFK (R := R) (FractionRing R)).left) A.isLB z
  obtain ⟨JG, hG⟩ := exists_good' (Z := (TFK (R := R) (FractionRing R)).left) U.LG.isLB z
  let r : TFK (R := R) (FractionRing R) ⟶ UnifPre.GF (G := G) (FractionRing R) := lift (𝟙 _) (x ≫ U.gen.inv)
  have e₁ : r.left ≫ (snd (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left =
      x.left ≫ U.gen.inv.left := by
    rw [← Over.comp_left, lift_snd]; rfl
  have e₂ : r.left ≫ (U.genF (FractionRing R)).left = (ptSecT A.A x).left := by
    rw [← Over.comp_left]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp [r, ptSecT]
    · simp [r, ptSecT]
  have e₀ : (toUnit (TF (R := R) (FractionRing R))).left = jFK (R := R) (FractionRing R) ≫ jK R := by
    simpa using Over.w (toUnit (TF (R := R) (FractionRing R)))
  have e₃ : r.left ≫ UnifPre.gFK (G := G) (FractionRing R) = (toUnit (TF (R := R) (FractionRing R)) ≫ h).left := by
    rw [← Category.assoc, e₁, Category.assoc]; exact hExt
  have e₄ : r.left ≫ (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have e₅ : (x.left ≫ U.gen.inv.left) ≫ U.gen.hom.left = x.left := by
    rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id]; exact Category.comp_id _
  have e₆ : (x.left ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R) (FractionRing R)) ≫ h).left := by
    rw [Category.assoc]; exact hExt
  have a₁ := isoRel_val hR r.left z hA hG
  rw [Category.comp_id, e₁, e₂, e₅, e₆] at a₁
  have a₂ := secLin_val hσ r.left z hG
  rw [e₃] at a₂
  have a₃ := hv z JA hA
  rw [GlobalTheory.UT.NonVan.val_powFrame, zpow_natCast] at a₃
  have a₄ := hF z JA JG hA hG

  rw [cst_eq] at a₃ a₄
  apply cstH_inj (R := R) z

  rw [map_mul, map_pow, map_sum]
  refine alg_value_at a₁ a₂ a₃ a₄ (fun i => ?_)
  have b : gs r.left z ⊤ (scal (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left (c i)) =
      cstH (R := R) z (c i) :=
    ((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₄]; rfl)).trans (cst_eq (R := R) z _)
  have cb : Geo.Tor.cst (toUnit (TF (R := R) (FractionRing R))).left z (xs i) =
      cstH (R := R) z (algebraMap (FractionRing R) (FractionRing R) (algebraMap R _ (xs i))) := by
    rw [e₀]; exact cst_base (R := R) (FractionRing R) z (xs i)
  rw [b, Over.comp_left, hxs i _ _ z JG hG, cb, map_mul, _root_.mul_assoc]
  simp

end GlobalTheory.Poinc.IntEval
end
end

section

noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem exists_sympCond_geom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ M → Odd M → M.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
    ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (Over.mk x ⟶ o.A)),
      SympCond o (Module.finrank ℤ D.La / 2) M (Over.mk x) t₁ lv := by
  intro p _ D R _ b N M e hM3 hModd hMp hMe hperf S t o K _ _ x
  have hM0 : 0 < M := by omega
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, x ≫ t = spMap β :=
    ⟨(Spec.preimage (x ≫ t)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨I, -⟩ := o.geom K x β hβ
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨L, hLker, hLonto, hLω⟩ := GlobalTheory.T.exists_lattice_map_mod_of_perfect_alternating D.La D.EF D.alt D.nondeg e M hperf hMe
  have hMK : IsUnit (M : K) := by simpa using (b.unit M hMp).map β
  have hprim : IsPrimitiveRoot ((I.ζ M : Kˣ) : K) M :=
    IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim M hM0 hMp)
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.T.exists_ringHom_cyclotomicAway_to_field_primitiveRoot M (by omega) K _ hprim hMK
  refine ⟨spMap β₀, fun a => I.ev M (L a), fun a c => by show I.ev M (L (a + c)) = I.ev M (L a) * I.ev M (L c); rw [map_add (f := _), I.add],
    fun a => (I.onto M hM0 hMp _).2 ⟨L a, rfl⟩, ?_⟩
  intro k _ _ x' β' z hx' hz
  obtain ⟨φ, rfl⟩ : ∃ φ : K →+* k, x' = spMap φ := ⟨(Spec.preimage x').hom, (Spec.map_preimage _).symm⟩
  have hβ' : β' = φ.comp β₀ := by
    have e2 : CommRingCat.ofHom β' = CommRingCat.ofHom (φ.comp β₀) :=
      Spec.map_injective (hx'.symm.trans (by simp [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]))
    exact congrArg CommRingCat.Hom.hom e2
  subst hβ'
  have hz' : z = Units.map φ.toMonoidHom (I.ζ M) := Units.ext (by simpa [hβ₀] using hz)
  subst hz'
  obtain ⟨β'', hβ''⟩ : ∃ β'' : R →+* k, (spMap φ ≫ x) ≫ t = spMap β'' :=
    ⟨(Spec.preimage ((spMap φ ≫ x) ≫ t)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨I', -⟩ := o.geom k (spMap φ ≫ x) β'' hβ''
  let h : Over.mk (spMap φ ≫ (Over.mk x).hom) ⟶ Over.mk x := Over.homMk (spMap φ) rfl
  have : Epi h.left := GlobalTheory.UPel.GeometricLevelExistence.epi_spMap_field φ
  have : Epi h := Over.epi_of_epi_left h
  change (∀ a, h ≫ I.ev M (L a) = 1 ↔ _) ∧ (∀ g : Over.mk (spMap φ ≫ (Over.mk x).hom) ⟶ o.A, g ^ M = 1 →
      ∃ a, h ≫ I.ev M (L a) = g) ∧ ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M
        (h ≫ I.ev M (L a)) (h ≫ I.ev M (L c)) (unitOn (Units.map φ.toMonoidHom (I.ζ M) ^ (2 * omegaStd a c)))
  have hPa : ∀ a b, h ≫ I.ev M (a + b) = (h ≫ I.ev M a) * (h ≫ I.ev M b) := fun a b => by
    rw [I.add, MonObj.comp_mul]
  have hP : ∀ a, h ≫ I.ev M a = 1 ↔ ∃ b, a = M • b := fun a => by
    rw [← I.ker M hM0 hMp a]
    constructor
    · intro e
      rw [← cancel_epi h, e, MonObj.comp_one]
    · intro e
      rw [e, MonObj.comp_one]
  have hQ : ∀ a, I'.ev M a = 1 ↔ ∃ b, a = M • b := I'.ker M hM0 hMp
  have hPQ : ∀ a, ∃ c, h ≫ I.ev M a = I'.ev M c := fun a => by
    have e : (h ≫ I.ev M a) ^ M = 1 := by
      rw [← MonObj.comp_pow, (I.onto M hM0 hMp (I.ev M a)).2 ⟨a, rfl⟩, MonObj.comp_one]
    obtain ⟨c, hc⟩ := (I'.onto M hM0 hMp _).1 e
    exact ⟨c, hc.symm⟩
  refine ⟨fun a => (hP (L a)).trans (hLker a), fun g hg => ?_, fun a c => ?_⟩
  · obtain ⟨c, rfl⟩ := (I'.onto M hM0 hMp g).1 hg
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.UPel.GeometricLevelExistence.exists_eq_of_count M hM0 _ _ hPa (I'.add M) hP hQ hPQ c
    obtain ⟨a, y, rfl⟩ := hLonto x₀
    refine ⟨a, ?_⟩
    rw [← hx₀, hPa, (hP _).2 ⟨y, rfl⟩, _root_.mul_one]
  · have H := CommPairing.weilIs_pull globalFns_holds o.ab (LB.isLB_pull o.isLB _) h (I.isom M hM0 hMp (L a) (L c))
    have e : Units.map h.left.appTop.hom.toMonoidHom (unitOn (I.ζ M ^ (2 * D.EF (L a) (L c)))) =
        unitOn (Units.map φ.toMonoidHom (I.ζ M) ^ (2 * omegaStd a c)) := by
      obtain ⟨k₀, hk₀⟩ := hLω a c
      have hζM : I.ζ M ^ (M : ℤ) = 1 := by
        rw [zpow_natCast]
        exact (I.ζ_prim M hM0 hMp).pow_eq_one
      have hK : I.ζ M ^ (2 * D.EF (L a) (L c)) = I.ζ M ^ (2 * omegaStd a c) := by
        rw [hk₀, show (2 : ℤ) * (omegaStd a c + M * k₀) = 2 * omegaStd a c + M * (2 * k₀) by ring, zpow_add,
          zpow_mul (I.ζ M) (M : ℤ), hζM, one_zpow, _root_.mul_one]
      rw [hK, ← map_zpow]
      exact GlobalTheory.UPel.GeometricLevelExistence.unitOn_pull_spMap φ _
    rw [e] at H
    exact H

end GlobalTheory.HTSympCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.HTSympCover

theorem isSympLev_of_sympCond_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
  (o' : Obj b N (T.hom ≫ t)) (m : ObjMap o' o T.hom)
  (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T.left) ⟶ o'.A)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
    (∀ a, (lv' a).left ≫ m.φ = (lv a).left) → SympCond o h M T t₁ lv →
      IsSympLev o'.P h M (zetaAway M) t₁ lv' := by
  intro p _ D R _ b N h M S t o T t₁ o' m lv' lv hα hlv
  obtain ⟨hadd, hkill, hgeo⟩ := hlv
  obtain ⟨ρ, eρ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over T.left))
  let j : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key : ∀ a, ρ (lv' a) = j ≫ lv a := fun a => Over.OverMorphism.ext (by simp [eρ, hα, j])
  have dg := GlobalTheory.SiegelPull.diag_iso m.sq m.pol
  refine ⟨fun a c => ρ.injective ?_, fun a => ρ.injective ?_, fun k _ _ x β z hx hz => ?_⟩
  · rw [map_mul, key, key, key, hadd, MonObj.comp_mul]
  · rw [map_pow, key, ← MonObj.comp_pow, hkill, MonObj.comp_one, map_one]
  obtain ⟨hker, honto, hw⟩ := hgeo k x β z hx hz
  obtain ⟨σ, eσ⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (Over.mk x)
  have key' : ∀ a, σ (toUnit (Over.mk x) ≫ lv' a) = (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a :=
    fun a => Over.OverMorphism.ext (by
      rw [eσ, Over.comp_left, Category.assoc, hα, Over.comp_left]
      congr 1)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a c => ?_⟩
  · rw [← hker a, ← key', map_eq_one_iff _ σ.injective]
  · obtain ⟨a, ha⟩ := honto (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σ.injective (by rw [key', ha])⟩
  · exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A T.hom m.φ _ _ (pull_isLB o.isLB _)
      (pull_isLB o'.isLB _) m.cart dg (Over.mk x) M _ _ _ _ _ (eσ _) (eσ _)).2 (by rw [key', key']; exact hw a c)

end GlobalTheory.HTSympCover
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

open GlobalTheory.FieldBaseChange

theorem exists_linear_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), ∃ b : SecF A F N →ₗ[F] SecF A F N, ∀ t t' : SecF A F N, IsActOf A.A A.L N θ t t' ↔ t' = b t := by
  intro R _ _ A F _ _ N θ
  have hex : ∀ t : SecF A F N, ∃ u : SecF A F N, IsActOf A.A A.L N θ t u :=
    fun t => GlobalTheory.VVCompare.exists_isActOf A.A A.isLB θ t
  choose Θ hΘ using hex
  have hb : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : translT A.A θ.pt ≫ fst _ _ = _)
  have hv := fun (t u : SecF A F N) (h : IsActOf A.A A.L N θ t u) y J hJ =>
    GlobalTheory.VVCompare.sv_of_isTwistPull A.A h (𝟙 _) y (J := J) hJ
  refine ⟨⟨⟨Θ, fun s s' => sec_ext' A.isLB fun y J hJ => ?_⟩,
    fun c s => sec_ext' A.isLB fun y J hJ => ?_⟩, fun t t' => ⟨fun h => sec_ext' A.isLB fun y J hJ => ?_, ?_⟩⟩
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_add' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_add' hJ _ s s')).symm))
    exact (congrArg₂ (· + ·) (hv _ _ (hΘ s) y J hJ) (hv _ _ (hΘ s') y J hJ)).trans (mul_add _ _ _).symm
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_smul' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_smul' hJ _ c s)).symm))
    rw [Category.assoc, hb]
    exact (congrArg _ (hv _ _ (hΘ s) y J hJ)).trans (mul_left_comm _ _ _)
  · exact (hv _ _ h y J hJ).trans (hv _ _ (hΘ t) y J hJ).symm
  · rintro rfl
    exact hΘ t

end GlobalTheory.Mum.Desc
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem _root_.GlobalTheory.T.isSymplecticLevel_of_pulledBack_object : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
  (o' : Obj b N (T.hom ≫ t)) (m : ObjMap o' o T.hom)
  (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T.left) ⟶ o'.A)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
    (∀ a, (lv' a).left ≫ m.φ = (lv a).left) → SympCond o h M T t₁ lv →
      IsSympLev o'.P h M (zetaAway M) t₁ lv' := by
  first | exact @GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull | exact GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull | (intros; apply GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull <;> assumption)

end
end
