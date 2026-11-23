module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle877
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1985
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torsionSection_of_torsionRationalOverFraction : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  first | exact @GlobalTheory.TorsConst.exists_section_of_torsRat | exact GlobalTheory.TorsConst.exists_section_of_torsRat | (intros; apply GlobalTheory.TorsConst.exists_section_of_torsRat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.weilPairing_eq_zpow_of_fieldPoint_domain : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), IsPPol A P → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (ζ : Oˣ), IsPrimitiveRoot ζ N → ∀ (m : ℤ) (K : Type) [Field K] (κ : O →+* K), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap κ)) ≫ u) (toUnit (Over.mk (spMap κ)) ≫ v) (unitOn (Units.map κ.toMonoidHom (ζ ^ m))) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom (ζ ^ m))) := by
  first | exact @GlobalTheory.WeilRoot.weilIs_zpow_of_fieldPoint | exact GlobalTheory.WeilRoot.weilIs_zpow_of_fieldPoint | (intros; apply GlobalTheory.WeilRoot.weilIs_zpow_of_fieldPoint <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tautologicalBase_periods_factor_mul_generator : ∀ {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : GlobalTheory.PolDeg.TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → ∀ a b : Q.X, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧ Q.TauCoord a b k := by
  first | exact @GlobalTheory.TautTau.tauCoord_of_dataFrom | exact GlobalTheory.TautTau.tauCoord_of_dataFrom | (intros; apply GlobalTheory.TautTau.tauCoord_of_dataFrom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart


set_option backward.isDefEq.respectTransparency false in
theorem Taut.isRegularLocalRing_and_isRelParam : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → ∀ C : Taut (zetaAway n) g n φ, IsRegularLocalRing C.R ∧ CharZero C.R ∧ Function.Injective C.b ∧ C.b.Flat ∧ IsRelParam C.b C.t ∧ IsRegularLocalRing (C.R ⧸ ((maximalIdeal C.R).comap C.b).map C.b) := by
  intro g n φ _ C
  haveI : IsNoetherianRing C.W := C.noeth
  haveI : IsLocalHom C.iw := C.ψ_loc
  set X := (LowChart.powA C.F C.T.r).left with hX
  set π := LowChart.toO C.F C.T.r with hπ
  set y := C.u (closedPoint C.W) with hy
  let φ₀ : X.presheaf.stalk y →+* C.W := (Scheme.stalkClosedPointTo C.u).hom
  let σ := (π.stalkMap y).hom
  let L := Localization.AtPrime (π y).asIdeal
  let e := Spec.stalkIso (CommRingCat.of (cycAway n)) (π y)
  let ρ : cycAway n →+* X.presheaf.stalk y := σ.comp (e.inv.hom.comp (algebraMap (cycAway n) L))
  have h3 : (Sp (cycAway n)).fromSpecStalk (π y) = Spec.map e.inv ≫ spMap (algebraMap (cycAway n) L) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of _) (π y)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of _) (x := π y)).symm
  have hb : C.T.b = φ₀.comp ρ := by
    have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk C.u
    have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y)
    have key : spMap C.T.b = spMap (φ₀.comp ρ) := by
      rw [← C.u_base, ← h1, Category.assoc, ← h2, h3]
      simp only [spMap, ρ, φ₀, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hq : (π y).asIdeal = (maximalIdeal C.W).comap C.T.b := by
    have : π y = spMap C.T.b (closedPoint C.W) := by
      rw [hy, ← C.u_base, Scheme.Hom.comp_apply]
    rw [this]; rfl
  haveI : IsRegularLocalRing (X.presheaf.stalk y) := LowChart.isRegularLocalRing_stalk C.F y
  have het := C.u_et
  haveI hW : IsRegularLocalRing C.W := by
    letI : Algebra (X.presheaf.stalk y) C.W := φ₀.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y) C.W := het.1
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ (maximalIdeal _) het.2.1.symm
  obtain ⟨hRreg, hRdom⟩ := isRegularLocalRing_and_isDomain_of_isComplAt C.W (Fin C.m ⊕ Fin C.N) C.R C.ψ C.compl C.ψ_loc
  have hρspec : spMap ρ = X.fromSpecStalk y ≫ π := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk π (x := y), h3]
    simp only [spMap, ρ, σ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
  have hflatρ : ρ.Flat := by
    haveI := GlobalTheory.SmoothStalkNormal.flat_fromSpecStalk' X y
    have h : Flat (spMap ρ) := by rw [hρspec]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
  have hiwflat : C.iw.Flat :=
    (show (algebraMap C.W (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W)).Flat from
      RingHom.flat_algebraMap_iff.mpr inferInstance).comp C.compl.2.2.1
  have hbeq : C.b = C.iw.comp (φ₀.comp ρ) := by rw [← hb]; rfl
  have hbflat : C.b.Flat := by rw [hbeq]; exact (hflatρ.comp het.1).comp hiwflat
  have hinj : Function.Injective C.b := GlobalTheory.SmoothStalkNormal.injective_of_flat_of_isDomain C.b hbflat
  have hmW : (maximalIdeal C.R).comap C.iw = maximalIdeal C.W := IsLocalRing.maximalIdeal_comap C.iw
  have h𝔮 : (maximalIdeal C.R).comap C.b = (π y).asIdeal := by
    rw [hq, show C.b = C.iw.comp C.T.b from rfl, ← Ideal.comap_comap, hmW]
  have hle : ((maximalIdeal C.R).comap C.b).map C.b ≤ (maximalIdeal C.W).map (C.ψ.comp MvPolynomial.C) := by
    rw [show C.b = C.iw.comp C.T.b from rfl, ← Ideal.map_map]
    refine Ideal.map_mono (Ideal.map_le_iff_le_comap.2 ?_)
    rw [← Ideal.comap_comap, hmW]
  refine ⟨hRreg, charZero_of_injective_ringHom hinj, hinj, hbflat, ⟨fun k => C.bd k, fun c hc k =>
    cotangent_indep_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc C.m ⟨Sum.inl, Sum.inl_injective⟩ (fun k => C.bd k) c
      (sup_le_sup_left hle (maximalIdeal C.R ^ 2) hc) k⟩, ?_⟩
  have hfib := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal (Sp (cycAway n)) X π y
  set I := (maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y))).map σ with hIdef
  have hI : I = (π y).asIdeal.map ρ := by
    have hsurj : Function.Surjective e.inv.hom := e.commRingCatIsoToRingEquiv.symm.surjective
    have hmL : maximalIdeal ((Sp (cycAway n)).presheaf.stalk (π y)) = (maximalIdeal L).map e.inv.hom :=
      (IsLocalRing.map_maximalIdeal_of_surjective _ hsurj).symm
    rw [hIdef, hmL, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
    rfl
  set 𝔭 := I.map φ₀ with h𝔭def
  have h𝔭 : 𝔭.map C.iw = ((maximalIdeal C.R).comap C.b).map C.b := by
    rw [h𝔭def, hI, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, ← hbeq, h𝔮]
  have hIm : I ≤ maximalIdeal (X.presheaf.stalk y) :=
    Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap σ).ge
  have h𝔭m : 𝔭 ≤ maximalIdeal C.W := het.2.1 ▸ Ideal.map_mono hIm
  have h𝔭ne : 𝔭 ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top h𝔭m
  haveI : Nontrivial (C.W ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.2 h𝔭ne
  haveI : IsLocalRing (C.W ⧸ 𝔭) := IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective
  have hreg𝔭 : IsRegularLocalRing (C.W ⧸ 𝔭) := by
    let χ : (X.presheaf.stalk y ⧸ I) →+* (C.W ⧸ 𝔭) := Ideal.quotientMap 𝔭 φ₀ Ideal.le_comap_map
    have hχflat : χ.Flat := GlobalTheory.Pat.flat_quotientMap_map φ₀ het.1 I
    letI : Algebra (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := χ.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk y ⧸ I) (C.W ⧸ 𝔭) := hχflat
    have hcomm : (Ideal.Quotient.mk 𝔭).comp φ₀ = χ.comp (Ideal.Quotient.mk I) := by
      ext a; simp [χ]
    have hmax : maximalIdeal (C.W ⧸ 𝔭) = (maximalIdeal (X.presheaf.stalk y ⧸ I)).map (algebraMap _ _) := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective, ← het.2.1,
        ← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, Ideal.map_map,
        Ideal.map_map, hcomm]
      rfl
    exact GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal _ _ _ hmax
  have hfin := isRegularLocalRing_quotient_of_isComplAt C.W _ C.R C.ψ C.compl C.ψ_loc 𝔭 h𝔭ne hreg𝔭
  rwa [show C.ψ.comp MvPolynomial.C = C.iw from rfl, h𝔭] at hfin

end GlobalTheory.TChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint : UTraitExtSt := by
  first | exact @GlobalTheory.UTraitExt.uTraitExtSt | exact GlobalTheory.UTraitExt.uTraitExtSt | (intros; apply GlobalTheory.UTraitExt.uTraitExtSt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsionRational_of_retract_galoisFixed_points : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G' ≅ A.A) (inc : G ⟶ G') (pr : G' ⟶ G) (n : ℕ), IsMonHom gen.hom → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → 1 ≤ n → (∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left) → TorsRat G n := by
  first | exact @GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed | exact GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed | (intros; apply GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.TraitUniq

theorem pow_eq_of_associated {W : Type} [CommRing W] [IsDomain W] {w : W} (hw : Irreducible w) {a b : ℕ}
    (h : Associated (w ^ a) (w ^ b)) : a = b := by
  have key : ∀ {a b : ℕ}, Associated (w ^ a) (w ^ b) → a ≤ b → a = b := by
    intro a b h hab
    by_contra hne
    have hlt : 0 < b - a := by omega
    have h1 : Associated (w ^ a * 1) (w ^ a * w ^ (b - a)) := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab]; exact h
    have h2 : Associated 1 (w ^ (b - a)) :=
      Associated.of_mul_left h1 (Associated.refl _) (pow_ne_zero _ hw.ne_zero)
    have h3 : IsUnit (w ^ (b - a)) := associated_one_iff_isUnit.1 h2.symm
    exact hw.not_isUnit ((isUnit_pow_iff hlt.ne').1 h3)
  rcases le_total a b with hab | hab
  · exact key h hab
  · exact (key h.symm hab).symm

theorem sq_associated {V W : Type} [CommRing V] [CommRing W] [IsDomain W] (f : V →+* W) (ϖ : V) (w : W) (m n : ℕ)
    (hm : Associated (f ϖ) (w ^ m)) (v : Wˣ) (u : Vˣ) :
    Associated ((v * f (u * ϖ ^ n)) ^ 2) (w ^ (2 * (m * n))) := by
  have hu : IsUnit (f (u : V)) := (Units.isUnit u).map f
  have e : (v * f (u * ϖ ^ n)) ^ 2 = (((v : W) * f u) ^ 2) * (f ϖ ^ n) ^ 2 := by
    rw [map_mul, map_pow]; ring
  rw [e]
  refine (associated_unit_mul_left _ _ ((v.isUnit.mul hu).pow 2)).trans ?_
  have eq : w ^ (2 * (m * n)) = ((w ^ m) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
  rw [eq]
  exact (hm.pow_pow (n := n)).pow_pow (n := 2)

end GlobalTheory.UPoinc.TraitUniq


open GlobalTheory.UPoinc.TraitUniq in
theorem GlobalTheory.UPoinc.uTraitUniqSt_holds : UTraitUniqSt := by
  intro E _ _ _ H Dw l Xo c T T' W _ _ _ f f' fK fK' hB hW hf hf' hfl hfl' hK hK' hy w m m' hw hm hm'
  obtain ⟨tW, ⟨φ⟩, ⟨φ'⟩⟩ := GlobalTheory.T.exists_common_semiAbelian_pullback_two_unitary_traits E H Dw l Xo c T T' W f f' fK fK' hB hW hf hf' hfl hfl' hK hK' hy
  obtain ⟨PW, e1, he1⟩ := GlobalTheory.T.exists_linear_uniformisation_base_change_complete_dvr E H T.V T.cdvr T.t T.P W hB hW f hf hfl tW ⟨φ⟩
  obtain ⟨PW', e1', he1'⟩ := GlobalTheory.T.exists_linear_uniformisation_base_change_complete_dvr E H T'.V T'.cdvr T'.t T'.P W hB hW f' hf' hfl' tW ⟨φ'⟩
  obtain ⟨e2, he2⟩ := GlobalTheory.T.linear_uniformisations_character_iso_associated_coords E H W hB tW PW PW'
  let e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X := e1.symm.trans (e2.trans e1')

  have diag : ∀ y, (m : ℤ) * T.be y y = m' * T'.be (e y) (e y) := by
    intro y
    obtain ⟨u, n, hn, hc⟩ := T.mono y
    obtain ⟨u', n', hn', hc'⟩ := T'.mono (e y)
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one] at hn hc hn' hc'
    have hc1 : PsiCoord T.P.D.toPre (e1 (e1.symm y)) (u * T.ϖ ^ n 0) := by
      rw [LinearEquiv.apply_symm_apply]; exact hc
    obtain ⟨v, hv⟩ := he1 _ _ hc1
    obtain ⟨v', hv'⟩ := he1' (e2 (e1.symm y)) _ hc'
    have ha := he2 _ _ _ hv hv'
    have h1 := sq_associated f T.ϖ w m (n 0) hm v u
    have h2 := sq_associated f' T'.ϖ w m' (n' 0) hm' v' u'
    have := pow_eq_of_associated hw (h1.symm.trans (ha.trans h2))
    rw [hn 0, hn' 0]
    have : ((2 * (m * n 0) : ℕ) : ℤ) = ((2 * (m' * n' 0) : ℕ) : ℤ) := by rw [this]
    push_cast at this
    linarith
  have hs : ∀ a b, T.be a b = T.be b a := fun a b => (mem_levelForms.1 T.lev).1 a b
  have hs' : ∀ a b, T'.be a b = T'.be b a := fun a b => (mem_levelForms.1 T'.lev).1 a b
  refine ⟨e, fun a b => ?_⟩
  have h := diag (a + b)
  simp only [map_add (f := _), LinearMap.add_apply] at h
  have ha := diag a
  have hb := diag b
  rw [hs b a, hs' (e b) (e a)] at h
  linarith
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LabMove

theorem exists_mulEquiv_points {S K K' X : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over K} [GrpObj A] {A' : Over K'}
    [GrpObj A'] {g : K ⟶ S} {g' : K' ⟶ S} {α : A.left ⟶ G.left} {α' : A'.left ⟶ G.left}
    (h : IsGrpPullback A G g α) (h' : IsGrpPullback A' G g' α') (t : X ⟶ K) (t' : X ⟶ K')
    (f : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left)
    (hf₁ : f ≫ (fst (Over.mk t) A).left = (fst (Over.mk t') A').left)
    (hf₂ : f ≫ (snd (Over.mk t) A).left ≫ α = (snd (Over.mk t') A').left ≫ α') :
    ∃ e : (Over.mk t' ⟶ A') ≃* (Over.mk t ⟶ A), ∀ x', (e x').left ≫ α = x'.left ≫ α' ∧
      (ptSecT A' x').left ≫ f = (ptSecT A (e x')).left := by
  have s₁ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (fst T Y).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have s₂ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (snd T Y).left = x.left := fun x => by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have w : (snd (Over.mk t) A).left ≫ A.hom = (fst (Over.mk t) A).left ≫ t :=
    (Over.w (snd (Over.mk t) A)).trans (Over.w (fst (Over.mk t) A)).symm
  have w' : (snd (Over.mk t') A').left ≫ A'.hom = (fst (Over.mk t') A').left ≫ t' :=
    (Over.w (snd (Over.mk t') A')).trans (Over.w (fst (Over.mk t') A')).symm
  have hu : t' ≫ g' = t ≫ g := by
    have e := congrArg (fun q => (ptSecT A' (1 : Over.mk t' ⟶ A')).left ≫ q ≫ G.hom) hf₂
    simp only [Category.assoc] at e
    rw [h.1.w, h'.1.w, reassoc_of% w, reassoc_of% w', reassoc_of% hf₁, reassoc_of% (s₁ (1 : Over.mk t' ⟶ A')),
      reassoc_of% (s₁ (1 : Over.mk t' ⟶ A'))] at e
    exact e.symm
  obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h t (t ≫ g) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h' t' (t ≫ g) hu
  have key : ∀ x', ((e'.trans e.symm) x').left ≫ α = x'.left ≫ α' := fun x' => by
    rw [← he, ← he', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  refine ⟨e'.trans e.symm, fun x' => ⟨key x', ?_⟩⟩
  have a₁ : ((ptSecT A' x').left ≫ f) ≫ (fst (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (fst (Over.mk t) A).left := by
    rw [Category.assoc, hf₁, s₁, s₁]; rfl
  have a₂ : ((ptSecT A' x').left ≫ f) ≫ (snd (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (snd (Over.mk t) A).left := by
    refine h.1.hom_ext ?_ ?_
    · rw [s₂, key, Category.assoc, Category.assoc, hf₂, reassoc_of% (s₂ x')]
    · rw [Category.assoc, w, Category.assoc _ _ A.hom, w, ← Category.assoc, a₁, Category.assoc]
  exact pullback.hom_ext a₁ a₂

end GlobalTheory.Mum.LabMove

namespace GlobalTheory.Mum

theorem Trait.exists_lab_push : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → (∀ x : TFK (R := W) F ⟶ T.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p', lab' p' = x) → ∃ lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A), LabExt em (C.lab j) lab ∧ (∀ x : TFK (R := R) F ⟶ C.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p, lab p = x) ∧ ∀ (p : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), p'.y = T.hD.xe.symm p.y → IsPullGtF T.φ T.hD F p.g p'.g → (ptSecT T.A.A (lab' p')).left ≫ f = (ptSecT C.A.A (lab p)).left := by
  intro R _ _ _ _ D C j W _ _ _ T F _ _ _ _ em hF f _ hf₁ hf₂ lab' hext honto
  have := T.U.gen_hom
  have : IsMonHom T.U.gen.symm.hom := by show IsMonHom T.U.gen.inv; infer_instance
  have gT : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ) (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) :=
    ((isGrpPullback_of_iso T.U.gen.symm).comp ((isGrpPullback_pullback T.G (jK W)).comp T.cart)).congr
      (Category.id_comp _) rfl
  obtain ⟨e, he⟩ := LabMove.exists_mulEquiv_points C.α_cart gT (jFK (R := R) F) (jFK (R := W) F) f hf₁ hf₂
  let P : QkPt D.toPre F (C.n ^ j) → QkPt T.D'.toPre F (C.n ^ j) :=
    GlobalTheory.ArcPull.pullQk T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hP : ∀ p p', p' = P p ↔ p'.y = T.hD.xe.symm p.y ∧ IsPullGtF T.φ T.hD F p.g p'.g :=
    GlobalTheory.ArcPull.eq_pullQk_iff T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hs : Function.Surjective P :=
    GlobalTheory.ArcPull.pullQk_surjective T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  refine ⟨fun p => e (lab' (P p)), fun p p₁ hp => ?_, fun x => ?_, fun p p' hy hg => ?_⟩
  · refine C.α_cart.1.hom_ext ?_ ?_
    · rw [Category.assoc]
      exact (he _).1.trans (hext p p₁ (P p₁) hp ((hP _ _).1 rfl).1 ((hP _ _).1 rfl).2)
    · rw [Category.assoc, Over.w, Over.w]
      simp only [TFK, Over.mk_hom, jFK]
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp
  · obtain ⟨x', rfl⟩ := e.surjective x
    rw [← map_pow, MulEquiv.map_eq_one_iff, honto, hs.exists]
    exact exists_congr fun p => e.injective.eq_iff.symm
  · obtain rfl := (hP p p').2 ⟨hy, hg⟩
    exact (he _).2

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU

noncomputable section

namespace GlobalTheory.Mum

theorem eqv_eq_smul : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ lab E E', Eqv D.toPre A F N lab E → Eqv D.toPre A F N lab E' → ∃ c : Fˣ, ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ _ I D A F _ _ _ N hN lab E E' hE hE'
  have hN1 : 1 ≤ N := hN.pos
  have hNF : (N : F) ≠ 0 := by
    have h1 : (N : R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : (N : FractionRing R) ≠ 0 := fun h =>
      h1 (IsFractionRing.injective R (FractionRing R) (by rw [map_natCast, map_zero]; exact h))
    intro h
    apply h2
    apply (algebraMap (FractionRing R) F).injective
    rw [map_zero, map_natCast]
    exact_mod_cast h
  let p : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing R)) := jFK (R := R) F
  let mkE : ∀ G : Fam D.toPre F N → SecK A.L (snd (TFK (R := R) F) A.A).left N, Eqv D.toPre A F N lab G →
      (Fam D.toPre F N →ₗ[F] EA A p N) := fun G hG =>
    { toFun := fun s => SecMod.mk _ (G s)
      map_add' := fun s t => DVR.SecOps.sec_ext fun j => hG.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => DVR.SecOps.sec_ext fun j =>
        hG.smul c s (c • s) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff c s _).2 rfl) j }
  have hbij : ∀ G hG, Function.Bijective (mkE G hG) := fun G hG => hG.bij
  let e := LinearEquiv.ofBijective (mkE E hE) (hbij E hE)
  let T : EA A p N →ₗ[F] EA A p N := (mkE E' hE').comp e.symm.toLinearMap
  have hTe : ∀ s, T (mkE E hE s) = mkE E' hE' s := fun s => by
    show mkE E' hE' (e.symm (e s)) = _
    rw [e.symm_apply_apply]
  obtain ⟨ρ, hact, -, -, -⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns _ A (N : ℤ) (TFK (R := R) F)
  have huniq : ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (a : EA A p N) (b b' : SecK A.L (snd (TFK (R := R) F) A.A).left N),
      IsActOf A.A A.L (N : ℤ) θ a.sec b → IsActOf A.A A.L (N : ℤ) θ a.sec b' → b = b' := fun θ a b b' h h' => by
    have := ((hact θ _ _).1 h).symm.trans ((hact θ _ _).1 h')
    exact DVR.SecOps.sec_ext fun j => congrFun (congrArg Subtype.val this) j
  have hT : ∀ x : Over.mk p ⟶ A.A, x ^ N = 1 → ∃ θ : ThetaGrp A.A A.L (N : ℤ) (Over.mk p), θ.pt = x ∧
      ∀ v v' : EA A p N, IsActOf A.A A.L (N : ℤ) θ v.sec v'.sec →
        IsActOf A.A A.L (N : ℤ) θ (T v).sec (T v').sec := by
    intro x hx
    obtain ⟨p₀, hp₀⟩ := (hE.onto x).1 hx
    obtain ⟨w, hw⟩ := hE.frame p₀
    obtain ⟨θ, hθ⟩ := hE.lift p₀
    obtain ⟨Φ, hΦ⟩ := ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of GlobalTheory.allSixLaws.1 R I D F N hN1 p₀ w hw.1
    refine ⟨θ, hθ.pt_eq.trans hp₀, fun v v' hvv => ?_⟩
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have hPhi := (hΦ s (Φ s)).2 rfl
    have h₁ := hE.act p₀ w θ s (Φ s) hw hθ hPhi
    have h₂ := hE'.act p₀ w θ s (Φ s) hw hθ hPhi
    have e₁ : v' = mkE E hE (Φ s) := huniq θ _ _ _ hvv h₁
    rw [e₁, hTe, hTe]
    exact h₂
  obtain ⟨c, hc⟩ := GlobalTheory.ThetaCommutant.eq_smul_of_commute A F p N hNF T hT
  have hpos : 0 < Module.finrank F (EA A p N) := by
    rw [GlobalTheory.ThetaCommutant.finrank_eq A F p N hNF]; positivity
  have : Nontrivial (EA A p N) := Module.nontrivial_of_finrank_pos hpos
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : EA A p N)
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have h0 : mkE E' hE' s = mkE E' hE' 0 := by rw [← hTe, hc, zero_smul, map_zero]
    have := (hbij E' hE').1 h0
    subst this
    exact hv (map_zero _)
  refine ⟨Units.mk0 c hc0, fun s j => ?_⟩
  have h := congrArg (fun v : EA A p N => v.sec.f j) ((hTe s).symm.trans (hc _))
  exact h

end GlobalTheory.Mum
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Nat.card {x : A.Pt // x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} = l ^ padicValNat l (deg f) := by
  first | (exact @GlobalTheory.AV.AbVar.card_kerLPart_eq) | (exact GlobalTheory.AV.AbVar.card_kerLPart_eq) | (intros; apply GlobalTheory.AV.AbVar.card_kerLPart_eq  <;> assumption)
end
