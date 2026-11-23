module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSysGlobalModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle155
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle210
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedThetaSectionNonzeroEveryFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle006
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfUnimodular

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.CombW

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}

theorem firstChernFormOfWeight_eq_hessianForm_chart {L : LB X.X} (ψ : Weight X.str σ L) (hψ : ψ.IsCInf) (c : AlgChart X.str σ X.dim)
    {y : CxPts X.str σ} (hy : y ∈ c.e.source) :
    c1W ψ ⟨(c, y), hy⟩ = GlobalTheory.ChernTop.matForm X.dim (c.hess ψ (pick ψ.isLB y) y) := by
  have hd := hψ.contDiffAt c hy (mem_pick ψ.isLB y)
  change ofValues _ = kappa • ∑ a, GlobalTheory.ChernTop.rowForm a _
  simp only [ofValues, GlobalTheory.ChernTop.rowForm, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact congrArg (kappa * ·) (GlobalTheory.CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd) a b).symm

theorem firstChernFormOfWeight_tensor {A B : LB X.X} (ψ : Weight X.str σ A) (φ : Weight X.str σ B) (hψ : ψ.IsCInf) (hφ : φ.IsCInf) :
    c1W (ψ.tens φ) = c1W ψ + c1W φ := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have ha := mem_pick ψ.isLB y
  have hb := mem_pick φ.isLB y
  show c1W (ψ.tens φ) ⟨(c, y), hy⟩ = c1W ψ ⟨(c, y), hy⟩ + c1W φ ⟨(c, y), hy⟩
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ (hψ.tens hφ) c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hψ c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hφ c hy,
    c.hess_eq (hψ.tens hφ) hy (i := (pick ψ.isLB y, pick φ.isLB y)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y),
    GlobalTheory.FlatMass.hess_tens hψ hφ hy ha hb, map_add]

theorem firstChernFormOfWeight_dual {B : LB X.X} (φ : Weight X.str σ B) (hφ : φ.IsCInf) :
    c1W φ.dual = -c1W φ := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have hb := mem_pick φ.isLB y
  show c1W φ.dual ⟨(c, y), hy⟩ = -c1W φ ⟨(c, y), hy⟩
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ hφ.dual c hy, firstChernFormOfWeight_eq_hessianForm_chart _ hφ c hy,
    c.hess_eq hφ.dual hy (i := (pick φ.isLB y : B.ι)) hb (mem_pick _ y),
    GlobalTheory.FlatMass.hess_dual hφ hy hb, map_neg]

theorem firstChernFormOfWeight_trivial_zero : c1W (Weight.ofFun (p := X.str) (σ := σ) fun _ => 0) = 0 := by
  funext x
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have h0 : (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)).IsCInf := Weight.isCInf_ofFun (cInfAt_const 0)
  show c1W _ ⟨(c, y), hy⟩ = 0
  rw [firstChernFormOfWeight_eq_hessianForm_chart _ h0 c hy]
  have e : c.hess (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)) (pick (Weight.ofFun (p := X.str) (σ := σ) fun _ => (0:ℝ)).isLB y) y = 0 :=
    GlobalTheory.FlatMass.cHess_zero _
  rw [e, map_zero]

def combSub (X : Var F) (σ : F →+* ℂ) : AddSubgroup (X.Dv × ((atlas X σ).Pt → Ev X.dim)) where
  carrier := {x | ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'),
    Presents x.1 L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = x.2}
  zero_mem' := ⟨LB.triv X.X, fun _ => 1, Weight.ofFun fun _ => 0, presents_zero,
    Weight.isCInf_ofFun (cInfAt_const 0), firstChernFormOfWeight_trivial_zero⟩
  add_mem' := by
    rintro ⟨D, w⟩ ⟨E, u⟩ ⟨L, r, ψ, h1, h2, h3⟩ ⟨M, r', φ, h1', h2', h3'⟩
    exact ⟨_, _, ψ.tens φ, h1.tens h1', h2.tens h2', by rw [firstChernFormOfWeight_tensor _ _ h2 h2', h3, h3']; rfl⟩
  neg_mem' := by
    rintro ⟨D, w⟩ ⟨L, r, ψ, h1, h2, h3⟩
    have hdual : Presents (-D) (CechPic.dual L) (fun i => (r i)⁻¹) := by
      refine ⟨CechPic.isLB_dual h1.isLB, fun i j hij => ?_, fun i x hx => (h1.isEqn i x hx).neg⟩
      change (↑((r i)⁻¹) : X.Fn) =
        fnOf (L.U i ⊓ L.U j) hij ↑((L.g i j)⁻¹) * ↑((r j)⁻¹)
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv,
        h1.isRatSec i j hij, mul_inv]
    exact ⟨_, _, ψ.dual, hdual, h2.dual, by rw [firstChernFormOfWeight_dual _ h2, h3]; rfl⟩

end GlobalTheory.ChernCalc.CombW

open GlobalTheory.ChernCalc.CombW in
theorem GlobalTheory.ChernCalc.exists_comb_smoothWeight : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ c : κ → ℤ, ∃ (L' : LB X.X) (r' : L'.ι → X.Fnˣ) (ψ' : Weight X.str σ L'), Presents (∑ a, c a • Δ a) L' r' ∧ ψ'.IsCInf ∧ c1W ψ' = ∑ a, (c a : ℂ) • c1W (ψ a) := by
  intro F _ σ X κ _ Δ L r ψ h c
  have hm : (∑ a, c a • ((Δ a, c1W (ψ a)) : X.Dv × ((atlas X σ).Pt → Ev X.dim))) ∈ combSub X σ :=
    AddSubgroup.sum_mem _ fun a _ => AddSubgroup.zsmul_mem _ (show ((Δ a, c1W (ψ a)) : X.Dv × ((atlas X σ).Pt → Ev X.dim)) ∈ combSub X σ from ⟨L a, r a, ψ a, (h a).1, (h a).2, rfl⟩) _
  obtain ⟨L', r', ψ', h1, h2, h3⟩ := hm
  refine ⟨L', r', ψ', ?_, h2, ?_⟩
  · simpa [Prod.fst_sum] using h1
  · rw [h3, Prod.snd_sum]
    simp only [Prod.smul_snd]
    exact Finset.sum_congr rfl fun a _ => (Int.cast_smul_eq_zsmul ℂ (c a) _).symm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitSemi

theorem spMap_comp'' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem exists_int_map (F : Type) [Field F] [NumberField F] (V : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    (g : F →+* FractionRing V) :
    ∃ oV : 𝓞 F →+* V, (algebraMap V (FractionRing V)).comp oV = g.comp (algebraMap (𝓞 F) F) := by
  have hint : ∀ a : 𝓞 F, ∃ r : V, algebraMap V (FractionRing V) r = g a := fun a => by
    have h2 : IsIntegral V (g a) := by
      obtain ⟨p, hp, h0⟩ := RingOfIntegers.isIntegral_coe a
      refine ⟨p.map (Int.castRingHom V), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap V (FractionRing V)).comp (Int.castRingHom V))
        (g.comp (algebraMap ℤ F)), ← Polynomial.hom_eval₂, h0, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.1 h2
  choose f hf using hint
  have hi := IsFractionRing.injective V (FractionRing V)
  let b : 𝓞 F →+* V :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun _ _ => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun _ _ => hi (by simp [hf]) }
  refine ⟨b, ?_⟩
  ext a
  exact hf a

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_genOf_of_model {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V]
    (y : Sp (FractionRing V) ⟶ Xo.XF c) : ∃ t : SAB H (Sp V), GenOf Xo c y t := by
  obtain ⟨g, hg⟩ := GlobalTheory.Models.RankZero.exists_spMap (y ≫ pullback.snd _ _)
  obtain ⟨oV, hoV⟩ := exists_int_map c.F V g
  obtain ⟨⟨yt, ⟨-, hyt⟩, -⟩, hG⟩ :=
    GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c (𝓞 c.F) _ Y V (FractionRing V) oV g y hoV hg
  obtain ⟨G, ⟨m⟩⟩ := hG yt
  obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, n₁, -⟩ := sabPull Out.CubePf.cubePull y Y.oF.t
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m n₁
  have hy' : y ≫ Y.jQ ≫ pullback.fst _ _ = jK V ≫ yt := hyt.symm
  rw [hy'] at b
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap n₁
  exact ⟨G, _, ⟨mK⟩, ⟨mx⟩⟩

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_finite_point' {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (K : Type) [Field K] (x : Sp K ⟶ Y)
    (hx : x (closedPoint K) ∈ Set.range π) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (η : Sp L ⟶ X),
      η ≫ π = spMap (algebraMap K L) ≫ x := by
  obtain ⟨p, hp⟩ := hx
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := S) (e.hom ≫ pullback.snd π x)
  letI : Algebra K S := f.hom.toAlgebra
  have hsp : spMap (algebraMap K S) = e.hom ≫ pullback.snd π x := hf
  have hfin : Module.Finite K S := by
    have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (closedPoint K) hp
  haveI : Nontrivial S := (e.inv z).nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (S ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  refine ⟨S ⧸ m, inferInstance, inferInstance, inferInstance, spMap (Ideal.Quotient.mk m) ≫ e.hom ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, ← hsp, ← Category.assoc, spMap_comp'']

theorem exists_closure_finite (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (L : Type) [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] :
    ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsLocalRing V₂) (j : V →+* V₂) (e : L →+* FractionRing V₂),
      GlobalTheory.Mum.Base V₂ ∧ IsDiscreteValuationRing V₂ ∧ Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧
        ∀ a : V, e (algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a)) =
          algebraMap V₂ (FractionRing V₂) (j a) := by
  letI : Algebra V L := ((algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite V (integralClosure V L) := GlobalTheory.FormalIsogeny.finite_integralClosure V (FractionRing V) L
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful V (FractionRing V) L
  haveI hloc : IsLocalRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalRing V L
  haveI hdvr : IsDiscreteValuationRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) L
  haveI : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension (FractionRing V) L
  have hj := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj V L
  haveI : CharZero (integralClosure V L) := charZero_of_injective_algebraMap hj
  refine ⟨integralClosure V L, inferInstance, inferInstance, hloc, algebraMap V (integralClosure V L),
    (FractionRing.algEquiv (integralClosure V L) L).symm.toRingEquiv.toRingHom,
    ⟨⟨inferInstance, inferInstance, inferInstance,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V (integralClosure V L)⟩, inferInstance⟩,
    hdvr, hj, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom V L, RingHom.finite_algebraMap.2 inferInstance, fun a => ?_⟩
  have h1 : algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a) =
      algebraMap (integralClosure V L) L (algebraMap V (integralClosure V L) a) := rfl
  rw [h1]
  exact (FractionRing.algEquiv (integralClosure V L) L).symm.commutes _

theorem finite_surjective_spMap {F F' : IntermediateField ℚ ℂ} [FiniteDimensional ℚ F'] (h : F ≤ F') :
    IsFinite (spMap (IntermediateField.inclusion h).toRingHom) ∧
      Surjective (spMap (IntermediateField.inclusion h).toRingHom) := by
  have hq : (algebraMap ℚ F').Finite := RingHom.finite_algebraMap.2 inferInstance
  have he : algebraMap ℚ F' = (IntermediateField.inclusion h).toRingHom.comp (algebraMap ℚ F) := Subsingleton.elim _ _
  rw [he] at hq
  refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_comp_finite hq), ⟨fun x => ?_⟩⟩
  refine ⟨closedPoint F', Subsingleton.elim _ _⟩

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_rankZero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (hD : Dw.p + Dw.q = 0) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (hB : GlobalTheory.Mum.Base V) (hV : IsDiscreteValuationRing V) (y : Sp (FractionRing V) ⟶ Xo.XF c) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
      (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  have hz := (GlobalTheory.Models.RankZero.isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo).2
  refine ⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V, RingHom.id _, ⟨hV, hB.1.2.2.2, hB.2⟩,
    Function.injective_id, inferInstance, RingHom.Finite.id V, fun a => rfl, Inhab.zeroTriple H _,
    Inhab.zeroTriple H _, GlobalTheory.Models.RankZero.nonempty_sabMap (GlobalTheory.Models.RankZero.isIso_zeroTriple _)
      (GlobalTheory.Models.RankZero.isIso_zeroTriple _) _,
    GlobalTheory.Models.RankZero.nonempty_sabMap (GlobalTheory.Models.RankZero.isIso_zeroTriple _) hz _⟩

theorem exists_pos {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (hD : 1 ≤ Dw.p + Dw.q) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (hB : GlobalTheory.Mum.Base V) (hV : IsDiscreteValuationRing V) (y : Sp (FractionRing V) ⟶ Xo.XF c) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
      (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  haveI := c.fin
  obtain ⟨l₂, hdvd, -, hgood⟩ := GlobalTheory.GoodMultipleLevel.exists_good_multiple E H l
  obtain ⟨c₂, hle⟩ := GlobalTheory.TupleCover.exists_coeff_ge l₂ c.F
  haveI := c₂.fin
  let Xf : ∀ l' : Geo.Tor.Level H, Moduli Dw l' := fun l' => (GlobalTheory.moduliScheme_levelMaps_heckePoints.1 E H Dw l' hD).some
  obtain ⟨s, hs⟩ := GlobalTheory.GlobalAllLevels.exists_sys_global_models E H Dw hD Xf
  obtain ⟨Ygl, -⟩ := hs l₂ c₂ hgood
  obtain ⟨r, h, r₀, m, hr, hfin, -, hsurj⟩ :=
    GlobalTheory.LevelMapBase.levelMap_coeff_le E H Dw l l₂ Xo (Xf l₂) c c₂ hle hD hdvd
  obtain ⟨hF, hS⟩ := finite_surjective_spMap hle
  have hrl : pullback.lift r _ h ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  haveI : IsFinite r := hrl ▸ inferInstance
  have hrs : Surjective r := hrl ▸ inferInstance
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point' r (FractionRing V) y (hrs.surj _)
  haveI : IsAdicComplete (maximalIdeal V) V := hB.1.2.2.2
  haveI : CharZero V := hB.2
  obtain ⟨V₁, _, _, _, j, e, hB₁, hD₁, hj, hjl, hjf, he⟩ := exists_closure_finite V L
  obtain ⟨t, tK, ⟨mK⟩, ⟨mx⟩⟩ := exists_genOf_of_model Ygl V₁ (spMap e ≫ η)
  obtain ⟨mx', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m mx
  have key : ((spMap e ≫ η) ≫ pullback.fst _ _) ≫ r₀ =
      (spMap (e.comp (algebraMap (FractionRing V) L)) ≫ y) ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, ← hr, ← Category.assoc η, hη, ← spMap_comp'']
    simp only [Category.assoc]
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, j, e.comp (algebraMap (FractionRing V) L),
    ⟨hD₁, hB₁.1.2.2.2, hB₁.2⟩, hj, hjl, hjf, fun a => he a, t, tK, ⟨mK⟩, ⟨?_⟩⟩
  rw [key] at mx'
  exact mx'

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_ext_semi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hB hV y
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · exact exists_rankZero H Dw hD l Xo c V hB hV y
  · exact exists_pos H Dw hD l Xo c V hB hV y

end GlobalTheory.TraitSemi
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValThru (Xo : Moduli D l) (c : Coeff l) {S T : Scheme.{0}} (i : Xo.XF c ⟶ T) (π : S ⟶ T) (A : Set S)
    (φ : InvFun (𝓞 E)) (J : S.IdealSheafData) (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ i = jK W ≫ χ ≫ π → χ (closedPoint W) ∈ A →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

variable {Xo : Moduli D l} {c : Coeff l}

theorem uValThru_top_of_disjoint {S : Scheme.{0}} {i : Xo.XF c ⟶ S} {A : Set S} (hA : IsOpen A)
    (hd : A ∩ Set.range i = ∅) (φ : InvFun (𝓞 E)) (d : ℕ) : UValThru Xo c i (𝟙 S) A φ ⊤ d := by
  intro W _ _ _ _ ϖ _ χ y hy hA' _ _ _ _ _ _ _ _
  exfalso
  let g : Sp (FractionRing W) := closedPoint (FractionRing W)
  have hsp : (jK W) g ⤳ closedPoint W := IsLocalRing.specializes_closedPoint _
  have hmem : χ ((jK W) g) ∈ A := (hsp.map χ.continuous).mem_open hA hA'
  have hrange : χ ((jK W) g) ∈ Set.range i := ⟨y g, by
    have := congrArg (fun f => f.base g) hy
    simpa using this⟩
  have : χ ((jK W) g) ∈ A ∩ Set.range i := ⟨hmem, hrange⟩
  rw [hd] at this
  exact this

theorem exists_uValOn_of_pieces {S : Scheme.{0}} (i : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) {ι : Type} [Fintype ι]
    (A : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ) (huniq : ∀ x, ∃! k, x ∈ A k) (hd : ∀ k, 1 ≤ d k)
    (hsupp : ∀ k, ∀ x ∈ (J k).support, x ∈ A k ∧ x ∉ Set.range i)
    (hv : ∀ k, UValThru Xo c i (𝟙 S) (A k) φ (J k) (d k)) :
    ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J' d' := by
  have hdvd : ∀ k, d k ∣ ∏ k, d k := fun k => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ k)
  have htop : ∀ k x, x ∉ A k → FinalTheorems.stalkId (J k) x = ⊤ := fun k x hx =>
    GlobalTheory.Vanishing.stalkId_eq_top (J k) fun hs => hx (hsupp k x hs).1
  refine ⟨∏ k, d k, ∏ k, J k ^ ((∏ k, d k) / d k), ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => by have := hd k; omega)
  · intro x hx
    obtain ⟨k, hk, -⟩ := huniq x
    by_cases hs : x ∈ (J k).support
    · exact (hsupp k x hs).2
    · exfalso
      refine (mem_support_iff_stalkId _ x).1 hx ?_
      rw [stalkId_prodPow, ← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun k' _ => ?_
      by_cases e : k' = k
      · subst e; rw [GlobalTheory.Vanishing.stalkId_eq_top (J k') hs, ← Ideal.one_eq_top, one_pow]
      · rw [htop k' x fun h => e ((huniq x).unique h hk), ← Ideal.one_eq_top, one_pow]
  · intro W _ _ _ hW ϖ hϖ χ y hy t tK h1 h2 P be hbe hmono
    obtain ⟨k, hk, -⟩ := huniq (χ (closedPoint W))
    obtain ⟨a, ha, hJ⟩ := hv k W hW ϖ hϖ χ y (by rw [Category.comp_id]; exact hy) hk t tK h1 h2 P be hbe hmono
    refine ⟨(∏ k, d k) / d k * a, ?_, ?_⟩
    · have hd0 : (d k : ℝ) ≠ 0 := by have := hd k; positivity
      rw [Nat.cast_mul, Nat.cast_div (hdvd k) hd0, ha]
      field_simp
    · unfold idlAlong at hJ ⊢
      rw [stalkId_prodPow, Finset.prod_eq_single k, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
      · intro k' _ e
        rw [htop k' _ fun h => e ((huniq _).unique h hk), ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.UPoinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

theorem exists_sharpOver_connected {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) {S : Scheme.{0}} [ConnectedSpace S] (u : S ⟶ F.X) : ∃ P : PolAV S, SharpOver F W P u := by
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := GlobalTheory.LowChart.siegPull F.univ u (u ≫ F.s) rfl
  have hpb : SiegPB c F.univ u := GlobalTheory.LowChart.siegPB_siegPull F.univ u _ rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ u _ rfl F.princ
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim_of_connected c.A c.ab
  obtain ⟨G, _, pr, hA, hdim, hpr, hu⟩ := GlobalTheory.EighthPower.exists_power c.A c.ab hd 8
  have hb := GlobalTheory.EighthPower.isSymBilin hG c hc.1
  have hL : (GlobalTheory.MatrixBundle.matLB c.P pr W).IsLB := LB.isLB_linComb c.isLB _ _
  refine ⟨{ A := G, isAb := hA, g := 8 * d, smoothDim := hdim, L := GlobalTheory.MatrixBundle.matLB c.P pr W, isLB := hL
            rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb hpr, sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb hpr
            ample := _root_.GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG _ _ 8 _ _ _ _ c G pr W hpr hu hc.1 hW.1
            ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb hpr hu hW.2 hc.2 }, c, hpb, pr, hpr, hu, ?_⟩
  exact PolBaseChange.lbIso_refl hL

theorem exists_sharpOver_domain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (R : Type) [CommRing R] [IsDomain R] (u : Sp R ⟶ F.X), ∃ P : PolAV (Sp R), SharpOver F W P u := by
  intro g n F W hW R _ _ u
  haveI : ConnectedSpace (Sp R) := by
    change ConnectedSpace (PrimeSpectrum R)
    infer_instance
  exact exists_sharpOver_connected F W hW u

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.exists_glued_thetaSection_nonzero_every_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → ZM.SecCoord δ t M.pt S.th → (∀ a, ∀ z ∈ nonzeroLocus (t a), a ∈ S.supI M z) → ∃ σ : (CechPic.tens Zh.L.L (δ.pull Zh.G.hom)).Sec, NzFib σ := by
  first | exact @GlobalTheory.KeyTheta.exists_nzFib | exact GlobalTheory.KeyTheta.exists_nzFib | (intros; apply GlobalTheory.KeyTheta.exists_nzFib <;> assumption)
end
