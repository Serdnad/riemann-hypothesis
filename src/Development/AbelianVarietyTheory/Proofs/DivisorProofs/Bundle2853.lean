module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_integralClosure_isCN_finite_local : ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀], IsCN V₀ → ∀ (L : Type) [Field L] [Algebra (FractionRing V₀) L] [FiniteDimensional (FractionRing V₀) L], ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V₀ →+* V₁) (σ : L →+* FractionRing V₁), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ x : V₀, σ (algebraMap (FractionRing V₀) L (algebraMap V₀ (FractionRing V₀) x)) = algebraMap V₁ (FractionRing V₁) (ρ x) := by
  intro V₀ _ _ _ hV L _ _ _
  obtain ⟨hN, hIC, hC, hCZ⟩ := hV
  haveI := hN
  haveI := hIC
  haveI := hC
  haveI := hCZ
  let K₀ := FractionRing V₀
  letI : Algebra V₀ L := ((algebraMap K₀ L).comp (algebraMap V₀ K₀)).toAlgebra
  haveI : IsScalarTower V₀ K₀ L := .of_algebraMap_eq fun _ => rfl
  haveI : CharZero K₀ := IsFractionRing.charZero_of_isFractionRing V₀
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K₀ L).injective
  haveI : Algebra.IsSeparable K₀ L := inferInstance
  let V₁ := integralClosure V₀ L
  haveI : Module.Finite V₀ V₁ := IsIntegralClosure.finite V₀ K₀ L V₁
  haveI hN₁ : IsNoetherianRing V₁ := IsIntegralClosure.isNoetherianRing V₀ K₀ L V₁
  haveI : IsFractionRing V₁ L := IsIntegralClosure.isFractionRing_of_finite_extension V₀ K₀ L V₁
  haveI : IsIntegrallyClosed V₁ := integralClosure.isIntegrallyClosedOfFiniteExtension K₀
  haveI : HenselianLocalRing V₀ := GlobalTheory.henselianLocalRing_of_isAdicComplete V₀
  haveI : IsLocalRing V₁ := GlobalTheory.TameKummer.isLocalRing_of_finite V₀ V₁
  have hinj : Function.Injective (algebraMap V₀ V₁) := by
    intro a b h
    have h' := congrArg (algebraMap V₁ L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply V₀ K₀ L, IsScalarTower.algebraMap_apply V₀ K₀ L b] at h'
    exact IsFractionRing.injective V₀ K₀ ((algebraMap K₀ L).injective h')
  haveI : CharZero V₁ := charZero_of_injective_algebraMap hinj
  haveI : IsLocalHom (algebraMap V₀ V₁) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : (maximalIdeal V₁).comap (algebraMap V₀ V₁) = maximalIdeal V₀ :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V₀) (maximalIdeal V₁))
    have hmem : a ∈ (maximalIdeal V₁).comap (algebraMap V₀ V₁) := by
      rw [hm]; exact hna
    exact hmem ha
  have hcompl : IsAdicComplete (maximalIdeal V₁) V₁ :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V₀ V₁
  let e : L ≃ₐ[V₁] FractionRing V₁ := IsLocalization.algEquiv (nonZeroDivisors V₁) L (FractionRing V₁)
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, algebraMap V₀ V₁, e.toRingEquiv.toRingHom,
    ⟨hN₁, inferInstance, hcompl, inferInstance⟩, hinj, RingHom.finite_algebraMap.mpr inferInstance,
    inferInstance, fun x => ?_⟩
  have hx : algebraMap K₀ L (algebraMap V₀ K₀ x) = algebraMap V₁ L (algebraMap V₀ V₁ x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  rw [hx, AlgEquiv.commutes]

end GlobalTheory.Poinc
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem torsion_lies_under : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V →
    ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N →
      ∀ β : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A, β ^ N = 1 →
      ∃ xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, xb ^ N = 1 ∧
        (∃ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 ∧
          QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb) ∧
        ∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 →
          QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → p.g.b = β := by
  intro V _ _ _ hCN D A G _ _ hG U N hN β hβ
  haveI : CharZero V := hCN.2.2.2
  have hA := GlobalTheory.TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA D A G hG U
    (AlgebraicClosure (FractionRing V)) N hN
  obtain ⟨p, hpy, hpb⟩ := GlobalTheory.TorusExt.exists_qkPt_of_torsion (F := AlgebraicClosure (FractionRing V))
    D.tau_bimult (n := N) (by omega) hβ
  refine ⟨f p, ?_, ⟨p, hpy, (hf.1 p (f p)).2 rfl⟩, fun p' hp'y hp' => ?_⟩
  · obtain ⟨w, hw⟩ := U.ext
    exact ((hf.1 p (f p)).2 rfl w hw).1
  · have e : f p = f p' := (hf.1 p' (f p)).1 hp'
    letI := GlobalTheory.TorusExt.gtGroup D.toPre (AlgebraicClosure (FractionRing V))
    obtain ⟨z, hy, w, hw₁, hw₂⟩ := (hf.2.2.1 p p').1 e
    have hg := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hw₂
    rw [hp'y, hpy, zero_add] at hy
    have hz : z = 0 := by
      have h2 : (N : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hy.symm
      rcases smul_eq_zero.1 h2 with h | h
      · omega
      · exact h
    subst hz
    have hw : w.b = 1 := by
      exact hw₁.1.trans (cPoint_zero _)
    rw [hg, GlobalTheory.TorusExt.add_b, hw, _root_.mul_one, hpb]

end GlobalTheory.Poinc.IntTerm
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

open GlobalTheory.GoodMetric.LinSubst

theorem sum_det_rowSel_mul {n : ℕ} (F : (Fin n → Fin n) → ℂ) :
    ∑ c : Fin n → Fin n, (rowSel c).det * F c =
      ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * F u := by
  classical
  symm
  refine Finset.sum_of_injOn (fun u : Equiv.Perm (Fin n) => (u : Fin n → Fin n))
    (fun u _ v _ h => DFunLike.coe_injective h) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro c _ hc
    rw [det_rowSel_of_not_injective, zero_mul]
    intro hinj
    exact hc ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  · intro u _
    rw [det_rowSel_perm]

theorem topCoeff_prod_forms {n : ℕ} (k : Fin n → Fin n → Fin n → ℂ) :
    topCoeff (∏ i, ∑ a, ∑ b, MvPolynomial.C (k i a b) * MvPolynomial.X (a, b)) =
      ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i b => k i (u i) b).det := by
  classical
  rw [← sum_det_rowSel_mul (fun c => (Matrix.of fun i b => k i (c i) b).det)]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum,
    ← sum_prod_mul_det_rowSel (Matrix.of fun i b => k i (c i) b), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul, topCoeff_prod_X_pair]
  simp only [Matrix.of_apply]
  ring

end GlobalTheory.GoodTop
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.CechPic

theorem lam_rosati_field (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O)
    (o : O) {T' : Over (Sp K)} (x z : T' ⟶ P.A) :
    haveI := P.isAb.comm
    lam (cls P.L P.isLB) (x ≫ oA.act (star o)) z = lam (cls P.L P.isLB) x (z ≫ oA.act o) := by
  haveI := P.isAb.comm
  haveI := oA.hom (star o)
  haveI := oA.hom o
  have hr := oA.rosati (star o)
  rw [star_star] at hr
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.globalFns_holds P.isAb P.isLB _ _ hr
  have h := GlobalTheory.EndRosati.cls_of_rosati P.isLB u hu x z
  show _ - _ - _ + _ = _ - _ - _ + _
  rw [h]

theorem kill_of_lam_triv : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O) (e f : O) (H : Over (Sp K)) (a : H ⟶ P.A) (r : P.A ⟶ H), r ≫ a = oA.act e → ∀ (T : Over (Sp K)) (y : T ⟶ P.A), (∃ t : LB.Gen (letI := P.isAb.comm; (abelian₂ P.A P.L).pull (lift (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) : H ⊗ T ⟶ G2 P.A).left), t.IsGen) → y ≫ oA.act (star e * star f) = toUnit T ≫ η[P.A] := by
  intro K _ P O _ _ oA e f H a r hra T y ⟨t, ht⟩
  haveI := P.isAb.comm
  have h0 : lam (cls P.L P.isLB) (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) = 0 := by
    have := (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).2 ⟨t, ht⟩
    rwa [GlobalTheory.FullSiegel.cls_lam_pull P.isLB] at this
  have h1 : lam (cls P.L P.isLB) (fst T P.A ≫ y) ((snd T P.A ≫ oA.act e) ≫ oA.act f) = 0 := by
    have := congrArg (pull (lift (snd T P.A ≫ r) (fst T P.A)).left) h0
    rw [pull_lam, map_zero, lift_snd_assoc, lift_fst_assoc, Category.assoc, reassoc_of% hra] at this
    rw [Category.assoc]
    exact this
  have h2 := (lam_rosati_field K P O oA f _ _).trans h1
  have h3 := (lam_rosati_field K P O oA e _ (snd T P.A)).trans h2
  have hb : ((fst T P.A ≫ y) ≫ oA.act (star f)) ≫ oA.act (star e) = fst T P.A ≫ y ≫ oA.act (star e * star f) := by
    rw [oA.map_mul]; simp only [Category.assoc]
  rw [hb] at h3
  have h4 := congrArg (pull (lift (snd P.A T) (fst P.A T)).left) h3
  rw [pull_lam, map_zero, lift_fst_assoc, lift_snd] at h4
  have hg : ∃ t : ((abelian₂ P.A P.L).pull (lift (snd P.A T ≫ y ≫ oA.act (star e * star f)) (fst P.A T)).left).Gen,
      t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).1 ?_
    rw [GlobalTheory.FullSiegel.cls_lam_pull P.isLB]
    exact h4
  exact (GlobalTheory.FullSiegel.eq_one_of_lam_triv P.isLB P.rigid P.ktriv T _ hg).trans (Hom.one_def ..)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelGalois

theorem exists_galois (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Module.Finite F E] (n : ℕ)
    (hn : 0 < n) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω) (i : E →+* Ω) (ζ : Ωˣ), FiniteDimensional F Ω ∧ IsGalois F Ω ∧
      i.comp (algebraMap F E) = algebraMap F Ω ∧ IsPrimitiveRoot ζ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : CharZero E := (algebraMap F E).charZero_iff (algebraMap F E).injective |>.1 inferInstance
  let C := CyclotomicField n E
  haveI : Module.Finite E C := IsCyclotomicExtension.finite {n} E C
  haveI : Module.Finite F C := Module.Finite.trans E C
  let L := AlgebraicClosure C
  haveI : IsAlgClosure F L := IsAlgClosure.ofAlgebraic F C L
  let Ω := IntermediateField.normalClosure F C L
  have hz := (IsCyclotomicExtension.zeta_spec n E C).map_of_injective (algebraMap C Ω).injective
  obtain ⟨ζ, hζ⟩ := hz.isUnit hn.ne'
  refine ⟨Ω, inferInstance, inferInstance, (algebraMap C Ω).comp (algebraMap E C), ζ, inferInstance, ?_, ?_,
    IsPrimitiveRoot.coe_units_iff.1 (hζ ▸ hz)⟩
  · exact { }
  · rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq F E C, ← IsScalarTower.algebraMap_eq F C Ω]


open MonObj in
theorem nonempty_level_of_rational {F : Type} [Field F] [CharZero F] (P : PolAV (Sp F)) (n : ℕ) (hn : 0 < n) (ζ : Fˣ)
    (hζ : IsPrimitiveRoot ζ n) (Q : PolAV (Sp (AlgebraicClosure F))) (φ : Q.A.left ⟶ P.A.left)
    (hQ : IsPolFibre (algebraMap F (AlgebraicClosure F)) P Q φ)
    (H : ∀ y, y ^ n = 1 → ∃ x, ObjPull.secPull hQ.2.1 x = y) : Nonempty (Out.Level P n (unitOn ζ)) := by
  let σ := algebraMap F (AlgebraicClosure F)
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have prim : ∀ {R : Type} [CommRing R] [Nontrivial R] (φ : F →+* R),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ζ) n := fun φ =>
    hζ.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  have nt : ∀ (F : Type) [Field F], Nontrivial Γ(Spec (CommRingCat.of F), ⊤) := fun F _ =>
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hp : IsPrimitiveRoot (unitOn ζ) n := by
    have := nt F
    exact prim (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  obtain ⟨l⟩ := GlobalTheory.nonempty_level_of_isAlgClosed _ Q n (Units.map σ.toMonoidHom ζ) (Nat.cast_ne_zero.2 hn.ne') (prim σ)
  have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
      {X : Scheme} (y y' : Sp K ⟶ X) (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
    obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
    obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
    simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
    have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
        spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
          (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
      intro q ψ
      simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
    rw [e, e] at h
    have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
    simp only [Sigma.mk.inj_iff] at h2
    obtain ⟨rfl, h3⟩ := h2
    have h4 : φ = φ' := by
      have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
      ext x
      apply gam.injective
      have := congrArg (fun f => f.hom x) h5
      simpa using this
    rw [h4]
  have hinj : Function.Injective (ObjPull.secPull hQ.2.1) := fun a b h =>
    Over.OverMorphism.ext (spec_map_field_cancel σ _ _ (by
      rw [← ObjPull.secPull_left hQ.2.1, ← ObjPull.secPull_left hQ.2.1, h]))
  choose t ht using fun a => H (l.pt a) (l.torsion a)
  have tors : ∀ a, t a ^ n = 1 := fun a => hinj (by rw [map_pow, ht, map_one]; exact l.torsion a)
  have uz : ∀ {R : Type} [CommRing R] (u : Rˣ) (m : ℤ), unitOn (u ^ m) = unitOn u ^ m := fun {R} _ u m =>
    map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom) u m
  have hg : 2 * P.g = 2 * Q.g := by rw [hQ.1]
  have hs : ∀ i j, stdSymp Q.g (Fin.cast hg i) (Fin.cast hg j) = stdSymp P.g i j := fun i j => by
    simp only [stdSymp, Fin.val_cast, hQ.1]
  obtain ⟨lev, -⟩ := GlobalTheory.exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp F) P n (unitOn ζ) hp
    (fun F' _ s => by
      have := nt F'
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)⟩
      rw [← map_natCast (Spec.preimage s).hom]
      exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn.ne')) (fun i => t (Fin.cast hg i)) (fun i => tors _)
    (fun i j => by
      have h := l.pairing (Fin.cast hg i) (Fin.cast hg j)
      rw [hs, ← uz, ← map_zpow, ← ht, ← ht] at h
      rw [← uz]
      exact LevelAfterExt.weilIs_of_ext σ hQ n _ _ _ (tors _) (tors _) h)
  exact ⟨lev⟩

theorem exists_level_galois : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (ι : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (K : ℕ), 0 < K → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp ι)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  intro Ω₁ _ _ R₁ _ ι P₁ K hK
  have hB := GlobalTheory.laws_without_cohomology.2.2.1
  obtain ⟨P₀, φ₀, h₀⟩ := exists_isPolFibre hB ι P₁
  obtain ⟨E, _, _, hfin, H⟩ := LevelAfterExt.exists_ext_torsion Ω₁ P₀ K hK
  obtain ⟨Ω₂, _, _, i, ζ, hfd, hgal, hi, hζ⟩ := exists_galois Ω₁ E K hK
  haveI : CharZero Ω₂ := (algebraMap Ω₁ Ω₂).charZero_iff (algebraMap Ω₁ Ω₂).injective |>.1 inferInstance
  obtain ⟨Q, ψ, hQ⟩ := exists_isPolFibre hB (algebraMap Ω₁ Ω₂) P₀
  obtain ⟨Q', ψ', hQ'⟩ := exists_isPolFibre hB (algebraMap Ω₂ (AlgebraicClosure Ω₂)) Q
  refine ⟨Ω₂, inferInstance, inferInstance, Q, ψ ≫ φ₀, ζ, hfd, hgal, hζ, hQ.1.trans h₀.1,
    (hQ.2.1.comp h₀.2.1).congr (GlobalTheory.spMap_comp_spMap _ _) rfl, ?_,
    nonempty_level_of_rational Q K hK ζ hζ Q' ψ' hQ' (H Ω₂ _ i _ hi Q ψ hQ _ Q' ψ' hQ')⟩
  exact LBIso.trans Q.isLB (pull_isLB P₀.isLB _) (pull_isLB P₁.isLB _) hQ.2.2.symm
    (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P₁.L _ _ _ ψ fun _ => rfl) h₀.2.2.symm)

end GlobalTheory.LevelGalois
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FreeCoord

open GlobalTheory.BoxIndep TensorProduct

theorem eq_zero_of_germOf_max {B : CommRingCat.{0}} (a : B)
    (h : ∀ z : Spec B, z.asIdeal.IsMaximal → germOf (𝟙 (Spec B)) z a = 0) : a = 0 := by
  have : (Ideal.span {a}).annihilator = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hI⟩ := Ideal.exists_le_maximal _ hne
    let z : Spec B := ⟨p, hp.isPrime⟩
    have h1 : algebraMap B ((Spec.structureSheaf B).presheaf.stalk z) a = 0 := h z hp
    have := StructureSheaf.IsLocalization.to_stalk B z
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff z.asIdeal.primeCompl _ _).1 h1
    exact c.2 (hI (Submodule.mem_annihilator_span_singleton _ _ |>.2 hc))
  have h1 : (1 : B) ∈ (Ideal.span {a}).annihilator := this ▸ Submodule.mem_top
  exact (one_smul B _).symm.trans ((Submodule.mem_annihilator_span_singleton _ _).1 h1)

theorem gs_comp' {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U) (f : Γ(X, U)) :
    gs (r ≫ F) z U f = (r.stalkMap z).hom (gs F (r z) U f) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem germ_eq_zero : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U → (∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z = x → ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0 := by
  intro R R₁ _ _ ρ₁ d b hb X f U a x hx h
  let _ : Algebra R R₁ := ρ₁.toAlgebra
  let A : CommRingCat.{0} := X.presheaf.stalk x
  let _ : Algebra R A := (germOf (B := CommRingCat.of R) f x).toAlgebra
  have hli : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun c hc =>
    congrFun ((hb 0).unique (y₁ := c) (y₂ := 0) (by simp only [Algebra.smul_def] at hc; exact hc.symm) (by simp))
  have hsp : ⊤ ≤ Submodule.span R (Set.range b) := fun r _ => by
    obtain ⟨c, hc, -⟩ := hb r
    rw [hc]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ (c l) (Submodule.subset_span ⟨l, rfl⟩)
  let β := Module.Basis.mk hli hsp
  have : Module.Finite R R₁ := Module.Finite.of_basis β
  let B : CommRingCat.{0} := CommRingCat.of (A ⊗[R] R₁)
  let iA : A ⟶ B := CommRingCat.ofHom (algebraMap A (A ⊗[R] R₁))
  let iR : CommRingCat.of R₁ ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).toRingHom
  have w : (Spec.map iA ≫ X.fromSpecStalk x) ≫ f = Spec.map iR ≫ spMap ρ₁ := by
    rw [Category.assoc, fromSpecStalk_comp (B := CommRingCat.of R)]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    ext r
    exact (IsScalarTower.algebraMap_apply R A (A ⊗[R] R₁) r).symm.trans
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := R₁)).commutes r).symm
  let r : Spec B ⟶ pullback f (spMap ρ₁) := pullback.lift _ _ w
  have r1 : r ≫ pullback.fst f (spMap ρ₁) = Spec.map iA ≫ X.fromSpecStalk x := pullback.lift_fst _ _ _
  have r2 : r ≫ pullback.snd f (spMap ρ₁) = Spec.map iR := pullback.lift_snd _ _ _
  have key : (∑ l, iR.hom (b l) * iA.hom (gs (𝟙 X) x U (a l)) : B) = 0 := by
    refine eq_zero_of_germOf_max _ fun z hz => ?_
    letI : z.asIdeal.IsMaximal := hz
    have hm : (z.asIdeal.comap (algebraMap A (A ⊗[R] R₁))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) z.asIdeal
    have hc : Spec.map iA z = closedPoint A := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    have hzx : pullback.fst f (spMap ρ₁) (r z) = x := by
      have : (r ≫ pullback.fst f (spMap ρ₁)) z = X.fromSpecStalk x (Spec.map iA z) := by rw [r1]; rfl
      rw [hc, Scheme.fromSpecStalk_closedPoint] at this
      exact this
    have e := congrArg (r.stalkMap z).hom (h (r z) hzx)

    rw [map_zero, map_sum] at e

    rw [← e, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_mul, ← gs_comp' r _ z ⊤ trivial, ← gs_comp' r _ z U (hzx ▸ hx), r1, r2,
      gs_fromSpecStalk x hx, ← germOf_apply, ← germOf_map, ← germOf_map, Category.id_comp, Category.id_comp]
  have hli' := (Algebra.TensorProduct.basis A β).linearIndependent
  refine Fintype.linearIndependent_iff.1 hli' (fun l => gs (𝟙 X) x U (a l)) ?_
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) key
  rw [Algebra.smul_def, _root_.mul_comm, Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
  rfl

end GlobalTheory.Mum.FreeCoord
end
end
