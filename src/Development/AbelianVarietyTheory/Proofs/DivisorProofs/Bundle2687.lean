module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle114
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelAmpleQProjNoeth

open GlobalTheory.RelAmpleQProj

theorem isQProjOver_of_relAmple_noeth : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0})
    (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L →
    IsQProjOver (A.hom ≫ s) := by
  rintro K _ _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProjNoeth
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem finite_lift_fractionField (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Sp R ⟶ P) (y : Sp (FractionRing R) ⟶ Z)
    (hp : IsFinite p) (hy : y ≫ p = jK R ≫ ξ₀) :
    ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first
  | exact @_root_.GlobalTheory.RetractionLiftSection.lift_finite
  | exact _root_.GlobalTheory.RetractionLiftSection.lift_finite
  | (apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RetractionLiftSection.lift_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RetractionLiftSection.lift_finite ..)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

variable {S : Scheme.{0}} (G : Over S) (L : LB G.left)

abbrev LocSec (N : S.Opens) : Type := ∀ i : L.ι, Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ N)

variable {G L}

def IsLocSec {N : S.Opens} (s : LocSec G L N) : Prop :=
  ∀ i j, resG _ (fun _ hx => ⟨hx.1.1, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
    resG _ (fun _ hx => hx.1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U i ⊓ L.U j) (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) *
      resG _ (fun _ hx => ⟨hx.1.2, hx.2⟩ : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N ≤ L.U j ⊓ G.hom ⁻¹ᵁ N) (s j)

theorem lpow_U_le [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (j : Fin 1 → L.ι) :
    (LPow G L 1 (Over.mk ξ)).U j ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ N) := by
  intro y hy
  refine ⟨Set.mem_iInter.1 hy 0, ?_⟩
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  show G.hom ((snd (Over.mk ξ) G).left y) ∈ N
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hξ ⟨_, rfl⟩

def genPull [GrpObj G] {K : Type} [Field K] {ξ : Sp K ⟶ S} {N : S.Opens} (hξ : Set.range ξ ⊆ N)
    (s : LocSec G L N) (j : Fin 1 → L.ι) : Γ((Over.mk ξ ⊗ G).left, (LPow G L 1 (Over.mk ξ)).U j) :=
  ((snd (Over.mk ξ) G).left.appLE _ _ (lpow_U_le hξ j)).hom (s (j 0))

def GenIs [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S) {N : S.Opens} (s : LocSec G L N)
    (v : SecM G L 1 (Over.mk ξ)) : Prop :=
  ∃ hξ : Set.range ξ ⊆ N, genPull hξ s = v.1

def FibNz {N : S.Opens} (s : LocSec G L N) (W : S.Opens) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), Set.range x ⊆ W →
    ∃ (y : Sp K ⟶ G.left) (i : L.ι), y ≫ G.hom = x ∧ Set.range y ⊆ (L.U i ⊓ G.hom ⁻¹ᵁ N : G.left.Opens) ∧
      valF y _ (s i) ≠ 0

theorem isLocSec_zero {N : S.Opens} : IsLocSec (0 : LocSec G L N) := fun i j => by
  simp [Pi.zero_apply, map_zero, mul_zero]

end GlobalTheory.UMin.ThBdl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntOverCdvr

open IsLocalRing

theorem isIntegralElem_of_val_nonneg : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v → ∀ z : F, 0 ≤ v z → ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).IsIntegralElem z := by
  intro V _ _ _ hV ϖ hϖ F _ _ _ v hv z hz
  obtain ⟨hdvr, hcomp, hchar⟩ := hV
  let K := FractionRing V
  letI : Algebra V F := ((algebraMap K F).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).mpr
    ((algebraMap K F).injective.comp (IsFractionRing.injective V K))
  haveI : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mpr inferInstance
  obtain ⟨W, hW, -, -, hfin, -, hloc, hs, -⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F {z}
  haveI := hfin

  have hVnn : ∀ r : V, 0 ≤ v (algebraMap V F r) := fun r =>
    GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r

  let S : ValuationSubring F := GlobalTheory.FiniteDVRValuation.nonnegSubring v (RingHom.id F)
  have hWnn : ∀ w ∈ W, 0 ≤ v w := by
    intro w hw
    have hint : IsIntegral V w := (Algebra.IsIntegral.isIntegral (R := V) (⟨w, hw⟩ : W)).map W.val
    let φ : V →+* S := (algebraMap V F).codRestrict S (fun r => hVnn r)
    have hS : (algebraMap S F).IsIntegralElem w := RingHom.IsIntegralElem.of_comp (f := φ) hint
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := F)).1 hS
    rw [← hy]
    exact y.2

  have hϖpos : 0 < v (algebraMap V F ϖ) := by
    obtain ⟨n, hn, hu⟩ := GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hϖ.ne_zero
    have hn0 : n ≠ 0 := fun h => hϖ.not_isUnit (hu h)
    change 0 < v (algebraMap K F (algebraMap V K ϖ))
    rw [hn]
    exact_mod_cast Nat.pos_of_ne_zero hn0

  have hunit : ∀ c : W, v (c : F) = 0 → IsUnit c := by
    intro c hc
    by_contra hnu
    have hinj : Function.Injective (algebraMap V W) := by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective V F
      have := congrArg Subtype.val hab
      simpa using this
    set ϖW : W := algebraMap V W ϖ
    have hϖW0 : ϖW ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    obtain ⟨N, hN⟩ : ∃ N : ℕ, IsDiscreteValuationRing.addVal W ϖW = N := by
      rcases h : IsDiscreteValuationRing.addVal W ϖW with _ | N
      · exact absurd (IsDiscreteValuationRing.addVal_eq_top_iff.1 h) hϖW0
      · exact ⟨N, rfl⟩
    have hc1 : 1 ≤ IsDiscreteValuationRing.addVal W c := by
      rw [ENat.one_le_iff_ne_zero]
      exact fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hdvd : ϖW ∣ c ^ N := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal W c := nsmul_le_nsmul_right hc1 N
    obtain ⟨d, hd⟩ := hdvd
    have h1 : v ((c : F) ^ N) = 0 := by rw [AddValuation.map_pow, hc, nsmul_zero]
    have h2 : v ((c : F) ^ N) = v (algebraMap V F ϖ) + v (d : F) := by
      rw [← AddValuation.map_mul]
      congr 1
      have h := congrArg Subtype.val hd
      simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul] at h
      exact h
    have h3 : 0 < v ((c : F) ^ N) := by
      rw [h2]
      exact lt_of_lt_of_le hϖpos (le_add_of_nonneg_right (hWnn d d.2))
    rw [h1] at h3
    exact lt_irrefl _ h3

  obtain ⟨a, ha, b, hb, hb0, hab⟩ := hs z (Finset.mem_singleton_self z)
  have hzW : z ∈ W := by
    let a' : W := ⟨a, ha⟩
    let b' : W := ⟨b, hb⟩
    rcases le_total (IsDiscreteValuationRing.addVal W b') (IsDiscreteValuationRing.addVal W a') with h | h
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : a = b * c := congrArg Subtype.val hc
      have : z = c := by
        apply mul_left_cancel₀ hb0
        rw [mul_comm, hab, hc']
      rw [this]; exact c.2
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : b = a * c := congrArg Subtype.val hc
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hb0 (by simpa using hc')
      have hzc : z * c = 1 := by
        apply mul_left_cancel₀ ha0
        calc a * (z * c) = z * (a * c) := by ring
          _ = a * 1 := by rw [← hc', hab, _root_.mul_one]
      have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hzc
      have hvc : v (c : F) = 0 := by
        have hsum : v z + v (c : F) = 0 := by rw [← AddValuation.map_mul, hzc, AddValuation.map_one]
        have hc0 := hWnn c c.2
        refine le_antisymm ?_ hc0
        calc v (c : F) = 0 + v (c : F) := (zero_add _).symm
          _ ≤ v z + v (c : F) := by gcongr
          _ = 0 := hsum
      obtain ⟨u, hu⟩ := hunit c hvc
      have : z = ((u⁻¹ : Wˣ) : W) := by
        have h1 : ((u : W) : F) * (((u⁻¹ : Wˣ) : W) : F) = 1 := by
          rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
        rw [hu] at h1
        calc z = z * ((c : F) * (((u⁻¹ : Wˣ) : W) : F)) := by rw [h1, _root_.mul_one]
          _ = (z * c) * (((u⁻¹ : Wˣ) : W) : F) := by ring
          _ = _ := by rw [hzc, _root_.one_mul]
      rw [this]; exact Subtype.property _

  exact (Algebra.IsIntegral.isIntegral (R := V) (⟨z, hzW⟩ : W)).map W.val

end GlobalTheory.IntOverCdvr
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem symm_lbIso_descends_to_subring_containing_finset : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → LBIso (P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)) ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull (lift (snd ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B)) (fst ((Over.pullback (spMap (Subring.inclusion h))).obj B) ((Over.pullback (spMap (Subring.inclusion h))).obj B))).left) := by
  intro R _ S A _ _ B _ _ φ φ₂ P P₀ hB hφ sq hP hP₀ hw hsym
  haveI := hB.proper
  have hprop : IsProper (G2 B).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : QuasiCompact (G2 B).hom := inferInstance
  haveI : QuasiSeparated (G2 B).hom := inferInstance
  set sw₀ := (lift (snd B B) (fst B B)).left with hsw₀
  have hpb := isPullback_square hφ.1 φ₂ sq
  have H : LBIso (P₀.pull φ₂) ((P₀.pull sw₀).pull φ₂) :=
    LBIso.trans (pull_isLB hP₀ _) hP (pull_isLB (pull_isLB hP₀ _) _) hw.symm
      (LBIso.trans hP (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _) hsym
        (lbIso_square hP hP₀ hw (lift_square sq sq.2.symm sq.1.symm)))
  obtain ⟨F, hF⟩ := lbIso_descends_to_subring_containing_finset R S (G2 A).left (G2 B).left (G2 A).hom
    (G2 B).hom φ₂ P₀ (P₀.pull sw₀) hpb hP₀ (pull_isLB hP₀ _) H
  refine ⟨F, fun R₁ h hF₁ => ?_⟩
  have hpb₁ := isPullback_square (isGrpPullback (spMap (Subring.inclusion h)) B).1 _
    (isSquare (spMap (Subring.inclusion h)) B)
  have H₁ := hF R₁ h hF₁ _ _ _ hpb₁
  have e := lift_swap (spMap (Subring.inclusion h)) B
  refine LBIso.trans (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB (pull_isLB hP₀ _) _) H₁ ?_
  exact lbIso_square (pull_isLB hP₀ _) hP₀ (lbIso_refl (pull_isLB hP₀ sw₀)) e.symm

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

namespace GlobalTheory

theorem lbIso_triv_pull_triv {X Y : Scheme.{0}} (f : Y ⟶ X) : LBIso ((LB.triv X).pull f) (LB.triv Y) :=
  Ex.ValInh.lbIso_of_g_one (fun i j => by
    simp only [LB.pull, LB.LinComb, LB.triv, map_one, one_zpow, Finset.prod_const_one]
    simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
    exact (res _).map_one) (fun i j => rfl)

theorem exists_finset_gen_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := by
  intro R _ S A _ _ B _ _ φ φ₂ P P₀ a a₀ hB hφ sq hP hP₀ hw e ht
  haveI := hB.proper
  have hN : (P₀.pull a₀.left).IsLB := pull_isLB hP₀ _
  have hT : ∀ X : Scheme.{0}, (LB.triv X).IsLB := fun X => LB.isLB_triv X
  have H₀ : LBIso (LB.triv A.left) ((P₀.pull a₀.left).pull φ) :=
    LBIso.trans (hT _) (pull_isLB hP _) (pull_isLB hN _) ((CechPic.iso_triv_iff _).2 ht)
      (lbIso_square hP hP₀ hw e)
  have H : LBIso ((LB.triv B.left).pull φ) ((P₀.pull a₀.left).pull φ) :=
    LBIso.trans (pull_isLB (hT _) _) (hT _) (pull_isLB hN _) (lbIso_triv_pull_triv φ) H₀
  obtain ⟨F, hF⟩ := lbIso_descends_to_subring_containing_finset R S A.left B.left A.hom B.hom φ
    (LB.triv B.left) (P₀.pull a₀.left) hφ.1 (hT _) hN H
  refine ⟨F, fun R₁ h hs a₁ e₁ => ?_⟩
  have H₁ := hF R₁ h hs _ _ (pφ (spMap (Subring.inclusion h)) B)
    (isGrpPullback (spMap (Subring.inclusion h)) B).1
  have H₂ : LBIso ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left)
      ((P₀.pull a₀.left).pull (pφ (spMap (Subring.inclusion h)) B)) :=
    lbIso_square (pull_isLB hP₀ _) hP₀ (PolBaseChange.lbIso_refl (pull_isLB hP₀ _)) e₁
  refine (CechPic.iso_triv_iff _).1 ?_
  exact LBIso.trans (hT _) (pull_isLB (hT _) _) (pull_isLB (pull_isLB hP₀ _) _)
    (lbIso_triv_pull_triv _).symm
    (LBIso.trans (pull_isLB (hT _) _) (pull_isLB hN _) (pull_isLB (pull_isLB hP₀ _) _) H₁ H₂.symm)

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.MulEpi

attribute [local instance] Over.cartesianMonoidalCategory

theorem epi_pow_of_isAbelianScheme (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (k : ℕ) (hk : 0 < k) : Epi ((𝟙 A) ^ k) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA k hk
  haveI : Epi ((𝟙 A) ^ k).left := Flat.epi_of_flat_of_surjective _
  exact (Over.forget S).epi_of_epi_map this

end GlobalTheory.UPel.HT.MulEpi
end
