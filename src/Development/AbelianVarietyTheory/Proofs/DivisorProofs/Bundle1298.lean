module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle396
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cmExtensionIdeleConj_mem_finiteUnitIdeles : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (y : Neutral.B1.Ideles E), y ∈ GlobalTheory.Mem.Chr.unitIdl E →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  first | exact @GlobalTheory.ConjUnit.ideleConj_mem_unitIdl | exact GlobalTheory.ConjUnit.ideleConj_mem_unitIdl | (intros; apply GlobalTheory.ConjUnit.ideleConj_mem_unitIdl <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_pow_eq_one_of_principal_unitIdele_norm_one : ∀ (E : Type) [Field E] [NumberField E] (t : Eˣ), Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E →
    (∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  first | exact @GlobalTheory.UnitTorsion.principal_unit_idele_torsion | exact GlobalTheory.UnitTorsion.principal_unit_idele_torsion | (intros; apply GlobalTheory.UnitTorsion.principal_unit_idele_torsion <;> assumption)
end

section

noncomputable section

open NumberField MeasureTheory Matrix Topology Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff InnerProductSpace ComplexConjugate

namespace GlobalTheory.CuspQuot

section Test

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Set V} {α : V → ℂ}

def IsTest (U : Set V) (α : V → ℂ) : Prop := ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U

theorem IsTest.continuous_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Continuous fun x => α x * G x :=
  continuous_of_tsupport fun x hx => h.1.continuous.continuousAt.mul
    (hG.continuousAt (hU.mem_nhds (h.2.2 (tsupport_mul_subset_left hx))))

theorem IsTest.add {β : V → ℂ} (h : IsTest U α) (h' : IsTest U β) : IsTest U (α + β) :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, (tsupport_add α β).trans (Set.union_subset h.2.2 h'.2.2)⟩

theorem IsTest.mul (h : IsTest U α) {β : V → ℂ} (hβ : ContDiff ℝ ∞ β) : IsTest U fun x => α x * β x :=
  ⟨h.1.mul hβ, h.2.1.mul_right, tsupport_mul_subset_left.trans h.2.2⟩

theorem IsTest.fderiv (h : IsTest U α) (v : V) : IsTest U fun x => fderiv ℝ α x v :=
  ⟨(h.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, h.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans h.2.2⟩

theorem isTest_zero : IsTest U (0 : V → ℂ) := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure]

theorem IsTest.integrable_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Integrable (fun x => α x * G x) ν :=
  (h.continuous_mul hU hG).integrable_of_hasCompactSupport h.2.1.mul_right

end Test

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def smoothing (ν : Measure (Lie E a)) (α : Lie E a → ℂ) (φ : GA E a → ℂ) (x : GA E a) : ℂ :=
  ∫ y, α y * chart φ x y ∂ν

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]


variable {μ} [μ.IsMulRightInvariant] {S : Submodule ℂ (L2 (latticeGL E a) μ)}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin a) (Cinf E) → Matrix (Fin a) (Fin a) (Cinf E)) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact Units.isOpenEmbedding_val
end

theorem continuous_infGL : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem continuous_integrand {α : Lie E a → ℂ} (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Continuous fun p : GA E a × Lie E a => α p.2 * chart φ p.1 p.2 := by
  refine continuous_of_tsupport fun p hp => (hα.1.continuous.comp continuous_snd).continuousAt.mul ?_
  have h1 : p.2 ∈ tsupport α := by
    refine (closure_minimal (fun q hq => ?_) ((isClosed_tsupport α).preimage continuous_snd) :
      _ ⊆ Prod.snd ⁻¹' tsupport α) hp
    exact subset_tsupport _ (left_ne_zero_of_mul hq)
  obtain ⟨x, y⟩ := p
  obtain ⟨u, hu⟩ := hα.2.2 h1
  obtain rfl : y = toL u.val := hu.symm
  have he : IsOpenEmbedding (Prod.map id fun u : GL (Fin a) (Cinf E) => toL u.val : GA E a × _ → GA E a × Lie E a) :=
    IsOpenEmbedding.id.prodMap isOpenEmbedding_val
  refine (he.continuousAt_iff (x := (x, u))).1 (Continuous.continuousAt ?_)
  exact (hφ.comp (continuous_fst.mul (continuous_infGL.comp continuous_snd))).congr fun q => (chart_val φ q.1 q.2).symm

theorem norm_chart_le {φ : GA E a → ℂ} {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (x : GA E a) (y : Lie E a) : ‖chart φ x y‖ ≤ C := by
  unfold chart
  split_ifs
  · exact hC _
  · exact norm_zero.trans_le ((norm_nonneg _).trans (hC 1))

theorem continuous_smoothing (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) :
    Continuous (smoothing ν α φ) :=
  continuous_of_dominated (bound := fun y => ‖α y‖ * C)
    (fun x => ((continuous_integrand hα hφ).comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    (fun x => .of_forall fun y => (norm_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (norm_chart_le hC x y) (norm_nonneg _)))
    ((hα.1.continuous.integrable_of_hasCompactSupport hα.2.1).norm.mul_const C)
    (.of_forall fun y => (continuous_integrand hα hφ).comp (Continuous.prodMk_left y))

variable [IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)]


omit [μ.IsMulRightInvariant] in
theorem memL2_of_bound {φ : GA E a → ℂ} (hφ : Continuous φ) (hl : LeftInv (latticeGL E a) φ) {C : ℝ}
    (hC : ∀ g, ‖φ g‖ ≤ C) : MemL2Quotient (latticeGL E a) μ φ :=
  ⟨hl, MemLp.of_bound (aestronglyMeasurable_quotMeasure_iff_lift.2 (by
    rw [hl.lift_descend]; exact hφ.aestronglyMeasurable)) C (.of_forall fun q => hC _)⟩


end GlobalTheory.CuspQuot

end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL
open scoped InnerProductSpace

namespace GlobalTheory.SqIntGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem memL2_iff_std {f : GA E a → ℂ} : MemL2Quotient (latticeGL E a) μ f ↔
    LeftInv (latticeGL E a) f ∧ MemLp f 2 (μ.restrict (stdDom (latticeGL E a))) :=
  memL2_iff_fundamental_domain (isFundamentalDomain_stdDom _ μ)

def squareIntegrableSmoothSubmoduleGL : Submodule ℂ (Sm E a) where
  carrier := {ψ | MemL2Quotient (latticeGL E a) μ ψ.1}
  zero_mem' := (memL2_iff_std μ).2 ⟨fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' {x y} hx hy := by
    rw [Set.mem_setOf_eq, memL2_iff_std] at hx hy ⊢
    exact ⟨fun γ hγ g => by simp [hx.1 γ hγ g, hy.1 γ hγ g], hx.2.add hy.2⟩
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq, memL2_iff_std] at hx ⊢
    exact ⟨fun γ hγ g => by simp [hx.1 γ hγ g], hx.2.const_smul c⟩

theorem mem_l2Sub {ψ : Sm E a} : ψ ∈ squareIntegrableSmoothSubmoduleGL μ ↔ MemL2Quotient (latticeGL E a) μ ψ.1 := Iff.rfl

def l2Map : Sm E a →ₗ[ℂ] L2 (latticeGL E a) μ :=
  toL2ₗ μ (squareIntegrableSmoothSubmoduleGL μ) (fun _ h => (mem_l2Sub μ).1 h) ∘ₗ
    Submodule.linearProjOfIsCompl (squareIntegrableSmoothSubmoduleGL μ) _ (Classical.choose_spec (Submodule.exists_isCompl (squareIntegrableSmoothSubmoduleGL μ)))

theorem l2Map_apply {ψ : Sm E a} (h : ψ ∈ squareIntegrableSmoothSubmoduleGL μ) : l2Map μ ψ = ((mem_l2Sub μ).1 h).toL2 := by
  unfold l2Map
  rw [LinearMap.comp_apply]
  have e := Submodule.linearProjOfIsCompl_apply_left (Classical.choose_spec (Submodule.exists_isCompl (squareIntegrableSmoothSubmoduleGL μ))) ⟨ψ, h⟩
  erw [e]
  rfl

def l2Form : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp (l2Map μ)).compl₂ (l2Map μ)

theorem l2Form_apply {x y : Sm E a} (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hy : y ∈ squareIntegrableSmoothSubmoduleGL μ) :
    l2Form μ x y = ⟪((mem_l2Sub μ).1 hx).toL2, ((mem_l2Sub μ).1 hy).toL2⟫_ℂ := by
  simp only [l2Form, LinearMap.compl₂_apply, LinearMap.comp_apply, l2Map_apply μ hx, l2Map_apply μ hy]
  rfl

theorem re_l2Form_pos {x : Sm E a} (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hc : Continuous x.1) (h0 : x ≠ 0) : 0 < (l2Form μ x x).re := by
  rw [l2Form_apply μ hx hx]
  have : ((mem_l2Sub μ).1 hx).toL2 ≠ 0 := toL2_ne_zero _ hc fun e => h0 (Subtype.ext e)
  first
    | exact (re_inner_self_pos (𝕜 := ℂ)).2 this
    | exact inner_self_pos.2 this
    | exact (RCLike.inner_self_pos).2 this
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; simpa using this)

theorem mem_l2Sub_of_isAutForm {ψ : Sm E a} (h : IsAutForm ψ) (h' : IsSqInt ψ.1) : ψ ∈ squareIntegrableSmoothSubmoduleGL μ :=
  memL2_of_isAutForm h h'

end GlobalTheory.SqIntGL

end
end

section

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.TorsionKill

theorem eq_of_pullback_eq {S S' : Scheme.{0}} (t : S' ⟶ S) [IsSchemeTheoreticallyDominant t]
    [QuasiCompact t] {Y X : Over S} [Flat Y.hom] [IsSeparated X.hom] {a b : Y ⟶ X}
    (h : (Over.pullback t).map a = (Over.pullback t).map b) : a = b := by
  apply Over.OverMorphism.ext
  refine GlobalTheory.KernelNoTorsion.eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm)
    (pullback.fst Y.hom t) ?_
  have h' := congr(($h).left ≫ pullback.fst X.hom t)
  exact (pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))

theorem isSchemeTheoreticallyDominant_complexPoint (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) :
    IsSchemeTheoreticallyDominant (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
  have : IsDominant (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    have hinj : Function.Injective (σ.comp (algebraMap (𝓞 K) K)) := by
      rw [RingHom.coe_comp]; exact σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem flat_ker (S : Scheme.{0}) (P : Out.PolAV S) (m : ℕ) (hm : 1 ≤ m) :
    Flat (pullback (𝟙 P.A ^ m) η[P.A]).hom := by
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hfin : IsFinite ((𝟙 P.A ^ m)).left := GlobalTheory.MulFinite.isFinite_mulA
    (GlobalTheory.MulPull.mulPull_of_cube_of_symm GlobalTheory.AbLaw.CubeAssembly.cube_gen
      (GlobalTheory.exists_gen_negLB GlobalTheory.laws_without_cohomology.1)).1 GlobalTheory.laws_without_cohomology.2.2.1 gi S P m hm
  have hc := P.isAb.comm
  have hsm := P.isAb.smooth
  have hmon := GlobalTheory.AbLaw.MulN.isMonHom_mulA P.A m
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map ((𝟙 P.A ^ m))).left ∧
        Surjective ((Over.pullback t).map ((𝟙 P.A ^ m))).left := fun K _ _ t =>
    GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd gi K _
      (ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hfin)
  have hf := GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance
    inferInstance hfin fun K _ _ t => (hgeo K t).1
  have hp := (IsPullback.of_hasPullback (𝟙 P.A ^ m) η[P.A]).map (Over.forget S)
  have he : Flat (pullback.snd (𝟙 P.A ^ m) η[P.A]).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp hf
  have hw : (pullback.snd (𝟙 P.A ^ m) η[P.A]).left = (pullback (𝟙 P.A ^ m) η[P.A]).hom := by
    simpa using Over.w (pullback.snd (𝟙 P.A ^ m) η[P.A])
  rw [hw] at he
  exact he

theorem kill_complex (A' B' : Over (Sp ℂ)) [GrpObj A'] [GrpObj B'] (hA : IsAbelianScheme A')
    [IsSeparated B'.hom] [LocallyOfFiniteType B'.hom] (N : ℕ) (hN : 1 ≤ N) (φ : A' ⟶ B')
    (h : ∀ p : Over.mk (𝟙 (Sp ℂ)) ⟶ pullback (𝟙 A' ^ N) η[A'],
      p ≫ pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ = p ≫ 1) :
    pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ = 1 := by
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective _ A' N hA hunit
  have hp := (IsPullback.of_hasPullback ((𝟙 A' ^ N)) η[A']).map (Over.forget (Sp ℂ))
  have he : Etale (pullback.snd ((𝟙 A' ^ N)) η[A']).left :=
    MorphismProperty.of_isPullback (P := @Etale) hp het
  have hw : (pullback.snd ((𝟙 A' ^ N)) η[A']).left = (pullback (𝟙 A' ^ N) η[A']).hom := by
    simpa using Over.w (pullback.snd ((𝟙 A' ^ N)) η[A'])
  rw [hw] at he
  have : IsReduced (pullback (𝟙 A' ^ N) η[A']).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback (𝟙 A' ^ N) η[A']).hom
  refine Over.OverMorphism.ext ?_
  have : LocallyOfFiniteType ((pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ).left ≫ B'.hom) := by
    rw [Over.w]; infer_instance
  refine ext_of_apply_eq B'.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
    ((Over.w _).trans (Over.w _).symm)
  let p : Over.mk (𝟙 (Sp ℂ)) ⟶ pullback (𝟙 A' ^ N) η[A'] :=
    Over.homMk (pointOfClosedPoint (pullback (𝟙 A' ^ N) η[A']).hom z hz) (pointOfClosedPoint_comp _ _ _)
  have e := h p
  have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) e
  have hz' : p.left (IsLocalRing.closedPoint ℂ) = z := pointOfClosedPoint_apply _ z hz _
  simp only [Over.comp_left] at e'
  rw [← hz']
  exact e'

end GlobalTheory.TorsionKill

noncomputable section
namespace GlobalTheory.TorsionKill

def ptOf {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S}
    (y : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) : Over.mk t ⟶ A :=
  Over.homMk (y.left ≫ pullback.fst A.hom t) (by
    have hy : y.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y
    simp only [Over.mk_hom, Category.assoc, pullback.condition, reassoc_of% hy, Category.id_comp])

theorem ptOf_comp {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A B : Over S}
    (y : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) (f : A ⟶ B) :
    ptOf t (y ≫ (Over.pullback t).map f) = ptOf t y ≫ f := by
  ext
  simp [ptOf, pullback.lift_fst]

theorem ptOf_injective {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S} :
    Function.Injective (ptOf t (A := A)) := by
  intro y y' h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun q => q.left) h
  · have hy : y.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y
    have hy' : y'.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y'
    rw [hy, hy']

theorem ptOf_one {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S} [GrpObj A] :
    ptOf t (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) = 1 := by
  have e : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) =
      (toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback t)) ≫ (Over.pullback t).map η[A] := by
    rw [Hom.one_def, Category.assoc]; rfl
  rw [e, ptOf_comp, Hom.one_def, toUnit_unique (ptOf t _) (toUnit _)]

end GlobalTheory.TorsionKill

noncomputable section
namespace GlobalTheory.TorsionKill

theorem kill_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    IsMonHom G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ^ m = 1 → x ≫ G = 1 := by
  intro E _ _ _ H K _ _ σ A B G _ m hm hpt T x hx
  let inc : pullback (𝟙 A.t.G ^ m) η[A.t.G] ⟶ A.t.G := pullback.fst _ _
  suffices hY : inc ≫ G = 1 by
    have hx' : x ≫ (𝟙 A.t.G ^ m) = toUnit T ≫ η[A.t.G] := by
      rw [MonObj.comp_pow, Category.comp_id]; exact hx
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ G = 1
    rw [hY, MonObj.comp_one]
  have := flat_ker _ A.pol m hm
  have := isSchemeTheoreticallyDominant_complexPoint K σ
  have := B.ab.proper
  have := A.ab.proper
  have : IsSeparated B.t.G.hom := inferInstance
  refine eq_of_pullback_eq (spMap (σ.comp (algebraMap (𝓞 K) K))) ?_
  set t := spMap (σ.comp (algebraMap (𝓞 K) K)) with ht
  let F := Over.pullback t
  have hA' : IsAbelianScheme (F.obj A.t.G) := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A.t.G A.ab
  have : IsSeparated (F.obj B.t.G).hom := by change IsSeparated (pullback.snd _ _); infer_instance
  have : LocallyOfFiniteType (F.obj B.t.G).hom := by change LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have hpow : F.map (𝟙 A.t.G ^ m) = 𝟙 (F.obj A.t.G) ^ m := by
    simpa using map_pow (F.homMonoidHom (X := A.t.G) (M := A.t.G)) (𝟙 A.t.G) m
  have hinc : inc ≫ (𝟙 A.t.G ^ m) = 1 := by
    rw [show inc ≫ (𝟙 A.t.G ^ m) = pullback.snd (𝟙 A.t.G ^ m) η[A.t.G] ≫ η[A.t.G] from pullback.condition,
      toUnit_unique (pullback.snd (𝟙 A.t.G ^ m) η[A.t.G]) (toUnit _)]
    rfl
  have hFinc : F.map inc ≫ (𝟙 (F.obj A.t.G) ^ m) = toUnit _ ≫ η[F.obj A.t.G] := by
    rw [← hpow, ← F.map_comp, hinc, Functor.map_one]; rfl
  have key := kill_complex (F.obj A.t.G) (F.obj B.t.G) hA' m hm (F.map G) (fun p => by
    let y := p ≫ pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G]
    have hy1 : y ≫ 𝟙 (F.obj A.t.G) ^ m = 1 := by
      have c : pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ 𝟙 (F.obj A.t.G) ^ m =
          pullback.snd (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ η[F.obj A.t.G] := pullback.condition
      simp only [y, Category.assoc, c]
      rw [← Category.assoc, toUnit_unique (p ≫ pullback.snd _ _) (toUnit _)]
      rfl
    have hyp : ptOf t y ^ m = 1 := by
      rw [← Category.comp_id (ptOf t y), ← MonObj.comp_pow, ← ptOf_comp, hpow, hy1, ptOf_one]
    have h2 : ptOf t (y ≫ F.map G) = ptOf t 1 := by
      rw [ptOf_comp, ptOf_one]; exact hpt _ hyp
    have h3 := ptOf_injective t h2
    simp only [y, Category.assoc] at h3
    rw [h3, MonObj.comp_one])
  have hl : F.map inc = pullback.lift (F.map inc) (toUnit _) hFinc ≫ pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).symm
  rw [F.map_comp, Functor.map_one, hl, Category.assoc, key, MonObj.comp_one]

end GlobalTheory.TorsionKill
end
end
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_qcqs_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hcp hqs haff
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hc' : IsLimit ((Over.conePost G i₀).obj c) := Over.isLimitConePost i₀ hc
  haveI := hcp i₀
  haveI := hqs i₀
  have hcore := GlobalTheory.T.cohomologyContinuous_baseChange_qcqs R F hF (G.obj i₀) (Over i₀) (Over.post G) ((Over.conePost G i₀).obj c) hc'
    (fun j => haff _ _ j.hom) (G.obj i₀) (𝟙 _)
  have hb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  haveI : IsIso (sch.map (𝟙 (G.obj i₀))) := inferInstance
  apply GlobalTheory.T.cohomologyContinuousOnCone_of_whisker R F I (Over i₀) (Over.forget i₀) (G ⋙ sch) (sch.mapCone c)
  · intro i
    exact ⟨Over.mk (IsCofiltered.minToRight i i₀), ⟨IsCofiltered.minToLeft i i₀⟩⟩
  · let α : Over.post G ⋙ bc (sch.map (𝟙 (G.obj i₀))) ⟶ Over.forget i₀ ⋙ G ⋙ sch :=
      { app := fun j => pullback.snd _ _
        naturality := fun j k f => by
          simp only [Functor.comp_map, bc, pullback.map]
          erw [pullback.lift_snd]
          rfl }
    refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F (Over i₀) _ _ ((bc (sch.map (𝟙 (G.obj i₀)))).mapCone ((Over.conePost G i₀).obj c))
      ((sch.mapCone c).whisker (Over.forget i₀)) α (pullback.snd _ _) ?_ ?_ ?_).1 hcore
    · intro j
      simp only [Functor.mapCone_π_app, Cone.whisker_π, bc, pullback.map]
      erw [pullback.lift_snd]
      rfl
    · intro j
      exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
    · exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
end GlobalTheory.EtC
end

end

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_of_qcqs_affine
  | exact GlobalTheory.EtC.contCone_of_qcqs_affine
  | (intros; apply GlobalTheory.EtC.contCone_of_qcqs_affine <;> assumption)

end
end
