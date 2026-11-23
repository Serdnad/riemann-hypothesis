module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetRationalApproximation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOneFormsIsBaseChangeTangentRep
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle804
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem pow_indep_tensor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n →
    ∀ (v : AwayP p) (c : Fin G.n → Qv v ⊗[ℚ] G.F),
      ∑ i, iotaF G v (c i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = 0 → c = 0 := by
  intro p _ G γ hn v c hc

  let ψ : (Fin G.n → G.F) →ₗ[ℚ] G.C :=
    { toFun := fun f => ∑ i, f i • γ ^ (i : ℕ)
      map_add' := fun f g => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun q f => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_assoc] }
  have li : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hn] at this
    exact this
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    exact funext ((Fintype.linearIndependent_iff.mp li) f hf)
  have hinj : Function.Injective (ψ.lTensor (Qv v)) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ hψ
  let e := TensorProduct.piRight ℚ ℚ (Qv v) (fun _ : Fin G.n => G.F)
  have key : ∀ t : Qv v ⊗[ℚ] (Fin G.n → G.F),
      ∑ i, iotaF G v (e t i) * (1 : Qv v) ⊗ₜ[ℚ] γ ^ (i : ℕ) = ψ.lTensor (Qv v) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), ← hx, ← hy, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, map_add (f := _), add_mul]
    | tmul q f =>
      rw [LinearMap.lTensor_tmul]
      have : ∀ i, e (q ⊗ₜ[ℚ] f) i = q ⊗ₜ[ℚ] f i := fun i => rfl
      simp only [this, iotaF_tmul, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum, Algebra.smul_def]

  have h0 : ψ.lTensor (Qv v) (e.symm c) = 0 := by
    rw [← key, LinearEquiv.apply_symm_apply]; exact hc
  have : e.symm c = 0 := hinj (by rw [h0, map_zero])
  rw [← e.apply_symm_apply c, this, map_zero]

end GlobalTheory.OrbFinAf
end
end

section

noncomputable section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem iotaF_injective (G : HTGroup p) (v : AwayP p) : Function.Injective (iotaF G v) := by
  have hf : Function.Injective (IsScalarTower.toAlgHom ℚ G.F G.C).toLinearMap :=
    (algebraMap G.F G.C).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := Qv v) _ hf

def intFAlgMap (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    v.1.adicCompletionIntegers ℚ →+* intF G v h1 hm :=
  ((algebraMap (Qv v) (Qv v ⊗[ℚ] G.F)).comp (v.1.adicCompletionIntegers ℚ).subtype).codRestrict _ fun c => by
    rw [mem_intF]
    intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      map_smul, Finsupp.smul_apply, smul_eq_mul, map_one]
    exact mul_mem c.2 (h1 i)

def intFCoord (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    letI := (intFAlgMap G v h1 hm).toAlgebra
    intF G v h1 hm →ₗ[v.1.adicCompletionIntegers ℚ] (Fin (Module.finrank ℚ G.C) → v.1.adicCompletionIntegers ℚ) :=
  letI := (intFAlgMap G v h1 hm).toAlgebra
  { toFun := fun m i => ⟨(basV G v).repr (iotaF G v m) i, (mem_intF G v h1 hm m).1 m.2 i⟩
    map_add' := fun a b => by
      funext i; apply Subtype.ext
      simp [map_add (f := _)]
    map_smul' := fun c m => by
      funext i; apply Subtype.ext
      show (basV G v).repr (iotaF G v (algebraMap (Qv v) (Qv v ⊗[ℚ] G.F) (c : Qv v) * m)) i =
        (c : Qv v) * (basV G v).repr (iotaF G v m) i
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, map_smul]
      rfl }

theorem intFCoord_injective (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    Function.Injective (intFCoord G v h1 hm) := by
  intro a b hab
  apply Subtype.ext
  apply iotaF_injective G v
  apply (basV G v).repr.injective
  refine Finsupp.ext fun i => ?_
  exact congrArg Subtype.val (congrFun hab i)

theorem intF_finite (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    letI := (intFAlgMap G v h1 hm).toAlgebra
    Module.Finite (v.1.adicCompletionIntegers ℚ) (intF G v h1 hm) :=
  letI := (intFAlgMap G v h1 hm).toAlgebra
  Module.Finite.of_injective (intFCoord G v h1 hm) (intFCoord_injective G v h1 hm)

theorem intF_finite_maximal : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)),
    Set.Finite {I : Ideal (intF G v h1 hm) | I.IsMaximal} := by
  intro p _ G v h1 hm
  letI := (intFAlgMap G v h1 hm).toAlgebra
  haveI := intF_finite G v h1 hm
  exact ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.finite_maximal_ideals_of_finite (R := v.1.adicCompletionIntegers ℚ) (intF G v h1 hm)

end GlobalTheory.OrbFinAf
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitNorm_gramDet_plane_reduction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x z : Fin M → E, hE σ J x x ≠ 0 → IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) → hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0 := by
  first | exact @GlobalTheory.PlaneNormReduce.reduce | exact GlobalTheory.PlaneNormReduce.reduce | (intros; apply GlobalTheory.PlaneNormReduce.reduce <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_common_hermitianGramDetTwoVectors_ne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  first | exact @GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | exact GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | (intros; apply GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitNorm_gramDet_rational_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → ∀ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) → IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) ∧ IsUnitNorm K σ (-(inclR K (gram2E σ J z y))) := by
  first | exact @GlobalTheory.PlaneNormApprox.approx | exact GlobalTheory.PlaneNormApprox.approx | (intros; apply GlobalTheory.PlaneNormApprox.approx <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weil_representation_l2_isometry : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {G : Type} [Group G]
    (om : G →* Module.End ℂ ((κ → AF F) → ℂ)), (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) → IsUnitaryOn (adeleClass F) om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A F μ Φ := by
  first | exact @GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn | exact GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn | (intros; apply GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn <;> assumption)
end

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.isStandardArchimedeanAddChar_of_isStandardTraceAdelic : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  first | exact @GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd | exact GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd | (intros; apply GlobalTheory.WeilL2Words.StdArch.isStdInf_of_isStd <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

theorem _root_.GlobalTheory.T.whittakerBumpArchimedeanFactor_contDiffOn_invertible : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (f : Lie E n → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ invSet E n → ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := by
  first | exact @GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet | exact GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet | (intros; apply GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
open GlobalTheory.AbTan GlobalTheory.AbTan.Transl GlobalTheory.TanForms GlobalTheory.InvForm

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvSpan

variable {R : Type} [CommRing R]

theorem dVal_smul {B D : Type} [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]
    (φ : B →ₐ[R] DualNumber D) (b : B) (m : Ω[B⁄R]) : dVal φ (b • m) = redHom φ b * dVal φ m := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  exact (map_smul (Derivation.liftKaehlerDifferential _) b m).trans (Algebra.smul_def _ _)

variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W]

def tr (A : Over (Sp R)) [GrpObj A] : TrTy A := fun B M ↦ tau A B M

theorem tr_bij : TrBij A (tr A) := fun _ _ _ _ _ _ _ _ P hP ↦ bijOn_tau A P hP

theorem tr_nat : TrNat A (tr A) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ α f β hβ P hP z hz ↦
  tau_natural A α f β hβ P hP z hz

theorem exists_tangent (T : TanRep A W) (U : A.left.affineOpens) {D : Type} [CommRing D] [Algebra R D]
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) :
    ∃ z : Sp (DualNumber D) ⟶ A.left, Lifts A.hom (unitPt A D) z ∧
      tau A D D (spMap (redHom φ) ≫ affPt A.hom U) z =
        spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U ∧
      ∀ w, T.Φ z w = dVal φ (eU T (tr A) U w) := by
  letI := opMod (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R]
  haveI : IsCentralScalar (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R] := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨hz0, hτz0⟩ := back_spec (τ := tr A) U tr_bij (pt A U (KaehlerDifferential.D R (Sec A.hom U.1)))
    (pt_lifts A U _)
  let α : Sec A.hom U.1 →ₐ[R] D := { redHom φ with commutes' := redHom_algebraMap φ }
  have hf : ∀ (b : Sec A.hom U.1) (m : Ω[Sec A.hom U.1⁄R]), (dVal φ).toAddMonoidHom (b • m) =
      redHom φ b • (dVal φ).toAddMonoidHom m := fun b m ↦ dVal_smul φ b m
  let β := sumHom (redHom φ) (dVal φ).toAddMonoidHom hf
  have hβ : IsSum β α (dVal φ) := sumHom_isSum _ (dVal φ).toAddMonoidHom hf
  obtain ⟨hl, hnat⟩ := tau_natural A α (dVal φ) β hβ (affPt A.hom U) (affPt_w A.hom U) _ hz0
  have hpt : spMap β ≫ pt A U (KaehlerDifferential.D R (Sec A.hom U.1)) =
      spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U := by
    rw [pt, ← Category.assoc, sp_comp]
    congr 2
    refine RingHom.ext fun b ↦ ?_
    rw [RingHom.comp_apply, show TanForms.derHom (KaehlerDifferential.D R (Sec A.hom U.1)) b =
      TrivSqZeroExt.inl b + TrivSqZeroExt.inr (KaehlerDifferential.D R (Sec A.hom U.1) b) from rfl, map_add,
      hβ.1, hβ.2, dVal_D]
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq (φ b)
  refine ⟨_, hl, ?_, fun w ↦ ?_⟩
  · refine hnat.trans ?_
    rw [← hpt]
    exact congrArg _ hτz0
  · rw [T.nat α (dVal φ) β hβ _ hz0]
    rfl

def form (T : TanRep A W) (w : W) : GlobForm A.hom :=
  ⟨fun V ↦ eU T (tr A) V.unop w, fun _ _ a ↦ eU_nat T tr_bij tr_nat a w⟩

theorem red_w (U : A.left.affineOpens) {D : Type} [CommRing D] [Algebra R D]
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) :
    (spMap (redHom φ) ≫ affPt A.hom U) ≫ A.hom = spMap (algebraMap R D) := by
  rw [Category.assoc, affPt_w, sp_comp]
  exact congrArg spMap (RingHom.ext (redHom_algebraMap φ))

theorem isInv_form [IsCommMonObj A] (T : TanRep A W) (w : W) : IsInv A (form T w) := by
  intro D _ _ U V φ ψ p q q₀ hp hq hpq
  obtain ⟨z, hz, hτ, hΦ⟩ := exists_tangent T U φ
  obtain ⟨z', hz', hτ', hΦ'⟩ := exists_tangent T V ψ
  change dVal φ (eU T (tr A) U w) = dVal ψ (eU T (tr A) V w)
  rw [← hΦ, ← hΦ']
  suffices h : z = z' by rw [h]
  rw [tau_eq A _ (red_w U φ) z hz.1, ← hp] at hτ
  rw [tau_eq A _ (red_w V ψ) z' hz'.1, ← hpq] at hτ'
  let c : ovT R D D ⟶ ovT R D D :=
    Over.homMk (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (TrivSqZeroExt.fstHom D D D).toRingHom) (by
      rw [Category.assoc, fst_w]
      exact sp_comp _ _)
  let p' : ovT R D D ⟶ A := p
  let q' : ovT R D D ⟶ A := q
  have e1 : Over.homMk (U := ovT R D D) (V := A)
      (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom φ) ≫ affPt A.hom U) (inl_w A _ (red_w U φ)) =
      c ≫ p' := by
    ext
    change spMap _ ≫ spMap (redHom φ) ≫ affPt A.hom U = (spMap _ ≫ spMap _) ≫ p.left
    rw [hp, Category.assoc, ← Category.assoc (spMap _) (spMap (φ : Sec A.hom U.1 →+* DualNumber D)), sp_comp]
    rfl
  have e2 : Over.homMk (U := ovT R D D) (V := A)
      (spMap (TrivSqZeroExt.inlHom D D) ≫ spMap (redHom ψ) ≫ affPt A.hom V) (inl_w A _ (red_w V ψ)) =
      c ≫ (p' * q') := by
    ext
    change spMap _ ≫ spMap (redHom ψ) ≫ affPt A.hom V = (spMap _ ≫ spMap _) ≫ (p * q).left
    rw [hpq, Category.assoc, ← Category.assoc (spMap _) (spMap (ψ : Sec A.hom V.1 →+* DualNumber D)), sp_comp]
    rfl
  have e3 : c ≫ q' = q' := by
    ext
    change (_ ≫ _) ≫ q.left = q.left
    rw [hq, Category.assoc]
    change _ ≫ _ ≫ spMap (TrivSqZeroExt.inlHom D D) ≫ q₀ = _
    rw [← Category.assoc (spMap _) (spMap _) q₀, fst_inl, Category.id_comp]
  rw [e1] at hτ
  rw [e2, MonObj.comp_mul, e3] at hτ'
  have k1 : (c ≫ p') * Over.homMk (U := ovT R D D) (V := A) z hz.1 = p' := Over.OverMorphism.ext hτ
  have k2 : (c ≫ p') * q' * Over.homMk (U := ovT R D D) (V := A) z' hz'.1 = p' * q' :=
    Over.OverMorphism.ext hτ'
  have k3 : Over.homMk (U := ovT R D D) (V := A) z hz.1 = Over.homMk (U := ovT R D D) (V := A) z' hz'.1 := by
    rw [mul_right_comm] at k2
    exact mul_left_cancel (k1.trans (mul_right_cancel k2).symm)
  exact congrArg CommaMorphism.left k3

theorem span_eq_top_of_tanRep [IsCommMonObj A] (T : TanRep A W) (U : AffOp A.left) :
    Submodule.span (Sec A.hom U.unop.1) (Set.range fun w : InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using (eU_isBaseChange T tr_bij tr_nat U.unop).inductionOn with
  | tmul w => exact Submodule.subset_span ⟨⟨form T w, isInv_form T w⟩, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ _ (hn trivial)
  | add a b ha hb => exact add_mem (ha trivial) (hb trivial)

theorem span_invForm_eq_top : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left,
    Submodule.span (Sec A.hom U.unop.1)
      (Set.range fun w : GlobalTheory.InvForm.InvForm A ↦ evForm A.hom U w.1) = ⊤ := by
  intro R _ A _ g hA _ U
  have := hA.comm
  obtain ⟨W, _, _, -, -, ⟨T⟩⟩ := GlobalTheory.T.exists_tangentRepresentation_smooth_groupScheme R A hA.smooth
  exact span_eq_top_of_tanRep T U

end GlobalTheory.InvSpan
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HeckeSym

theorem grpSchemeSquareProductMap_comm_swap {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') :
    GlobalTheory.UPel.HT.Hecke.sq2 ψ ≫ (lift (snd A' A') (fst A' A')).left =
      (lift (snd A A) (fst A A)).left ≫ GlobalTheory.UPel.HT.Hecke.sq2 ψ := by
  unfold GlobalTheory.UPel.HT.Hecke.sq2
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp

theorem descended_symm : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) := by
  intro p _ D R _ b M S s o A' _ _ ψ G hA' hψ hG m P' hP' H r₁ r₂
  set sw' := (lift (snd A' A') (fst A' A')).left with hsw'
  set sw := (lift (snd o.A o.A) (fst o.A o.A)).left with hsw
  set q := GlobalTheory.UPel.HT.Hecke.sq2 ψ with hq
  have hQ : (P'.pull sw').IsLB := pull_isLB hP' sw'

  have ax : ∀ (e₁ e₂ : A' ⟶ G2 A'), e₁ ≫ lift (snd A' A') (fst A' A') = e₂ →
      (∃ t : (P'.pull e₂.left).Gen, t.IsGen) → ∃ t : ((P'.pull sw').pull e₁.left).Gen, t.IsGen := by
    intro e₁ e₂ he ⟨t, ht⟩
    have hc : ∀ k : PUnit, (fun _ : PUnit => e₁.left) k ≫ sw' = 𝟙 _ ≫ (fun _ : PUnit => e₂.left) k := by
      intro _
      rw [Category.id_comp, hsw', ← Over.comp_left, he]
    have iso : LBIso ((P'.pull sw').pull e₁.left) (P'.pull e₂.left) :=
      LBIso.chartPull (chartPullLinComb P' sw' (fun _ => e₁.left) (fun _ => e₂.left) (fun _ => 1) (𝟙 _) hc)
        (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP' _))
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP' _) (pull_isLB hQ _) iso.symm t ht
  have a₁ := ax (lift (1 : A' ⟶ A') (𝟙 A')) (lift (𝟙 A') (1 : A' ⟶ A')) (by ext <;> simp) r₂
  have a₂ := ax (lift (𝟙 A') (1 : A' ⟶ A')) (lift (1 : A' ⟶ A') (𝟙 A')) (by ext <;> simp) r₁

  have E := grpSchemeSquareProductMap_comm_swap ψ
  have hPow : (GlobalTheory.UPel.HT.Hecke.lbPow o.P m).IsLB := DVR.linComb_isLB _ o.isLB _ _
  have step1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m)
      (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb o.symm _ _
  have step2 : LBIso (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1))
      ((P'.pull sw').pull q) := by
    refine LBIso.chartPull (h := sw)
      (chartPullLinComb o.P sw (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) sw (fun _ => by simp))
      (chartPullLinComb P' sw' (fun _ : PUnit => q) (fun _ : PUnit => q) (fun _ => 1) sw (fun _ => E)) H
  have hmid : (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1)).IsLB :=
    DVR.linComb_isLB _ (pull_isLB o.isLB _) _ _
  have key : LBIso (P'.pull q) ((P'.pull sw').pull q) :=
    LBIso.trans (pull_isLB hP' q) hPow (pull_isLB hQ q) H.symm
      (LBIso.trans hPow hmid (pull_isLB hQ q) step1 step2)
  exact GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A A' G ψ o.ab hA' hψ hG P' (P'.pull sw') hP' hQ r₁ r₂ a₁ a₂ key

end GlobalTheory.HeckeSym
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem rowCutInf_unipB_mul_levSetInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n),
    ∀ g ∈ levSetInf E n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) =
      rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧
    ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  intro E _ _ n ρ g hg
  have hw : ∀ w, compGL w g ∈ levSet n (ρ + 1) := hg
  have hc : ∀ w (x : GL (Fin n) (Cinf E)) j,
      rowCut ρ ((compGL w x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) j =
        rowCutInf ρ (x : Matrix (Fin n) (Fin n) (Cinf E)) j w := by
    intro w x j
    unfold rowCut rowCutInf
    split_ifs <;> rfl
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    have hmem : ∀ w, compGL w u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n) := by
      intro w
      refine (GlobalTheory.SmGL.mem_unipB ℂ).2 ⟨fun i j h => ?_, fun i => ?_⟩
      · rw [compGL_apply, hu0 i j h]; rfl
      · rw [compGL_apply, hu1 i]; rfl
    funext j w
    rw [← hc, ← hc, map_mul]
    exact congrFun ((truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).1 _ (hmem w)) j
  · intro w
    obtain ⟨j, hj, hne⟩ := (truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).2
    exact ⟨j, hj, by rwa [← hc]⟩

end GlobalTheory.JSW.MirCinf
end
