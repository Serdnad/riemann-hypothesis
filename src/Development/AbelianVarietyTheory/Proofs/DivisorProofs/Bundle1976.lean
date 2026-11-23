module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1931
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle057
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMarkedPairClassesDegreeOneTermNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftLowerBoundOffBasePlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle377
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.MBLow.Cl

namespace GlobalTheory.MBLow.Cl

theorem exists_NF : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g), ∃ u τ a b c W, NF x hg u τ a b c W := by
  intro g x hg
  subst hg
  obtain ⟨⟨τ, M, a, b, c, hab, hc, -, u, h₁, h₂, h₃, h₄, h₅, h₆⟩, -⟩ :=
    GlobalTheory.KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all x
  exact ⟨u, τ, a, b, c, fun i => (2 * Real.pi * Complex.I : ℂ)⁻¹ • M i, h₁, h₂, hab.1, hab.2, hc, h₃, h₄, h₅, h₆⟩

end GlobalTheory.MBLow.Cl
end

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU


theorem _root_.GlobalTheory.T.exists_darbouxChangeOperatorWithDouble_lowerUnipotent : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ C : Matrix κ κ F, Cᵀ = C → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1)) S S' := by
  first | exact @GlobalTheory.TowU.UnipOp.main | exact GlobalTheory.TowU.UnipOp.main | (intros; apply GlobalTheory.TowU.UnipOp.main <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU


theorem _root_.GlobalTheory.T.weylElement_realised_by_fourierTransforms : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  first | exact @GlobalTheory.TowU.realised_weyl2 | exact GlobalTheory.TowU.realised_weyl2 | (intros; apply GlobalTheory.TowU.realised_weyl2 <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit


open GlobalTheory.SWQ GlobalTheory.PoissonReindex in
theorem GlobalTheory.SWLit.tamagawa_eq_map_pi : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (e : κ ≃ Fin N) (ν : Measure (AF F)), GlobalTheory.SWQ.IsCov1 ν → ∀ μ : Measure (κ → AF F), IsTamagawa F κ μ → μ = Measure.map (GlobalTheory.PoissonReindex.reidx (F := F) e) (GlobalTheory.SWQ.muV N ν) := by
  intro F _ _ κ _ N e ν hν μ ⟨hμ, 𝓕, h𝓕1, h𝓕⟩
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨hHaar, hmem, -, -, D, hDm, hD, hD1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  haveI := hHaar
  haveI := hμ
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)
  have hr := Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))
  set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))
  let L := (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range
  let L' := AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))
  have hmap : ∀ g : L', T g.1 ∈ L := by
    intro g
    obtain ⟨ξ, hξ⟩ := (hmem g.1).1 g.2
    exact ⟨fun i => ξ (e i), by rw [hξ]; rfl⟩
  let φ : L' → L := fun g => ⟨T g.1, hmap g⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => Subtype.ext (T.injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, η, rfl⟩
    refine ⟨⟨rat fun j => η (e.symm j), (hmem _).2 ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
    funext i
    show algebraMap F (AF F) (η (e.symm (e i))) = algebraMap F (AF F) (η i)
    rw [e.symm_apply_apply]
  have hmp : MeasurePreserving Tm.symm (Measure.map Tm (muV N ν)) (muV N ν) :=
    MeasurePreserving.symm Tm ⟨Tm.measurable, rfl⟩
  have hD' : IsAddFundamentalDomain L (Tm.symm ⁻¹' D) (Measure.map Tm (muV N ν)) := by
    refine hD.preimage_of_equiv hmp.quasiMeasurePreserving hφ fun g x => ?_
    show T.symm (T g.1 + x) = g.1 + T.symm x
    rw [map_add (f := _), T.symm_apply_apply]
  have hD'1 : Measure.map Tm (muV N ν) (Tm.symm ⁻¹' D) = 1 := by
    rw [hmp.measure_preimage hDm.nullMeasurableSet, hD1]
  have hac : μ ≪ Measure.map Tm (muV N ν) := by
    rw [hr]
    exact Measure.smul_absolutelyContinuous
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  haveI : Countable L := by
    have : Countable (Set.range (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ)) :=
      (Set.countable_range _).to_subtype
    exact this
  have h1 : μ (Tm.symm ⁻¹' D) = 1 := by
    rw [← h𝓕1]
    exact (hD'.mono hac).measure_eq h𝓕
  have hr1 : r = 1 := by
    rw [hr, Measure.smul_apply, hD'1] at h1
    simpa using h1
  rw [hr1, one_smul] at hr
  exact hr
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cuspidalLetterRealExponent_eq_zero_iff_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Letter E), 1 ≤ x.1 → (rexp x = 0 ↔ x.2.IsUnitary) ∧ (x.2.IsUnitary ↔ (CG.mk x.2).IsUnitary) := by
  first | exact @GlobalTheory.ResW.rexp_eq_zero_iff_isUnitary | exact GlobalTheory.ResW.rexp_eq_zero_iff_isUnitary | (intros; apply GlobalTheory.ResW.rexp_eq_zero_iff_isUnitary <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.finite_markedPairClasses_degreeOne_term_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → Set.Finite {Q : Cls G | (∃ μ, (Quot.out Q).Mark μ) ∧ (Quot.out Q).term L.K.toSubgroup f 1 K' f' ≠ 0} := by
  first | exact @GlobalTheory.LKCx.FiniteClassIntegralRoots.finite_cls_term_one_a_one | exact GlobalTheory.LKCx.FiniteClassIntegralRoots.finite_cls_term_one_a_one | (intros; apply GlobalTheory.LKCx.FiniteClassIntegralRoots.finite_cls_term_one_a_one <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.Overlap

section Kernel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

theorem kZero_zero (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (x₁ x₂ : Frame X.Ψ r) :
    kZero X idx x₁ x₂ (0 : Fin n → Fin g → ℂ) 0 =
      ∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹ := by
  unfold kZero
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h : ∀ k, dblz X idx x₁ x₂ (0 : Fin n → Fin g → ℂ) 0 τ k = 0 := fun k => by
    have e : (fun a : Fin r => if (a : ℕ) < X.p0 then (0 : Fin n → Fin g → ℂ) k (idx.symm (τ, a))
        else (0 : Fin n → Fin g → ℂ) k (idx.symm (τ, a))) = 0 := by
      funext a
      simp
    funext c
    simp only [dblz, Matrix.of_apply, e, mulVec_zero, smul_zero]
  simp only [h, mulVec_zero, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one]

theorem aLin_move {x₁ x₂ y₁ y₂ : Frame X.Ψ r} (τ : X.Ψ) {u : Matrix (Fin r) (Fin r) ℂ} (hu : IsUnit u.det)
    (hh : ∀ v w, hermC τ.1 X.Gm (u *ᵥ v) (u *ᵥ w) = hermC τ.1 X.Gm v w)
    (h₁ : mat y₁ τ = u * mat x₁ τ) (h₂ : mat y₂ τ = u * mat x₂ τ) :
    aLin X y₁ y₂ τ * u = aLin X x₁ x₂ τ := by
  refine Matrix.ext_of_mulVec_single fun c => ?_
  generalize (Pi.single c 1 : Fin r → ℂ) = w
  funext a
  rw [← mulVec_mulVec]
  by_cases ha : (a : ℕ) < X.p0
  · rw [DblPoint.aLin_mulVec_of_lt X _ _ _ _ ha, DblPoint.aLin_mulVec_of_lt X _ _ _ _ ha, h₂, ← hh w]
    rfl
  · rw [DblPoint.aLin_mulVec_of_not_lt X _ _ _ _ ha, DblPoint.aLin_mulVec_of_not_lt X _ _ _ _ ha, h₁,
      Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem det_move {x₁ x₂ y₁ y₂ : Frame X.Ψ r} (τ : X.Ψ) {u : Matrix (Fin r) (Fin r) ℂ}
    (hu : u.det * conj u.det = 1)
    (hh : ∀ v w, hermC τ.1 X.Gm (u *ᵥ v) (u *ᵥ w) = hermC τ.1 X.Gm v w)
    (h₁ : mat y₁ τ = u * mat x₁ τ) (h₂ : mat y₂ τ = u * mat x₂ τ) :
    (aLin X y₁ y₂ τ).det * (aAnti X y₁ y₂ τ).det = (aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det := by
  have hu' : IsUnit u.det := IsUnit.of_mul_eq_one _ hu
  have e : ∀ z₁ z₂ : Frame X.Ψ r, (aAnti X z₁ z₂ τ).det = conj (aLin X z₂ z₁ τ).det := fun z₁ z₂ => by
    rw [DblPoint.aLin_swap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_conj]
  rw [e, e, ← aLin_move X τ hu' hh h₁ h₂, ← aLin_move X τ hu' hh h₂ h₁, det_mul, det_mul, map_mul]
  linear_combination (-((aLin X y₁ y₂ τ).det * conj (aLin X y₂ y₁ τ).det)) * hu

end Kernel

variable {D : D7} {S T : HSp D} (C : GlobalTheory.Ker.Ctx S T)

theorem kZero_mvB {B B' : C.Bas} (hB : C.IsB B) (u : GA D T) :
    kZero C.X C.idx (C.xB (C.mvB u B)) (C.xB (C.mvB u B')) (0 : Fin S.rank → Fin C.g → ℂ) 0 =
      kZero C.X C.idx (C.xB B) (C.xB B') (0 : Fin S.rank → Fin C.g → ℂ) 0 := by
  rw [kZero_zero, kZero_zero]
  refine Finset.prod_congr rfl fun σ _ => ?_
  obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
  have hU := GlobalTheory.Ker.ONBasis.compAt_unitary C τ u
  have hm : ∀ A : C.Bas, mat (C.xB (C.mvB u A)) (C.m.e τ) =
      (compAt C.θ τ (Formalism.L2.Theta.mt T u)).map conj * mat (C.xB A) (C.m.e τ) := fun A => by
    rw [GlobalTheory.Ker.ONBasis.mat_xB, GlobalTheory.Ker.ONBasis.mat_xB, ← Matrix.map_mul]
    rfl
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T u) = U at hU hm
  have hG : (gramAt D T τ).det ≠ 0 := by
    intro h0
    have h1 := congrArg det (hB τ)
    have h2 := congrArg det (GlobalTheory.Ker.ONBasis.sgnM_sq C.X)
    rw [det_mul, det_mul, h0, mul_zero, zero_mul] at h1
    rw [det_mul, ← h1, zero_mul, det_one] at h2
    exact zero_ne_one h2
  rw [det_move C.X (C.m.e τ) (u := U.map conj) ?_ ?_ (hm B) (hm B')]
  · have h1 := congrArg det hU
    rw [det_mul, det_mul, det_conjTranspose] at h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_conj]
    apply mul_right_cancel₀ hG
    rw [one_mul]
    refine Eq.trans ?_ h1
    rw [Complex.star_def]
    ring
  · intro v w
    have e : ∀ v : Fin T.rank → ℂ, U.map conj *ᵥ v = fun a => conj ((U *ᵥ star v) a) := fun v => by
      funext a
      simp [mulVec, dotProduct]
    have e' : ∀ v : Fin T.rank → ℂ, v = fun a => conj (star v a) := fun v => by
      funext a
      simp
    rw [e, e, GlobalTheory.Ker.ONBasis.hermC_conj]
    conv_rhs => rw [e' v, e' w, GlobalTheory.Ker.ONBasis.hermC_conj, ← hU]
    rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star (star v)) Uᴴ]

theorem ipO_Th {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {x₁ x₂ : Frame C.X.Ψ T.rank} (h₁ : x₁ ∈ C.X.dom) (h₂ : x₂ ∈ C.X.dom) {φ₁ φ₂ : TF S.rank C.g}
    (s₁ : GlobalTheory.SW.IsSB φ₁) (s₂ : GlobalTheory.SW.IsSB φ₂) :
    GlobalTheory.Ker.ipO μ 𝓕 (C.Th x₁ φ₁) (C.Th x₂ φ₂) =
      dbl C.X C.bas C.idx φ₁ φ₂ 0 * kZero C.X C.idx x₁ x₂ (0 : Fin S.rank → Fin C.g → ℂ) 0 := by
  have h0 : GlobalTheory.Ker.IsRealPt (0 : WO S T) := Matrix.map_zero _ (map_zero _)
  have h := GlobalTheory.Ker.GaussKer.ipO_rho_Th D S T C μ 𝓕 hμ x₁ h₁ x₂ h₂ φ₁ φ₂ s₁ s₂ 0 0 h0 h0
  have hr : ∀ f, C.rho 0 f = f := fun f => by
    funext w
    simp [GlobalTheory.Ker.Ctx.rho, heisO, symplOH, symplO, hO]
  have hz : ∀ x, C.zOf x (0 : WO S T) = 0 := fun x => by
    funext k i
    simp [GlobalTheory.Ker.Ctx.zOf, GlobalTheory.Ker.zR, GlobalTheory.Ker.Ctx.realPt, compAt, hermC, mulVec, dotProduct]
  have hg : ∀ x, GlobalTheory.Ker.gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := fun x => by
    simp [GlobalTheory.Ker.gaussR, hx]
  rw [hr, hr, hz, hz, hg, hg] at h
  have e : (fun (k : Fin S.rank) (i : Fin C.g) => conj ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [h, e, map_one, one_mul, one_mul]

theorem isBasOf_unique {W : HSp D} {X : Data D.host.E W.rank} (hm : IsMod W rfl X) {q0 : ℕ}
    (hq : X.p0 + q0 = W.rank) {x : Frame X.Ψ W.rank} {B B' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (h : IsBasOf W rfl X hq x B) (h' : IsBasOf W rfl X hq x B') : B = B' := by
  funext ρ
  ext a i
  have hτ : tauE D ρ ∈ X.Ψ := (hm.psi _).2 ⟨ρ, rfl⟩
  by_cases hi : (i : ℕ) < q0
  · rw [h ρ ⟨_, hτ⟩ rfl (Sum.inl ⟨i, hi⟩) i a rfl, h' ρ ⟨_, hτ⟩ rfl (Sum.inl ⟨i, hi⟩) i a rfl]
  · have h1 : (i : ℕ) - q0 < X.p0 := by have := i.2; omega
    have h2 : (i : ℕ) = q0 + ((i : ℕ) - q0) := by omega
    rw [h ρ ⟨_, hτ⟩ rfl (Sum.inr ⟨_, h1⟩) i a h2, h' ρ ⟨_, hτ⟩ rfl (Sum.inr ⟨_, h1⟩) i a h2]

end GlobalTheory.AdTh.Overlap


open GlobalTheory.AdTh.Overlap in
theorem GlobalTheory.AdTh.inner_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∃ G : Frame X.Ψ r → Frame X.Ψ r → ℂ, ∀ x x' : Frame X.Ψ r, IsONFr X x → IsONFr X x' → G x x' ≠ 0 ∧ (∀ u : GA D W, G (frMove θ W hr X u x) (frMove θ W hr X u x') = G x x') ∧ ∀ v : TF V.rank g, GlobalTheory.SW.IsSB v → v ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ y y' : Frame X.Ψ r, IsONFr X y → IsONFr X y' → ∀ (f f' : WO V W → ℂ) (κ κ' : ℂ), IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → Reads θ V W hr X bas idx f (κ • v) y → Reads θ V W hr X bas idx f' (κ' • v) y' → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∫ w in 𝓕, f w * conj (f' w) ∂μ = κ * conj κ' * (c * G y y') := by
  intro D ψ θ V W r g hr X bas idx hstd hinf hV he hm hs
  subst hr
  obtain ⟨X', m, hq', hq, bas', idx', hs', -, -, -, -, -, -, H⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hinf he hV hm hs
  let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs', he⟩
  let Bx : Frame X.Ψ W.rank → C.Bas := fun x => Classical.epsilon fun B => IsBasOf W rfl X hq x B
  have hBx : ∀ x, IsONFr X x → IsBasOf W rfl X hq x (Bx x) := fun x hx => Classical.epsilon_spec (H x hx).1
  have hB : ∀ x, IsONFr X x → C.IsB (Bx x) := fun x hx => ((H x hx).2 _ (hBx x hx)).1
  have hd : ∀ x, IsONFr X x → C.xB (Bx x) ∈ C.X.dom := fun x hx =>
    GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C (hB x hx))
  have hmv : ∀ x, IsONFr X x → ∀ u, Bx (frMove θ W rfl X u x) = C.mvB u (Bx x) := fun x hx u => by
    obtain ⟨h1, h2⟩ := ((H x hx).2 _ (hBx x hx)).2.2.2.2.2.2.2.1 u
    exact isBasOf_unique hm hq (hBx _ h1) h2
  have hT : ∀ x, IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), GlobalTheory.SW.IsSB φ →
      ((IsThetaFunO ψ V W f ∧ Reads θ V W rfl X bas idx f φ x) ↔ f = C.Th (C.xB (Bx x)) φ) := fun x hx =>
    ((H x hx).2 _ (hBx x hx)).2.2.2.2.2.2.2.2
  have hne : ∀ x x', IsONFr X x → IsONFr X x' →
      kZero C.X C.idx (C.xB (Bx x)) (C.xB (Bx x')) (0 : Fin V.rank → Fin g → ℂ) 0 ≠ 0 := fun x x' hx hx' => by
    rw [kZero_zero]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
      (DblPoint.det_aLin_ne_zero (hd x hx) (hd x' hx') τ) (DblPoint.det_aAnti_ne_zero (hd x hx) (hd x' hx') τ)))
  refine ⟨fun x x' => kZero C.X C.idx (C.xB (Bx x)) (C.xB (Bx x')) (0 : Fin V.rank → Fin g → ℂ) 0,
    fun x x' hx hx' => ⟨hne x x' hx hx', fun u => ?_, fun v hv hv0 => ⟨dbl C.X C.bas C.idx v v 0, fun hc => ?_, ?_⟩⟩⟩
  · beta_reduce
    rw [hmv x hx, hmv x' hx']
    exact kZero_mvB C (hB x hx) u
  · obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D V W C
    have h1 := ipO_Th C hμ (hd x hx) (hd x hx) hv hv
    rw [hc, zero_mul] at h1
    have h2 := (hip μ 𝓕 hμ _ ((hT x hx _ v hv).2 rfl).1).2.1 h1
    obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd x hx) v hv
    have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • v) := by
      obtain ⟨R, hR, -, -⟩ := hv
      exact ⟨R, hR, fun x hx => absurd (by simp) hx, fun x y hy => by simp⟩
    refine hv0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ v))
    rw [l2, h2, zero_smul]
  · intro y y' hy hy' f f' κ κ' hf hf' rf rf' μ 𝓕 hμ
    have e := (hT y hy f _ rf.1).1 ⟨hf, rf⟩
    have e' := (hT y' hy' f' _ rf'.1).1 ⟨hf', rf'⟩
    rw [(GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd y hy) v hv).2.1] at e
    rw [(GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd y' hy') v hv).2.1] at e'
    have h1 := ipO_Th C hμ (hd y hy) (hd y' hy') hv hv
    refine Eq.trans ?_ (congrArg (κ * conj κ' * ·) h1)
    rw [e, e', GlobalTheory.Ker.ipO, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicVacuum_reads_multiple_classicalVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (Λ' : Lt D.host.E V.rank) (L : Lt D.host.E r), V.SigOK → W.SigOK → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (∀ v : Fin V.rank → D.host.E, v ∈ Λ' ↔ (fun j => star (v j)) ∈ ΛV) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens Λ' L) v → ∃ κ : ℂ, κ ≠ 0 ∧ Reads θ V W hr X bas idx f (κ • v) x := by
  first | exact @GlobalTheory.AdTh.VacLine.vac_reads | exact GlobalTheory.AdTh.VacLine.vac_reads | (intros; apply GlobalTheory.AdTh.VacLine.vac_reads <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.liftAdjoint_eigenvalue_lower_bound_base_embedding : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ), AdelC R F → GlobalTheory.Hk3.Core R F → A.fam.Ok s → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowTop R b := by
  first | exact @GlobalTheory.LowTopCore.lowTop_ofCore | exact GlobalTheory.LowTopCore.lowTop_ofCore | (intros; apply GlobalTheory.LowTopCore.lowTop_ofCore <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.rationalLift_lowerBound_off_basePlace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ), AdelC R F → (∀ i, GalOut R i 1) → GlobalTheory.Hk3.Core R F → A.fam.Ok s → (∀ i σ, ∃ v : (R.MW i σ).Vec, IsExtVec (R.MW i σ) v) → R.LUnif → GlobalTheory.BigOn.BaseLinks R F → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowForm R F b := by
  first | exact @GlobalTheory.LowForm.lowForm_six | exact GlobalTheory.LowForm.lowForm_six | (intros; apply GlobalTheory.LowForm.lowForm_six <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinTrace

variable {D : D7}

local instance (V : HSp D) : Submodule.IsLattice D.host.E (frameLat V) :=
  Submodule.IsLattice.of_fg D.host.E (frameLat_fg V)

theorem finFn_mem_SB (V : HSp D) {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) : finFn V ff ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  have hm := hff.tensorFin_mem
  rw [show finFn V ff = tensorFin D.sp.cm.sig V.gram ff ∘ (finPtsEquiv D.sp.cm.sig V.gram).symm from
    funext fun y => GlobalTheory.TrConv.finFn_eq_tensorFin V ff y]
  exact ⟨hm.1.comp_continuous (finPtsEquiv D.sp.cm.sig V.gram).symm.continuous,
    hm.2.comp_homeomorph (finPtsEquiv D.sp.cm.sig V.gram).symm.toHomeomorph⟩

theorem hasTrace_finFn : ∀ (D : D7) (V : HSp D) (ν : Measure (GfC V)) [ν.IsHaarMeasure] (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c) ∧ ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → IsCompact (K : Set (GfC V)) → (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x := by
  intro D V ν _ ff hff W _ _ σ hσ
  obtain ⟨hlc, hcs⟩ := finFn_mem_SB V hff
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) (smoothOp σ ν (finFn V ff)) := by
    intro v l
    refine ⟨?_, ?_⟩
    · have h := GlobalTheory.OpTrace.integrable_map (μ := ν) (hσ.1.smoothOp_integrand hlc hcs v).1
        (hσ.1.smoothOp_integrand hlc hcs v).2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using h
    · rw [hσ.1.map_smoothOp hlc hcs l v]
      simp only [smul_eq_mul]
  obtain ⟨K₀, ho, hc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hfd := hσ.finiteDimensional_range_smoothOp (μ := ν) hlc hcs ho hc
  refine ⟨⟨_, _, hA, hfd, rfl⟩, fun K _ _ hK hne => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, smoothOp σ ν (finFn V ff) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by convert hA using 1; exact (LinearMap.ext h).symm)
  exact ⟨_, hv, GlobalTheory.OpTrace.mem_fixed.1 (hσ.1.smoothOp_mem_fixed hlc hcs hK v)⟩

end GlobalTheory.FinTrace

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_restrictedProduct_haar_given_finiteFactors : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → (∃ μa, IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) ∧ ∃ ν, IsFinMeas V μf ν := by
  first | exact @GlobalTheory.ProdMeas.exists_prod_of_haar | exact GlobalTheory.ProdMeas.exists_prod_of_haar | (intros; apply GlobalTheory.ProdMeas.exists_prod_of_haar <;> assumption)
end
