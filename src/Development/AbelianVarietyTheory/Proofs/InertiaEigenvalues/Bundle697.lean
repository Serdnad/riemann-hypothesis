module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle672
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelFullAtInertPlacePrincipalElsewhere
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle676
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle674
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle675
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle493
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle642
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockCharactersCrystalline
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  first | exact @GlobalTheory.LocalUnitary.loc_mem_GU | exact GlobalTheory.LocalUnitary.loc_mem_GU | (intros; apply GlobalTheory.LocalUnitary.loc_mem_GU <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeFunI_add_and_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ (c : ℂ) (f : GAf L n → W), heckeFunI L n U Dv (h₁ + h₂) f = heckeFunI L n U Dv h₁ f + heckeFunI L n U Dv h₂ f ∧ heckeFunI L n U Dv (c • h₁) f = c • heckeFunI L n U Dv h₁ f := by
  first | exact @GlobalTheory.InertHeckeAdd.heckeFunI_add_smul | exact GlobalTheory.InertHeckeAdd.heckeFunI_add_smul | (intros; apply GlobalTheory.InertHeckeAdd.heckeFunI_add_smul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), x ∈ Umax L n → ∀ hg : Dv.loc x ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  first | exact @GlobalTheory.InertKU.loc_mem_KU | exact GlobalTheory.InertKU.loc_mem_KU | (intros; apply GlobalTheory.InertKU.loc_mem_KU <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inertLocal_surjective_from_trivOutside : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (y : GL (Fin n) (w.adicCompletion L)), y ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  first | exact @GlobalTheory.InertSurj.loc_surj | exact GlobalTheory.InertSurj.loc_surj | (intros; apply GlobalTheory.InertSurj.loc_surj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.exists_finset_doubleCosets_conj_maxCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n), ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ γ ∈ GQ L n, ∃ t ∈ T, ∃ κ ∈ (Umax L n ⊓ (Umax L n).map (MulAut.conj h).toMonoidHom), g = γ * t * κ := by
  first | exact @GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj | exact GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj | (intros; apply GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_level_full_at_inert_place_principal_elsewhere : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), 0 < N → ∃ U : Subgroup (GAf L n), (∀ κ, NG.Cong L n N κ → κ ∈ U) ∧ (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧ ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := by
  first | exact @GlobalTheory.InertLevel.exists_level | exact GlobalTheory.InertLevel.exists_level | (intros; apply GlobalTheory.InertLevel.exists_level <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.map_mul_right_unitaryAdelicMatrix_addHaar : ∀ (D : D7) (V : HSp D) (m : ℕ) (g : GA D V) (μ : Measure (Mx D m V.rank)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D m V.rank => (HMul.hMul (x : Matrix (Fin m) (Fin V.rank) (AE D)) (mt V g) : Mx D m V.rank)) = μ := by
  first | exact @GlobalTheory.AdelicModulus.map_mul_right_unitary | exact GlobalTheory.AdelicModulus.map_mul_right_unitary | (intros; apply GlobalTheory.AdelicModulus.map_mul_right_unitary <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.gammaSemisimpleQuotientD_statement : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | exact GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.fontaine_fullFaithful_exact_psi : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  first | exact @GlobalTheory.fontaine_litFont_assembled | exact GlobalTheory.fontaine_litFont_assembled | (intros; apply GlobalTheory.fontaine_litFont_assembled <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.RestPtAssembly

theorem chiRat_isCrys (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (h1 : 1 ≤ c)
    (h2 : c ≤ D.R.t) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) := by
  have h0 := ((GlobalTheory.BlockCrys.chiRatioCrysAt D i w hw) c h1 h2).2
  have hM : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c))) := by
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ (LinearEquiv.funUnique (Fin 1) _ _).symm
      (fun g x => ?_) h0
    funext a
    rw [Subsingleton.elim a 0]
    have e1 : Br.loc D.nbr i w hw (chiRatO D.nd i c) g 0 0 =
        ((Br.locChi D.nbr i w hw (GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatio D i c) g : (Br.LL D.nbr i w hw)ˣ) :
          Br.LL D.nbr i w hw) := by
      change (D.nbr i w hw).toLL (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0) =
        (D.nbr i w hw).toLL ((GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatio D i c (decS D.nd w (Br.iota D.nbr i w hw g)) :
          (D.nd.O i)ˣ) : D.nd.O i)
      rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatO_apply]
    change _ = (Br.loc D.nbr i w hw (chiRatO D.nd i c) g).mulVec (fun _ => x) 0
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, e1]
    rfl
  exact GlobalTheory.CrysCoef.isCrys_inclusion _ (D.loc (D.nd.l i)) _ _ _ C.le _ _ hM

end GlobalTheory.RestPtAssembly

end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

theorem _root_.GlobalTheory.T.inertia_fixes_maximalUnramifiedExtension_Ql : ∀ (l : ℕ) [Fact l.Prime] (g : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l))), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → ∀ x ∈ MaximalUnramifiedExtension l, (g : GQ l) x = x := by
  first | exact @GlobalTheory.InertQlUnr.IK_qlExt_fixes_Kur | exact GlobalTheory.InertQlUnr.IK_qlExt_fixes_Kur | (intros; apply GlobalTheory.InertQlUnr.IK_qlExt_fixes_Kur <;> assumption)
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKRightExact

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

section Res

variable (L : Type) [Field L] [Algebra Qp L] [Algebra L LL] [Module L V] [IsScalarTower L LL V]
  [IsScalarTower Qp L V] (ρ : Representation LL G V)

def res : Representation L G V where
  toFun g := (ρ g).restrictScalars L
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem Dcris_res : Dcris PD (res L ρ) = (Dcris PD ρ).restrictScalars L := by
  ext x
  simp only [Dcris, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

theorem DdR_res : DdR PD (res L ρ) = (DdR PD ρ).restrictScalars L := by
  ext x
  simp only [DdR, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

theorem isCrys_res (h : IsCrys PD ρ) : IsCrys PD (res L ρ) := by
  unfold IsCrys at h ⊢
  rw [Dcris_res]
  change finrank L ↥(Dcris PD ρ) = _
  rw [← Module.finrank_mul_finrank L LL ↥(Dcris PD ρ), ← Module.finrank_mul_finrank L LL V, h,
    mul_left_comm]

theorem isDR_of_res [FiniteDimensional L LL] (h : IsDR PD (res L ρ)) : IsDR PD ρ := by
  unfold IsDR at h ⊢
  rw [DdR_res] at h
  change finrank L ↥(DdR PD ρ) = _ at h
  rw [← Module.finrank_mul_finrank L LL ↥(DdR PD ρ), ← Module.finrank_mul_finrank L LL V,
    mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h

end Res

variable (f : V →ₗ[LL] V')

theorem map_φVB (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (φVB PD (LL := LL) x) =
      φVB PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_ιV (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) x) =
      ιV PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_mem_FilV {a : ℤ} {y : V ⊗[Qp] BdR} (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨AlgebraTensorModule.map f LinearMap.id z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_actVB {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g x) =
      actVB PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

include PD in
theorem tmul_one_injective {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  have h1 : (1 : B) ≠ 0 := fun h0 => PD.not_mem_filtration_two (by
    rw [← mul_one PD.t, h0, mul_zero, map_zero]; exact Submodule.zero_mem _)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one Qp h1
  have := congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V φ z)) h
  simpa [hφ] using this

end Generic

theorem lift_periods {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (hs : Function.Surjective f) (h : IsCrys (P.PD K) ρ) :
    IsDR (P.PD K) ρ' ∧
      (∀ y ∈ Dcris (P.PD K) ρ', ∃ x ∈ Dcris (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x = y) ∧
      ∀ y ∈ DdR (P.PD K) ρ', ∃ x ∈ DdR (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y := by
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  letI : Module ↥L.1 V' := Module.compHom V' (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ↥L.1 LL V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : IsScalarTower ℚ_[l] ↥L.1 V' := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V'
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  haveI : FiniteDimensional ↥L.1 V' := Module.Finite.trans LL V'
  have hc := isCrys_res (P.PD K) ↥L.1 ρ h
  have hd := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K L V _ hc).1
  obtain ⟨-, h1⟩ := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hc
  obtain ⟨h2, h3⟩ := (GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hd
  rw [Dcris_res, Dcris_res] at h1
  rw [DdR_res, DdR_res] at h3
  refine ⟨isDR_of_res (P.PD K) ↥L.1 ρ' h2, h1, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.DRFil.exists_mem_FilV (P.PD K) (LL := ↥L.1) y
  obtain ⟨x, hx, hxy⟩ := h3 a y ⟨hy, ha⟩
  exact ⟨x, hx.1, hxy⟩

theorem bkARightExact_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.bkARightExact (P.PD K) := by
  intro l _ P AI T K LL _ _ _ O _ _ hO A A' f hf hs hA _ c' hc'
  haveI := hO.2.1
  obtain ⟨hdr, hl1, hl2⟩ := lift_periods T K LL A.ρ A'.ρ f hf hs hA
  obtain ⟨-, x', hx'⟩ := hc'
  obtain ⟨hd1, d₂', hd2, hfil⟩ := GlobalTheory.T.crystalline_coboundary_lift l P AI T K LL O hO A' hdr c' x' hx'
  obtain ⟨d₁, hd₁, e₁⟩ := hl1 _ hd1
  obtain ⟨d₂, hd₂, e₂⟩ := hl2 _ hd2
  obtain ⟨x, y, c, hy, hx1, hx2, hc, hcx⟩ := GlobalTheory.T.exists_blochKato_cocycle_of_crys_deRham_pair l P AI T K LL O hO A d₁ hd₁ d₂ hd₂
  refine ⟨c, hc, ?_⟩
  rw [← hx1, map_sub, map_φVB] at e₁
  rw [← hx2, map_sub, map_ιV] at e₂
  obtain ⟨v, hv⟩ := (GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K LL A'.V).2
    (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x - x')
    (by rw [map_sub, eq_comm, sub_eq_sub_iff_sub_eq_sub]; exact e₁)
    (by
      have := Submodule.sub_mem _ (map_mem_FilV (P.PD K) f hy) hfil
      rw [← e₂] at this
      rw [map_sub]
      convert this using 1
      abel)
  refine ⟨v, funext fun g => tmul_one_injective (P.PD K) ?_⟩
  have h1 := congrArg (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) (hcx g)
  rw [map_sub, map_actVB (P.PD K) f hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply] at h1
  have h2 : actVB (P.PD K) A'.ρ g (v ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = A'.ρ g v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    simp [actVB]
  change (A'.ρ g v - v) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = (f (c g) - c' g) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
  rw [sub_tmul, sub_tmul, h1, hx', ← h2, ← hv, map_sub]
  abel

end GlobalTheory.BKRightExact
end
end
