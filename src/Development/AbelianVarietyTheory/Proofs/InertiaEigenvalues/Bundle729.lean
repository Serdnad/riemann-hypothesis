module

public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle713
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle700
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle716
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle715
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle705
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle710
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle714
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.inertHeckeOperator_maximalCompact_indicator_eq_id : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) f = f := by
  first | exact @GlobalTheory.InertHeckeOne.heckeFunI_one | exact GlobalTheory.InertHeckeOne.heckeFunI_one | (intros; apply GlobalTheory.InertHeckeOne.heckeFunI_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.maxCompactUnitary_conj_relIndex_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n), ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) ≠ 0 ∧ ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) = (Umax L n).relIndex ((Umax L n).map (MulAut.conj h).toMonoidHom) := by
  first | exact @GlobalTheory.UnimodMass.umax_relIndex_conj | exact GlobalTheory.UnimodMass.umax_relIndex_conj | (intros; apply GlobalTheory.UnimodMass.umax_relIndex_conj <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.H1fGeneration


set_option maxHeartbeats 1000000 in
theorem h1fGen_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) [IsTopologicalAddGroup T.V], FiniteCohomologyGeneratorsBound (P.PD K) T.L := by
  intro l _ P AI hT K LL _ T _ hG hC hcont
  have hO := (GlobalTheory.LocalIntegers.good_integers l LL).1
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T.V T.ρ hC).1
  obtain ⟨s, hs, hcard⟩ := GlobalTheory.T.h1fT_span_card_bound l P AI hT K (↥LL.1) (↥(OL LL)) hO T hDR
  have hBK := GlobalTheory.T.blochKatoDimensionFormula_concretePeriodRings l P AI hT K LL hG.1 T.V T.ρ hcont hC
  refine ⟨s, hs, ?_⟩
  have h0 : (0 : ℤ) ≤ (finrank ↥LL.1 ↥(H0V T.ρ) : ℤ) := by positivity
  set_option synthInstance.maxHeartbeats 200000 in
    have hc : ((s.card + finrank ↥LL.1 ↥(H0V T.ρ) : ℕ) : ℤ) ≤ ((finrank ↥LL.1 (FiniteCohomology (P.PD K) T.ρ) + finrank ↥LL.1 T.V : ℕ) : ℤ) := by
      exact_mod_cast hcard
    push_cast at hc
    linarith

end GlobalTheory.H1fGeneration
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.completion_over_q_or_d_eq_unramified_sup_sqrt : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), ∃ M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)), M ≤ MaximalUnramifiedExtension (D.nd.l i) ∧ ∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧ (D.nbr i w hw).Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y} := by
  first | exact @GlobalTheory.HubLoc.kw_eq_unram_sup_sqrt | exact GlobalTheory.HubLoc.kw_eq_unram_sup_sqrt | (intros; apply GlobalTheory.HubLoc.kw_eq_unram_sup_sqrt <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.dcris_exact_strict_elementwise_crystalline : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  first | exact @GlobalTheory.dcris_exact_strict_elementwise | exact GlobalTheory.dcris_exact_strict_elementwise | (intros; apply GlobalTheory.dcris_exact_strict_elementwise <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wach_lattice_expansion_at_low_level_points : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P4 D HW F Cm := by
  first | exact @GlobalTheory.NL.LatLevel.lattice_at_level | exact GlobalTheory.NL.LatLevel.lattice_at_level | (intros; apply GlobalTheory.NL.LatLevel.lattice_at_level <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.p8_of_cmpOf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P8 D HW F := by
  first | exact @GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places | exact GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places | (intros; apply GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachModule_saturated_exactness_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P6 D HW F := by
  first | exact @GlobalTheory.NL.Exact.exactness_of_N | exact GlobalTheory.NL.Exact.exactness_of_N | (intros; apply GlobalTheory.NL.Exact.exactness_of_N <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.blochKatoDim_at_auxiliary_prime_places : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), EmbeddingTypeJumps.AtQD i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Formalism.WeaklyAdmissibleFiltrations.BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 := by
  first | exact @GlobalTheory.InertiaEigenvalues.DimAtQD.main | exact GlobalTheory.InertiaEigenvalues.DimAtQD.main | (intros; apply GlobalTheory.InertiaEigenvalues.DimAtQD.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂

theorem aux_of_blochKato_tateDuality_eulerChar₂ :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ D : D7, LocalSituation.Conclusion5 D :=
  GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato

end GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.InertiaMod

open scoped Pointwise

variable {l : ℕ} [Fact l.Prime]

theorem ofGQ_apply (g : GQ l) (x : Om l) : Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ g x = g x := rfl

theorem Kur_stable (g : GQ l) {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : g x ∈ MaximalUnramifiedExtension l := by
  rw [← Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq] at hx ⊢
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.Kur_stable (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l) (Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ g) x hx
  rw [ofGQ_apply] at h
  exact h

theorem resid_of_fix (n : GQ l) (hn : ∀ x ∈ MaximalUnramifiedExtension l, n x = x) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖n x - x‖ < 1 := by
  have hmem : Formalism.MainNotions.N.PreambleDegrees.Loc.ofGQ n ∈
      ReciprocityTheory.DiscreteGroups.LocalClassField.subG l (Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)
        (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)) := by
    rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_iff]
    intro x hx
    rw [Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq] at hx
    rw [ofGQ_apply]
    exact hn x hx
  intro x hx
  have h := (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff (p := l) (K := Formalism.MainNotions.N.PreambleDegrees.Loc.Q0 l)
    Formalism.MainNotions.N.PreambleDegrees.Loc.finiteDimensional_Q0_alt _).1 hmem x hx
  rw [ofGQ_apply] at h
  exact h

theorem fix_Kur_normal : ((MaximalUnramifiedExtension l).fixingSubgroup : Subgroup (GQ l)).Normal := by
  constructor
  intro n hn τ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ (Kur_stable τ⁻¹ hx), ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

theorem mem_IK_of_fix (σ : GQ l) (hσ : ∀ x ∈ MaximalUnramifiedExtension l, σ x = x) :
    ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), (k' : GQ l) = σ := by
  have hG : σ ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact σ.commutes a
  exact ⟨⟨σ, hG⟩, Subgroup.subset_closure (fun x hx => resid_of_fix σ hσ x hx), rfl⟩

theorem exists_fix_Kur (M : IntermediateField ℚ_[l] (Om l)) (g : GQ l)
    (hg : ∀ x ∈ M, x ∈ MaximalUnramifiedExtension l → g x = x) :
    ∃ h ∈ M.fixingSubgroup, ∀ x ∈ MaximalUnramifiedExtension l, (g * h) x = x := by
  haveI := fix_Kur_normal (l := l)
  let S : Subgroup (GQ l) := M.fixingSubgroup ⊔ (MaximalUnramifiedExtension l).fixingSubgroup
  have hSc : IsClosed (S : Set (GQ l)) := by
    rw [Subgroup.mul_normal]
    exact IsClosed.mul_left_of_isCompact (InfiniteGalois.fixingSubgroup_isClosed _)
      (InfiniteGalois.fixingSubgroup_isClosed M).isCompact
  have hfS : (IntermediateField.fixedField S).fixingSubgroup = S :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨S, hSc⟩
  have hgS : g ∈ S := by
    rw [← hfS, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    apply hg
    · rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => hx σ (Subgroup.mem_sup_left hσ)
    · rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun σ hσ => hx σ (Subgroup.mem_sup_right hσ)
  have hgNH : g ∈ ((M.fixingSubgroup : Set (GQ l)) * ((MaximalUnramifiedExtension l).fixingSubgroup : Set (GQ l))) := by
    rw [← Subgroup.mul_normal]; exact hgS
  obtain ⟨u, hu, n, hn, hun⟩ := Set.mem_mul.1 hgNH
  refine ⟨u⁻¹, M.fixingSubgroup.inv_mem hu, ?_⟩
  have hmem : g * u⁻¹ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := by
    rw [← hun]
    exact (inferInstance : (MaximalUnramifiedExtension l).fixingSubgroup.Normal).conj_mem n hn u
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem

theorem seq_add_pow {e : ℕ} (ϖ : PiSys l e) (m k : ℕ) : ϖ.seq (m + k) ^ l ^ k = ϖ.seq m := by
  induction k with
  | zero => simp
  | succ k ih =>
    show ϖ.seq (m + k + 1) ^ l ^ (k + 1) = _
    rw [pow_succ', pow_mul, ϖ.seq_succ, ih]

theorem mem_level {a e : ℕ} [NeZero a] (ϖ : PiSys l e) {x : Om l} (hx : x ∈ ϖ.fieldInf a) :
    ∃ n, x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} := by
  let F : ℕ → IntermediateField ℚ_[l] (Om l) := fun n => Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n}
  have hs : ∀ n, ϖ.seq n ∈ F n := fun n =>
    (le_sup_right : _ ≤ F n) (IntermediateField.mem_adjoin_simple_self _ _)
  have hseq : ∀ m k, ϖ.seq m ∈ F (m + k) := by
    intro m k
    rw [← seq_add_pow ϖ m k]
    exact pow_mem (hs (m + k)) _
  have hmono : Monotone F := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact sup_le le_sup_left (IntermediateField.adjoin_simple_le_iff.2 (hseq m k))
  have hle : ϖ.fieldInf a ≤ ⨆ n, F n := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_trans le_sup_left (le_iSup F 0)
    · exact le_trans (IntermediateField.adjoin_simple_le_iff.2 (hs 0)) (le_iSup F 0)
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨n, rfl⟩
      exact le_iSup F n (hs n)
  have hx' : x ∈ ((⨆ n, F n : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hle hx
  rw [IntermediateField.coe_iSup_of_directed hmono.directed_le] at hx'
  exact Set.mem_iUnion.1 hx'

theorem fix_Kunr {a : ℕ} [NeZero a] (g : GQ l) (hg : ∀ x : Om l, x ^ l ^ a = x → g x = x) :
    ∀ x ∈ Kunr l a, g x = x := fun x hx => by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact hg x hx
  | algebraMap r => exact g.commutes r
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a →
    ∀ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x) →
      ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ h ∈ ϖ.GfieldInf a, (k' : GQ l) = g * h := by
  intro l _ a e _ _ ϖ _ g hg
  obtain ⟨h, hh, hgh⟩ := exists_fix_Kur (ϖ.fieldInf a) g fun x hx hK => by
    obtain ⟨n, hn⟩ := mem_level ϖ hx
    exact fix_Kunr g hg x (GlobalTheory.T.mem_unramifiedField_of_mem_maxUnramified_sup_root l a e ϖ n x hK hn)
  obtain ⟨k', hk', hkeq⟩ := mem_IK_of_fix (g * h) hgh
  exact ⟨k', hk', h, hh, hkeq⟩

end GlobalTheory.InertiaMod
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem blochKatoDim_at_every_local_situation : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm12 D := by
  intro D l _ K LL _
  exact GlobalTheory.T.blochKatoDimensionFormula_concretePeriodRings l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory
end
