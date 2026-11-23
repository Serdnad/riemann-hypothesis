module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle359
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle353
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle332
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle355
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle354
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
import Mathlib.NumberTheory.Padics.LocalField
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LocalSituation TensorProduct Module GlobalTheory.Per GlobalTheory.Prism

noncomputable section
namespace GlobalTheory.BSCoeff

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

section Dcris

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

theorem Dcris_resQ : Dcris (P.PD K) (resQ ρ) = (Dcris (P.PD K) ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [Dcris, sub_eq_zero, actVB_resQ]

theorem isCrys_resQ_iff [FiniteDimensional ℚ_[l] LL] : IsCrys (P.PD K) (resQ ρ) ↔ IsCrys (P.PD K) ρ := by
  have e : finrank ℚ_[l] ↥(Dcris (P.PD K) (resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dcris (P.PD K) ρ) := by
    rw [Dcris_resQ, finrank_mul_finrank]
    rfl
  rw [IsCrys, IsCrys, e, ← finrank_mul_finrank ℚ_[l] LL V, mul_left_comm]
  exact Nat.mul_right_inj finrank_pos.ne'

end Dcris

variable {l : ℕ} [Fact l.Prime]



theorem algebraMap_OL (LL : FinExt l) (z : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z) = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]; rfl

theorem finite_OL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

variable {G : Type} [Group G] [TopologicalSpace G]

@[reducible] def zlV (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : Module ℤ_[l] T.V :=
  Module.compHom T.V (algebraMap ℤ_[l] ↥(OL LL))

theorem modO_smul (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (o : ↥(OL LL)) (w : T.V) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ T.modO.toSMul) o w = algebraMap ↥(OL LL) ↥LL.1 o • w := by
  letI := T.modO
  haveI := T.towO
  exact (algebraMap_smul ↥LL.1 o w).symm

theorem zlV_smul (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (z : ℤ_[l]) (w : T.V) :
    (zlV LL T).toSMul.smul z w = (z : ℚ_[l]) • w := by
  change @HSMul.hSMul _ _ _ (@instHSMul _ _ T.modO.toSMul) (algebraMap ℤ_[l] ↥(OL LL) z) w = _
  rw [modO_smul, algebraMap_OL, algebraMap_smul]

theorem zlV_tower (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlV LL T
    IsScalarTower ℤ_[l] ℚ_[l] T.V := by
  letI := zlV LL T
  refine ⟨fun z q v => ?_⟩
  change (z • q) • v = (zlV LL T).toSMul.smul z (q • v)
  rw [zlV_smul, smul_smul]
  rfl

theorem finite_compHom {O M : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] :
    letI := Module.compHom M (algebraMap ℤ_[l] O)
    Module.Finite ℤ_[l] M := by
  letI := Module.compHom M (algebraMap ℤ_[l] O)
  haveI : IsScalarTower ℤ_[l] O M := ⟨fun c a x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  exact Module.Finite.trans O M

theorem denom (LL : FinExt l) (c : ↥LL.1) :
    ∃ (z : ℚ_[l]) (a : ↥(OL LL)), c = z • algebraMap ↥(OL LL) ↥LL.1 a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have halg : IsAlgebraic ℤ_[l] c :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz, hint⟩ := halg.exists_integral_multiple
  have hz' : (z : ℚ_[l]) ≠ 0 := fun h => hz (Subtype.ext h)
  refine ⟨(z : ℚ_[l])⁻¹, ⟨z • c, hint⟩, ?_⟩
  change c = (z : ℚ_[l])⁻¹ • ((z : ℚ_[l]) • c)
  rw [smul_smul, inv_mul_cancel₀ hz', one_smul]

end GlobalTheory.BSCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff GlobalTheory.BSCoeff



theorem bhattScholze_coeff : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.BhattScholzeCrystallineLattices := by
  intro h l _ K P₀ e hA
  obtain ⟨h1, h2⟩ := h l K P₀ e hA
  refine ⟨fun P AI hS LL T hC => ?_, h2⟩
  letI := zlV LL T
  haveI := zlV_tower LL T
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : FiniteDimensional ℚ_[l] T.V := Module.Finite.trans ↥LL.1 T.V
  haveI : IsModuleTopology ℚ_[l] ↥LL.1 := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology ℚ_[l] T.V := isModuleTopology_of_tower ℚ_[l] ↥LL.1 T.V
  let TZ : Submodule ℤ_[l] T.V :=
    { carrier := (T.L.T : Set T.V)
      add_mem' := fun ha hb => T.L.T.add_mem ha hb
      zero_mem' := T.L.T.zero_mem
      smul_mem' := fun z v hv => T.L.T.smul_mem (algebraMap ℤ_[l] ↥(OL LL) z) hv }
  haveI := finite_OL LL
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  have hfin' := finite_compHom (l := l) (O := ↥(OL LL)) (M := ↥T.L.T)
  haveI hfin : Module.Finite ℤ_[l] ↥TZ := hfin'
  have hz : ∀ (z : ℤ_[l]) (v : T.V), z • v = (z : ℚ_[l]) • v := fun z v => zlV_smul LL T z v
  have htf : Module.IsTorsionFree ℤ_[l] ↥TZ := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro z x hx
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    right
    have h' : (z : ℚ_[l]) • (x : T.V) = 0 := by
      rw [← hz]; exact congrArg Subtype.val hx
    have hq : (z : ℚ_[l]) ≠ 0 := fun h0 => hz0 (PadicInt.coe_eq_zero.1 h0)
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left hq)
  have hspan : Submodule.span ℚ_[l] (TZ : Set T.V) = ⊤ := by
    let W : Submodule ↥LL.1 T.V :=
      { carrier := (Submodule.span ℚ_[l] (TZ : Set T.V) : Set T.V)
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := by
          intro a x hx
          induction hx using Submodule.span_induction with
          | mem t ht =>
            obtain ⟨q, o, rfl⟩ := denom LL a
            show (q • algebraMap ↥(OL LL) ↥LL.1 o) • t ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [smul_assoc, ← modO_smul]
            exact Submodule.smul_mem _ q (Submodule.subset_span (T.L.T.smul_mem o ht))
          | zero => simp
          | add x y _ _ hx hy =>
            show a • (x + y) ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [smul_add]; exact Submodule.add_mem _ hx hy
          | smul q x _ hx =>
            show a • (q • x) ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [← algebraMap_smul ↥LL.1 q x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
            exact Submodule.smul_mem _ q hx }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← T.L.span, Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ht
    rw [eq_top_iff]
    intro v _
    have : v ∈ W := hW ▸ Submodule.mem_top
    exact this
  let L : Lattice (O := ℤ_[l]) (resQ T.ρ) :=
    { T := TZ
      stable := fun g x hx => T.L.stable g x hx
      fg := Module.Finite.iff_fg.mp hfin
      free := Module.free_of_finite_type_torsion_free'
      span := hspan }
  obtain ⟨E, j, hR⟩ := h1 P AI hS T.V (resQ T.ρ) L (fun x => T.cont x) ((isCrys_resQ_iff P T.ρ).mpr hC)
  exact ⟨E, j, hR⟩

end GlobalTheory
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

variable {l : ℕ} [Fact l.Prime]

section Cob

variable {G : Type} [Group G] [TopologicalSpace G] {K₀ K : Type} [Field K₀] [Field K]
    [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B]
    [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR]
    (PD : PeriodData G ℚ_[l] K₀ K B BdR)

theorem cyclotomicTwist_differential_apply {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (f : G → LL) (x : G × G) :
    ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f x =
      algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1 := by
  simp [ReciprocityTheory.Def.d1, charRep, cycLL, Algebra.smul_def]

theorem cobL_iff_trace {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    [FiniteDimensional ℚ_[l] LL] [IsModuleTopology ℚ_[l] LL] (z : G × G → LL) :
    CobL PD z ↔ ∀ c : LL, CobL PD (fun x => Algebra.trace ℚ_[l] LL (c * z x)) := by
  haveI : ContinuousAdd LL := IsModuleTopology.toContinuousAdd ℚ_[l] LL
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  constructor
  · rintro ⟨f, hf, rfl⟩ c
    refine ⟨fun g => Algebra.trace ℚ_[l] LL (c * f g), ?_, ?_⟩
    · exact (IsModuleTopology.continuous_of_linearMap
        ((Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c))).comp hf
    · funext x
      rw [cyclotomicTwist_differential_apply, cyclotomicTwist_differential_apply]
      have e1 : c * (algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1) =
          (PD.χ x.1 : ℚ_[l]) • (c * f x.2) - c * f (x.1 * x.2) + c * f x.1 := by
        rw [Algebra.smul_def]; ring
      rw [e1, map_add (f := _), map_sub, map_smul, smul_eq_mul]
      simp
  · intro h
    choose f hf using h
    have hB := traceForm_nondegenerate ℚ_[l] LL
    let b := Module.finBasis ℚ_[l] LL
    let d := (Algebra.traceForm ℚ_[l] LL).dualBasis hB b
    refine ⟨fun g => ∑ i, f (b i) g • d i, ?_, ?_⟩
    · exact continuous_finsetSum _ fun i _ => ((hf (b i)).1).smul continuous_const
    · funext x
      rw [cyclotomicTwist_differential_apply]
      have hz : z x = ∑ i, (d.repr (z x) i) • d i := (d.sum_repr (z x)).symm
      have hc : ∀ i, d.repr (z x) i = (PD.χ x.1 : ℚ_[l]) * f (b i) x.2 - f (b i) (x.1 * x.2) + f (b i) x.1 := by
        intro i
        rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm,
          ← congrFun (hf (b i)).2 x, cyclotomicTwist_differential_apply]
        simp
      rw [hz]
      simp_rw [hc, add_smul, sub_smul, mul_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.smul_sum, Algebra.smul_def]

end Cob

section Main

variable (P : LocPrime l) {K : FinExt l}

def trPair {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l] :=
  LinearMap.mk₂ ℚ_[l] (fun x y => Algebra.trace ℚ_[l] LL (Pr x y))
    (fun x x' y => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])
    (fun x y y' => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])

theorem trPair_apply {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (x : V) (y : V') :
    trPair Pr x y = Algebra.trace ℚ_[l] LL (Pr x y) := rfl

theorem isDual1_trPair {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {Pr : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : IsDual1 (P.PD K) ρ ρ' Pr) : IsDual1 (P.PD K) (resQ ρ) (resQ ρ') (trPair Pr) := by
  have hB := traceForm_nondegenerate ℚ_[l] LL
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨fun g x y => ?_, fun x hx => h2 x fun y => ?_, fun y hy => h3 y fun x => ?_, ?_⟩
  · rw [resQ_apply, resQ_apply, trPair_apply, trPair_apply, h1]
    have e : ((cycLL (P.PD K) LL g : LLˣ) : LL) * Pr x y = ((P.PD K).χ g : ℚ_[l]) • Pr x y := by
      simp [cycLL, Algebra.smul_def]
    rw [e, map_smul, smul_eq_mul]
    simp [cycLL]
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul]
    exact hx (c • y)
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul]
    exact hy (c • x)
  · rw [← Module.finrank_mul_finrank ℚ_[l] LL V, ← Module.finrank_mul_finrank ℚ_[l] LL V', h4]

end Main

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkACore_of_rationalDuality (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
    (h : GlobalTheory.Published.BlochKato.RationalDuality (P.PD K)) : bkACore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A A' Pr hdR hP
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : FiniteDimensional ℚ_[l] A'.V := Module.Finite.trans LL A'.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  haveI : IsModuleTopology ℚ_[l] A'.V := isModuleTopology_of_tower ℚ_[l] LL A'.V
  haveI : ContinuousConstSMul ℚ_[l] A.V := ⟨fun c => by
    have hc : Continuous fun x : A.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  haveI : ContinuousConstSMul ℚ_[l] A'.V := ⟨fun c => by
    have hc : Continuous fun x : A'.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  have key := h A.V A'.V (resQ A.ρ) (resQ A'.ρ) (trPair Pr) A.cont A'.cont
    ((isDR_resQ_iff P A.ρ).mpr hdR) (isDual1_trPair P hP)
  have cupS : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a (c • b) = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cupS' : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) (c • a) b = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cup1 : ∀ (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a b = fun x => Algebra.trace ℚ_[l] LL (1 * cupL A'.ρ Pr a b x) := by
    intro a b; funext x
    simp [cupL, trPair_apply]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.1 a ha)]
    constructor
    · intro H b hb
      rw [cobL_iff_trace]
      intro c
      rw [← cupS]
      exact H (c • b) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A'.ρ).smul_mem c hb))
    · intro H b hb
      have := (cobL_iff_trace (P.PD K) _).mp (H b ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp hb)) 1
      rwa [← cup1] at this
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.2 b hb)]
    constructor
    · intro H a ha
      rw [cobL_iff_trace]
      intro c
      rw [← cupS']
      exact H (c • a) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A.ρ).smul_mem c ha))
    · intro H a ha
      have := (cobL_iff_trace (P.PD K) _).mp (H a ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp ha)) 1
      rwa [← cup1] at this

end GlobalTheory
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.fixed_of_fixed_inertia_of_fixed_frobenius : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ y : ℂ_[l], (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σC g y = y) → Per.σC F y = y → ∀ g : GQ l, Per.σC g y = y := by
  first | exact @GlobalTheory.RegularDense.fixed_of_inertia_frobenius | exact GlobalTheory.RegularDense.fixed_of_inertia_frobenius | (intros; apply GlobalTheory.RegularDense.fixed_of_inertia_frobenius <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisRep_entries_coboundary_complexPadic : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∃ b : ℝ, 0 < b ∧ ∀ (H : Subgroup ↥(GK K)) (t : ℝ), 0 < t → (∀ g ∈ H, ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ t) → ∀ i j, ∃ y : ℂ_[l], ∀ g ∈ H, ‖Formalism.Per.σC (g : GQ l) y - y - algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j)‖ ≤ b * t ^ 2 := by
  first | exact @GlobalTheory.ph_c_cob | exact GlobalTheory.ph_c_cob | (intros; apply GlobalTheory.ph_c_cob <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachInclusion_X_Q_frobenius : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; E.io W.X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).π₁ ∧ E.io W.Q = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ ∧ Function.Injective (inclR LL) ∧ Function.Injective E.ioE ∧ (∀ a, inclR LL (E.io (W.φA a)) = φRW LL (inclR LL (E.io a))) ∧ (∀ x : W.EE, (∃ y, inclR LL y = E.ioE x) → ∃ a : AA K LL, algebraMap _ W.EE a = x) ∧ ∀ j : ℕ, IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.X)) ∧ IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.Q)) := by
  first | exact @GlobalTheory.NL.IoXQ.main | exact GlobalTheory.NL.IoXQ.main | (intros; apply GlobalTheory.NL.IoXQ.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
open scoped Pointwise

namespace GlobalTheory.TypeSplit

theorem main : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), IsSplitPl D.host w := by
  intro D k w hw
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2
  by_contra hn
  have hle : ∀ x ∈ w.asIdeal, D.host.conj • x ∈ w.asIdeal := by
    intro x hx
    by_contra hy
    refine hn ⟨x, hx, fun y e hy' => hy ?_⟩
    have : y = D.host.conj • x := Subtype.ext e
    rwa [← this]
  refine GlobalTheory.TypePlace.conj_ne_one D.host (hP _ ?_)
  have h1 : D.host.conj • w.asIdeal ≤ w.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa using hle _ hy
  have hm : (D.host.conj • w.asIdeal).IsMaximal :=
    Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ (𝓞 D.host.E) D.host.conj) (hp := w.isMaximal)
  exact hm.eq_of_le w.isMaximal.ne_top h1

end GlobalTheory.TypeSplit
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



theorem _root_.GlobalTheory.T.exists_tateDual_localGaloisRep_atPlace : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)) (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX := by
  first | exact @GlobalTheory.TateDualX.exists_tateDual | exact GlobalTheory.TateDualX.exists_tateDual | (intros; apply GlobalTheory.TateDualX.exists_tateDual <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.heckeChar_loc_pow_eq_one_on_localUnits : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ), Formalism.L2.Host.IsUnitAt v x → ∃ m : ℕ, 0 < m ∧ χ.loc v x ^ m = 1 := by
  first | exact @GlobalTheory.LocUnitPow.loc_pow_eq_one | exact GlobalTheory.LocUnitPow.loc_pow_eq_one | (intros; apply GlobalTheory.LocUnitPow.loc_pow_eq_one <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



theorem _root_.GlobalTheory.T.lenMod_mono_left' : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S S' H : Submodule O M), S ≤ S' → BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  first | exact @GlobalTheory.lenMod_mono_left | exact GlobalTheory.lenMod_mono_left | (intros; apply GlobalTheory.lenMod_mono_left <;> assumption)
end
