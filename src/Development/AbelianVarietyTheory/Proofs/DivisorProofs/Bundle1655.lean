module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.ReductionIwasawa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalNormOneOfIdempotentConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.kTypeInKFinite : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → S ≤ D ∧ FiniteDimensional ℂ (S.comap D.subtype) ∧ KStab ε E (S.comap D.subtype) ∧ (∀ ν : Fin n → ℝ, ∀ x ∈ S.comap D.subtype, x ≠ 0 → KHighest ε E ν x → ν = μ) := by
  intro n ε H _ _ σ D E hH hU hI hK μ S hS
  have hSD : S ≤ D := fun v hv => (hK.mem v).2 ⟨S, hS.1, hv, hS.2.1⟩
  haveI : FiniteDimensional ℂ S := hS.1
  have hmap : (S.comap D.subtype).map D.subtype = S := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hSD
  haveI hFD : FiniteDimensional ℂ (S.comap D.subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSD).symm
  have hStab : KStab ε E (S.comap D.subtype) := by
    rw [GlobalTheory.T.kStab_iff_isKStableOn_finite_vectors n ε H σ D E hH hU hI hK _ hFD, hmap]; exact hS.2.1
  have hinj := Submodule.map_injective_of_injective (f := D.subtype) Subtype.val_injective
  have hirr : ∀ L' ≤ S.comap D.subtype, KStab ε E L' → L' = ⊥ ∨ L' = S.comap D.subtype := by
    intro L' hL' hst
    haveI : FiniteDimensional ℂ L' := Submodule.finiteDimensional_of_le hL'
    have hK' := (GlobalTheory.T.kStab_iff_isKStableOn_finite_vectors n ε H σ D E hH hU hI hK L' inferInstance).1 hst
    have hle : L'.map D.subtype ≤ S := hmap ▸ Submodule.map_mono hL'
    rcases hS.2.2.1 _ hle hK' with h | h
    · left; apply hinj; rw [h, Submodule.map_bot]
    · right; apply hinj; rw [h, hmap]
  obtain ⟨v, hv0, hvS, hvh⟩ := hK.hw μ S hS
  have hKR : KRel ε E := fun a b c d _ _ => hK.gl a b c d
  have hKU : KUnit ε E := fun a b h x y => by rw [hK.unit a b x y]; simp [Formalism.REAL.sgn, h]
  refine ⟨hSD, hFD, hStab, ?_⟩
  exact GlobalTheory.T.compactHighestWeight_unique_of_irreducible n ε D E hKR hKU _ hFD hStab hirr μ v hvS hv0 hvh
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinIrr

theorem smE_eq {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hK : IsKMod ε σ D E) (v : D) (hv : (v : H) ∈ ReciprocityTheory.ChartRestriction.DS.smD ε σ)
    (a b : Fin n) :
    ((ReciprocityTheory.ChartRestriction.DS.smE ε σ a b ⟨v, hv⟩ : ReciprocityTheory.ChartRestriction.DS.smD ε σ) : H) = ((E a b v : D) : H) := by
  have hσ' : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := hσ
  have key : ∀ X, ReciprocityTheory.ChartRestriction.DS.inG ε X →
      ReciprocityTheory.ChartRestriction.DS.dS σ X (v : H) = ∑ c, ∑ d, X c d • ((E c d v : D) : H) := fun X hX =>
    (hK.real X hX v).deriv
  rw [ReciprocityTheory.ChartRestriction.DS.smE_apply hσ']
  change ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) + Complex.I • ReciprocityTheory.ChartRestriction.DS.dS σ _ (v : H) = _
  rw [key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε _), key _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε _)]
  have hz : ∀ c d, ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
      Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d = Matrix.single a b (1 : ℂ) c d := by
    intro c d
    have := congrFun (congrFun (ReciprocityTheory.ChartRestriction.DS.SmDerA.cpart_decomp ε (Matrix.single a b 1)) c) d
    rw [this]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  calc _ = ∑ c, ∑ d, (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single a b 1) c d +
        Complex.I * ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single a b 1) c d) • ((E c d v : D) : H) := by
          simp only [Finset.smul_sum, add_smul, Finset.sum_add_distrib, smul_smul]
    _ = ∑ c, ∑ d, Matrix.single a b (1 : ℂ) c d • ((E c d v : D) : H) := by simp only [hz]
    _ = ((E a b v : D) : H) := by
          simp [Matrix.single_apply, ite_smul, ite_and]

theorem kMod_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro n ε H _ _ σ D E hc hσ hirr hK N hN
  haveI := hc
  have hle : D ≤ ReciprocityTheory.ChartRestriction.DS.smD ε σ := fun v hv =>
    (CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr).1 v ((hK.mem v).1 hv)
  let ι : D →ₗ[ℂ] ReciprocityTheory.ChartRestriction.DS.smD ε σ := Submodule.inclusion hle
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  have hcomm : ∀ a b (x : D), ReciprocityTheory.ChartRestriction.DS.smE ε σ a b (ι x) = ι (E a b x) := fun a b x =>
    Subtype.ext (smE_eq hσ hK x (hle x.2) a b)
  let N' : Submodule ℂ (ReciprocityTheory.ChartRestriction.DS.smD ε σ) := N.map ι
  have hN'K : (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) ⊆ CompanionTheory.D.gk.HC.KF ε σ := by
    rintro _ ⟨x, -, rfl⟩
    exact (hK.mem x).1 x.2
  have hN'st : ∀ a b, ∀ v ∈ N', ReciprocityTheory.ChartRestriction.DS.smE ε σ a b v ∈ N' := by
    rintro a b _ ⟨x, hx, rfl⟩
    rw [hcomm]
    exact ⟨_, hN a b x hx, rfl⟩
  rcases GlobalTheory.HcPort.uIrr n ε H σ hσ hirr N' hN'K hN'st with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : ι x ∈ N' := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at hx'
    rw [Submodule.mem_bot]
    exact hι (by rw [hx', map_zero])
  · right
    rw [eq_top_iff]
    intro x _
    have hx' : ι x ∈ (N' : Set (ReciprocityTheory.ChartRestriction.DS.smD ε σ)) := by
      rw [h]
      exact (hK.mem x).1 x.2
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [hι hyx] at hy
    exact hy

end GlobalTheory.KFinIrr
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section Hom

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem subst_sum_smul {σ τ ι : Type} [Fintype ι] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (m : ι → C)
    (f : ι → MvPowerSeries σ C) : subst a (∑ i, m i • f i) = ∑ i, m i • (subst a (f i) : MvPowerSeries τ C) := by

  rw [← substAlgHom_apply ha, map_sum]
  simp only [map_smul, substAlgHom_apply]

theorem isIntHom_comp {d d' d'' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'} {G'' : LogFGL v d''}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {ψ : Fin d'' → MvPowerSeries (Fin d') C}
    {M : Matrix (Fin d') (Fin d) C} {N : Matrix (Fin d'') (Fin d') C}
    (hφ : IsIntHom G G' φ M) (hψ : IsIntHom G' G'' ψ N) :
    IsIntHom G G'' (fun b => subst φ (ψ b)) (N * M) := by
  obtain ⟨hφ0, hφi, hφl⟩ := hφ
  obtain ⟨hψ0, hψi, hψl⟩ := hψ
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  refine ⟨fun b => constantCoeff_subst_eq_zero hφs hφ0 (hψ0 b), fun b => ?_, fun c => ?_⟩
  · exact ptIntSer_subst hφs (fun s => hφi s) (hψi b)
  · rw [← subst_comp_subst_apply hψs hφs, hψl c, subst_sum_smul hφs]
    simp_rw [hφl, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm

end Hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

section Labels

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def embO (σ : E →+* ℂ) : 𝓞 E →+* X.O where
  toFun a := (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose
  map_one' := X.ints.hom_inj (by rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_one, map_one])
  map_zero' := X.ints.hom_inj (by
    rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_zero, map_zero])
  map_mul' a b := X.ints.hom_inj (by
    rw [map_mul (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_mul])
  map_add' a b := X.ints.hom_inj (by
    rw [map_add (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_add])

theorem algebraMap_embO (σ : E →+* ℂ) (a : 𝓞 E) : algebraMap X.O X.C (embO io X σ a) = embX io X σ a :=
  (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose_spec

def red (σ : E →+* ℂ) : 𝓞 E →+* ResidueField X.O := (residue X.O).comp (embO io X σ)

theorem residue_eq_zero_iff_v (x : X.O) : residue X.O x = 0 ↔ X.v (algebraMap X.O X.C x) < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, X.ints.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (X.ints.map_le_one x) h, fun h => h.ne⟩

theorem residue_eq_iff_v (x y : X.O) :
    residue X.O x = residue X.O y ↔ X.v (algebraMap X.O X.C x - algebraMap X.O X.C y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_v, map_sub]

theorem primeBelow_eq_ker (σ : E →+* ℂ) : primeBelow io X σ = RingHom.ker (red io X σ) := by
  ext a
  rw [RingHom.mem_ker]
  show X.v (embX io X σ a) < 1 ↔ residue X.O (embO io X σ a) = 0
  rw [residue_eq_zero_iff_v, algebraMap_embO]

theorem red_eq_pow_iff (σ σ' : E →+* ℂ) (a : 𝓞 E) (n : ℕ) :
    red io X σ' a = red io X σ a ^ n ↔ X.v (embX io X σ' a - embX io X σ a ^ n) < 1 := by
  show residue X.O (embO io X σ' a) = residue X.O (embO io X σ a) ^ n ↔ _
  rw [← map_pow, residue_eq_iff_v, map_pow, algebraMap_embO, algebraMap_embO]

theorem charP_residueField_of_irreducible : CharP (ResidueField X.O) p := by
  have h : ((p : ℕ) : ResidueField X.O) = 0 := by
    rw [← map_natCast (residue X.O), residue_eq_zero_iff]
    exact X.nonunit.out
  exact (CharP.charP_iff_prime_eq_zero Fact.out).2 h

theorem vX_vp_pos_iff (x : X.C) : 0 < vX_vp X x ↔ X.v x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpO : ¬ IsUnit (p : X.O) := X.nonunit.out
  have hp1 : X.v (p : X.C) < 1 := by
    have h := X.ints.map_le_one (p : X.O)
    rw [map_natCast] at h
    refine lt_of_le_of_ne h fun h1 => hpO ?_
    apply X.ints.isUnit_of_one'
    rw [map_natCast]
    exact h1
  have hp0 : (0 : NNReal) < X.v (p : X.C) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : (0 : NNReal) < X.v x := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact hx
  have hlp : Real.log (X.v (p : X.C) : ℝ) < 0 :=
    Real.log_neg (by exact_mod_cast hp0) (by exact_mod_cast hp1)
  have hi : (Real.log (X.v (p : X.C) : ℝ))⁻¹ < 0 := inv_lt_zero.mpr hlp
  rw [vX_vp_apply X hx, show (0 : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) from rfl, WithTop.coe_lt_coe,
    mul_pos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact absurd h1 (not_lt.mpr hi.le)
    · have h3 := (Real.log_neg_iff (by exact_mod_cast hx0)).mp h2
      exact_mod_cast h3
  · intro h
    right
    exact ⟨hi, Real.log_neg (by exact_mod_cast hx0) (by exact_mod_cast h)⟩

end Labels

variable {Dw : Datum H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr}
  {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def tanX (a : 𝓞 E) : Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  Matrix.of fun i j => jX X (coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a i))

end GlobalTheory.PrimePart
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem ratGL_bounded_count : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  intro E _ _ _ a
  obtain ⟨m, hm⟩ := GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount E
  refine ⟨m * (a * a), fun Kf hKf => ?_⟩
  let Kf' : Set (Af E) := ⋃ i : Fin a, ⋃ j : Fin a, (fun g : GL (Fin a) (Af E) => g.val i j) '' Kf
  have hc : IsCompact Kf' := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hKf.image ?_
    exact (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨C, hC0, hC⟩ := hm Kf' hc
  refine ⟨C ^ (a * a), pow_nonneg hC0 _, fun T hT => ?_⟩
  obtain ⟨hNf, hNc⟩ := hC T hT
  let N : Set E := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf'}
  let S : Set (GL (Fin a) E) := {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}
  change S.Finite ∧ (S.ncard : ℝ) ≤ C ^ (a * a) * T ^ (m * (a * a))
  have hsub : ∀ γ ∈ S, ∀ i j, γ.val i j ∈ N := by
    intro γ hγ i j
    obtain ⟨h1, h2⟩ := hγ
    refine ⟨?_, ?_⟩
    · have he : pInf E (algebraMap E (Ad E) (γ.val i j)) = (toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val) i j := rfl
      rw [he]
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans h1
    · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨_, h2, rfl⟩⟩⟩
  classical
  let F : Finset E := hNf.toFinset
  let P : Finset (Fin a → Fin a → E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  let f : GL (Fin a) E → (Fin a → Fin a → E) := fun γ => γ.val
  have hf : Function.Injective f := fun x y h => Units.ext h
  have himg : f '' S ⊆ (P : Set (Fin a → Fin a → E)) := by
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [P, F, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i j => hsub γ hγ i j
  have hSfin : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset himg) hf.injOn
  refine ⟨hSfin, ?_⟩
  have hcardP : P.card = (F.card ^ a) ^ a := by
    simp [P, Fintype.card_piFinset, Finset.prod_const]
  have hS : S.ncard ≤ (F.card ^ a) ^ a := by
    rw [← Set.ncard_image_of_injective S hf, ← hcardP, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg P.finite_toSet
  have hF : (F.card : ℝ) ≤ C * T ^ m := by
    rw [← Set.ncard_eq_toFinset_card N hNf]; exact hNc
  calc (S.ncard : ℝ) ≤ ((F.card ^ a) ^ a : ℕ) := by exact_mod_cast hS
    _ = (F.card : ℝ) ^ (a * a) := by push_cast; rw [← pow_mul]
    _ ≤ (C * T ^ m) ^ (a * a) := pow_le_pow_left₀ (Nat.cast_nonneg _) hF _
    _ = C ^ (a * a) * T ^ (m * (a * a)) := by rw [mul_pow, ← pow_mul]

end GlobalTheory
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

open Pointwise Matrix

namespace GlobalTheory.SiegelSetGL

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

theorem continuous_pInfC : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pInfC E))

theorem continuous_mapFin : Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

theorem exists_compact_decomp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ω : Set (AdelicGLn.AdelicGL E a)), IsCompact ω →
    ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) → ∀ t : ℝ, 0 < t →
    ∃ (Ω : Set (GL (Fin a) (Cinf E))) (Kf : Set (GL (Fin a) (Af E))), IsCompact Ω ∧ IsCompact Kf ∧
      ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
        d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, ∀ k ∈ maxCompact (K := E) (n := a),
          ∃ c ∈ Ω, ∃ f ∈ Kf, b * infGL E a d * k = infGL E a (d * c) * finGL E a f := by
  intro E _ _ _ a ω hω hωB t ht
  set pI := GeneralLinearGroup.map (n := Fin a) (pInf E)
  set pF := GeneralLinearGroup.map (n := Fin a) (pFin E)
  have hωI : IsCompact (pI '' ω) := hω.image (continuous_mapInf E a)
  have hup : ∀ b ∈ pI '' ω, b.val.BlockTriangular id := by
    rintro _ ⟨b, hb, rfl⟩ i j hij
    have h0 : (b : Matrix (Fin a) (Fin a) (Ad E)) i j = 0 := hωB hb hij
    change pInf E ((b : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0
    rw [h0, map_zero]
  obtain ⟨Ω0, hΩ0, hΩ⟩ := GlobalTheory.T.exists_compact_coneDiagonal_conj_upperTriangular E a (pI '' ω) hωI hup t ht
  have hK := isCompact_maxCompact (K := E) (n := a)
  refine ⟨Ω0 * pI '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    pF '' ω * pF '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    hΩ0.mul (hK.image (continuous_mapInf E a)),
    (hω.image (continuous_mapFin E a)).mul (hK.image (continuous_mapFin E a)), ?_⟩
  intro r d hr hrt hd b hb k hk
  refine ⟨(d⁻¹ * pI b * d) * pI k, Set.mul_mem_mul (hΩ r d hr hrt hd _ ⟨b, hb, rfl⟩) ⟨k, hk, rfl⟩,
    pF b * pF k, Set.mul_mem_mul ⟨b, hb, rfl⟩ ⟨k, hk, rfl⟩, ?_⟩
  apply ga_ext
  · change pI (b * infGL E a d * k) = pI (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pI, pInf_infGL, pInf_finGL, mul_one]
    group
  · change pF (b * infGL E a d * k) = pF (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pF, pFin_infGL, pFin_finGL, mul_one, one_mul]

end GlobalTheory.SiegelSetGL
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.capelli_operator_algebra_stable_under_complex_conj : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a), (∀ o φ, act o (C φ) = C (act o φ)) → ∀ z ∈ Zalg E a, ∃ z' ∈ Zalg E a, ∀ φ, z (C φ) = C (z' φ) := by
  first | exact @GlobalTheory.CuspRep.ConjZalg.conj_Zalg | exact GlobalTheory.CuspRep.ConjZalg.conj_Zalg | (intros; apply GlobalTheory.CuspRep.ConjZalg.conj_Zalg <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.smooth_adelic_GL_complex_conj_commutes_operators : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ C : Sm E a ≃ₗ⋆[ℂ] Sm E a, (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) ∧ ∀ o φ, act o (C φ) = C (act o φ) := by
  first | exact @GlobalTheory.smooth_conj_commutes_act | exact GlobalTheory.smooth_conj_commutes_act | (intros; apply GlobalTheory.smooth_conj_commutes_act <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ), (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  first | exact @GlobalTheory.CuspRep.norm_le_of_unip_variation | exact GlobalTheory.CuspRep.norm_le_of_unip_variation | (intros; apply GlobalTheory.CuspRep.norm_le_of_unip_variation <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

theorem _root_.GlobalTheory.T.normalisedImageHeight_unique_frame : Quoted → ∀ (F : Type) [Field F] [NumberField F] (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω) (D : ℕ) (h h' : ℝ), IsTotallyComplex F → CompHt.IsImageHeight Nm W ev D h → CompHt.IsImageHeight Nm W ev D h' → h = h' := by
  first | exact @GlobalTheory.ImageHeightFrame.isImageHeight_unique | exact GlobalTheory.ImageHeightFrame.isImageHeight_unique | (intros; apply GlobalTheory.ImageHeightFrame.isImageHeight_unique <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etale_cohomology_equivalence_of_strictly_henselian_stalks : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → ∀ (U : Over S), Etale U.hom → ∀ n : ℤ, (∀ x : H R ((bc (α ≫ p)).obj U) F n, ∃ (V : Over S) (h : V ⟶ U) (y : H R ((bc p).obj V) F n), Etale V.hom ∧ Surjective h.left ∧ pull R ((bcMap α p).app V) F n y = pull R ((bc (α ≫ p)).map h) F n x) ∧ ∀ y : H R ((bc p).obj U) F n, pull R ((bcMap α p).app U) F n y = 0 → ∃ (V : Over S) (h : V ⟶ U), Etale V.hom ∧ Surjective h.left ∧ pull R ((bc p).map h) F n y = 0 := by
  first
  | exact @GlobalTheory.EtC.loc_glob_classes
  | exact GlobalTheory.EtC.loc_glob_classes
  | (intros; apply GlobalTheory.EtC.loc_glob_classes <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.mem_closure_rationalNormOne_of_idempotent_conj : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ ε : AF F, ε * ε = ε → ∀ g : DA F a b, nrm g = 1 → η • (g - 1) = g - 1 → ∀ c c' : DA F a b, c * c' = 1 → c' * c = 1 → c * g * c' ∈ closure (H0 (a := a) (b := b) ε) → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.Unconj.conj_mem_closure_normOne_of_idempotent | exact GlobalTheory.QSA.Unconj.conj_mem_closure_normOne_of_idempotent | (intros; apply GlobalTheory.QSA.Unconj.conj_mem_closure_normOne_of_idempotent <;> assumption)
end
