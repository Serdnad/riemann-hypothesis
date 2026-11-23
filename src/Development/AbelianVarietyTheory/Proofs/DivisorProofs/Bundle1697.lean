module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle848
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.ReductionIwasawa
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1657
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Mathlib.RingTheory.DedekindDomain.Factorization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem rat_mem_adicCompletionIntegers_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  apply _root_.GlobalTheory.FinClsLoc.ratInt_eventually <;> assumption

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} (b : Module.Basis κ ℚ C) (v : HeightOneSpectrum ℤ)

theorem repr_tmul_apply (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

theorem eq_sum_tmul [Fintype κ] (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

theorem isIntB_mul_star_eventually : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (σ : C →+* Cᵐᵒᵖ) (κ : Type)
    (b : Module.Basis κ ℚ C), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) ∧
      (∀ y, IsIntB v b y → IsIntB v b (starT σ (v.adicCompletion ℚ) y).unop) := by
  intro C _ _ _ σ κ b
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (σ (b t.1)).unop t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (hc.and hs)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨hcv, hsv⟩ := hv
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_

    rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : κ → (v.adicCompletion ℚ ⊗[ℚ] C)ᵐᵒᵖ), (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : v.adicCompletion ℚ ⊗[ℚ] C ≃+ _).symm f Finset.univ

    rw [eq_sum_tmul b v y, map_sum, hu, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.AdicSpan
end
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.pMinus_annihilates_lowestKType_holomorphicChamber : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), GlRel E → IsUnitary ε E → StrictAnti lam → IsHolChamber ε lam → IsMin ε E lam → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = lowK ε lam) → ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0 := by
  first | exact @GlobalTheory.HolDS.pMinus_kills_lowest | exact GlobalTheory.HolDS.pMinus_kills_lowest | (intros; apply GlobalTheory.HolDS.pMinus_kills_lowest <;> assumption)
end

section

open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset)
open CompanionTheory.D.LK (IsKMod)

theorem GlobalTheory.T.kFiniteModule_irreducible_of_irreducible_unitaryRep :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
      (E : Fin n → Fin n → Module.End ℂ D),
      CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E →
      ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ :=
  @GlobalTheory.KFinIrr.kMod_irred
end

section

set_option autoImplicit false

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PrimePart

theorem ker_isMaximal_card {E k : Type} [Field E] [NumberField E] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : 𝓞 E →+* k) :
    (RingHom.ker f).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ RingHom.ker f) = p ^ h := by
  have hp : p.Prime := Fact.out
  have hmem : ((p : ℕ) : 𝓞 E) ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero k p
  have hne : RingHom.ker f ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hp.ne_zero (Nat.cast_eq_zero.1 hmem)
  have hmax : (RingHom.ker f).IsMaximal := (RingHom.ker_isPrime f).isMaximal hne
  refine ⟨hmax, ?_⟩
  haveI : Finite (𝓞 E ⧸ RingHom.ker f) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI : Fintype (𝓞 E ⧸ RingHom.ker f) := Fintype.ofFinite _
  letI : Field (𝓞 E ⧸ RingHom.ker f) := Ideal.Quotient.field _
  haveI : CharP (𝓞 E ⧸ RingHom.ker f) p := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk (RingHom.ker f)), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ RingHom.ker f) p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem primeBelow_isMaximal_card (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (τ : E →+* ℂ) :
    (primeBelow io X τ).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h := by
  haveI := charP_residueField_of_irreducible X
  rw [primeBelow_eq_ker]
  exact ker_isMaximal_card p (red io X τ)

end GlobalTheory.PrimePart
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.DepthMono

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) : Fin d' → MvPowerSeries (Fin d) C :=
  fun b => ∑ a, M b a • (X a : MvPowerSeries (Fin d) C)

theorem constantCoeff_linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) (b : Fin d') :
    constantCoeff (linSub M b) = 0 := by
  simp [linSub]

theorem subst_expOf_hom {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    (c : Fin d') : subst (expOf G) (φ c) = subst (linSub M) (expOf G' c) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hE' : HasSubst (expOf G') := hasSubst_of_constantCoeff_zero (isExp_expOf G').1
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.1
  have hL : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hlg' : HasSubst G'.lg := hasSubst_of_constantCoeff_zero G'.lg_const
  set ψ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (expOf G) (φ c) with hψ
  set ρ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (linSub M) (expOf G' c) with hρ
  have hψ0 : ∀ c, constantCoeff (ψ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hE (isExp_expOf G).1 (hφ.1 c)
  have hρ0 : ∀ c, constantCoeff (ρ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hL (constantCoeff_linSub M) ((isExp_expOf G').1 c)
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hρs : HasSubst ρ := hasSubst_of_constantCoeff_zero hρ0
  have key : ∀ b, subst ψ (G'.lg b) = subst ρ (G'.lg b) := by
    intro b
    have h1 : subst ψ (G'.lg b) = subst (expOf G) (subst φ (G'.lg b)) :=
      (subst_comp_subst_apply hφs hE (G'.lg b)).symm
    have h2 : subst ρ (G'.lg b) = subst (linSub M) (subst (expOf G') (G'.lg b)) :=
      (subst_comp_subst_apply hE' hL (G'.lg b)).symm
    rw [h1, h2, hφ.2.2, (isExp_expOf G').2, subst_sum_smul hE, subst_X hL]
    simp only [(isExp_expOf G).2, linSub]
  have inj : ∀ c, ψ c = subst (fun b => subst ψ (G'.lg b)) (expOf G' c) ∧
      ρ c = subst (fun b => subst ρ (G'.lg b)) (expOf G' c) := by
    intro c
    constructor
    · rw [← subst_comp_subst_apply hlg' hψs, subst_lg_expOf, subst_X hψs]
    · rw [← subst_comp_subst_apply hlg' hρs, subst_lg_expOf, subst_X hρs]
  show ψ c = ρ c
  rw [(inj c).1, (inj c).2, funext key]

theorem subst_exp_hom {τ : Type} {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    {L : Fin d → MvPowerSeries τ C} (hL0 : ∀ e, constantCoeff (L e) = 0) (c : Fin d') :
    subst (fun e => (subst L (expOf G e) : MvPowerSeries τ C)) (φ c) =
      (subst (fun b => ∑ a, M b a • L a) (expOf G' c) : MvPowerSeries τ C) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hM : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero hL0
  rw [← subst_comp_subst_apply hE hL, subst_expOf_hom hφ, subst_comp_subst_apply hM hL]
  congr 1
  funext b
  rw [linSub, subst_sum_smul hL]
  simp only [subst_X hL]

theorem detDepth_le_of_isIntHom : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)),
    ∀ (i d d' k : ℕ) (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C)
      (M : Matrix (Fin d') (Fin d) C), IsIntHom G G' φ M → ∀ u : Fin i → Fin d → C,
      detDepth G u k ≤ detDepth G' (fun a => M.mulVec (u a)) k := by
  intro C _ _ v i d d' k G G' φ M hφ u
  have hX : ∀ b : Fin i, HasSubst
      (fun e : Fin d => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) := fun b =>
    hasSubst_of_constantCoeff_zero fun e => by simp
  let Φ : (Σ _ : Fin i, Fin d') → MvPowerSeries (Σ _ : Fin i, Fin d) C := fun x =>
    subst (fun e : Fin d => (X ⟨x.1, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (φ x.2)
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero (hX x.1) (fun e => by simp) (hφ.1 x.2)
  have hΦi : ∀ x, MvIsInt v (Φ x) := fun x =>
    ptIntSer_subst (v := v) (hX x.1) (fun e => ptIntSer_X _) (hφ.2.1 x.2)
  have hL0 : ∀ (b : Fin i) (e : Fin d), constantCoeff
      (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := fun b e => by simp
  have hA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
    hasSubst_of_constantCoeff_zero fun x =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hL0 x.1)) (hL0 x.1)
        ((isExp_expOf G).1 x.2)
  have hcol : (fun x => subst (expAlong (fun _ : Fin i => G) (fun _ => u)) (Φ x)) =
      expAlong (fun _ : Fin i => G') (fun _ a => M.mulVec (u a)) := by
    funext x
    simp only [Φ]
    rw [subst_comp_subst_apply (hX x.1) hA]
    simp only [subst_X hA, expAlong]
    rw [subst_exp_hom hφ (hL0 x.1)]
    congr 1
    funext b
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  refine le_iInf fun f => iInf_le_of_le ⟨subst Φ f.1, ptIntSer_subst (v := v) hΦ hΦi f.2⟩ (le_of_eq ?_)
  simp only
  rw [subst_comp_subst_apply hΦ hA, hcol]

end GlobalTheory.DepthMono
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit
namespace GlobalTheory.StdRescale

theorem exists_isStd_mulShift : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∃ a : F, a ≠ 0 ∧ IsStd (ψ.mulShift (algebraMap F (AF F) a)) := by
  intro F _ _ hF ψ h
  haveI := hF
  obtain ⟨a₀, ha₀, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling h
  have him : ∀ (w : InfinitePlace F) (x : F), (w.embedding x).im = 0 := fun w x => by
    have := congrArg Complex.im (GlobalTheory.AdeleCharConductor.embedding_re w x)
    simpa using this.symm
  have hkey : ∀ w : InfinitePlace F, (w.embedding a₀).re * (w.embedding (-a₀⁻¹)).re = -1 := fun w => by
    have := congrArg Complex.re
      (show w.embedding (a₀ * -a₀⁻¹) = -1 by rw [mul_neg, mul_inv_cancel₀ ha₀, map_neg, map_one])
    rw [map_mul, Complex.mul_re, him, him, mul_zero, sub_zero] at this
    simpa using this
  refine ⟨-a₀⁻¹, neg_ne_zero.2 (inv_ne_zero ha₀), ?_, ?_, ?_⟩
  · exact h.1.comp (continuous_const.mul continuous_id)
  · intro x
    rw [AddChar.mulShift_apply, ← map_mul]
    exact h.2.2.1 _
  · intro b hb
    have hu : evI F (pairA F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    have hb2 : b.2 = 0 := by
      have h0 := congrArg Prod.snd (hb (pairA F 0 1) hu)
      change (1 : Af F) * b.2 = 0 at h0
      rwa [one_mul] at h0
    have e1 : algebraMap F (AF F) (-a₀⁻¹) * b = pairA F (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) 0 := by
      refine Prod.ext rfl ?_
      change (algebraMap F (AF F) (-a₀⁻¹)).2 * b.2 = 0
      rw [hb2, mul_zero]
    have hterm : ∀ w : InfinitePlace F, (w.embedding a₀).re *
        (InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w)).re =
        -(InfinitePlace.Completion.extensionEmbedding w (b.1 w)).re := fun w => by
      rw [show (algebraMap F (Ainf F) (-a₀⁻¹) * b.1) w = algebraMap F (Ainf F) (-a₀⁻¹) w * b.1 w from rfl, map_mul, GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap, Complex.mul_re, him,
        zero_mul, sub_zero, ← mul_assoc, hkey, neg_one_mul]
    rw [AddChar.mulShift_apply, e1]
    show psiInf F ψ _ = _
    rw [hinf, GlobalTheory.WrongSignPair.trace_evI]
    simp only [hterm, Finset.sum_neg_distrib]
    push_cast
    ring_nf

end GlobalTheory.StdRescale
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.KilledFinCentre

theorem centre_orbit_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (q : (E →+* ℂ) → ℂ → Polynomial ℂ), (∀ τ u, q τ u ≠ 0) → ∃ (X' : Set (Module.End ℂ (Sm E b) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E b) → ℂ) (u : Sm E b), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b) → u ≠ 0 → (∀ z ∈ Zalg E b, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E b, χ' z = χ z := by
  intro E _ _ _ b q hq
  classical
  obtain ⟨T, hT, hZ⟩ := GlobalTheory.T.zalg_eq_adjoin_finite_capelli E b
  let p : Module.End ℂ (Sm E b) → Polynomial ℂ := fun t =>
    if h : ∃ τ u, t = cap τ u then q h.choose h.choose_spec.choose else 1
  have hp : ∀ t ∈ T, p t ≠ 0 := by
    intro t ht
    simp only [p]
    split_ifs with h
    · exact hq _ _
    · exact one_ne_zero
  have hkill : ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) →
      ∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0 := by
    intro ψ hψ t ht
    have h : ∃ τ u, t = cap τ u := hT t ht
    have key : ∀ τ u, t = cap τ u → Polynomial.aeval t (q τ u) ψ = 0 := by
      rintro τ u rfl; exact hψ τ u
    simp only [p, dif_pos h]
    exact key _ _ h.choose_spec.choose_spec
  have hc : ∀ s ∈ T, ∀ t ∈ T, Commute s t := fun s hs t ht =>
    GlobalTheory.AutGrowth.KilledFin.Zalg_commute (hZ ▸ Algebra.subset_adjoin hs) (hZ ▸ Algebra.subset_adjoin ht)
  obtain ⟨X', hX', hX'e⟩ := GlobalTheory.T.exists_mem_eigencharacters_of_eigenvector _ T p hc hp
  refine ⟨X', ∏ t ∈ T, (p t).natDegree, hX', fun ψ hψ => ?_⟩
  rw [hZ]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated _ T p hc hp ψ (hkill ψ hψ)
  exact ⟨h1, h2, hX'e ψ (hkill ψ hψ)⟩

end GlobalTheory.KilledFinCentre
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

theorem _root_.GlobalTheory.T.rationalGL_boundedSize_compactFinite_polynomialCount : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  first | exact @GlobalTheory.ratGL_bounded_count | exact GlobalTheory.ratGL_bounded_count | (intros; apply GlobalTheory.ratGL_bounded_count <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : Set (AdelicGLn.AdelicGL E a)), IsCompact ω → ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) → ∀ t : ℝ, 0 < t → ∃ (Ω : Set (GL (Fin a) (Cinf E))) (Kf : Set (GL (Fin a) (Af E))), IsCompact Ω ∧ IsCompact Kf ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, ∀ k ∈ maxCompact (K := E) (n := a), ∃ c ∈ Ω, ∃ f ∈ Kf, b * infGL E a d * k = infGL E a (d * c) * finGL E a f := by
  first | exact @GlobalTheory.SiegelSetGL.exists_compact_decomp | exact GlobalTheory.SiegelSetGL.exists_compact_decomp | (intros; apply GlobalTheory.SiegelSetGL.exists_compact_decomp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory

def CuspRep.CuspSub.mapConj {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (π : CuspSub E a) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hact : ∀ o φ, act o (C φ) = C (act o φ))
    (hcusp : ∀ φ : Sm E a, IsCuspForm φ → IsCuspForm (C φ)) : CuspSub E a where
  V := π.V.map C.toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact hcusp φ (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable o φ hφ, (hact o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := C)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap C.toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← C.injective h2]) fun o φ hφ => by
      change C (act o φ) ∈ W
      rw [← hact]
      exact hs o _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := C.toLinearMap) C.surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem exists_conj_cuspSub : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a),
    ∃ (π' : CuspSub E a) (J : π.V ≃ₗ⋆[ℂ] π'.V), ∀ o φ, J (π.op o φ) = π'.op o (J φ) := by
  intro E _ _ _ a π
  obtain ⟨C, hC, hact⟩ := GlobalTheory.T.smooth_adelic_GL_complex_conj_commutes_operators E a
  have hZ := GlobalTheory.T.capelli_operator_algebra_stable_under_complex_conj E a C hact
  have hcusp := isCuspForm_of_conj_pointwise E a C hC hact hZ
  refine ⟨π.mapConj C hact hcusp, C.submoduleMap π.V, fun o φ => Subtype.ext ?_⟩
  exact (hact o φ.1).symm

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.normOneQuaternion_near_conj_rational_times_supported : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → ε • (g - 1) = 0 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ w ∈ W, ∃ y : DA F a b, IsUnit (nrm y) ∧ ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ y * w = rat γ * y * h := by
  first | exact @GlobalTheory.QSAStep.key_step | exact GlobalTheory.QSAStep.key_step | (intros; apply GlobalTheory.QSAStep.key_step <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.strongApproximation_normOne_splitQuaternionAlgebra : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.strongApprox_split | exact GlobalTheory.QSA.strongApprox_split | (intros; apply GlobalTheory.QSA.strongApprox_split <;> assumption)
end
