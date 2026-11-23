module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle122
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem norm_not_mem_sq {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (hd : u.asIdeal.inertiaDeg ℤ = 1) (he : u.asIdeal.ramificationIdx ℤ = 1) :
    ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 := by
  classical
  have hprime : Nat.Prime (Ideal.absNorm u.asIdeal) :=
    ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 u).2 hd
  haveI : Fact (Nat.Prime (Ideal.absNorm u.asIdeal)) := ⟨hprime⟩
  have hmemZ : ((Ideal.absNorm u.asIdeal : ℕ) : ℤ) ∈ u.asIdeal.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using Ideal.absNorm_mem u.asIdeal
  have hspan : u.asIdeal.under ℤ = Ideal.span {((Ideal.absNorm u.asIdeal : ℕ) : ℤ)} :=
    ((Int.ideal_span_isMaximal_of_prime (Ideal.absNorm u.asIdeal)).eq_of_le
      Ideal.IsPrime.ne_top' ((Ideal.span_singleton_le_iff_mem _).2 hmemZ)).symm
  have hp0 : u.asIdeal.under ℤ ≠ ⊥ := by
    rw [hspan, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hprime.ne_zero
  have he' : (u.asIdeal.under ℤ).ramificationIdx' u.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (u.asIdeal.under ℤ) u.asIdeal hp0]
    exact he
  have hmap : (u.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 F)) ≤ u.asIdeal := Ideal.map_comap_le
  intro hmem
  refine (Ideal.ramificationIdx'_ne_one_iff hmap).2 ?_ he'
  rw [hspan, Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
  simpa using hmem

private theorem dec_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {N : Subgroup (G F Ω)} (hNo : IsOpen (N : Set (G F Ω))) {B : ValuationSubring Ω}
    {u : HeightOneSpectrum (𝓞 F)} (hB : IsPlaceOver B u) (hI : Ine (F := F) B ≤ N) {σ : G F Ω}
    (hσ : IsFrob B (normV u) σ) (hσN : σ ∈ N) : Dec (F := F) B ≤ N := by
  intro d hd
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω B u hB ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((N.subgroupOf (Dec (F := F) B) : Subgroup (Dec (F := F) B)) : Set (Dec (F := F) B)) :=
    (N.isClosed_of_isOpen hNo).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) B) ⊔ (Ine (F := F) B).subgroupOf (Dec (F := F) B))
    (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hσN))
      (fun x hx => Subgroup.mem_subgroupOf.2 (hI (Subgroup.mem_subgroupOf.1 hx)))) hc
  rw [h] at h2
  exact Subgroup.mem_subgroupOf.1 (h2 (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := F) B)))

theorem splitPlace : SplitPlace := by
  intro F Ω _ _ _ _ _ U hU T hT
  obtain ⟨N, hNn, hNo, -, hNU⟩ := GlobalTheory.T.exists_openNormal_finiteIndex_le_absGaloisGroup Ω F U hU
  have hc : GlobalTheory.TwSys.Cheb :=
    GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne'
  unfold GlobalTheory.TwSys.Cheb at hc
  obtain ⟨v, hvA, hd, he, B, hB, hIB, σ, hσ, hσN⟩ := hc F Ω N hNo hNn 1 hT.toFinset
  have hvT : v ∉ T := fun h => hvA (hT.mem_toFinset.2 h)
  have hσN' : σ ∈ N := by simpa using hσN
  have hdec := dec_le hNo hB hIB hσ hσN'
  have hnorm : normV v = Ideal.absNorm v.asIdeal := by
    simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨v, hvT, ?_, ?_, ?_, ?_⟩
  · rw [hnorm]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd
  · rw [hnorm]
    exact Ideal.absNorm_mem _
  · rw [hnorm]
    exact norm_not_mem_sq v hd he
  · intro A hA ρ hρ
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver hB hA
    apply hNU
    have h1 : τ⁻¹ * ρ * τ ∈ Dec (F := F) B := by
      rw [mem_Dec] at hρ ⊢
      rw [← hτ] at hρ
      rw [mul_smul, mul_smul, hρ, ← mul_smul, inv_mul_cancel, one_smul]
    have h2 := hNn.conj_mem _ (hdec h1) τ
    simpa [mul_assoc] using h2

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameQuot

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem decPow : DecPow := by
  intro F Ω _ _ _ _ _ A t hA p hp hpt ζ hζ
  have hN : ¬ A.valuation (p : Ω) < 1 := by
    simpa using not_valuation_lt_one_of_isPlaceOver hpt hA 1
  have hz1 : ζ ^ p = 1 := hζ.pow_eq_one
  have hint : ζ ∈ IntCl F Ω :=
    IsIntegral.of_pow hp.pos (by rw [hz1]; exact isIntegral_one)
  have hv : A.valuation ζ ≤ 1 := by
    have h1 : A.valuation ζ ^ p = 1 := by rw [← map_pow, hz1, map_one]
    exact ((pow_eq_one_iff.1 h1).resolve_right hp.ne_zero).le
  refine ⟨fun g hg => ?_, fun τ hτ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_pow_cong hA hg {⟨ζ, hint⟩}
    refine ⟨i, eq_of_pow_eq_one A hN ?_ ?_ (hi ⟨ζ, hint⟩ (Finset.mem_singleton_self _))⟩
    · rw [← map_pow, hz1, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
  · exact eq_of_pow_eq_one A hN (by rw [← map_pow, hz1, map_one]) hz1 ((mem_Ine.1 hτ).2 ζ hv)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem valuation_apply_le_one_of_mem_dec {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (e : G F Ω) (he : e ∈ Dec A) (x : Ω) (hx : A.valuation x ≤ 1) : A.valuation (e x) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  have h2 := ValuationSubring.smul_mem_pointwise_smul e x A hx
  open Pointwise in
  have h3 : e • A = A := he
  rw [h3] at h2
  exact h2

private theorem valuation_apply_lt_one_of_mem_dec {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (e : G F Ω) (he : e ∈ Dec A) (z : Ω) (hz : A.valuation z < 1) : A.valuation (e z) < 1 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa using hz
  have hez : e z ≠ 0 := by simpa using hz0
  have key : 1 < A.valuation z⁻¹ := by
    rw [Valuation.one_lt_val_iff _ (inv_ne_zero hz0), inv_inv]
    exact hz
  have h1 : 1 < A.valuation (e z)⁻¹ := by
    by_contra hc
    push_neg at hc
    have h4 := valuation_apply_le_one_of_mem_dec A e⁻¹ (inv_mem he) _ hc
    have h5 : e⁻¹ (e z)⁻¹ = z⁻¹ := by
      rw [map_inv₀, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [h5] at h4
    exact absurd key (not_lt.mpr h4)
  rw [Valuation.one_lt_val_iff _ (inv_ne_zero hez), inv_inv] at h1
  exact h1

private theorem inv_mul_mul_mem_ine_of_mem_dec {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (d τ : G F Ω) (hd : d ∈ Dec A) (hτ : τ ∈ Ine A) :
    d⁻¹ * τ * d ∈ Ine A := by
  have hτD : τ ∈ Dec A := Ine_le_Dec A hτ
  obtain ⟨_, hτ2⟩ := hτ
  refine ⟨(Dec A).mul_mem ((Dec A).mul_mem ((Dec A).inv_mem hd) hτD) hd, fun x hx => ?_⟩
  have h1 := hτ2 (d x) (valuation_apply_le_one_of_mem_dec A d hd x hx)
  have h2 := valuation_apply_lt_one_of_mem_dec A d⁻¹ ((Dec A).inv_mem hd) _ h1
  have e : (d⁻¹ * τ * d) x - x = d⁻¹ (τ (d x) - d x) := by
    rw [map_sub, ← AlgEquiv.mul_apply d⁻¹ d, inv_mul_cancel, AlgEquiv.one_apply, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply]
  rw [e]
  exact h2

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.decGen :
    DecGen := by
  intro F Ω _ _ _ _ _ A v hAv φ hφ X hX hXI g hg
  set Y : Set Ω := {y | ∀ τ ∈ Ine (F := F) A, τ y = y} with hYdef
  have hφD : φ ∈ Dec A := hφ.1
  have hstab : ∀ (k : ℤ) (y : Ω), y ∈ Y → (φ ^ k) y ∈ Y := by
    intro k y hy τ hτ
    have h1 := hy _ (inv_mul_mul_mem_ine_of_mem_dec A (φ ^ k) τ (zpow_mem hφD k) hτ)
    have h2 := congrArg (φ ^ k) h1
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply (φ ^ k) (φ ^ k)⁻¹,
      mul_inv_cancel, AlgEquiv.one_apply] at h2
    exact h2
  let φ' : Dec A := ⟨φ, hφD⟩
  have hdense := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hAv φ' hφ
  have hP : ∀ h ∈ (Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)),
      ∃ k : ℤ, ∀ y ∈ Y, (h : G F Ω) y = (φ ^ k) y := by
    intro h hh
    rw [Subgroup.sup_eq_closure] at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ⟨k, fun y _ => by rw [Subgroup.coe_zpow]⟩
      · refine ⟨0, fun y hy => ?_⟩
        rw [zpow_zero, AlgEquiv.one_apply]
        exact hy _ (Subgroup.mem_subgroupOf.mp hx)
    | one => exact ⟨0, fun y _ => by rw [zpow_zero]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, fun z hz => ?_⟩
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply, hb z hz, ha _ (hstab b z hz), zpow_add,
        AlgEquiv.mul_apply]
    | inv x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨-a, fun z hz => ?_⟩
      have hw := ha _ (hstab (-a) z hz)
      have e1 : (φ ^ a) ((φ ^ (-a)) z) = z := by
        rw [← AlgEquiv.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, AlgEquiv.one_apply]
      rw [e1] at hw
      rw [Subgroup.coe_inv]
      calc ((x : G F Ω)⁻¹) z = ((x : G F Ω)⁻¹) ((x : G F Ω) ((φ ^ (-a)) z)) := by rw [hw]
        _ = (φ ^ (-a)) z := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Finite X := hX.to_subtype
  haveI : FiniteDimensional F (IntermediateField.adjoin F X) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let O : Set (Dec A) := Subtype.val ⁻¹' ((fun σ : G F Ω => g⁻¹ * σ) ⁻¹'
    ((IntermediateField.adjoin F X).fixingSubgroup : Set (G F Ω)))
  have hO : IsOpen O :=
    ((IntermediateField.adjoin F X).fixingSubgroup_isOpen.preimage (continuous_const_mul g⁻¹)).preimage
      continuous_subtype_val
  have hgO : (⟨g, hg⟩ : Dec A) ∈ O := by
    show g⁻¹ * g ∈ (IntermediateField.adjoin F X).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  have hmem : (⟨g, hg⟩ : Dec A) ∈
      ((Subgroup.zpowers φ' ⊔ (Ine A).subgroupOf (Dec A)).topologicalClosure : Set (Dec A)) := by
    rw [hdense]
    exact Subgroup.mem_top _
  rw [Subgroup.topologicalClosure_coe] at hmem
  obtain ⟨h, hhO, hhK⟩ := (mem_closure_iff.mp hmem) O hO hgO
  obtain ⟨k, hk⟩ := hP h hhK
  refine ⟨k, fun x hx => ?_⟩
  have hfix : g⁻¹ * (h : G F Ω) ∈ (IntermediateField.adjoin F X).fixingSubgroup := hhO
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix x
    (IntermediateField.subset_adjoin F X hx)
  have hxY : x ∈ Y := fun τ hτ => hXI τ hτ x hx
  rw [← hk x hxY]
  have h2 := congrArg g h1
  rw [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h2
  exact h2.symm
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def QuadDisj : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : Set (HeightOneSpectrum (𝓞 F)))
    (N : Subgroup (G F Ω)), (∀ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Ine (F := F) A ≤ N) →
    ∀ Q : QCM F Ω, RamOff T Q → GlobalTheory.AboveL.SolvDisj ↥Q.K N

def AllUnr : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (T : Set (HeightOneSpectrum (𝓞 Y)))
    (Q : QCM Y Ω), Step1 T Q → ∀ w : HeightOneSpectrum (𝓞 ↥Q.K),
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield ↥Q.K)) w.asIdeal

def Double : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))) (Q : QCM E Ω), Step0 T Q → ∀ t ∈ T,
    ∃ w₁ w₂ : HeightOneSpectrum (𝓞 ↥Q.K), w₁.under (𝓞 E) = t ∧ w₂.under (𝓞 E) = t ∧ GlobalTheory.Cong.Apart w₁ w₂

def ApartUp : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M],
    (∀ w₁ w₂ : HeightOneSpectrum (𝓞 M), GlobalTheory.Cong.Apart (w₁.under (𝓞 K)) (w₂.under (𝓞 K)) → GlobalTheory.Cong.Apart w₁ w₂) ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v

def ThreeApart : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T₁ : Set (HeightOneSpectrum (𝓞 E))) (Q₁ : QCM E Ω), Step0 T₁ Q₁ →
    ∀ (T₂ : Set (HeightOneSpectrum (𝓞 ↥Q₁.K))) (Q₂ : QCM ↥Q₁.K Ω), Step0 T₂ Q₂ → ∀ t ∈ T₁,
    (∀ w : HeightOneSpectrum (𝓞 ↥Q₁.K), w.under (𝓞 E) = t → w ∈ T₂) →
    ∀ (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra ↥Q₂.K M],
    ∃ w : Fin 3 → HeightOneSpectrum (𝓞 M), (∀ i, (((w i).under (𝓞 ↥Q₂.K)).under (𝓞 ↥Q₁.K)).under (𝓞 E) = t) ∧
      ∀ i j, i ≠ j → GlobalTheory.Cong.Apart (w i) (w j)

def SatSplit : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra K M]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)), IsPlaceOver A v → IsPlaceOver A w →
    (∀ g ∈ Dec (F := K) A, Fixes M g) → ∀ (a : ℕ) (π : CuspSub K a) (P : CuspSub M a),
    UpperTheory.CBC.SplitLift (UpperTheory.CBC.Cusp.cx π) (UpperTheory.CBC.Cusp.cx P) → ∀ B, (CG.mk π).HasSat v B → (CG.mk P).HasSat w B

theorem threeApart_of (h1 : Double) (h2 : ApartUp) : ThreeApart := by
  intro E Ω _ _ _ _ _ _ T₁ Q₁ s₁ T₂ Q₂ s₂ t ht hT M _ _ _ _
  obtain ⟨a, b, ha, hb, hab⟩ := h1 E Ω T₁ Q₁ s₁ t ht
  obtain ⟨x, y, hx, hy, hxy⟩ := h1 ↥Q₁.K Ω T₂ Q₂ s₂ a (hT a ha)
  obtain ⟨z, hz⟩ := (h2 ↥Q₁.K ↥Q₂.K).2 b
  have hxz : GlobalTheory.Cong.Apart x z := (h2 ↥Q₁.K ↥Q₂.K).1 x z (by rw [hx, hz]; exact hab)
  have hyz : GlobalTheory.Cong.Apart y z := (h2 ↥Q₁.K ↥Q₂.K).1 y z (by rw [hy, hz]; exact hab)
  choose up hup using (h2 ↥Q₂.K M).2
  refine ⟨fun i => up (![x, y, z] i), fun i => ?_, fun i j hij => (h2 ↥Q₂.K M).1 _ _ ?_⟩
  · rw [hup]
    fin_cases i
    · simpa [hx] using ha
    · simpa [hy] using ha
    · simpa [hz] using hb
  · rw [hup, hup]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact hxy | exact hxz | exact hyz | exact hxy.symm | exact hxz.symm | exact hyz.symm

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_conj (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] :
    ∃ (j : Ω →+* ℂ) (c : Ω ≃+* Ω), ∀ z, j (c z) = starRingEnd ℂ (j z) := by
  haveI : Normal ℚ Ω := normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  haveI : IsGalois ℚ Ω := ⟨⟩
  let j : Ω →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Ω) : Ω →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j
    (ComplexEmbedding.conjugate j) (Subsingleton.elim _ _)
  exact ⟨j, σ.symm.toRingEquiv, fun x => DFunLike.congr_fun hσ x⟩

private theorem conj_of_sq {w : ℂ} {q : ℕ} (hq : 0 < q) (h : w ^ 2 = (q : ℂ)) :
    starRingEnd ℂ w = w :=
  _root_.UpperTheory.Reformulated.B.Qh56.conj_of_sq hq h

private theorem sq_fix {E Y Ω : Type} [Field E] [Field Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    (δ : Y) (q : ℕ) (hq : δ ^ 2 = (q : Y))
    (hspan : ∀ y : Y, ∃ a b : E, y = algebraMap E Y a + algebraMap E Y b * δ)
    (g : Ω ≃+* Ω) (hδ : g (algebraMap Y Ω δ) = -algebraMap Y Ω δ)
    (hE : ∀ (j : E →+* Ω) (x : E), g (g (j x)) = j x) (j : Y →+* Ω) (y : Y) :
    g (g (j y)) = j y := by
  have h2 : (j δ) ^ 2 = (algebraMap Y Ω δ) ^ 2 := by
    rw [← map_pow, ← map_pow, hq, map_natCast, map_natCast]
  have hfix : g (g (j δ)) = j δ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp [hδ]
  obtain ⟨a, b, rfl⟩ := hspan y
  have ha := hE (j.comp (algebraMap E Y)) a
  have hb := hE (j.comp (algebraMap E Y)) b
  simp only [RingHom.comp_apply] at ha hb
  simp only [map_add (f := _), map_mul, ha, hb, hfix]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.twoPrimes :
    PrimeWith → TwoPrimes := by
  intro PW E Y Ω _ _ _ _ _ _ _ _ δ hδ M B hM
  obtain ⟨⟨q, hq0, hq⟩, hspan, s, hsE, hsδ⟩ := hδ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Y
  haveI : Algebra.IsAlgebraic Y Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ Y Ω
  obtain ⟨j0, c, hc⟩ := exists_conj Ω
  have hδ2 : (algebraMap Y Ω δ) ^ 2 = (q : Ω) := by rw [← map_pow, hq, map_natCast]
  have hcc : ∀ z, c (c z) = z := fun z => j0.injective (by rw [hc, hc, Complex.conj_conj])
  have hcδ : c (algebraMap Y Ω δ) = algebraMap Y Ω δ := j0.injective (by
    rw [hc]
    exact conj_of_sq hq0 (by rw [← map_pow, hδ2, map_natCast]))
  have hcroot : ∀ ξ : Ω, ξ ^ M = 1 → c ξ = ξ⁻¹ := fun ξ h => j0.injective (by
    have h1 : (j0 ξ) ^ M = 1 := by rw [← map_pow, h, map_one]
    rw [hc, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hM.ne')])
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hsc : ∀ (j : E →+* Ω) (x : E), s (c (j x)) = c (j x) :=
    fun j x => hsE ((c : Ω →+* Ω).comp j) x
  have hsinv : ∀ (j : E →+* Ω) (x : E), s.symm (j x) = j x := fun j x => by
    rw [RingEquiv.symm_apply_eq, hsE]
  have hsinvδ : s.symm (algebraMap Y Ω δ) = -algebraMap Y Ω δ := by
    rw [RingEquiv.symm_apply_eq, map_neg, hsδ, neg_neg]
  have h1δ : (s.trans c) (algebraMap Y Ω δ) = -algebraMap Y Ω δ := by
    show c (s _) = _
    rw [hsδ, map_neg, hcδ]
  have h11 : ∀ (j : Y →+* Ω) (y : Y), (s.trans c) ((s.trans c) (j y)) = j y :=
    sq_fix (E := E) δ q hq hspan (s.trans c) h1δ (fun j x => by
      show c (s (c (s (j x)))) = j x
      rw [hsE j x, hsc j x, hcc])
  have h22 : ∀ (j : Y →+* Ω) (y : Y), s.symm (s.symm (j y)) = j y :=
    sq_fix (E := E) δ q hq hspan s.symm hsinvδ (fun j x => by rw [hsinv, hsinv])
  obtain ⟨p₁, hp₁, hB, hz₁, hA₁⟩ := PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 (s.trans c) h1δ h11 M ζ hM hζ B
  obtain ⟨p₂, hp₂, hB₂, hz₂, hA₂⟩ := PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 s.symm hsinvδ h22 M ζ hM hζ p₁
  have hsζ : (s ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have e1 : (s ζ)⁻¹ = ζ ^ p₁ := by rw [← hcroot _ hsζ]; exact hz₁
  have e2 : ζ = (s ζ) ^ p₂ := by
    rw [← map_pow, ← hz₂, RingEquiv.apply_symm_apply]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdvd : M ∣ p₁ * p₂ + 1 := by
    refine hζ.dvd_of_pow_eq_one _ ?_
    rw [pow_succ, pow_mul, ← e1, inv_pow, ← e2, inv_mul_cancel₀ hζ0]
  refine ⟨p₁, p₂, hp₁, hp₂, hB, hB₂, hdvd, fun A hA h hh hδh y => ?_⟩
  have hle : ∀ n : ℕ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).2 (natCast_mem A n)
  rw [Nat.cast_mul, map_mul] at hA
  by_cases h₁ : A.valuation (p₁ : Ω) < 1
  · exact hA₁ A h₁ h hh hδh y
  · have e : A.valuation (p₁ : Ω) = 1 := le_antisymm (hle _) (not_lt.1 h₁)
    rw [e, one_mul] at hA
    exact hA₂ A hA h hh hδh y
end
