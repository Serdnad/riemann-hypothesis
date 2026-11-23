module

public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocF
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle496
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle646
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.AlgebraicWeights.IsAlgWeight
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKReal IsLocalRing Polynomial Formalism.BasicNotions.Examples₂.LB
open scoped Formalism.Per TensorProduct

namespace GlobalTheory.AinfK

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem l_res : ((l : ℕ) : ResidueField ↥(OL K)) = 0 := by
  rw [← map_natCast (residue ↥(OL K))]
  exact (residue_eq_zero_iff _).mpr (l_mem_max K)

theorem exists_card : ∃ a : ℕ, a ≠ 0 ∧ Nat.card (ResidueField ↥(OL K)) = l ^ a := by
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have : CharP (ResidueField ↥(OL K)) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (l_res K)
  obtain ⟨n, -, hn⟩ := FiniteField.card (ResidueField ↥(OL K)) l
  exact ⟨n, n.ne_zero, by rw [Nat.card_eq_fintype_card, hn]⟩

variable {K} {a : ℕ} [NeZero a]


omit [NeZero a] in
theorem res_pow (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : ResidueField ↥(OL K)) : x ^ l ^ a = x := by
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  rw [← h, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_teich (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : ↥(OL K)) :
    ∃ w : ↥(OL K), w ^ l ^ a = w ∧ residue _ w = residue _ x := by
  obtain ⟨_, hc, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete K
  have h1 := one_lt_pow_l l a
  have hm : (X ^ l ^ a - X : (↥(OL K))[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  obtain ⟨w, hw, hx⟩ := HenselianRing.is_henselian (I := maximalIdeal ↥(OL K)) _ hm x (by
      rw [← residue_eq_zero_iff]; simp [res_pow h]) (by
      change IsUnit (residue _ _)
      have : ((l : ResidueField ↥(OL K))) ^ a = 0 := by rw [l_res, zero_pow (NeZero.ne a)]
      simp [derivative_X_pow, this])
  refine ⟨w, by simpa [sub_eq_zero] using hw, ?_⟩
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hx

theorem exists_toOm (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : Om l) (hx : x ^ l ^ a = x) :
    ∃ w : ↥(OL K), toOm K w = x := by
  classical
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have h1 := one_lt_pow_l l a
  choose r hr using residue_surjective (R := ↥(OL K))
  choose s hs hs' using fun y => exists_teich h (r y)
  have hinj : Function.Injective fun y => toOm K (s y) := fun y z e => by
    rw [← hr y, ← hr z, ← hs', ← hs', toOm_injective K e]
  have hm : (X ^ l ^ a - X : (Om l)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  have hmem : ∀ y : Om l, y ∈ (X ^ l ^ a - X : (Om l)[X]).roots.toFinset ↔ y ^ l ^ a = y := fun y => by
    simp [mem_roots hm.ne_zero, sub_eq_zero]
  have hsub : Finset.univ.image (fun y => toOm K (s y)) = (X ^ l ^ a - X : (Om l)[X]).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
      rw [hmem, ← map_pow, hs]
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, h]
      refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
      rw [Polynomial.natDegree_X_pow_sub_X h1]
  obtain ⟨z, -, hz⟩ := Finset.mem_image.1 (hsub ▸ (hmem x).2 hx)
  exact ⟨_, hz⟩

theorem hasUnr (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) : HasUnr a K :=
  ⟨IntermediateField.adjoin_le_iff.2 fun x hx => by
    obtain ⟨w, rfl⟩ := exists_toOm h x hx
    exact (w : ↥K.1).2⟩

theorem pow_eq_of_root (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) {x : Om l} (hx : x ∈ K.1) {m : ℕ}
    (h0 : 0 < m) (hm : ¬ l ∣ m) (h1 : x ^ m = 1) : x ^ l ^ a = x := by
  have h2 : (⟨x, hx⟩ : ↥K.1) ∈ OL K := IsIntegral.of_pow h0 (by
    rw [show (⟨x, hx⟩ : ↥K.1) ^ m = 1 from Subtype.ext h1]; exact isIntegral_one)
  set y : ↥(OL K) := ⟨_, h2⟩
  have hy : y ^ m = 1 := Subtype.ext (Subtype.ext h1)
  obtain ⟨k, hk⟩ : ∃ k, l ^ a = k + 1 := ⟨l ^ a - 1, by have := one_lt_pow_l l a; omega⟩
  have hr0 : residue _ y ≠ 0 := ((IsUnit.of_pow_eq_one hy h0.ne').map _).ne_zero
  have hr : residue _ (y ^ k) = 1 := by
    have := res_pow h (residue _ y)
    rw [hk, pow_succ] at this
    rw [map_pow]
    exact mul_right_cancel₀ hr0 (by rw [this, one_mul])
  have hg := mul_geom_sum (y ^ k) m
  rw [← pow_mul, mul_comm k, pow_mul, hy, one_pow, sub_self] at hg
  have : CharP (ResidueField ↥(OL K)) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (l_res K)
  have hs : ∑ i ∈ Finset.range m, (y ^ k) ^ i ≠ 0 := fun e => hm (by
    have := congrArg (residue _) e

    simp only [map_sum, map_pow (residue _) (y ^ k), hr, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, map_zero] at this
    exact (CharP.cast_eq_zero_iff _ l m).1 this)
  have h3 : y ^ k = 1 := sub_eq_zero.1 ((mul_eq_zero.1 hg).resolve_right hs)
  have h4 : x ^ k = 1 := congrArg (toOm K) h3
  rw [hk, pow_succ, h4, one_mul]

theorem Kunr_eq (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) : Kunr l a = K0 K := by
  refine le_antisymm (le_inf (hasUnr h).le (Kunr_le_Kur l a)) ?_
  have key : ∀ c ∈ K0 K, ‖c‖ ≤ 1 → c ∈ Kunr l a := fun c hc h1 => by
    obtain ⟨n, z, ω, hω, rfl⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c hc h1
    refine sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    obtain ⟨h2, m, h0, hm, h3⟩ := hω i
    exact IntermediateField.subset_adjoin _ _ (pow_eq_of_root h h2.1 h0 hm h3)
  intro c hc
  rcases le_total ‖c‖ 1 with h1 | h1
  · exact key c hc h1
  · exact inv_mem_iff.1 (key _ (inv_mem hc) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h1))


variable (l a) in
theorem free_Wq : Module.Free ℤ_[l] (Wq l a) := by
  have := GlobalTheory.TameFrob.finite_Wq l a
  have : FaithfulSMul ℤ_[l] (Wq l a) := (faithfulSMul_iff_algebraMap_injective _ _).2 fun u v h => by
    have := congrArg (GlobalTheory.TameFrob.iotaO l a) h
    simp only [GlobalTheory.TameFrob.iotaO_algebraMap] at this
    exact Subtype.val_injective ((algebraMap ℚ_[l] (Om l)).injective this)
  infer_instance


variable (l a) in
theorem finrank_Wq : Module.finrank ℤ_[l] (Wq l a) = a := by
  have := free_Wq l a
  have h := (splitEquiv (AlgHom.id ℤ_[l] (Wq l a))).toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange] at h
  simpa using h


attribute [local instance] GlobalTheory.TameFrob.algK GlobalTheory.TameFrob.isFractionRing in
variable (l a) in
theorem finrank_Kunr : Module.finrank ℚ_[l] ↥(Kunr l a) = a := by
  have := GlobalTheory.TameFrob.finite_Wq l a
  have : IsScalarTower ℤ_[l] (Wq l a) ↥(Kunr l a) := IsScalarTower.of_algebraMap_eq fun u =>
    Subtype.ext (GlobalTheory.TameFrob.iotaO_algebraMap l a u).symm
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing ℤ_[l] ℚ_[l] (Wq l a) ↥(Kunr l a), finrank_Wq]

variable (K)

def fK : ℕ := Module.finrank ℚ_[l] ↥(K0 K)

theorem card_res' : fK K ≠ 0 ∧ Nat.card (ResidueField ↥(OL K)) = l ^ fK K := by
  obtain ⟨a, ha, h⟩ := exists_card K
  have : NeZero a := ⟨ha⟩
  have e : fK K = a := by rw [fK, ← Kunr_eq h, finrank_Kunr]
  rw [e]
  exact ⟨ha, h⟩

instance : NeZero (fK K) := ⟨(card_res' K).1⟩

theorem card_res : Nat.card (ResidueField ↥(OL K)) = l ^ fK K := (card_res' K).2

theorem Kunr_fK : Kunr l (fK K) = K0 K := Kunr_eq (card_res K)

end GlobalTheory.AinfK
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeSatakeEigen

theorem exists_satU_eigenvector : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  intro K _ _ _ ϖ σ q n hU V _ _ _ T hadd hsmul h1 hmul x₀ hx₀
  haveI : Nontrivial V := ⟨⟨x₀, 0, hx₀⟩⟩
  have hcomm : ∀ a b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T a.1 * T b.1 = T b.1 * T a.1 := by
    intro a b
    rw [← hmul _ a.2 _ b.2, ← hmul _ b.2 _ a.2, GlobalTheory.UnitarySwap.heckeCommU K ϖ σ q n ℂ hU _ a.2 _ b.2]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.exists_common_eigenvector_of_commute
    (fun b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) => T b.1) hcomm
  choose c hc using hx
  have hinj : Function.Injective fun a : ℂ => a • x := smul_left_injective ℂ hx0
  let l : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) →ₗ[ℂ] ℂ :=
    { toFun := c
      map_add' := fun a b => hinj (by
        show c (a + b) • x = (c a + c b) • x
        rw [← hc, add_smul, ← hc, ← hc]
        show T (a.1 + b.1) x = _
        rw [hadd _ a.2 _ b.2]; rfl)
      map_smul' := fun r a => hinj (by
        show c (r • a) • x = (r * c a) • x
        rw [← hc, mul_smul, ← hc]
        show T (r • a.1) x = _
        rw [hsmul r _ a.2]; rfl) }
  have hl1 : l ⟨_, Formalism.UG.Final.DosetIndMem _ _ ℂ 1⟩ = 1 := hinj (by
    show c _ • x = (1 : ℂ) • x
    rw [← hc, one_smul]
    show T (Formalism.UG.dosetInd ℂ _ 1) x = x
    rw [h1]; rfl)
  have hlm : ∀ f f' : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n),
      l ⟨_, Formalism.UG.Final.HeckeConvMem _ _ ℂ (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n) _ f.2 _ f'.2⟩ = l f * l f' :=
    fun f f' => hinj (by
      show c _ • x = (c f * c f') • x
      rw [← hc]
      show T (Formalism.UG.conv _ f.1 f'.1) x = _
      rw [hmul _ f.2 _ f'.2, Module.End.mul_apply, hc f', map_smul, hc f, smul_smul, mul_comm])
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq hU l hl1 hlm
  refine ⟨fun i => (α i : ℂ), x, hx0, fun h hh => ?_⟩
  rw [hc ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.HeckeSatakeEigen
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.TameCharDet

open scoped Pointwise

theorem eq_of_pow_eq_one_of_val_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ)
    (hn : ¬ A.valuation (n : Ω) < 1) {ξ ξ' : Ω} (h : ξ ^ n = 1) (h' : ξ' ^ n = 1)
    (hlt : A.valuation (ξ - ξ') < 1) : ξ = ξ' := by
  first
  | exact @_root_.GlobalTheory.RootValuationOne.main
  | exact _root_.GlobalTheory.RootValuationOne.main
  | (apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootValuationOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootValuationOne.main ..)

theorem eq_of_tameChar : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ γ : Formalism.ConjugateSelfDual.G E Ω, TameGenAt A γ → ∀ (K : Type) [Field K] [TopologicalSpace K] [T2Space K] (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ), Continuous r → ∀ n : ℕ, 0 < n → ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ σ ∈ Ine (F := E) A, r σ ^ n = 1) → ∀ (π : Ω) (e : E), π ≠ 0 → π ^ n = algebraMap E Ω e → orderOf (γ π / π) = n → ∀ σ ∈ Ine (F := E) A, A.valuation (σ π / π - γ π / π) < 1 → r σ = r γ := by
  intro E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr n hn hnv hI π e hπ he hord σ hσ hσv
  have hn0 : n ≠ 0 := hn.ne'
  have hnA : ¬ A.valuation (n : Ω) < 1 := by
    intro h
    apply hnv
    rw [← hA]
    simpa using h
  set ζ := γ π / π with hζ
  have hζn : ζ ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one ζ
  have hγn : r γ ^ n = 1 := hI γ hγ.1
  have hred : ∀ {M : Type} [Monoid M] (x : M), x ^ n = 1 → ∀ a : ℕ, x ^ a = x ^ (a % n) := by
    intro M _ x hx a
    conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hx, one_pow, one_mul]
  have hvζ : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ n = 1 := by rw [← map_pow, hζn, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hl | he | hg
    · exact absurd hp (pow_lt_one₀ zero_le' hl hn0).ne
    · exact he
    · exact absurd hp (one_lt_pow₀ hg hn0).ne'

  have hfixζ : ∀ τ ∈ Ine (F := E) A, τ ζ = ζ := by
    intro τ hτ
    refine eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn (hτ.2 ζ hvζ.le)
    rw [← map_pow, hζn, map_one]

  have hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π := by
    intro τ hτ
    have h1 : (τ π / π) ^ n = 1 := by
      rw [div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
      rw [← he]; exact pow_ne_zero _ hπ
    have h2 := eq_of_pow_eq_one_of_val_lt A n hnA h1 (one_pow n) (hτ π hπ)
    rwa [div_eq_one_iff_eq hπ] at h2

  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1 := by
    intro τ hτ
    by_contra hne
    have hd : orderOf (r τ) ∣ n := orderOf_dvd_of_pow_eq_one (hI τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
    have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
    have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
      intro h
      apply hnv
      obtain ⟨c, hc⟩ := hd
      rw [hc, hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
    have h1 : r (τ ^ k) = 1 := by
      refine GlobalTheory.TameGenPowers.eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
        (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
      rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    rw [map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have ho : orderOf (r τ) ≠ 0 := fun h => hn0 (by simpa [h] using hd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ho (by simpa using hk)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
    rw [hk] at h3
    have := hl.two_le
    have := Nat.pos_of_ne_zero hk0
    nlinarith

  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hfixH : ∀ τ g : Formalism.ConjugateSelfDual.G E Ω, g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup →
      (τ * g) π = τ π := by
    intro τ g hg
    rw [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π
      (IntermediateField.mem_adjoin_simple_self E π)]
  have hopen : ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup,
      τ * g ∈ U) → IsOpen U := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    rw [← map_mul_left_nhds_one τ]
    exact Filter.mem_map.2 (Filter.mem_of_superset (hHo.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)
  have hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopen _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [hfixH τ g hg]
  let T : Set (Formalism.ConjugateSelfDual.G E Ω) := ⋃ a ∈ Finset.range n, {τ | r τ = r γ ^ a ∧ τ π = ζ ^ a * π}
  have hTc : IsClosed T := by
    refine isClosed_biUnion_finset fun a _ => ?_
    exact (isClosed_singleton.preimage hr).inter (hloc _)

  let P : Formalism.ConjugateSelfDual.G E Ω → Prop := fun τ =>
    τ ∈ Ine (F := E) A ∧ ∃ a : ℕ, r τ = r γ ^ a ∧ τ π = ζ ^ a * π
  have hP : ∀ τ ∈ Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), P τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩
      · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero],
          by rw [hfixπ x hx, pow_zero, one_mul]⟩
    | one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      obtain ⟨hyI, b, hb, hbπ⟩ := ihy
      refine ⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩
      rw [AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]
      ring
    | inv x _ ihx =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      have hiI : x⁻¹ ∈ Ine (F := E) A := inv_mem hxI
      have hex : a * (n - 1) + a = a * n := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      refine ⟨hiI, a * (n - 1), ?_, ?_⟩
      · rw [map_inv, ha]
        symm
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, hex, pow_mul', hγn, one_pow]
      · have hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π := by
          rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
          have h2 := congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ
          rw [hxx, map_mul, map_pow, hfixζ _ hiI] at h2
          exact h2
        calc (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π = ζ ^ (a * (n - 1) + a) * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
              rw [hex, pow_mul', hζn, one_pow, one_mul]
          _ = ζ ^ (a * (n - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring
          _ = ζ ^ (a * (n - 1)) * π := by rw [← h1]
  have hST : ((Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
        Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T := by
    intro τ hτ
    obtain ⟨-, a, ha, haπ⟩ := hP τ hτ
    refine Set.mem_biUnion (x := a % n) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_
    exact ⟨by rw [ha, hred _ hγn a], by rw [haπ, hred _ hζn a]⟩
  have hσT : σ ∈ T := closure_minimal hST hTc (hγ.2 hσ)
  obtain ⟨a, ha, haπ⟩ : ∃ a : ℕ, r σ = r γ ^ a ∧ σ π = ζ ^ a * π := by
    simp only [T, Set.mem_iUnion] at hσT
    obtain ⟨a, -, h⟩ := hσT
    exact ⟨a, h⟩
  have hq : σ π / π = ζ ^ a := by rw [haπ, mul_div_assoc, div_self hπ, mul_one]
  rw [hq] at hσv
  have hζa : ζ ^ a = ζ := by
    refine eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn hσv
    rw [← pow_mul, mul_comm, pow_mul, hζn, one_pow]
  have hmod : a ≡ 1 [MOD n] := by
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · have h1 : orderOf ζ = 1 := orderOf_eq_one_iff.2 (by rw [← hζa, pow_zero])
      rw [← hord, h1]; exact Nat.modEq_one
    · have hζ0 : ζ ≠ 0 := by
        intro h; rw [h, zero_pow hn0] at hζn; exact zero_ne_one hζn
      have h1 : ζ ^ (a - 1) = 1 := by
        have h3 : ζ ^ (a - 1) * ζ = 1 * ζ := by
          rw [← pow_succ, Nat.sub_add_cancel ha0, hζa, one_mul]
        exact mul_right_cancel₀ hζ0 h3
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at h2
      exact ((Nat.modEq_iff_dvd' ha0).2 h2).symm
  rw [ha]
  conv_rhs => rw [← pow_one (r γ)]
  exact (pow_eq_pow_iff_modEq).2 (hmod.of_dvd (orderOf_dvd_of_pow_eq_one hγn))

end GlobalTheory.TameCharDet
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_apply_eq_pow_of_pow_pow_eq : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l), ∃ m : ZMod a, ∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val := by
  first | exact @GlobalTheory.FrobAction.galois_pow_frobenius | exact GlobalTheory.FrobAction.galois_pow_frobenius | (intros; apply GlobalTheory.FrobAction.galois_pow_frobenius <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

theorem _root_.GlobalTheory.T.exists_inertia_mul_galois_compositum : ∀ (l : ℕ) [Fact l.Prime] (K' F K'' : FinExt l), (GK K').Normal → K''.1 = K'.1 ⊔ F.1 → ∀ h : GQ l, h ∈ GK F → (∀ x ∈ K0 K'', h x = x) → ∃ i : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)), i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (i : GQ l) ∈ GK F ∧ (i : GQ l)⁻¹ * h ∈ GK K'' := by
  first | exact @GlobalTheory.InertiaLift.lift | exact GlobalTheory.InertiaLift.lift | (intros; apply GlobalTheory.InertiaLift.lift <;> assumption)
end
