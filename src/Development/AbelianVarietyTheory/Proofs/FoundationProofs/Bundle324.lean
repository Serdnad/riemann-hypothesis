module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle198
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThKill

theorem cgA_natCast {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (l n a b : ℕ)
    (h : ((a : ℕ) : ZMod (l ^ n)) = ((b : ℕ) : ZMod (l ^ n))) : CgA A l n (a : Ω) (b : Ω) := by
  have h' : ((a : ℤ) : ZMod (l ^ n)) = ((b : ℤ) : ZMod (l ^ n)) := by exact_mod_cast h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
  obtain ⟨k, hk⟩ := h'
  refine ⟨((-k : ℤ) : Ω), intCast_mem A (-k), ?_⟩
  have hk' : ((b : ℤ) : Ω) - ((a : ℤ) : Ω) = ((l : ℤ) : Ω) ^ n * (k : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hk
    push_cast at this ⊢
    linear_combination this
  push_cast at hk' ⊢
  linear_combination -hk'

theorem cgA_trans {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ} {x y z : Ω}
    (h1 : CgA A l n x y) (h2 : CgA A l n y z) : CgA A l n x z := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, add_mem ha hb, by linear_combination e1 + e2⟩

theorem cgA_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ} {x y t : Ω}
    (h : CgA A l n x y) (ht : t ∈ A) : CgA A l n (x * t) (y * t) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨a * t, mul_mem ha ht, by linear_combination t * e⟩

theorem gamma1_le_of_dvd {N M : ℕ} (h : N ∣ M) :
    CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma1 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have key : ∀ x y : ℤ, ((x : ZMod M)) = (y : ZMod M) → (x : ZMod N) = (y : ZMod N) := by
    intro x y hxy
    have := congrArg (ZMod.castHom h (ZMod N)) hxy
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · simpa using key _ 1 (by simpa using h1)
  · simpa using key _ 1 (by simpa using h2)
  · simpa using key _ 0 (by simpa using h3)

theorem isThB_level_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω)
    (N M l n : ℕ) [Fact l.Prime] (b : X.Fn l) (φ : HahnSeries ℚ Ω) (h : IsThB X A N l n b φ) :
    IsThB X A (N * M) l n b φ := by
  obtain ⟨f, hI, hc, hδ, hD⟩ := h
  have hle : CongruenceSubgroup.Gamma1 (N * M * l ^ n) ≤ CongruenceSubgroup.Gamma1 (N * l ^ n) :=
    gamma1_le_of_dvd ⟨M, by ring⟩
  refine ⟨f, fun γ hγ => hI γ (hle hγ), hc, fun δ hδ' hneg => ?_, hD⟩
  obtain ⟨g, hg, e⟩ := hδ δ (gamma1_le_of_dvd (dvd_mul_right N M) hδ') hneg
  exact ⟨g, fun γ hγ => hg γ (hle hγ), e⟩

theorem B_level_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N M l w : ℕ) [Fact l.Prime] :
    X.B N l w ≤ X.B (N * M) l w := by
  apply Submodule.span_mono
  rintro b ⟨hp, hg⟩
  refine ⟨hp, fun γ hγ => hg γ ?_⟩
  rw [Gam, Subgroup.mem_inf] at hγ ⊢
  exact ⟨gamma1_le_of_dvd (dvd_mul_right N M) hγ.1, hγ.2⟩

theorem auxiliaryLevel_coprime_ge_five (l N : ℕ) [hl : Fact l.Prime] (hN : 1 ≤ N) (hlN : ¬ l ∣ N) :
    5 ≤ N * (if l = 5 then 7 else 5) ∧ ¬ l ∣ N * (if l = 5 then 7 else 5) := by
  refine ⟨?_, ?_⟩
  · split_ifs <;> nlinarith
  · intro h
    rcases (Nat.Prime.dvd_mul hl.out).1 h with h' | h'
    · exact hlN h'
    · split_ifs at h' with h5
      · subst h5; norm_num at h'
      · have := (Nat.prime_dvd_prime_iff_eq hl.out (by norm_num)).1 h'
        exact h5 this

theorem discrete (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (hA : A.valuation (l : Ω) < 1) (hl2 : l ≠ 2)
    (N : ℕ) (hN : 1 ≤ N) (hlN : ¬ l ∣ N) (w : ℕ) (hw : Odd w) (F : Finset Ω) :
    ∃ c : ℕ, ∀ v : X.Fn l, v ∈ X.B N l w →
      (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → X.galB l s v = ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)) • v) →
      ∀ (n : ℕ) (φ : HahnSeries ℚ Ω), IsThB X A N l n v φ → ∀ r, CgA A l n ((l : Ω) ^ c * φ.coeff r) 0 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨c, hc⟩ := GlobalTheory.T.integral_tate_inertia_cyclotomic_twist_torsion l Ω A hA (w + 1) (by omega) F
  refine ⟨c, fun v hv hgal n φ hφ r => ?_⟩
  have hφA : ∀ r, φ.coeff r ∈ A := by
    obtain ⟨f, -, -, -, hDl⟩ := hφ
    exact hDl.1
  refine hc n (φ.coeff r) (hφA r) (fun s hs hF => ?_)
  have hsA : ∀ x, x ∈ A ↔ s x ∈ A := fun x => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs) x).symm
  set u : ℤ_[l] := (cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1) with hu
  have h1 := GlobalTheory.isThB_galB Ω ε X A N l n w s ((ValuationSubring.mem_nonunits_iff A).2 hA) hsA v hv φ hφ
  rw [hgal s hs hF] at h1
  have h2 := GlobalTheory.ThAdd.isThB_add Ω ε X A N l n w v v ((ValuationSubring.mem_nonunits_iff A).2 hA) hv hv u 0 φ φ hφ hφ
  rw [zero_smul, add_zero] at h2
  have huv : u • v ∈ X.B N l w := Submodule.smul_mem _ u hv
  obtain ⟨hN5, hlN5⟩ := auxiliaryLevel_coprime_ge_five l N hN hlN
  have h3 := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A _ l hj hl2 hlN5 hN5 ((ValuationSubring.mem_nonunits_iff A).2 hA) n w hw (u • v)
    (B_level_mul X N _ l w huv) _ _ (isThB_level_mul X A N _ l n _ _ h1) (isThB_level_mul X A N _ l n _ _ h2) r

  have h0 : ((0 : ℤ_[l]).appr n : ℕ) = 0 := by
    have hlt := PadicInt.appr_lt (0 : ℤ_[l]) n
    have hk : ((PadicInt.toZModPow n (0 : ℤ_[l]) : ZMod (l ^ n))) = 0 := map_zero _
    have hk' : (((0 : ℤ_[l]).appr n : ℕ) : ZMod (l ^ n)) = 0 := hk
    rw [ZMod.natCast_eq_zero_iff] at hk'
    exact Nat.eq_zero_of_dvd_of_lt hk' hlt
  rw [h0] at h3
  have e : ((((u.appr n : ℕ)) : Ω) • φ + ((0 : ℕ) : Ω) • φ).coeff r = ((u.appr n : ℕ) : Ω) * φ.coeff r := by simp
  have e' : (HahnSeries.map φ (s : Ω →+* Ω)).coeff r = s (φ.coeff r) := rfl
  rw [e, e'] at h3
  have hcg : CgA A l n ((u.appr n : ℕ) : Ω) ((((cycMod ℚ Ω l n s : ZMod (l ^ n)).val ^ (w + 1) : ℕ) : Ω)) :=
    cgA_natCast A l n _ _ (by
      have e1 : (((u.appr n : ℕ)) : ZMod (l ^ n)) = PadicInt.toZModPow n u := rfl
      rw [e1, hu, map_pow]
      push_cast
      congr 1
      simp [cycMod])
  rw [Nat.cast_pow] at hcg
  exact cgA_trans h3 (cgA_mul hcg (hφA r))

theorem th_kills_Fplus_discrete : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω),
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → A.valuation (l : Ω) < 1 → ∀ (N w : ℕ) (F : Finset Ω), l ≠ 2 → ¬ l ∣ N → 1 ≤ N → Odd w → ∃ c : ℕ, ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → X.galB l s b = ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)) • b) →
  ∀ (n : ℕ) (φ : HahnSeries ℚ Ω), IsThB X A N l n b φ → ∀ r, CgA A l n ((l : Ω) ^ c * φ.coeff r) 0 := by
  intro l _ Ω _ _ _ ε X A hj hA N w F hl2 hlN hN hw
  exact discrete l Ω ε X A hj hA hl2 N hN hlN w hw F

end GlobalTheory.ThKill
end

section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped ComplexConjugate ContDiff InnerProductSpace

noncomputable section

namespace GlobalTheory.Orb

variable {H : Type} [Group H] [TopologicalSpace H]
  {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] {D : H →* (V →L[ℂ] V)} {π : H →* (U →L[ℂ] U)}

theorem continuous_trace_rep (hD : IsUnitaryRep D) :
    Continuous fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) := by
  simp only [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V)]
  exact continuous_finsetSum _ fun i _ => continuous_const.inner (hD.continuous_apply _)


omit [TopologicalSpace H] in
theorem trace_rep_conj (x s : H) :
    LinearMap.trace ℂ V (D (x⁻¹ * s * x) : V →ₗ[ℂ] V) = LinearMap.trace ℂ V (D s : V →ₗ[ℂ] V) := by
  have h := Representation.char_conj (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp D) s x⁻¹
  rwa [inv_inv] at h

variable [MeasurableSpace H] [BorelSpace H] {μ : Measure H}

theorem hasTrace_repOp_of_finiteDimensional [CompleteSpace V] [IsFiniteMeasureOnCompacts μ] (hD : IsUnitaryRep D)
    {f : H → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    HasTrace (repOp D μ f) (∫ g, f g * LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) ∂μ) := by
  refine ⟨isTraceClass_of_finiteDimensional _, ?_⟩
  simp only [trace_eq_linearMap_trace, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V), Finset.mul_sum,
    ContinuousLinearMap.coe_coe, hD.inner_repOp hf hc]
  exact (integral_finsetSum _ fun i _ => (hf.mul (continuous_const.inner
    (hD.continuous_apply _))).integrable_of_hasCompactSupport hc.mul_right).symm

variable [IsTopologicalGroup H] [CompactSpace H] [μ.IsHaarMeasure]

theorem integral_conj_trace_mul_trace (hD : IsUnitaryRep D) (hi : IsTopIrreducible D) :
    ∫ g, conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) * LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) ∂μ = μ.real univ := by
  let ρ : Representation ℂ H V := ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp D
  have := hi.1
  have : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule h)⟩
  have : ρ.IsIrreducible := ⟨fun S => (hi.2 S.toSubmodule ⟨S.toSubmodule.closed_of_finiteDimensional,
    fun g v hv => S.apply_mem_toSubmodule g hv⟩).imp (fun h => Subrepresentation.toSubmodule_injective h)
      fun h => Subrepresentation.toSubmodule_injective h⟩
  have h := integral_conj_character_mul_character_self (haarProb H) ρ hD.continuous_apply hD.norm_apply
  conv_lhs => rw [eq_smul_haarProb μ]
  rw [integral_smul_measure]
  exact (congrArg _ h).trans (by simp [Measure.real])

theorem integral_inner_smul_eq_zero [CompleteSpace V] [CompleteSpace U] (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hπ : IsUnitaryRep π) (hi' : IsTopIrreducible π) (hne : ¬ IsUnitEquiv π D) (e x : V) (v : U) :
    ∫ g, ⟪D g e, x⟫_ℂ • π g v ∂μ = 0 := by
  have hI : ∀ z : V, Integrable (fun g => ⟪D g e, z⟫_ℂ • π g v) μ := fun z =>
    integrable_of_continuous_of_compactSpace μ
      (((hD.continuous_apply e).inner continuous_const).smul (hπ.continuous_apply v))
  let T : V →ₗ[ℂ] U :=
    { toFun := fun x => ∫ g, ⟪D g e, x⟫_ℂ • π g v ∂μ
      map_add' := fun x y => by
        rw [← integral_add (hI x) (hI y)]
        simp [add_smul]
      map_smul' := fun c x => by simp [mul_smul, integral_smul] }
  have hT : LinearMap.toContinuousLinearMap T ∈ AutMult.homIn D π ⊤ := AutMult.mem_homIn_top.2 fun g x => by
    change ∫ k, ⟪D k e, D g x⟫_ℂ • π k v ∂μ = π g (∫ k, ⟪D k e, x⟫_ℂ • π k v ∂μ)
    rw [← integral_mul_left_eq_self _ g, ← (π g).integral_comp_comm (hI x)]
    simp only [map_mul, ContinuousLinearMap.mul_apply, AutMult.inner_map_map hD, map_smul]
  have h0 : AutMult.homIn D π ⊤ = ⊥ := AutMult.multIn_eq_zero_iff.1 (by_contra fun h =>
    hne (AutMult.uEquiv_of_multIn_ne_zero ⟨‹_›, hD, hi⟩ ⟨‹_›, hπ, hi'⟩ h).symm)
  rw [h0, Submodule.mem_bot] at hT
  exact DFunLike.congr_fun hT x

theorem repOp_conj_trace_eq_zero [CompleteSpace V] [CompleteSpace U] (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hπ : IsUnitaryRep π) (hi' : IsTopIrreducible π) (hne : ¬ IsUnitEquiv π D) (c : ℂ) :
    repOp π μ (fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / c) = 0 := by
  ext v
  rw [hπ.repOp_apply (f := fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / c)
    ((Complex.continuous_conj.comp (continuous_trace_rep hD)).div_const c)
    (HasCompactSupport.of_compactSpace _)]

  simp only [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V), map_sum, inner_conj_symm, div_eq_inv_mul,
  mul_smul, integral_smul, Finset.sum_smul, ContinuousLinearMap.coe_coe]
  have hI : ∀ e : V, Integrable (fun g => ⟪D g e, e⟫_ℂ • π g v) μ := fun e =>
    integrable_of_continuous_of_compactSpace μ
      (((hD.continuous_apply e).inner continuous_const).smul (hπ.continuous_apply v))
  rw [integral_finsetSum _ fun i _ => hI _]
  simp [integral_inner_smul_eq_zero hD hi hπ hi' hne]

theorem isCharFn_and_isPseudoCoeff_of_compact [T2Space H] [SecondCountableTopology H] [CompleteSpace V]
    {n : Type} [Fintype n] [DecidableEq n] {ι : H →* Matrix n n ℂ} (hι : Continuous (matCoord ι))
    (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hχ : (fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V))) ∈ CcMat ι) :
    IsCharFn ι μ D (fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) ∧
      IsPseudoCoeff ι μ D fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ := by
  have h0 : (μ.real univ : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(isOpen_univ.measure_pos μ univ_nonempty).ne', measure_ne_top _ _⟩
  have hc := continuous_trace_rep hD
  have hf : Continuous fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ :=
    (Complex.continuous_conj.comp hc).div_const _
  have hΘ : IsCharFn ι μ D (fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) :=
    ⟨hc.locallyIntegrable, fun s _ => hc.continuousAt, fun f hf' =>
      hasTrace_repOp_of_finiteDimensional hD (continuous_of_mem_ccSmooth hι hf') hf'.1⟩
  refine ⟨hΘ, ?_, ?_, fun U _ _ _ π hπ hirr _ hne => ?_, fun s _ hT => absurd (isClosed_cent s).isCompact hT,
    _, hΘ, fun s _ hT dt _ _ => ?_⟩
  · simp only [div_eq_inv_mul]
    exact (CcMat ι).smul_mem (μ.real univ : ℂ)⁻¹ hχ
  · convert hasTrace_repOp_of_finiteDimensional (μ := μ) hD hf (HasCompactSupport.of_compactSpace _) using 1
    simp only [div_mul_eq_mul_div, integral_div, integral_conj_trace_mul_trace hD hi, div_self h0]
  · rw [repOp_conj_trace_eq_zero hD hi hπ hirr hne]
    exact ⟨isTraceClass_zero, trace_zero⟩
  · haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
    convert hasOrbInt_of_finite (dh := μ) (dt := dt)
      (f := fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ)
      ((hf.comp (f := fun x => x⁻¹ * s * x) (by fun_prop)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) using 2
    simp only [trace_rep_conj, integral_const, Complex.real_smul]
    field_simp

end GlobalTheory.Orb
end
end

section

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace HeightProper


omit [NumberField F] [NumberField E] in
theorem repr_map {R R' ι : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (b : Module.Basis ι F E)
    (φ : R →ₐ[F] R') (z : R ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) i =
      φ ((Algebra.TensorProduct.basis R b).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem nnnorm_repr_le_absFin {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (hb : ∀ i, IsIntegral ℤ (b i)) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (i : ι) :
    ‖(Algebra.TensorProduct.basis (Fv F v) b.traceDual).repr y i‖₊ ≤ absFin F v y := by
  rw [← absBar_algebraMap, algebraMap_basis_repr]
  refine (valBar F v).map_sum_le fun τ _ => ?_
  change absBar F v _ ≤ _
  rw [absBar_mul]
  refine (mul_le_of_le_one_right' ?_).trans (le_absFin F v τ y)
  have := (le_absFin F v τ _).trans (absFin_tmul_le F v 1 (⟨b i, hb i⟩ : 𝓞 E))
  rw [finEmb_tmul, map_one, one_mul, nnnorm_one] at this
  exact this

theorem exists_norm_repr_le {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (w : InfinitePlace F) (c : ℝ) (i : ι) : ∃ B : ℝ, ∀ y : w.Completion ⊗[F] E,
      (∀ τ : EmbOver E w, ‖infEmb τ y‖ ≤ c) →
      ‖(Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i‖ ≤ B := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let t : (E →ₐ[F] ℂ) → EmbOver E w := fun τ => ⟨τ, RingHom.ext τ.commutes⟩
  have key : ∀ y : w.Completion ⊗[F] E, InfinitePlace.Completion.extensionEmbedding w
      ((Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] ℂ, infEmb (t τ) y * τ (b i) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
    | tmul a e =>
      have h : ∀ x : F, InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) =
          algebraMap F ℂ x := fun x => by
        rw [AbsoluteValue.Completion.algebraMap_def, InfinitePlace.Completion.extensionEmbedding_coe]
        rfl
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
        h, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
        trace_eq_sum_embeddings, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [infEmb_tmul, map_mul, mul_assoc]; rfl
  refine ⟨∑ τ : E →ₐ[F] ℂ, c * ‖τ (b i)‖, fun y hy => ?_⟩
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), key]
  refine norm_sum_le_of_le _ fun τ _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hy _) (norm_nonneg _)

theorem norm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ opNorm A := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j 1)
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i
  have h3 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ k, A i k * (EuclideanSpace.single j (1 : ℂ)) k = _
    simp [Pi.single_apply]
  rw [h3] at h2
  simpa [opNorm] using h2.trans h

theorem exists_compact_adeles (B : InfinitePlace F → ℝ) (c : ℝ≥0) : ∃ C : Set (AF F), IsCompact C ∧
    ∀ a : AF F, (∀ w, ‖evInf F w a‖ ≤ B w) → ∀ d : ℕ, 0 < d → (d : ℝ≥0) ≤ c →
      (∀ v, ‖(d : Fv F v) * evFin F v a‖ ≤ 1) → a ∈ C := by
  have h1 : IsCompact (X := Ainf F) (Set.pi Set.univ fun w : InfinitePlace F => {x : w.Completion | ‖x‖ ≤ B w}) :=
    isCompact_univ_pi fun w => by
      have := (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
        (isCompact_closedBall 0 (B w))
      convert this using 1
      ext x
      rw [Set.mem_preimage, mem_closedBall_zero_iff,
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), Set.mem_setOf_eq]
  have h2 : IsCompact (⋃ d ∈ Finset.range (⌊c⌋₊ + 1), (fun x : Af F => algebraMap F (Af F) (d : F)⁻¹ * x) ''
      {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}) :=
    (Finset.range _).isCompact_biUnion fun d _ =>
      (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id)
  refine ⟨_, h1.prod h2, fun a ha d hd hdc hv => ⟨fun w _ => ha w, ?_⟩⟩
  refine Set.mem_biUnion (x := d) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hdc))))
    ⟨(d : Af F) * a.2, fun v => ?_, ?_⟩
  · have := hv v
    rw [← map_natCast (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)] at this
    exact Valued.toNormedField.norm_le_one_iff.1 this
  · have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    beta_reduce
    rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul]

theorem exists_compact_entries (n : Type) [Fintype n] [DecidableEq n] (c : ℝ≥0) :
    ∃ C : Set (AF F ⊗[F] E), IsCompact C ∧
      ∀ g : GL n (AF F ⊗[F] E), heightGL F g ≤ c → ∀ i j, g.1 i j ∈ C := by
  classical
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  choose B hB using fun (k : s) (w : InfinitePlace F) => exists_norm_repr_le b w c k
  choose C hC hC' using fun k : s => exists_compact_adeles (B k) c
  let e := (Algebra.TensorProduct.basis (AF F) b.traceDual).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  refine ⟨e.symm '' Set.pi Set.univ C, (isCompact_univ_pi hC).image he, fun g hg i j =>
    ⟨e (g.1 i j), fun k _ => ?_, e.symm_apply_apply _⟩⟩
  obtain ⟨d, hd, hdc, hv⟩ := GlobalTheory.SmoothForms.denom_global (fun v => htFin F v (bc (compFin F E v) g))
    (fun v => one_le_htOf _ _) (finite_mulSupport_htFin F g)
  refine hC' k _ (fun w => ?_) d hd ?_ fun v => hv v _ ?_
  · refine (congrArg norm (repr_map b.traceDual (evInf F w) (g.1 i j) k)).symm.trans_le (hB k w _ fun τ => ?_)
    have h := (((normInf_le_iff F w).1 (le_htOf _ _) τ).trans (GlobalTheory.Grow.htInf_le_heightGL F g w)).trans hg
    exact (norm_entry_le_opNorm _ i j).trans (NNReal.coe_le_coe.2 h)
  · exact (hdc.trans (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _))).trans hg
  · refine (congrArg nnnorm (repr_map b.traceDual (evFin F v) (g.1 i j) k)).symm.trans_le
      ((nnnorm_repr_le_absFin b hb' v _ k).trans ?_)
    exact (absFin_le_normFin F v (bc (compFin F E v) g).1 i j).trans (le_htOf _ _)

end HeightProper

section GeneralLinearIntegers

variable (F) {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_heightGL_le (c : ℝ≥0) : IsCompact {g : GL n (AF F ⊗[F] E) | heightGL F g ≤ c} := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  obtain ⟨C, hC, hC'⟩ := HeightProper.exists_compact_entries (F := F) (E := E) n c
  let S : Set (Matrix n n (AF F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hK := (Units.isClosedEmbedding_embedProduct (α := Matrix n n (AF F ⊗[F] E))).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (isClosed_le (GlobalTheory.Grow.continuous_heightGL F) continuous_const) fun g hg => ?_
  exact ⟨fun i _ j _ => hC' g hg i j, (g⁻¹).1, fun i _ j _ => hC' g⁻¹ (by rwa [heightGL_inv]) i j, rfl⟩

end GeneralLinearIntegers

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosedEmbedding_matHom_GAd : Topology.IsClosedEmbedding (matHom (AF F) σ J) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have hcl : IsClosed (HR (AF F) σ J : Set (GL (Fin n) (AF F ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  exact hcl.isClosedEmbedding_subtypeVal

theorem continuous_height_GAd : Continuous (height σ J) :=
  (GlobalTheory.Grow.continuous_heightGL F).comp (isEmbedding_matHom _ σ J).continuous

theorem isCompact_height_le (c : ℝ≥0) : IsCompact {g : GAd σ J | height σ J g ≤ c} :=
  (isClosedEmbedding_matHom_GAd σ J).isCompact_preimage (isCompact_heightGL_le F c)

theorem height_bddAbove_of_isCompact {K : Set (GAd σ J)} (hK : IsCompact K) :
    ∃ c : ℝ≥0, ∀ g ∈ K, height σ J g ≤ c := by
  obtain ⟨c, hc⟩ := hK.bddAbove_image (continuous_height_GAd σ J).continuousOn
  exact ⟨c, fun g hg => hc ⟨g, hg, rfl⟩⟩

end GlobalTheory.AdelicU

end
end
