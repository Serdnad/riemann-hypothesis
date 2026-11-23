module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle137
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle113
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle030
public import ReciprocityTheory.Hypotheses.GalCohDefs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import ReciprocityTheory.GaloisValuations.Bundle002
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
import Formalism.GaloisCohomology.StatementLoc

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Count

theorem decOrbit_root_count : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β β' : Ω) (S : Finset Ω), (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) → ∀ g : Polynomial E, g.Monic → g.natDegree = S.card → aeval β' g = 0 → (∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β) → (∀ σ : G E Ω, ∃ d ∈ Dec (F := E) A, σ β' = d β') ∧ (∀ σ ∈ Dec (F := E) A, σ β = β → σ β' = β') := by
  intro E Ω _ _ _ _ _ A β β' S hS g hg hdeg hroot hstab
  classical

  let φ : Ω → Ω := fun x => if h : ∃ d ∈ Dec (F := E) A, d β = x then (Classical.choose h) β' else 0
  have hφ : ∀ x ∈ S, ∃ d ∈ Dec (F := E) A, d β = x ∧ φ x = d β' := by
    intro x hx
    have h := (hS x).1 hx
    refine ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2, ?_⟩
    simp only [φ, dif_pos h]

  have hg0 : g ≠ 0 := hg.ne_zero
  have hconj : ∀ σ : G E Ω, σ β' ∈ (g.aroots Ω).toFinset := by
    intro σ
    rw [Multiset.mem_toFinset, mem_aroots]
    refine ⟨hg0, ?_⟩
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, hroot, map_zero]

  have hinj : Set.InjOn φ S := by
    intro x hx y hy hxy
    obtain ⟨d, hd, rfl, hdx⟩ := hφ x hx
    obtain ⟨e, he, rfl, hey⟩ := hφ y hy
    have h1 : (e⁻¹ * d) β' = β' := by
      rw [AlgEquiv.mul_apply, ← hdx, hxy, hey]
      exact (AlgEquiv.symm_apply_apply e β')
    have h2 := hstab _ ((Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem he) hd) h1
    rw [AlgEquiv.mul_apply] at h2
    have := congrArg e h2
    simpa using this
  have hsub : S.image φ ⊆ (g.aroots Ω).toFinset := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨d, -, -, hdx⟩ := hφ x hx
    rw [hdx]; exact hconj d
  have hcard : (g.aroots Ω).toFinset.card ≤ (S.image φ).card := by
    rw [Finset.card_image_of_injOn hinj, ← hdeg]
    calc (g.aroots Ω).toFinset.card ≤ (g.aroots Ω).card := Multiset.toFinset_card_le _
      _ ≤ (g.map (algebraMap E Ω)).natDegree := Polynomial.card_roots' _
      _ = g.natDegree := Polynomial.natDegree_map _
  have heq : S.image φ = (g.aroots Ω).toFinset := Finset.eq_of_subset_of_card_le hsub hcard

  have hin : ∀ σ : G E Ω, ∃ x ∈ S, φ x = σ β' := by
    intro σ
    have := hconj σ
    rw [← heq] at this
    exact Finset.mem_image.1 this

  have hkey : ∀ τ ∈ Dec (F := E) A, τ β' = φ (τ β) := by
    intro τ hτ
    obtain ⟨x, hx, hxe⟩ := hin τ
    obtain ⟨d, hd, rfl, hdx⟩ := hφ x hx
    have h1 : (d⁻¹ * τ) β' = β' := by
      rw [AlgEquiv.mul_apply, ← hxe, hdx]
      exact (AlgEquiv.symm_apply_apply d β')
    have h2 := hstab _ ((Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hd) hτ) h1
    rw [AlgEquiv.mul_apply] at h2
    have h3 : τ β = d β := by
      have := congrArg d h2
      simpa using this
    rw [h3, ← hxe]
  refine ⟨fun σ => ?_, fun σ hσ hσβ => ?_⟩
  · obtain ⟨x, hx, hxe⟩ := hin σ
    obtain ⟨d, hd, -, hdx⟩ := hφ x hx
    exact ⟨d, hd, by rw [← hxe, hdx]⟩
  · have h1 := hkey σ hσ
    have h0 := hkey 1 (Dec (F := E) A).one_mem
    rw [h1, hσβ]
    exact h0.symm

end GlobalTheory.Count
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise

namespace GlobalTheory

theorem exists_base_near_of_dec_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (z : Ω), (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r := by
  intro E Ω _ _ _ _ _ A w h z hz r hr
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hint : ∀ x : Ω, IsIntegral ℤ x → A.valuation x ≤ 1 := fun x hx =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hx)
  have halg : ∀ x : Ω, IsAlgebraic ℤ x := fun x => by
    have : IsIntegral ℚ x := isIntegral_trans (R := ℚ) (A := E) x (Algebra.IsIntegral.isIntegral x)
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr this.isAlgebraic

  obtain ⟨b, hb0, hbz⟩ := (halg z).exists_integral_multiple

  obtain ⟨b', hb'0, hb'r⟩ := (halg r⁻¹).exists_integral_multiple

  set m : ℕ := Ideal.absNorm w.asIdeal with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hmA : A.valuation (m : Ω) < 1 := by
    have h1 := (h ((m : ℕ) : 𝓞 E)).mpr (Ideal.absNorm_mem w.asIdeal)
    simpa using h1
  have hbv : A.valuation (b : Ω) ≠ 0 := by simpa using hb0
  have hrv : A.valuation r ≠ 0 := by simpa using hr
  have hb'v : A.valuation (b' : Ω) ≤ A.valuation r := by
    have h1 := hint _ hb'r
    rw [zsmul_eq_mul, Valuation.map_mul, map_inv₀] at h1
    have := mul_le_mul_left h1 (A.valuation r)
    rwa [mul_assoc, inv_mul_cancel₀ hrv, mul_one, one_mul] at this
  set c : ℕ := b'.natAbs * b.natAbs * m with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero (mul_ne_zero (Int.natAbs_ne_zero.mpr hb'0) (Int.natAbs_ne_zero.mpr hb0)) hm0
  have hnat : ∀ n : ℤ, A.valuation ((n.natAbs : ℕ) : Ω) = A.valuation (n : Ω) := by
    intro n
    rcases Int.natAbs_eq n with e | e
    · conv_rhs => rw [e]
      simp
    · conv_rhs => rw [e]
      simp

  have hcv : A.valuation (c : Ω) < A.valuation r * A.valuation (b : Ω) := by
    rw [hc, Nat.cast_mul, Nat.cast_mul, Valuation.map_mul, Valuation.map_mul, hnat, hnat]
    have h1 : A.valuation (b' : Ω) * A.valuation (b : Ω) ≤ A.valuation r * A.valuation (b : Ω) :=
      mul_le_mul_left hb'v _
    have hpos : 0 < A.valuation (b' : Ω) * A.valuation (b : Ω) := by
      rw [zero_lt_iff, ← Valuation.map_mul]; simpa using ⟨hb'0, hb0⟩
    calc A.valuation (b' : Ω) * A.valuation (b : Ω) * A.valuation (m : Ω)
        < A.valuation (b' : Ω) * A.valuation (b : Ω) * 1 := mul_lt_mul_of_pos_left hmA hpos
      _ ≤ A.valuation r * A.valuation (b : Ω) := by rw [mul_one]; exact h1
  have hbz' : IsIntegral ℤ ((b : Ω) * z) := by rwa [zsmul_eq_mul] at hbz
  have key : ∀ x u : Ω, A.valuation x ≤ A.valuation (c : Ω) → IsIntegral ℤ ((b : Ω) * u) →
      A.valuation (x * u) < A.valuation r := by
    intro x u hx hu
    refine lt_of_mul_lt_mul_right' (a := A.valuation (b : Ω)) ?_
    calc A.valuation (x * u) * A.valuation (b : Ω) = A.valuation x * A.valuation ((b : Ω) * u) := by
          rw [Valuation.map_mul, Valuation.map_mul, mul_assoc, mul_comm (A.valuation u)]
      _ ≤ A.valuation (c : Ω) * 1 := mul_le_mul' hx (hint _ hu)
      _ < A.valuation r * A.valuation (b : Ω) := by rw [mul_one]; exact hcv
  set K := IntermediateField.adjoin E ({z} : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  have hzK : z ∈ K := IntermediateField.mem_adjoin_simple_self E z
  have hfix : ∀ σ : G E Ω, σ z = z → ∀ x ∈ K, σ x = x := by
    intro σ hσ x hx
    have e1 : ((σ : Ω →ₐ[E] Ω).comp K.val) = K.val :=
      IntermediateField.adjoin_algHom_ext E (fun y hy => by
        rw [Set.mem_singleton_iff] at hy; subst hy; simpa using hσ)
    simpa using congrArg (fun φ : K →ₐ[E] Ω => φ ⟨x, hx⟩) e1
  have hsame : ∀ σ : G E Ω, (∀ x ∈ K, IsIntegral ℤ x → (A.valuation (σ x) < 1 ↔ A.valuation x < 1)) →
      σ z = z := by
    intro σ hall
    obtain ⟨ρ, hρK, hρ⟩ := GlobalTheory.T.exists_conj_valuationSubring_of_same_below E Ω K A (σ⁻¹ • A) (fun x hx hxi => by
      rw [smul_valuation_lt_one_iff, inv_inv]; exact (hall x hx hxi).symm)
    have hD : σ * ρ ∈ Dec (F := E) A := by
      rw [mem_Dec, mul_smul, hρ, smul_inv_smul]
    have := hz _ hD
    rw [AlgEquiv.mul_apply, hρK z hzK] at this
    exact this
  obtain ⟨t, htK, htint, ht1, htσ⟩ := GlobalTheory.T.exists_integral_near_one_small_off_decomposition E Ω K A c hc0
  obtain ⟨e, s, hs, he⟩ := GlobalTheory.T.exists_algebraMap_sub_eq_sum_conjugates' E Ω (t * z)
  refine ⟨e, ?_⟩
  have hyz : A.valuation (t * z - z) < A.valuation r := by
    have : t * z - z = (t - 1) * z := by ring
    rw [this]; exact key _ _ ht1 hbz'
  have hsum : ∀ x ∈ s, A.valuation x < A.valuation r := by
    intro x hx
    obtain ⟨hxy, σ, rfl⟩ := hs x hx
    have hσz : σ z ≠ z := by
      intro hσz
      apply hxy
      rw [map_mul, hfix σ hσz t htK, hσz]
    have hex : ∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1) := by
      by_contra hne
      exact hσz (hsame σ (fun x hx hxi => by
        by_contra hn
        exact hne ⟨x, hx, hxi, hn⟩))
    rw [map_mul]
    refine key _ _ (htσ σ hex) ?_
    have : (b : Ω) * σ z = σ ((b : Ω) * z) := by simp
    rw [this]
    exact hbz'.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)
  have e2 : algebraMap E Ω e - z = (∑ x ∈ s, x) + (t * z - z) := by rw [← he]; ring
  rw [e2]
  exact Valuation.map_add_lt _ (Valuation.map_sum_lt _ hrv hsum) hyz

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField
open Pointwise

namespace GlobalTheory.HilbertKill

theorem hilbertSubgroup_le_ker : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (M : Type) [AddCommGroup M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    IsLocallyConstant z → (∀ v, ∀ σ ∈ Ine (F := E) (Av v), z σ = 0) →
    (∀ c : Ω ≃ₐ[E] Ω, IsComplexConjugation c → z c = 0) →
    ∀ σ ∈ hilbertSubgroup E Ω, z σ = 0 := by
  intro E Ω _ _ _ _ _ Av hAv M _ z hz hlc hIne hC
  let f : G E Ω →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by
        have h := hz 1 1
        rw [mul_one, left_eq_add] at h
        simp [h]
      map_mul' := fun g h => by simp [hz] }
  have hf : ∀ g, g ∈ f.ker ↔ z g = 0 := fun g => by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z g) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  have hclosed : IsClosed (f.ker : Set (G E Ω)) := by
    convert hlc.isClosed_fiber 0 using 1
    ext g
    exact hf g
  have hinv : ∀ g, z g⁻¹ = - z g := fun g => by
    have h := hz g g⁻¹
    have h1 : z 1 = 0 := (hf 1).1 f.ker.one_mem
    rw [mul_inv_cancel, h1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  intro σ hσ
  refine (hf σ).1 (Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).2 ?_) hclosed hσ)
  rintro g ((hg | ⟨A, hg⟩) | hg)
  · exact Abelianization.commutator_subset_ker f hg
  · have hg' := (ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff E A g).1 hg
    rcases GlobalTheory.inertiaEl_eq_one_or_liesAbove E Ω A g hg' with rfl | ⟨v, hv⟩
    · exact f.ker.one_mem
    have hA : IsPlaceOver A v := fun x => by rw [← hv x, A.mem_nonunits_iff]
    have hgI : g ∈ Ine (F := E) A :=
      ⟨hg'.1, fun x hx => A.mem_nonunits_iff.1 (hg'.2 x ((A.valuation_le_one_iff x).1 hx))⟩
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (hAv v) hA
    have h2 : τ⁻¹ * g * τ⁻¹⁻¹ ∈ Ine (F := E) (τ⁻¹ • A) := conj_mem_Ine_smul hgI
    rw [inv_inv, ← hτ, inv_smul_smul] at h2
    have h3 := hIne v _ h2
    show z g = 0
    have e : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
    rw [e, hz, hz, h3, hinv, add_zero, add_neg_cancel]
  · exact (hf g).2 (hC g hg)

end GlobalTheory.HilbertKill
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

noncomputable section

namespace GlobalTheory.CohTransport

section Res

variable {R : Type*} [CommRing R]
  {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N) (φ : Γ' →* Γ)
  (hσ : ∀ g n, σ' g n = σ (φ g) n)

def rh0 : H0 σ →ₗ[R] H0 σ' :=
  Submodule.inclusion fun m hm g => by
    show σ' g m = m
    rw [hσ]; exact hm (φ g)

variable (hφ : Continuous φ)

def rz1 : Z1 σ →ₗ[R] Z1 σ' where
  toFun f := ⟨f.1 ∘ φ, f.2.1.comp hφ, fun g h => by
    simp only [Function.comp_apply, map_mul, hσ]; exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rh1 : H1 σ →ₗ[R] H1 σ' :=
  Submodule.mapQ _ _ (rz1 σ σ' φ hσ hφ) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 σ _).1 hf
    refine (mem_coboundaries1 _ _).2 ⟨m, fun h => ?_⟩
    show f.1 (φ h) = σ' h m - m
    rw [hσ]; exact hm (φ h)

def rz2 : Z2 σ →ₗ[R] Z2 σ' where
  toFun f := ⟨fun p => f.1 (φ p.1, φ p.2), f.2.1.comp (hφ.prodMap hφ), fun g h k => by
    simp only [map_mul, hσ]; exact f.2.2 _ _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rh2 : H2 σ →ₗ[R] H2 σ' :=
  Submodule.mapQ _ _ (rz2 σ σ' φ hσ hφ) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem σ _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ φ, hc.comp hφ, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    have e := congrFun hcf (φ g, φ h)
    simp only [Submodule.coe_subtype] at e
    change _ = f.1 (φ g, φ h)
    rw [← e]
    simp [d1_apply, hσ, map_mul]

end Res

section Equiv

variable {R : Type*} [CommRing R]
  {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N) (e : Γ' ≃* Γ)
  (he : Continuous e) (he' : Continuous e.symm)

theorem symm_rel (hσ : ∀ g n, σ' g n = σ (e g) n) : ∀ g n, σ g n = σ' (e.symm g) n := fun g n => by
  rw [hσ, MulEquiv.apply_symm_apply]

def eq0 (hσ : ∀ g n, σ' g n = σ (e g) n) : H0 σ ≃ₗ[R] H0 σ' :=
  LinearEquiv.ofLinear (rh0 σ σ' e.toMonoidHom hσ)
    (rh0 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ)) (by ext; rfl) (by ext; rfl)

def eq1 (hσ : ∀ g n, σ' g n = σ (e g) n) : H1 σ ≃ₗ[R] H1 σ' :=
  LinearEquiv.ofLinear (rh1 σ σ' e.toMonoidHom hσ he)
    (rh1 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ) he')
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => by
        show f.1 (e.symm (e g)) = f.1 g
        rw [MulEquiv.symm_apply_apply])))
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => by
        show f.1 (e (e.symm g)) = f.1 g
        rw [MulEquiv.apply_symm_apply])))

def eq2 (hσ : ∀ g n, σ' g n = σ (e g) n) : H2 σ ≃ₗ[R] H2 σ' :=
  LinearEquiv.ofLinear (rh2 σ σ' e.toMonoidHom hσ he)
    (rh2 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ) he')
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => by
        show f.1 (e.symm (e p.1), e.symm (e p.2)) = f.1 p
        rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply])))
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => by
        show f.1 (e (e.symm p.1), e (e.symm p.2)) = f.1 p
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])))

end Equiv

theorem bijective_of_conj {R : Type*} [CommRing R] {A B C A' B' C' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']
    (b : A →ₗ[R] B →ₗ[R] C) (b' : A' →ₗ[R] B' →ₗ[R] C') (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B')
    (eC : C ≃ₗ[R] C') (h : ∀ a x, b' (eA a) (eB x) = eC (b a x)) (hb : Function.Bijective b') :
    Function.Bijective b := by
  have key : (⇑b' ∘ ⇑eA) = ⇑(LinearEquiv.arrowCongr eB eC) ∘ ⇑b := by
    funext a
    refine LinearMap.ext fun x => ?_
    simp only [Function.comp_apply, LinearEquiv.arrowCongr_apply]
    rw [← h, LinearEquiv.apply_symm_apply]
  have h2 : Function.Bijective (⇑(LinearEquiv.arrowCongr eB eC) ∘ ⇑b) := key ▸ hb.comp eA.bijective
  exact (LinearEquiv.bijective _).of_comp_iff' _ |>.1 h2

theorem dualityClauses_of_mulEquiv : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (h : ContAction ρ) (h' : ContAction (ρ.comp e.toMonoidHom)), (Nonempty (H2 (charRep (χ.comp e.toMonoidHom)) ≃ₗ[R] R) ∧ Function.Bijective (cupH0H2TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)) ∧ Function.Bijective (cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _) (h'.comp' continuous_id)) ∧ Function.Bijective (cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _) (h'.comp' continuous_id)).flip ∧ Function.Bijective (cup20 (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _))) → (Nonempty (H2 (charRep χ) ≃ₗ[R] R) ∧ Function.Bijective (cupH0H2TwistedDual χ ρ (MonoidHom.id _)) ∧ Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id)) ∧ Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id)).flip ∧ Function.Bijective (cup20 χ ρ (MonoidHom.id _))) := by
  intro R _ _ _ Γ Γ' _ _ _ _ M _ _ _ _ _ e he he' χ ρ h h' H
  have hA : ∀ g m, ((ρ.comp e.toMonoidHom).comp (MonoidHom.id Γ')) g m =
      (ρ.comp (MonoidHom.id Γ)) (e g) m := fun _ _ => rfl
  have hB : ∀ g φ, ((twDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)).comp
      (MonoidHom.id Γ')) g φ = ((twDual χ ρ).comp (MonoidHom.id Γ)) (e g) φ := by
    intro g φ
    refine DFunLike.ext _ _ fun m => ?_
    simp [twDual_apply, map_inv]
  have hC : ∀ g x, ((charRep (χ.comp e.toMonoidHom)).comp (MonoidHom.id Γ')) g x =
      ((charRep χ).comp (MonoidHom.id Γ)) (e g) x := fun _ _ => rfl
  let E0A := eq0 _ _ e hA
  let E0B := eq0 _ _ e hB
  let FrameLocalData := eq1 _ _ e he he' hA
  let E1B := eq1 _ _ e he he' hB
  let E2A := eq2 _ _ e he he' hA
  let E2B := eq2 _ _ e he he' hB
  let E2C := eq2 _ _ e he he' hC
  have c02 : ∀ m y, cupH0H2TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (E0A m) (E2B y) = E2C (cupH0H2TwistedDual χ ρ (MonoidHom.id _) m y) := by
    intro m y
    induction y using Submodule.Quotient.induction_on with
    | H f => rfl
  have c11 : ∀ y x, cupH1H1TwistedDual (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (h'.comp' continuous_id) (E1B y) (FrameLocalData x) =
      E2C (cupH1H1TwistedDual χ ρ (MonoidHom.id _) (h.comp' continuous_id) y x) := by
    intro y x
    induction y using Submodule.Quotient.induction_on with
    | H f =>
      induction x using Submodule.Quotient.induction_on with
      | H f' => rfl
  have c20 : ∀ x m, cup20 (χ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (MonoidHom.id _)
      (E2A x) (E0B m) = E2C (cup20 χ ρ (MonoidHom.id _) x m) := by
    intro x m
    induction x using Submodule.Quotient.induction_on with
    | H f => rfl
  obtain ⟨⟨j⟩, b02, b11, b11', b20⟩ := H
  refine ⟨⟨(eq2 (charRep χ) (charRep (χ.comp e.toMonoidHom)) e he he' (fun _ _ => rfl)).trans j⟩,
    bijective_of_conj _ _ E0A E2B E2C c02 b02, bijective_of_conj _ _ E1B FrameLocalData E2C c11 b11,
    bijective_of_conj _ _ FrameLocalData E1B E2C (fun x y => by simp only [LinearMap.flip_apply]; exact c11 y x) b11',
    bijective_of_conj _ _ E2A E0B E2C c20 b20⟩

end GlobalTheory.CohTransport
end
end
