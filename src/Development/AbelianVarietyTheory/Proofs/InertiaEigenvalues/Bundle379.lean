module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
public import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.TameFixedLift

open Pointwise

theorem transfer {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hfix : ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) :
    ∃ g ∈ Ine (F := E) A, cycZ (F := E) (Ω := Ω) l g = cycZ (F := ℚ) (Ω := Ω) l σ := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) hfix, ⟨?_, hσ.2⟩, rfl⟩
  have h : σ • A = A := hσ.1
  exact h

theorem root_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (σ : G ℚ Ω) (u : ℤ_[l])
    (h : ((cycZ (F := ℚ) (Ω := Ω) l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u)
    (t : Ω) (ht : t ^ l ^ n = 1) : σ t = t := by
  have : CharZero Ω := algebraRat.charZero Ω
  have : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Ω) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero i (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec l (n := n) (σ : Ω ≃+* Ω) t ht
  have h2 : ((cyclotomicCharacter Ω l (σ : Ω ≃+* Ω) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u := h
  have h3 : PadicInt.toZModPow n ((l : ℤ_[l]) ^ n) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]; exact Ideal.mem_span_singleton_self _
  rw [h2, map_add (f := _), map_mul, h3, zero_mul, add_zero, map_one] at h1
  have h4 : t ^ (1 : ZMod (l ^ n)).val = t := by
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 ht, pow_one]
  rw [h4] at h1
  exact h1

theorem exists_place (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ w, w ∈ placesOver E l := by
  have hl : l.Prime := Fact.out
  have hnu : Ideal.span {(l : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    rcases Nat.pow_eq_one.mp h1 with h2 | h2
    · exact hl.one_lt.ne' h2
    · exact Module.finrank_pos.ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hmem : (l : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hl.ne_zero (by exact_mod_cast hmem)

private theorem eq_one_of_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hc : Nat.Coprime m l) {z : Ω} (hz : z ^ m = 1)
    (h1 : A.valuation (z - 1) < 1) : z = 1 := by
  by_contra hne
  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have hz1 : A.valuation z ≤ 1 := by
    have := Valuation.map_add_le A.valuation h1.le (le_of_eq (map_one A.valuation))
    simpa using this
  have hp : ∀ i : ℕ, A.valuation (z ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show z ^ (i + 1) - 1 = (z ^ i - 1) * z + (z - 1) by ring]
      refine Valuation.map_add_lt _ ?_ h1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hz1) ih
  have hs : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := mul_geom_sum z m
    rw [hz, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hm : A.valuation (m : Ω) < 1 := by
    have h2 : A.valuation (∑ i ∈ Finset.range m, (z ^ i - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun i _ => hp i
    rw [Finset.sum_sub_distrib, hs] at h2
    simpa using h2
  have hb : (1 : Ω) = (m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω) := by
    have h3 := Nat.gcd_eq_gcd_ab m l
    rw [hc.gcd_eq_one] at h3
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) h3
  have h4 : A.valuation ((m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hm
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hA
  rw [← hb, map_one] at h4
  exact lt_irrefl _ h4

private theorem tame_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hm : m ≠ 0) (hc : Nat.Coprime m l) (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (z : Ω) (hz : z ^ m = 1) : σ z = z := by
  have hv : A.valuation z = 1 := by
    have := congrArg A.valuation hz
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hm).mp this
  have hz0 : z ≠ 0 := by rintro rfl; simp at hv
  have h3 : A.valuation (σ z - z) < 1 := hσ.2 z hv.le
  have h4 : σ z / z = 1 := eq_one_of_cong A hA hc
    (by rw [div_pow, ← map_pow, hz, map_one, div_one]) (by
      rw [show σ z / z - 1 = (σ z - z) / z by field_simp, map_div₀, hv, div_one]
      exact h3)
  exact (div_eq_one_iff_eq hz0).mp h4

private theorem loc_fix {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime) (hA : A.valuation (l : Ω) < 1)
    (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hroot : ∀ t : Ω, t ^ l ^ H.condN.factorization l = 1 → σ t = t) (x : H.E) :
    σ (algebraMap H.E Ω x) = algebraMap H.E Ω x := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  refine H.image_mem_of_roots (algebraMap H.E Ω) (RingHom.eqLocusField (σ : Ω →+* Ω) (RingHom.id Ω))
    (fun y hy => ?_) x
  show σ y = y
  have hy0 : y ≠ 0 := by rintro rfl; simp [hN] at hy
  have hmul := Nat.ordProj_mul_ordCompl_eq_self H.condN l
  have hco : Nat.Coprime l (ordCompl[l] H.condN) := Nat.coprime_ordCompl hl hN
  have h1 := hroot (y ^ ordCompl[l] H.condN) (by rw [← pow_mul, mul_comm, hmul, hy])
  have h2 := tame_fix A hA (Nat.ordCompl_pos l hN).ne' hco.symm σ hσ (y ^ ordProj[l] H.condN)
    (by rw [← pow_mul, hmul, hy])
  rw [map_pow] at h1 h2
  have h3 : (σ y / y) ^ Nat.gcd (ordProj[l] H.condN) (ordCompl[l] H.condN) = 1 :=
    pow_gcd_eq_one.2 ⟨by rw [div_pow, h2, div_self (pow_ne_zero _ hy0)],
      by rw [div_pow, h1, div_self (pow_ne_zero _ hy0)]⟩
  rw [(Nat.Coprime.pow_left _ hco).gcd_eq_one, pow_one] at h3
  exact (div_eq_one_iff_eq hy0).mp h3

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) , ∃ w ∈ placesOver H.E (N.l i), ∀ u : ℤ_[N.l i], ∃ g ∈ Ine (F := H.E) (N.plOm.1 w), ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) = 1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by
  intro R H what₂ N i
  obtain ⟨w, hw⟩ := exists_place H.E (N.l i)
  refine ⟨w, hw, fun u => ?_⟩
  have : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap H.E N.Om).injective
  have : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed H.E
  have : IsScalarTower ℚ H.E N.Om := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : IsAlgClosure ℚ N.Om := IsAlgClosure.ofAlgebraic ℚ H.E N.Om
  have hA : (N.plOm.1 w).valuation (N.l i : N.Om) < 1 := by
    have := (N.plOm.2 w (N.l i : 𝓞 H.E)).2 hw
    simpa using this
  have hs : 1 ≤ N.s0 i := UpperTheory.KStar.S0.one_le_localLevel N i
  have hunit : IsUnit (1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u) := by
    have hm : -((N.l i : ℤ_[N.l i]) ^ N.s0 i * u) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
      rw [PadicInt.maximalIdeal_eq_span_p, neg_mem_iff, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm
    simpa using this
  obtain ⟨σ, hσ, hv⟩ := GlobalTheory.T.cyclotomicChar_inertia_surjective N.Om (N.l i) (N.plOm.1 w) hA hunit.unit
  have hv' : ((cycZ (F := ℚ) (Ω := N.Om) (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by rw [hv]; rfl
  obtain ⟨k, hk⟩ := pow_dvd_pow (N.l i) (UpperTheory.KStar.S0.factorization_conductor_le_localLevel N i)
  obtain ⟨g, hg, hc⟩ := transfer (E := H.E) (N.plOm.1 w) (N.l i) σ hσ
    (loc_fix H _ (N.lPrime i).out hA σ hσ fun t ht =>
      root_fix (N.l i) (N.s0 i) σ u hv' t (by rw [hk, pow_mul, ht, one_pow]))
  exact ⟨g, hg, by rw [hc, hv']⟩

end GlobalTheory.TameFixedLift
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.ContCharUnitsOL

theorem norm_algHom_apply (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (x : ↥K.1) : ‖((τ₀ x : ↥LL.1) : Om l)‖ = ‖(x : Om l)‖ := by
  have h1 : minpoly ℚ_[l] ((τ₀ x : ↥LL.1) : Om l) = minpoly ℚ_[l] x :=
    minpoly.algHom_eq ((LL.1).val.comp τ₀) ((Subtype.val_injective).comp τ₀.toRingHom.injective) x
  have h2 : minpoly ℚ_[l] (x : Om l) = minpoly ℚ_[l] x :=
    minpoly.algHom_eq (K.1).val Subtype.val_injective x
  show spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

theorem continuous_algHom (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    Continuous (fun x : ↥K.1 => τ₀ x) := by
  refine AddMonoidHomClass.continuous_of_bound τ₀ 1 (fun x => ?_)
  show ‖((τ₀ x : ↥LL.1) : Om l)‖ ≤ 1 * ‖(x : Om l)‖
  rw [norm_algHom_apply, one_mul]

theorem norm_le_one (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : ↥(GK K) →* (↥(K0 K))ˣ)
    (hc : Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))) (g : ↥(GK K)) :
    ‖(((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
  obtain ⟨B, hB⟩ := (isCompact_univ (X := ↥(GK K))).exists_bound_of_continuousOn hc.continuousOn
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
  have hpow : (((c (g ^ n) : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l) = ((((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) ^ n := by
    simp [map_pow]
  have := hB (g ^ n) (Set.mem_univ _)
  rw [hpow, norm_pow] at this
  linarith

end GlobalTheory.ContCharUnitsOL

namespace GlobalTheory.ContCharUnitsOL

theorem exists_unit_char (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (c : ↥(GK K) →* (↥(K0 K))ˣ)
    (hc : Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))) :
    ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ,
      Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧
      ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) *
        τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  let ι : ↥(K0 K) →+* ↥K.1 := algebraMap ↥(K0 K) ↥K.1
  have hι : ∀ x : ↥(K0 K), ((ι x : ↥K.1) : Om l) = (x : Om l) := fun x => rfl
  let v : ↥(GK K) → ↥LL.1 := fun g => τ₀ (ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)))
  let w : ↥(GK K) → ↥LL.1 := fun g => τ₀ (ι ((c g : (↥(K0 K))ˣ) : ↥(K0 K)))
  have hw : ∀ g, w g ∈ OL LL := fun g => by
    rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
    show ‖((τ₀ _ : ↥LL.1) : Om l)‖ ≤ 1
    rw [norm_algHom_apply, hι]
    exact norm_le_one l K c hc g
  have hv : ∀ g, v g ∈ OL LL := fun g => by
    rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
    show ‖((τ₀ _ : ↥LL.1) : Om l)‖ ≤ 1
    rw [norm_algHom_apply, hι, ← map_inv]
    exact norm_le_one l K c hc g⁻¹
  have hvw : ∀ g, v g * w g = 1 := fun g => by
    show τ₀ (ι _) * τ₀ (ι _) = 1
    rw [← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, map_one]
  have hwv : ∀ g, w g * v g = 1 := fun g => by rw [mul_comm]; exact hvw g
  let χf : ↥(GK K) → (↥(OL LL))ˣ := fun g =>
    ⟨⟨v g, hv g⟩, ⟨w g, hw g⟩, Subtype.ext (hvw g), Subtype.ext (hwv g)⟩
  let χ : ↥(GK K) →* (↥(OL LL))ˣ :=
    { toFun := χf
      map_one' := by
        apply Units.ext; apply Subtype.ext
        show τ₀ (ι (((c 1)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) = 1
        rw [map_one, inv_one, Units.val_one, map_one, map_one]
      map_mul' := fun g h => by
        apply Units.ext; apply Subtype.ext
        show τ₀ (ι (((c (g * h))⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) =
          τ₀ (ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) * τ₀ (ι (((c h)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)))
        rw [map_mul, mul_inv, Units.val_mul, map_mul, map_mul] }
  refine ⟨χ, ?_, fun g => hvw g⟩
  show Continuous v
  have hne : ∀ g, (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l) ≠ 0 := fun g h => by
    have : ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 0 := Subtype.ext h
    exact (c g).ne_zero this
  have h1 : Continuous (fun g : ↥(GK K) => ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) := by
    refine continuous_induced_rng.2 ?_
    have : (fun g : ↥(GK K) => ((ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)) : ↥K.1) : Om l)) =
        fun g => ((((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))⁻¹ := by
      funext g; rw [hι, Units.val_inv_eq_inv_val]; rfl
    rw [Function.comp_def, this]
    exact hc.inv₀ hne
  exact (continuous_algHom l K LL τ₀).comp h1

end GlobalTheory.ContCharUnitsOL

theorem GlobalTheory.ContCharUnitsOL.main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ↥(GK K) →* (↥(K0 K))ˣ), Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) → ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  intro l _ K LL τ₀ c hc
  exact GlobalTheory.ContCharUnitsOL.exists_unit_char l K LL τ₀ c hc
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaMove

theorem fixed_apply {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal) (σ : GQ l)
    {x : Om l} (hx : ∀ g ∈ H, g x = x) : ∀ g ∈ H, g (σ x) = σ x := by
  intro g hg
  have h := hx _ (hH.conj_mem' g hg σ)
  have h2 : σ ((σ⁻¹ * g * σ) x) = g (σ x) := by
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  rw [← h2, h]

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add (f := _), ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem norm_natCast_le_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one _ _

theorem norm_pow_sub_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : Subgroup (GQ l)), H.Normal → H.index ≠ 0 → ∀ m n : ℕ, H.index ≤ l ^ m → γ ^ l ^ n ∈ H → ∀ j ≤ m, ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖(γ ^ l ^ j) x - x‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (m - j)) * ‖x‖ := by
  intro l hl γ hγ H hH hi m n hm hn j
  have hτ0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have hτ1 := norm_natCast_le_one l
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hτpos : 0 < ‖((l : ℕ) : Om l)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hl0
  induction j with
  | zero =>
    intro _ x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hlt := GlobalTheory.WildMove.norm_sub_lt l γ hγ n x hx0 (hx _ hn)
    set z : Om l := (γ x - x) / x with hz
    have hzfix : ∀ g ∈ H, g z = z := by
      intro g hg
      rw [hz, map_div₀, map_sub, fixed_apply hH γ hx g hg, hx g hg]
    have hzn : ‖z‖ = ‖γ x - x‖ / ‖x‖ := norm_div _ _
    have hz1 : ‖z‖ < 1 := by rw [hzn, div_lt_one hxpos]; exact hlt
    have hv := GlobalTheory.Per.norm_pow_index_le_of_fixed l H hi z hzfix hz1
    have h1 : ‖z‖ ^ (l ^ m) ≤ ‖((l : ℕ) : Om l)‖ :=
      (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hm).trans hv
    have h2 : ‖z‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ m) := by
      have h3 := Real.rpow_le_rpow (by positivity) h1
        (show (0 : ℝ) ≤ ((l ^ m : ℕ) : ℝ)⁻¹ by positivity)
      rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ hl0)] at h3
      rw [one_div]
      exact_mod_cast h3
    rw [hzn, div_le_iff₀ hxpos] at h2
    simpa using h2
  | succ j ih =>
    intro hj x hx
    have ih' := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
    have hk' : m - (j + 1) = k := by omega
    rw [hk] at ih'
    rw [hk']
    set s : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hs
    have hs0 : 0 ≤ s := Real.rpow_nonneg hτ0 _
    have hs1 : s ≤ 1 := Real.rpow_le_one hτ0 hτ1 (by positivity)
    have h := (GlobalTheory.MemLoc.norm_geom_sum_galois_le l (γ ^ l ^ j) (fixedAdd H) s hs0 hs1
      (fun y hy => fixed_apply hH _ hy) (fun y hy => ih' y hy) x hx).2
    rw [← pow_mul, ← pow_succ] at h
    have hsl : s ^ l = ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ k) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hτ0]
      congr 1
      field_simp
      ring
    have hτs : ‖((l : ℕ) : Om l)‖ ≤ s ^ (l - 1) := by
      have h1 : s ^ l ≤ s ^ (l - 1) := pow_le_pow_of_le_one hs0 hs1 (by omega)
      refine le_trans ?_ h1
      rw [hsl]
      have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.pos
      have h2 : (1 : ℝ) / (l : ℝ) ^ k ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ hl1
      have h3 := Real.rpow_le_rpow_of_exponent_ge hτpos hτ1 h2
      rwa [Real.rpow_one] at h3
    rw [max_eq_left hτs, ← pow_succ, Nat.sub_add_cancel hl.out.pos, hsl] at h
    exact h

end GlobalTheory.InertiaMove
end

section

noncomputable section

namespace GlobalTheory.SenLines.AllRoots

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc GlobalTheory.SenLines TensorProduct

theorem zeta_isPrimitiveRoot {l : ℕ} [Fact l.Prime] (P : LocPrime l) {s : ℕ} (hs : 1 ≤ s) :
    IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [hpow]; exact P.ζQ_one
  have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by
    rw [pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

theorem exists_isPt {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ (l ^ s)) :
    ∃ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ := by
  have hs : 1 ≤ s := h.1
  have hLL := h.2.2.2
  have hprim := zeta_isPrimitiveRoot P hs
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos s).ne'⟩
  let Φ : Om l →ₐ[ℚ_[l]] Om l := ((H.W K s LL h).emb i).liftNormal (Om l)
  have hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l) := fun x =>
    AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x
  have hζ' : IsPrimitiveRoot (ζ : Om l) (l ^ s) := hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  obtain ⟨a, -, ha⟩ := (hprim.map_of_injective (f := Φ) Φ.injective).eq_pow_of_pow_eq_one hζ'.pow_eq_one
  rw [← map_pow] at ha
  have hpa : IsPrimitiveRoot (P.ζQ s ^ a) (l ^ s) :=
    IsPrimitiveRoot.of_map_of_injective (f := Φ) (ha ▸ hζ') Φ.injective
  have hconj : IsConjRoot ↥(K0 K) (P.ζQ s ^ a) (P.ζQ s) := by
    unfold IsConjRoot
    rw [GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs _ hprim, GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs _ hpa]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  let τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l := (Φ.comp (σ.restrictScalars ℚ_[l]).toAlgHom).comp (Ks K s).val
  let τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)
  have hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (σ (y : Om l)) := fun _ => rfl
  refine ⟨τ, fun x y hxy => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩
  · rw [hτ, hxy, show σ (x : Om l) = x from σ.commutes x, hΦ]
  · rw [hτ, hy, hσ, ha]

end GlobalTheory.SenLines.AllRoots
end
end

section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.UnramCyc


open PowerSeries in
theorem _root_.GlobalTheory.UnramCyc.chi_onto_of_unramified : ∀ {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (K : _root_.Formalism.BasicNotions.Loc.FinExt l),
    K.1 ≤ _root_.Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l → ∀ c : ℤ_[l]ˣ, ∃ g ∈ _root_.Formalism.BasicNotions.Loc.GK K, (P.χQ g : ℚ_[l]) = ((c : ℤ_[l]) : ℚ_[l]) := by
  intro l _ P K hK c
  have hnorm : ‖((c : ℤ_[l]) : ℚ_[l])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_units c
  obtain ⟨g, hg, hgc⟩ := _root_.GlobalTheory.Cyc.exists_chi_eq K P.χQ P.χQ_cyc _ hnorm
  have hK0 : _root_.Formalism.BasicNotions.Loc.K0 K = K.1 := by
    unfold _root_.Formalism.BasicNotions.Loc.K0
    exact inf_eq_left.mpr hK
  refine ⟨g, ?_, hgc⟩
  unfold _root_.Formalism.BasicNotions.Loc.GK
  rw [← hK0]
  exact hg

end GlobalTheory.UnramCyc
end
