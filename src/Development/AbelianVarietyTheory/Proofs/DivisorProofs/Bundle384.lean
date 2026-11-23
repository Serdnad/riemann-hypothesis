module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle317
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle316
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle318
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

noncomputable section

namespace GlobalTheory.JacVal

theorem mem_iff_dvd_of_height_one : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A), Irreducible t → (∀ b : B, (b : K) = algebraMap F K t → b ∈ Q) → ∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a) := by
  intro k F K _ _ _ _ _ _ _ d u hu A _ hA B hB Q hQ hQ1 t ht htQ
  have hmem : ∀ x : K, x ∈ B ↔ x ∈ integralClosure A K := by
    intro x; rw [hB]; rfl
  let φ : A →+* B := (algebraMap A K).codRestrict B
    (fun a => (hmem _).2 (Subalgebra.algebraMap_mem _ a))
  letI : Algebra A B := φ.toAlgebra
  have hφ : ∀ a : A, ((algebraMap A B a : B) : K) = algebraMap F K (a : F) := fun a => rfl
  have hinjK : Function.Injective (algebraMap A K) := by
    intro x y h
    exact Subtype.val_injective ((algebraMap F K).injective h)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr (by
    intro x y h
    apply hinjK
    have := congrArg (fun z : B => (z : K)) h
    exact this)
  let f : B →ₐ[A] K := { (B.val : B →ₐ[k] K).toRingHom with commutes' := fun a => rfl }
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    have hb : IsIntegral A (b : K) := (hmem _).1 b.2
    exact (isIntegral_algHom_iff f Subtype.val_injective).1 hb⟩
  let e : MvPolynomial (Fin d) k ≃ₐ[k] A :=
    hu.aevalEquiv.trans (Subalgebra.equivOfEq _ _ hA.symm)
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have htp : Prime t := by
    have h1 : Irreducible (e.symm t) := (MulEquiv.irreducible_iff e.symm.toMulEquiv).2 ht
    have h2 : Prime (e.symm t) := h1.prime
    exact (MulEquiv.prime_iff e.symm.toMulEquiv).1 h2
  have ht0 : t ≠ 0 := htp.ne_zero
  haveI hsp : (Ideal.span {t} : Ideal A).IsPrime := (Ideal.span_singleton_prime ht0).2 htp
  set P : Ideal A := Q.comap (algebraMap A B) with hP
  haveI : P.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver P := ⟨rfl⟩
  have htP : t ∈ P := htQ _ (hφ t)
  have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 htP
  have hPeq : P = Ideal.span {t} := by
    by_contra hne
    have hlt : Ideal.span {t} < P := lt_of_le_of_ne hle (Ne.symm hne)
    obtain ⟨Q', hQ'Q, hQ', hQ'o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := Ideal.span {t}) (q := P) Q hlt
    haveI := hQ'
    have hQ'0 : Q' ≠ ⊥ := by
      rintro rfl
      have h := hQ'o.over
      have : t ∈ (⊥ : Ideal B).under A := h ▸ Ideal.mem_span_singleton_self t
      rw [Ideal.under, Ideal.mem_comap, Ideal.mem_bot] at this
      exact ht0 ((FaithfulSMul.algebraMap_injective A B) (by rw [this, map_zero]))
    haveI : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hQ'0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQ'Q
    have h4 : (1 : ℕ∞) ≤ Q'.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h2.trans hQ1.le)
    exact absurd h3 (by decide)
  intro a b hab
  have hb : b = algebraMap A B a := Subtype.ext (hab.trans (hφ a).symm)
  subst hb
  have : algebraMap A B a ∈ Q ↔ a ∈ P := Iff.rfl
  rw [this, hPeq, Ideal.mem_span_singleton]

end GlobalTheory.JacVal
end
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem ideal_map_eq_span_pow_uniformizer
    : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by
  intro V W _ _ _ _ _ _ f _ ϖ w e a I hϖ hw hfe hI
  by_cases h0 : I = ⊥
  · exfalso
    subst h0
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at hI
    exact hw.ne_zero (pow_eq_zero_iff'.mp hI).1
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h0 hϖ
  refine ⟨b, ?_, hb⟩
  rw [hb, Ideal.map_span, Set.image_singleton, map_pow,
    Ideal.span_singleton_eq_span_singleton] at hI
  have h1 : Associated (w ^ (e * b)) (w ^ a) := by
    rw [pow_mul]
    exact (hfe.pow_pow (n := b)).symm.trans hI
  have hw0 : w ≠ 0 := hw.ne_zero
  have hwu : ¬ IsUnit w := hw.not_isUnit
  apply le_antisymm
  · exact (pow_dvd_pow_iff hw0 hwu).mp h1.dvd
  · exact (pow_dvd_pow_iff hw0 hwu).mp h1.symm.dvd

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_complete_dvr_of_finite_fractionRing_hom :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (maximalIdeal V) V → ∀ (K' : Type) [Field K'] (σ : FractionRing V →+* K'),
      σ.Finite → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
        (_ : CharZero V') (f : V →+* V') (τ : K' →+* FractionRing V'),
        IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        ∀ a, τ (σ (algebraMap V _ a)) = algebraMap V' _ (f a) := by
  intro V _ _ _ _ hV K' _ σ hσ
  letI : Algebra (FractionRing V) K' := σ.toAlgebra
  letI : Algebra V K' := (σ.comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional (FractionRing V) K' := hσ
  haveI := hV
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  let B := integralClosure V K'
  haveI : Module.Finite V B := IsIntegralClosure.finite V (FractionRing V) K' B
  haveI hBd : IsDiscreteValuationRing B := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) K'
  haveI : IsFractionRing B K' := integralClosure.isFractionRing_of_finite_extension (FractionRing V) K'
  have hinj : Function.Injective (algebraMap V B) := by
    intro x y h
    have h2 := congrArg (algebraMap B K') h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
    exact (σ.injective.comp (IsFractionRing.injective V (FractionRing V))) h2
  haveI : CharZero B := charZero_of_injective_algebraMap hinj
  haveI : FaithfulSMul V B := (faithfulSMul_iff_algebraMap_injective V B).2 hinj
  haveI : Algebra.IsIntegral V B := IsIntegralClosure.isIntegral_algebra V K'
  haveI : IsLocalHom (algebraMap V B) := Algebra.IsIntegral.isLocalHom _ _
  let e : FractionRing B ≃ₐ[B] K' := IsLocalization.algEquiv (nonZeroDivisors B) (FractionRing B) K'
  refine ⟨B, inferInstance, inferInstance, hBd, inferInstance, algebraMap V B, e.symm.toRingHom,
    CompleteFiniteExtension.isAdicComplete_of_finite_local V B, hinj, inferInstance, ?_, fun a => ?_⟩
  · exact (inferInstance : Module.Finite V B)
  · change e.symm (algebraMap B K' (algebraMap V B a)) = _
    exact e.symm.commutes _

end GlobalTheory
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DPQuot

theorem quotient_subDPIdeal : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J),
    (∀ 𝔟 : Ideal B, δ.IsSubDPIdeal 𝔟 → ∃ δ' : DividedPowers (J.map (Ideal.Quotient.mk 𝔟)),
      IsDPMorphism δ δ' (Ideal.Quotient.mk 𝔟) ∧
      ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : B ⧸ 𝔟 →+* C),
        IsDPMorphism δ δ'' (g.comp (Ideal.Quotient.mk 𝔟)) → IsDPMorphism δ' δ'' g) ∧
    ∀ s : Set B, s ⊆ J →
      δ.IsSubDPIdeal (Ideal.span {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x ∈ s, y = δ.dpow n x}) := by
  intro B _ J δ
  refine ⟨fun 𝔟 h𝔟 ↦ ?_, fun s hs ↦ ?_⟩
  · have hinf : δ.IsSubDPIdeal (𝔟 ⊓ J) := by
      rw [inf_eq_left.mpr h𝔟.isSubideal]; exact h𝔟
    refine ⟨Quotient.dividedPowers δ hinf, Quotient.isDPMorphism δ hinf, ?_⟩
    intro C _ J'' δ'' g hg
    refine ⟨?_, fun {n} y hy ↦ ?_⟩
    · rw [Ideal.map_map]; exact hg.1
    · obtain ⟨a, ha, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
      rw [Quotient.dpow_apply δ hinf ha]
      exact hg.2 a ha
  · have hset : {y | ∃ n : ℕ, n ≠ 0 ∧ ∃ x ∈ s, y = δ.dpow n x} =
        {y : B | ∃ (n : ℕ) (_ : n ≠ 0) (x : B) (_ : x ∈ s), y = δ.dpow n x} := by
      ext y; simp only [Set.mem_setOf_eq, exists_prop]
    rw [hset, ← SubDPIdeal.span_carrier_eq_dpow_span δ hs]
    exact (SubDPIdeal.span δ s).toIsSubDPIdeal

end GlobalTheory.DPQuot
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etale_tensor_diagonal_complement_over_basicOpen : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∃ e u : A' ⊗[A] A', (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) ∧ algebraMap A (A' ⊗[A] A') f * u = 1 - e := by
  first | (exact @GlobalTheory.etale_diag_complement) | (exact GlobalTheory.etale_diag_complement) | (intros; apply GlobalTheory.etale_diag_complement  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_etale_faithfullyFlat_picMapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A), ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (_ : Module.FaithfullyFlat A B), CommRing.Pic.mapAlgebra A B c = 1 := by
  first | (exact @GlobalTheory.PicLoc.exists_etale_faithfullyFlat_mapAlgebra_eq_one) | (exact GlobalTheory.PicLoc.exists_etale_faithfullyFlat_mapAlgebra_eq_one) | (intros; apply GlobalTheory.PicLoc.exists_etale_faithfullyFlat_mapAlgebra_eq_one  <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.etale_over_directedUnion_essEtale_local : ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] [Algebra.Etale S B], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i))) → ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (C : ι → Subalgebra R B), Monotone C ∧ (∀ b : B, ∃ i, b ∈ C i) ∧ ∀ i (P : Ideal (C i)) (_ : P.IsPrime), (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  first | exact @GlobalTheory.EtaleOverDirectedUnion.construct | exact GlobalTheory.EtaleOverDirectedUnion.construct | (intros; apply GlobalTheory.EtaleOverDirectedUnion.construct <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.localization_directedUnion_essEtale_local : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → (∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (W : μ → Subalgebra R (Localization.AtPrime Q)), Monotone W ∧ (∀ x : Localization.AtPrime Q, ∃ m, x ∈ W m) ∧ (∀ m, ∀ x ∈ W m, IsUnit x → ∃ z ∈ W m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W m)) := by
  first | exact @GlobalTheory.localDecomp_core | exact GlobalTheory.localDecomp_core | (intros; apply GlobalTheory.localDecomp_core <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory

theorem flat_of_algHom_atPrime (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Algebra.Etale R B] (p : Ideal B) [p.IsPrime] (φ : A →ₐ[R] Localization.AtPrime p) :
    φ.toRingHom.Flat := by
  obtain ⟨g, hg, ψ, hψ⟩ := GlobalTheory.T.algHom_localizationAtPrime_factors_through_away R A B p φ
  set h := Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
    (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) with hh
  have e : φ.toRingHom = h.comp ψ.toRingHom := by ext a; exact (hψ a).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · letI : Algebra A (Localization.Away g) := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower R A (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
    haveI : Algebra.Etale A (Localization.Away g) := Algebra.Etale.of_restrictScalars R A _
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · letI : Algebra (Localization.Away g) (Localization.AtPrime p) := h.toAlgebra
    haveI : IsScalarTower B (Localization.Away g) (Localization.AtPrime p) :=
      IsScalarTower.of_algebraMap_eq (fun b => by
        change _ = h _
        simp [hh, Localization.awayLift, IsLocalization.Away.lift])
    have : Module.Flat (Localization.Away g) (Localization.AtPrime p) :=
      (Module.flat_iff_of_isLocalization (Localization.Away g) (Submonoid.powers g)
        (Localization.AtPrime p)).mpr inferInstance
    exact RingHom.flat_algebraMap_iff.mpr this

theorem flat_of_essEtale : ∀ (R L₁ L₂ : Type) [CommRing R] [CommRing L₁] [CommRing L₂] [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₂] [IsScalarTower R L₁ L₂], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₁)) → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₂)) → Module.Flat L₁ L₂ := by
  intro R L₁ L₂ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨e₁⟩⟩ ⟨A', _, _, _, q', _, ⟨e₂⟩⟩
  let φ : A →ₐ[R] Localization.AtPrime q' :=
    (e₂.symm.toAlgHom.comp (IsScalarTower.toAlgHom R L₁ L₂)).comp
      (e₁.toAlgHom.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)))
  have hφ := flat_of_algHom_atPrime R A A' q' φ
  let f : A →+* L₁ := e₁.toRingHom.comp (algebraMap A (Localization.AtPrime q))
  letI : Algebra A L₁ := f.toAlgebra
  letI : Algebra A L₂ := ((algebraMap L₁ L₂).comp f).toAlgebra
  haveI : IsScalarTower A L₁ L₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₁' : Localization.AtPrime q ≃ₐ[A] L₁ := { e₁ with commutes' := fun _ => rfl }
  haveI : IsLocalization q.primeCompl L₁ := IsLocalization.isLocalization_of_algEquiv q.primeCompl e₁'
  have hflat : Module.Flat A L₂ := by
    rw [← RingHom.flat_algebraMap_iff]
    have : algebraMap A L₂ = e₂.toRingHom.comp φ.toRingHom := by
      ext a; simp [φ, f, RingHom.algebraMap_toAlgebra]
    rw [this]
    exact RingHom.Flat.comp hφ (RingHom.Flat.of_bijective e₂.bijective)
  exact (Module.flat_iff_of_isLocalization L₁ q.primeCompl L₂).mpr hflat

end GlobalTheory
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.surjective_of_injective_of_trace_eq_of_smul_mem_range : ∀ (S A B : Type) [CommRing S] [IsLocalRing S] [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A] [Algebra.Etale S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B] [Algebra.Etale S B] (φ : A →ₐ[S] B), Function.Injective φ → ∀ s : S, s ≠ 0 → (∀ b : B, s • b ∈ φ.range) → (∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x) → Function.Surjective φ := by
  first | exact @GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range | exact GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range | (intros; apply GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_ne_zero_isNilpotent_mul_finite_inf_fg_ideals : ∀ (D E : Type) [CommRing D] [IsDomain D] [CommRing E] [Algebra D E] (ι : Type) (X : Finset ι) (P : ι → Ideal E), (∀ i ∈ X, (P i).FG) → (∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → (⨅ i ∈ X, P i) ≤ Q) → ∃ s : D, s ≠ 0 ∧ ∀ y ∈ (⨅ i ∈ X, P i), IsNilpotent (algebraMap D E s * y) := by
  first | (exact @GlobalTheory.FinInterNil.main) | (exact GlobalTheory.FinInterNil.main) | (intros; apply GlobalTheory.FinInterNil.main  <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.lift_square_presentation_of_flat_alt : ∀ (O B A k H σ : Type) [CommRing O] [IsLocalRing O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Module.Flat B A] [Field k] [CommRing H] [Algebra k H] [Fintype σ] (ε : A →ₐ[O] O) (π : O →+* k) (ρ : A →+* H) (εH : H →ₐ[k] k) (x : σ → A), Function.Surjective π → RingHom.ker π = IsLocalRing.maximalIdeal O → (∀ c : O, ρ (algebraMap O A c) = algebraMap k H (π c)) → (∀ a, εH (ρ a) = π (ε a)) → RingHom.ker ρ = (RingHom.ker (π.comp ((ε : A →+* O).comp (algebraMap B A)))).map (algebraMap B A) → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A)).FG → ∀ g : σ → MvPolynomial σ k, (∀ i, MvPolynomial.aeval (fun j => ρ (x j)) (g i) = 0) → RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H)) * RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) → ∃ f : σ → MvPolynomial σ B, (∀ i, MvPolynomial.aeval x (f i) = 0) ∧ RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) := by
  first | exact @GlobalTheory.lift_square_presentation_of_flat | exact GlobalTheory.lift_square_presentation_of_flat | (intros; apply GlobalTheory.lift_square_presentation_of_flat <;> assumption)
end
