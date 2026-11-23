module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle594
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle596
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
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
public import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle595
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.CMTypeRealEmb

theorem comp_isReal {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
  rw [ComplexEmbedding.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]
  rw [← IsCMField.complexEmbedding_complexConj]
  congr 1
  exact IsCMField.complexConj_apply_eq_self E a

theorem exists_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E),
      φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  set F := maximalRealSubfield E
  let ψ : I → F →+* ℂ := fun i => (φ i).comp (algebraMap F E)
  have hre : ∀ i, ComplexEmbedding.IsReal (ψ i) := fun i => comp_isReal (φ i)
  let e : I → Emb F := fun i => (hre i).embedding
  have he : ∀ i a, ((e i a : ℝ) : ℂ) = φ i (a : E) := fun i a =>
    (hre i).coe_embedding_apply a
  have hplace : ∀ i, (InfinitePlace.mk (φ i)).comap (algebraMap F E) = InfinitePlace.mk (ψ i) :=
    fun i => InfinitePlace.comap_mk _ _
  refine ⟨Equiv.ofBijective e ⟨?_, ?_⟩, fun i a => (he i a).symm⟩
  · intro i j hij
    have hψ : ψ i = ψ j := by
      ext a
      show φ i (a : E) = φ j (a : E)
      rw [← he, ← he, hij]
    have h1 : InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j) := by
      apply (IsCMField.equivInfinitePlace E).injective
      simp only [IsCMField.equivInfinitePlace_apply]
      rw [hplace, hplace, hψ]
    rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inl h.symm)).trans (hk j (Or.inl rfl)).symm
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inr h.symm)).trans (hk j (Or.inl rfl)).symm
  · intro f
    let fc : F →+* ℂ := Complex.ofRealHom.comp f
    have hfc : ComplexEmbedding.IsReal fc := by
      rw [ComplexEmbedding.isReal_iff]
      ext a
      simp [fc]
    let w : InfinitePlace E := (IsCMField.equivInfinitePlace E).symm (InfinitePlace.mk fc)
    obtain ⟨i, hi, _⟩ := hφ w.embedding
    have hmk : InfinitePlace.mk (φ i) = w := by
      rcases hi with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h2 : InfinitePlace.mk (ψ i) = InfinitePlace.mk fc := by
      rw [← hplace, hmk]
      have := (IsCMField.equivInfinitePlace E).apply_symm_apply (InfinitePlace.mk fc)
      rw [IsCMField.equivInfinitePlace_apply] at this
      exact this
    have h3 : ψ i = fc := by
      rcases InfinitePlace.mk_eq_iff.mp h2 with h | h
      · exact h
      · rw [← h]; exact ((ComplexEmbedding.isReal_iff).mp (hre i)).symm
    refine ⟨i, ?_⟩
    ext a
    apply Complex.ofReal_injective
    rw [he]
    show ψ i a = fc a
    rw [h3]

end GlobalTheory.CMTypeRealEmb
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.parFun_sieg_mul' : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), (∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (1 : UG c (stdJ ν E))) φ = φ) ∧ ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, ∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (p * q)) φ = parFun c ψ χ Q (mat c p) (parFun c ψ χ Q (mat c q) φ) := by
  first | exact @GlobalTheory.KSp.parFun_sieg_mul | exact GlobalTheory.KSp.parFun_sieg_mul | (intros; apply GlobalTheory.KSp.parFun_sieg_mul <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.CondExp

theorem dvd_prod_primes_iff {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) :
    v.asIdeal ∣ ∏ q ∈ Q, q.asIdeal ↔ v ∈ Q := by
  constructor
  · intro h
    have hex : ∃ q ∈ Q, v.asIdeal ∣ q.asIdeal :=
      (v.prime.dvd_finsetProd_iff (fun q : HeightOneSpectrum R => q.asIdeal)).1 h
    obtain ⟨q, hq, hd⟩ := hex
    have : q.asIdeal = v.asIdeal :=
      q.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd)
    rwa [← HeightOneSpectrum.ext this]
  · intro h
    exact Finset.dvd_prod_of_mem _ h

theorem prod_primes_ne_zero {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) : ∏ q ∈ Q, q.asIdeal ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot

theorem multiplicity_prod_primes_of_mem {R : Type} [CommRing R] [IsDedekindDomain R]
    (Q : Finset (HeightOneSpectrum R)) (v : HeightOneSpectrum R) (hv : v ∈ Q) :
    multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal) = 1 := by
  classical
  have h0 := prod_primes_ne_zero Q
  rw [← Finset.mul_prod_erase Q _ hv] at h0 ⊢
  rw [multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0),
    multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.ne_bot),
    multiplicity_eq_zero_of_not_dvd (by rw [dvd_prod_primes_iff]; simp)]

theorem condQ_exponents : ∀ (E : Type) [Field E] [NumberField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → condQ 𝔣 Q ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → Splits v) ∧ (∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q) ∧ (∀ v ∈ Q, expIn (condQ 𝔣 Q) v = 1) ∧ (∀ v ∉ Q, expIn (condQ 𝔣 Q) v = expIn 𝔣 v) ∧ {v : HeightOneSpectrum (OF E) | expIn (condQ 𝔣 Q) v ≠ 0}.Finite := by
  intro E _ _ 𝔣 Q hb ha
  have h0 : condQ 𝔣 Q ≠ 0 := mul_ne_zero hb.1 (prod_primes_ne_zero Q)
  have hm : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v =
      expIn 𝔣 v + multiplicity v.asIdeal (∏ q ∈ Q, q.asIdeal) := fun v =>
    multiplicity_mul v.prime (FiniteMultiplicity.of_prime_left v.prime h0)
  have hd : ∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q := by
    intro v hv
    by_contra h
    exact hv (multiplicity_eq_zero_of_not_dvd h)
  refine ⟨h0, ?_, hd, ?_, ?_, (Ideal.finite_factors h0).subset hd⟩
  · intro v hv
    rcases v.prime.dvd_or_dvd hv with h | h
    · exact (hb.2.2 v h).1
    · exact (ha v ((dvd_prod_primes_iff Q v).1 h)).1
  · intro v hv
    have h1 : expIn 𝔣 v = 0 := multiplicity_eq_zero_of_not_dvd (ha v hv).2
    rw [hm, h1, multiplicity_prod_primes_of_mem Q v hv]
  · intro v hv
    rw [hm, multiplicity_eq_zero_of_not_dvd (fun h => hv ((dvd_prod_primes_iff Q v).1 h)), add_zero]

end GlobalTheory.CMVal.CondExp
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.SplitPlace

theorem two_primes (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (p : Ideal (𝓞 F)) [p.IsMaximal] (P P' : p.primesOver (𝓞 E)) (hne : P ≠ P') :
    (∀ R : p.primesOver (𝓞 E), R = P ∨ R = P') ∧
      ∀ R : p.primesOver (𝓞 E), R.1.ramificationIdx (𝓞 F) * R.1.inertiaDeg (𝓞 F) = 1 := by
  classical
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2] at hsum
  have hpos : ∀ P : p.primesOver (𝓞 E),
      1 ≤ P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) := fun P =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hall : ∀ R : p.primesOver (𝓞 E), R = P ∨ R = P' := by
    intro R
    by_contra hR
    push Not at hR
    have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
      P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {R, P, P'})
    rw [hsum, Finset.sum_insert (by simp [hR.1, hR.2]), Finset.sum_pair hne] at h3
    have := hpos R
    have := hpos P
    have := hpos P'
    omega
  refine ⟨hall, fun R => ?_⟩
  have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
    P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {P, P'})
  rw [hsum, Finset.sum_pair hne] at h3
  have := hpos P
  have := hpos P'
  rcases hall R with rfl | rfl <;> omega

theorem split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → (∀ P P' : HeightOneSpectrum (𝓞 E), Over P v → Over P' v → P ≠ P' → ∀ R : HeightOneSpectrum (𝓞 E), Over R v → R = P ∨ R = P') ∧ ∀ P : HeightOneSpectrum (𝓞 E), Over P v → Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ (∀ (a : OF E) (k : ℕ), algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ k ↔ a ∈ v.asIdeal ^ k) ∧ ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal := by
  intro E _ _ _ v hv
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  have hm : ∀ P : HeightOneSpectrum (𝓞 E), Over P v → P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) :=
    fun P h => ⟨P.isPrime, ⟨h.symm⟩⟩
  have hne : ∀ P P' (h : Over P v) (h' : Over P' v), P ≠ P' →
      (⟨_, hm P h⟩ : v.asIdeal.primesOver (𝓞 E)) ≠ ⟨_, hm P' h'⟩ :=
    fun P P' h h' hn he => hn (HeightOneSpectrum.ext (congrArg Subtype.val he))
  refine ⟨fun P P' h h' hn R hR => ?_, fun P hP => ?_⟩
  · rcases (two_primes _ E h2 v.asIdeal _ _ (hne P P' h h' hn)).1 ⟨_, hm R hR⟩ with e | e
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val e))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val e))
  obtain ⟨Q, Q', hn, h, h'⟩ := hv
  have hef := (two_primes _ E h2 v.asIdeal _ _ (hne Q Q' h h' hn)).2 ⟨_, hm P hP⟩
  have hlo : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have he : v.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact Nat.eq_one_of_mul_eq_one_right hef
  have hf : v.asIdeal.inertiaDeg' P.asIdeal = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  refine ⟨?_, fun a k => ?_, fun b => ?_⟩
  · rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal v.asIdeal v.isPrime v.ne_bot, hf, pow_one]
  · rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot] at he
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ← HeightOneSpectrum.intValuation_liesOver v P a, he, pow_one]
  · rw [Ideal.inertiaDeg'_algebraMap] at hf
    let _ := Ideal.Quotient.field v.asIdeal
    obtain ⟨c, hc⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hf).2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨a, Ideal.Quotient.eq.1 hc.symm⟩

end GlobalTheory.CMVal.Euler.SplitPlace
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem isReduced_of_pReg_of_factor (p : ℕ) {Y₀ Y : Scheme.{0}} [IsReduced Y₀] (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    (hp : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0)
    (hfac : ∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) :
    IsReduced Y := by

  have haff : ∀ (V : Y.Opens), IsAffineOpen V → ∀ g : Γ(Y, V), IsNilpotent g → g = 0 := by
    intro V hV g hg
    let q : Γ(Y, V) := (p : Γ(Y, V))
    let O := Y.basicOpen q
    let ρ : Γ(Y, V) →+* Γ(Y, O) := (Y.presheaf.map (homOfLE (Y.basicOpen_le q)).op).hom
    letI : Algebra Γ(Y, V) Γ(Y, O) := ρ.toAlgebra
    haveI : IsLocalization.Away q Γ(Y, O) := hV.isLocalization_basicOpen q
    have hu : IsUnit ((p : ℕ) : Γ(O.toScheme, ⊤)) := by
      have h1 : IsUnit (algebraMap Γ(Y, V) Γ(Y, O) q) := IsLocalization.Away.algebraMap_isUnit q
      rw [map_natCast] at h1
      have := h1.map (O.topIso.inv.hom)
      rwa [map_natCast] at this
    obtain ⟨f₀, hf₀⟩ := hfac O.toScheme O.ι hu
    haveI : IsOpenImmersion (f₀ ≫ i) := hf₀ ▸ inferInstance
    haveI : IsOpenImmersion f₀ := IsOpenImmersion.of_comp f₀ i
    haveI : IsReduced O.toScheme := isReduced_of_isOpenImmersion f₀
    haveI : _root_.IsReduced Γ(Y, O) :=
      isReduced_of_injective (O.topIso.inv.hom) (O.topIso.commRingCatIsoToRingEquiv.symm.injective)
    have h0 : algebraMap Γ(Y, V) Γ(Y, O) g = 0 := (hg.map (algebraMap Γ(Y, V) Γ(Y, O))).eq_zero
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers q) _ g).1 h0
    have hk' : q ^ k * g = 0 := hk
    clear hk h0
    induction k with
    | zero => simpa using hk'
    | succ k ih => exact ih (hp V _ (by rw [pow_succ', _root_.mul_assoc] at hk'; exact hk'))
  refine ⟨fun U => ⟨fun f hf => ?_⟩⟩
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · rw [map_zero]
    exact haff V.1.1 V.1.2 _ (hf.map _)

theorem isReduced_normalModel_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ gs hgs _ Y s i _ _ hfl hfac
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsReduced Y₀ := GlobalTheory.isReduced_of_smooth_of_isReduced (gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s)
  have hR : ∀ a : R, (p : R) * a = 0 → a = 0 := fun a ha =>
    (mul_eq_zero.1 ha).resolve_left (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  haveI := hfl
  exact isReduced_of_pReg_of_factor p i (fun U f hf => pReg_of_flat (p := p) (s ≫ M.s) hR U f hf) hfac

end GlobalTheory.UPel.HT.ES
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_lie_conditions_of_etale_galois_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (Ga : Type) [Group Ga] (ρ : Ga → (o.A.left ⟶ o.A.left)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover Ga ρ ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ A', IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A'), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  first | exact @GlobalTheory.UPel.HT.EtaleLie.lie_of_etale | exact GlobalTheory.UPel.HT.EtaleLie.lie_of_etale | (intros; apply GlobalTheory.UPel.HT.EtaleLie.lie_of_etale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.UPel.HT

theorem trace_comp_pos_of_adjoint {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ u v, g u v = g v u) (hp : ∀ u, u ≠ 0 → 0 < g u u)
    (T T' : V →ₗ[ℝ] V) (hadj : ∀ u v, g (T u) v = g u (T' v)) (hT' : T' ≠ 0) :
    0 < LinearMap.trace ℝ V (T ∘ₗ T') := by
  letI core : InnerProductSpace.Core ℝ V :=
    { inner := fun x y => g x y
      conj_inner_symm := fun x y => by simpa using hs y x
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · simpa using (hp x h).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hp x h).ne' hx }
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore
  let b := stdOrthonormalBasis ℝ V
  rw [LinearMap.trace_eq_sum_inner _ b]
  have key : ∀ i, ⟪b i, (T ∘ₗ T') (b i)⟫_ℝ = g (T' (b i)) (T' (b i)) := by
    intro i
    show g (b i) (T (T' (b i))) = _
    rw [hs, hadj]
  simp only [key]
  have hnn : ∀ i, 0 ≤ g (T' (b i)) (T' (b i)) := fun i => by
    by_cases h : T' (b i) = 0
    · simp [h]
    · exact (hp _ h).le
  obtain ⟨i, hi⟩ : ∃ i, T' (b i) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hT'
    exact b.toBasis.ext (fun i => by simpa using h i)
  exact Finset.sum_pos' (fun i _ => hnn i) ⟨i, Finset.mem_univ _, hp _ hi⟩

theorem trace_mul_star_pos : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), x ≠ 0 →
    0 < LinearMap.trace ℤ D.La (DistribSMul.toLinearMap ℤ D.La (x * (D.star x).unop)) := by
  intro p _ D x hx
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨J, hJJ, hJinv, hpos, hcomm, -⟩ := D.dom
  let A : D.O → (ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La) := fun b =>
    (DistribSMul.toLinearMap ℤ D.La b).baseChange ℝ
  have hcomp : A x ∘ₗ A (D.star x).unop =
      (DistribSMul.toLinearMap ℤ D.La (x * (D.star x).unop)).baseChange ℝ := by
    clear hcomm hpos hJinv hJJ
    simp only [A]
    rw [← LinearMap.baseChange_comp]
    congr 1
    ext y
    show x • ((D.star x).unop • y) = (x * (D.star x).unop) • y
    rw [mul_smul]
  have hA : ∀ b (r : ℝ) (y : D.La), A b (r ⊗ₜ y) = r ⊗ₜ (b • y) := fun _ _ _ => rfl
  have hAJ : ∀ b, J ∘ₗ A b = A b ∘ₗ J := fun b => hcomm b (A b) (fun y => rfl)
  have hEF : ∀ y z : D.La, D.EF y z = - D.EF z y := by
    intro y z
    have h := D.alt (y + z)
    simp only [map_add (f := _), LinearMap.add_apply, D.alt y, D.alt z, zero_add, add_zero] at h
    omega
  have hanti : ∀ u v, D.EF.baseChange ℝ u v = - D.EF.baseChange ℝ v u := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hEF y z]
        simp only [zsmul_eq_mul, Int.cast_neg]
        ring
      | add v w hv hw =>
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [hv, hw]
        ring
    | add u w hu hw =>
      simp only [map_add (f := _), LinearMap.add_apply]
      rw [hu, hw]
      ring
  have hadjB : ∀ b u v, D.EF.baseChange ℝ (A b u) v = D.EF.baseChange ℝ u (A (D.star b).unop v) := by
    intro b u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul s z =>
        rw [hA, hA, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, D.adj]
      | add v w hv hw => simp only [map_add (f := _), LinearMap.add_apply, hv, hw]
    | add u w hu hw => simp only [map_add (f := _), LinearMap.add_apply, hu, hw]
  have hsym : ∀ u v, D.EF.baseChange ℝ (J u) v = D.EF.baseChange ℝ (J v) u := by
    intro u v
    rw [← hJinv (J v) u, hJJ, map_neg, LinearMap.neg_apply, hanti v (J u), neg_neg]
  have hadjg : ∀ u v, (D.EF.baseChange ℝ ∘ₗ J) (A x u) v =
      (D.EF.baseChange ℝ ∘ₗ J) u (A (D.star x).unop v) := by
    intro u v
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.comp_apply J (A x), hAJ, LinearMap.comp_apply, hadjB]
  have hinj : ∀ y : D.La, (1 : ℝ) ⊗ₜ[ℤ] y = 0 → y = 0 := by
    intro y hy
    refine (Module.forall_dual_apply_eq_zero_iff ℤ y).1 fun φ => ?_
    have h := congrArg (fun t => TensorProduct.rid ℤ ℝ (LinearMap.baseChange ℝ φ t)) hy
    simp only [LinearMap.baseChange_tmul, TensorProduct.rid_tmul, map_zero] at h
    simpa using h
  have hT' : A (D.star x).unop ≠ 0 := by
    intro h0
    apply hx
    have hz : ∀ y : D.La, (D.star x).unop • y = 0 := fun y => hinj _ (by
      have := LinearMap.congr_fun h0 ((1 : ℝ) ⊗ₜ y)
      rwa [hA, LinearMap.zero_apply] at this)
    have h1 := GlobalTheory.T.harrisTaylor_order_faithful_lattice p D _ hz
    rw [← D.star_star x, h1]
    simp
  have htr := trace_comp_pos_of_adjoint (D.EF.baseChange ℝ ∘ₗ J)
    (fun u v => by simp only [LinearMap.comp_apply]; exact hsym u v)
    (fun u hu => by simpa only [LinearMap.comp_apply] using hpos u hu)
    (A x) (A (D.star x).unop) hadjg hT'
  rw [hcomp, LinearMap.trace_baseChange] at htr
  simpa using htr

end GlobalTheory.UPel.HT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.exists_adjoint_primeToP_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : D.La →ₗ[D.O] D.La) (c k : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∃ g' : D.La →ₗ[D.O] D.La, (∀ x, g (g' x) = k • x) ∧ (∀ x, g' (g x) = k • x) ∧ (∀ x y, D.EF (g' x) (g' y) = (k ^ 2 / c) * D.EF x y) ∧ (∀ x, ∃ y, g' y = k • x) ∧ (k ^ 2 / c).Coprime p ∧ (k ^ 2 / c) ∣ k ^ 2 ∧ c * (k ^ 2 / c) = k ^ 2 := by
  first | exact @GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude | exact GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude <;> assumption)
end
