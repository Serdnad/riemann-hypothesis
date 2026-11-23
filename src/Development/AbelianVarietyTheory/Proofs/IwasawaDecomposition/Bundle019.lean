module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section

section

open NumberField

namespace GlobalTheory.CMScalar
open Matrix Polynomial

theorem eval_charpolyRev_neg {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (w : K) :
    (-A).charpolyRev.eval w = (1 + w • A).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm w, sub_eq_add_neg]

theorem exists_unit_norm_one_det_ne_zero (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K]
    [CharZero K] (n : ℕ) (M : (L →+* K) → Matrix (Fin n) (Fin n) K) :
    ∃ u : L, u * (IsCMField.complexConj L : L →+* L) u = 1 ∧ ∀ σ : L →+* K, (1 + σ u • M σ).det ≠ 0 := by
  classical
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => IsCMField.complexConj_apply_apply L x
  obtain ⟨y, hy⟩ : ∃ y : L, c y ≠ y := by
    by_contra h
    push_neg at h
    apply IsCMField.complexConj_ne_one L
    ext x
    exact h x
  set i : L := y - c y with hi
  have hi0 : i ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hci : c i = -i := by rw [hi, map_sub, hcc]; ring
  have hden : ∀ t : ℚ, (1 : L) + (t : L) * i ≠ 0 := by
    intro t h
    have h1 : (t : L) * i = -1 := by linear_combination h
    have h2 := congrArg c h1
    rw [map_mul, map_ratCast, hci, map_neg, map_one] at h2
    have : (2 : L) = 0 := by linear_combination h1 + h2
    exact two_ne_zero this
  let f : ℚ → L := fun t => (1 - (t : L) * i) / (1 + (t : L) * i)
  have hfu : ∀ t, f t * c (f t) = 1 := by
    intro t
    have hd := hden t
    have hd' : (1 : L) - (t : L) * i ≠ 0 := by
      intro h; apply hden (-t); push_cast; linear_combination h
    have e : c (f t) = (1 + (t : L) * i) / (1 - (t : L) * i) := by
      simp only [f, map_div₀, map_sub, map_add (f := _), map_one, map_mul, map_ratCast, hci]
      congr 1 <;> ring
    rw [e, div_mul_div_comm]
    exact (div_eq_one_iff_eq (mul_ne_zero hd hd')).2 (by ring)
  have hfinj : Function.Injective f := by
    intro s t hst
    simp only [f] at hst
    rw [div_eq_div_iff (hden s) (hden t)] at hst
    have h2 : (2 : L) * ((t : L) - s) * i = 0 := by linear_combination hst
    have : ((t : L) - s) = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h two_ne_zero
        · exact h
      · exact absurd h hi0
    have : ((t - s : ℚ) : L) = 0 := by push_cast; exact this
    exact (sub_eq_zero.1 (Rat.cast_eq_zero.1 this)).symm
  have hp : ∀ σ : L →+* K, (-(M σ)).charpolyRev ≠ 0 := by
    intro σ h
    have := Matrix.eval_charpolyRev (M := -(M σ))
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  let B : Set L := ⋃ σ : L →+* K, σ ⁻¹' ((-(M σ)).charpolyRev.roots.toFinset : Set K)
  have hB : B.Finite := by
    apply Set.finite_iUnion
    intro σ
    exact (Finset.finite_toSet _).preimage σ.injective.injOn
  have hS : (f ⁻¹' B).Finite := hB.preimage hfinj.injOn
  obtain ⟨t, ht⟩ := (Set.infinite_univ (α := ℚ)).diff hS |>.nonempty
  refine ⟨f t, hfu t, fun σ hσ => ht.2 ?_⟩
  simp only [Set.mem_preimage, B, Set.mem_iUnion]
  refine ⟨σ, ?_⟩
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (hp σ), Polynomial.IsRoot, eval_charpolyRev_neg]
  exact hσ

end GlobalTheory.CMScalar
end

section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped WithZeroTopology WithZero

namespace GlobalTheory.CompletionHomContinuous

theorem continuous_of_valuation_eq_pow {A B Γ : Type*} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [hA : Valued A Γ] [hB : Valued B Γ]
    (hs : Function.Surjective hA.v) (g : A →+* B) {e : ℕ} (he : 0 < e)
    (hg : ∀ x, hB.v (g x) = hA.v x ^ e) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero B Γ).tendsto_right_iff]
  intro γ _
  have hc : Continuous fun x : A => hA.v x ^ e :=
    (Valued.continuous_valuation_of_surjective hs).pow e
  have h0 : Tendsto (fun x : A => hA.v x ^ e) (𝓝 0) (𝓝 0) :=
    hc.tendsto' 0 0 (by simp [he.ne'])
  rw [WithZeroTopology.tendsto_zero] at h0
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  filter_upwards [h0 _ hγ] with x hx
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, hg]
  exact hx

theorem exists_completion_hom (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (RingOfIntegers K))
    (v' : HeightOneSpectrum (RingOfIntegers L)) (e : ℕ) (he : 0 < e)
    (h : ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) :
    ∃ f : adicCompletion K v →+* adicCompletion L v', Continuous f ∧
      (∀ x : K, f (algebraMap K (adicCompletion K v) x) =
        algebraMap L (adicCompletion L v') (algebraMap K L x)) ∧
      ∀ y : adicCompletion K v, (Valued.v (f y) : WithZero (Multiplicative ℤ)) = Valued.v y ^ e := by
  let g : WithVal (v.valuation K) →+* adicCompletion L v' :=
    (algebraMap L (adicCompletion L v')).comp
      ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom)
  have hL : ∀ x : L, (Valued.v (algebraMap L (adicCompletion L v') x) : WithZero (Multiplicative ℤ))
      = v'.valuation L x := fun x => valuedAdicCompletion_eq_valuation' v' x
  have hK : ∀ x : K, (Valued.v (algebraMap K (adicCompletion K v) x) : WithZero (Multiplicative ℤ))
      = v.valuation K x := fun x => valuedAdicCompletion_eq_valuation' v x
  have hg : Continuous g := by
    refine continuous_of_valuation_eq_pow (Γ := WithZero (Multiplicative ℤ)) ?_ g he ?_
    · intro c
      obtain ⟨x, hx⟩ := v.valuation_surjective K c
      exact ⟨(WithVal.equiv (v.valuation K)).symm x, hx⟩
    · intro x
      exact (hL _).trans (h _)
  let f : adicCompletion K v →+* adicCompletion L v' :=
    (UniformSpace.Completion.extensionHom g hg).comp (adicCompletion.equiv K v).toRingHom
  have hf : Continuous f :=
    (UniformSpace.Completion.continuous_extension (f := g)).comp
      (adicCompletion.continuous_toCompletion K v)
  have hfx : ∀ x : K, f (algebraMap K (adicCompletion K v) x) =
      algebraMap L (adicCompletion L v') (algebraMap K L x) := fun x =>
    UniformSpace.Completion.extensionHom_coe g hg ((WithVal.equiv (v.valuation K)).symm x)
  refine ⟨f, hf, hfx, fun y => ?_⟩
  refine (denseRange_algebraMap K v).induction_on y ?_ ?_
  · exact isClosed_eq
      ((Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective L v')).comp hf)
      ((Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v)).pow e)
  · intro x
    rw [hfx, hL, hK, h]

end GlobalTheory.CompletionHomContinuous
end

section

namespace GlobalTheory.TendstoOfIntegrals

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology

theorem tendsto_of_forall_integral {L : Type} [Field L] [NumberField L] {ι : Type} {l : Filter ι}
    (f : ι → FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (b : FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (hf : ∀ (i : ι) (v : HeightOneSpectrum (NumberField.RingOfIntegers L)),
      (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hb : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      (b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hl : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      Tendsto (fun i ↦ (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) →
        a.adicCompletion L) v) l
        (𝓝 ((b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v))) :
    Tendsto f l (𝓝 b) := by

  let A : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → Set (v.adicCompletion L) :=
    fun v ↦ (v.adicCompletionIntegers L : Set (v.adicCompletion L))
  let g : ι → (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v :=
    fun i v ↦ ⟨_, hf i v⟩
  let c : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v := fun v ↦ ⟨_, hb v⟩
  have hg : Tendsto g l (𝓝 c) :=
    tendsto_pi_nhds.2 fun v ↦ tendsto_subtype_rng.2 (hl v)
  have hemb := RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦ v.adicCompletion L)
    (A := A) (𝓕 := cofinite)
  exact (hemb.continuous.tendsto c).comp hg

end GlobalTheory.TendstoOfIntegrals

theorem GlobalTheory.TendstoOfIntegrals.target_check : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {ι : Type} {l : Filter ι} (f : ι → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L) (b : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L), (∀ (i : ι) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), Filter.Tendsto (fun (i : ι) ↦ (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v) l (nhds ((b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v))) → Filter.Tendsto f l (nhds b) := by
  intro L _ _ ι l f b hf hb hl
  exact GlobalTheory.TendstoOfIntegrals.tendsto_of_forall_integral f b hf hb hl
end

section

open IsLocalRing

namespace GlobalTheory

open IsLocalRing in
private theorem ringKrullDim_le_of_isLocalization (A D : Type) [CommRing A] [CommRing D]
    [Algebra A D] (M : Submonoid A) [IsLocalization M D] :
    ringKrullDim D ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A D)) ?_
  refine Monotone.strictMono_of_injective (fun p q h => ?_)
    (PrimeSpectrum.localization_comap_injective D M)
  exact Ideal.comap_mono h

open IsLocalRing in
private theorem ringKrullDim_finite_of_finiteType_int (A : Type) [CommRing A]
    [Algebra.FiniteType ℤ A] : ringKrullDim A < ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  refine lt_of_le_of_lt (ringKrullDim_le_of_surjective f.toRingHom hf) ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  have h : ((1 + Nat.card (Fin n) : ℕ) : WithBot ℕ∞) < ⊤ :=
    WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  push_cast [ENat.card_eq_coe_natCard]
  exact h


open IsLocalRing in
theorem _root_.GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D] :
    ringKrullDim D < ⊤ :=
  lt_of_le_of_lt
    (ringKrullDim_le_of_isLocalization (Algebra.EssFiniteType.subalgebra ℤ D) D
      (Algebra.EssFiniteType.submonoid ℤ D))
    (ringKrullDim_finite_of_finiteType_int _)

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem integral_of_finite_base_change_image : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ (ω : L ⊗[F] K) (p : Polynomial (U ⊗[T] C)), p.Monic → p.eval₂ φ ω = 0 → IsIntegral U ω := by
  intro T U C F K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ ω p hp h
  letI : Algebra (U ⊗[T] C) (L ⊗[F] K) := φ.toAlgebra
  have hmap : algebraMap (U ⊗[T] C) (L ⊗[F] K) = φ := rfl
  haveI : IsScalarTower U (U ⊗[T] C) (L ⊗[F] K) := by
    refine IsScalarTower.of_algebraMap_eq fun u => ?_
    rw [hmap]
    change algebraMap U (L ⊗[F] K) u = φ (u ⊗ₜ 1)
    rw [hφ, map_one]
    rfl
  have hint : IsIntegral (U ⊗[T] C) ω := ⟨p, hp, h⟩
  haveI : Algebra.IsIntegral U (U ⊗[T] C) := inferInstance
  exact isIntegral_trans ω hint

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem flat_comap_map_of_one_tmul_mem {B C R : Type} [CommRing B] [CommRing C] [CommRing R]
    [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R)
    (h : (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R)) :
    r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by
  let f : B →ₗ[B] C ⧸ J := (Ideal.Quotient.mkₐ B J).toLinearMap ∘ₗ Algebra.linearMap B C
  have hex := Module.Flat.rTensor_exact R (LinearMap.exact_subtype_ker_map f)
  let φ : C ⊗[B] R →ₐ[B] (C ⧸ J) ⊗[B] R :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B J) (AlgHom.id B R)
  have hle : J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R) ≤
      RingHom.ker φ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    show φ (j ⊗ₜ[B] (1 : R)) = 0
    simp [φ, Algebra.TensorProduct.map_tmul, (Ideal.Quotient.eq_zero_iff_mem).2 hj]
  have h0 : LinearMap.rTensor R f ((1 : B) ⊗ₜ[B] r) = 0 := by
    have := hle h
    rw [RingHom.mem_ker] at this
    simpa [f, φ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul] using this
  obtain ⟨x, hx⟩ := (hex ((1 : B) ⊗ₜ[B] r)).1 h0
  have key : ∀ y : (LinearMap.ker f) ⊗[B] R,
      TensorProduct.lid B R (LinearMap.rTensor R (LinearMap.ker f).subtype y) ∈
        (J.comap (algebraMap B C)).map (algebraMap B R) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul i s =>
      simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype, TensorProduct.lid_tmul]
      rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      apply Ideal.mem_map_of_mem
      have hi := i.2
      rw [LinearMap.mem_ker] at hi
      simp only [f, LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
        AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hi
      exact hi
    | add a b ha hb => simpa [map_add (f := _)] using Ideal.add_mem _ ha hb
  have := key x
  rwa [hx, TensorProduct.lid_tmul, one_smul] at this

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory.FlatIdealInf

open TensorProduct

theorem range_lTensor_iInf_le {B R M : Type} [CommRing B] [AddCommGroup R] [Module B R]
    [Module.Flat B R] [AddCommGroup M] [Module B M] {ι : Type} [Finite ι]
    (K : ι → Submodule B M) :
    ⨅ i, LinearMap.range (LinearMap.lTensor R (K i).subtype) ≤
      LinearMap.range (LinearMap.lTensor R (⨅ i, K i).subtype) := by
  classical
  cases nonempty_fintype ι
  intro t ht
  rw [Submodule.mem_iInf] at ht
  let φ : M →ₗ[B] (∀ i, M ⧸ K i) := LinearMap.pi (fun i => (K i).mkQ)
  have hexB : Function.Exact (⨅ i, K i).subtype φ := by
    rw [LinearMap.exact_iff, LinearMap.ker_pi, Submodule.range_subtype]
    simp only [Submodule.ker_mkQ]
  have hex := Module.Flat.lTensor_exact R hexB
  have hcomp : ∀ i (u : R ⊗[B] M), TensorProduct.piRight B B R (fun i => M ⧸ K i) (LinearMap.lTensor R φ u) i =
      LinearMap.lTensor R (K i).mkQ u := by
    intro i u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [φ]
    | add x y hx hy => simp_all
  have h0 : LinearMap.lTensor R φ t = 0 := by
    apply (TensorProduct.piRight B B R (fun i => M ⧸ K i)).injective
    rw [map_zero]
    funext i
    rw [hcomp i t, Pi.zero_apply]
    obtain ⟨s, hs⟩ := ht i
    rw [← hs]
    exact (lTensor_exact R (LinearMap.exact_subtype_mkQ (K i)) (Submodule.mkQ_surjective _) _).mpr
      ⟨s, rfl⟩
  obtain ⟨s, hs⟩ := (hex t).mp h0
  exact ⟨s, hs⟩

theorem mem_map_algebraMap_iff {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (I : Ideal B) (x : R) :
    x ∈ I.map (algebraMap B R) ↔
      x ⊗ₜ[B] (1 : B) ∈ LinearMap.range (LinearMap.lTensor R (Submodule.subtype (I.restrictScalars B))) := by
  rw [← Ideal.map_includeRight_eq (R := B) (A := R) I, Submodule.restrictScalars_mem]
  let e := (Algebra.TensorProduct.rid B R R).toRingEquiv
  have he : (e : R ⊗[B] B →+* R).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[B] R ⊗[B] B) : B →+* R ⊗[B] B) = algebraMap B R := by
    ext b
    simp [e, Algebra.algebraMap_eq_smul_one]
  rw [← he, ← Ideal.map_map, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl

theorem iInf_map_le_map_iInf : ∀ {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    [Module.Flat B R] {ι : Type} [Finite ι] (K : ι → Ideal B),
    ⨅ i, (K i).map (algebraMap B R) ≤ (⨅ i, K i).map (algebraMap B R) := by
  intro B R _ _ _ _ ι _ K x hx
  rw [mem_map_algebraMap_iff]
  have h := range_lTensor_iInf_le (R := R) (fun i => (K i).restrictScalars B)
  have hK : (⨅ i, (K i).restrictScalars B) = (⨅ i, K i).restrictScalars B := by
    ext y; simp
  rw [hK] at h
  apply h
  rw [Submodule.mem_iInf]
  intro i
  exact (mem_map_algebraMap_iff (K i) x).mp ((Submodule.mem_iInf _).mp hx i)

end GlobalTheory.FlatIdealInf
end

section

open NumberField IsDedekindDomain IsLocalRing IsDiscreteValuationRing

namespace GlobalTheory

namespace OrderNorm

theorem length_quot_ringEquiv {T U : Type*} [CommRing T] [CommRing U] (e : T ≃+* U) (x : T) :
    Module.length T (T ⧸ Ideal.span {x}) = Module.length U (U ⧸ Ideal.span {e x}) := by
  let _ : Algebra T U := e.toRingHom.toAlgebra
  let f : T ≃ₐ[T] U := AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)
  have hI : Ideal.span {e x} = (Ideal.span {x}).map (f : T →+* U) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [(Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) f hI).toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective e.surjective

end OrderNorm

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.ValuationPowSubPow

theorem valuation_pow_sub_pow_le {K : Type u_1} {Γ : Type u_2} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {a b : K}
    (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) : w (a ^ m - b ^ m) ≤ w (a - b) := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
    rw [h]
    refine w.map_add_le ?_ ?_
    · rw [map_mul]
      exact (mul_le_of_le_one_left' ha).trans ih
    · rw [map_mul, map_pow]
      exact mul_le_of_le_one_left' (pow_le_one' hb n)

end GlobalTheory.ValuationPowSubPow
end
