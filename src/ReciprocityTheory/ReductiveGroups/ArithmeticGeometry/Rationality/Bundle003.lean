module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Lemmata.MiscLemmasJ.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle002
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Trace.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotShiftPfH
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.Order.Int.LeastGreatest

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open Module

section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

theorem freeQuot_exists_smul_mem (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.SecondBlockLemmaK.goal1 S hx

theorem freeQuot_rank_span (S : Submodule R X) :
    Module.rank R S = Module.rank F (Submodule.span F (S : Set X)) := by
  set T := Submodule.span F (S : Set X)
  have hST : S ≤ T.restrictScalars R := fun x hx => Submodule.subset_span hx
  let S' : Submodule R (T.restrictScalars R) := S.comap (T.restrictScalars R).subtype
  have h0 : Module.rank R ((T.restrictScalars R) ⧸ S') = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S' q
    obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem S (y.2 : (y : X) ∈ T)
    refine ⟨d, hd, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hd'
  have h1 := rank_quotient_add_rank_of_isDomain S'
  rw [h0, zero_add, (Submodule.comapSubtypeEquivOfLe hST).rank_eq] at h1
  rw [h1, IsLocalization.rank_eq (N := T) F (nonZeroDivisors R) le_rfl]
  rfl

end

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem galAct_tmul {K₂ : Type*} [Field K₂] [Algebra K K₂] (σ : K₂ ≃ₐ[K] K₂) (a : K₂) (v : V) :
    galAct σ (a ⊗ₜ[K] v) = σ a ⊗ₜ[K] v := rfl

end SlopeTestRemainingChoices

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable def lenLa {K : Type*} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    (N : Type*) [AddCommGroup N] [Module (𝓞 K) N] : ℕ∞ :=
  Module.length (Localization.AtPrime la.asIdeal) (LocalizedModule la.asIdeal.primeCompl N)

def LiesOver {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    (w : HeightOneSpectrum (𝓞 K₁)) (la : HeightOneSpectrum (𝓞 K)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁)) = la.asIdeal

abbrev QuotMW {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) (W : Submodule K V) :=
  M ⧸ (W.restrictScalars (𝓞 K)).comap M.subtype

noncomputable def lenW {K K₁ V : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁]
    [Algebra K K₁] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (w : HeightOneSpectrum (𝓞 K₁)) (M : Submodule (𝓞 K) V) (W : Submodule K V) {ρ : ℕ}
    (θ : Fin ρ → M) : ℕ∞ :=
  let Rw := (w.valuationSubringAtPrime K₁).toSubring
  letI : Module Rw (K₁ ⊗[K] V) := Module.compHom _ Rw.subtype
  let Mw := Submodule.span Rw ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (M.restrictScalars ℤ : Set V))
  let Nw := (Submodule.span Rw (Submodule.span K₁
      ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓ Mw) ⊔
    Submodule.span Rw (Set.range fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V))
  Module.length Rw (Mw ⧸ Nw.comap Mw.subtype)

def LenDescentStatement : Prop :=
  ∀ (K K₁ V : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → Submodule.span K (M : Set V) = ⊤ →
    ∀ (W : Submodule K V) {ρ : ℕ} (θ : Fin ρ → M) (la : HeightOneSpectrum (𝓞 K))
      (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la →
      lenW w M W θ = (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) *
        lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
          (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W)))

def QuotCoreStatement : Prop :=
  LenDescentStatement →
  ∀ (K K₁ V : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → Submodule.span K (M : Set V) = ⊤ →
    ∀ (W : Submodule K V) (θ : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → M),
      Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤ →
    ∀ (c : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V)),

      (∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
        x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) →
    ∀ (be : HeightOneSpectrum (𝓞 K) → ℝ)
      (s : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → HeightOneSpectrum (𝓞 K₁) → ℝ),
      (∀ la, 0 ≤ be la) → (Function.support be).Finite → (∀ i, (Function.support (s i)).Finite) →

      (∀ (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la →
        ∀ i, ∀ m ∈ M, c i ((1 : K₁) ⊗ₜ[K] m) ≠ 0 →
          -((w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * be la) ≤
            (ordAt w (c i ((1 : K₁) ⊗ₜ[K] m)) : ℝ) + s i w) →
    ∀ (supN : (K →+* ℂ) → V → ℝ) (a : Fin (Module.finrank (𝓞 K) (QuotMW M W)) → InfinitePlace K₁ → ℝ)
      (Bθ Carch Bdeg : ℝ),

      (∀ τ v, supN ((starRingEnd ℂ).comp τ) v = supN τ v) →

      (∀ j, (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Fintype.card (K →+* ℂ) : ℝ) ≤ Bθ) →

      (∀ (σ : InfinitePlace K₁) i j, c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)) ≠ 0 →
        Real.log (σ (c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V)))) + a i σ ≤
          Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch) →

      (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
          (Module.finrank ℚ K₁ : ℝ) ≤ Bdeg) →
      ∃ nn : HeightOneSpectrum (𝓞 K) →₀ ℝ,
        (∀ la, ∃ ℓ : ℕ,
          lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
            (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) = ℓ ∧
          (ℓ : ℝ) ≤ nn la + (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) * be la) ∧
        (nn.sum fun la v => v * logN la) / (Module.finrank ℚ K : ℝ) ≤
          (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) * (Bθ + Carch + Bdeg) +
            (Module.finrank (𝓞 K) (QuotMW M W) : ℝ) / 2 *
              Real.log (Module.finrank (𝓞 K) (QuotMW M W) : ℝ)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

namespace DescPf

variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]

noncomputable def trT [FiniteDimensional K K₂] : K₂ ⊗[K] V →ₗ[K] V :=
  TensorProduct.lid K V ∘ₗ LinearMap.rTensor V (Algebra.trace K K₂)

lemma trT_tmul [FiniteDimensional K K₂] (x : K₂) (v : V) :
    trT (x ⊗ₜ[K] v) = Algebra.trace K K₂ x • v := by
  simp [trT]

lemma galAct_tmul (σ : K₂ ≃ₐ[K] K₂) (x : K₂) (v : V) :
    galAct σ (x ⊗ₜ[K] v) = σ x ⊗ₜ[K] v := by
  simp [galAct]

lemma sum_galAct [FiniteDimensional K K₂] [IsGalois K K₂] (y : K₂ ⊗[K] V) :
    ∑ σ : K₂ ≃ₐ[K] K₂, galAct σ y = (1 : K₂) ⊗ₜ[K] trT y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
    simp only [galAct_tmul, trT_tmul]
    rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add y z hy hz =>
    simp only [map_add (f := _), Finset.sum_add_distrib, hy, hz, TensorProduct.tmul_add]

lemma expand [FiniteDimensional K K₂] [Algebra.IsSeparable K K₂] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K K₂) (w : K₂ ⊗[K] V) :
    w = ∑ i, ((Algebra.traceForm K K₂).dualBasis
      (traceForm_nondegenerate (K := K) (L := K₂)) b i) • ((1 : K₂) ⊗ₜ[K] trT (b i • w)) := by
  set d := (Algebra.traceForm K K₂).dualBasis (traceForm_nondegenerate (K := K) (L := K₂)) b
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
    have hx : x = ∑ i, Algebra.trace K K₂ (b i * x) • d i := by
      conv_lhs => rw [← d.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm]
    conv_lhs => rw [hx]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, trT_tmul]
    exact TensorProduct.smul_tmul _ _ _
  | add y z hy hz =>
    simp only [smul_add, map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hy, ← hz]

end DescPf

theorem galoisDescent_holds : GaloisDescentStatement := by
  intro K K₂ V _ _ _ _ _ _ _ W hW
  classical
  apply le_antisymm
  · intro w hw
    rw [DescPf.expand (Module.finBasis K K₂) w]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    simp only [SetLike.mem_coe, kPoints, Submodule.mem_comap, Submodule.restrictScalars_mem,
      TensorProduct.mk_apply]
    rw [← DescPf.sum_galAct]
    exact Submodule.sum_mem _ fun σ _ => hW σ _ (W.smul_mem _ hw)
  · rw [baseSpan, Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    simpa only [SetLike.mem_coe, kPoints, Submodule.mem_comap, Submodule.restrictScalars_mem,
      TensorProduct.mk_apply] using hu

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open IsDedekindDomain QuotShiftPfH

private theorem ordAt_mul_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [map_mul, WithZero.log_mul ((v.valuation F).ne_zero_iff.mpr hx)
    ((v.valuation F).ne_zero_iff.mpr hy)]
  ring

private theorem ordAt_zpow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (x : F) (k : ℤ) :
    ordAt v (x ^ k) = k * ordAt v x := by
  unfold ordAt
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

private theorem ordAt_prod_rationality {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) {ι : Type} (S : Finset ι)
    (f : ι → F) (hf : ∀ i, f i ≠ 0) : ordAt v (∏ i ∈ S, f i) = ∑ i ∈ S, ordAt v (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    unfold ordAt
    rw [map_one]
    rfl
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ordAt_mul_rationality v (hf a) (Finset.prod_ne_zero_iff.mpr fun i _ => hf i), ih]

theorem exists_length_quotient_span_le (hL : QuotLocalStatement) {R F : Type} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (Q : Type)
    [AddCommGroup Q] [Module (Rv F v) Q] (ρ : ℕ) (hb : Nonempty (Module.Basis (Fin ρ) (Rv F v) Q))
    (c : Fin ρ → (Q →ₗ[Rv F v] F)) (s : Fin ρ → ℝ) (β : ℝ) (th : Fin ρ → Q)
    (hc : ∀ i q, c i q ≠ 0 → -β ≤ (ordAt v (c i q) : ℝ) + s i)
    (hdet : (Matrix.of fun i j => c i (th j)).det ≠ 0) :
    ∃ n : ℕ, Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) = n ∧
      (n : ℝ) ≤ (ordAt v (Matrix.of fun i j => c i (th j)).det : ℝ) + ∑ i, s i + ρ * β := by
  classical

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Rv F v)
  set π : F := (ϖ : F) with hπdef
  have hπ0 : π ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hπ1 : ordAt v π = 1 := by
    have h1 := (addVal_eq_ord v ϖ hπ0).symm.trans (IsDiscreteValuationRing.addVal_uniformizer hϖ)
    have h2 : (ordAt v π).toNat = 1 := by exact_mod_cast h1
    have h3 := ord_nonneg v ϖ hπ0
    omega

  have hne : ∀ i, ∃ q, c i q ≠ 0 := by
    intro i
    by_contra h
    push_neg at h
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [h])

  have hex : ∀ i, ∃ μ : ℤ, (∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = μ) ∧
      ∀ q, c i q ≠ 0 → μ ≤ ordAt v (c i q) := by
    intro i
    obtain ⟨lb, ⟨q, hq, rfl⟩, hlb⟩ := Int.exists_least_of_bdd
      (P := fun z => ∃ q, c i q ≠ 0 ∧ ordAt v (c i q) = z)
      ⟨⌈-β - s i⌉, by
        rintro z ⟨q, hq, rfl⟩
        refine Int.ceil_le.mpr ?_
        have := hc i q hq
        linarith⟩
      (by obtain ⟨q, hq⟩ := hne i; exact ⟨_, q, hq, rfl⟩)
    exact ⟨_, ⟨q, hq, rfl⟩, fun q' hq' => hlb _ ⟨q', hq', rfl⟩⟩
  choose μ hμ1 hμ2 using hex
  have hμβ : ∀ i, -(μ i : ℝ) ≤ β + s i := by
    intro i
    obtain ⟨q, hq, hqμ⟩ := hμ1 i
    have := hc i q hq
    rw [hqμ] at this
    linarith

  have hmem : ∀ i q, π ^ (-μ i) * c i q ∈ Rv F v := by
    intro i q
    by_cases hq : c i q = 0
    · rw [hq, mul_zero]; exact (Rv F v).zero_mem
    · refine (mem_Rv_iff_ord v (mul_ne_zero (zpow_ne_zero _ hπ0) hq)).mpr ?_
      rw [ordAt_mul_rationality v (zpow_ne_zero _ hπ0) hq, ordAt_zpow, hπ1]
      have := hμ2 i q hq
      linarith
  let c' : Fin ρ → (Q →ₗ[Rv F v] Rv F v) := fun i =>
    { toFun := fun q => ⟨π ^ (-μ i) * c i q, hmem i q⟩
      map_add' := fun a b => by ext; simp [mul_add]
      map_smul' := fun r q => by
        ext
        simp only [LinearMap.map_smul, RingHom.id_apply, Subring.coe_mul, Subring.smul_def,
          smul_eq_mul]
        ring }
  have hmap : ((Matrix.of fun i j => c' i (th j)).map (Rv F v).subtype) =
      Matrix.diagonal (fun i => π ^ (-μ i)) * Matrix.of fun i j => c i (th j) := by
    ext i j
    simp [Matrix.diagonal_mul, c']
  have hdetF : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (∏ i, π ^ (-μ i)) * (Matrix.of fun i j => c i (th j)).det := by
    have := RingHom.map_det (Rv F v).subtype (Matrix.of fun i j => c' i (th j))
    simp only [RingHom.mapMatrix_apply] at this
    rw [show (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      (Rv F v).subtype (Matrix.of fun i j => c' i (th j)).det from rfl, this, hmap,
      Matrix.det_mul, Matrix.det_diagonal]
  have hP0 : (∏ i, π ^ (-μ i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ hπ0
  have hdF0 : (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) ≠ 0 := by
    rw [hdetF]; exact mul_ne_zero hP0 hdet
  have hdet' : (Matrix.of fun i j => c' i (th j)).det ≠ 0 := fun h => hdF0 (by rw [h]; rfl)
  have hlen := hL (Rv F v) Q ρ hb c' th hdet'
  rw [addVal_eq_ord v _ hdF0] at hlen
  have hord : ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) =
      ∑ i, -μ i + ordAt v (Matrix.of fun i j => c i (th j)).det := by
    rw [hdetF, ordAt_mul_rationality v hP0 hdet, ordAt_prod_rationality v _ _ fun i => zpow_ne_zero _ hπ0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ordAt_zpow, hπ1, mul_one]
  have hnn := ord_nonneg v _ hdF0
  have htop : Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hlen
  refine ⟨(Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat,
    (ENat.coe_toNat htop).symm, ?_⟩
  have hle : (Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F)).toNat := by
    rw [← ENat.coe_toNat htop] at hlen
    exact_mod_cast hlen
  have hle' : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℝ) ≤
      (ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) : ℝ) := by
    have : ((Module.length (Rv F v) (Q ⧸ Submodule.span (Rv F v) (Set.range th))).toNat : ℤ) ≤
        ordAt v (((Matrix.of fun i j => c' i (th j)).det : Rv F v) : F) := by omega
    exact_mod_cast this
  rw [hord] at hle'
  push_cast at hle'
  have hsum : ∑ i, (-(μ i : ℝ)) ≤ ∑ i, (β + s i) := Finset.sum_le_sum fun i _ => hμβ i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end
