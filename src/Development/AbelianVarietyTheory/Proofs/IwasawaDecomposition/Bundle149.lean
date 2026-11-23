module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle110
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocIntegral

open Polynomial
open scoped WithZero

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem exists_valued_eq (γ : ℤᵐ⁰) : ∃ c : v.adicCompletion K, Valued.v c = γ := by
  obtain ⟨x, hx⟩ := v.valuation_surjective K γ
  exact ⟨algebraMap K _ x, (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans hx⟩

theorem valued_coeff_minpoly_le_one (e : ℕ) (he : 0 < e)
    (f : v.adicCompletion K →+* v'.adicCompletion L)
    (hfv : ∀ y, Valued.v (f y) = Valued.v y ^ e) :
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ x : v'.adicCompletion L, Valued.v x ≤ 1 →
      ∀ n, Valued.v ((minpoly (v.adicCompletion K) x).coeff n) ≤ 1 := by
  letI := f.toAlgebra
  intro hfd x hx n
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ ℤᵐ⁰
  haveI : IsUltrametricDist (v.adicCompletion K) :=
    inferInstanceAs (@IsUltrametricDist (v.adicCompletion K)
      (Valued.toNormedField (v.adicCompletion K) ℤᵐ⁰).toDist)
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  choose c hc using (exists_valued_eq (v := v) : ∀ γ : ℤᵐ⁰, ∃ c : v.adicCompletion K, Valued.v c = γ)
  have hmono : ∀ a b : v.adicCompletion K, Valued.v a ≤ Valued.v b → ‖a‖ ≤ ‖b‖ :=
    fun a b h => Valued.toNormedField.norm_le_iff.2 h
  have hnorm : ∀ a b : v.adicCompletion K, Valued.v a = Valued.v b → ‖a‖ = ‖b‖ :=
    fun a b h => le_antisymm (hmono a b h.le) (hmono b a h.ge)
  have he' : (e : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast he.ne')
  let ρ : v'.adicCompletion L → ℝ := fun z => ‖c (Valued.v z)‖ ^ ((e : ℝ)⁻¹)
  have ρ_nonneg : ∀ z, 0 ≤ ρ z := fun z => Real.rpow_nonneg (norm_nonneg _) _
  have ρ_mul : ∀ a b, ρ (a * b) = ρ a * ρ b := by
    intro a b
    simp only [ρ]
    rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← norm_mul]
    congr 1
    apply hnorm
    rw [hc, Valuation.map_mul, Valuation.map_mul, hc, hc]
  have ρ_le : ∀ a b, Valued.v a ≤ Valued.v b → ρ a ≤ ρ b := by
    intro a b h
    exact Real.rpow_le_rpow (norm_nonneg _) (hmono _ _ (by rw [hc, hc]; exact h))
      (inv_nonneg.2 (Nat.cast_nonneg _))
  have ρ_zero : ρ 0 = 0 := by
    simp only [ρ]
    have : c (Valued.v (0 : v'.adicCompletion L)) = 0 := by
      rw [← Valuation.zero_iff Valued.v, hc, Valuation.map_zero]
    rw [this, norm_zero, Real.zero_rpow he']
  have ρ_eq_zero : ∀ z, ρ z = 0 → z = 0 := by
    intro z hz
    simp only [ρ] at hz
    rw [Real.rpow_eq_zero (norm_nonneg _) he', norm_eq_zero] at hz
    have := hc (Valued.v z)
    rw [hz, Valuation.map_zero] at this
    exact (Valuation.zero_iff _).1 this.symm
  have ρ_f : ∀ a, ρ (f a) = ‖a‖ := by
    intro a
    simp only [ρ]
    rw [hnorm _ (a ^ e) (by rw [hc, hfv, Valuation.map_pow]), norm_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) he.ne']
  have ρ_one : ρ 1 = 1 := by
    have := ρ_f 1
    rwa [map_one, norm_one] at this
  let N : AlgebraNorm (v.adicCompletion K) (v'.adicCompletion L) :=
    { toFun := ρ
      map_zero' := ρ_zero
      add_le' := fun a b => by
        rcases le_total (Valued.v a) (Valued.v b) with h | h
        · have := ρ_le (a + b) b ((Valuation.map_add _ a b).trans (max_le h le_rfl))
          linarith [ρ_nonneg a]
        · have := ρ_le (a + b) a ((Valuation.map_add _ a b).trans (max_le le_rfl h))
          linarith [ρ_nonneg b]
      neg' := fun a => by simp only [ρ, Valuation.map_neg]
      mul_le' := fun a b => (ρ_mul a b).le
      eq_zero_of_map_eq_zero' := ρ_eq_zero
      smul' := fun a z => by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, ρ_mul, ρ_f] }
  have hN : ∀ z, N z = ρ z := fun _ => rfl
  have hpm : IsPowMul N := by
    intro a k hk
    clear hk
    rw [hN, hN]
    induction k with
    | zero => simp [ρ_one]
    | succ k ih => rw [pow_succ, ρ_mul, ih, pow_succ]
  have hu := spectralNorm_unique (K := v.adicCompletion K) (L := v'.adicCompletion L) hpm
  have hsx : spectralNorm (v.adicCompletion K) (v'.adicCompletion L) x ≤ 1 := by
    rw [← spectralAlgNorm_def, ← hu, hN, ← ρ_one]
    exact ρ_le x 1 (by rw [Valuation.map_one]; exact hx)
  have hxi : IsIntegral (v.adicCompletion K) x := Algebra.IsIntegral.isIntegral x
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hxi)] at hsx
  exact Valued.toNormedField.norm_le_one_iff.1 (hsx n)

end GlobalTheory.LocIntegral

namespace GlobalTheory.LocIntegral

open Polynomial

theorem isIntegral_iff_isIntegral_map : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ)
    (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e →
    (∀ y, Valued.v (f y) = Valued.v y ^ e) →
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ b₀ : Kbar v ≃+* Kbar v',
      (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) =
        algebraMap (v'.adicCompletion L) (Kbar v') (f x)) →
      ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔
        IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  intro K L _ _ _ _ v v' e f he hfv
  letI := f.toAlgebra
  intro hfd b₀ hb y
  have hle : ∀ a ∈ v.adicCompletionIntegers K, f a ∈ v'.adicCompletionIntegers L := by
    intro a ha
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hfv]
    exact pow_le_one₀ zero_le' ha
  let g : v.adicCompletionIntegers K →+* v'.adicCompletionIntegers L :=
    f.restrict (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) hle
  have hg : ∀ a, ((g a : v'.adicCompletionIntegers L) : v'.adicCompletion L) = f a := fun _ => rfl
  have hcomp : (algebraMap (v'.adicCompletionIntegers L) (Kbar v')).comp g =
      b₀.toRingHom.comp (algebraMap (v.adicCompletionIntegers K) (Kbar v)) := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v),
      IsScalarTower.algebraMap_apply (v'.adicCompletionIntegers L) (v'.adicCompletion L) (Kbar v'),
      hb]
    rfl
  constructor
  · intro hy
    exact IsIntegral.map_of_comp_eq g b₀.toRingHom hcomp hy
  · intro hy
    letI alg1 : Algebra (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := g.toAlgebra
    letI alg2 : Algebra (v'.adicCompletionIntegers L) (Kbar v) :=
      (b₀.symm.toRingHom.comp (algebraMap (v'.adicCompletionIntegers L) (Kbar v'))).toAlgebra
    haveI : IsScalarTower (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) (Kbar v) := by
      refine IsScalarTower.of_algebraMap_eq fun a => ?_
      have h := congrArg (fun φ => b₀.symm (φ a)) hcomp
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h
      rw [← h]
      rfl
    haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := by
      constructor
      intro a
      have ha : Valued.v (a : v'.adicCompletion L) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2
      have hc := valued_coeff_minpoly_le_one e he f hfv hfd (a : v'.adicCompletion L) ha
      have hai : IsIntegral (v.adicCompletion K) (a : v'.adicCompletion L) :=
        Algebra.IsIntegral.isIntegral _
      have hl : minpoly (v.adicCompletion K) (a : v'.adicCompletion L) ∈
          Polynomial.lifts (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hc n)⟩, rfl⟩
      obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hai)
      refine ⟨q, hm, ?_⟩
      apply Subtype.ext
      have e1 := Polynomial.hom_eval₂ q (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L))
        (v'.adicCompletionIntegers L).subtype a
      have e2 : ((v'.adicCompletionIntegers L).subtype).comp
          (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L)) =
          (algebraMap (v.adicCompletion K) (v'.adicCompletion L)).comp
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        ext; rfl
      rw [e2, ← Polynomial.eval₂_map, hq] at e1
      exact e1.trans (minpoly.aeval (v.adicCompletion K) (a : v'.adicCompletion L))
    have h1 : IsIntegral (v'.adicCompletionIntegers L) y := by
      have := IsIntegral.map_of_comp_eq (RingHom.id (v'.adicCompletionIntegers L)) b₀.symm.toRingHom
        (by ext; rfl) hy
      simpa using this
    exact isIntegral_trans y h1

end GlobalTheory.LocIntegral
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Pointwise

namespace GlobalTheory.LocEmbDec

theorem exists_dec_of_isLocEmb : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (ι ι₂ : Ω →ₐ[K] Kbar v), IsLocEmb A v ι → IsLocEmb A v ι₂ → ∃ σ ∈ Dec (F := K) A, ∀ z, ι₂ z = ι (σ z) := by
  intro K Ω _ _ _ _ _ A v ι ι₂ hι hι₂
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  set e : Ω ≃ₐ[K] ι.fieldRange := AlgEquiv.ofInjectiveField ι with he
  haveI : Normal K ι.fieldRange := Normal.of_algEquiv e
  have hr : (ι₂.comp e.symm.toAlgHom).fieldRange = ι.fieldRange :=
    AlgHom.fieldRange_of_normal _
  have hmem : ∀ z, ι₂ z ∈ ι.fieldRange := fun z => by
    rw [← hr]; exact ⟨e z, by simp⟩
  let f : Ω →ₐ[K] ι.fieldRange := ι₂.codRestrict ι.fieldRange.toSubalgebra hmem
  let σ0 : Ω →ₐ[K] Ω := e.symm.toAlgHom.comp f
  let σ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective σ0 (Algebra.IsAlgebraic.algHom_bijective σ0)
  have key : ∀ z, ι (σ z) = ι₂ z := fun z => by
    have h1 : ((e (σ z) : ι.fieldRange) : Kbar v) = ι (σ z) := rfl
    rw [← h1]
    change ((e (e.symm (f z)) : ι.fieldRange) : Kbar v) = ι₂ z
    rw [AlgEquiv.apply_symm_apply]; rfl
  refine ⟨σ, ?_, fun z => (key z).symm⟩
  show σ • A = A
  have hA : ∀ x, σ x ∈ A ↔ x ∈ A := fun x => by rw [hι, key, ← hι₂]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hA]
  show σ (σ⁻¹ y) ∈ A ↔ y ∈ A
  rw [← AlgEquiv.mul_apply, mul_inv_cancel]
  rfl

end GlobalTheory.LocEmbDec
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocEmbExist

variable {E : Type} [Field E] [NumberField E]

theorem isIntegral_or_isIntegral_inv (w : HeightOneSpectrum (𝓞 E)) (x : GlobalTheory.LocDict.Kbar w) :
    IsIntegral (w.adicCompletionIntegers E) x ∨ IsIntegral (w.adicCompletionIntegers E) x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inl isIntegral_zero
  let K := w.adicCompletion E
  let L : IntermediateField K (GlobalTheory.LocDict.Kbar w) := IntermediateField.adjoin K {x}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hy0 : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  let f : L →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w := L.val.restrictScalars _
  have hf : Function.Injective f := L.val.injective
  have key : ∀ z : L, IsIntegral (w.adicCompletionIntegers E) (z : GlobalTheory.LocDict.Kbar w) ↔
      Valued.v (Algebra.norm K z) ≤ 1 := fun z => by
    rw [← GlobalTheory.CNorm.isIntegral_iff_valued_norm_le_one E w L z]
    exact isIntegral_algHom_iff f hf
  have hyx : ((y⁻¹ : L) : GlobalTheory.LocDict.Kbar w) = x⁻¹ := by simp [y]
  have hmul : Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  rcases le_total (Valued.v (Algebra.norm K y)) 1 with h | h
  · exact Or.inl ((key y).2 h)
  · right
    rw [← hyx]
    refine (key _).2 ?_
    calc Valued.v (Algebra.norm K y⁻¹) = 1 * Valued.v (Algebra.norm K y⁻¹) := (one_mul _).symm
      _ ≤ Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) := mul_le_mul' h le_rfl
      _ = 1 := hmul

def intValRing (w : HeightOneSpectrum (𝓞 E)) : ValuationSubring (GlobalTheory.LocDict.Kbar w) where
  toSubring := (integralClosure (w.adicCompletionIntegers E) (GlobalTheory.LocDict.Kbar w)).toSubring
  mem_or_inv_mem' x := isIntegral_or_isIntegral_inv w x

theorem isIntegral_algebraMap_iff (w : HeightOneSpectrum (𝓞 E)) (e : E) :
    IsIntegral (w.adicCompletionIntegers E) (algebraMap E (GlobalTheory.LocDict.Kbar w) e) ↔
      w.valuation E e ≤ 1 := by
  let K := w.adicCompletion E
  have h1 : algebraMap E (GlobalTheory.LocDict.Kbar w) e = algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) :=
    IsScalarTower.algebraMap_apply E K _ e
  let f : K →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w :=
    (IsScalarTower.toAlgHom K K (GlobalTheory.LocDict.Kbar w)).restrictScalars _
  rw [h1, show algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) = f (algebraMap E K e) from rfl,
    isIntegral_algHom_iff f f.toRingHom.injective, IsIntegrallyClosed.isIntegral_iff (K := K)]
  have hv : Valued.v (algebraMap E K e) = w.valuation E e :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w e
  constructor
  · rintro ⟨y, hy⟩
    have h := y.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    change Valued.v (y : K) ≤ 1 at h
    rw [show (y : K) = algebraMap E K e from hy, hv] at h
    exact h
  · intro h
    refine ⟨⟨algebraMap E K e, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv]
    exact h

theorem valuation_lt_one_iff_of_mem_iff {Ω : Type} [Field Ω] [Algebra E Ω] (B : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (hB : ∀ e : E, algebraMap E Ω e ∈ B ↔ w.valuation E e ≤ 1) (e : E) :
    B.valuation (algebraMap E Ω e) < 1 ↔ w.valuation E e < 1 := by
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have ha : algebraMap E Ω e ≠ 0 := (map_ne_zero _).2 he
  have h1 : B.valuation (algebraMap E Ω e) < 1 ↔ ¬ B.valuation (algebraMap E Ω e⁻¹) ≤ 1 := by
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha)), not_le]
  have h2 : w.valuation E e < 1 ↔ ¬ w.valuation E e⁻¹ ≤ 1 := by
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 he)), not_le]
  rw [h1, h2, ValuationSubring.valuation_le_one_iff, hB]

end GlobalTheory.LocEmbExist

namespace GlobalTheory.LocDict

theorem exists_isLocEmb : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ ι : Ω →ₐ[E] Kbar w, IsLocEmb A w ι := by
  intro E Ω _ _ _ _ _ A w h
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let ι₀ : Ω →ₐ[E] Kbar w := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let A₀ : ValuationSubring Ω := (GlobalTheory.LocEmbExist.intValRing w).comap ι₀.toRingHom
  have hA₀ : ∀ z, z ∈ A₀ ↔ IsIntegral (w.adicCompletionIntegers E) (ι₀ z) := fun _ => Iff.rfl
  have hE : ∀ e : E, algebraMap E Ω e ∈ A₀ ↔ w.valuation E e ≤ 1 := fun e => by
    rw [hA₀, ι₀.commutes]
    exact GlobalTheory.LocEmbExist.isIntegral_algebraMap_iff w e
  have hP : IsPlaceOver A₀ w := fun x => by
    rw [GlobalTheory.LocEmbExist.valuation_lt_one_iff_of_mem_iff A₀ w hE]
    exact w.valuation_lt_one_iff_mem (K := E) x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hP h
  refine ⟨ι₀.comp (σ.symm : Ω →ₐ[E] Ω), fun z => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA₀]
  rfl

end GlobalTheory.LocDict
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.autRep_isotypic_splitPlace_localComponent : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : σ.V →ₗ[ℂ] (GAf L n → π.W)),
    Function.Injective T → (∀ a, T a ∈ π.S) → GlobalTheory.HeckeFrob.IsLocMap s σ i T →
    ∀ g ∈ π.S, g ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 := by
  first | exact @GlobalTheory.HeckeFrob.mem_iSup_range_locMap | exact GlobalTheory.HeckeFrob.mem_iSup_range_locMap | (intros; apply GlobalTheory.HeckeFrob.mem_iSup_range_locMap <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem exists_residueDegree_pos_of_mem_range (W Z : Scheme.{0}) (g : W ⟶ Z) [QuasiCompact g]
    [LocallyOfFiniteType g] (z : Z) (hz : z ∈ Set.range g) :
    ∃ w, g w = z ∧ 0 < g.residueDegree w := by
  obtain ⟨w₀, hw₀⟩ := hz
  let F := g.fiber z
  have hne : (Set.univ : Set F).Nonempty := ⟨(g.fiberHomeo z).symm ⟨w₀, hw₀⟩, trivial⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton isClosed_univ hne
  have h₁ : LocallyOfFiniteType (F.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h₂ : LocallyOfFiniteType (g.fiberToSpecResidueField z) := by
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let h : F ⟶ Z := g.fiberι z ≫ g
  have e : h x = z := by
    have := (g.range_fiberι z).le ⟨x, rfl⟩
    simpa [h] using this
  let β : Z.residueField z ⟶ F.residueField x := (Z.residueFieldCongr e.symm).hom ≫ h.residueFieldMap x
  have hβ : Spec.map β = F.fromSpecResidueField x ≫ g.fiberToSpecResidueField z := by
    rw [← cancel_mono (Z.fromSpecResidueField z)]
    simp only [β, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp [h, Scheme.Hom.fiber_fac]
  have hβft : β.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map β) := hβ ▸ inferInstance
    exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) |>.mp this
  have hβf : β.hom.Finite := by
    letI := β.hom.toAlgebra
    haveI : Algebra.FiniteType (Z.residueField z) (F.residueField x) := hβft
    exact finite_of_finite_type_of_isJacobsonRing _ _
  have hhf : (h.residueFieldMap x).hom.Finite := by
    have : h.residueFieldMap x = (Z.residueFieldCongr e.symm).inv ≫ β := by simp [β]
    rw [this, CommRingCat.hom_comp]
    exact hβf.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Z.residueFieldCongr e.symm).inv).2)
  refine ⟨g.fiberι z x, e, ?_⟩
  rw [show h.residueFieldMap x = g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x
    from Scheme.residueFieldMap_comp _ _ _] at hhf
  letI := (g.residueFieldMap (g.fiberι z x)).hom.toAlgebra
  letI := ((g.fiberι z).residueFieldMap x).hom.toAlgebra
  letI := (g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x))
      (F.residueField x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (F.residueField x) := hhf
  let φ := IsScalarTower.toAlgHom (Z.residueField (g (g.fiberι z x)))
    (W.residueField (g.fiberι z x)) (F.residueField x)
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x)) :=
    Module.Finite.of_injective φ.toLinearMap φ.toRingHom.injective
  exact Module.finrank_pos

end GlobalTheory
end
