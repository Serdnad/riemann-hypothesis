module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle024
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem mulVec_injective_map_of_linearIndependent {K L : Type} [Field K] [Field L] (σ : K →+* L) {d j : ℕ}
    (e : Fin j → Fin d → K) (he : LinearIndependent K e) :
    Function.Injective (((Matrix.of e)ᵀ).map σ).mulVec := by
  letI : Algebra K L := σ.toAlgebra
  rw [Matrix.mulVec_injective_iff]
  have h := (linearIndependent_algebraMap_comp_iff (S := L) (v := e)).2 he
  exact h

theorem gram_eq_conjTranspose_mul {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding)ᴴ * ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
  rw [Matrix.mul_apply]
  rfl

theorem gramR_ne_zero_and_gram_posDef : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d j : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsMetric H X → ∀ e : Fin j → Fin d → K, LinearIndependent K e → gramR H e ≠ 0 ∧ ∀ v, (gram X v e).PosDef := by
  intro K _ _ _ _ v0 hv0 d j H X hX e he
  have hpos : ∀ v, (gram X v e).PosDef := by
    intro v
    rw [gram_eq_conjTranspose_mul]
    refine Matrix.PosDef.conjTranspose_mul_self _ ?_
    have h1 : Function.Injective ((X v)⁻¹).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hX v).1))
    have h2 := mulVec_injective_map_of_linearIndependent v.embedding e he
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact h2 (h1 hxy)
  refine ⟨?_, hpos⟩
  have key : v0.embedding (gramR H e) = (gram X v0 e).det := by
    unfold gramR
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    set σ := v0.embedding
    have hM : H.map σ = ((X v0)⁻¹).conjTranspose * (X v0)⁻¹ := (hX v0).2.symm
    ext a b
    rw [Matrix.map_apply, Matrix.of_apply, RingHom.map_dotProduct]
    have hmv : (⇑σ ∘ (H *ᵥ e b)) = H.map σ *ᵥ (⇑σ ∘ e b) :=
      funext fun i => RingHom.map_mulVec σ _ _ i
    have hs : (⇑σ ∘ star (e a)) = star (⇑σ ∘ e a) := by
      funext i
      simp only [Function.comp_apply, Pi.star_apply]
      rw [← starRingEnd_apply]
      exact hv0 (e a i)
    rw [hmv, hs, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
    rfl
  intro h0
  rw [h0, map_zero] at key
  exact (hpos v0).det_pos.ne key

end GlobalTheory.TestLat
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.GramLoc

theorem exists_common_denom {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (p : Ideal R) [p.IsPrime] (L M : Submodule R W) (hM : M.FG) (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p L) :
    ∃ s : R, s ∉ p ∧ ∀ y ∈ M, s • y ∈ L := by
  obtain ⟨T, rfl⟩ := hM
  have h1 : ∀ y : T, ∃ s : R, s ∈ p.primeCompl ∧ s • (y : W) ∈ L := fun y =>
    h (Submodule.subset_span y.2)
  choose f hf hf' using h1
  refine ⟨∏ y, f y, Submonoid.prod_mem p.primeCompl (fun y _ => hf y), ?_⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    classical
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : T)), mul_smul]
    exact L.smul_mem _ (hf' ⟨x, hx⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L.smul_mem _ hx

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def locRing (w : HeightOneSpectrum (𝓞 K)) : Subring K where
  carrier := {a | ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * a = r}
  mul_mem' := by
    rintro a b ⟨s, hs, r, hr⟩ ⟨t, ht, u, hu⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, r * u, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add (f := _), map_neg] at *
    rw [← hr, ← hu]; ring
  one_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, 1, by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs, r, hr⟩ ⟨t, ht, u, hu⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, t * r + s * u, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add (f := _), map_neg] at *
    rw [← hr, ← hu]; ring
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, 0, by simp⟩
  neg_mem' := by
    rintro a ⟨s, hs, r, hr⟩
    refine ⟨s, hs, -r, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add (f := _), map_neg] at *
    rw [← hr]; ring

theorem det_mem_subring (S : Subring K) (P : Matrix (Fin n) (Fin n) K) (h : ∀ a b, P a b ∈ S) :
    P.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem col_mem_colLat (B : GL (Fin n) K) (j : Fin n) :
    (fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ colLat B :=
  Submodule.subset_span ⟨j, rfl⟩

theorem coord_of_mem_colLat (B : GL (Fin n) K) (x : Fin n → K) (hx : x ∈ colLat B) (j : Fin n) :
    ∃ r : 𝓞 K, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j = r := by
  unfold colLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have h : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.inv_mul B
    have h2 := congrFun (congrFun h j) i
    refine ⟨if j = i then 1 else 0, ?_⟩
    change (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) j i = _
    rw [h2, Matrix.one_apply]
    split_ifs <;> simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨u, hu⟩ := hy
    exact ⟨r + u, by rw [Matrix.mulVec_add, Pi.add_apply, hr, hu]; simp⟩
  | smul a x _ hx =>
    obtain ⟨r, hr⟩ := hx
    refine ⟨a * r, ?_⟩
    rw [Matrix.mulVec_smul, Pi.smul_apply, hr, Algebra.smul_def]
    simp

variable [StarRing K]

theorem vw_nonneg_of_mem (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ∈ locRing w) :
    0 ≤ vw w a := by
  obtain ⟨s, hs, r, hr⟩ := ha
  by_cases h0 : a = 0
  · rw [h0, ValuationRepresentative.vw_zero]
  have hs0 : (s : K) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have h1 := ValuationRepresentative.vw_mul w _ _ hs0 h0
  have h2 : vw w (s : K) = 0 := idxChange_cnt_unit (K := K) w hs
  have h3 := ValuationRepresentative.vw_int_nonneg w r
  rw [hr, h2] at h1
  omega

theorem cO_notMem (w : HeightOneSpectrum (𝓞 K)) (t : 𝓞 K) (ht : t ∉ (conjPl w).asIdeal) :
    cO K t ∉ w.asIdeal := by
  intro h
  apply ht
  have := Ideal.mem_map_of_mem (cO K) h
  rwa [ValuationRepresentative.cO_cO] at this

theorem mem_localization_of_mem {w : HeightOneSpectrum (𝓞 K)} (M : Submodule (𝓞 K) (Fin n → K)) :
    M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := fun x hx =>
  ⟨1, one_mem _, by simpa using hx⟩

theorem gram_mem (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : hdualFr G M = M) (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (hB : IsBasisAt (conjPl w) M B) (hB' : IsBasisAt w M B') (a b : Fin n) :
    ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) a b ∈ locRing w := by
  unfold IsBasisAt at hB hB'
  have h1 := mem_localization_of_mem (w := conjPl w) _ (col_mem_colLat B a)
  have h2 := mem_localization_of_mem (w := w) _ (col_mem_colLat B' b)
  rw [← hB] at h1
  rw [← hB'] at h2
  obtain ⟨t, ht, h1⟩ := h1
  obtain ⟨u, hu, h2⟩ := h2
  rw [← hM] at h2
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h2 _ h1)
  refine ⟨cO K t * u, fun h => (w.isPrime.mem_or_mem h).elim (cO_notMem w t ht) hu, r, ?_⟩
  change _ = algebraMap (𝓞 K) K r
  rw [hr, Matrix.mul_assoc]
  have hc : ((cO K t * u : 𝓞 K) : K) = star (t : K) * (u : K) := by
    rw [← ValuationRepresentative.cO_apply]; exact map_mul (algebraMap (𝓞 K) K) _ _
  rw [hc]
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply,
    Algebra.smul_def, Matrix.conjTranspose_apply, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change star (t : K) * (u : K) * _ = star (t : K) * _ * (_ * ((u : K) * _))
  ring

theorem gram_inv_mem (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) (hfg : M.FG)
    (hM : hdualFr G M = M) (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (hB : IsBasisAt (conjPl w) M B) (hB' : IsBasisAt w M B') (a b : Fin n) :
    (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (G⁻¹ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ)) a b ∈ locRing w := by
  unfold IsBasisAt at hB hB'
  obtain ⟨t, ht, h1⟩ := exists_common_denom (conjPl w).asIdeal (colLat B) M hfg
    (hB ▸ mem_localization_of_mem M)
  set C : Matrix (Fin n) (Fin n) K := ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hC
  set x : Fin n → K := fun i => (G⁻¹ * Cᴴ) i b with hx
  have hGx : G *ᵥ x = fun i => star (C b i) := by
    funext i
    change (G * (G⁻¹ * Cᴴ)) i b = _
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hG, Matrix.conjTranspose_apply]
  have hxM : cO K t • x ∈ hdualFr G M := by
    intro y hy
    obtain ⟨r, hr⟩ := coord_of_mem_colLat B _ (h1 y hy) b
    refine Submodule.mem_one.2 ⟨cO K r, ?_⟩
    change ((cO K r : 𝓞 K) : K) = _
    rw [ValuationRepresentative.cO_apply, ← hr, Matrix.mulVec_smul, Matrix.mulVec_smul, hGx]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply,
      Algebra.smul_def, star_mul', Finset.mul_sum, star_sum, ← hC]
    refine Finset.sum_congr rfl fun i _ => ?_
    change star (t : K) * _ = _ * (star (t : K) * _)
    ring
  rw [hM] at hxM
  have h3 := mem_localization_of_mem (w := w) M hxM
  rw [hB'] at h3
  obtain ⟨u, hu, h3⟩ := h3
  obtain ⟨r, hr⟩ := coord_of_mem_colLat B' _ h3 a
  refine ⟨u * cO K t, fun h => (w.isPrime.mem_or_mem h).elim hu (cO_notMem w t ht), r, ?_⟩
  rw [← hr, ← mul_smul, Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  rfl

theorem gram_locally_unimodular : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)), Gᴴ = G → IsUnit G.det → IsSelfDualK G M → ∀ (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K), IsBasisAt (conjPl w) M B → IsBasisAt w M B' → (∀ a b, 0 ≤ vw w (((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) a b)) ∧ vw w ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)).det = 0 := by
  intro K _ _ _ n G M _ hG hM w B B' hB hB'
  have hfg : M.FG := hM.1.fg
  have h1 := gram_mem G M hM.2 w B B' hB hB'
  have h2 := gram_inv_mem G M hG hfg hM.2 w B B' hB hB'
  refine ⟨fun a b => vw_nonneg_of_mem w _ (h1 a b), ?_⟩
  have d1 := vw_nonneg_of_mem w _ (det_mem_subring _ _ h1)
  have d2 := vw_nonneg_of_mem w _ (det_mem_subring _ _ h2)
  have e : ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) *
      (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (G⁻¹ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ)) = 1 := by
    have e1 : (B' : Matrix (Fin n) (Fin n) K) * ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.mul_inv B'
    have e2 : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.inv_mul B
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B' : Matrix (Fin n) (Fin n) K), e1, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hG, ← Matrix.conjTranspose_mul, e2,
      Matrix.conjTranspose_one]
  have e' := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_one] at e'
  have e3 := ValuationRepresentative.vw_mul w _ _ (left_ne_zero_of_mul_eq_one e') (right_ne_zero_of_mul_eq_one e')
  rw [e', ValuationRepresentative.vw_one] at e3
  omega

end GlobalTheory.GramLoc
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType
open GlobalTheory.DepthZeroJac GlobalTheory.IwahoriInj GlobalTheory.StepData

theorem unipRad_points_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    unipRad k (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) = unipB k (Fin n) := by
  ext g
  rw [mem_unipB, mem_unipRad, mem_parab]
  simp only [blk, Equiv.sigmaUnique_symm_apply, Equiv.sigmaUnique_apply]
  refine and_congr Iff.rfl ⟨fun h i => (h i 0 0).trans (by simp), fun h a i j => ?_⟩
  rw [h a, Subsingleton.elim i j]
  simp

theorem eq_zero_of_fixed_KO_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v ∈ twKer π (unipB k (Fin n)) 1, (∀ g ∈ KO k (Fin n), π g v = v) → v = 0 := by
  intro k _ _ _ _ n V _ _ π hπ v h1 hfix
  rw [← unipRad_points_eq] at h1
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_deep (k := k) 1
  obtain ⟨M, hM⟩ := (eventually_mem_twKer (hc := hc0) hc1 hc2 h1).exists
  refine claim_of_antitone hc1 hc2 hπ _ _ rfl (antitone_expo M) v ?_ hM
  exact mem_fixed.2 fun g hg => hfix g ((sup_le KOne_le_KO inf_le_right) hg)

end GlobalTheory.PsType
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V), (∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) → ∀ x ∈ N, x ∈ (⨆ μ : Ix p q → ℚ, wtSub act μ) → x ∈ ⨆ μ : Ix p q → ℚ, N ⊓ wtSub act μ := by
  first | exact @GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub | exact GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub | (intros; apply GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolDS

variable {p q : ℕ}

instance t2Space_cuspAdeles (T : GrpData p q) : T2Space T.G := T.emb.t2Space

instance instSecondCountable (T : GrpData p q) : SecondCountableTopology T.G := by
  haveI : SecondCountableTopology (Mat p q) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))
  haveI : SecondCountableTopology (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  exact T.emb.secondCountableTopology

instance instLocallyCompact (T : GrpData p q) : LocallyCompactSpace T.G := by
  haveI : LocallyCompactSpace (Mat p q) := inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))
  exact (GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).locallyCompactSpace

end GlobalTheory.HolDS

end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GradedCentralCircle

open GlobalTheory.RealPar

variable {p q : ℕ}

theorem flow_eq {T : GrpData p q} (σ : URep T) {X : Mat p q} (hX : X ∈ upq p q) {w : σ.H} {c : ℂ}
    (h0 : HasDerivAt (fun t : ℝ => σ.π (T.expt (t • X)) w) (c • w) 0) :
    σ.π (T.expt X) w = Complex.exp c • w := by
  set f : ℝ → σ.H := fun t => σ.π (T.expt (t • X)) w with hf
  have hd : ∀ t, HasDerivAt f (c • f t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) (c • w) t := by
      have := HasDerivAt.comp_sub_const t t (f := f) (f' := c • w) (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((σ.π (T.expt (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    convert (preTransparency := .reducible) h2 using 1
    · funext s
      simp only [hf, Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    · simp [hf]
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    convert h1.fun_smul (hd t) using 1
    rw [smul_smul, ← add_smul]; simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, ContinuousLinearMap.one_apply] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem exp_injective (c : ℂ) : Function.Injective fun m : ℕ => Complex.exp (Complex.I * (c + m)) := by
  intro m n h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h1 : ((m : ℝ) : ℂ) - (n : ℝ) = ((k : ℝ) * 2 * Real.pi : ℝ) := by
    push_cast
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination hk
  have h2 : (m : ℝ) - n = (k : ℝ) * 2 * Real.pi := by exact_mod_cast h1
  by_cases hk0 : k = 0
  · subst hk0
    have : (m : ℝ) = n := by simpa [sub_eq_zero] using h2
    exact_mod_cast this
  · exfalso
    have hi : Irrational (((k * 2 : ℤ) : ℝ) * Real.pi) :=
      irrational_pi.intCast_mul (by omega)
    have : ((k * 2 : ℤ) : ℝ) * Real.pi = ((m - n : ℤ) : ℝ) := by push_cast; linarith
    rw [this] at hi
    exact Int.not_irrational _ hi

theorem exists_central_eigen : ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (c : ℚ), (∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = ((c : ℂ) + m) • x) → ∃ k ∈ T.Kset, ∃ lam : ℕ → ℂ, Function.Injective lam ∧ ∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x := by
  intro p q T σ M j hj N c hN
  set θ : Ix p q → ℝ := Sum.elim (fun _ => 1) (fun _ => 0) with hθ
  have hX := TorusWt.torX_mem θ
  have hK : IsKC (TorusWt.torX θ) := by
    intro a b hab
    have : a ≠ b := by
      rintro rfl
      cases a <;> simp [sameBlock] at hab
    simp [TorusWt.torX, this]
  have hk := KStabLie.expt_mem T hX hK 1
  rw [one_smul] at hk
  refine ⟨_, hk, _, exp_injective (c : ℂ), fun m x hx => ?_⟩
  apply flow_eq σ hX
  have h0 := hj _ hX x
  have h1 : M.act (TorusWt.torX θ) x = (Complex.I * ((c : ℂ) + m)) • x := by

    rw [TorusWt.torX_eq_sum, map_sum, LinearMap.sum_apply, Fintype.sum_sum_type, mul_smul, ← hN m x hx,
    Finset.smul_sum]
    simp [hθ]
  rw [h1, map_smul] at h0
  exact h0

end GlobalTheory.GradedCentralCircle
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.global_positivity_ineq_multiplicative_coeff : ∀ (M : ℕ) (b ω : ℕ → ℂ) (s C : ℝ), 0 < s → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ X : ℕ, Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  first | exact @GlobalTheory.EisM.global_positivity_ineq | exact GlobalTheory.EisM.global_positivity_ineq | (intros; apply GlobalTheory.EisM.global_positivity_ineq <;> assumption)
end
