module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsBaseTwoWords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle291
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle676
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle681
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
import Mathlib.Algebra.Lie.OfAssociative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecondKindMatrixMooreDetNeZero
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.RayRootOfUnity

theorem norm_pos_of_pos_real {K : Type} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    (h : ∀ τ : K →+* ℝ, 0 < τ x) : 0 < Algebra.norm ℚ x := by
  classical
  let c : (K →ₐ[ℚ] ℂ) → (K →ₐ[ℚ] ℂ) := fun φ =>
    { (starRingEnd ℂ).comp φ.toRingHom with
      commutes' := fun a => by
        change starRingEnd ℂ (φ (algebraMap ℚ K a)) = _
        rw [φ.commutes]; simp }
  have hc : ∀ φ e, c φ e = starRingEnd ℂ (φ e) := fun _ _ => rfl
  have hφ : ∀ φ : K →ₐ[ℚ] ℂ, φ x ≠ 0 := fun φ => (map_ne_zero _).2 hx
  have hn : ∀ φ : K →ₐ[ℚ] ℂ, (‖φ x‖ : ℂ) ≠ 0 := fun φ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hφ φ))
  have h1 : ∏ φ : K →ₐ[ℚ] ℂ, (φ x / (‖φ x‖ : ℂ)) = 1 := by
    refine Finset.prod_involution (fun φ _ => c φ) (fun φ _ => ?_) (fun φ _ hne he => ?_)
      (fun _ _ => Finset.mem_univ _) (fun φ _ => ?_)
    · rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have := hn φ
      push_cast
      field_simp
    · apply hne
      have hr : ∀ e, ((φ e).re : ℂ) = φ e := fun e =>
        Complex.conj_eq_iff_re.1 (by rw [← hc, he])
      let τ : K →+* ℝ :=
        { toFun := fun e => (φ e).re, map_one' := by simp, map_zero' := by simp,
          map_add' := by simp, map_mul' := fun a b => by
            apply Complex.ofReal_injective
            rw [Complex.ofReal_mul, hr, hr, hr, map_mul] }
      have hτ : 0 < (φ x).re := h τ
      rw [← hr x, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
      exact div_self (by exact_mod_cast hτ.ne')
    · ext e; simp [hc]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun φ _ => hn φ),
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x] at h1
  have h2 : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ φ : K →ₐ[ℚ] ℂ, ‖φ x‖ := by
    apply Complex.ofReal_injective
    push_cast
    rw [← h1]
    rfl
  have : (0 : ℝ) < ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    rw [h2]; exact Finset.prod_pos fun φ _ => norm_pos_iff.2 (hφ φ)
  exact_mod_cast this

theorem absNorm_modEq_one {K : Type} [Field K] [NumberField K] {𝔮 : Ideal (𝓞 K)} {p : ℕ}
    (hq : 𝔮 ≤ Ideal.span {(p : 𝓞 K)}) {I : Ideal (𝓞 K)} {α β : 𝓞 K} (hαβ : RayPair 𝔮 α β)
    (hI : I * Ideal.span {β} = Ideal.span {α}) : Ideal.absNorm I ≡ 1 [MOD p] := by
  obtain ⟨hα, hβ, _, hcβ, hd, hpos⟩ := hαβ
  have hpos' : 0 < Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have hx : ((α * β : 𝓞 K) : K) ≠ 0 := by simpa using mul_ne_zero hα hβ
    have := norm_pos_of_pos_real hx fun τ => by
      have := hpos τ
      simpa [map_mul] using this
    rw [← Algebra.coe_norm_int, map_mul] at this
    exact_mod_cast this
  have h1 := congrArg Ideal.absNorm hI
  rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at h1
  have h2 : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β * Algebra.norm ℤ β = Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have e := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, Int.natCast_natAbs, Int.natCast_natAbs] at e
    have e2 : (Ideal.absNorm I : ℤ) * |Algebra.norm ℤ β| * |Algebra.norm ℤ β| =
        |Algebra.norm ℤ α| * |Algebra.norm ℤ β| := by rw [e]
    rw [mul_assoc, abs_mul_abs_self, ← abs_mul, abs_of_pos hpos'] at e2
    rw [mul_assoc]; exact e2
  have h3 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (hq hd)
  obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hcβ
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have h4 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (x := b * β) (y := 1) (by
    have : b * β - 1 = -v := by linear_combination huv
    rw [this]; exact neg_mem (hq hv))
  rw [map_mul, map_one] at h4
  have h5 := congrArg (Int.cast : ℤ → ZMod p) h2
  push_cast at h4 h5
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  linear_combination ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * h5 +
    ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * ((Algebra.norm ℤ β : ℤ) : ZMod p) * h3 +
    (((Algebra.norm ℤ b : ℤ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) + 1) * (1 - (Ideal.absNorm I : ZMod p)) * h4

end GlobalTheory.RayRootOfUnity

namespace GlobalTheory.RayRootOfUnity

theorem exists_isPrimitiveRoot_of_isRay : ∀ {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) →
    ∃ ζ : H, IsPrimitiveRoot ζ n := by
  intro K H _ _ _ _ _ _ n hn hR
  classical
  have hRF : GlobalTheory.Mem.Fld.IsRayField K H (Ideal.span {(n : 𝓞 K)}) := ⟨inferInstance, hR⟩
  have h𝔮 : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by simpa using hn
  let ψ : H →+* ℂ := (IsAlgClosed.lift : H →ₐ[ℚ] ℂ).toRingHom
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨S, hSa, hS⟩ := GlobalTheory.Mem.BaseField.exists_gens H
  obtain ⟨L, hfd, hgal, hSL, -, -⟩ := GlobalTheory.exists_galois_subfield_conj_stable (insert z S) (by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    exacts [GlobalTheory.Mem.BaseField.isAlgebraic_exp n, hSa w hw])
  have hψL : ∀ x, ψ x ∈ L := hS L (fun w hw => hSL w (Finset.mem_insert_of_mem hw)) ψ
  have hzL : z ∈ L := hSL z (Finset.mem_insert_self _ _)
  have : NumberField L := {}
  letI : Algebra H L := (ψ.codRestrict L hψL).toAlgebra
  letI : Algebra K L := ((ψ.codRestrict L hψL).comp (algebraMap K H)).toAlgebra
  have : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  obtain ⟨x, hx⟩ := GlobalTheory.Mem.RayZeta.root_mem_rayField K H L _ n hn le_rfl hRF
    (GlobalTheory.RayMaximal.closure_isFrob_eq_top L h𝔮)
    (fun I α β hαβ hI => absNorm_modEq_one le_rfl hαβ hI) ⟨z, hzL⟩
    (Subtype.ext (by simpa using hz.pow_eq_one))
  have e : ψ x = z := congrArg Subtype.val hx
  exact ⟨x, IsPrimitiveRoot.of_map_of_injective (f := ψ) (by rw [e]; exact hz) ψ.injective⟩

end GlobalTheory.RayRootOfUnity
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.RayTopGalois GlobalTheory.FieldSize

namespace GlobalTheory.RayNatGalois

theorem isModulus_transport {K K' N : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field N]
    [NumberField N] [Algebra K N] [Algebra K' N] (s : K ≃+* K')
    (hs : ∀ x, algebraMap K' N (s x) = algebraMap K N x) [IsGalois K N] [IsGalois K' N] {𝔪 : Ideal (𝓞 K)}
    {𝔪' : Ideal (𝓞 K')} (hm' : 𝔪' ≠ ⊥) (hmm : ∀ x, RingOfIntegers.mapRingEquiv s x ∈ 𝔪' ↔ x ∈ 𝔪)
    (h : ∀ χ : (N ≃ₐ[K] N) →* ℂˣ, IsModulus N χ 𝔪) (χ : (N ≃ₐ[K'] N) →* ℂˣ) : IsModulus N χ 𝔪' := by
  have hc : ∀ a : 𝓞 K, IsCoprime (Ideal.span {RingOfIntegers.mapRingEquiv s a}) 𝔪' →
      IsCoprime (Ideal.span {a}) 𝔪 := fun a H => by
    rw [Ideal.isCoprime_iff_exists] at H ⊢
    obtain ⟨i, hi, j, hj, hij⟩ := H
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
    obtain ⟨c, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective c
    obtain ⟨j, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective j
    refine ⟨c * a, Ideal.mem_span_singleton'.2 ⟨c, rfl⟩, j, (hmm j).1 hj,
      (RingOfIntegers.mapRingEquiv s).injective ?_⟩
    rw [map_add (f := _), map_mul, hij, map_one]
  refine ⟨hm', fun 𝔭 hp => ?_, fun α β hr => ?_⟩
  · obtain ⟨𝔮, rfl⟩ := (primeEquiv s).surjective 𝔭
    rw [heckeVal_transport s hs]
    refine (h _).2.1 𝔮 fun H => hp (Ideal.dvd_iff_le.2 fun x hx => ?_)
    obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective x
    change (RingOfIntegers.mapRingEquiv s).symm (RingOfIntegers.mapRingEquiv s y) ∈ 𝔮.asIdeal
    rw [RingEquiv.symm_apply_apply]
    exact Ideal.le_of_dvd H ((hmm y).1 hx)
  · obtain ⟨a, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective α
    obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective β
    have ha : a ≠ 0 := fun h => hr.1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => hr.2.1 (by rw [h, map_zero])
    rw [heckeIdeal_transport s hs χ ha, heckeIdeal_transport s hs χ hb]
    refine (h _).2.2 a b ⟨ha, hb, hc _ hr.2.2.1, hc _ hr.2.2.2.1, (hmm _).1 ?_, fun φ => ?_⟩
    · rw [map_sub]; exact hr.2.2.2.2.1
    · have := hr.2.2.2.2.2 (φ.comp s.symm.toRingHom)
      change 0 < φ (s.symm (s a)) * φ (s.symm (s b)) at this
      rwa [s.symm_apply_apply, s.symm_apply_apply] at this

theorem exists_extension {L N : Type} [Field L] [NumberField L] [Field N] [NumberField N] [i : Algebra L N]
    [hab : IsAbelianGalois L N] {n : ℕ} (hn : n ≠ 0) (h : IsRay N (Ideal.span {(n : 𝓞 L)})) (s : L ≃+* L) :
    ∃ f : N →+* N, ∀ x, f (algebraMap L N x) = algebraMap L N (s x) := by
  have hb : Ideal.span {(n : 𝓞 L)} ≠ ⊥ := by simpa using hn
  have hmm : ∀ x, RingOfIntegers.mapRingEquiv s x ∈ Ideal.span {(n : 𝓞 L)} ↔ x ∈ Ideal.span {(n : 𝓞 L)} :=
    fun x => by
      rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        ← map_dvd_iff (RingOfIntegers.mapRingEquiv s) (a := (n : 𝓞 L)) (b := x), map_natCast]
  let j : Algebra L N := ((@algebraMap L N _ _ i).comp s.symm.toRingHom).toAlgebra
  have hs : ∀ x, @algebraMap L N _ _ j (s x) = @algebraMap L N _ _ i x := fun x =>
    congrArg (@algebraMap L N _ _ i) (s.symm_apply_apply x)
  have hab' := @isAbelianGalois_transport L L N _ _ _ _ i j s hs _ hab
  have hm := @GlobalTheory.RayMaximal.isModulus_of_isRay L _ _ N _ _ i hab _ _ h dvd_rfl hb
  obtain ⟨f⟩ := @rayClassFieldMaximalSt_holds L N N _ _ _ _ i hab _ _ j hab' _ hb h
    (@isModulus_transport L L N _ _ _ _ _ _ i j s hs (@IsAbelianGalois.toIsGalois _ _ _ _ i hab)
      (@IsAbelianGalois.toIsGalois _ _ _ _ j hab') _ _ hb hmm hm)
  refine ⟨@AlgHom.toRingHom L N N _ _ _ j i f, fun x => ?_⟩
  rw [← hs]
  exact @AlgHom.commutes L N N _ _ _ j i f (s x)

theorem isGalois_of_isRay_nat (K : Type) {L N : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L]
    [IsAbelianGalois L N] {n : ℕ} (hn : n ≠ 0) (h : IsRay N (Ideal.span {(n : 𝓞 L)})) : IsGalois K N := by
  refine IsGalois.of_fixedField_eq_bot K N (eq_bot_iff.2 fun x hx => ?_)
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).2 fun σ =>
    hx (σ.restrictScalars K) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) y).2 fun s => by
    obtain ⟨f, hf⟩ := exists_extension hn h s.toRingEquiv
    let g : N →ₐ[K] N := { f with
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K L N]
        exact (hf _).trans (congrArg _ (s.commutes k)) }
    exact (algebraMap L N).injective ((hf y).symm.trans
      (hx (AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)) trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

theorem isGalois_fieldRange : ∀ {K H : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) →
    ∀ j : H →+* ℂ, IsGalois ℚ j.toRatAlgHom.fieldRange := by
  intro K H _ _ _ _ _ _ _ n hn h j
  have : IsGalois ℚ H := isGalois_of_isRay_nat ℚ hn h
  exact IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField j.toRatAlgHom)

end GlobalTheory.RayNatGalois

end
end

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LatLevel

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_smul (c : LL) (e : PowerSeries LL) (f : ℤ → M) : conv (c • e) f = c • conv e f := by
  funext k
  unfold conv
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, mul_smul]
  rw [smul_finsum]

theorem conv_congr (e e' : PowerSeries LL) (f : ℤ → M) (a m : ℕ)
    (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (hd : PowerSeries.X ^ m ∣ e - e') (r : ℤ)
    (hr : r < (m : ℤ) - a) : conv e f r = conv e' f r := by
  by_cases h : r < -(a : ℤ)
  · rw [LatFil.conv_vanish e f _ hf r h, LatFil.conv_vanish e' f _ hf r h]
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, r = (q : ℤ) - a := ⟨(r + a).toNat, by omega⟩
    rw [LatFil.conv_eq_sum e f a hf, LatFil.conv_eq_sum e' f a hf]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m := by have := Finset.mem_range.1 hj; omega
    have := (PowerSeries.X_pow_dvd_iff.1 hd) j hj'
    rw [map_sub, sub_eq_zero] at this
    rw [this]

theorem approx_step (bb c cc : LL) (e q : PowerSeries LL) (f : ℤ → M) (a m : ℕ)
    (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (hd : PowerSeries.X ^ m ∣ PowerSeries.C c * q - e)
    (hcc : bb * c = cc) (r : ℤ) (hr : r < (m : ℤ) - a) : bb • conv e f r = conv (PowerSeries.C cc * q) f r := by
  subst hcc
  have h1 : bb • conv e f r = conv (PowerSeries.C bb * e) f r := by
    rw [← PowerSeries.smul_eq_C_mul, conv_smul]
    rfl
  rw [h1]
  refine conv_congr _ _ f a m hf ?_ r hr
  have h2 : PowerSeries.C bb * e - PowerSeries.C (bb * c) * q = -(PowerSeries.C bb * (PowerSeries.C c * q - e)) := by
    rw [map_mul]
    ring
  rw [h2, dvd_neg]
  exact Dvd.dvd.mul_left hd _

end Series

end GlobalTheory.NL.LatLevel

namespace GlobalTheory.NL.LatLevel


private theorem exists_smul_expansion_eq {O L A N M J : Type}
    [CommRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [CommRing A] [Algebra O A] [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module L M] [Fintype J]
    (lev : A →ₐ[O] PowerSeries L) (expansion : N →+ (ℤ → M)) (basis : J → N)
    (hsupp : ∀ j, ∃ a : ℤ, ∀ r < a, expansion (basis j) r = 0)
    (hsmul : ∀ a x, expansion (a • x) = conv (lev a) (expansion x))
    (hdense : ∀ (e : PowerSeries L) (m : ℕ),
      ∃ (a : A) (c : L), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • lev a - e)
    {f : ℤ → M} (hcoeff : ∃ e : J → PowerSeries L,
      f = ∑ j, conv (e j) (expansion (basis j))) (k : ℤ) :
    ∃ (x : N) (c : L), c ≠ 0 ∧ ∀ r ≤ k, c • expansion x r = f r := by
  obtain ⟨e, he⟩ := hcoeff
  choose bound hbound using hsupp
  let a₀ := ∑ j, (-bound j).toNat
  have ha₀ (j : J) (r : ℤ) (hr : r < -(a₀ : ℤ)) : expansion (basis j) r = 0 := by
    apply hbound j r
    have hle : (-bound j).toNat ≤ a₀ :=
      Finset.single_le_sum (f := fun j => (-bound j).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k < (m : ℤ) - a₀ := ⟨(k + a₀ + 1).toNat, by omega⟩
  choose a c _ hca using fun j => hdense (e j) m
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset J) c
  choose o ho using fun j => hb j (Finset.mem_univ j)
  let bL : L := algebraMap O L (b : O)
  have hb0 : bL ≠ 0 := (IsLocalization.map_units L b).ne_zero
  let coeff (j : J) := algebraMap O A (o j) * a j
  let x := ∑ j, coeff j • basis j
  have hx : expansion x = ∑ j, conv (lev (coeff j)) (expansion (basis j)) := by
    change expansion (∑ j, coeff j • basis j) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => hsmul (coeff j) (basis j))
  refine ⟨x, bL⁻¹, inv_ne_zero hb0, fun r hr => ?_⟩
  have hkey : bL • f r = expansion x r := by
    rw [he, hx, Finset.sum_apply, Finset.smul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlev : lev (coeff j) = PowerSeries.C (algebraMap O L (o j)) * lev (a j) := by
      change lev (algebraMap O A (o j) * a j) = _
      rw [map_mul, lev.commutes, PowerSeries.algebraMap_apply]
    have hca' : PowerSeries.X ^ m ∣ PowerSeries.C (c j) * lev (a j) - e j :=
      PowerSeries.smul_eq_C_mul (lev (a j)) (c j) ▸ hca j
    have ho' : bL * c j = algebraMap O L (o j) :=
      (Algebra.smul_def (b : O) (c j)).symm.trans (ho j).symm
    exact (approx_step bL (c j) _ (e j) (lev (a j)) (expansion (basis j))
      a₀ m (ha₀ j) hca' ho' r (hr.trans_lt hm)).trans
      (congrArg (fun p => conv p (expansion (basis j)) r) hlev.symm)
  exact (congrArg (fun y : M => bL⁻¹ • y) hkey.symm).trans (inv_smul_smul₀ hb0 _)

set_option maxHeartbeats 20000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem lattice_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P4 D HW F Cm := by
  intro D HW F Cm l _ K s LL h T hT
  have hP4a := GlobalTheory.NL.LowLevel.expansions_low_and_pullback_record D HW F Cm l K s LL h T hT
  unfold p4
  refine ⟨hP4a.1, ?_⟩
  intro i ζ τ hpt
  let W := (HW l).W K s LL h
  let tie := ((Cm l).C K s LL h).tie
  let expansion := tie.levB T i ζ
  let embed := ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)
  let letter : AA K LL := letE i
  have hlevN (x) (j) : W.levN T i ζ x j = embed (expansion x j) := tie.levN_eq T i ζ x j
  have hlat := LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hpt
  refine ⟨hP4a.2 i ζ τ hpt, ?_, ?_⟩
  · intro x k
    let y := letter • x
    have hmem : ex (Cm l) h T i ζ y ∈ Lat (Cm l) h T i ζ :=
      Submodule.subset_span ⟨1, y, (LowLevel.conv_one (LL := ↥LL.1) (expansion y)).symm⟩
    have hk := ((hlat _).1 hmem).2 k
    exact (hlevN y k).symm ▸ ⟨Submodule.mem_map_of_mem hk.1, hk.2⟩
  · intro k w hw
    have hpoint := (GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hpt
    have hprim := hpoint.1
    refine hpoint.2.2.elim fun ι hcomp => ?_
    have hC := GlobalTheory.NL.CompD.component D HW l K s LL h T hT i ζ τ ι hcomp hpoint.2.1
    have hw' : w ∈ DdRE ((D.loc l).PD K) T.ρ τ ⊓ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (-k) := hw
    refine (hC.2.2.1 w (Submodule.mem_inf.1 hw').1).elim fun d hd => ?_
    have hdw := hd.2
    have hdF : embed d ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
      have hsum : w + (embed d - w) = embed d :=
        (add_comm _ _).trans (sub_add_cancel (embed d) w)
      exact hsum ▸ Submodule.add_mem_sup hw hdw
    let f : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B := Pi.single k d
    have hf_same : f k = d :=
      Pi.single_eq_same (M := fun _ => T.V ⊗[ℚ_[l]] (D.loc l).R.B) k d
    have hf_ne {r : ℤ} (hr : r ≠ k) : f r = 0 :=
      Pi.single_eq_of_ne (M := fun _ => T.V ⊗[ℚ_[l]] (D.loc l).R.B) hr d
    have hsingle : f ∈ Lat (Cm l) h T i ζ := by
      refine (hlat f).2 ⟨⟨k, fun r hr => hf_ne hr.ne⟩, fun r => ?_⟩
      by_cases hr : r = k
      · subst r
        exact hf_same.symm ▸ ⟨hd.1, hdF⟩
      · have hzero := (congrArg (fun z => embed z) (hf_ne hr)).trans embed.map_zero
        exact ⟨(hf_ne hr).symm ▸ zero_mem _, hzero.symm ▸ zero_mem _⟩
    have hfull := GlobalTheory.T.wach_expansions_span_full_lattice D HW F Cm l K s LL h T hT i ζ hprim
    refine (@GlobalTheory.NL.N_basis D HW F l _ K s LL h T hT).elim fun nb => ?_
    have hli := GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i ζ ⟨s, hprim⟩ hfull
    have hdense := (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).2.2.1 i ζ ⟨s, hprim⟩
    have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have : IsFractionRing ↥(OL LL) ↥LL.1 :=
      integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
    have hagree := exists_smul_expansion_eq (W.lev i ζ) expansion (fun j => nb j)
      (fun j => tie.levB_supp T i ζ (nb j)) hli.1 hdense ((hli.2 _ nb).2.1 f hsingle) k
    refine hagree.elim fun x hexists => ?_
    refine hexists.elim fun c hc => ?_
    have hl1 : W.lev i ζ letter = 1 :=
      (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩).2.1
    let expansionN := W.levN T i ζ
    have hN1 (j : ℤ) : expansionN (letter • x) j = embed (expansion x j) := calc
      _ = conv (W.lev i ζ letter) (expansionN x) j := W.levN_smul T i ζ letter x j
      _ = conv (1 : PowerSeries ↥LL.1) (expansionN x) j :=
        congrArg (fun p => conv p (expansionN x) j) hl1
      _ = expansionN x j := congrFun (LowLevel.conv_one (LL := ↥LL.1) (expansionN x)) j
      _ = _ := hlevN x j
    have hscaled (j : ℤ) (hj : j ≤ k) : c • expansionN (letter • x) j = embed (f j) := calc
      _ = c • embed (expansion x j) := congrArg (fun z => c • z) (hN1 j)
      _ = embed (c • expansion x j) := (embed.map_smul c (expansion x j)).symm
      _ = _ := congrArg (fun z => embed z) (hc.2 j hj)
    refine ⟨x, c, hc.1, fun j hj => ?_, ?_⟩
    · have hz := (hscaled j hj.le).trans ((congrArg (fun z => embed z) (hf_ne hj.ne)).trans embed.map_zero)
      exact hz.symm ▸ zero_mem _
    · have heq := (hscaled k le_rfl).trans (congrArg (fun z => embed z) hf_same)
      exact heq.symm ▸ Submodule.mem_sup_right hdw

end GlobalTheory.NL.LatLevel
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ S : TopSit P, S.CrysCalc := by
  first | exact @GlobalTheory.TopSteps.CrysRules.crysCalc | exact GlobalTheory.TopSteps.CrysRules.crysCalc | (intros; apply GlobalTheory.TopSteps.CrysRules.crysCalc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_secondKind_matrix_moore_det_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h → ∀ lam : Fin h → P.R.BdR, (∀ j, lam j ∈ Fil P 0) → (∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0) → ∃ a : Fin h → P.R.B, (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) ∧ (∀ (i : ℕ) j, ev P i (a j) ∈ Fil P 0) ∧ (∀ i : Fin h, ∑ j, lam j * ev P i (a j) ∈ Fil P 1) ∧ (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ≠ 0 := by
  first | exact @GlobalTheory.SecondKind.exists_secondKind | exact GlobalTheory.SecondKind.exists_secondKind | (intros; apply GlobalTheory.SecondKind.exists_secondKind <;> assumption)
end
