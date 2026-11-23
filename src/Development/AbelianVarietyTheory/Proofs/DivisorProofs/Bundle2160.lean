module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2132
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueEisenstein.Swap

open GlobalTheory.ResLine.Swap

theorem two_mul_le_and_exists_ratPts_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    2 * (r + 1) ≤ n ∧ ∃ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F Y = adMat F X ∧
      (matHom _ σ J w).1 * adMat F X = adMat F Y := by
  intro F E _ _ _ _ _ σ n J r X Y hσ hJ hW
  classical
  have hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0 := hW.xx
  have hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 := hW.yy
  have hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 := hW.xy
  have hJ' := cT_eq_of_isHermND hJ
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have h := congrArg (Formalism.UG.cT (σ : E →+* E)) hxy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ', Formalism.UG.cT_one] at h
    simpa [Matrix.mul_assoc] using h
  refine ⟨?_, ?_⟩
  ·
    let f : ((Fin (r + 1) → E) × (Fin (r + 1) → E)) →ₗ[E] (Fin n → E) :=
      Y.mulVecLin.comp (LinearMap.fst E _ _) + X.mulVecLin.comp (LinearMap.snd E _ _)
    have hf : Function.Injective f := by
      intro p q hpq
      have hp : ∀ p : (Fin (r + 1) → E) × (Fin (r + 1) → E),
          (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ f p = p.1 ∧ (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ f p = p.2 := by
        intro p
        simp only [f, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
          Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec, hxx, hyy, hxy, hyx,
          Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
        exact ⟨trivial, trivial⟩
      have h1 := hp p
      have h2 := hp q
      rw [hpq] at h1
      exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
    have h := LinearMap.finrank_le_finrank_of_injective hf
    simpa [Module.finrank_prod, two_mul] using h
  set u := X - Y with hu
  set v := Formalism.UG.cT (σ : E →+* E) u * J with hv
  have hvy : v * Y = 1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxy, hyy, sub_zero]
  have hvx : v * X = -1 := by
    rw [hv, hu, cT_sub', Matrix.sub_mul, Matrix.sub_mul, hxx, hyx, zero_sub]
  set w0 : Matrix (Fin n) (Fin n) E := 1 + u * v with hw0
  have hw0y : w0 * Y = X := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvy, Matrix.mul_one, hu]; abel
  have hw0x : w0 * X = Y := by
    rw [hw0, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hvx, Matrix.mul_neg, Matrix.mul_one, hu]; abel
  have hw0u : w0 * u = -u := by
    rw [hu, Matrix.mul_sub, hw0y, hw0x]; abel
  have hsq : w0 * w0 = 1 := by
    conv_lhs => rw [show w0 * w0 = w0 * (1 + u * v) from rfl]
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hw0u, hw0, Matrix.neg_mul]; abel
  have hcw : Formalism.UG.cT (σ : E →+* E) w0 * J = J * w0 := by
    rw [hw0, cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, hv, Formalism.UG.cT_mul, cT_cT_of_isCMExt hσ, hJ',
      Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hunit : Formalism.UG.cT (σ : E →+* E) w0 * J * w0 = J := by
    rw [hcw, Matrix.mul_assoc, hsq, Matrix.mul_one]
  let U : GL (Fin n) E := ⟨w0, w0, hsq, hsq⟩
  have hU : U ∈ Formalism.UG.UJ (σ : E →+* E) J := hunit
  refine ⟨GlobalTheory.AdelicU.ratEmb σ J ⟨U, hU⟩, ?_, ?_, ?_⟩
  · rw [← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨_, rfl⟩
  · change w0.map (inclR (F := F) (AF F)) * adMat F Y = adMat F X
    simp only [adMat]
    rw [← Matrix.map_mul, hw0y]
  · change w0.map (inclR (F := F) (AF F)) * adMat F X = adMat F Y
    simp only [adMat]
    rw [← Matrix.map_mul, hw0x]

end GlobalTheory.ResidueEisenstein.Swap

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRedRes

theorem residue_perfect_and_char :
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField (ResidueField R)] (L W : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra W L] [IsFractionRing W L], IsAbove R K (algebraMap W L).range → PerfectField (ResidueField W) ∧ ∀ m : ℕ, (m : ResidueField R) ≠ 0 → (m : ResidueField W) ≠ 0 := by
  intro R K _ _ _ _ _ _ _ L W _ _ _ _ _ _ _ _ h
  have hWL : Function.Injective (algebraMap W L) := IsFractionRing.injective W L
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  set V : Subring L := (algebraMap W L).range with hV
  have memV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ (algebraMap R K).range := by
    intro x
    rw [← Subring.mem_comap, show V.comap (algebraMap K L) = (algebraMap R K).range from h]
  let e : W ≃+* V := RingEquiv.ofBijective (algebraMap W L).rangeRestrict
    ⟨fun a b hab => hWL (by simpa using congrArg Subtype.val hab), (algebraMap W L).rangeRestrict_surjective⟩
  have he : ∀ v : V, algebraMap W L (e.symm v) = v := by
    intro v
    have := congrArg Subtype.val (e.apply_symm_apply v)
    exact this
  let ψ : R →+* V := ((algebraMap K L).comp (algebraMap R K)).codRestrict V
    (fun r => (memV _).2 ⟨r, rfl⟩)
  let φ : R →+* W := e.symm.toRingHom.comp ψ
  have hφ : ∀ r, algebraMap W L (φ r) = algebraMap K L (algebraMap R K r) := by
    intro r; exact he (ψ r)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := congrArg (algebraMap W L) hab
    rw [hφ, hφ] at this
    exact hRK ((algebraMap K L).injective this)
  haveI : IsLocalHom φ := by
    constructor
    intro r hr
    obtain ⟨u, hu⟩ := hr
    have hx : algebraMap W L (φ r) * algebraMap W L (u⁻¹ : Wˣ) = 1 := by
      rw [← map_mul, ← hu]; simp
    rw [hφ] at hx
    have hx0 : algebraMap R K r ≠ 0 := by
      intro h0; rw [h0] at hx; simp at hx
    have hinv : algebraMap K L (algebraMap R K r)⁻¹ = algebraMap W L (u⁻¹ : Wˣ) := by
      rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right hx).symm
    obtain ⟨s, hs⟩ := (memV _).1 (by rw [hinv]; exact RingHom.mem_range_self _ _)
    have h1 : r * s = 1 := hRK (by rw [map_mul, hs, map_one, mul_inv_cancel₀ hx0])
    exact ⟨⟨r, s, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  let f := ResidueField.map φ
  have hf : Function.Injective f := f.injective
  refine ⟨?_, fun m hm hW => hm (hf (by rw [map_natCast, map_zero]; exact hW))⟩
  letI : Algebra (ResidueField R) (ResidueField W) := f.toAlgebra
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := R)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField W) := by
    constructor
    intro y
    obtain ⟨w, rfl⟩ := residue_surjective y
    have hint : IsIntegral K (algebraMap W L w) := Algebra.IsIntegral.isIntegral _
    set p := minpoly K (algebraMap W L w)
    obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
    set q := IsLocalization.integerNormalization (nonZeroDivisors R) p
    have hp0 : p ≠ 0 := minpoly.ne_zero hint
    have hq0 : q ≠ 0 := by
      intro hq; rw [hq, Polynomial.map_zero] at hb
      have hb0 : (algebraMap R K b) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbmem
      rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hb
      exact hp0 ((mul_eq_zero.1 hb.symm).resolve_left (by simpa using hb0))
    have hqw : Polynomial.eval₂ φ w q = 0 := by
      apply hWL
      rw [map_zero, Polynomial.hom_eval₂]
      have : (algebraMap W L).comp φ = (algebraMap K L).comp (algebraMap R K) := RingHom.ext hφ
      rw [this, ← Polynomial.eval₂_map, hb]
      rw [Algebra.smul_def, Polynomial.eval₂_mul]
      have : Polynomial.eval₂ (algebraMap K L) (algebraMap W L w) p = 0 := minpoly.aeval K _
      rw [this, mul_zero]
    set pp := q.primPart
    have hpp : Polynomial.eval₂ φ w pp = 0 := by
      have hc : q.content ≠ 0 := (Polynomial.content_eq_zero_iff).not.2 hq0
      have := hqw
      rw [Polynomial.eq_C_content_mul_primPart q, Polynomial.eval₂_mul, Polynomial.eval₂_C] at this
      exact (mul_eq_zero.1 this).resolve_left (fun h0 => hc (hφinj (by rw [h0, map_zero])))
    refine ⟨pp.map (residue R), ?_, ?_⟩
    · intro h0
      have hmem : pp ∈ RingHom.ker (Polynomial.mapRingHom (residue R)) := by
        simpa [RingHom.mem_ker] using h0
      rw [Polynomial.ker_mapRingHom, ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
        Set.image_singleton, Ideal.mem_span_singleton] at hmem
      exact hϖ.not_isUnit (Polynomial.isPrimitive_primPart q ϖ hmem)
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      change Polynomial.eval₂ (f.comp (residue R)) _ _ = 0
      rw [ResidueField.map_comp_residue, ← Polynomial.hom_eval₂, hpp, map_zero]
  exact Algebra.IsAlgebraic.perfectField (ResidueField R)

end GlobalTheory.AbVarRedRes
end

section

set_option autoImplicit false

noncomputable section

open Polynomial GlobalTheory.Published.AbVarRed IsLocalRing

namespace GlobalTheory.ValAbove

theorem partialSum_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (c : ℕ → R) (n : ℕ)
    (x : Ω) (h : ∑ i ∈ Finset.range (n + 1), c i • x ^ i = 0) {m t : ℕ} (hm : m ≤ n) (ht : t ≤ n + 1) :
    (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
  have hmem : ∀ e, e ≤ n → ∀ r : R, r • x ^ e ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
    intro e he r
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_image_of_mem _ (Set.mem_Iic.2 he)
  by_cases htm : t < m
  · rw [Finset.sum_mul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [smul_mul_assoc, ← pow_add]
    exact hmem _ (by omega) _
  · push_neg at htm
    have hsplit := Finset.sum_range_add_sum_Ico (fun i => c i • x ^ i) (show m ≤ n + 1 by omega)
    rw [h] at hsplit
    have e1 : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ i) * x ^ (t - m) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      rw [smul_mul_assoc, smul_mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    have key : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = -∑ i ∈ Finset.range m, c i • x ^ (i + (t - m)) := by
      rw [e1, eq_neg_of_add_eq_zero_right hsplit, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, ← pow_add]
    rw [key]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    rw [Finset.mem_range] at hi
    exact hmem _ (by omega) _

theorem isIntegral_of_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (n : ℕ) (x z : Ω)
    (hz : ∀ t ≤ n, z * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) :
    IsIntegral R z := by
  refine isIntegral_of_smul_mem_submodule
    (Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) ?_ (Submodule.fg_span ((Set.finite_Iic n).image _)) z ?_
  · rw [Ne, Submodule.span_eq_bot]
    push_neg
    refine ⟨1, ?_, one_ne_zero⟩
    exact ⟨0, Set.mem_Iic.2 (Nat.zero_le n), pow_zero x⟩
  · intro w hw
    refine Submodule.span_induction (fun w hw => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [smul_add]; exact Submodule.add_mem _ ha hb)
      (fun r a _ ha => by rw [smul_eq_mul, mul_smul_comm]; exact Submodule.smul_mem _ r ha) hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [Set.mem_Iic] at ht
    rw [smul_eq_mul]
    exact hz t (by omega)

theorem exists_integral_mul_eq_of_isAbove : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ y ∈ V, ∃ a s : Ω,
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem a ∧
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem s ∧ V.valuation s = 1 ∧ y * s = a := by
  intro R K Ω _ _ _ _ _ _ _ _ _ V hV y hy
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hιinj : Function.Injective ((algebraMap K Ω).comp (algebraMap R K)) :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hmemV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact this
  have hle : ∀ r : R, V.valuation (algebraMap R Ω r) ≤ 1 := fun r => (V.valuation_le_one_iff _).2 (hmemV r)
  have hlt : ∀ r : R, ¬ IsUnit r → V.valuation (algebraMap R Ω r) < 1 := by
    intro r hr
    refine lt_of_le_of_ne (hle r) fun h1 => hr ?_
    have h0 : algebraMap R Ω r ≠ 0 := by
      intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
    have hinv : (algebraMap R Ω r)⁻¹ ∈ V := (V.valuation_le_one_iff _).1 (by rw [map_inv₀, h1, inv_one])
    have hK : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω ((algebraMap R K r)⁻¹) ∈ V
      rw [map_inv₀]; exact hinv
    rw [hV] at hK
    obtain ⟨r', hr'⟩ := hK
    have hrK : algebraMap R K r ≠ 0 := by
      intro h; apply h0; change algebraMap K Ω (algebraMap R K r) = 0; rw [h, map_zero]
    have hrr : r * r' = 1 :=
      IsFractionRing.injective R K (by rw [map_mul, hr', mul_inv_cancel₀ hrK, map_one])
    exact ⟨⟨r, r', hrr, by rw [mul_comm, hrr]⟩, rfl⟩
  have hunit : ∀ r : R, IsUnit r → V.valuation (algebraMap R Ω r) = 1 := by
    intro r hr
    obtain ⟨u, rfl⟩ := hr
    have h := congrArg (fun w => V.valuation (algebraMap R Ω w)) u.mul_inv
    simp only [map_mul, map_one] at h
    refine le_antisymm (hle _) ?_
    by_contra hlt'
    push_neg at hlt'
    have : V.valuation (algebraMap R Ω ↑u) * V.valuation (algebraMap R Ω ↑u⁻¹) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' (hle _)) hlt'
    rw [h] at this
    exact lt_irrefl _ this

  classical
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have halgK : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
  have halgR : IsAlgebraic R y := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨f, hf0, hfy⟩ := halgR
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hex : ∃ e : ℕ, ¬ (C (ϖ ^ (e + 1)) ∣ f) := by
    have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf0
    obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨e, fun hd => ?_⟩
    have hd' : ϖ ^ e * ϖ ∣ ϖ ^ e * (u : R) := by
      rw [← pow_succ, mul_comm]; rw [← hu]
      exact (C_dvd_iff_dvd_coeff _ _).1 hd _
    have : ϖ ∣ (u : R) := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).1 hd'
    exact hϖ.not_isUnit (isUnit_of_dvd_unit this u.isUnit)
  have hdiv : ∀ e, (∀ k < e, ¬ ¬ (C (ϖ ^ (k + 1)) ∣ f)) → C (ϖ ^ e) ∣ f := by
    intro e he
    cases e with
    | zero => simp
    | succ k => exact not_not.1 (he k (Nat.lt_succ_self k))
  obtain ⟨g, hg⟩ := hdiv (Nat.find hex) (fun k hk => Nat.find_min hex hk)
  have hgunit : ∃ i, IsUnit (g.coeff i) := by
    by_contra hno
    push_neg at hno
    apply Nat.find_spec hex
    have hmax : maximalIdeal R = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    have hCg : C ϖ ∣ g := (C_dvd_iff_dvd_coeff _ _).2 fun i => by
      have : g.coeff i ∈ maximalIdeal R := (mem_maximalIdeal _).2 (hno i)
      rw [hmax] at this
      exact Ideal.mem_span_singleton.1 this
    have h2 := mul_dvd_mul_left (C (ϖ ^ Nat.find hex)) hCg
    rw [← hg, ← C_mul, ← pow_succ] at h2
    exact h2
  have hgy : aeval y g = 0 := by
    rw [hg, map_mul, aeval_C] at hfy
    refine (mul_eq_zero.1 hfy).resolve_left ?_
    exact fun h => pow_ne_zero _ hϖ.ne_zero (hιinj (h.trans (map_zero _).symm))
  set n := g.natDegree with hn
  set c := g.coeff with hc
  have hsum : ∑ i ∈ Finset.range (n + 1), c i • y ^ i = 0 := by
    rw [← hgy, aeval_eq_sum_range]
  obtain ⟨i₀, hi₀⟩ := hgunit
  have hS : ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).Nonempty :=
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hi₀.ne_zero)), hi₀⟩⟩
  set j := ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).max' hS with hj
  have hjmem := Finset.max'_mem _ hS
  rw [← hj, Finset.mem_filter, Finset.mem_range] at hjmem
  have hjn : j ≤ n := Nat.le_of_lt_succ hjmem.1
  have hbig : ∀ i, j < i → i ≤ n → ¬ IsUnit (c i) := by
    intro i hji hin hu
    have := Finset.le_max' ((Finset.range (n + 1)).filter fun i => IsUnit (c i)) i
      (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hu⟩)
    rw [← hj] at this
    omega
  set b := ∑ i ∈ Finset.Ico j (n + 1), c i • y ^ (i - j) with hb
  have hyle : V.valuation y ≤ 1 := (V.valuation_le_one_iff y).2 hy
  have hvb : V.valuation b = 1 := by
    rw [hb, Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn), Nat.sub_self, pow_zero, Algebra.smul_def,
      mul_one, add_comm]
    rw [Valuation.map_add_eq_of_lt_right, hunit _ hjmem.2]
    rw [hunit _ hjmem.2]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [Algebra.smul_def, map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hyle _)) (hlt _ (hbig i (by omega) (by omega)))
  refine ⟨y * b, b, ?_, ?_, hvb, rfl⟩
  · exact isIntegral_of_mul_pow_mem n y (y * b) fun t ht => by
      rw [show y * b * y ^ t = b * y ^ (t + 1) by ring]
      exact partialSum_mul_pow_mem c n y hsum hjn (by omega)
  · exact isIntegral_of_mul_pow_mem n y b fun t ht => partialSum_mul_pow_mem c n y hsum hjn (by omega)

end GlobalTheory.ValAbove
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Published.AbVarRed

def ptOverMap {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') :
    ptOver K Ω' ⟶ ptOver K Ω :=
  Over.homMk (spMap (j : Ω →+* Ω')) (by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp)

theorem epi_ptOverMap {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') :
    Epi (ptOverMap j).left := by
  change Epi (spMap (j : Ω →+* Ω'))
  letI := (j : Ω →+* Ω').toAlgebra
  haveI : Flat (spMap (j : Ω →+* Ω')) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat Ω Ω')
  haveI : Surjective (spMap (j : Ω →+* Ω')) :=
    ⟨fun p => ⟨(⊥ : PrimeSpectrum Ω'), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem ptOverMap_comp_specAut {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω']
    (j : Ω →ₐ[K] Ω') (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω') (h : ∀ x, σ' (j x) = j (σ x)) :
    ptOverMap j ≫ specAut σ = specAut σ' ≫ ptOverMap j :=
  Over.OverMorphism.ext (by
    change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (h x).symm)

theorem exists_injective_ptOver_galois : ∀ (K Ω Ω' : Type) [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A], ∃ f : (ptOver K Ω ⟶ A) →* (ptOver K Ω' ⟶ A), Function.Injective f ∧ ∀ (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) → ∀ x, f (specAut σ ≫ x) = specAut σ' ≫ f x := by
  intro K Ω Ω' _ _ _ _ _ j A _
  refine ⟨MonoidHom.mk' (fun x => ptOverMap j ≫ x) fun x y => MonObj.comp_mul _ x y, ?_, ?_⟩
  · intro x y e
    have := epi_ptOverMap j
    exact Over.OverMorphism.ext ((cancel_epi (ptOverMap j).left).1
      (by simpa using congrArg (fun q => q.left) (show ptOverMap j ≫ x = ptOverMap j ≫ y from e)))
  · intro σ σ' h x
    change ptOverMap j ≫ specAut σ ≫ x = specAut σ' ≫ ptOverMap j ≫ x
    rw [← Category.assoc, ptOverMap_comp_specAut j σ σ' h, Category.assoc]

end GlobalTheory.Published.AbVarRed

end
end

section

open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.betaConjugate_mean_logAbs_bound_of_transport : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LBound → TorEx → BetaArch := by
  first | exact @GlobalTheory.SqTop.betaArch_of_transport | exact GlobalTheory.SqTop.betaArch_of_transport | (intros; apply GlobalTheory.SqTop.betaArch_of_transport <;> assumption)
end
