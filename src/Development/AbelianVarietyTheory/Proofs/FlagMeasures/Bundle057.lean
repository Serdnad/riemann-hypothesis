module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousUnitriangularSection
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormula
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IdealResProd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable {p : HeightOneSpectrum (𝓞 F)}

theorem val_le_iff (A : LocAt F E sig p) (x y : F) :
    valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← A.val, (valuation A.Fp).vle_iff_le]

theorem val_unit {K : Type} [Field K] [ValuativeRel K] (u : (𝒪[K])ˣ) :
    valuation K ((u : 𝒪[K]) : K) = 1 :=
  (Valuation.integer.integers (valuation K)).valuation_unit u

theorem val_unif (A : LocAt F E sig p) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ) {π : F}
    (hπ : p.valuation F π = WithZero.exp (-1)) :
    valuation A.Fp (A.ιF π) = valuation A.Fp ϖ := by
  haveI := A.lf
  have h0 : (ϖ : A.Fp) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hv0 : valuation A.Fp ϖ ≠ 0 := by simpa using h0
  have hlt : valuation A.Fp ϖ < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact ((Valuation.integer.integers (valuation A.Fp)).isUnit_iff_valuation_eq_one).2 h
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ; exact WithZero.exp_ne_zero hπ.symm
  have hπ1 : valuation A.Fp (A.ιF π) < 1 := by
    have : ¬ valuation A.Fp (A.ιF 1) ≤ valuation A.Fp (A.ιF π) := by
      rw [val_le_iff, hπ, map_one, not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    simpa using this
  apply le_antisymm
  · obtain ⟨k, u, hk⟩ := GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ ((map_ne_zero A.ιF).2 hπ0)
    rw [hk, map_mul, val_unit, mul_one, map_zpow₀] at hπ1 ⊢
    have hk1 : 0 < k := (zpow_lt_one_iff_right_of_lt_one₀ (zero_lt_iff.2 hv0) hlt).1 hπ1
    calc _ ≤ valuation A.Fp ϖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv0) hlt.le hk1
      _ = _ := zpow_one _
  · have hn : {z : A.Fp | valuation A.Fp z = valuation A.Fp ϖ} ∈ nhds (ϖ : A.Fp) := by
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨Units.mk0 _ hv0, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (valuation A.Fp).map_add_eq_of_lt_left hz
    obtain ⟨y, hy⟩ := A.dense.mem_nhds hn
    have hy : valuation A.Fp (A.ιF y) = valuation A.Fp ϖ := hy
    rw [← hy, val_le_iff, hπ]
    have h1 : ¬ p.valuation F 1 ≤ p.valuation F y := by
      rw [← val_le_iff A, hy, map_one, map_one, not_le]; exact hlt
    rw [map_one, not_le] at h1
    by_cases hz : p.valuation F y = 0
    · rw [hz]; exact zero_le
    · rw [← WithZero.exp_log hz] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]; omega

theorem mem_pow_iff (A : LocAt F E sig p) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ) (x : 𝓞 F) (n : ℕ) :
    x ∈ p.asIdeal ^ n ↔ valuation A.Fp (A.ιF x) ≤ valuation A.Fp ϖ ^ n := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer F
  rw [← val_unif A hϖ hπ, ← map_pow, ← map_pow, val_le_iff, map_pow, hπ, ← WithZero.exp_nsmul,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  simp

theorem le_pow_iff (I : Ideal (𝓞 F)) (hI : I ≠ 0) (n : ℕ) :
    I ≤ p.asIdeal ^ n ↔ n ≤ (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) p.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

theorem val_lt_one {K : Type} [Field K] [ValuativeRel K] {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    0 < valuation K ϖ ∧ valuation K ϖ < 1 := by
  have h0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨zero_lt_iff.2 (by simpa using h0), lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_⟩
  exact ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one).2 h

theorem mem_span_iff (A : LocAt F E sig p) (L : LocE A.Fp A.Ep) {c : A.Fp} (hc : c ≠ 0) (x : A.Fp) :
    algebraMap A.Fp A.Ep x ∈ Submodule.span L.O {algebraMap A.Fp A.Ep c} ↔
      valuation A.Fp x ≤ valuation A.Fp c := by
  have hun : IsUnit (algebraMap A.Fp A.Ep c) := (IsUnit.mk0 _ hc).map _
  have hx : algebraMap A.Fp A.Ep x = algebraMap A.Fp A.Ep (x / c) * algebraMap A.Fp A.Ep c := by
    rw [← map_mul, div_mul_cancel₀ _ hc]
  have h1 : valuation A.Fp x ≤ valuation A.Fp c ↔ x / c ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using hc))]
  rw [h1, ← GlobalTheory.UnramOrder.algebraMap_mem_iff L, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨o, ho⟩
    rw [hx] at ho
    have : (o : A.Ep) = algebraMap A.Fp A.Ep (x / c) := hun.mul_right_cancel ho
    rw [← this]; exact o.2
  · intro h
    exact ⟨⟨_, h⟩, hx.symm⟩

theorem vE_eq_count (A : LocAt F E sig p) (L : LocE A.Fp A.Ep) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ)
    (I : Ideal (𝓞 F)) (hI : I ≠ 0) {c : A.Fp} (hc : c ≠ 0)
    (h : Submodule.span L.O ((fun x : 𝓞 F => A.ιE (algebraMap F E x)) '' (I : Set (𝓞 F))) =
      Submodule.span L.O {algebraMap A.Fp A.Ep c}) :
    vE L ϖ (algebraMap A.Fp A.Ep c) =
      ((Associates.mk p.asIdeal).count (Associates.mk I).factors : ℕ) := by
  haveI := A.lf
  obtain ⟨h0, h1⟩ := val_lt_one hϖ
  have hϖ0 : (ϖ : A.Fp) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  obtain ⟨k, u, rfl⟩ := GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ hc
  rw [GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ]
  have key : ∀ n : ℕ, n ≤ (Associates.mk p.asIdeal).count (Associates.mk I).factors ↔ (n : ℤ) ≤ k := by
    intro n
    rw [← le_pow_iff I hI]
    have e1 : (n : ℤ) ≤ k ↔ Submodule.span L.O {algebraMap A.Fp A.Ep ((ϖ : A.Fp) ^ k * ((u : 𝒪[A.Fp]) : A.Fp))}
        ≤ Submodule.span L.O {algebraMap A.Fp A.Ep ((ϖ : A.Fp) ^ n)} := by
      rw [Submodule.span_singleton_le_iff_mem, mem_span_iff A L (pow_ne_zero n hϖ0), map_mul, val_unit,
        mul_one, map_zpow₀, map_pow, ← zpow_natCast, zpow_le_zpow_iff_right_of_lt_one₀ h0 h1]
    rw [e1, ← h, Submodule.span_le, Set.image_subset_iff]
    refine forall₂_congr fun x _ => ?_
    rw [mem_pow_iff A hϖ, Set.mem_preimage, A.compat, SetLike.mem_coe,
      mem_span_iff A L (pow_ne_zero n hϖ0), map_pow]
  have hk : 0 ≤ k := by simpa using (key 0).1 (Nat.zero_le _)
  lift k to ℕ using hk
  have a := (key k).2 le_rfl
  have b := (key _).1 le_rfl
  omega

theorem absNorm_eq_finprod (I : Ideal (𝓞 F)) (hI : I ≠ 0) :
    ∏ᶠ p : HeightOneSpectrum (𝓞 F), (Ideal.absNorm p.asIdeal : ℝ) ^
      (Associates.mk p.asIdeal).count (Associates.mk I).factors = (Ideal.absNorm I : ℝ) := by
  have := map_finprod ((Nat.castRingHom ℝ).toMonoidHom.comp (Ideal.absNorm (S := 𝓞 F)).toMonoidHom)
    (Ideal.hasFiniteMulSupport hI)
  rw [Ideal.finprod_heightOneSpectrum_factorization hI] at this
  simpa [HeightOneSpectrum.maxPowDividing] using this.symm

theorem discr_and_level : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ ϖ : ∀ p, 𝒪[(A.loc p).Fp], (∀ p, Irreducible (ϖ p)) → (∀ c : ∀ p, ((A.loc p).Fp)ˣ, (∀ p, Submodule.span (A.L p).O ((fun x : 𝓞 F => (A.loc p).ιE (algebraMap F E x)) '' (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) = Submodule.span (A.L p).O {algebraMap (A.loc p).Fp (A.loc p).Ep (c p)}) → ∏ᶠ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep (c p)) = |(NumberField.discr F : ℝ)|) ∧ ∀ g : ℕ, g ≠ 0 → (∀ p : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ p.asIdeal → ∃ u : (𝒪[(A.loc p).Fp])ˣ, (g : (A.loc p).Fp) = ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) * (ϖ p : (A.loc p).Fp)) → ∏ᶠ p : HeightOneSpectrum (𝓞 F), (if (g : 𝓞 F) ∈ p.asIdeal then (resQ (ϖ p) : ℝ) else 1) = (g : ℝ) ^ Module.finrank ℚ F := by
  intro F E _ _ _ _ _ sig A ϖ hϖ
  have hq : ∀ p, resQ (ϖ p) = Ideal.absNorm p.asIdeal := fun p => (GlobalTheory.HL.PlacesInt.integers_local A).2.2.2 p _ (hϖ p)
  refine ⟨fun c hc => ?_, fun g hg hu => ?_⟩
  · have hI : differentIdeal ℤ (𝓞 F) ≠ 0 := by
      intro h
      have := absNorm_differentIdeal F (𝓞 F)
      rw [h, map_zero] at this
      exact discr_ne_zero F (Int.natAbs_eq_zero.1 this.symm)
    have := absNorm_eq_finprod _ hI
    rw [absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, Int.cast_abs] at this
    rw [← this]
    refine finprod_congr fun p => ?_
    rw [vE_eq_count (A.loc p) (A.L p) (hϖ p) _ hI (c p).ne_zero (hc p), zpow_natCast, hq]
  · have hg' : (g : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hg
    have hI : Ideal.span {(g : 𝓞 F)} ≠ 0 := by simpa using hg
    have := absNorm_eq_finprod _ hI
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Nat.cast_pow] at this
    rw [← this]
    refine finprod_congr fun p => ?_
    have key := le_pow_iff (p := p) _ hI
    simp only [Ideal.span_singleton_le_iff_mem] at key
    split_ifs with h
    · obtain ⟨u, hu⟩ := hu p h
      obtain ⟨h0, h1⟩ := val_lt_one (hϖ p)
      have a := (key 1).1 (by simpa using h)
      have b : ¬ (g : 𝓞 F) ∈ p.asIdeal ^ 2 := by
        rw [mem_pow_iff (A.loc p) (hϖ p)]
        have e : (A.loc p).ιF ((g : 𝓞 F) : F) = (g : (A.loc p).Fp) := by simp
        rw [e, hu, map_mul, val_unit, one_mul, not_le]
        calc _ < valuation (A.loc p).Fp (ϖ p) ^ 1 := pow_lt_pow_right_of_lt_one₀ h0 h1 (by norm_num)
          _ = _ := pow_one _
      rw [key] at b
      have : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 F)})).factors = 1 := by omega
      rw [this, pow_one, hq]
    · have b : ¬ (g : 𝓞 F) ∈ p.asIdeal ^ 1 := by simpa using h
      rw [key] at b
      have : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 F)})).factors = 0 := by omega
      rw [this, pow_zero]

end GlobalTheory.IdealResProd
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

open scoped Pointwise

namespace GlobalTheory.SnMass.SkewDom

theorem im_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w : InfinitePlace E) (z : E) :
    (w.embedding (σ z)).im = -(w.embedding z).im := by
  rw [h.2.2.2 w.embedding z]; simp

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem mem_skewLat_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ x ∈ I, σ x ∈ I)
    {θ : 𝓞 E} (hθ : (θ : E) + σ θ = 1) (c : ℝ) (z : InfinitePlace E → ℝ) :
    z ∈ (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) ↔
      ∃ b ∈ {b | ∃ x ∈ I, imV x = b}, z = (2 * c) • b := by
  change (∃ y ∈ I, (σ : E →+* E) y = -y ∧ ∀ w, z w = c * (w.embedding y).im) ↔ _
  simp only [AlgHom.coe_toRingHom]
  constructor
  · rintro ⟨y, hy, hs, hz⟩
    have hθy : (θ : E) * y ∈ I := by
      have := (I : Submodule (𝓞 E) E).smul_mem θ hy
      rwa [Algebra.smul_def] at this
    refine ⟨imV ((θ : E) * y), ⟨(θ : E) * y, hθy, rfl⟩, ?_⟩
    funext w
    have hy2 : y = (θ : E) * y - σ ((θ : E) * y) := by
      rw [map_mul, hs]; linear_combination (-y) * hθ
    rw [hz w, Pi.smul_apply, smul_eq_mul, imV]
    conv_lhs => rw [hy2]
    rw [map_sub, Complex.sub_im, im_sigma hcm]; ring
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x - σ x, (I : Submodule (𝓞 E) E).sub_mem hx (hI x hx), ?_, fun w => ?_⟩
    · rw [map_sub, sigma_sigma hcm]; ring
    · rw [Pi.smul_apply, smul_eq_mul, imV, map_sub, Complex.sub_im, im_sigma hcm]; ring

theorem skewDom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, σ x ∈ I) → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ (c : ℝ), 0 < c → ∀ (D : Set (InfinitePlace E → ℝ)) (m : ℝ≥0∞), MeasurableSet D → (∀ y, ∃! l, l ∈ {b | ∃ x ∈ I, imV x = b} ∧ y + l ∈ D) → volume D = m → HasDom volume (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal ((2 * c) ^ Fintype.card (InfinitePlace E)) * m) := by
  intro F E _ _ _ _ _ σ hcm I hI θ hθ c hc D m hD hU hm
  have hmem := mem_skewLat_iff hcm hI hθ c
  have h2c : (2 * c) ≠ 0 := by positivity
  refine ⟨(2 * c) • D, hD.const_smul₀ _, fun v => ?_, ?_⟩
  · obtain ⟨l, ⟨hl, hlD⟩, hu⟩ := hU ((2 * c)⁻¹ • v)
    refine ⟨(2 * c) • l, ⟨(hmem _).2 ⟨l, hl, rfl⟩, ?_⟩, ?_⟩
    · refine Set.mem_smul_set.2 ⟨_, hlD, ?_⟩
      rw [smul_add, smul_inv_smul₀ h2c]
    · rintro l' ⟨hl', hl'D⟩
      obtain ⟨b, hb, rfl⟩ := (hmem _).1 hl'
      obtain ⟨d, hd, hdv⟩ := Set.mem_smul_set.1 hl'D
      have hbd : (2 * c)⁻¹ • v + b = d := by
        rw [← inv_smul_smul₀ h2c d, hdv, smul_add, inv_smul_smul₀ h2c]
      rw [hu b ⟨hb, hbd ▸ hd⟩]
  · rw [Measure.addHaar_smul, hm, Module.finrank_fintype_fun_eq_card, abs_of_pos (by positivity)]

end GlobalTheory.SnMass.SkewDom
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LeftMul

theorem pos_eI (k r : ℕ) (a : Fin r) : pos k r (eI k r a) = a.val := by
  have := a.isLt
  unfold pos eI
  dsimp only
  split_ifs <;> omega

theorem pos_wI (k r : ℕ) (j : Fin (k + 1)) : pos k r (wI k r j) = r := by
  have := j.isLt
  unfold pos wI
  dsimp only
  split_ifs <;> omega

theorem pos_esI (k r : ℕ) (a : Fin r) : pos k r (esI k r a) = 2 * r - a.val := by
  have := a.isLt
  unfold pos esI
  dsimp only
  split_ifs <;> omega

theorem mul_apply_of_dep (k r d : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : Dep k r d (g - 1)) (hx : Dep k r 1 (x - 1)) (i j : Fin (2 * r + k + 1)) (hij : i ≠ j)
    (hp : pos k r j ≤ pos k r i + d) : (g * x) i j = g i j + x i j := by
  have h1 : g * x = (g - 1) * (x - 1) + (g - 1) + (x - 1) + 1 := by noncomm_ring
  have h2 : ((g - 1) * (x - 1)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : pos k r l < pos k r i + d
    · rw [hg i l hl, zero_mul]
    · rw [hx l j (by omega), mul_zero]
  rw [h1, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h2, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.one_apply_ne hij]
  ring

end GlobalTheory.SnMass.VolN.LeftMul

namespace GlobalTheory.SnMass.VolN


open GlobalTheory.SnMass.VolN.LeftMul in
theorem cM_mul_of_dep : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ),
    Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d →
      cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  intro k r g x d hg hx β hβ
  rcases β with p | a | p | a
  · have hlt : p.1.1.val < p.1.2.val := p.2
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (eI k r p.1.2) = x (eI k r p.1.1) (eI k r p.1.2) + g (eI k r p.1.1) (eI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI] at this; omega
    · rw [pos_eI, pos_eI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show (fun j => (g * x) (eI k r a) (wI k r j)) = (fun j => x (eI k r a) (wI k r j)) + (fun j => g (eI k r a) (wI k r j))
    funext l
    rw [Pi.add_apply, mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, wI] at this; omega
    · rw [pos_eI, pos_wI]; omega
  · have hlt : p.1.1.val < p.1.2.val := p.2
    have hb := p.1.2.isLt
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (esI k r p.1.2) = x (eI k r p.1.1) (esI k r p.1.2) + g (eI k r p.1.1) (esI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show ((g * x) (eI k r a) (esI k r a)).im = (x (eI k r a) (esI k r a)).im + (g (eI k r a) (esI k r a)).im
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, Complex.add_im, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega

end GlobalTheory.SnMass.VolN
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem re_corner_eq_zero (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (hx : x ∈ Nset k r) (hd : Dep k r (2 * r - 2 * a.val) (x - 1)) :
    (x (eI k r a) (esI k r a)).re = 0 := by
  have hsv : (esI k r a).val = 2 * r + k - a.val := rfl
  have hev : (eI k r a).val = a.val := rfl
  generalize esI k r a = s at *
  generalize eI k r a = e at *
  have ha := a.isLt

  have hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → i ≠ s → x i s = 0 := by
    intro i hi hne
    have h0 := hd i s (by
      simp only [pos]
      split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h0; exact h0
  have hss : x s s = 1 := by
    have h0 := hd s s (by simp only [pos]; split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0; exact h0
  have hU := congrFun (congrFun hx.1 s) s
  have hH : Hpk k r s s = 0 := by
    simp only [Hpk, Fin.ext_iff, and_true]
    split_ifs <;> first | rfl | omega | (exfalso; omega)
  rw [hH] at hU
  have key : ∀ i j : Fin (2 * r + k + 1), star (x i s) * Hpk k r i j * x j s =
      (if i = s ∧ j = e then x j s else 0) + (if i = e ∧ j = s then star (x i s) else 0) := by
    intro i j
    by_cases h1 : i = s ∧ j = e
    · rw [h1.1, h1.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r s e = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    by_cases h2 : i = e ∧ j = s
    · rw [h2.1, h2.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r e s = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    rw [if_neg h1, if_neg h2, add_zero]
    have hi : i = s ∨ i.val ≤ a.val ∨ x i s = 0 := by
      by_cases h : i = s
      · exact Or.inl h
      by_cases h' : i.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol i (by omega) h))
    have hj : j = s ∨ j.val ≤ a.val ∨ x j s = 0 := by
      by_cases h : j = s
      · exact Or.inl h
      by_cases h' : j.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol j (by omega) h))
    have hI : ∀ i : Fin (2 * r + k + 1), i = s ↔ i.val = 2 * r + k - a.val := fun i =>
      ⟨fun h => h ▸ hsv, fun h => Fin.ext (h.trans hsv.symm)⟩
    have hE : ∀ i : Fin (2 * r + k + 1), i = e ↔ i.val = a.val := fun i =>
      ⟨fun h => h ▸ hev, fun h => Fin.ext (h.trans hev.symm)⟩
    rw [hI, hE] at h1 h2
    rcases hi with hi | hi | hi
    · rcases hj with hj | hj | hj
      · subst hi; subst hj; simp [hH]
      · have : Hpk k r i j = 0 := by
          rw [hI] at hi
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · rcases hj with hj | hj | hj
      · have : Hpk k r i j = 0 := by
          rw [hI] at hj
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · have : Hpk k r i j = 0 := by
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · simp [hi]
  have hsum : (xᴴ * Hpk k r * x) s s = x e s + star (x e s) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [key, Finset.sum_add_distrib]
    simp [ite_and, hss]
  rw [hsum] at hU
  have := congrArg Complex.re hU
  simp at this
  linarith

end GlobalTheory.SnMass.VolN
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_continuous_unitriangular_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, Continuous t ∧ (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) := by
  first | exact @GlobalTheory.UnitriSection.unitri_section | exact GlobalTheory.UnitriSection.unitri_section | (intros; apply GlobalTheory.UnitriSection.unitri_section <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hyperboloid_chart_measure_formula : PI.RhsWLim.W.HypChart := by
  first | exact @GlobalTheory.HypChartPf.hypChart | exact GlobalTheory.HypChartPf.hypChart | (intros; apply GlobalTheory.HypChartPf.hypChart <;> assumption)
end
