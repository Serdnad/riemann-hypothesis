module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumePosSimplexLe
public import ReciprocityTheory.Automorphisms.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem exists_isPrimitive_invol_invariant {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (ω : B) (hω : IsUnit (ω - c ω))
    (hfix : ∀ t, c t = t → t ≠ 0 → IsUnit t) :
    ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨1, fun a ha => absurd (Subsingleton.elim a 0) ha, fun u => by simp⟩
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : B))).2 one_ne_zero
  let T : B →+ B := AddMonoidHom.id B + c.toAddMonoidHom
  have hT : ∀ u, T u = u + c u := fun u => rfl
  refine ⟨ψ.compAddMonoidHom T, ?_, ?_⟩
  · intro a ha h
    have hex : ∃ u, a * u + c (a * u) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h1 := hne 1
      have h2 := hne ω
      rw [mul_one] at h1
      rw [map_mul] at h2
      have h3 : a * (ω - c ω) = 0 := by linear_combination h2 - c ω * h1
      exact ha ((hω.mul_left_eq_zero).1 h3)
    obtain ⟨u, hu⟩ := hex
    have hs : c (a * u + c (a * u)) = a * u + c (a * u) := by
      rw [map_add (f := _), hc, add_comm]
    obtain ⟨s', hs'⟩ := (hfix _ hs hu).exists_right_inv
    have hcs : c s' = s' := by
      have h4 := congrArg c hs'
      rw [map_mul, hs, map_one] at h4
      linear_combination s' * h4 - c s' * hs'
    have h5 : T (a * (u * s')) = 1 := by
      rw [hT, ← mul_assoc, map_mul c (a * u), hcs, ← hs']
      ring
    have h6 := DFunLike.congr_fun h (u * s')
    rw [AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply, h5] at h6
    exact hψ (by simpa using h6)
  · intro u
    simp only [AddChar.compAddMonoidHom_apply, hT, hc, add_comm]

end GlobalTheory.GramCount
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocalTraceSum

open Filter Topology TensorProduct

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isOpen_lt (γ : ValueGroupWithZero K) : IsOpen {x : K | valuation K x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hγ : γ ≠ 0 := (lt_of_le_of_lt zero_le hx).ne'
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.2 ⟨γ, hγ, fun y hy => ?_⟩
  have := (valuation K).map_add_lt (x := y - x) (y := x) hy hx
  simpa using this

theorem tendsto_pow {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

variable {l : ℕ} [Fact l.Prime] [Algebra ℚ_[l] K]

variable {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

end Local

section Place

variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]

end Place

section Ext

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[l] K] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

end Ext

end GlobalTheory.LocalTraceSum
end

section

open MeasureTheory NumberField Finset

namespace GlobalTheory.RegulatorClassBound

open NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem Module
open scoped nonZeroDivisors

theorem exists_mem_box (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (c : InfinitePlace K → ℝ)
    (hc : ∑ w, (w.mult : ℝ) * c w = Real.log ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|)) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧ ∀ w : InfinitePlace K, w (a : K) < Real.exp (c w) := by
  classical
  set n := finrank ℚ K with hn_def
  have hn : 0 < n := finrank_pos
  have hN : 0 < (Ideal.absNorm I : ℝ) :=
    Nat.cast_pos.2 (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2
      (mem_nonZeroDivisors_of_ne_zero (by simpa using hI)))
  have hD : 0 < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  set X : ℝ := (Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)| with hX_def
  have hX : 0 < X := mul_pos hN hD
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI)
  let f : InfinitePlace K → NNReal := fun w => ⟨Real.exp (c w), (Real.exp_pos _).le⟩
  have hL : (minkowskiBound K J).toReal =
      (Ideal.absNorm I : ℝ) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n := by
    simp_rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis,
      volume_fundamentalDomain_latticeBasis, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.coe_toReal, ENNReal.toReal_ofNat, mixedEmbedding.finrank]
    rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]
    simp only [J, Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Real.coe_sqrt,
      coe_nnnorm, Int.norm_eq_abs]
    ring
  have hV : volume (convexBodyLT K f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hR' : (volume (convexBodyLT K f)).toReal = (convexBodyLTFactor K : ℝ) * X := by
    rw [convexBodyLT_volume, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
    congr 1
    rw [NNReal.coe_prod]
    have e : ∀ x : InfinitePlace K, ((f x ^ x.mult : NNReal) : ℝ) = Real.exp (x.mult * c x) :=
      fun x => by rw [NNReal.coe_pow, Real.exp_nat_mul]; rfl
    rw [Finset.prod_congr rfl fun x _ => e x, ← Real.exp_sum, hc, Real.exp_log hX]
  have hfin : n = 2 * nrComplexPlaces K := IsTotallyComplex.finrank K
  have hr : nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have h : minkowskiBound K J < volume (convexBodyLT K f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top K J).ne hV, hL, hR']
    have h1 : (convexBodyLTFactor K : ℝ) = Real.pi ^ nrComplexPlaces K := by
      simp [convexBodyLTFactor, hr]
    have h3 : (2 : ℝ) ^ nrComplexPlaces K < Real.pi ^ nrComplexPlaces K :=
      pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) (by omega)
    have h4 : (2 : ℝ)⁻¹ ^ nrComplexPlaces K * 2 ^ n = 2 ^ nrComplexPlaces K := by
      rw [hfin, pow_mul, ← mul_pow]; norm_num
    calc (Ideal.absNorm I : ℝ) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n
        = ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * 2 ^ n) * X := by rw [hX_def]; ring
      _ < (convexBodyLTFactor K : ℝ) * X := by
        rw [h4, h1]; exact mul_lt_mul_of_pos_right h3 hX
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt K J h
  rw [Units.val_mk0, FractionalIdeal.mem_coeIdeal] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  refine ⟨x, hx, fun h0 => hne (by rw [h0, map_zero]), fun w => ?_⟩
  exact hlt w

theorem sum_mult_log (K : Type) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0) :
    ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w (a : K)) =
      Real.log (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  have ha' : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha
  have h := prod_eq_abs_norm (a : K)
  have h2 : (Ideal.absNorm (Ideal.span {a}) : ℝ) = ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) := by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast; rfl
  rw [h2, ← h, Real.log_prod (fun w _ => pow_ne_zero _ (pos_iff.2 ha').ne')]
  simp [Real.log_pow]

theorem regulator_le_sum_class : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → ∀ (C : ClassGroup (𝓞 K)) (S : Finset (Ideal (𝓞 K))), (∀ I, I ∈ S ↔ ∃ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)), ClassGroup.mk0 ⟨I, hI⟩ = C ∧ (Ideal.absNorm I : ℝ) ≤ Real.sqrt |(discr K : ℝ)|) → Units.regulator K ≤ ∑ I ∈ S, Real.log (Real.sqrt |(discr K : ℝ)| / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) := by
  intro K _ _ hK C S hS
  classical
  set Y := Real.sqrt |(discr K : ℝ)| with hY
  have hD : 0 < Y := Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  obtain ⟨⟨J, hJ⟩, hJC⟩ := ClassGroup.mk0_surjective C⁻¹
  have hJ0 : J ≠ ⊥ := nonZeroDivisors.ne_zero hJ
  have hpos : ∀ I : Ideal (𝓞 K), I ∈ (Ideal (𝓞 K))⁰ → 0 < (Ideal.absNorm I : ℝ) := fun I hI =>
    Nat.cast_pos.2 (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2 hI)
  have hgen : ∀ I : Ideal (𝓞 K), ∃ y : 𝓞 K,
      (∃ x : 𝓞 K, Ideal.span {x} = J * I) → Ideal.span {y} = J * I := by
    intro I
    by_cases h : ∃ x : 𝓞 K, Ideal.span {x} = J * I
    · obtain ⟨x, hx⟩ := h
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose y hy using hgen
  let a : Ideal (𝓞 K) → logSpace K := fun I w => (w.1.mult : ℝ) * Real.log (w.1 (y I : K))
  let A : Ideal (𝓞 K) → Set (logSpace K) := fun I =>
    {t | (∀ i, a I i ≤ t i) ∧ ∑ i, (t i - a I i) ≤ Real.log (Y / Ideal.absNorm I)}
  have hL : ∀ I ∈ S, 0 ≤ Real.log (Y / Ideal.absNorm I) := by
    intro I hI
    obtain ⟨h1, -, h2⟩ := (hS I).1 hI
    exact Real.log_nonneg ((one_le_div (hpos I h1)).2 h2)
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = Units.rank K := by
    simp [Units.rank]
  have hmeas : ∀ I, MeasurableSet (A I) := by
    intro I
    refine IsClosed.measurableSet ?_
    have h1 : IsClosed {t : logSpace K | ∀ i, a I i ≤ t i} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    exact h1.inter (isClosed_le (f := fun t : logSpace K => ∑ i, (t i - a I i))
      (by fun_prop) continuous_const)
  have hcov : ∀ t : logSpace K, ∃ I ∈ S, ∃ l ∈ unitLattice K, t + l ∈ A I := by
    intro t
    let b : InfinitePlace K → ℝ := fun w =>
      if h : w = w₀ then Real.log ((Ideal.absNorm J : ℝ) * Y) - ∑ i, t i else t ⟨w, h⟩
    have hb : ∀ i : {w : InfinitePlace K // w ≠ w₀}, b i.1 = t i := fun i => dif_neg i.2
    have hbsum : ∑ w, b w = Real.log ((Ideal.absNorm J : ℝ) * Y) := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
      simp only [hb]
      simp [b]
    have hm : ∀ w : InfinitePlace K, (0 : ℝ) < w.mult := fun w => Nat.cast_pos.2 mult_pos
    have hbc : ∀ w : InfinitePlace K, (w.mult : ℝ) * (b w / w.mult) = b w := fun w =>
      mul_div_cancel₀ _ (hm w).ne'
    obtain ⟨x, hxJ, hx0, hx⟩ := exists_mem_box K J hJ0 (fun w => b w / w.mult)
      (by simp only [hbc]; exact hbsum)
    have hx0' : (x : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hx0
    have hs : ∀ w : InfinitePlace K, 0 ≤ b w - (w.mult : ℝ) * Real.log (w (x : K)) := by
      intro w
      have h1 : Real.log (w (x : K)) ≤ b w / w.mult :=
        (Real.log_le_iff_le_exp (pos_iff.2 hx0')).2 (hx w).le
      have := mul_le_mul_of_nonneg_left h1 (hm w).le
      rw [hbc] at this
      linarith
    obtain ⟨I, hI⟩ : J ∣ Ideal.span {x} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxJ)
    have hI0 : I ∈ (Ideal (𝓞 K))⁰ := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      rintro rfl
      rw [mul_zero] at hI
      exact hx0 (Ideal.span_singleton_eq_bot.1 hI)
    have hsum : ∑ w : InfinitePlace K, (b w - (w.mult : ℝ) * Real.log (w (x : K))) =
        Real.log (Y / Ideal.absNorm I) := by
      rw [Finset.sum_sub_distrib, hbsum, sum_mult_log K x hx0, hI, map_mul, Nat.cast_mul,
        Real.log_mul (hpos J hJ).ne' hD.ne', Real.log_mul (hpos J hJ).ne' (hpos I hI0).ne',
        Real.log_div hD.ne' (hpos I hI0).ne']
      ring
    have hIS : I ∈ S := by
      refine (hS I).2 ⟨hI0, ?_, ?_⟩
      · have : ClassGroup.mk0 ⟨J, hJ⟩ = (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹ :=
          ClassGroup.mk0_eq_mk0_inv_iff.2 ⟨x, hx0, hI.symm⟩
        rw [hJC] at this
        exact (inv_injective this).symm
      · have h0 : 0 ≤ Real.log (Y / Ideal.absNorm I) :=
          hsum ▸ Finset.sum_nonneg fun w _ => hs w
        have := (Real.log_nonneg_iff (div_pos hD (hpos I hI0))).1 h0
        exact (one_le_div (hpos I hI0)).1 this
    have hyI : Ideal.span {x} = Ideal.span {y I} := hI.trans (hy I ⟨x, hI⟩).symm
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 hyI
    have key : ∀ i : {w : InfinitePlace K // w ≠ w₀},
        (t + logEmbedding K (Additive.ofMul u)) i - a I i =
          b i.1 - (i.1.mult : ℝ) * Real.log (i.1 (x : K)) := by
      intro i
      have h1 : ((y I : 𝓞 K) : K) = (x : K) * ((u : 𝓞 K) : K) := by
        rw [← hu]; simp
      simp only [a, Pi.add_apply, logEmbedding_component, hb, h1, map_mul]
      rw [Real.log_mul (pos_iff.2 hx0').ne' (Units.pos_at_place u i.1).ne']
      ring
    refine ⟨I, hIS, logEmbedding K (Additive.ofMul u), ⟨Additive.ofMul u, trivial, rfl⟩, ?_, ?_⟩
    · intro i
      have := hs i.1
      rw [← key] at this
      linarith
    · simp only [key]
      rw [← hsum, Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K)]
      linarith [hs w₀]
  have h1 := GlobalTheory.covolume_le_sum_volume_of_cover _ (unitLattice K) _ S A hmeas hcov
  have h2 : ∑ I ∈ S, volume (A I) ≤ ∑ I ∈ S, ENNReal.ofReal
      (Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ)) := by
    refine Finset.sum_le_sum fun I hI => ?_
    have := GlobalTheory.SimplexVolume.volume_simplex_le _ (a I) _ (hL I hI)
    rw [hcard] at this
    exact this
  have hnn : ∀ I ∈ S, 0 ≤
      Real.log (Y / Ideal.absNorm I) ^ Units.rank K / ((Units.rank K).factorial : ℝ) :=
    fun I hI => div_nonneg (pow_nonneg (hL I hI) _) (Nat.cast_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg hnn] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hnn)).1 (h1.trans h2)

end GlobalTheory.RegulatorClassBound
end

section

open Matrix

namespace GlobalTheory

open ReciprocityTheory.Aut

theorem unitary_conjugator_of_split_idempotents :
  ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m n : ℕ) (ι : Type) [Fintype ι] (ε : ι → R), (∀ j, ε j * ε j = ε j) → (∀ j, ε j * σ (ε j) = 0) → (∀ j k, j ≠ k → ε j * ε k = 0 ∧ ε j * σ (ε k) = 0) → ∀ (Z P : Matrix (Fin m) (Fin n) R) (Z' P' : Matrix (Fin n) (Fin m) R), Z * Z' = 1 → Z' * Z = 1 → P * P' = 1 → P' * P = 1 → ∃ c : GL (Fin n) R, (c : Matrix (Fin n) (Fin n) R) * ReciprocityTheory.Aut.conjT σ (c : Matrix (Fin n) (Fin n) R) = 1 ∧ ∀ j, ε j • (Z * (c : Matrix (Fin n) (Fin n) R)) = ε j • P ∧ ε j • (((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * Z') = ε j • P' := by
  intro R _ σ hσ m n ι _ ε hidem hself hcross Z P Z' P' hZZ' hZ'Z hPP' hP'P
  classical

  obtain ⟨e, he⟩ : ∃ e : R, e = ∑ j, ε j := ⟨_, rfl⟩
  have hje : ∀ j, ε j * e = ε j := by
    intro j
    rw [he, Finset.mul_sum, Finset.sum_eq_single j (fun k _ hk => (hcross j k (Ne.symm hk)).1)
      (fun h => absurd (Finset.mem_univ j) h), hidem]
  have hjse : ∀ j, ε j * σ e = 0 := by
    intro j

    rw [he, map_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hk : j = k
    · subst hk; exact hself j
    · exact (hcross j k hk).2
  have hee : e * e = e := by
    nth_rewrite 1 [he]
    rw [Finset.sum_mul]
    simp only [hje]
    exact he.symm
  have hese : e * σ e = 0 := by
    nth_rewrite 1 [he]
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero (fun j _ => hjse j)
  obtain ⟨e', he'⟩ : ∃ e' : R, e' = σ e := ⟨_, rfl⟩
  rw [← he'] at hese hjse
  have he'e' : e' * e' = e' := by rw [he', ← map_mul, hee]
  have he'e : e' * e = 0 := by rw [mul_comm, hese]
  have hσe' : σ e' = e := by rw [he', hσ]
  obtain ⟨f, hf⟩ : ∃ f : R, f = 1 - e - e' := ⟨_, rfl⟩
  have hσf : σ f = f := by rw [hf, map_sub, map_sub, map_one, hσe', ← he']; ring
  have hfe : f * e = 0 := by rw [hf]; linear_combination -hee - he'e
  have hfe' : f * e' = 0 := by rw [hf]; linear_combination -hese - he'e'
  have hff : f * f = f := by rw [hf]; linear_combination hee + he'e' + 2 * hese
  have hef : e * f = 0 := by rw [mul_comm, hfe]
  have he'f : e' * f = 0 := by rw [mul_comm, hfe']
  have hee'' : e * e' = 0 := hese
  have hsum : f + e + e' = 1 := by rw [hf]; ring

  have cadd : ∀ A B : Matrix (Fin n) (Fin n) R, conjT σ (A + B) = conjT σ A + conjT σ B := by
    intro A B; ext i j; simp [conjT]
  have csmul : ∀ (a : R) (A : Matrix (Fin n) (Fin n) R), conjT σ (a • A) = σ a • conjT σ A := by
    intro a A; ext i j; simp [conjT]
  set X : Matrix (Fin n) (Fin n) R := Z' * P with hX
  set Y : Matrix (Fin n) (Fin n) R := conjT σ (P' * Z) with hY
  set c : Matrix (Fin n) (Fin n) R := f • (1 : Matrix (Fin n) (Fin n) R) + e • X + e' • Y with hc
  have hcT : conjT σ c = f • (1 : Matrix (Fin n) (Fin n) R) + e' • conjT σ X + e • (P' * Z) := by
    rw [hc, cadd, cadd, csmul, csmul, csmul, conjT_one, hσf, hY, conjT_conjT σ hσ, hσe', ← he']
  have hXY : X * conjT σ Y = 1 := by
    rw [hY, conjT_conjT σ hσ, hX, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul, hZ'Z]
  have hYX : Y * conjT σ X = 1 := by
    rw [hY, ← conjT_mul, ← hXY, hY, conjT_conjT σ hσ]
    rw [hX, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul, hZ'Z, conjT_one]
  have hcc : c * conjT σ c = 1 := by
    rw [hcT, hc]
    have hYeq : P' * Z = conjT σ Y := by rw [hY, conjT_conjT σ hσ]
    rw [hYeq]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hff, hfe, hfe', hef, he'f, hee, hee'', he'e, he'e', zero_smul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, hXY, hYX, smul_add]
    conv_rhs => rw [← one_smul R (1 : Matrix (Fin n) (Fin n) R), ← hsum]
    simp only [add_smul]
    abel
  have hcc' : conjT σ c * c = 1 := mul_eq_one_comm.mp hcc
  refine ⟨⟨c, conjT σ c, hcc, hcc'⟩, hcc, fun j => ⟨?_, ?_⟩⟩
  · show ε j • (Z * c) = ε j • P
    have hjf : ε j * f = 0 := by
      rw [hf]; linear_combination -hje j - hjse j
    rw [hc, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul, hjf, hje, hjse, zero_smul, zero_smul,
      zero_add, add_zero, hX, ← Matrix.mul_assoc, hZZ', Matrix.one_mul]
  · show ε j • (conjT σ c * Z') = ε j • P'
    have hjf : ε j * f = 0 := by
      rw [hf]; linear_combination -hje j - hjse j
    rw [hcT, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul, hjf, hje, hjse, zero_smul, zero_smul,
      zero_add, zero_add, Matrix.mul_assoc, hZZ', Matrix.mul_one]

end GlobalTheory
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory.SplitProj

theorem proj_eq_lift_compAt (L : Type) [Field L] [NumberField L] (s : SplitPlace L) (x : AL L) :
    s.proj x = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)) (compAt L s.v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

theorem proj_eq_zero_of_compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] (s : ReciprocityTheory.Aut.SplitPlace L)
    (a : ReciprocityTheory.Aut.AL L), ReciprocityTheory.Aut.compAt L s.v a = 0 → s.proj a = 0 := by
  intro L _ _ s a h
  rw [proj_eq_lift_compAt, h, map_zero]

end GlobalTheory.SplitProj
end
