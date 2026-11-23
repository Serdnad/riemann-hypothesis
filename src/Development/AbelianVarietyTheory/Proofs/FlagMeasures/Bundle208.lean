module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle202
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle036
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle145
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle146
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle187
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle142
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle107
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle188
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.SkewFund

open GlobalTheory.HomCovolume

theorem one_le_covolume {ι : Type} [Fintype ι] (A : Submodule ℤ (ι → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A]
    (h : ∀ x ∈ A, x ≠ 0 → 1 ≤ ‖x‖) : 1 ≤ ZLattice.covolume A volume := by
  by_contra hlt
  rw [not_le] at hlt
  have : Countable A.toAddSubgroup := inferInstanceAs (Countable A)
  have hF : IsAddFundamentalDomain A.toAddSubgroup (latticeDomain A) volume :=
    isAddFundamentalDomain_latticeDomain A volume
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF
    (s := Metric.ball 0 1) (fun x hx => by simpa using hx) (convex_ball _ _) (by
      rw [measure_latticeDomain, Real.volume_pi_ball _ one_pos, Module.finrank_fintype_fun_eq_card,
        mul_one, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
      calc _ < 1 * 2 ^ Fintype.card ι :=
            ENNReal.mul_lt_mul_left (by simp) (by simp) (ENNReal.ofReal_lt_one.2 hlt)
        _ = _ := one_mul _)
  exact absurd (h x x.2 (fun h0 => hx0 (Subtype.ext h0))) (by simpa using hx)

theorem imag_covolume {ι : Type} [Fintype ι] (L : Submodule ℤ (ι → ℂ)) {c : ℝ} (hc : HasCov volume L c)
    (hs : ∀ z ∈ L, (fun v => starRingEnd ℂ (z v)) ∈ L) (hn : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) :
    ∃ B : Submodule ℤ (ι → ℝ), (∀ y, y ∈ B ↔ (fun v => (⟨0, y v⟩ : ℂ)) ∈ L) ∧
      ∃ b, HasCov volume B b ∧ 1 ≤ b ∧ b ≤ 2 ^ Fintype.card ι * c := by
  let e : ((ι → ℝ) × (ι → ℝ)) ≃L[ℝ] (ι → ℂ) := LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p v => ⟨p.1 v, p.2 v⟩
      invFun := fun z => (fun v => (z v).re, fun v => (z v).im)
      map_add' := fun p q => by ext v; apply Complex.ext <;> simp
      map_smul' := fun c p => by ext v; apply Complex.ext <;> simp
      left_inv := fun p => rfl
      right_inv := fun z => rfl }
  have he : ∀ p v, e p v = ⟨p.1 v, p.2 v⟩ := fun _ _ => rfl
  have hmp : MeasurePreserving e (Measure.prod volume volume) volume :=
    (volume_preserving_pi (ι := ι) fun _ => Complex.volume_preserving_equiv_real_prod.symm).comp
      (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι).symm
  let M : Submodule ℤ ((ι → ℝ) × (ι → ℝ)) := L.comap (e.toLinearMap.restrictScalars ℤ)
  have hM : ∀ p, p ∈ M ↔ e p ∈ L := fun _ => Iff.rfl
  have : ((volume : Measure (ι → ℝ)).prod (volume : Measure (ι → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨_, _, hcM⟩ := HasCov.of_measurePreserving e hmp hM hc
  let A : Submodule ℤ (ι → ℝ) := M.comap (LinearMap.inl ℤ _ _)
  let B : Submodule ℤ (ι → ℝ) := M.comap (LinearMap.inr ℤ _ _)
  obtain ⟨⟨_, _⟩, ⟨_, _⟩, h⟩ := GlobalTheory.ReImLattice.reflection_stable volume M (fun p hp => by
    rw [hM] at hp ⊢
    convert hs _ hp using 1
    ext v; apply Complex.ext <;> simp [he]) A B (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have key : ∀ (x : ι → ℝ) (z : ι → ℂ), z ∈ L → (∀ v, ‖z v‖ = ‖x v‖) → x ≠ 0 → 1 ≤ ‖x‖ := by
    intro x z hz hzx hx
    have h1 : ‖z‖ = ‖x‖ := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_)
        ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_)
      · rw [hzx]; exact norm_le_pi_norm x v
      · rw [← hzx]; exact norm_le_pi_norm z v
    rw [← h1]
    exact hn z hz (by rw [← norm_ne_zero_iff, h1]; exact norm_ne_zero_iff.2 hx)
  have hA : 1 ≤ ZLattice.covolume A volume := one_le_covolume A fun x hx =>
    key x (e (x, 0)) hx fun v => by
      have : e (x, 0) v = (x v : ℂ) := rfl
      rw [this, Complex.norm_real]
  have hB : 1 ≤ ZLattice.covolume B volume := one_le_covolume B fun x hx =>
    key x (e (0, x)) hx fun v => by
      have : e (0, x) v = (x v : ℂ) * Complex.I := by apply Complex.ext <;> simp [he]
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  refine ⟨B, fun _ => Iff.rfl, _, ⟨inferInstance, inferInstance, rfl⟩, hB, ?_⟩
  rw [hcM, Module.finrank_fintype_fun_eq_card] at h
  exact (le_mul_of_one_le_left (zero_le_one.trans hB) hA).trans h

theorem prod_norm_sq (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K) {ι : Type} [Fintype ι]
    (σ : ι → (K →+* ℂ)) (hσ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w) (t : K) :
    ∏ v, ‖σ v t‖ ^ 2 = ((|Algebra.norm ℚ t| : ℚ) : ℝ) := by
  rw [← InfinitePlace.prod_eq_abs_norm]
  refine Fintype.prod_bijective _ ((Function.bijective_iff_existsUnique _).2 hσ) _ _ fun v => ?_
  rw [InfinitePlace.mult_isComplex ⟨_, hK.isComplex _⟩, InfinitePlace.apply]

theorem exists_fund_skew : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)), IsPlaces σ → ∀ (𝔡 : Ideal (𝓞 K)) (n : ℕ), 𝔡 ≠ ⊥ → (∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) → (Ideal.absNorm 𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∃ F : Set (ι → ℝ), MeasurableSet F ∧ (∀ a : ι → ℝ, ∃! t : K, (t ∈ ipow 𝔡 (-(2 * (n : ℤ))) ∧ t + star t = 0) ∧ ((fun v => (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * n) * (σ v t).im) + a) ∈ F) ∧ ENNReal.ofReal ((8 * Formalism.HermitianLatticesTheory.vInv K) ^ (-(Fintype.card ι : ℝ))) ≤ volume F ∧ volume F ≤ ENNReal.ofReal ((8 * Formalism.HermitianLatticesTheory.vInv K) ^ (Fintype.card ι : ℝ)) := by
  intro K _ _ _ hK ι _ σ hσ 𝔡 n h𝔡 hs hN hv
  set v₀ := Formalism.HermitianLatticesTheory.vInv K with hv₀
  set c : ℝ := (2 * v₀) ^ (2 * n) with hc
  have hc0 : 0 < c := by positivity
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔡
  obtain ⟨L₀, hL₀, hcov⟩ := GlobalTheory.IdealFund.exists_lat K hK.1 ι σ hσ.2 _ (zpow_ne_zero (-(2 * (n : ℤ))) h0)
  have hNa : ((FractionalIdeal.absNorm ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(2 * (n : ℤ)))) : ℚ) : ℝ) =
      c⁻¹ ^ (2 * Fintype.card ι) := by
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    rw [hN, _root_.zpow_neg, inv_pow, hc, show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; rfl, _root_.zpow_natCast,
      ← pow_mul, ← pow_mul, mul_comm (2 * n)]
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := c⁻¹ • LinearMap.id
  have hf : ∀ z v, f z v = (c : ℂ)⁻¹ * z v := fun _ _ => by simp [f]
  have hdet : LinearMap.det f = c⁻¹ ^ (2 * Fintype.card ι) := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_pi_fintype]
    simp [mul_comm]
  have hpos : 0 < c⁻¹ ^ (2 * Fintype.card ι) := by positivity
  let L : Submodule ℤ (ι → ℂ) := L₀.comap (f.restrictScalars ℤ)
  have h := HasCov.of_det f (L := L) (by rw [hdet]; exact hpos.ne') (fun _ => Iff.rfl) hcov
  rw [hNa, hdet, abs_of_pos hpos, mul_div_cancel_left₀ _ hpos.ne'] at h
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hL : ∀ z, z ∈ L ↔ ∃ t ∈ ipow 𝔡 (-(2 * (n : ℤ))), z = fun v => c * σ v t := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => funext fun v => ?_, fun h v => ?_⟩
    · rw [← h, hf, mul_inv_cancel_left₀ hcc]
    · rw [hf, h, inv_mul_cancel_left₀ hcc]
  obtain ⟨B, hB, b, ⟨_, _, hb⟩, hb1, hb2⟩ := imag_covolume L h (fun z hz => by
    obtain ⟨t, ht, rfl⟩ := (hL z).1 hz
    exact (hL _).2 ⟨star t, IdealPow.star_mem h𝔡 hs ht, funext fun v => by simp [hσ.1]⟩) (fun z hz hz0 => by
    obtain ⟨t, ht, rfl⟩ := (hL z).1 hz
    have ht0 : t ≠ 0 := by rintro rfl; exact hz0 (funext fun v => by simp)
    have h1 : c⁻¹ ^ (2 * Fintype.card ι) ≤ ∏ v, ‖σ v t‖ ^ 2 := by
      rw [← hNa, prod_norm_sq K hK.1 σ hσ.2]
      exact_mod_cast GlobalTheory.absNorm_le_abs_norm_of_mem ht ht0
    by_contra hlt
    rw [not_le, pi_norm_lt_iff one_pos] at hlt
    obtain ⟨u, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
    refine absurd h1 (not_le.2 ?_)
    rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_lt_prod_of_nonempty₀ (fun v _ => pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 ht0)) _)
      (fun v _ => pow_lt_pow_left₀ ?_ (norm_nonneg _) two_ne_zero) ⟨u, Finset.mem_univ _⟩
    have := hlt v
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at this
    rwa [← one_mul c⁻¹, lt_mul_inv_iff₀ hc0, mul_comm])
  obtain ⟨u, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
  have hre : ∀ t : K, t + star t = 0 → ∀ v, (σ v t).re = 0 := fun t ht v => by
    have := congrArg (fun x => (σ v x).re) ht
    simp only [map_add (f := _), hσ.1, map_zero, Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    linarith
  have hB' : ∀ y, y ∈ B ↔ ∃ t : K, (t ∈ ipow 𝔡 (-(2 * (n : ℤ))) ∧ t + star t = 0) ∧
      y = fun v => c * (σ v t).im := by
    intro y
    rw [hB, hL]
    constructor
    · rintro ⟨t, ht, hy⟩
      refine ⟨t, ⟨ht, (σ u).injective ?_⟩, funext fun v => by simpa using congrArg Complex.im (congrFun hy v)⟩
      have h1 : (σ u t).re = 0 := by simpa [hc0.ne'] using congrArg Complex.re (congrFun hy u)
      rw [map_add (f := _), hσ.1, map_zero]
      apply Complex.ext <;> simp [h1]
    · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
      exact ⟨t, ht, funext fun v => by apply Complex.ext <;> simp [hre t ht']⟩
  refine ⟨latticeDomain B, measurableSet_latticeDomain B, fun a => ?_, ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := existsUnique_add_mem_latticeDomain B a
    obtain ⟨t, ht, hzt⟩ := (hB' z).1 z.2
    refine ⟨t, ⟨ht, by rw [← hzt, add_comm]; exact hz⟩, ?_⟩
    rintro t' ⟨ht', h'⟩
    have h1 := hu ⟨_, (hB' _).2 ⟨t', ht', rfl⟩⟩ (by rw [add_comm] at h'; exact h')
    have h2 := congrFun ((congrArg Subtype.val h1).trans hzt) u
    exact (σ u).injective (Complex.ext (by rw [hre t ht.2, hre t' ht'.2]) (mul_left_cancel₀ hc0.ne' h2))
  · rw [measure_latticeDomain, hb]
    exact ENNReal.ofReal_le_ofReal ((Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simp)).trans hb1)
  · rw [measure_latticeDomain, hb, Real.rpow_natCast]
    refine ENNReal.ofReal_le_ofReal (hb2.trans ?_)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _

end GlobalTheory.SkewFund
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TypesCS

theorem count_le (r a : ℕ) (H : ℝ) (ha : 1 ≤ a) (hH : (2 : ℝ) ^ a ≤ H) :
    ((a + a * (r * a) : ℕ) : ℝ) ≤ H ^ (r + 2) := by
  have hnat : a + a * (r * a) ≤ 2 ^ (a * (r + 2)) := by
    have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2 : r * a < 2 ^ (r * a) := Nat.lt_two_pow_self
    calc a + a * (r * a) = a * (1 + r * a) := by ring
      _ ≤ 2 ^ a * 2 ^ (r * a) := Nat.mul_le_mul h1.le (by omega)
      _ = 2 ^ (a + r * a) := (pow_add 2 a (r * a)).symm
      _ ≤ 2 ^ (a * (r + 2)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc ((a + a * (r * a) : ℕ) : ℝ) ≤ ((2 ^ (a * (r + 2)) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ((2 : ℝ) ^ a) ^ (r + 2) := by push_cast; rw [pow_mul]
    _ ≤ H ^ (r + 2) := by gcongr

theorem ampSq_le_of_types : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ B : ℝ≥0∞, (∀ β, (S.ampSq fun d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = β) ≤ B) → (∀ β J βJ, S.ampSq (S.InFF β J βJ) ≤ B) → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk B hB1 hB2
  have hk1 : 1 ≤ k := by omega
  have hq2 : 2 ≤ S.q := GlobalTheory.HL.LevelFamilies.two_le_resQ S.ϖ S.ϖ_irr
  by_cases hex : ∃ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ
  swap
  ·
    simp only [not_exists] at hex
    have h0 := GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 (∅ : Finset ℕ)
      (fun _ _ _ => False) (fun d Λ => ¬ S.BBzero d Λ)
      (fun d Λ ht => absurd ht (hex d Λ)) (fun d Λ ht => absurd ht (hex d Λ))
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul] at h0
    exact h0.trans zero_le
  obtain ⟨d₀, Λ₀, ht₀⟩ := hex
  obtain ⟨ha0, -, -, hqa, hHp1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht₀
  obtain ⟨A, hAa⟩ : ∃ A : ℕ, (A : ℤ) = S.a := ⟨_, Int.toNat_of_nonneg ha0⟩

  let s : Finset (ℕ ⊕ (ℕ × ℕ × ℕ)) :=
    (Finset.Icc 1 A).disjSum
      ((Finset.Icc 1 A ×ˢ Finset.Icc 1 r ×ˢ Finset.range A).filter fun t => t.2.2 < t.1)
  let P : ℕ ⊕ (ℕ × ℕ × ℕ) → S.Datum → Submodule L.O S.V → Prop := fun x =>
    Sum.elim (fun i d Λ => ¬ S.BBzero d Λ ∧ ¬ S.TypeBe d Λ ∧ S.be d Λ = S.q ^ i)
      (fun t => S.InFF (S.q ^ t.1) t.2.1 (S.q ^ t.1 - S.q ^ t.2.2)) x
  have hinj : ∀ m n : ℕ, S.q ^ m = S.q ^ n → m = n := fun m n h =>
    Nat.pow_right_injective hq2 h
  have hcover : ∀ d Λ, S.IsTerm d Λ → ((¬ S.BBzero d Λ) ↔ ∃ x ∈ s, P x d Λ) := by
    intro d Λ ht
    obtain ⟨-, -, -, -, -, ⟨i, hia, hbe⟩, hBB, -⟩ :=
      GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ ht
    constructor
    · intro hnz
      have hi1 : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · exact absurd (hBB.mpr (by rw [hbe, h, pow_zero])) hnz
        · exact h
      by_cases hT : S.TypeBe d Λ
      · obtain ⟨i₁, J, i', h1, h1a, hJ1, hJr, hi', hF⟩ :=
          GlobalTheory.HL.LevelFamilies.exists_family L r k S d Λ ht hT
        refine ⟨Sum.inr (i₁, J, i'), ?_, hF⟩
        simp only [s, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_range]
        omega
      · refine ⟨Sum.inl i, ?_, hnz, hT, hbe⟩
        simp only [s, Finset.inl_mem_disjSum, Finset.mem_Icc]
        omega
    · rintro ⟨x, -, hx⟩
      rcases x with i | ⟨i, J, i'⟩
      · exact hx.1
      · exact hx.1.1
  have hdisj : ∀ d Λ, S.IsTerm d Λ → ∀ x ∈ s, ∀ y ∈ s, P x d Λ → P y d Λ → x = y := by
    intro d Λ _ x hx y hy hPx hPy
    rcases x with i | ⟨i, J, i'⟩ <;> rcases y with j | ⟨j, J', j'⟩ <;>
      dsimp only [P, Sum.elim_inl, Sum.elim_inr] at hPx hPy
    · exact congrArg Sum.inl (hinj _ _ (hPx.2.2.symm.trans hPy.2.2))
    · exact absurd hPy.1 hPx.2.1
    · exact absurd hPx.1 hPy.2.1
    · obtain ⟨-, hb, hle, ⟨y₀, hy₀, hlev⟩, hn⟩ := hPx
      obtain ⟨-, hb', hle', ⟨y₁, hy₁, hlev'⟩, hn'⟩ := hPy
      have hij : i = j := hinj _ _ (hb.symm.trans hb')
      subst hij
      have hJJ : J = J' := le_antisymm (hlev ▸ hle' y₀ hy₀) (hlev' ▸ hle y₁ hy₁)
      subst hJJ
      simp only [s, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range] at hx hy
      have hlt1 : S.q ^ i' ≤ S.q ^ i := Nat.pow_le_pow_right (by omega) hx.2.le
      have hlt2 : S.q ^ j' ≤ S.q ^ i := Nat.pow_le_pow_right (by omega) hy.2.le
      have hpow : S.q ^ i' = S.q ^ j' := by
        generalize S.q ^ i' = u at hn hlt1
        generalize S.q ^ j' = v at hn' hlt2
        generalize S.q ^ i = w at hn hn' hlt1 hlt2
        omega
      rw [hinj _ _ hpow]
  have hmain := GlobalTheory.AmpCS.ampSq_le_card_mul_sum L r k S hk1 s P (fun d Λ => ¬ S.BBzero d Λ)
    hcover hdisj
  have hsumB : ∑ x ∈ s, S.ampSq (P x) ≤ s.card * B := by
    have hle : ∀ x ∈ s, S.ampSq (P x) ≤ B := by
      intro x _
      rcases x with i | ⟨i, J, i'⟩
      · exact hB1 _
      · exact hB2 _ _ _
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul s (fun x => S.ampSq (P x)) B hle
  have hcard : s.card ≤ A + A * (r * A) := by
    simp only [s, Finset.card_disjSum, Nat.card_Icc, Nat.add_sub_cancel]
    have h := Finset.card_filter_le (Finset.Icc 1 A ×ˢ Finset.Icc 1 r ×ˢ Finset.range A)
      (fun t => t.2.2 < t.1)
    simp only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, Finset.card_range] at h
    omega
  have hHp0 : 0 ≤ S.Hp := le_trans zero_le_one hHp1
  have hreal : ((s.card : ℕ) : ℝ) ≤ S.Hp ^ (r + 2) := by
    rcases Nat.eq_zero_or_pos A with hA | hA
    · have : s.card = 0 := by rw [hA] at hcard; simpa using hcard
      rw [this, Nat.cast_zero]
      positivity
    · have h2A : (2 : ℝ) ^ A ≤ S.Hp :=
        calc (2 : ℝ) ^ A ≤ (S.q : ℝ) ^ A := by gcongr; exact_mod_cast hq2
          _ = (S.q : ℝ) ^ S.a := by rw [← hAa, zpow_natCast]
          _ ≤ S.Hp := hqa
      calc ((s.card : ℕ) : ℝ) ≤ ((A + A * (r * A) : ℕ) : ℝ) := by exact_mod_cast hcard
        _ ≤ S.Hp ^ (r + 2) := count_le r A S.Hp hA h2A
  have hN : ((s.card : ℝ≥0∞) * s.card) ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [pow_mul', sq]
    exact mul_le_mul hreal hreal (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hreal)
  calc (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ s.card * ∑ x ∈ s, S.ampSq (P x) := hmain
    _ ≤ s.card * (s.card * B) := by gcongr
    _ = (s.card * s.card) * B := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (S.Hp ^ (2 * (r + 2))) * B := by gcongr

end GlobalTheory.HL.TypesCS
end

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

open Inhab GlobalTheory.Mem.RowsBundle

theorem hAf_add_left (I : AutInst) (x x' y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (x + x') y = hAf I x y + hAf I x' y := by
  unfold hAf Formalism.UG.hform
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hAf_smul_left (I : AutInst) (a : I.E ⊗[I.F] Af I.F) (x y : Fin I.n → (I.E ⊗[I.F] Af I.F)) :
    hAf I (a • x) y = Formalism.UG.sigR I.cm.sig (Af I.F) a * hAf I x y := by
  unfold hAf Formalism.UG.hform
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

theorem mapsTo_conj_of_adjoint (I : AutInst) (w w' : HeightOneSpectrum (𝓞 I.E))
    (T T' : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (hc : IsConj I w w')
    (hadj : ∀ x y, hAf I (T' *ᵥ x) y = hAf I x (T *ᵥ y))
    (hT' : ∀ y ∈ I.Lf, T' *ᵥ y ∈ extId I w.asIdeal • I.Lf) :
    ∀ y ∈ I.Lf, T *ᵥ y ∈ extId I w'.asIdeal • I.Lf := by
  intro y hy
  rw [DualIdeal.mem_extId_smul_iff I _ w'.ne_bot]
  intro y' hy'
  rw [← hadj]
  have key : ∀ u ∈ extId I w.asIdeal • I.Lf, ∃ z ∈ extId I w'.asIdeal,
      (z : I.E ⊗[I.F] Af I.F) = hAf I u y := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha l hl => ?_) (fun u u' hu hu' => ?_)
    · obtain ⟨a', ha', e⟩ := (extId_mul_sup_natCast_conj I).2.2.2.2.2.2 w w' hc a ha
      refine ⟨a' * ⟨_, (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 hy l hl⟩, Ideal.mul_mem_right _ _ ha', ?_⟩
      rw [Subring.coe_mul, e]
      show _ = hAf I ((a : I.E ⊗[I.F] Af I.F) • l) y
      rw [hAf_smul_left]
    · obtain ⟨z, hz, e⟩ := hu
      obtain ⟨z', hz', e'⟩ := hu'
      exact ⟨z + z', add_mem hz hz', by rw [Subring.coe_add, e, e', hAf_add_left]⟩
  exact key _ (hT' y' hy')

theorem PlFrame.trivial_iff {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
    {x : I.Gf} (hx : x ∈ I.Kset) :
    (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y) ↔
      ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I w.asIdeal • I.Lf := by
  have key : ∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = fr.c y ↔
      (I.fmat x - 1) *ᵥ (y : Fin I.n → _) ∈ extId I w.asIdeal • I.Lf := by
    intro y h
    rw [← sub_eq_zero, ← map_sub, fr.c_ker, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  exact ⟨fun H y hy => (key ⟨y, hy⟩ (mulVec_mem hx hy)).1 (H _ _), fun H y h => (key y h).2 (H y.1 y.2)⟩

theorem IsChoice.isRadical_mul {I : AutInst} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type}
    {w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)} (hC : IsChoice I g Pl w) :
    (Ideal.span {((g 0 * g 1 : ℕ) : 𝓞 I.E)}).IsRadical := by
  have hc : Nat.Coprime (g 0) (g 1) := (Nat.coprime_primes (hC.1 0) (hC.1 1)).2 hC.2.1
  have hc' : IsCoprime ((g 0 : ℕ) : 𝓞 I.E) ((g 1 : ℕ) : 𝓞 I.E) := Nat.Coprime.cast hc
  rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.mul_eq_inf_of_isCoprime ((Ideal.isCoprime_span_singleton_iff _ _).2 hc')]
  exact (hC.2.2.1 0).inf (hC.2.2.1 1)

theorem trivial_iff_mem_Kg : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type)
    (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)), I.n = N →
    IsChoice I g Pl w → ∀ x ∈ I.Kset, (∀ k v (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf),
      (fr k v).c ⟨_, h⟩ = (fr k v).c y) ↔ x ∈ I.Kg (g 0 * g 1) := by
  intro I N g Pl w fr _ hC x hx
  have hx' : x⁻¹ ∈ I.Kset := (Ksub I).inv_mem hx
  have hone : 1 ≤ g 0 * g 1 := Nat.mul_pos (hC.1 0).pos (hC.1 1).pos
  have hmem : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ I.Lf := fun y hy => by
    simpa using sub_one_pow_mem hx 1 hy
  have crt := fun y hy => GlobalTheory.RowLev.SqfCrt.mem_extId_smul_forall_iff I (g 0 * g 1) hone hC.isRadical_mul _ (hmem y hy)
  constructor
  · intro H
    have H1 := fun k v => ((fr k v).trivial_iff hx).1 (H k v)
    have H2 : ∀ k v, ∀ y ∈ I.Lf, (I.fmat x⁻¹ - 1) *ᵥ y ∈ extId I (w k v).asIdeal • I.Lf := by
      intro k v y hy
      have h1 : I.fmat x * I.fmat x⁻¹ = 1 := by rw [← fmat_mul, mul_inv_cancel, fmat_one]
      have h := neg_mem (H1 k v _ (mulVec_mem hx' hy))
      rw [Matrix.mulVec_mulVec, sub_mul, h1, one_mul, ← Matrix.neg_mulVec, neg_sub] at h
      exact h
    refine ⟨hx, fun y hy => (crt y hy).1 fun u hu => ?_⟩
    have hk : ∃ k, ((g k : ℕ) : 𝓞 I.E) ∈ u.asIdeal := by
      rw [Nat.cast_mul] at hu
      exact (u.isPrime.mem_or_mem hu).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨v, rfl | hv⟩ := hC.2.2.2.2.2.2 k u hk
    · exact H1 k v y hy
    · refine mapsTo_conj_of_adjoint I _ _ _ _ hv (fun a b => ?_) (H2 k v) y hy
      simpa only [pow_one] using hAf_pow_adjoint x 1 a b
  · intro H k v
    refine ((fr k v).trivial_iff hx).2 fun y hy => (crt y hy).2 (H.2 y hy) _ ?_
    have h := (hC.2.2.2.1 k v).1
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.RowLev
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (U : Submodule K V) (L L' : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → Submodule.IsFullLattice K L' → ((({η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y}).encard : ℕ∞) : ℝ≥0∞) ≤ ((4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K)) := by
  first | exact @GlobalTheory.IsoCount.isoCnt | exact GlobalTheory.IsoCount.isoCnt | (intros; apply GlobalTheory.IsoCount.isoCnt <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.prod_layer_height_quotients_eq_sq : ∀ (n f a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ) (τ : Fin a → ℝ) (h : ℕ → ℝ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → (∀ i : Fin a, 0 < τ i ∧ h i = τ i ^ (2 * f * j i) ∧ h (2 * a - i) = (τ i ^ (2 * f * j i))⁻¹) → h a = 1 → (∀ b, 2 * a + 1 ≤ b → h b = 1) → ∏ c ∈ Finset.range (2 * a + 1), ∏ b ∈ Finset.range (2 * a + 1), h b ^ r (b + c + 1) / h (b + c + 1) ^ r b = layerProd n f j τ id ^ 2 := by
  first | exact @GlobalTheory.HtProd.htProd | exact GlobalTheory.HtProd.htProd | (intros; apply GlobalTheory.HtProd.htProd <;> assumption)
end
