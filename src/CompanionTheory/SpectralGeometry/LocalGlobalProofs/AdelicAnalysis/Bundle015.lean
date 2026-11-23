module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.quadratic_setup_invariant_under_isometry : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (gi : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → (∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) → QSetup M B ρ (fun w => (gi w)ᵀ * P w * gi w) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.qsetup_conj_majorant | exact GlobalTheory.CompanionTheory.SW.ThW.qsetup_conj_majorant | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.qsetup_conj_majorant <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Red

theorem prod_sq_embedding {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (x : F) :
    ∏ w, (ρ w x) ^ 2 = ((Algebra.norm ℚ x : ℚ) : ℝ) ^ 2 := by
  have h1 := InfinitePlace.prod_eq_abs_norm x
  have h2 : ∀ w : InfinitePlace F, w x ^ w.mult = |ρ w x| := by
    intro w
    have hm : w.mult = 1 := by
      simp [InfinitePlace.mult, hF.isReal w]
    rw [hm, pow_one, ← InfinitePlace.norm_embedding_eq, ← hρ]
    simp
  have h3 : ∏ w : InfinitePlace F, |ρ w x| = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    rw [← Finset.prod_congr rfl (fun w _ => h2 w), h1]
    simp
  calc ∏ w, (ρ w x) ^ 2 = ∏ w, |ρ w x| ^ 2 := by simp
    _ = (∏ w, |ρ w x|) ^ 2 := by rw [Finset.prod_pow]
    _ = _ := by rw [h3, sq_abs]

theorem balanced_lower {ι : Type} [Fintype ι] (z : ι → ℝ) (hz : ∀ i, 0 < z i) (κ P : ℝ)
    (hκ : 0 < κ) (hbal : ∀ v w, κ * z w ≤ z v) (hprod : P ≤ ∏ i, z i) (w : ι) :
    κ * min 1 P ≤ z w := by
  by_contra h
  push_neg at h
  set q := z w / κ with hq
  have hqpos : 0 < q := div_pos (hz w) hκ
  have hqlt : q < min 1 P := by
    rw [hq, div_lt_iff₀ hκ]; linarith
  have hq1 : q ≤ 1 := (hqlt.trans_le (min_le_left _ _)).le
  have hqP : q < P := hqlt.trans_le (min_le_right _ _)
  have hle : ∀ v, z v ≤ q := by
    intro v
    rw [hq, le_div_iff₀ hκ]
    have := hbal w v
    linarith
  haveI : Nonempty ι := ⟨w⟩
  have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hp : ∏ i, z i ≤ q ^ Fintype.card ι := by
    calc ∏ i, z i ≤ ∏ _i : ι, q :=
          Finset.prod_le_prod₀ (fun i _ => (hz i).le) (fun i _ => hle i)
      _ = q ^ Fintype.card ι := by simp
  have := pow_le_of_le_one hqpos.le hq1 hcard
  linarith

theorem reduction : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ (s : Finset SL(2, F)) (κ t : ℝ), 0 < κ ∧ 0 < t ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (∀ w, t ≤ (mob ρ (r * k) τ w).im) ∧ ∀ v w, κ * (mob ρ (r * k) τ w).im ≤ (mob ρ (r * k) τ v).im := by
  intro F _ _ hF ρ hρ
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.exists_cusp_reduction_bound F hF ρ hρ
  obtain ⟨s, C₂, hrow⟩ := GlobalTheory.T.cusp_representatives_finite F
  obtain ⟨κ, hκ, hbal⟩ := GlobalTheory.T.unit_balancing_imaginary_parts F hF ρ hρ
  set n := Fintype.card (InfinitePlace F) with hn
  set A : ℝ := |C₁| + 1 with hAdef
  set B : ℝ := |C₂| + 1 with hBdef
  set P : ℝ := 1 / (A ^ n * B ^ 2) with hPdef
  have hP : 0 < P := by positivity
  refine ⟨s, κ, κ * min 1 P, hκ, mul_pos hκ (lt_min one_pos hP), ?_⟩
  intro τ hτ
  have him := (GlobalTheory.T.mobius_action_upper_half_plane F ρ τ hτ).1
  obtain ⟨c, d, hcd, hD⟩ := hC₁ τ hτ
  obtain ⟨l, hl0, hlN, hl⟩ := hrow c d hcd
  obtain ⟨r₁, -, k₁, -, h₁0, h₁1⟩ := hl 1
  have h₁0' : (r₁ * k₁) 1 0 = l * c := by simpa using h₁0
  have h₁1' : (r₁ * k₁) 1 1 = l * d := by simpa using h₁1
  set y' : InfinitePlace F → ℝ := fun w => (mob ρ (r₁ * k₁) τ w).im with hy'
  have hy'pos : ∀ w, 0 < y' w := fun w => (him _ w).2
  obtain ⟨u, hu⟩ := hbal y' hy'pos
  obtain ⟨r, hr, k, hk, h0, h1⟩ := hl u⁻¹

  set N : InfinitePlace F → ℝ := fun w =>
    ‖((ρ w (l * c) : ℝ) : ℂ) * τ w + (ρ w (l * d) : ℝ)‖ ^ 2 with hN
  have hy'eq : ∀ w, y' w = (τ w).im / N w := by
    intro w
    have := (him (r₁ * k₁) w).1
    rw [h₁0', h₁1'] at this
    exact this
  have hNpos : ∀ w, 0 < N w := by
    intro w
    have hnn : 0 ≤ N w := by positivity
    rcases hnn.lt_or_eq with h | h
    · exact h
    · have := hy'pos w
      rw [hy'eq w, ← h, div_zero] at this
      exact absurd this (lt_irrefl _)
  have hinv : ∀ w, ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ρ w ((u : 𝓞 F) : F) = 1 := by
    intro w
    rw [← map_mul]
    have : (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((u : 𝓞 F) : F) = 1 := by
      have h := congrArg (fun x : 𝓞 F => (x : F)) (Units.inv_mul u)
      simpa using h
    rw [this, map_one]
  have hz : ∀ w, (mob ρ (r * k) τ w).im = ρ w ((u : 𝓞 F) : F) ^ 2 * y' w := by
    intro w
    have hw := (him (r * k) w).1
    rw [h0, h1] at hw
    have hnorm : ‖((ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * l * c) : ℝ) : ℂ) * τ w
        + (ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * l * d) : ℝ)‖ ^ 2
        = ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) ^ 2 * N w := by
      have : ((ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * c) : ℝ) : ℂ) * τ w
          + (ρ w ((((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * l * d) : ℝ)
          = ((ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) : ℝ) : ℂ)
            * (((ρ w (l * c) : ℝ) : ℂ) * τ w + (ρ w (l * d) : ℝ)) := by
        simp only [map_mul, Complex.ofReal_mul]
        ring
      rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hw, hnorm, hy'eq w]
    have ha := hinv w
    have hNw := (hNpos w).ne'
    have ha0 : ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) ≠ 0 := left_ne_zero_of_mul_eq_one ha
    have hb : ρ w ((u : 𝓞 F) : F) = (ρ w (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F))⁻¹ :=
      eq_inv_of_mul_eq_one_right ha
    rw [hb]
    field_simp
  have hzpos : ∀ w, 0 < (mob ρ (r * k) τ w).im := fun w => (him _ w).2
  have hbal' : ∀ v w, κ * (mob ρ (r * k) τ w).im ≤ (mob ρ (r * k) τ v).im := by
    intro v w
    rw [hz v, hz w]
    exact hu v w

  have hlow : ∀ w, 1 / (A * ρ w l ^ 2) ≤ y' w := by
    intro w
    have hlw : ρ w l ≠ 0 := (map_ne_zero _).2 hl0
    have hlsq : 0 < ρ w l ^ 2 := by positivity
    have hNle : N w ≤ ρ w l ^ 2 * (A * (τ w).im) := by
      have h1' : N w = ρ w l ^ 2 * ‖((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)‖ ^ 2 := by
        have : ((ρ w (l * c) : ℝ) : ℂ) * τ w + (ρ w (l * d) : ℝ)
            = ((ρ w l : ℝ) : ℂ) * (((ρ w (c : F) : ℝ) : ℂ) * τ w + (ρ w (d : F) : ℝ)) := by
          simp only [map_mul, Complex.ofReal_mul]
          ring
        simp only [hN]
        rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [h1']
      apply mul_le_mul_of_nonneg_left _ hlsq.le
      refine (hD w).trans ?_
      apply mul_le_mul_of_nonneg_right _ (hτ w).le
      have := le_abs_self C₁
      simp only [hAdef]
      linarith
    rw [hy'eq w, div_le_div_iff₀ (by positivity) (hNpos w)]
    nlinarith [hNle]
  have hprodu : ∏ w, ρ w ((u : 𝓞 F) : F) ^ 2 = 1 := by
    rw [prod_sq_embedding hF ρ hρ]
    have h := (NumberField.isUnit_iff_norm (x := (u : 𝓞 F))).1 u.isUnit
    have h' : |((Algebra.norm ℚ ((u : 𝓞 F) : F) : ℚ) : ℝ)| = 1 := by
      rw [RingOfIntegers.coe_norm] at h
      exact_mod_cast h
    rw [← sq_abs, h', one_pow]
  have hprod : P ≤ ∏ w, (mob ρ (r * k) τ w).im := by
    rw [Finset.prod_congr rfl (fun w _ => hz w), Finset.prod_mul_distrib, hprodu, one_mul]
    have h1' : ∏ w, 1 / (A * ρ w l ^ 2) ≤ ∏ w, y' w :=
      Finset.prod_le_prod₀ (fun w _ => by
        have hlw : ρ w l ≠ 0 := (map_ne_zero _).2 hl0
        positivity) (fun w _ => hlow w)
    refine le_trans ?_ h1'
    have h2' : ∏ w, 1 / (A * ρ w l ^ 2) = 1 / (A ^ n * ((Algebra.norm ℚ l : ℚ) : ℝ) ^ 2) := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, prod_sq_embedding hF ρ hρ]
      simp [hn]
    rw [h2', hPdef]
    have hN0 : ((Algebra.norm ℚ l : ℚ) : ℝ) ≠ 0 := by
      have : (Algebra.norm ℚ l : ℚ) ≠ 0 := (Algebra.norm_ne_zero_iff).2 hl0
      exact_mod_cast this
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h3 : |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ B := by
      have := le_abs_self C₂
      simp only [hBdef]
      linarith
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  refine ⟨r, hr, k, hk, ?_, hbal'⟩
  intro w
  exact balanced_lower _ hzpos κ P hκ hbal' hprod w

end GlobalTheory.CompanionTheory.SW.Red
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.UnitProdAlg

variable {F : Type} [Field F] [NumberField F]

theorem mulSupport_finite {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    (Function.mulSupport c).Finite := by
  have := h.1
  rw [Filter.eventually_cofinite] at this
  exact this

theorem map_hom (f : ℝ≥0 →* ℝ≥0) {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) : IsUnitProd (f a) (fun v => f (c v)) := by
  have hfin := mulSupport_finite h
  refine ⟨h.1.mono fun v hv => by simp [hv], ?_⟩
  have hsub : Function.mulSupport (fun v => f (c v)) ⊆ (hfin.toFinset : Set _) := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    exact hv (by simp [h1])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← map_prod, ← map_mul,
    ← finprod_eq_prod_of_mulSupport_subset c (by simp), h.2, map_one]

def sqrtHom : ℝ≥0 →* ℝ≥0 where
  toFun := NNReal.sqrt
  map_one' := NNReal.sqrt_one
  map_mul' := NNReal.sqrt_mul

theorem mul {a b : ℝ≥0} {c e : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) (k : IsUnitProd b e) : IsUnitProd (a * b) (fun v => c v * e v) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1, k.1] with v h1 h2
    simp [h1, h2]
  · rw [finprod_mul_distrib (mulSupport_finite h) (mulSupport_finite k), mul_mul_mul_comm,
      h.2, k.2, one_mul]

theorem ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) : a ≠ 0 := by
  rintro rfl
  simpa using h.2

theorem family_ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c)
    (v : HeightOneSpectrum (𝓞 F)) : c v ≠ 0 := by
  intro hv
  have h2 := h.2
  rw [finprod_eq_zero c v hv (mulSupport_finite h)] at h2
  simp at h2

theorem inv {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) :=
  map_hom (invMonoidWithZeroHom (G₀ := ℝ≥0) : ℝ≥0 →* ℝ≥0) h

theorem main : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0)
    (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e →
    a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧
    IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧
    (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  intro F _ _ a b c e h k
  refine ⟨ne_zero h, family_ne_zero h, mul h k, inv h, ?_, map_hom sqrtHom h,
    fun n => map_hom (powMonoidHom n) h, (mulSupport_finite h).toFinset, fun S hS => ?_⟩
  · simpa only [div_eq_mul_inv] using mul h (inv k)
  · have hsub : Function.mulSupport c ⊆ (S : Set _) := by
      intro v hv
      exact hS ((mulSupport_finite h).mem_toFinset.2 hv)
    refine ⟨fun v hv => ?_, ?_⟩
    · by_contra hne
      exact hv (hsub hne)
    · rw [← finprod_eq_prod_of_mulSupport_subset c hsub]
      exact h.2

end GlobalTheory.CompanionTheory.SW.UnitProdAlg
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AlgSplit

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz : ∀ j : Fin M, blockOne t A 0 j.succ = 0 := by intro j; simp [blockOne]
  have h00 : blockOne t A 0 0 = t := by simp [blockOne]
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j; simp [blockOne]
  simp [hz, h00, h0]

theorem split_anisotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (t : F) (x : Fin (M + 1) → E), t ≠ 0 → hE σ J x x = algebraMap F E t → ∃ (g : GL (Fin (M + 1)) E) (J₁ : Matrix (Fin M) (Fin M) E), IsHermND σ J₁ ∧ blockOne (algebraMap F E t) J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * g ∧ ∀ i, (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i 0 = x i := by
  intro F E _ _ _ _ _ σ hCM M J hJ t x ht hx
  obtain ⟨-, -, -, hconj⟩ := hCM
  have hσ : ∀ e : E, σ (σ e) = e := by
    intro e
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hconj, hconj, star_star]
  have hherm : ∀ y z, σ (hE σ J y z) = hE σ J z y := by
    intro y z

    simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    ring
  set s : E := algebraMap F E t with hs
  have hs0 : s ≠ 0 := (map_ne_zero _).2 ht
  let φ : (Fin (M + 1) → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := by
        intro y z
        simp [hE, hform, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        simp only [hE, hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring }
  have hφ : ∀ y, φ y = hE σ J x y := fun _ => rfl
  have hsurj : Function.Surjective φ := fun e =>
    ⟨(e / s) • x, by rw [map_smul, hφ, hx, smul_eq_mul]; field_simp⟩
  have hfr : Module.finrank E (LinearMap.ker φ) = M := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
    simp at h
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker φ) hfr
  have hb : ∀ k, hE σ J x (b k : Fin (M + 1) → E) = 0 := fun k => (b k).2
  let col : Fin (M + 1) → Fin (M + 1) → E := Fin.cons x (fun k => (b k : Fin (M + 1) → E))
  let gm : Matrix (Fin (M + 1)) (Fin (M + 1)) E := Matrix.of fun i j => col j i
  have hG : ∀ i j, (cT (σ : E →+* E) gm * J * gm) i j = hE σ J (col i) (col j) := by
    intro i j
    simp only [cT, Matrix.mul_apply, hE, hform, gm, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : gm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hsum : v 0 • x + ∑ k : Fin M, v k.succ • (b k : Fin (M + 1) → E) = 0 := by
      rw [← hv]
      ext i
      simp [gm, col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
    have hv00 : v 0 = 0 := by
      have h1 := congrArg φ hsum

      rw [map_add (f := _), map_smul, map_sum, map_zero, hφ, hx, smul_eq_mul] at h1
      have h2 : ∀ k : Fin M, φ (v k.succ • (b k : Fin (M + 1) → E)) = 0 := by
        intro k
        rw [map_smul, hφ, hb, smul_zero]
      simp only [h2, Finset.sum_const_zero, add_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_right hs0
    have hker : ∑ k : Fin M, v k.succ • b k = 0 := by
      apply Subtype.ext
      rw [hv00, zero_smul, zero_add] at hsum
      simpa using hsum
    have hvs := Fintype.linearIndependent_iff.1 b.linearIndependent _ hker
    apply hv0
    ext i
    refine Fin.cases hv00 hvs i
  let J₁ : Matrix (Fin M) (Fin M) E := Matrix.of fun k l =>
    hE σ J (b k : Fin (M + 1) → E) (b l : Fin (M + 1) → E)
  have hblock : blockOne s J₁ = cT (σ : E →+* E) gm * J * gm := by
    ext i j
    rw [hG]
    refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
    · simp [blockOne, col, hx, hs]
    · simp [blockOne, col, hb]
    · have h3 : hE σ J (b k : Fin (M + 1) → E) x = 0 := by
        rw [← hherm, hb, map_zero]
      simp [blockOne, col, h3]
    · simp [blockOne, col, J₁]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero gm hdet, J₁, ⟨?_, ?_⟩, hblock, fun i => rfl⟩
  · intro k l
    exact hherm _ _
  · intro hJ0
    have h4 := congrArg Matrix.det hblock
    rw [det_blockOne, hJ0, mul_zero, Matrix.det_mul, Matrix.det_mul] at h4
    have h5 : (cT (σ : E →+* E) gm).det = σ gm.det := by
      rw [cT, Matrix.det_transpose]
      exact ((σ : E →+* E).map_det gm).symm
    rw [h5] at h4
    have h6 : σ gm.det ≠ 0 := (map_ne_zero _).2 hdet
    exact mul_ne_zero (mul_ne_zero h6 hJ.2) hdet h4.symm

end GlobalTheory.CompanionTheory.SW.AlgSplit
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.ScalTrace

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hermScal_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (s : R) :
    (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = algebraMap R (R ⊗[F] E) s := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem trace_det : ∀ (F E : Type) [Field F] [Field E] [Algebra F E], (1 / 2 : F) ≠ 0 → Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (β : F), algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = algebraMap F R β ∧ (β ≠ 0 → IsUnit ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det) := by
  intro F E _ _ _ h2 hf σ R _ _ β
  have hfin : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hf
  have hent := hermScal_entry σ R (algebraMap F R β)
  refine ⟨?_, fun hβ => ?_⟩
  · rw [hent, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) (algebraMap F R β)]
    have h20 : (2 : F) ≠ 0 := by
      intro h
      apply h2
      simp [h]
    have hhalf : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
      rw [← map_mul, one_div, inv_mul_cancel₀ h20, map_one]
    rw [Fintype.card_fin, nsmul_eq_mul]
    have h2R : ((2 : ℕ) : R) = algebraMap F R 2 := by
      rw [map_ofNat]
      norm_num
    rw [h2R, ← mul_assoc, hhalf, one_mul]
  · rw [Matrix.det_fin_one, hent]
    exact ((isUnit_iff_ne_zero.2 hβ).map (algebraMap F R)).map (algebraMap R (R ⊗[F] E))

end GlobalTheory.CompanionTheory.SW.BB.ScalTrace
end
end

section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.fibre_family_eq_on_open_subset : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B B' : Set X), IsOpen B → IsOpen B' → B' ⊆ B → ∀ fib fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib' → ∀ b ∈ B', fib' b = fib b := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq | exact GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq | (intros; apply GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq <;> assumption)
end
