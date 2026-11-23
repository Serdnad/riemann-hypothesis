module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle030
public import ReciprocityTheory.SemistableReduction.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle006
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ExistsIntMultiple
import ReciprocityTheory.SemistableReduction.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CardEmbPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogHeightGeneratorLowerBound
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

theorem satDeg_le (K : Type) [Field K] [NumberField K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : MvPolynomial κ K) (hF : F ≠ 0) (T S : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (F * MvPolynomial.monomial m 1).support ⊆ T) :
    ∃ b : Fin S.card → Fin r → K, (∀ j, b j ∈ stdLat K r) ∧ LinearIndependent K b ∧
      Submodule.span K (Set.range b) =
        Submodule.span K (Set.range fun m : S => fun i => (F * MvPolynomial.monomial (m : κ →₀ ℕ) 1).coeff
          (e.symm i : κ →₀ ℕ)) ∧
      ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b) b ≤
        -((S.card : ℝ) * (Module.finrank ℚ K : ℝ) * hT F) := by
  obtain ⟨c, G₀, hc, hG₀⟩ := exists_int_multiple F
  have hG : MvPolynomial.map (algebraMap (𝓞 K) K) G₀ ≠ 0 := by
    rw [hG₀]
    exact mul_ne_zero (by simpa using hc) hF
  have hG₀ne : G₀ ≠ 0 := by
    rintro rfl
    exact hG (map_zero _)
  have hSTG : ∀ m ∈ S,
      (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial m 1).support ⊆ T := by
    intro m hm s hs
    apply hST m hm
    rw [MvPolynomial.mem_support_iff] at hs ⊢
    rw [hG₀, mul_assoc, MvPolynomial.coeff_C_mul] at hs
    exact right_ne_zero_of_mul hs
  refine ⟨bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e, ?_, linInd_bG _ hG S T e hSTG, ?_, ?_⟩
  ·
    intro j
    show _ ∈ Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)
    rw [Submodule.mem_pi]
    intro i _
    rw [Submodule.mem_one]
    refine ⟨(G₀ * MvPolynomial.monomial (mS S j) 1).coeff (e.symm i : κ →₀ ℕ), ?_⟩
    show _ = (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial (mS S j) 1).coeff
      (e.symm i : κ →₀ ℕ)
    rw [← MvPolynomial.coeff_map, map_mul, MvPolynomial.map_monomial, map_one]
  ·
    have key : ∀ j, bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e j =
        c • fun i => (F * MvPolynomial.monomial (S.equivFin.symm j : κ →₀ ℕ) 1).coeff
          (e.symm i : κ →₀ ℕ) := by
      intro j
      funext i
      simp only [bG, coordVec, mS, hG₀, mul_assoc, MvPolynomial.coeff_C_mul, Pi.smul_apply,
        smul_eq_mul]
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro j
      simp only [SetLike.mem_coe]
      rw [key j]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S.equivFin.symm j, rfl⟩)
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro m
      simp only [SetLike.mem_coe]
      have h1 := key (S.equivFin m)
      rw [Equiv.symm_apply_apply] at h1
      have h2 : (fun i => (F * MvPolynomial.monomial (m : κ →₀ ℕ) 1).coeff (e.symm i : κ →₀ ℕ)) =
          c⁻¹ • bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e (S.equivFin m) := by
        rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  ·
    have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
    have hd' : (Module.finrank ℚ K : ℝ) ≠ 0 := hd.ne'
    have hTeq : hT F = hT (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) := by
      rw [hG₀, hT_C_mul F hF c hc]
    have hTG : (Module.finrank ℚ K : ℝ) * hT (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) =
        (∑ᶠ w : FinitePlace K,
          Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀))) +
        ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean
          (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) := by
      rw [hT]
      field_simp
    have hnorm : Real.log (Ideal.absNorm (contId G₀) : ℝ) =
        -∑ᶠ w : FinitePlace K,
          Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) := by
      have hprod := absNorm_mul_gauss G₀ hG₀ne
      have hN := left_ne_zero_of_mul_eq_one hprod
      have hP := right_ne_zero_of_mul_eq_one hprod
      have hsum := finsum_log_eq
        (fun w : FinitePlace K => ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀))
        (fun w => ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero w _ hG) (gaussAbs_mulSupport_finite _ hG)
      have hlog : Real.log (Ideal.absNorm (contId G₀) : ℝ) + Real.log (∏ᶠ w : FinitePlace K,
          ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) = 0 := by
        rw [← Real.log_mul hN hP, hprod, Real.log_one]
      rw [hsum]
      linarith
    have h1 := log_relIndex_le G₀ hG₀ne S T e hSTG
    rw [hnorm] at h1
    have h3 : ∑ σ : K →+* ℂ, 2 * (S.card : ℝ) * ReciprocityTheory.MultiplicativeHeights.torusMean
          (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) ≤
        ∑ σ : K →+* ℂ, Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (1 : Matrix (Fin r) (Fin r) ℂ) σ
          (bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e)).det.re :=
      Finset.sum_le_sum fun σ _ => gram_le _ hG S T e hSTG σ
    have e1 : ∑ σ : K →+* ℂ, 2 * (S.card : ℝ) * ReciprocityTheory.MultiplicativeHeights.torusMean
          (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) =
        2 * (S.card : ℝ) * ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean
          (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) := by
      rw [Finset.mul_sum]
    have e2 : (S.card : ℝ) * (Module.finrank ℚ K : ℝ) * hT F =
        (S.card : ℝ) * ((Module.finrank ℚ K : ℝ) * hT (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) := by
      rw [hTeq]
      ring
    simp only [ReciprocityTheory.MultiplicativeHeights.latDeg]
    rw [e2, hTG]
    linarith

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem h_seven (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (hF1d : d.TrivialPlaceHyp) (hSup : d.HtSup)
    (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K) (hx : ∀ c, d.wx x c ≠ 0) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
    let HL := d.Hgt h d.wL (d.wx x)
    let Hde := d.Hgt h (d.n1 • d.wde) d.et / d.n1
    let ade := (d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1
    let aG1 := (d.aG h ((2 : ℕ) • d.G1) d.ta1 : ℝ) / 2
    let X8 := d.HgtMM h (d.wx x) + d.del * ((∑ᶠ la, d.nu la * logNorm la) /
      (Module.finrank ℚ K : ℝ) + d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) + d.D * d.cc * d.g0 * ade * lr
    let Y := d.del * d.PI4 * d.D * d.wsize d.wL + d.D * aG1 * lr
    HL ≤ X8 + d.cc * d.g0 * Hde ∧ Hde ≤ HL + Y ∧
      d.Hgt h d.wF ta' ≤ (d.D + 4) * HL + d.del * d.PI4 * d.D * d.wsize d.wL +
        d.D * d.aG h d.G2 d.ta2 * lr := by
  dsimp only
  have hf : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hi : (0 : ℝ) < d.i := by exact_mod_cast hd.i_ge
  have hg : (0 : ℝ) < d.g0 := by exact_mod_cast hd.g_zero_ge_ask_sum
  have hn1 : ((d.n1 : ℕ) : ℝ) = (d.i : ℝ) * d.g0 := by simp [Data.n1]
  have hn1pos : (0 : ℝ) < d.n1 := by rw [hn1]; positivity
  have hdel : (0 : ℝ) ≤ d.del := Nat.cast_nonneg _
  have hla := d.la_part hd h hH1 (d.wx x) hf
  have hsg := d.sg_part hd h hI2be (d.wx x) hf
  have h0 := d.logHeight_section_bound hd h hF1d (d.wx x) hf
  obtain ⟨-, -, hind3, hind4⟩ := d.h_ind hd h hI2be
  have hta1 : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1) ∧ d.ta1 c ≠ 0 :=
    fun c => ⟨hd.firstSectionMem c, hd.firstSectionNeZero c⟩
  have hta2 : ∀ c, d.ta2 c ∈ 𝒜 c d.G2 ∧ d.ta2 c ≠ 0 := fun c => ⟨hd.secondSectionMem c, hd.secondSectionNeZero c⟩
  have hbdd1 := fun sg => hd.bdd sg _ d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have hbdd2 := fun sg => hd.bdd sg _ d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  have hint1 := fun c sg => (d.int_Nsg hd h hI2be c sg).1 ((2 : ℕ) • d.G1) (d.ta1 c) (by simp)
    (hd.firstSectionMem c) (hd.firstSectionNeZero c)
  have hint2 := fun c sg => (d.int_Nsg hd h hI2be c sg).1 d.G2 (d.ta2 c) (by simp)
    (hd.secondSectionMem c) (hd.secondSectionNeZero c)
  have h41 := (d.h_four hd h _ d.ta1 hta1 hd.ordDoubleFirstSection_nonneg hbdd1 hint1).1
  have h42 := (d.h_four hd h _ d.ta2 hta2 hd.ordSecondSectionNonneg hbdd2 hint2).1
  obtain ⟨-, -, hsup1, hsup2⟩ := hSup
  have m1 := mul_le_mul_of_nonneg_left hsup1 hdel
  have m2 := mul_le_mul_of_nonneg_left hsup2 hdel
  refine ⟨?_, ?_, ?_⟩
  · have e1 : d.Hgt h d.wL (d.wx x) = (∑ᶠ la, d.NlaG h d.wL (d.wx x) la * logNorm la) /
        (Module.finrank ℚ K : ℝ) + meanK (d.Nsg d.wL (d.wx x)) + d.h0f h d.wL (d.wx x) := rfl
    have e2 : d.HgtMM h (d.wx x) = (∑ᶠ la, d.NlaMM h (d.wx x) la * logNorm la) /
        (Module.finrank ℚ K : ℝ) + meanK (d.NsgMM (d.wx x)) + d.mahlerMeasureHeight h (d.wx x) := rfl
    have e3 : d.Hgt h (d.n1 • d.wde) d.et = (∑ᶠ la, d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) /
        (Module.finrank ℚ K : ℝ) + meanK (d.Nsg (d.n1 • d.wde) d.et) + d.h0f h (d.n1 • d.wde) d.et := rfl
    have hla' := div_le_div_of_nonneg_right hla hK.le
    rw [add_div, add_div, mul_div_assoc, mul_div_assoc] at hla'
    have eH : d.cc * d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1) =
        d.cc / d.i * d.Hgt h (d.n1 • d.wde) d.et := by
      rw [hn1]; field_simp
    have eA : d.D * d.cc * d.g0 * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) *
        (Real.log (d.N + 1 : ℕ) + 1 / 2) =
        d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) := by
      rw [hn1]; field_simp
    rw [e1, e2, eH, eA, e3]
    nlinarith [hla', hsg, h0]
  · have hd3 := hind3 x hx
    have eq : d.Hgt h (d.n1 • d.wde) d.et / d.n1 =
        d.Hgt h d.wL (d.wx x) - d.Hgt h ((2 : ℕ) • d.G1) d.ta1 / 2 := by
      rw [div_eq_iff hn1pos.ne']
      linarith
    rw [eq]
    linarith [h41, m1]
  · have hd4 := hind4 x ta' hx hta'
    linarith [h42, m2]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
