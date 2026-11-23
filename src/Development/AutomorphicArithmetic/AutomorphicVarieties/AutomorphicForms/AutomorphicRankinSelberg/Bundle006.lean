module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.PSeries

@[expose] public section

section

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal

theorem UpperTheory.V.Af.Rs.fdCount :
    UpperTheory.V.Af.Rs.FdNull → UpperTheory.V.Af.Rs.FdCount := by
  intro hN
  unfold UpperTheory.V.Af.Rs.FdNull at hN
  unfold UpperTheory.V.Af.Rs.FdCount
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hnull : ∀ γ : SL(2, ℤ),
      volume ((fun z : ℍ => γ • z) ⁻¹' (ModularGroup.fd \ ModularGroup.fdo)) = 0 := by
    intro γ
    have : (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z := rfl
    rw [this, measure_preimage_smul]
    exact hN
  have hB := measure_iUnion_null hnull
  rw [ae_iff]
  refine measure_mono_null ?_ hB
  intro z hz
  by_contra hzB
  simp only [mem_iUnion, mem_preimage, not_exists] at hzB
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hgo : g • z ∈ ModularGroup.fdo := by
    by_contra h
    exact hzB g ⟨hg, h⟩
  have hne : g ≠ -g := by
    intro h
    have h1 : (1 : SL(2, ℤ)) = -1 := by
      have := congrArg (fun A => A * g⁻¹) h
      simpa using this
    have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1
    simp at this
  apply hz
  rw [tsum_eq_sum (s := {g, -g}) ?_]
  · rw [Finset.sum_pair hne]
    have hg' : (-g) • z ∈ ModularGroup.fd := by simpa using hg
    rw [indicator_of_mem hg, indicator_of_mem hg', one_add_one_eq_two]
  · intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
    apply indicator_of_notMem
    intro hmem
    have heq : γ • z = (γ * g⁻¹) • (g • z) := by
      rw [smul_smul, inv_mul_cancel_right]
    rw [heq] at hmem
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hgo hmem with h | h
    · exact hγ.1 (mul_inv_eq_one.mp h)
    · apply hγ.2
      rw [mul_inv_eq_iff_eq_mul] at h
      rw [h]
      simp
end

section

open UpperHalfPlane hiding I
open scoped MatrixGroups

private theorem UpperTheory.V.Af.Rs.eq_T_zpow_mul_of_row_eq {γ δ : SL(2, ℤ)}
    (h : UpperTheory.V.Af.Rs.row γ = UpperTheory.V.Af.Rs.row δ) : ∃ n : ℤ, γ = ModularGroup.T ^ n * δ := by
  have hc : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := congrFun h 0
  have hd : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := congrFun h 1
  have hγ := γ.det_coe
  have hδ := δ.det_coe
  rw [Matrix.det_fin_two] at hγ hδ
  refine ⟨-(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
      + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
  · rw [hc, hd] at hγ
    linear_combination (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hγ
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hδ
  · rw [hc, hd] at hγ
    linear_combination (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hγ
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hδ

private theorem UpperTheory.V.Af.Rs.row_T_zpow_mul (n : ℤ) (δ : SL(2, ℤ)) :
    UpperTheory.V.Af.Rs.row (ModularGroup.T ^ n * δ) = UpperTheory.V.Af.Rs.row δ := by
  funext i
  simp [UpperTheory.V.Af.Rs.row, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.V.Af.Rs.rowBij :
    UpperTheory.V.Af.Rs.RowBij := by
  refine ⟨fun γ => ModularGroup.bottom_row_coprime γ, ?_⟩
  intro z x
  obtain ⟨g, -, hg⟩ := ModularGroup.bottom_row_surj (R := ℤ) (Set.mem_setOf_eq ▸ x.2 : x.1 ∈ _)
  have hrow : UpperTheory.V.Af.Rs.row g = x.1 := hg
  refine ⟨ModularGroup.T ^ (-⌊(g • z).re⌋) * g, ⟨?_, ?_⟩, ?_⟩
  · rw [UpperTheory.V.Af.Rs.row_T_zpow_mul, hrow]
  · show 0 ≤ (_ : ℍ).re ∧ (_ : ℍ).re < 1
    rw [mul_smul, ModularGroup.re_T_zpow_smul]
    push_cast
    constructor
    · linarith [Int.floor_le (g • z).re]
    · linarith [Int.lt_floor_add_one (g • z).re]
  · rintro γ' ⟨hr, hs⟩
    have hr' : UpperTheory.V.Af.Rs.row γ' = UpperTheory.V.Af.Rs.row g := by rw [hr, hrow]
    obtain ⟨m, rfl⟩ := UpperTheory.V.Af.Rs.eq_T_zpow_mul_of_row_eq hr'
    have hs' : 0 ≤ ((ModularGroup.T ^ m * g) • z).re ∧ ((ModularGroup.T ^ m * g) • z).re < 1 := hs
    rw [mul_smul, ModularGroup.re_T_zpow_smul] at hs'
    have h1 : ((m + ⌊(g • z).re⌋ : ℤ) : ℝ) < 1 := by
      push_cast
      linarith [Int.floor_le (g • z).re]
    have h2 : (-1 : ℝ) < ((m + ⌊(g • z).re⌋ : ℤ) : ℝ) := by
      push_cast
      linarith [Int.lt_floor_add_one (g • z).re]
    have h1' : m + ⌊(g • z).re⌋ < 1 := by exact_mod_cast h1
    have h2' : -1 < m + ⌊(g • z).re⌋ := by exact_mod_cast h2
    have hm : m = -⌊(g • z).re⌋ := by omega
    rw [hm]
end

section

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

private theorem clsEx_key (L : ℕ) (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ)
    (hF : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ z, F (γ • z) = ψ ((γ 1 1 : ℤ) : ZMod L) * F z)
    (n m : ℕ) (γ δ : SL(2, ℤ))
    (h : UpperTheory.V.Af.Rs.cls L ((m : ℤ) • UpperTheory.V.Af.Rs.row δ) = UpperTheory.V.Af.Rs.cls L ((n : ℤ) • UpperTheory.V.Af.Rs.row γ))
    (z : ℍ) : ψ (m : ZMod L) * F (δ • z) = ψ (n : ZMod L) * F (γ • z) := by
  classical
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [UpperTheory.V.Af.Rs.cls, UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
    Int.cast_natCast] at h0 h1
  have hdet : ((γ 0 0 : ℤ) : ZMod L) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast congrArg (fun t : ℤ => (t : ZMod L)) this
  have hn : (n : ZMod L) = m * (((γ 0 0 : ℤ) : ZMod L) * (δ 1 1 : ℤ) - (γ 0 1 : ℤ) * (δ 1 0 : ℤ)) := by
    linear_combination (-(n : ZMod L)) * hdet - ((γ 0 0 : ℤ) : ZMod L) * h1 +
      ((γ 0 1 : ℤ) : ZMod L) * h0
  by_cases hm : IsUnit (m : ZMod L)
  · obtain ⟨η, hη⟩ : ∃ η : SL(2, ℤ), η = δ * γ⁻¹ := ⟨_, rfl⟩
    have e10 : (η 1 0 : ℤ) = δ 1 0 * γ 1 1 - δ 1 1 * γ 1 0 := by
      rw [hη]
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have e11 : (η 1 1 : ℤ) = δ 1 1 * γ 0 0 - δ 1 0 * γ 0 1 := by
      rw [hη]
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hmem : η ∈ Gamma0 L := by
      rw [Gamma0_mem, e10]
      push_cast
      refine (hm.mul_right_eq_zero).1 ?_
      linear_combination ((γ 1 1 : ℤ) : ZMod L) * h0 - ((γ 1 0 : ℤ) : ZMod L) * h1
    have hδ : δ = η * γ := by
      rw [hη, inv_mul_cancel_right]
    have hn' : (n : ZMod L) = m * ((η 1 1 : ℤ) : ZMod L) := by
      rw [e11, hn]
      push_cast
      ring
    rw [hδ, mul_smul, hF η hmem, hn', map_mul]
    ring
  · have hn' : ¬IsUnit (n : ZMod L) := by
      intro hu
      rw [hn] at hu
      exact hm (isUnit_of_mul_isUnit_left hu)
    rw [MulChar.map_nonunit _ hm, MulChar.map_nonunit _ hn']
    simp

theorem UpperTheory.V.Af.Rs.clsEx :
    UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.ClsEx := by
  intro _ L _ ψ F hF
  classical
  refine ⟨fun v z => if h : ∃ p : ℕ × SL(2, ℤ), cls L ((p.1 : ℤ) • row p.2) = v then
    ψ (h.choose.1 : ZMod L) * F (h.choose.2 • z) else 0, ?_⟩
  intro n γ z
  have h : ∃ p : ℕ × SL(2, ℤ), cls L ((p.1 : ℤ) • row p.2) = cls L ((n : ℤ) • row γ) := ⟨(n, γ), rfl⟩
  simp only [dif_pos h]
  exact clsEx_key L ψ F hF n _ γ _ h.choose_spec z
end

section

open MeasureTheory Set UpperTheory.V.Af.Rs
open UpperHalfPlane hiding I
open scoped MatrixGroups

theorem UpperTheory.V.Af.Rs.tEq :
    UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.Unfold → UpperTheory.V.Af.Rs.GcdSum → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.Swap → UpperTheory.V.Af.Rs.LBd → UpperTheory.V.Af.Rs.TEq := by
  intro hRB hSI hUnf hGcd hKer hSw hLB L _ ψ F G hG hF hGn s hs
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨hkc, hk0, hkz, hkrow, hkn, -⟩ := hKer s hs'
  obtain ⟨hint, hsum⟩ := hSw L G hGn s hs
  have hrow : ∀ x : Cop, ∃ γ : SL(2, ℤ), row γ = (x : Fin 2 → ℤ) := fun x =>
    ((hRB.2 UpperHalfPlane.I x).exists).imp fun γ h => h.1
  have hone : ∀ (γ : SL(2, ℤ)) (z : ℍ), G (cls L (row γ)) z = F (γ • z) := by
    intro γ z
    have := hG 1 γ z
    simpa using this
  have hGn' : ∀ (n : ℕ) (γ : SL(2, ℤ)) (z : ℍ),
      G (cls L ((n : ℤ) • row γ)) z = ψ n * G (cls L (row γ)) z := by
    intro n γ z
    rw [hG, hone]
  set a : (Fin 2 → ℤ) → ℂ := fun x => ∫ z in ModularGroup.fd, G (cls L x) z * (ker s x z : ℂ) with ha
  set c : ℕ → ℂ := fun n => ψ n / ((n : ℝ) ^ (2 * s) : ℝ) with hc
  have hs2 : (2 * s) ≠ 0 := by have := hs.1; linarith
  have hgcd := hGcd a c hsum.summable (hLB L ψ s hs.1.le).1
    (by simp [ha, hkz])
    (by simp [hc, Real.zero_rpow hs2])
    (by
      intro n x
      obtain ⟨γ, hγ⟩ := hrow x
      simp only [ha, hc]
      rw [← hγ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hkn]
      rw [hGn', Complex.ofReal_div]
      ring)
  have hunf := hUnf (fun z => F z * ((z.im ^ s : ℝ) : ℂ)) (fun x z => G (cls L x) z * (ker s x z : ℂ))
    (by
      have hc1 : Continuous (fun z : ℍ => z.im ^ s) :=
        UpperHalfPlane.continuous_im.rpow_const (fun _ => Or.inr (by linarith [hs.1]))
      exact hF.1.mul (Complex.continuous_ofReal.comp hc1))
    (hSI F hF s hs)
    (by intro γ z; rw [hkrow, hone])
    (fun x => hint x)
  rw [← hsum.tsum_eq, hgcd]
  congr 1
  exact hunf.tsum_eq
end

section

open MeasureTheory Set UpperHalfPlane in
private theorem UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane (U : Set ℍ) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (volume : Measure ℍ) U := by
  rw [pos_iff_ne_zero]
  intro h0
  have hac : (volume.comap UpperHalfPlane.coe : Measure ℍ) ≪ (volume : Measure ℍ) := by
    rw [volume_def]
    refine withDensity_absolutelyContinuous' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine Measurable.aemeasurable (Measurable.coe_nnreal_ennreal ?_)
      refine Continuous.measurable ?_
      refine .pow (.div₀ continuous_const ?_ ?_) _
      · exact continuous_im.subtype_mk _
      · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero
    · have hz : NNReal.mk z.im z.im_pos.le ≠ 0 := NNReal.ne_iff.mp z.im_ne_zero
      exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (one_div_ne_zero hz))
  have h1 := hac h0
  rw [measurableEmbedding_coe.comap_apply] at h1
  exact ((isOpenEmbedding_coe.isOpenMap U hU).measure_pos volume (hne.image _)).ne' h1

open MeasureTheory Set UpperHalfPlane in
theorem UpperTheory.V.Af.Rs.fdPos :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdPos := by
  intro _ φ hc h0 hint z hz hpos
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hint]
  have hV : IsOpen {w : ℍ | 0 < φ w} := isOpen_lt continuous_const hc
  rw [ModularGroup.fd_eq_closure_fdo] at hz
  have hne : ({w : ℍ | 0 < φ w} ∩ ModularGroup.fdo).Nonempty :=
    mem_closure_iff.mp hz _ hV hpos
  refine (UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane _ (hV.inter ModularGroup.isOpen_fdo) hne).trans_le
    (measure_mono ?_)
  rintro w ⟨hw, hw'⟩
  exact ⟨ne_of_gt hw, ModularGroup.fdo_subset_fd hw'⟩
end

section

theorem UpperTheory.V.Af.Rs.zLow :
    UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.KerLow → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZLow := by
  intro hB hL hW L _ s hs z hz
  have hs' : s ∈ Set.Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, h0, -, -, -, hub⟩ := hB s hs'
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hW.1 (2 * s) (by linarith [hs.1])
  have hk : Summable fun x : Fin 2 → ℤ => UpperTheory.V.Af.Rs.ker s x z :=
    Summable.of_nonneg_of_le (fun x => h0 x z) (fun x => hub x z hz) (hsum.mul_left _)
  have hv : ∀ v ∈ (Finset.univ : Finset (Fin 2 → ZMod L)), Summable fun x : Fin 2 → ℤ =>
      if UpperTheory.V.Af.Rs.cls L x = v then UpperTheory.V.Af.Rs.ker s x z else 0 := by
    intro v _
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hk
    · split_ifs
      · exact h0 x z
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact h0 x z
  have he : ∑ v, UpperTheory.V.Af.Rs.Zc L v s z = ∑' x : Fin 2 → ℤ, UpperTheory.V.Af.Rs.ker s x z := by
    unfold UpperTheory.V.Af.Rs.Zc
    rw [← Summable.tsum_finsetSum hv]
    refine tsum_congr fun x => ?_
    simp
  rw [he, UpperTheory.V.Af.Rs.Wsum, ← tsum_mul_left]
  exact (hsum.mul_left _).tsum_le_tsum (fun x => hL s hs' x z hz) hk
end

section

open Filter Topology Set

private lemma not_summable_two : ¬ Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * (1 : ℝ))) := by
  intro hs
  set f : (Fin 2 → ℤ) → ℝ := fun x => ‖x‖ ^ (-(2 * (1 : ℝ))) with hf
  have hnn : ∀ x, 0 ≤ f x := fun x => Real.rpow_nonneg (norm_nonneg _) _
  let g : ℕ × ℕ → (Fin 2 → ℤ) := fun p => ![(p.1 : ℤ) + 1, (p.2 : ℤ)]
  have hg : Function.Injective g := by
    intro p q h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [g] at h0 h1
    exact Prod.ext (by omega) (by omega)
  have hsg : Summable (f ∘ g) := hs.comp_injective hg
  have hprod : Summable fun a : ℕ => ∑' b : ℕ, (f ∘ g) (a, b) := hsg.prod
  have key : ∀ a : ℕ, (1 : ℝ) / ((a : ℝ) + 1) ≤ ∑' b : ℕ, (f ∘ g) (a, b) := by
    intro a
    have hrow : Summable fun b : ℕ => (f ∘ g) (a, b) := hsg.prod_factor a
    have hterm : ∀ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) = 1 / ((a : ℝ) + 1) ^ 2 := by
      intro b hb
      have hb' : b ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hn : ‖g (a, b)‖ = (a : ℝ) + 1 := by
        apply le_antisymm
        · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
          intro i
          fin_cases i
          · simp [g, Int.norm_eq_abs]
            rw [abs_of_nonneg (by positivity)]
          · simp [g, Int.norm_eq_abs]
            have : (b : ℝ) ≤ a := by exact_mod_cast hb'
            linarith
        · have h := norm_le_pi_norm (g (a, b)) 0
          have h2 : ‖g (a, b) 0‖ = (a : ℝ) + 1 := by
            simp [g, Int.norm_eq_abs]
            positivity
          linarith
      simp only [Function.comp, hf, hn]
      rw [show (-(2 * (1 : ℝ))) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast, one_div]
    calc (1 : ℝ) / ((a : ℝ) + 1)
        = ∑ b ∈ Finset.range (a + 1), 1 / ((a : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
      _ = ∑ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) :=
          Finset.sum_congr rfl (fun b hb => (hterm b hb).symm)
      _ ≤ ∑' b, (f ∘ g) (a, b) := hrow.sum_le_tsum _ (fun b _ => hnn _)
  have hsum : Summable fun a : ℕ => (1 : ℝ) / ((a : ℝ) + 1) :=
    Summable.of_nonneg_of_le (fun a => by positivity) key hprod
  have hsum' : Summable fun a : ℕ => (1 : ℝ) / ((a + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hsum
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hsum')

theorem UpperTheory.V.Af.Rs.wTop :
    UpperTheory.V.Af.Rs.WTop := by
  unfold UpperTheory.V.Af.Rs.WTop
  refine ⟨fun t ht => EisensteinSeries.summable_one_div_norm_rpow ht, fun M => ?_⟩
  have hnn : ∀ (s : ℝ) (x : Fin 2 → ℤ), 0 ≤ ‖x‖ ^ (-(2 * s)) :=
    fun s x => Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin 2 → ℤ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ))) := by
    by_contra h
    push_neg at h
    exact not_summable_two (summable_of_sum_le (hnn 1) h)
  have ht : Tendsto (fun s : ℝ => ∑ x ∈ F, ‖x‖ ^ (-(2 * s))) (𝓝 1)
      (𝓝 (∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ))))) := by
    apply tendsto_finsetSum
    intro x _
    have hc : ContinuousAt (fun s : ℝ => ‖x‖ ^ (-(2 * s))) 1 := by
      apply ContinuousAt.comp (f := fun s : ℝ => -(2 * s)) (g := fun y : ℝ => ‖x‖ ^ y)
      · exact Real.continuousAt_const_rpow' (by norm_num)
      · fun_prop
    exact hc
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * s)) ∧ s ∈ Ioc 1 2 := by
    refine ((ht.eventually (lt_mem_nhds hF)).filter_mono nhdsWithin_le_nhds).and ?_
    have hI : Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hI] with s hs using ⟨hs.1, hs.2.le⟩
  obtain ⟨s, hsM, hs⟩ := hev.exists
  refine ⟨s, hs, ?_⟩
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) :=
    EisensteinSeries.summable_one_div_norm_rpow (by linarith [hs.1])
  exact hsM.le.trans (hsum.sum_le_tsum F (fun x _ => hnn s x))
end

section

open CongruenceSubgroup UpperTheory.V.Af
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

theorem UpperTheory.V.Af.Rs.petChar :
    UpperTheory.V.Af.Rs.PetChar := by
  intro k L _ χ ψ f g hf hg γ hγ z
  have h := UpperHalfPlane.petersson_slash_SL (k : ℤ) g f γ z
  rw [hg γ hγ, hf γ hγ] at h
  rw [← h]
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply,
    MulChar.star_apply', MulChar.mul_apply]
  ring
end
