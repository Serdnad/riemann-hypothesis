module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.ZLattice.Basic

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule Matrix

theorem relIndex_nsmul_mem {E : Type*} [AddCommGroup E] (H L : AddSubgroup E) {x : E}
    (hx : x ∈ L) : H.relIndex L • x ∈ H := by
  exact AddSubgroup.nsmul_relIndex_mem H hx

theorem exists_ne_zero_mem_norm_sq_le_gram_det_div_relIndex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (hN : 0 < N) (w : Fin N → E) (hw : LinearIndependent ℝ w) (Λ : AddSubgroup E)
    (hΛ : ∀ i, w i ∈ Λ) (hI : (span ℤ (Set.range w)).toAddSubgroup.relIndex Λ ≠ 0) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ‖v‖ ^ 2 ≤ N * ((gram ℝ w).det /
      ((span ℤ (Set.range w)).toAddSubgroup.relIndex Λ : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by
  classical
  set S : AddSubgroup E := (span ℤ (Set.range w)).toAddSubgroup with hS
  set I : ℕ := S.relIndex Λ with hIdef
  have hI0 : (I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hI
  set V : Submodule ℝ E := Submodule.span ℝ (Set.range w) with hV
  have hSV : ∀ x ∈ S, x ∈ V := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hΛV : ∀ x ∈ Λ, x ∈ V := by
    intro x hx
    have h1 : I • x ∈ S := relIndex_nsmul_mem S Λ hx
    have h2 : (I : ℝ) • x ∈ V := by rw [Nat.cast_smul_eq_nsmul]; exact hSV _ h1
    have h3 := V.smul_mem ((I : ℝ)⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ hI0, one_smul] at h3
  have hSΛ : S ≤ Λ := by
    intro x hx
    have hle : span ℤ (Set.range w) ≤ Λ.toIntSubmodule :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hΛ i)
    exact hle hx
  have hfin : Module.finrank ℝ V = N := by rw [finrank_span_eq_card hw, Fintype.card_fin]
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  let f : OrthonormalBasis (Fin N) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hfin)
  let wV : Fin N → V := fun i => ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hwV : LinearIndependent ℝ wV := LinearIndependent.of_comp V.subtype hw
  let φ : V ≃ₗ[ℝ] (Fin N → ℝ) := f.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))
  have hφ : ∀ v : V, φ v = (f.repr v).ofLp := fun v => rfl
  let vb : Fin N → (Fin N → ℝ) := fun i => φ (wV i)
  have hvb : LinearIndependent ℝ vb := hwV.map' φ.toLinearMap (LinearEquiv.ker _)
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let b : Module.Basis (Fin N) ℝ (Fin N → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hvb (by simp)
  have hb : ∀ i, b i = φ (wV i) := fun i => by simp [b, vb]
  set d := (Matrix.of ⇑b).det with hd
  have hgram : (gram ℝ w).det = d ^ 2 := by
    have hG : gram ℝ w = Matrix.of ⇑b * (Matrix.of ⇑b).transpose := by
      ext i j
      rw [Matrix.gram_apply, Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.transpose_apply, hb, hφ]
      have e1 : inner ℝ (w i) (w j) = inner ℝ (f.repr (wV i)) (f.repr (wV j)) := by
        rw [LinearIsometryEquiv.inner_map_map]
        rfl
      rw [e1, PiLp.inner_apply]
      simp [mul_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  have hnorm : ∀ v : V, ‖(v : E)‖ ^ 2 = ∑ j, (φ v j) ^ 2 := by
    intro v
    change ‖v‖ ^ 2 = _
    rw [← f.repr.norm_map, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs, hφ]
  let χ : V →+ (Fin N → ℝ) := φ.toLinearMap.toAddMonoidHom
  have hχ : Function.Injective χ := φ.injective
  let ι : V →+ E := V.subtype.toAddMonoidHom
  let L2g : AddSubgroup (Fin N → ℝ) := (Λ.comap ι).map χ
  let L1 : Submodule ℤ (Fin N → ℝ) := span ℤ (Set.range b)
  have hL1g : L1.toAddSubgroup = (S.comap ι).map χ := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, AddSubgroup.mem_comap]
    constructor
    · intro hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
      refine ⟨∑ i, c i • wV i, ?_, ?_⟩
      · show ((∑ i, c i • wV i : V) : E) ∈ S
        rw [hS, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun ℤ]
        exact ⟨c, by simp [wV]⟩

      · simp [χ, hb, map_sum]
    · rintro ⟨v, hv, rfl⟩
      have hv' : (v : E) ∈ span ℤ (Set.range w) := hv
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv'
      have hvc : v = ∑ i, c i • wV i := Subtype.ext (by simp [wV, ← hc])
      rw [hvc]
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, by simp [χ, hb, map_sum]⟩
  have hΛr : Λ ≤ ι.range := fun x hx => ⟨⟨x, hΛV x hx⟩, rfl⟩
  have hrel : L1.toAddSubgroup.relIndex L2g = I := by
    rw [hL1g, AddSubgroup.relIndex_map_map_of_injective _ _ hχ, AddSubgroup.relIndex_comap,
      AddSubgroup.map_comap_eq_self hΛr]
  let L2 : Submodule ℤ (Fin N → ℝ) := L2g.toIntSubmodule
  have hL12 : L1 ≤ L2 := by
    intro x hx
    have h1 : x ∈ L1.toAddSubgroup := hx
    rw [hL1g] at h1
    exact AddSubgroup.map_mono (AddSubgroup.comap_mono hSΛ) h1
  let b' : Module.Basis (Fin N) ℝ (Fin N → ℝ) := b.unitsSMul (fun _ => Units.mk0 ((I : ℝ)⁻¹) (inv_ne_zero hI0))
  have hb' : ∀ i, b' i = (I : ℝ)⁻¹ • b i := fun i => by
    show (b.unitsSMul _) i = _
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
  have hL2sub : (L2 : Set (Fin N → ℝ)) ⊆ span ℤ (Set.range b') := by
    intro x hx
    have h1 : L1.toAddSubgroup.relIndex L2g • x ∈ L1.toAddSubgroup := relIndex_nsmul_mem _ _ hx
    rw [hrel] at h1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h1
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, ?_⟩
    have hx' : x = (I : ℝ)⁻¹ • (I • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hI0, one_smul]
    rw [hx', ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb', smul_comm]
  haveI : DiscreteTopology L2 := DiscreteTopology.of_subset (inferInstance :
    DiscreteTopology (span ℤ (Set.range b'))) hL2sub
  haveI : IsZLattice ℝ L2 := ⟨by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_le.mpr fun x hx => Submodule.subset_span (hL12 (Submodule.subset_span hx))⟩
  have hcov1 : ZLattice.covolume L1 MeasureTheory.volume = |d| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L1 MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b MeasureTheory.volume), MeasureTheory.Measure.real,
      ZSpan.volume_fundamentalDomain, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hcov2 : ZLattice.covolume L2 MeasureTheory.volume = |d| / I := by
    have h := ZLattice.covolume_div_covolume_eq_relIndex L1 L2 hL12
    have h' : L1.toAddSubgroup.relIndex L2.toAddSubgroup = I := hrel
    rw [h', hcov1] at h
    have hpos : 0 < ZLattice.covolume L2 MeasureTheory.volume := ZLattice.covolume_pos L2 _
    field_simp at h ⊢
    linarith
  let b2 := (Module.Free.chooseBasis ℤ L2).ofZLatticeBasis ℝ L2
  have hspan2 : span ℤ (Set.range b2) = L2 := Module.Basis.ofZLatticeBasis_span ℝ L2 _
  have hF2 : MeasureTheory.IsAddFundamentalDomain L2 (ZSpan.fundamentalDomain b2) MeasureTheory.volume := by
    have := ZSpan.isAddFundamentalDomain b2 MeasureTheory.volume
    rwa [hspan2] at this
  have hvolF2 : MeasureTheory.volume (ZSpan.fundamentalDomain b2) = ENNReal.ofReal (|d| / I) := by
    rw [← hcov2, ZLattice.covolume_eq_measure_fundamentalDomain L2 MeasureTheory.volume hF2,
      MeasureTheory.Measure.real, ENNReal.ofReal_toReal
        (ZSpan.fundamentalDomain_isBounded b2).measure_lt_top.ne]
  haveI : Countable ↥L2.toAddSubgroup := by
    have hc : ((L2.toAddSubgroup : AddSubgroup (Fin N → ℝ)) : Set (Fin N → ℝ)) ⊆
        Set.range (fun c : Fin N → ℤ => ∑ i, c i • b' i) := by
      intro z hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hL2sub hz)
      exact ⟨c, hc⟩
    exact ((Set.countable_range _).mono hc).to_subtype
  haveI : DiscreteTopology ↥L2.toAddSubgroup := inferInstanceAs (DiscreteTopology L2)
  set t : ℝ := (|d| / I) ^ ((N : ℝ)⁻¹) with ht
  have hq : 0 ≤ |d| / I := div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have ht0 : 0 ≤ t := Real.rpow_nonneg hq _
  have htN : t ^ N = |d| / I := Real.rpow_inv_natCast_pow hq (by omega)
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (μ := MeasureTheory.volume) (L := L2.toAddSubgroup)
    (s := Set.Icc (-(fun _ : Fin N => t)) (fun _ : Fin N => t))
    hF2 (fun z hz => ⟨neg_le_neg hz.2, by simpa using neg_le_neg hz.1⟩) (convex_Icc _ _) isCompact_Icc
    (by
      rw [hvolF2, Real.volume_Icc_pi, Module.finrank_fin_fun]
      have e2 : ∏ i : Fin N, ENNReal.ofReal ((fun _ : Fin N => t) i - (-(fun _ : Fin N => t)) i) =
          2 ^ N * ENNReal.ofReal (|d| / I) := by
        simp only [Pi.neg_apply, sub_neg_eq_add, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        rw [← ENNReal.ofReal_pow (by positivity), show t + t = 2 * t by ring, mul_pow, htN,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [e2, mul_comm])
  have hxL2 : (x : Fin N → ℝ) ∈ L2g := x.2
  obtain ⟨v, hv, hvx⟩ := AddSubgroup.mem_map.mp hxL2
  have hxj : ∀ j, |(x : Fin N → ℝ) j| ≤ t := fun j =>
    abs_le.mpr ⟨by simpa using hxs.1 j, hxs.2 j⟩
  refine ⟨(v : E), hv, ?_, ?_⟩
  · intro h0
    apply hx0
    have hv0 : v = 0 := Subtype.ext h0
    apply Subtype.ext
    rw [← hvx, hv0, map_zero]
    rfl
  have hxv : ∀ j, φ v j = (x : Fin N → ℝ) j := fun j => by rw [← hvx]; rfl
  rw [hnorm v]
  calc ∑ j, (φ v j) ^ 2 ≤ ∑ _j : Fin N, t ^ 2 := Finset.sum_le_sum fun j _ => by
        have := pow_le_pow_left₀ (abs_nonneg _) (hxj j) 2
        rwa [sq_abs, ← hxv j] at this
    _ = N * ((gram ℝ w).det / (I : ℝ) ^ 2) ^ (1 / (N : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hgram, ht, one_div]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq, mul_comm, Real.rpow_mul hq, Real.rpow_natCast,
          div_pow, sq_abs]

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0



theorem heights_arith
    (D δ L lr lw1 hN sF laW nuS c g0 i DF PP0' PN tableLineDegreeFive tableLineDegreeTwo PI4 Prw G Pet
      aL ade aG1 aF aG2 HMM HL Hde HF SI SN Ssum δlogδ : ℝ)
    (hD : 3 ≤ D) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcg : c * g0 ≤ 1 / 2)
    (hg0 : 0 ≤ g0) (hi : 1 ≤ i)
    (hP : 1 ≤ PP0' ∧ 1 ≤ PN ∧ 1 ≤ tableLineDegreeFive ∧ 1 ≤ tableLineDegreeTwo ∧ 1 ≤ PI4 ∧ 1 ≤ Prw ∧ 1 ≤ G ∧ 1 ≤ Pet)
    (hlr0 : 0 ≤ lr) (hlr : lr ≤ Prw * L) (hlw1 : lw1 ≤ Prw * L) (hhN : hN / 2 ≤ Prw * L)
    (hDF : DF ≤ L) (hlaW : laW ≤ G * L) (hnu : nuS ≤ PN * L)

    (hUP : sF ≤ (D + 2) * δ * (PP0' * L + max 0 laW + lw1))
    (hb1 : HMM = sF + δ * hN / 2)

    (haL : aL ≤ 4 / 3 * δ) (hade0 : 0 ≤ ade) (hade : ade ≤ aL) (haG10 : 0 ≤ aG1) (haG1 : aG1 ≤ aL)
    (haF0 : 0 ≤ aF) (haF : aF ≤ (D + 4) * aL) (haG20 : 0 ≤ aG2) (haG2 : aG2 ≤ (D + 4) * aL)

    (h7a : HL ≤ HMM + δ * (nuS + tableLineDegreeFive * DF + c * tableLineDegreeTwo) + D * c * g0 * ade * lr + c * g0 * Hde)
    (h7b : Hde ≤ HL + (δ * PI4 * D * L + D * aG1 * lr))
    (h7c : HF ≤ (D + 4) * HL + δ * PI4 * D * L + D * aG2 * lr)

    (hdi : 2 * SI ≤ δlogδ + 2 * Ssum + 2 * D * aF * lr + 2 * HF)
    (hdn : SN / i ≤ g0 * (Hde + D * ade * lr) + δ * Pet) :
    2 * SI ≤ δlogδ + 2 * Ssum + 8 / 3 * D * (D + 4) * δ * Prw * L +
        2 * (D + 4) * (D + 1) * δ *
          (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L ∧
      SN / i ≤ g0 * ((D + 1) * δ *
        (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L +
        4 / 3 * D * δ * Prw * L) + δ * Pet := by
  obtain ⟨hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8⟩ := hP
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have hD2 : 0 ≤ D + 2 := add_nonneg hD0 (by norm_num)
  have hD4 : 0 ≤ D + 4 := add_nonneg hD0 (by norm_num)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hT : 0 ≤ δ * L := mul_nonneg hδ hL0
  have hcg0 : 0 ≤ c * g0 := mul_nonneg hc0 hg0
  have hPP0 : 0 ≤ PP0' := le_trans zero_le_one hP1
  have hPN : 0 ≤ PN := le_trans zero_le_one hP2
  have hFive : 0 ≤ tableLineDegreeFive := le_trans zero_le_one hP3
  have hTwo : 0 ≤ tableLineDegreeTwo := le_trans zero_le_one hP4
  have hPI0 : 0 ≤ PI4 := le_trans zero_le_one hP5
  have hPrw : 0 ≤ Prw := le_trans zero_le_one hP6
  have hG : 0 ≤ G := le_trans zero_le_one hP7
  have hLines : 0 ≤ PN + tableLineDegreeFive + tableLineDegreeTwo :=
    add_nonneg (add_nonneg hPN hFive) hTwo
  have hPL : 0 ≤ Prw * L := mul_nonneg hPrw hL0
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hδ4 : 0 ≤ 4 / 3 * δ := mul_nonneg (by norm_num) hδ
  have hδPL : 0 ≤ 4 / 3 * δ * (Prw * L) := mul_nonneg hδ4 hPL
  have hmax : max 0 laW ≤ G * L := max_le (mul_nonneg hG hL0) hlaW
  have hin : PP0' * L + max 0 laW + lw1 ≤ (PP0' + G + Prw) * L := by
    linarith only [hmax, hlw1]
  have hsF : sF ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) :=
    hUP.trans (mul_le_mul_of_nonneg_left hin (mul_nonneg hD2 hδ))
  have hN2 : δ * hN / 2 ≤ δ * (Prw * L) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hhN hδ
  have hnu2 : δ * (nuS + tableLineDegreeFive * DF + c * tableLineDegreeTwo) ≤ δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) := by
    apply mul_le_mul_of_nonneg_left _ hδ
    have h1 := mul_le_mul_of_nonneg_left hDF hFive
    have h2 := mul_le_mul_of_nonneg_right hc1 hTwo
    have h3 := mul_le_mul_of_nonneg_left hL hTwo
    linarith only [hnu, h1, h2, h3]
  have hadlr : ade * lr ≤ 4 / 3 * δ * (Prw * L) :=
    mul_le_mul (hade.trans haL) hlr hlr0 hδ4
  have hcross : D * c * g0 * ade * lr ≤ D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := by
    have h := mul_le_mul hcg hadlr (mul_nonneg hade0 hlr0) hhalf
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hD0
  have hadl : D * ade * lr ≤ D * (4 / 3 * δ * (Prw * L)) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hadlr hD0
  have hY1 : D * aG1 * lr ≤ D * (4 / 3 * δ * (Prw * L)) := by
    have h := mul_le_mul (haG1.trans haL) hlr hlr0 hδ4
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hD0
  have hA4 : (D + 4) * aL ≤ (D + 4) * (4 / 3 * δ) := mul_le_mul_of_nonneg_left haL hD4
  have hA40 := mul_nonneg hD4 hδ4
  have hY2 : D * aG2 * lr ≤ D * ((D + 4) * (4 / 3 * δ) * (Prw * L)) := by
    have h := mul_le_mul (haG2.trans hA4) hlr hlr0 hA40
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hD0
  have hYF : D * aF * lr ≤ D * ((D + 4) * (4 / 3 * δ) * (Prw * L)) := by
    have h := mul_le_mul (haF.trans hA4) hlr hlr0 hA40
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h hD0
  have hPI : 0 ≤ δ * PI4 * D * L :=
    mul_nonneg (mul_nonneg (mul_nonneg hδ hPI0) hD0) hL0
  have hXb0 : 0 ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := by
    have e1 : 0 ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) :=
      mul_nonneg (mul_nonneg hD2 hδ) (mul_nonneg (add_nonneg (add_nonneg hPP0 hG) hPrw) hL0)
    exact add_nonneg
      (add_nonneg (add_nonneg e1 (mul_nonneg hδ hPL)) (mul_nonneg hδ (mul_nonneg hLines hL0)))
      (mul_nonneg hD0 (mul_nonneg hhalf hδPL))
  have hYb0 : 0 ≤ δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)) :=
    add_nonneg hPI (mul_nonneg hD0 hδPL)
  have hHde : Hde ≤ HL + (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L))) := by
    linarith only [h7b, hY1]
  have hHL1 : HL ≤ ((D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L)))) +
      c * g0 * (HL + (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)))) := by
    have h := mul_le_mul_of_nonneg_left hHde hcg0
    linarith only [h7a, hb1, hsF, hN2, hnu2, hcross, h]
  have hHL : HL ≤ 2 * ((D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L)))) +
      (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L))) := by
    by_cases hHL0 : 0 ≤ HL
    · have a1 := mul_le_mul_of_nonneg_right hcg hHL0
      have a2 := mul_le_mul_of_nonneg_right hcg hYb0
      linarith only [hHL1, a1, a2]
    · linarith only [lt_of_not_ge hHL0, hXb0, hYb0]
  have hHF := mul_le_mul_of_nonneg_left hHL hD4
  have f1 : 0 ≤ (6 * D + 4) * G := mul_nonneg (by linarith only [hD0]) hG
  have f2 : 0 ≤ (10 * D + 8) * PP0' := mul_nonneg (by linarith only [hD0]) hPP0
  have f3 : 0 ≤ (12 * D + 10) * (PN + tableLineDegreeFive + tableLineDegreeTwo) :=
    mul_nonneg (by linarith only [hD0]) hLines
  have f4 : 0 ≤ (10 * D + 12) * PI4 := mul_nonneg (by linarith only [hD0]) hPI0
  have f5 : 0 ≤ (6 * D + 6) * Prw := mul_nonneg (by linarith only [hD0]) hPrw
  have e1 : 0 ≤ (D + 4) * (6 * D + 4) * G := by
    simpa only [mul_assoc] using mul_nonneg hD4 f1
  have e2 : 0 ≤ (D + 4) * (10 * D + 8) * PP0' := by
    simpa only [mul_assoc] using mul_nonneg hD4 f2
  have e3 : 0 ≤ (D + 4) * (6 * D + 6) * Prw := by
    simpa only [mul_assoc] using mul_nonneg hD4 f5
  have e4 : 0 ≤ (D + 4) * (12 * D + 10) * (PN + tableLineDegreeFive + tableLineDegreeTwo) := by
    simpa only [mul_assoc] using mul_nonneg hD4 f3
  have e5 : 0 ≤ (11 * D * D + 55 * D + 48) * PI4 :=
    mul_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD0) hD0)
      (mul_nonneg (by norm_num) hD0)) (by norm_num)) hPI0
  have hE := mul_nonneg hT (add_nonneg (add_nonneg (add_nonneg (add_nonneg e1 e2) e3) e4) e5)
  have hE2 := mul_nonneg hT (add_nonneg (add_nonneg (add_nonneg (add_nonneg f1 f2) f3) f4) f5)
  constructor
  · linarith only [hdi, h7c, hHF, hY2, hYF, hE]
  · have hb : Hde + D * ade * lr ≤ (D + 1) * δ * (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L +
        4 / 3 * D * δ * Prw * L := by
      linarith only [hHde, hHL, hadl, hE2]
    exact hdn.trans (add_le_add (mul_le_mul_of_nonneg_left hb hg0) (le_refl (δ * Pet)))

end ReciprocityTheory.ChartRestriction.G.T0
end

section

namespace ReciprocityTheory.ChartRestriction.G.T0

private theorem choose_succ_mul_succ_eq_choose_mul_sub (n k : ℕ) (h : k ≤ n) :
    ((n.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((n.choose k : ℕ) : ℝ) * ((n : ℝ) - k) := by
  have h1 := Nat.choose_succ_right_eq n k
  have h2 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub h
  rw [← h2]
  exact_mod_cast h1

theorem sub_mul_choose_le_mul_choose (T D : ℕ) (hT : D * (2 * D + 7) ≤ T) :
    ∀ k ≤ D, ((T : ℝ) - k * (2 * D + 7)) * (((T + 2 * D + 6).choose k : ℕ) : ℝ) ≤
      (T : ℝ) * (((T - 1).choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have h7 : 7 * D ≤ T := by nlinarith [Nat.zero_le (D * D)]
    have hA := choose_succ_mul_succ_eq_choose_mul_sub (T + 2 * D + 6) k (by omega)
    have hB := choose_succ_mul_succ_eq_choose_mul_sub (T - 1) k (by omega)
    have ha : ((T + 2 * D + 6 : ℕ) : ℝ) = (T : ℝ) + 2 * D + 6 := by push_cast; ring
    have hT1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [ha] at hA
    rw [hT1] at hB
    have hkT : ((k : ℝ) + 2) ≤ T := by exact_mod_cast (show k + 2 ≤ T by omega)
    have hb : (0 : ℝ) ≤ (T : ℝ) - 1 - k := by linarith
    have hCA : (0 : ℝ) ≤ (((T + 2 * D + 6).choose k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hdiff : (0 : ℝ) ≤ ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
        ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) := by
      have e : ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) =
          (2 * (D : ℝ) + 7) * ((k : ℝ) + 1) * (2 * (D : ℝ) + 6) := by ring
      rw [e]; positivity
    have P := mul_le_mul_of_nonneg_right ih hb
    have Q := mul_nonneg hCA hdiff
    have key : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
        (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ≤
        (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      have e1 : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          ((((T + 2 * D + 6).choose k : ℕ) : ℝ) * ((T : ℝ) + 2 * D + 6 - k)) := by
        linear_combination ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * hA
      have e2 : (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          (T : ℝ) * ((((T - 1).choose k : ℕ) : ℝ) * ((T : ℝ) - 1 - k)) := by
        linear_combination (T : ℝ) * hB
      rw [e1, e2]
      nlinarith [P, Q]
    push_cast
    exact le_of_mul_le_mul_right key hk1

end ReciprocityTheory.ChartRestriction.G.T0
end
