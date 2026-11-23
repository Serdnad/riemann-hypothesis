module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

namespace PIW.AdelClassFin

open NumberField

theorem partBetween : PartBetween := by
  intro E _ _ m N hN δ hδ
  obtain ⟨k, n, hn⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hN
  have hne : Ideal.span {δ} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  haveI : Finite ((𝓞 E) ⧸ Ideal.span {δ}) := by
    first
      | exact (Ideal.absNorm_ne_zero_iff _).mp (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne)
      | exact Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hδE : algebraMap (𝓞 E) E δ ≠ 0 := by
    intro h
    apply hδ
    exact IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero])
  let g := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {δ}))
  let T : Set (Fin m → E) := Set.range (fun c : Fin k → ((𝓞 E) ⧸ Ideal.span {δ}) =>
    (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, (algebraMap (𝓞 E) E (g (c i))) • n i)
  have hT : T.Finite := Set.finite_range _
  have key : ∀ x : Fin m → E, δ • x ∈ N → ∃ t ∈ T, x - t ∈ N := by
    intro x hx
    rw [← hn] at hx
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hx
    have hq : ∀ i, ∃ q : 𝓞 E, algebraMap (𝓞 E) E (a i) -
        algebraMap (𝓞 E) E (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i))) =
        algebraMap (𝓞 E) E δ * algebraMap (𝓞 E) E q := by
      intro i
      have h := Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {δ}))
        (Ideal.Quotient.mk (Ideal.span {δ}) (a i))
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      refine ⟨-c, ?_⟩
      rw [← map_sub, ← map_mul, mul_neg, ← hc, neg_sub]
    choose q hq using hq
    refine ⟨_, ⟨fun i => Ideal.Quotient.mk (Ideal.span {δ}) (a i), rfl⟩, ?_⟩
    have hx2 : x = (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, a i • n i := by
      rw [ha, ← algebraMap_smul E δ x, smul_smul, inv_mul_cancel₀ hδE, one_smul]
    have e1 : ∀ i, a i • n i - (algebraMap (𝓞 E) E (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i)))) • n i =
        (algebraMap (𝓞 E) E δ) • (q i • n i) := by
      intro i
      rw [← algebraMap_smul E (a i), ← algebraMap_smul E (q i), smul_smul, ← sub_smul, hq i]
    have hdiff : x - (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, (algebraMap (𝓞 E) E
        (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i)))) • n i = ∑ i, q i • n i := by
      rw [hx2, ← smul_sub, ← Finset.sum_sub_distrib]
      simp_rw [e1]
      rw [← Finset.smul_sum, smul_smul, inv_mul_cancel₀ hδE, one_smul]
    show x - (algebraMap (𝓞 E) E δ)⁻¹ • ∑ i, (algebraMap (𝓞 E) E
        (g (Ideal.Quotient.mk (Ideal.span {δ}) (a i)))) • n i ∈ N
    rw [hdiff, ← hn]
    exact (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mpr ⟨q, rfl⟩
  apply Set.Finite.subset (hT.powerset.image (fun S => N ⊔ Submodule.span (𝓞 E) S))
  intro M hM
  obtain ⟨hNM, hMδ⟩ := hM
  refine ⟨(M : Set (Fin m → E)) ∩ T, Set.inter_subset_right, ?_⟩
  apply le_antisymm
  · exact sup_le hNM (Submodule.span_le.mpr Set.inter_subset_left)
  · intro x hx
    obtain ⟨t, htT, hxt⟩ := key x (hMδ x hx)
    have htM : t ∈ M := by
      have h := M.sub_mem hx (hNM hxt)
      rwa [sub_sub_cancel] at h
    have e : x = (x - t) + t := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hxt)
      (Submodule.mem_sup_right (Submodule.subset_span ⟨htM, htT⟩))

end PIW.AdelClassFin
end
end

section

noncomputable section

namespace PIW.AdelClassFin

open MeasureTheory Matrix Module
open scoped MatrixOrder

theorem hmk_factor {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef) :
    ∃ B : Matrix (Fin N) (Fin N) ℝ, G = Bᵀ * B := by
  refine ⟨CFC.sqrt G, ?_⟩
  have h0 : (0 : Matrix (Fin N) (Fin N) ℝ) ≤ G := hG.posSemidef.nonneg
  have hsa : IsSelfAdjoint (CFC.sqrt G) := (CFC.sqrt_nonneg G).isSelfAdjoint
  have ht : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsa.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [ht, CFC.sqrt_mul_sqrt_self G h0]

theorem hmk_int {N : ℕ} (x : Fin N → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin N)))) :
    ∃ c : Fin N → ℤ, (fun i => (c i : ℝ)) = x := by
  rw [(Pi.basisFun ℝ (Fin N)).mem_span_iff_repr_mem (R := ℤ) x] at hx
  choose c hc using hx
  refine ⟨c, funext fun i => ?_⟩
  have := hc i
  simp only [Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom] at this
  exact this

theorem hmk_box {N : ℕ} (hN : 1 ≤ N) (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.det ≠ 0) :
    ∃ c : Fin N → ℤ, c ≠ 0 ∧
      ∀ i, |(B *ᵥ fun j => (c j : ℝ)) i| ≤ 2 * |B.det| ^ ((1 : ℝ) / N) := by
  set d := |B.det| with hd
  have hd0 : 0 < d := abs_pos.mpr hB
  set t := 2 * d ^ ((1 : ℝ) / N) with ht
  have ht0 : 0 < t := by positivity
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  have htN : t ^ N = 2 ^ N * d := by
    rw [ht, mul_pow, ← Real.rpow_natCast (d ^ _), ← Real.rpow_mul hd0.le]
    rw [one_div_mul_cancel hN0, Real.rpow_one]
  let f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := Matrix.toLin' B
  have hf : LinearMap.det f ≠ 0 := by rw [LinearMap.det_toLin']; exact hB
  let box : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-t) t
  let s : Set (Fin N → ℝ) := f ⁻¹' box
  let b := Pi.basisFun ℝ (Fin N)
  have fund := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin N → ℝ))
  have hvolF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp
  have hvolbox : volume box = ENNReal.ofReal (2 * t) ^ N := by
    simp only [box]
    rw [volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  have hvols : volume s = ENNReal.ofReal (4 ^ N) := by
    simp only [s]
    rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hf, hvolbox,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [LinearMap.det_toLin', abs_inv, ← hd, mul_pow, htN]
    rw [show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
    field_simp
  have h_symm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
      map_neg, Pi.neg_apply] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith
  have h_conv : Convex ℝ s :=
    (convex_pi fun i _ => convex_Icc (-t) t).linear_preimage f
  have h : volume (ZSpan.fundamentalDomain b) * 2 ^ finrank ℝ (Fin N → ℝ) < volume s := by
    rw [hvolF, one_mul, hvols, Module.finrank_fin_fun]
    rw [show (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  haveI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv h
  obtain ⟨c, hc⟩ := hmk_int (x : Fin N → ℝ) x.2
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply hx0
    ext i
    have := congrFun hc i
    simp at this
    simp [← this]
  · intro i
    have := hxs
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc] at this
    rw [hc]
    exact abs_le.mpr (this i)

theorem partMink : PartMink := by
  intro N hN
  refine ⟨4 * N, fun G hG => ?_⟩
  obtain ⟨B, rfl⟩ := hmk_factor G hG
  have hdet : (Bᵀ * B).det = B.det ^ 2 := by rw [det_mul, det_transpose, sq]
  have hpos := hG.det_pos
  have hB : B.det ≠ 0 := by
    intro h0; rw [hdet, h0] at hpos; simp at hpos
  obtain ⟨c, hc0, hc⟩ := hmk_box hN B hB
  refine ⟨c, hc0, ?_⟩
  set v : Fin N → ℝ := fun i => (c i : ℝ)
  set d := |B.det|
  have hd0 : 0 < d := abs_pos.mpr hB
  have hq : v ⬝ᵥ ((Bᵀ * B) *ᵥ v) = ∑ i, (B *ᵥ v) i ^ 2 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp [dotProduct, sq]
  have hdetG : (Bᵀ * B).det = d ^ 2 := by rw [hdet, sq_abs]
  have hpow : (d ^ ((1 : ℝ) / N)) ^ 2 = (d ^ 2) ^ ((1 : ℝ) / N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast d, ← Real.rpow_mul hd0.le, ← Real.rpow_mul hd0.le,
      mul_comm]
  rw [hq, hdetG, ← hpow]
  calc ∑ i, (B *ᵥ v) i ^ 2 ≤ ∑ _i : Fin N, (2 * d ^ ((1 : ℝ) / N)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq' (abs_le.mp (hc i)).1 (abs_le.mp (hc i)).2
    _ = 4 * N * (d ^ ((1 : ℝ) / N)) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]; ring

end PIW.AdelClassFin
end
end
