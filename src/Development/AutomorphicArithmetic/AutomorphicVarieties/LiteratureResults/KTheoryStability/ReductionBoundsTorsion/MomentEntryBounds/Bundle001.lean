module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SubLeSumAbsConsecutiveDiff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Disc

theorem eq_zero_of_lt_one {L : Type} [Field L] [NumberField L] (a : 𝓞 L)
    (h : ∀ w : InfinitePlace L, w (a : L) < 1) : a = 0 := by
  apply GlobalTheory.SmallIntegerVanishing.eq_zero_of_small <;> assumption

theorem continuous_entry {L : Type} [Field L] [NumberField L] {N : ℕ} (w : InfinitePlace L) (i j : Fin N) :
    Continuous fun x : Sp L N => mt x w i j := by
  fun_prop

theorem mt_latS {L : Type} [Field L] [NumberField L] {N : ℕ} (σ : SpecialLinearGroup (Fin N) (𝓞 L))
    (w : InfinitePlace L) (i j : Fin N) :
    mt ((MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w)) σ) w i j =
      w.embedding (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j : 𝓞 L) : L) := rfl

theorem countable_O (L : Type) [Field L] [NumberField L] : Countable (𝓞 L) :=
  (RingOfIntegers.basis L).equivFun.injective.countable

end PositivityTheory.KB.MomentRationality.Disc

namespace PositivityTheory.KB

open MomentRationality MomentRationality.Disc

theorem discrete_specialLinearGroup_ringOfIntegers : SDisc := by
  intro L _ _ N
  refine ⟨?_, ?_⟩
  · rw [discreteTopology_iff_isOpen_singleton_one]
    let U : Set (Sp L N) :=
      {x | ∀ w i j, ‖mt x w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1}
    have hU : IsOpen U := by
      simp only [U, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i =>
        isOpen_iInter_of_finite fun j =>
          isOpen_lt ((continuous_entry w i j).sub continuous_const).norm continuous_const
    refine isOpen_induced_iff.2 ⟨U, hU, ?_⟩
    ext ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hγU
      obtain ⟨σ, rfl⟩ := hγ
      have hσ : σ = 1 := by
        refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
        have h0 := eq_zero_of_lt_one
          (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j) - (1 : Matrix (Fin N) (Fin N) (𝓞 L)) i j) (fun w => ?_)
        · simpa using sub_eq_zero.1 h0
        · have h1 := hγU w i j
          rw [mt_latS] at h1
          rw [← norm_embedding_eq]
          convert h1 using 2
          by_cases hij : i = j
          · subst hij
            simp
          · simp [Matrix.one_apply, hij]
      subst hσ
      apply Subtype.ext
      simp
    · intro h
      have h' : γ = 1 := congrArg Subtype.val h
      subst h'
      intro w i j
      have hone : mt (1 : Sp L N) w = 1 := rfl
      rw [hone, sub_self, norm_zero]
      exact one_pos
  · haveI := countable_O L
    haveI : Countable (Matrix (Fin N) (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable (Fin N → Fin N → 𝓞 L))
    haveI : Countable (SpecialLinearGroup (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable {A : Matrix (Fin N) (Fin N) (𝓞 L) // A.det = 1})
    exact (MonoidHom.rangeRestrict_surjective
      (MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w))).countable

end PositivityTheory.KB

end
end

section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

abbrev gi (g : GL (Fin N) L) : Matrix (Fin N) (Fin N) L := ((g⁻¹ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L)

theorem z_ne (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (w : InfinitePlace L) : z w ≠ 0 := by
  intro h
  have h1 := hc w
  rw [h, zero_smul] at h1
  have h2 : (mt c w).det = 1 := (c w).prop
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [h1, Matrix.det_zero] at h2
  exact zero_ne_one h2

theorem emb_toL (y : Lat L N) (w : InfinitePlace L) (a : Fin N) : w.embedding (toL y a) = toR y w a := rfl

theorem cinv_vec (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (y : Lat L N) (w : InfinitePlace L) :
    mt c⁻¹ w *ᵥ toR y w = (z w)⁻¹ • (fun a => w.embedding ((gi g *ᵥ toL y) a)) := by
  have hz := z_ne hN hc w
  have hgg : (g : Matrix (Fin N) (Fin N) L) * gi g = 1 := g.mul_inv
  have hinv : mt c⁻¹ w * mt c w = 1 := by
    show (((c w)⁻¹ : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (c w : Matrix (Fin N) (Fin N) ℂ) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hx : toR y w = mt c w *ᵥ ((z w)⁻¹ • (fun a => w.embedding ((gi g *ᵥ toL y) a))) := by
    rw [hc w, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]
    funext a
    change toR y w a = ((g : Matrix (Fin N) (Fin N) L).map w.embedding *ᵥ (w.embedding ∘ (gi g *ᵥ toL y))) a
    rw [← RingHom.map_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, emb_toL]
  rw [hx, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem cT_vec {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (y : Lat L N) (w : InfinitePlace L) :
    (mt c w)ᵀ *ᵥ toR y w = z w • (fun a => w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) a)) := by
  rw [hc w, transpose_smul, smul_mulVec, ← transpose_map]
  congr 1
  ext a
  have := RingHom.map_mulVec w.embedding (g : Matrix (Fin N) (Fin N) L)ᵀ (toL y) a
  rw [this]
  rfl

theorem toL_ne {y : Lat L N} (hy : y ≠ 0) : toL y ≠ 0 := by
  intro h
  apply hy
  funext a
  have h1 := congrFun h a
  simpa [toL] using h1

theorem gi_ne (g : GL (Fin N) L) {y : Lat L N} (hy : y ≠ 0) : gi g *ᵥ toL y ≠ 0 := by
  intro h
  apply toL_ne hy
  have := congrArg (fun v => (g : Matrix (Fin N) (Fin N) L) *ᵥ v) h
  simpa [mulVec_mulVec, Units.mul_inv, one_mulVec] using this

theorem gT_ne (g : GL (Fin N) L) {y : Lat L N} (hy : y ≠ 0) : (g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y ≠ 0 := by
  intro h
  apply toL_ne hy
  have h2 : (gi g)ᵀ * (g : Matrix (Fin N) (Fin N) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]
  have h1 : (gi g)ᵀ *ᵥ ((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) = (gi g)ᵀ *ᵥ 0 := by rw [h]
  rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at h1

theorem int_d {d : ℤ} {G : Matrix (Fin N) (Fin N) L} (hd : ∀ i j, IsIntegral ℤ ((d : L) * G i j)) (y : Lat L N)
    (a : Fin N) : IsIntegral ℤ ((d : L) * (G *ᵥ toL y) a) := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [← mul_assoc]
  exact (hd a j).mul (RingOfIntegers.isIntegral_coe (y j))

theorem sum_sq_ge (hL : IsTotallyComplex L) {d : ℤ} (hd : d ≠ 0) {β : L} (hβ : β ≠ 0)
    (hint : IsIntegral ℤ ((d : L) * β)) : ((d : ℝ) ^ 2)⁻¹ ≤ ∑ w : InfinitePlace L, ‖w.embedding β‖ ^ 2 := by
  have hdR : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
  let α : 𝓞 L := ⟨(d : L) * β, hint⟩
  have hαc : ((α : 𝓞 L) : L) = (d : L) * β := rfl
  have hα0 : α ≠ 0 := by
    intro h
    have h1 : ((α : 𝓞 L) : L) = 0 := by rw [h]; rfl
    rw [hαc] at h1
    exact mul_ne_zero (Int.cast_ne_zero.mpr hd) hβ h1
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, 1 ≤ w ((α : 𝓞 L) : L) := by
    by_contra H
    push_neg at H
    obtain ⟨w0⟩ : Nonempty (InfinitePlace L) := inferInstance
    exact absurd (InfinitePlace.one_le_of_lt_one hα0 (fun z _ => H z)) (not_le.mpr (H w0))
  have hwα : w ((α : 𝓞 L) : L) = |(d : ℝ)| * ‖w.embedding β‖ := by
    rw [← InfinitePlace.norm_embedding_eq, hαc, map_mul, norm_mul, map_intCast, Complex.norm_intCast]
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have h1 : 1 ≤ (d : ℝ) ^ 2 * ‖w.embedding β‖ ^ 2 := by
    have h2 : (1 : ℝ) ≤ (|(d : ℝ)| * ‖w.embedding β‖) ^ 2 := one_le_pow₀ (hwα ▸ hw)
    rwa [mul_pow, sq_abs] at h2
  have key : ((d : ℝ) ^ 2)⁻¹ ≤ ‖w.embedding β‖ ^ 2 := by
    calc ((d : ℝ) ^ 2)⁻¹ = ((d : ℝ) ^ 2)⁻¹ * 1 := (mul_one _).symm
      _ ≤ ((d : ℝ) ^ 2)⁻¹ * ((d : ℝ) ^ 2 * ‖w.embedding β‖ ^ 2) := by gcongr
      _ = ‖w.embedding β‖ ^ 2 := by field_simp
  exact key.trans (Finset.single_le_sum (f := fun v : InfinitePlace L => ‖v.embedding β‖ ^ 2)
    (fun v _ => sq_nonneg _) (Finset.mem_univ w))

end PositivityTheory.KB.MomentRationality.Ht
end
end

section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem mt_mul (x y : Sp L N) (w : InfinitePlace L) :
    mt (x * y) w = mt x w * mt y w := rfl

theorem mt_one (w : InfinitePlace L) : mt (1 : Sp L N) w = 1 := rfl

theorem mt_inv_mul (x : Sp L N) (w : InfinitePlace L) : mt x⁻¹ w * mt x w = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem mt_mul_inv (x : Sp L N) (w : InfinitePlace L) : mt x w * mt x⁻¹ w = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem ofS_inv_coe (x : Sp L N) (w : InfinitePlace L) :
    ((((ofS L N x) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = mt x⁻¹ w := by
  rw [← Pi.inv_apply, ← map_inv]
  rfl

theorem mat_one (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

theorem q_actL (x : Sp L N) (y : Lat L N) :
    q (actL (ofS L N x) (one L N).1) y = ∑ w, ∑ i, ‖(mt x⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  rw [hm, re_quad]

theorem q_dual (x : Sp L N) (y : Lat L N) :
    q (dualH (actL (ofS L N x) (one L N).1)) y =
      ∑ w, ∑ i, ‖((mt x w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hBM : mt x⁻¹ w * mt x w = 1 := mt_inv_mul x w
  have hMB : mt x w * mt x⁻¹ w = 1 := mt_mul_inv x w
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  have hinv : (mat (actL (ofS L N x) (one L N).1) w)⁻¹ = mt x w * (mt x w)ᴴ := by
    rw [hm]
    refine Matrix.inv_eq_left_inv ?_
    calc mt x w * (mt x w)ᴴ * ((mt x⁻¹ w)ᴴ * mt x⁻¹ w)
        = mt x w * (mt x⁻¹ w * mt x w)ᴴ * mt x⁻¹ w := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBM, Matrix.conjTranspose_one, Matrix.mul_one, hMB]
  have hd : mat (dualH (actL (ofS L N x) (one L N).1)) w =
      ((mt x w)ᵀ)ᴴ * (mt x w)ᵀ := by
    simp only [dualH, mat_mkHS]
    rw [hinv, Matrix.transpose_mul]
    rfl
  rw [hd, re_quad]

theorem lam_ge (hN : 1 ≤ N) {h : HS L N} {κ : ℝ} (hκ : ∀ y : Lat L N, y ≠ 0 → κ ≤ q h y) : κ ≤ lam h := by
  have hne : Nonempty {y : Lat L N // y ≠ 0} := by
    refine ⟨⟨fun _ => 1, fun h0 => ?_⟩⟩
    have := congrFun h0 ⟨0, hN⟩
    exact one_ne_zero this
  unfold lam
  exact le_ciInf fun y => hκ y.1 y.2

end PositivityTheory.KB.MomentRationality.Ht
end
end
