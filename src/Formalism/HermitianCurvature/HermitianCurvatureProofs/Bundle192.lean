module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle180
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle181
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle182
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle138
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle119
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle110
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QminorZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialSideRaising
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle080
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle183
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section abstract

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_wsum {ι : Type} [Fintype ι] (Y : Finset α) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (V : ι → α → H) :
    TB.PSDOn Y (fun P Q => ∑ i, (d i : ℂ) * gramH (V i) P Q) := by
  have h := loe_sum (Finset.univ : Finset ι) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun i P Q => (d i : ℂ) * gramH (V i) P Q) fun i _ => by
      have := loe_smul (d i) (hd i) (loe_zero_of_psd (psd_gramH Y (V i)))
      refine loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem loe_sub_states {ι ι' : Type} [Fintype ι] [Fintype ι'] (Y : Finset α) (g : ι → ι') (hg : Function.Injective g)
    (K : ι' → α → α → ℂ) (hK : ∀ j, TB.PSDOn Y (K j)) :
    Loe Y (fun x y => ∑ i, K (g i) x y) (fun x y => ∑ j, K j x y) := by
  have e : ∀ x y, ∑ j, K j x y = ∑ j ∈ Finset.univ.image g, K j x y +
      ∑ j ∈ Finset.univ \ Finset.univ.image g, K j x y := by
    intro x y
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have e2 : ∀ x y, ∑ j ∈ Finset.univ.image g, K j x y = ∑ i, K (g i) x y := by
    intro x y
    rw [Finset.sum_image fun i _ i' _ h => hg h]
  have h1 := loe_sum (Finset.univ \ Finset.univ.image g) (Y := Y) (A := fun _ _ _ => (0 : ℂ)) (B := K)
    fun j _ => loe_zero_of_psd (hK j)
  have h2 := loe_add (loe_refl Y (fun x y => ∑ i, K (g i) x y)) h1
  refine loe_congr (fun x _ y _ => by simp) (fun x _ y _ => ?_) h2
  rw [e, e2]

theorem top_kernel {Ea R N : Type} {Ew : N → Type} [Fintype Ea] [∀ n, Fintype (Ew n)] [Fintype R] [Fintype N]
    (Y : Finset α) (g : ∀ n, Ea → Ew n) (hg : ∀ n, Function.Injective (g n)) (Va : Ea → R → α → H)
    (Vn : ∀ n, Ew n → R → α → H) (da : Ea → R → ℝ) (dn : ∀ n, Ew n → R → ℝ) (hda : ∀ e ρ, 0 ≤ da e ρ)
    (hdn : ∀ n e ρ, 0 ≤ dn n e ρ)
    (lam : N → ℝ) (Pn : N → ℝ) (hPn : ∀ n, 0 < Pn n) (c : ℂ) (C0 : ℝ) (K : ℕ) (hC0 : 0 ≤ C0)
    (hdeg : ∀ P ∈ Y, ∀ e ρ, Va e ρ P = c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P)
    (hwt : ∀ n e ρ, da e ρ * Pn n ≤ C0 ^ K * dn n (g n e) ρ) :
    Loe Y (fun P Q => ∑ e, ∑ ρ, (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => ((‖c‖ ^ 2 * (∑ n, |lam n|) * C0 ^ K : ℝ) : ℂ) *
        ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) := by
  set Λ : ℝ := ∑ n, |lam n| with hΛ

  have s1 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Va e ρ) P Q)
      (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * (((∑ n, ‖(lam n : ℂ)‖ : ℝ) : ℂ) *
        ∑ n, ((‖(lam n : ℂ)‖ : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ
    have hc := loe_convex Y (fun n => (lam n : ℂ)) (fun n P => Vn n (g n e) ρ P)
    have hc2 := loe_smul (da e ρ * ‖c‖ ^ 2) (mul_nonneg (hda e ρ) (sq_nonneg _)) hc
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => by push_cast; ring) hc2
    have : gramH (Va e ρ) P Q = gramH (fun P => c • ∑ n, (lam n : ℂ) • Vn n (g n e) ρ P) P Q := by
      unfold gramH; rw [hdeg P hP e ρ, hdeg Q hQ e ρ]
    rw [this, gramH_smul]
    push_cast; ring
  have hnorm : ∀ n, ‖(lam n : ℂ)‖ = |lam n| := fun n => by rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [hnorm] at s1

  have s2 : ∀ e ρ n, Loe Y (fun P Q => (da e ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)) := by
    intro e ρ n
    have h := loe_scale (psd_gramH Y (Vn n (g n e) ρ)) (r := da e ρ) (r' := C0 ^ K / Pn n * dn n (g n e) ρ) (by
      have := hwt n e ρ
      rw [sub_nonneg, div_mul_eq_mul_div, le_div_iff₀ (hPn n)]
      linarith)
    refine loe_congr (fun _ _ _ _ => rfl) (fun P _ Q _ => by push_cast; ring) h

  have s3 : ∀ n, Loe Y (fun P Q => ∑ e, ∑ ρ, (dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q)
      (fun P Q => ∑ e', ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q) :=
    fun n => loe_sub_states Y (g n) (hg n) (fun e' P Q => ∑ ρ, (dn n e' ρ : ℂ) * gramH (Vn n e' ρ) P Q)
      fun e' => psd_wsum Y (fun ρ => dn n e' ρ) (fun ρ => hdn n e' ρ) (fun ρ => Vn n e' ρ)

  have c1 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => s1 e ρ
  refine loe_trans c1 ?_

  have c2 : ∀ e ρ, Loe Y (fun P Q => (da e ρ : ℂ) * ((‖c‖ ^ 2 : ℝ) : ℂ) * ((Λ : ℂ) *
        ∑ n, ((|lam n| : ℝ) : ℂ) * gramH (Vn n (g n e) ρ) P Q))
      (fun P Q => ((‖c‖ ^ 2 * Λ : ℝ) : ℂ) * ∑ n, ((|lam n| : ℝ) : ℂ) *
        (((C0 ^ K / Pn n : ℝ) : ℂ) * ((dn n (g n e) ρ : ℂ) * gramH (Vn n (g n e) ρ) P Q))) := by
    intro e ρ
    have h := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
      (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n|) (abs_nonneg _) (s2 e ρ n))
    refine loe_congr (fun P _ Q _ => ?_) (fun _ _ _ _ => rfl) h
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring
  have c3 := loe_sum (Finset.univ : Finset Ea) fun e _ => loe_sum (Finset.univ : Finset R) fun ρ _ => c2 e ρ
  refine loe_trans (loe_congr (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) c3) ?_
  have c4 := loe_smul (‖c‖ ^ 2 * Λ) (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => abs_nonneg _))
    (loe_sum (Finset.univ : Finset N) fun n _ => loe_smul (|lam n| * (C0 ^ K / Pn n))
      (mul_nonneg (abs_nonneg _) (div_nonneg (pow_nonneg hC0 _) (hPn n).le)) (s3 n))
  refine loe_congr (fun P _ Q _ => ?_) (fun P _ Q _ => ?_) c4
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    refine Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring
  · simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun ρ _ => ?_
    push_cast; ring

end abstract

end

end Formalism.FourierDecayAlt.P.PBL
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem om_cast {a b : ℕ} (h : a = b) (v v' : Fin (2 * a + k + 1) → ℂ) (g : B.Mat k a) (hg : g ∈ JF.Om k a v v') :
    D.castM h g ∈ JF.Om k b (D.castV h v) (D.castV h v') := by
  subst h; rwa [Dx2.MN.castM_rfl, Dx2.Tower.castV_rfl, Dx2.Tower.castV_rfl]

theorem lowV_lift (ρ : ℕ) (v : Fin (2 * ρ + k + 1) → ℂ) : U.lowV k 1 ρ (liftVec k 1 ρ v) = v := by
  funext i
  simp only [U.lowV, liftVec]
  rw [dite_eq_left (by omega)]
  congr 1; ext; simp

theorem mcOm : MCOm := by
  intro k ρ z0 z0' hz0 hz0' c hc γ hγ hγO
  apply om_cast
  set Z : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => c with hZd
  have hZdet : Z.det = c := by rw [Matrix.det_unique]; rfl
  have hz := Qx4.lift_inWb hz0
  have hz' := Qx4.lift_inWb hz0'
  have hZ : Zhat k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
      Matrix.reindex (Ux3.eC 1 ρ) (Ux3.eC 1 ρ) (Matrix.fromBlocks Z 0 0 (Zhat k ρ z0 z0' γ)) := by
    unfold U.mMap
    rw [Ux3.z_hat_of_block3 _ _ hz hz', Formalism.QuantumDeterminants.Zhat_eq, lowV_lift, lowV_lift]
    congr 1
    simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k 1 ρ).1 Z γ (by rw [hZdet]; exact hc) hγ, ?_, ?_⟩
  · intro l hl
    obtain ⟨lv, hlv⟩ := l
    rcases Nat.eq_zero_or_pos lv with h0 | hpos
    · subst h0
      unfold Dmin
      rw [Matrix.det_isEmpty]; exact one_ne_zero
    · obtain ⟨l', rfl⟩ : ∃ l', lv = 1 + l' := ⟨lv - 1, by omega⟩
      have hl' : l' ≤ ρ := by simp only at hl; omega
      unfold Dmin
      rw [hZ, Ux3.minor_blocks Z _ l' (by omega) (by omega), hZdet]
      refine mul_ne_zero hc ?_
      exact hγO.1 ⟨l', by omega⟩ hl'
  · have h1 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) (Fin.last _) =
        Z.det * Dmin k ρ z0 z0' γ (Fin.last _) := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ (ρ + 1) le_rfl _
    have h0 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) ⟨1 + ρ, by omega⟩ =
        Z.det * Dmin k ρ z0 z0' γ ⟨ρ, by omega⟩ := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ ρ (by omega) _
    have ht : Tz k (1 + ρ) (liftVec k 1 ρ z0) = Tz k ρ z0 := by rw [Ux3.tz_low _ hz, lowV_lift]
    have ht' : Tz k (1 + ρ) (liftVec k 1 ρ z0') = Tz k ρ z0' := by rw [Ux3.tz_low _ hz', lowV_lift]
    have hG : Gf k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
        Complex.normSq c * Gf k ρ z0 z0' γ := by
      unfold Gf
      rw [h1, h0, ht, ht', hZdet, Complex.normSq_mul, Complex.normSq_mul]
      ring
    rw [hG]
    exact mul_pos (Complex.normSq_pos.2 hc) hγO.2

theorem jfStep : JFStep := jfStep_of mcOm

end Formalism.FourierDecayAlt.P.PBH
end
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JDAToda

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem omB_eq {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Gauge.OmB Bs = Q.OmPlus k r Bs.z Bs.z' := by
  ext g
  constructor
  · rintro ⟨hG, hD⟩
    refine ⟨fun l hl => ?_, hG⟩
    rcases Nat.eq_zero_or_pos l.val with h0 | hpos
    · have : l = ⟨0, by omega⟩ := Fin.ext h0
      rw [this, show Dmin k r Bs.z Bs.z' g ⟨0, by omega⟩ = 1 by unfold Dmin; exact Matrix.det_isEmpty]
      exact one_ne_zero
    · have := hD ⟨l.val - 1, by omega⟩
      have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (r + 2)) = l := Fin.ext (by simp; omega)
      simpa [e] using this
  · rintro ⟨hD, hG⟩
    exact ⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by show a.val + 1 ≤ r; have := a.isLt; omega)⟩

theorem gg_pos {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hcg : wCell k r (Fin.last r) c * g ∈ Gauge.OmB Bs) :
    0 < GGl k r Bs.z Bs.z' g := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Formalism.FourierDecayAlt.P5.Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * B2.embWb k r μ = bigCell k r c μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  have hmin := big_cell_minors_holds k r Bs.z Bs.z' c μ Bs.z_mem Bs.z'_mem
  have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ Bs.z') Bs.z = zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ) := by
    rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart Bs.z'_mem, Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
  have hr : Dmin k r Bs.z Bs.z' (bigCell k r c μ) ⟨r, by omega⟩ = ∏ a, c a := by
    have h := hmin.1 (Fin.last r)
    simp only [Fin.val_last] at h
    rw [h]
    simp
  have hP0 : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Dmin k r Bs.z Bs.z' (bigCell k r c μ) (Fin.last (r + 1)) =
      (∏ a, c a) * zetaL k r Bs.z Bs.z' (Fin.last r) (B2.embWb k r μ) := by
    have hzeta := hmin.2.2 hc
    rw [hζ] at hzeta
    unfold Formalism.QuantumDeterminants.zeta at hzeta
    rw [hr] at hzeta
    rw [← hzeta, mul_div_cancel₀ _ hP0]
  have hGf : Gf k r Bs.z Bs.z' (bigCell k r c μ) =
      Complex.normSq (∏ a, c a) * GGl k r Bs.z Bs.z' (B2.embWb k r μ) := by
    unfold Gf GGl
    rw [hlast, hr, Complex.normSq_mul]
    ring
  have h1 := hcg.1
  rw [e, hGf] at h1
  exact pos_of_mul_pos_right h1 (Complex.normSq_nonneg _)

theorem minorCell_of {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hf : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') J) (hLf : LeftEq k r Bs.z 0 (OmPlus k r Bs.z Bs.z') J)
    (hRf : RightEq k r Bs.z' 0 (OmPlus k r Bs.z Bs.z') J) (y : ℂ) (x : (Fin r → ℂ) × Mx k r)
    (hx : x ∈ DomR k r Bs.z Bs.z') :
    Q.resG k r (Fin.last r) (qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) J) x.1 x.2 =
      Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) J) x.1 x.2 := by
  have hRR := Formalism.FourierDecayAlt.P.right_rule_derivative
  have hLR := Formalism.FourierDecayAlt.P.left_rule_cell
  have hTC := Formalism.FourierDecayAlt.P.torus_cell
  have hGP := Formalism.FourierDecayAlt.P.gauge_positivity
  set D := OmPlus k r Bs.z Bs.z' with hDdef
  have hD : IsOpen D := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus Bs.z Bs.z'
  have h1N : (1 : Mx k r) ∈ Nlev k r 0 :=
    ⟨(Formalism.QuantumDeterminants.unipotent_subgroup_holds k r).1, by simp [Glev, UH]⟩
  have hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D := by
    intro g hg n hn
    have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) Bs.z_mem Bs.z'_mem
    have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z, n, hn, (one_mul n).symm⟩ 1
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one Bs.z', 1, h1N, (one_mul 1).symm⟩
    rwa [Matrix.mul_one] at this
  set v₀ : VS k r 0 D (Wq →L[ℂ] Wp) := ⟨cut k r 0 D J, cut_mem hD hf⟩ with hv₀
  have hcellB : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ C6.bigPos Bs := fun c hc =>
    (Formalism.FourierDecayAlt.P.big_cell_values k r Wp Wq Bs (c, x.2) ⟨hc, hx.2.1, hx.2.2⟩).1
  have hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * x.2 ∈ Glev k r 0 ∩ D := by
    intro c hc
    have h := hcellB c hc
    exact ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 h.1, fun l _ => h.2.2 l (by simp), h.2.1⟩
  have hdiff : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD, ∀ c ∈ OmX r, DifferentiableAt ℝ
      (fun c' => ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp))
        (wCell k r (Fin.last r) c' * x.2)) c :=
    fun x' c hc => cell_diff Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2 hc
  have hWS : ∀ x' : SA (E := Wq →L[ℂ] Wp) hD,
      resW ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) x.2 ∈ WSm r (Wq →L[ℂ] Wp) :=
    fun x' => resG_wsm Bs ((x' : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀).2.1 hx.2.1 hx.2.2
  have hcl := claim hD v₀ x.2 y hRR hLR hTC hGP Bs.z Bs.z' Bs.z_mem Bs.z'_mem hN hf hLf hRf rfl hx.2.1 hcell hdiff hWS
    r le_rfl 1 (Subalgebra.one_mem _) x.1 hx.1
  rw [mul_one] at hcl
  have vAB_loc : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp)),
      (∀ c ∈ OmX r, f₁ c = f₂ c) → ∀ c ∈ OmX r,
      (Q.vAB r y i).1 f₁ c = (Q.vAB r y i).1 f₂ c ∧
      (Q.vAB r y i).2 f₁ c = (Q.vAB r y i).2 f₂ c := by
    intro i
    induction i with
    | zero => intro f₁ f₂ h c hc; exact ⟨h c hc, rfl⟩
    | succ i ih =>
      intro f₁ f₂ h c hc
      have hi' := ih f₁ f₂ h
      by_cases hi : i < r
      · simp only [Q.vAB, dif_pos hi]
        refine ⟨?_, ?_⟩
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
          have hev : (Q.vAB r y i).1 f₁ =ᶠ[nhds c] (Q.vAB r y i).1 f₂ := by
            filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc'
            exact (hi' c' hc').1
          simp only [pOp, wirt, if_pos hc, hev.fderiv_eq]
          rw [(hi' c hc).1, (hi' c hc).2]
        · simp only [ciOp]
          rw [(hi' c hc).1]
      · simp only [Q.vAB, dif_neg hi]
        exact hi' c hc
  have eR : Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) J) x.1 x.2 =
      (Q.vAB r y r).1 (fun c' => Q.resG k r (Fin.last r)
        (((1 : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) v₀ : Mx k r → (Wq →L[ℂ] Wp)) c' x.2) x.1 := by
    refine (vAB_loc r _ _ (fun c' hc' => ?_) x.1 hx.1).1
    rw [resG_last, resG_last]
    congr 1
    exact (cut_of_mem _ (hcell c' hc')).symm
  rw [eR, ← hcl, resG_last, resG_last]
  congr 1
  have hγ := hcell x.1 hx.1
  have e1 : ((qminor (EA (E := Wq →L[ℂ] Wp) hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2) : SA (E := Wq →L[ℂ] Wp) hD) : Module.End ℂ (VS k r 0 D (Wq →L[ℂ] Wp))) =
      qminor (Eh (E := Wq →L[ℂ] Wp) (i := 0) hD) (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) := by
    have := map_qminor (SA (E := Wq →L[ℂ] Wp) hD).val (EA hD) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
      (y + ((2 * r + k : ℕ) : ℂ) / 2)
    rw [Subalgebra.coe_val] at this
    rw [this]
    exact qminor_reindex (Eh hD) cI cI_inj _ _ _
  rw [e1, rep_qminor hD _ _ _ v₀ _ hγ]
  have hpos : posL k r 0 ∘ (cI ∘ C3.xR k r r le_rfl) = C3.xR k r r le_rfl := funext fun l => posL_cI _
  have hloc := (good_qminor (E := Wq →L[ℂ] Wp) hD (cI ∘ C3.xR k r r le_rfl) (cI ∘ C3.xR k r r le_rfl)
    (y + ((2 * r + k : ℕ) : ℂ) / 2)).loc (cut k r 0 D J) J (fun x' hx' => cut_of_mem _ hx')
    _ hγ
  rw [hpos] at hloc
  rw [hpos]
  exact hloc.symm

theorem uC_zero (k r : ℕ) (y : ℂ) : Q.uC k r 0 y = y + ((2 * r + k : ℕ) : ℂ) / 2 := by
  simp only [Q.uC, Q.mdim, Fin.val_zero, Nat.sub_zero]
  push_cast
  ring

end Formalism.FourierDecayAlt.P.CutMP.JDAToda

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jda_capelli_toda_proof : JDACapToda := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have hGG := JDAToda.gg_pos Bs hc hg hcg
  have hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hc, hg, hGG⟩
  obtain ⟨hf, hLf, hRf, -⟩ := hJ
  rw [JDAToda.omB_eq] at hf hLf hRf
  have hm := JDAToda.minorCell_of Bs hf hLf hRf y (c, g) hx
  have hcell := Formalism.FourierDecayAlt.P.raising_cell P.k P.r (Wq →L[ℂ] Wp) J (Q.uC P.k P.r 0 y) c g hg
  simp only [dMul, drF, Q.crd, Q.cmp, ↓reduceIte] at hm ⊢
  rw [← hm]
  simp only [Q.resG, capA]
  rw [hcell, JDAToda.uC_zero, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_of_coefficients_holds : SmoothOfCoeffs := by
  intro k r E _ _ _ Dm J h g₀ hg₀
  let b := Module.finBasis ℂ E
  let ℓ : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  choose U F hU hgU hF hJF using fun i => h (ℓ i) g₀ hg₀
  refine ⟨⋂ i, U i, fun g => ∑ i, F i g • b i, isOpen_iInter_of_finite hU, Set.mem_iInter.2 hgU, ?_, ?_⟩
  · refine ContDiffOn.sum fun i _ => ?_
    exact ((hF i).mono (Set.iInter_subset _ i)).smul contDiffOn_const
  · intro g hg hgG
    have hg' := Set.mem_iInter.1 hg
    conv_lhs => rw [← b.sum_repr (J g)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hJF i g (hg' i) hgG]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

def NFOpOKMulG : Prop :=
  ∀ C : ℝ, ∃ C' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (N : ℕ) (Th : B.DiffOp P.k P.r Wp Wq), NFOpOK C p N Th →
      ∃ Th' : B.DiffOp P.k P.r Wp Wq, NFOpOK C' p N Th' ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
          B.opApply Th' F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • B.opApply Th F g

end

end Formalism.FourierDecayAlt.P.CutBP
end
