module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle014
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

variable {f p q : ℕ}

theorem dkV_contDiff (k : Fin f) :
    ContDiff ℝ ∞ (fun v : V (nD f p q) => dk v k) := by
  have hZ : ∀ a b, ContDiff ℝ ∞ (fun v : V (nD f p q) => Zof v k a b) := by
    intro a b
    unfold Zof
    simp only [Matrix.of_apply]
    exact ((EuclideanSpace.proj (𝕜 := ℂ)
      (finProdFinEquiv (k, finProdFinEquiv (a, b)))).contDiff).restrict_scalars ℝ
  have hM : ∀ a b, ContDiff ℝ ∞ (fun v : V (nD f p q) =>
      (1 - Zof v k * (Zof v k)ᴴ : Matrix (Fin p) (Fin p) ℂ) a b) := by
    intro a b
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact contDiff_const.sub (ContDiff.sum fun c _ => (hZ a c).mul (Complex.conjCLE.contDiff.comp (hZ b c)))
  have hdet : ContDiff ℝ ∞ (fun v : V (nD f p q) => (1 - Zof v k * (Zof v k)ᴴ).det) := by
    simp only [Matrix.det_apply']
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)
  unfold dk
  exact Complex.reCLM.contDiff.comp hdet

private lemma fderiv_ofReal_sub_const {n : ℕ} (g : V n → ℝ) (K : ℝ) :
    fderiv ℝ (fun y => (((g y - K : ℝ)) : ℂ)) = fderiv ℝ (fun y => ((g y : ℝ) : ℂ)) := by
  funext y
  have h : (fun y => (((g y - K : ℝ)) : ℂ)) = fun y => ((g y : ℝ) : ℂ) - (K : ℂ) := by
    funext z
    push_cast
    ring
  rw [h, fderiv_sub_const]

private lemma wd_ofReal_sub_const {n : ℕ} (g : V n → ℝ) (K : ℝ) (j : Fin n) (y : V n) :
    wd n j (fun y => (((g y - K : ℝ)) : ℂ)) y = wd n j (fun y => ((g y : ℝ) : ℂ)) y := by
  unfold wd
  rw [fderiv_ofReal_sub_const]

private lemma leviV_ofReal_sub_const {n : ℕ} (g : V n → ℝ) (K : ℝ) (y : V n) (ξ : Fin n → ℂ) :
    leviV n (fun y => (((g y - K : ℝ)) : ℂ)) y ξ = leviV n (fun y => ((g y : ℝ) : ℂ)) y ξ := by
  have h : ∀ k, wdb n k (fun y => (((g y - K : ℝ)) : ℂ)) = wdb n k (fun y => ((g y : ℝ) : ℂ)) := by
    intro k
    funext z
    unfold wdb
    rw [fderiv_ofReal_sub_const]
  unfold leviV
  simp only [h]

theorem rhGrad_main (hf : 0 < f) (hm : 0 < min p q) (v0 : V (nD f p q)) (hv0 : v0 ∈ Dset f p q)
    (ξ : Fin (nD f p q) → ℂ) :
    Complex.normSq (∑ j, wd (nD f p q) j (fun w => ((rh w : ℝ) : ℂ)) v0 * ξ j) ≤
      ((f * min p q : ℕ) : ℝ) * (leviV (nD f p q) (fun w => ((rh w : ℝ) : ℂ)) v0 ξ).re := by
  classical
  have hf0 : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have hfR : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hmR : (0 : ℝ) < ((min p q : ℕ) : ℝ) := by exact_mod_cast hm
  have hm0 : ((min p q : ℕ) : ℝ) ≠ 0 := hmR.ne'
  have hC_eq : (((f * min p q : ℕ)) : ℝ) = (f : ℝ) * ((min p q : ℕ) : ℝ) := by push_cast; ring
  have hCpos : (0 : ℝ) < ((f * min p q : ℕ) : ℝ) := by rw [hC_eq]; positivity
  haveI : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  choose Q hQc hQL hQ0 hQle using fun k : Fin f => RgD.block hm hv0 k
  have hdk : ∀ v ∈ Dset f p q, ∀ k, 0 < dk v k := by
    intro v hv k
    have hv' : ∀ k, (1 - Zof v k * (Zof v k)ᴴ).PosDef := hv
    have h := (hv' k).det_pos
    exact (Complex.pos_iff.mp h).1
  have hkey : ∀ v ∈ Dset f p q, 0 < ∑ k, Q k v ∧
      -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) ≤
        rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) := by
    intro v hv
    have ht : ∀ k, 0 < Q k v / ((min p q : ℕ) : ℝ) := by
      intro k
      have h1 := hQle k v hv
      have ha : 0 < dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (hdk v hv k) _
      have ha0 : 0 < dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (hdk v0 hv0 k) _
      by_contra hneg
      push_neg at hneg
      have h2 : dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q k v / ((min p q : ℕ) : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha0.le hneg
      linarith
    have hlog : ∀ k, Real.log (dk v k) ≤
        Real.log (dk v0 k) + ((min p q : ℕ) : ℝ) * Real.log (Q k v / ((min p q : ℕ) : ℝ)) := by
      intro k
      have h1 := hQle k v hv
      have ha : 0 < dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (hdk v hv k) _
      have h2 := Real.log_le_log ha h1
      rw [Real.log_mul (Real.rpow_pos_of_pos (hdk v0 hv0 k) _).ne' (ht k).ne',
        Real.log_rpow (hdk v hv k), Real.log_rpow (hdk v0 hv0 k)] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 hmR.le
      have hmm : ((min p q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hm0
      rw [mul_add, ← mul_assoc, ← mul_assoc, hmm] at h3
      simpa only [one_mul] using h3
    have hQpos : ∀ k, 0 < Q k v := fun k => (div_pos_iff_of_pos_right hmR).mp (ht k)
    have hSpos : 0 < ∑ k, Q k v := Finset.sum_pos (fun k _ => hQpos k) Finset.univ_nonempty
    refine ⟨hSpos, ?_⟩
    have hJ : ∑ k, (f : ℝ)⁻¹ • Real.log (Q k v / ((min p q : ℕ) : ℝ)) ≤
        Real.log (∑ k, (f : ℝ)⁻¹ • (Q k v / ((min p q : ℕ) : ℝ))) :=
      (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (fun _ _ => inv_nonneg.mpr hfR.le)
        (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            exact mul_inv_cancel₀ hf0)
        (fun k _ => ht k)
    have hS : ∑ k, (f : ℝ)⁻¹ • (Q k v / ((min p q : ℕ) : ℝ)) =
        (∑ k, Q k v) / ((f * min p q : ℕ) : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_eq_mul, hC_eq]
      field_simp
    have hL : ∑ k, (f : ℝ)⁻¹ • Real.log (Q k v / ((min p q : ℕ) : ℝ)) =
        (f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) := by
      simp only [smul_eq_mul, Finset.mul_sum]
    rw [hS, hL, Real.log_div hSpos.ne' hCpos.ne'] at hJ
    have hsum : ∑ k, Real.log (dk v k) ≤ ∑ k, Real.log (dk v0 k) +
        ((min p q : ℕ) : ℝ) * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun k _ => hlog k
    have hmX : ((min p q : ℕ) : ℝ) * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) =
        ((f * min p q : ℕ) : ℝ) * ((f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ))) := by
      rw [hC_eq]
      field_simp
    have hCJ : ((f * min p q : ℕ) : ℝ) * ((f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ))) ≤
        ((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) -
          ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ) := by
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left hJ hCpos.le
    have hrv : rh v = -∑ k, Real.log (dk v k) := rfl
    have hrv0 : rh v0 = -∑ k, Real.log (dk v0 k) := rfl
    rw [hrv, hrv0]
    linarith
  have hle : ∀ᶠ v in 𝓝 v0, -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) ≤
      rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) := by
    filter_upwards [(isOpen_Dset f p q).mem_nhds hv0] with v hv using (hkey v hv).2
  have h2c : ∀ {g : V (nD f p q) → ℝ}, ContDiff ℝ ∞ g → ContDiffAt ℝ 2 g v0 := fun hg => by
    simpa using (contDiff_infty.mp hg 2).contDiffAt
  have hrhc : ContDiffAt ℝ 2 (fun v : V (nD f p q) =>
      rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ))) v0 := by
    have h1 : ContDiffAt ℝ 2 (fun v : V (nD f p q) => -∑ k, Real.log (dk v k)) v0 := by
      refine ContDiffAt.neg (ContDiffAt.sum fun k _ => ?_)
      exact (h2c (dkV_contDiff k)).log (hdk v0 hv0 k).ne'
    exact h1.sub contDiffAt_const
  have hΨc : ContDiffAt ℝ 2 (fun v : V (nD f p q) => ∑ k, Q k v) v0 :=
    ContDiffAt.sum fun k _ => h2c (hQc k)
  have hLev : (leviV (nD f p q) (fun y => ((∑ k, Q k y : ℝ) : ℂ)) v0 ξ).re ≤ 0 := by
    rw [leviV_ofReal_sum (fun k => h2c (hQc k)) ξ,
      Complex.re_sum]
    exact Finset.sum_nonpos fun k _ => hQL k ξ
  have hSv0 : ∑ k, Q k v0 = ((f * min p q : ℕ) : ℝ) := by
    simp only [hQ0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hC_eq]
  have heq : rh v0 - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) =
      -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v0) := by
    rw [hSv0]
    ring
  have hmain := RgA.grad_le_of_minorant
    (fun v : V (nD f p q) =>
      rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)))
    (fun v : V (nD f p q) => ∑ k, Q k v) v0 ((f * min p q : ℕ) : ℝ) hCpos
    (hkey v0 hv0).1 hrhc hΨc ξ hLev hle heq
  simp only [wd_ofReal_sub_const (fun w : V (nD f p q) => rh w), leviV_ofReal_sub_const (fun w : V (nD f p q) => rh w)]
    at hmain
  exact hmain

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

theorem RhGradStatement_holds : RhGradStatement := by
  intro f p q v hv ξ
  by_cases h : 0 < f ∧ 0 < min p q
  · exact rhGrad_main h.1 h.2 v hv ξ
  · have hn : nD f p q = 0 := by
      simp only [nD]
      rcases Nat.eq_zero_or_pos f with hf | hf
      · simp [hf]
      · have hm : ¬ 0 < min p q := fun hm => h ⟨hf, hm⟩
        rcases Nat.min_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hm) with hp | hq
        · simp [hp]
        · simp [hq]
    haveI : IsEmpty (Fin (nD f p q)) := by rw [hn]; infer_instance
    simp [leviV]

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

def Φ (z : V (nd X)) : V (nd X) := D.zOf (cpt X (rmul x1' b1) z)

def β (z : V (nd X)) : Frame X.Ψ r := D.bOf (cpt X (rmul x1' b1) z)

theorem cell_zero (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) :
    cpt X (rmul x1' b1) 0 ∈ ExtFPf.cell D := by
  have h0 : cpt X (rmul x1' b1) 0 = rmul x1' b1 := by
    funext τ
    show (mat (rmul x1' b1) τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = rmul x1' b1 τ
    rw [IW.nmat_zero, Matrix.mul_one]
    rfl
  have hx0 : cpt X x1' 0 = x1' := by
    funext τ
    show (mat x1' τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x1' τ
    rw [IW.nmat_zero, Matrix.mul_one]
    rfl
  have hdom : x1' ∈ X.dom := IW.orth_mem_dom X x1' ho'
  have hO : (0 : V (nd X)) ∈ OmF X x1' := by
    show cpt X x1' 0 ∈ X.dom
    rw [hx0]
    exact hdom
  have hu := (D.uniq 0 hO b1 hb1).1
  rw [hx0] at hu
  rw [h0]
  exact ⟨OntoS.dom_rmul X hdom hb1, hu⟩

theorem exists_ball (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∀ z ∈ Metric.ball (0 : V (nd X)) ρ1, cpt X (rmul x1' b1) z ∈ ExtFPf.cell D := by
  have hopen : IsOpen {z : V (nd X) | cpt X (rmul x1' b1) z ∈ ExtFPf.cell D} := by
    have h1 := ExF.isOpen_OmF (X := X) (rmul x1' b1)
    have h2 : IsOpen {z : V (nd X) | D.Δ (cpt X (rmul x1' b1) z) ≠ 0} :=
      isOpen_ne_fun (D.hΔ.continuous.comp (MI.continuous_cpt (X := X) _)) continuous_const
    exact h1.inter h2
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 (cell_zero X b1 D ho' hb1)
  exact ⟨ρ, hρ, fun z hz => hball hz⟩

theorem split {z : V (nd X)} (hz : cpt X (rmul x1' b1) z ∈ ExtFPf.cell D) :
    Φ X b1 D z ∈ OmF X x1' ∧ β X b1 D z ∈ Bor X.Ψ r ∧
      cpt X (rmul x1' b1) z = rmul (cpt X x1' (Φ X b1 D z)) (β X b1 D z) :=
  D.split _ hz.1 hz.2

private theorem eq_of_unipotent_lower_mul_eq_upper {n : ℕ} (A C B1 B2 N1 N2 : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A.det)
    (hB1 : IsUnit B1.det) (hB2 : IsUnit B2.det) (hB1t : B1.BlockTriangular id) (hB2t : B2.BlockTriangular id)
    (hN1t : N1.BlockTriangular OrderDual.toDual) (hN2t : N2.BlockTriangular OrderDual.toDual)
    (hd1 : ∀ a, N1 a a = 1) (hd2 : ∀ a, N2 a a = 1) (h1 : A * N1 = C * B1) (h2 : A * N2 = C * B2) :
    N1 = N2 := by
  have hN2u : IsUnit N2.det := by
    rw [Matrix.det_of_lowerTriangular N2 hN2t]
    simp [hd2]
  have h3 : N1 * B1⁻¹ = N2 * B2⁻¹ := by
    have e : A * (N1 * B1⁻¹) = A * (N2 * B2⁻¹) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB1,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB2]
    have e' := congrArg (fun M => A⁻¹ * M) e
    rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hA] at e'
  have hk : N2⁻¹ * N1 = B2⁻¹ * B1 := by
    have e3 : N1 = N1 * B1⁻¹ * B1 := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB1, Matrix.mul_one]
    rw [e3, h3, Matrix.mul_assoc N2, ← Matrix.mul_assoc N2⁻¹, Matrix.nonsing_inv_mul _ hN2u, Matrix.one_mul]
  have hPlow : (N2⁻¹ * N1).BlockTriangular OrderDual.toDual := by
    haveI := Matrix.invertibleOfIsUnitDet N2 hN2u
    exact (Matrix.blockTriangular_inv_of_blockTriangular hN2t).mul hN1t
  have hPup : (N2⁻¹ * N1).BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet B2 hB2
    rw [hk]
    exact (Matrix.blockTriangular_inv_of_blockTriangular hB2t).mul hB1t
  have hoff : ∀ a c, a ≠ c → (N2⁻¹ * N1) a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact hPlow (show OrderDual.toDual c < OrderDual.toDual a from h)
    · exact hPup h
  have hN1 : N1 = N2 * (N2⁻¹ * N1) := (Matrix.mul_nonsing_inv_cancel_left N2 N1 hN2u).symm
  have hsum : ∀ a c, (N2 * (N2⁻¹ * N1)) a c = N2 a c * (N2⁻¹ * N1) c c := by
    intro a c
    rw [Matrix.mul_apply, Finset.sum_eq_single c (fun k _ hk => by rw [hoff k c hk, mul_zero]) (by simp)]
  have hPd : ∀ c, (N2⁻¹ * N1) c c = 1 := by
    intro c
    have e := congrFun (congrFun hN1 c) c
    rw [hsum, hd1, hd2, one_mul] at e
    exact e.symm
  ext a c
  have e := congrFun (congrFun hN1 a) c
  rw [hsum, hPd, mul_one] at e
  exact e

theorem Φ_injOn (hx1 : rmul x1' b1 ∈ X.dom) :
    Set.InjOn (Φ X b1 D) {z | cpt X (rmul x1' b1) z ∈ ExtFPf.cell D} := by
  intro z1 hz1 z2 hz2 hΦ
  obtain ⟨-, hB1, e1⟩ := split X b1 D hz1
  obtain ⟨-, hB2, e2⟩ := split X b1 D hz2
  rw [hΦ] at e1
  have hlow : ∀ (z : V (nd X)) (τ : X.Ψ), (mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
    intro z τ a c hac
    have hac' : a < c := hac
    simp [mat, nmat, not_lt.2 hac'.le, hac'.ne]
  have hdiag : ∀ (z : V (nd X)) (τ : X.Ψ) (a : Fin r), mat (nmat X z) τ a a = 1 := by
    intro z τ a
    simp [mat, nmat]
  have hup : ∀ b ∈ Bor X.Ψ r, ∀ τ : X.Ψ, (mat b τ).BlockTriangular id := by
    intro b hb τ a c hac
    exact (hb τ).2 a c hac
  have hN : ∀ τ, mat (nmat X z1) τ = mat (nmat X z2) τ := by
    intro τ
    exact eq_of_unipotent_lower_mul_eq_upper (mat (rmul x1' b1) τ) (mat (cpt X x1' (Φ X b1 D z2)) τ) (mat (β X b1 D z1) τ)
      (mat (β X b1 D z2) τ) _ _ (isUnit_iff_ne_zero.2 (hx1 τ).1) (isUnit_iff_ne_zero.2 (hB1 τ).1)
      (isUnit_iff_ne_zero.2 (hB2 τ).1) (hup _ hB1 τ) (hup _ hB2 τ) (hlow z1 τ) (hlow z2 τ)
      (hdiag z1 τ) (hdiag z2 τ) (congrFun e1 τ) (congrFun e2 τ)
  ext i
  obtain ⟨⟨τ, ⟨⟨a, c⟩, hac⟩⟩, rfl⟩ : ∃ e : Ent X, Fintype.equivFin (Ent X) e = i :=
    ⟨(Fintype.equivFin (Ent X)).symm i, (Fintype.equivFin (Ent X)).apply_symm_apply i⟩
  have e := congrFun (congrFun (hN τ) a) c
  simpa [mat, nmat, hac] using e

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
end
