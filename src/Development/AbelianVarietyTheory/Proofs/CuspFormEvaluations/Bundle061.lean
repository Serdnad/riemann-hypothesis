module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle055
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle056
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle034
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

theorem _root_.GlobalTheory.T.indep_span_rank_transfer_largeField_complex : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (t : Idx D j N → ℂ), R.Generic t → ∀ (u : WeightFamilies.Wt D j) (ι : Type) [Fintype ι] (p : ι → MvPolynomial (Idx D j N) X.Forms), (∀ i, OfWt X u (p i)) → (LinearIndependent (Kp X la N) (fun i => toRp X la N (p i)) ↔ LinearIndependent ℂ (fun i => R.toFn t (p i))) ∧ (∀ q, OfWt X u q → (toRp X la N q ∈ Submodule.span (Kp X la N) (Set.range fun i => toRp X la N (p i)) ↔ R.toFn t q ∈ Submodule.span ℂ (Set.range fun i => R.toFn t (p i)))) ∧ Module.finrank (Kp X la N) (Submodule.span (Kp X la N) (Set.range fun i => toRp X la N (p i))) = Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => R.toFn t (p i))) := by
  first | exact @GlobalTheory.reading_transfer | exact GlobalTheory.reading_transfer | (intros; apply GlobalTheory.reading_transfer <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn.ScalSize

variable {D : D7} {j : ℕ}

theorem one_le_f (D : D7) : (1 : ℝ) ≤ D.R.f := by
  have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  exact_mod_cast this

theorem one_le_r (D : D7) : (1 : ℝ) ≤ D.R.r := by
  have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact_mod_cast this

theorem size_eq (w : WeightFamilies.Wt D j) :
    w.size = (WeightAlgebra.DF w : ℝ) + (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  push_cast
  ring

theorem size_ge (w : WeightFamilies.Wt D j) : (WeightAlgebra.DF w : ℝ) + (D.R.f : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 ≤ w.size := by
  rw [size_eq]
  have h1 : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h2 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

theorem n_le_size (w : WeightFamilies.Wt D j) : (w.n : ℝ) ≤ w.size := by
  have h := size_ge w
  have h1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le (one_le_f D) (one_le_r D)
  have h2 : (0 : ℝ) ≤ w.n := by positivity
  have h3 : (0 : ℝ) ≤ WeightAlgebra.DF w := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem size_comb (T : ℕ) (wL wF : WeightFamilies.Wt D j) :
    (wadd wF (wsmul T wL)).size + T = T * wL.size + wF.size := by
  unfold WeightFamilies.Wt.size
  simp only [wadd, wsmul]
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  ring

theorem log_zOwn_le (p : ℕ) (hp : 0 < p) (w : WeightFamilies.Wt D j) :
    Real.log (zOwnP D p w : ℝ) ≤ 2 * Real.log p * w.size := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h := size_ge w
  have h3 : (0 : ℝ) ≤ WeightAlgebra.DF w := by positivity
  unfold zOwnP
  push_cast
  rw [Real.log_pow]
  push_cast
  have : (WeightAlgebra.DF w : ℝ) + 2 * D.R.f * D.R.r * w.n ≤ 2 * w.size := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hl]

theorem lamStar_nonneg (w : WeightFamilies.Wt D j) : 0 ≤ lamStar D := by
  obtain ⟨-, -, h1, h2, -⟩ := GlobalTheory.RunIn.pPow_size D j w
  unfold lamStar
  linarith

noncomputable def comb (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) : 𝓞 B.KO :=
  (zOwnP D p G : 𝓞 B.KO) * sOf B hinj EX wL ^ T * sOf B hinj EX wF

theorem comb_eq (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (zOwnP D p G : 𝓞 B.KO) * nnW B hinj EX wL ^ T * nnW B hinj EX wF *
      (pPow D (T * c2 D wL + c2 D wF) (T * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
        (T * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) : 𝓞 B.KO) = comb B hinj EX p G wL wF T := by
  unfold comb sOf pPow
  push_cast
  ring

theorem comb_ne_zero (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) : comb B hinj EX p G wL wF T ≠ 0 := by
  unfold comb
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wL).1)) (GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wF).1
  exact Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')

theorem log_comb_le (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (comb B hinj EX p G wL wF T : B.KO)‖ ≤
      2 * Real.log p * G.size + lamStar D * (T * wL.size + wF.size) := by
  obtain ⟨hL0, hL⟩ := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wL
  obtain ⟨hF0, hF⟩ := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wF
  have hL1 := (hL σ).2.2.2
  have hF1 := (hF σ).2.2.2
  have nz : ∀ x : 𝓞 B.KO, x ≠ 0 → ‖σ (x : B.KO)‖ ≠ 0 := fun x hx => by
    rw [norm_ne_zero_iff, map_ne_zero]
    exact_mod_cast hx
  have hz : (zOwnP D p G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')
  have e : ‖σ (comb B hinj EX p G wL wF T : B.KO)‖ =
      (zOwnP D p G : ℝ) * ‖σ (sOf B hinj EX wL : B.KO)‖ ^ T * ‖σ (sOf B hinj EX wF : B.KO)‖ := by
    unfold comb
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, norm_mul, norm_pow,
      Complex.norm_natCast]
  rw [e, Real.log_mul (mul_ne_zero hz (pow_ne_zero _ (nz _ hL0))) (nz _ hF0),
    Real.log_mul hz (pow_ne_zero _ (nz _ hL0)), Real.log_pow]
  have h1 := log_zOwn_le p hp G
  have hT : (0 : ℝ) ≤ T := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hL1 hT]

theorem log_comb_le' (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (wL wF : WeightFamilies.Wt D j) (hn : 1 ≤ wL.n) (T : ℕ) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (comb B hinj EX p (wadd wF (wsmul T wL)) wL wF T : B.KO)‖ ≤
      2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul T wL)).size := by
  have h := log_comb_le B hinj EX p hp (wadd wF (wsmul T wL)) wL wF T σ
  rw [← size_comb] at h
  have h1 := n_le_size (wadd wF (wsmul T wL))
  have h2 : T ≤ (wadd wF (wsmul T wL)).n := by
    simp only [wadd, wsmul]
    nlinarith
  have h3 : (T : ℝ) ≤ (wadd wF (wsmul T wL)).size := le_trans (by exact_mod_cast h2) h1
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hΛ := lamStar_nonneg wL
  have hs := (wadd wF (wsmul T wL)).one_le_size
  nlinarith [mul_le_mul_of_nonneg_left h3 hΛ, mul_nonneg hl (le_trans zero_le_one hs)]

theorem wt_eq {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} (hF : IsF' ka wL wF T nP) (hL : wL.n = nW)
    (hn : ka.n = nP + T * nW) : ka = wadd wF (wsmul T wL) := by
  obtain ⟨h1, h2, h3⟩ := hF
  obtain ⟨a, b, _, _, n, _⟩ := ka
  have e1 : a = (wadd wF (wsmul T wL)).aP := funext fun τ => funext fun i => by
    have := h2 τ i
    simp only [wadd, wsmul] at this ⊢
    zify
    linarith
  have e2 : b = (wadd wF (wsmul T wL)).aM := funext fun τ => funext fun i => by
    have := h3 τ i
    simp only [wadd, wsmul] at this ⊢
    zify
    linarith
  have e3 : n = (wadd wF (wsmul T wL)).n := by
    simp only [wadd, wsmul] at hn ⊢
    rw [h1, hL, hn]
  subst e1 e2 e3
  rfl

end GlobalTheory.RunIn.ScalSize


open GlobalTheory.RunIn.ScalSize in
theorem GlobalTheory.RunIn.scalOfP_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ), 0 < p → 1 ≤ nW → wL.n = nW → IsF' ka wL wF Tn nP → ka.n = nP + Tn * nW → (scalOfP B hinj EX p ka wL wF Tn).sF ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).s0 ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).sK ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, (Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sW : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wL.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sF : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).s0 : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul (WeightFamilies.dimY D j) wL)).size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sK : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * ka.size) := by
  intro D B hinj EX j p ka wL wF Tn nP nW hp hW hL hF hn
  have eF : (scalOfP B hinj EX p ka wL wF Tn).sF = comb B hinj EX p wF wL wF 0 := by
    unfold comb sOf
    simp only [scalOfP, pow_zero, mul_one, mul_assoc]
  have e0 : (scalOfP B hinj EX p ka wL wF Tn).s0 =
      comb B hinj EX p (wadd wF (wsmul (WeightFamilies.dimY D j) wL)) wL wF (WeightFamilies.dimY D j) := comb_eq ..
  have eK : (scalOfP B hinj EX p ka wL wF Tn).sK = comb B hinj EX p ka wL wF Tn := comb_eq ..
  have hn1 : 1 ≤ wL.n := hL ▸ hW
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [eF, e0, eK, sW_eq_sOf]
  refine ⟨comb_ne_zero B hinj EX p hp _ _ _ _, comb_ne_zero B hinj EX p hp _ _ _ _,
    comb_ne_zero B hinj EX p hp _ _ _ _, fun σ => ⟨?_, ?_, log_comb_le' B hinj EX p hp wL wF hn1 _ σ, ?_⟩⟩
  · have h := ((GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wL).2 σ).2.2.2
    nlinarith [mul_nonneg hl (le_trans zero_le_one wL.one_le_size)]
  · have h := log_comb_le B hinj EX p hp wF wL wF 0 σ
    push_cast at h
    linarith
  · rw [wt_eq hF hL hn]
    exact log_comb_le' B hinj EX p hp wL wF hn1 _ σ
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem shortSum_toΓ_injective (S : Type) [CommRing S] : Function.Injective (toΓ S) := by
  intro a b h
  have hinv : ∀ x : S, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (toΓ S x) = x := by
    intro x
    unfold toΓ
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  rw [← hinv a, ← hinv b, h]

private theorem eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one {M : Type*} [CommMonoid M] (x : M) (N : ℕ) (hN : Odd N)
    (h2 : x ^ 2 = 1) (hN2 : x ^ (N ^ 2) = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hN.pow (n := 2)
  rw [hk, pow_succ, pow_mul, h2, one_pow, _root_.one_mul] at hN2
  exact hN2



theorem shortSum_indep_local : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (P : MvPolynomial (LtN Dw n) c.F) (T : Type) [CommRing T] [IsLocalRing T] [Algebra c.F T] (y : FrPt Xo c T) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ q, ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F1 q i b) (colOf m b) = ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b) := by
  intro hL E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hTr hLev P T _ _ _ y z1 tp1 F1 z2 tp2 F2 hz1 hg1 htp1 hF1 hz2 hg2 htp2 hF2 q
  obtain ⟨hNodd, hMN, hNL⟩ := hLev
  have hN0 : 0 < N := hNodd.pos
  have hLa : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hNL.trans inf_le_left
  have hsurj := (GlobalTheory.T.isotropic_enumeration_surjective_local_ring hL E H Dw l Xo T y.x n Λ N hU hN0 hLa z1 hz1 hg1).1
  have h58 := GlobalTheory.T.torsion_isotropic_commutator_pairing hL E H Dw l Xo T y.x n Λ N hU hN0 hLa
  have h56 := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  have h57 := (GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique hL E H Dw l Xo N hN0).2.1

  have hz2inj : Function.Injective z2 := by
    intro i i' h
    let g : ptO Xo (spMap (IsLocalRing.residue T) ≫ y.x) ⟶ ptO Xo y.x :=
      Over.homMk (spMap (IsLocalRing.residue T)) rfl
    exact hg2 (IsLocalRing.ResidueField T) (IsLocalRing.residue T) g rfl
      (congrArg (fun (w : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (b : Fin n) => g ≫ w b) h)

  obtain ⟨u, hu⟩ : ∃ u : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G), ∀ b, u b = (tp1 q b)⁻¹ * tp2 q b :=
    ⟨_, fun _ => rfl⟩
  have htp : ∀ b, tp2 q b = tp1 q b * u b := fun b => by
    rw [hu, mul_inv_cancel_left]
  have hlev : ∀ a : Dw.La, levPt Xo y.x a ^ N = 1 := by
    intro a
    obtain ⟨k, hk⟩ := hMN
    unfold levPt
    rw [← MonObj.comp_pow, hk, pow_mul, (GlobalTheory.moduli_univ_eta_killed hL E H Dw l Xo a).2.2, one_pow,
      MonObj.comp_one]
  have hu1 : ∀ b, u b ^ N = 1 := fun b => by
    rw [hu, mul_pow, inv_pow, (htp1 q b).1, (htp2 q b).1, inv_mul_cancel]
  have hsq : ∀ x : ptO Xo y.x ⟶ Xo.univ.t.G, x ^ N = 1 → x ^ (N ^ 2) = 1 := fun x hx => by
    rw [sq, pow_mul, hx, one_pow]
  have ht2 : ∀ b, tp1 q b ^ (N ^ 2) = 1 := fun b => by
    rw [sq, pow_mul, (htp1 q b).1, hlev]
  have hkill : ∀ b, ∃ j, KilledBy Xo (l.Mb ^ j) (tp1 q b) ∧ KilledBy Xo (l.Mb ^ j) (u b) := by
    intro b
    obtain ⟨j1, hj1⟩ := (htp1 q b).2
    obtain ⟨j2, hj2⟩ := (htp2 q b).2
    have mono : ∀ {i j : ℕ} (t : ptO Xo y.x ⟶ Xo.univ.t.G), i ≤ j →
        KilledBy Xo (l.Mb ^ i) t → KilledBy Xo (l.Mb ^ j) t :=
      fun t hij ht a ha => ht a (Ideal.pow_le_pow_right hij ha)
    refine ⟨max j1 j2, mono _ (le_max_left _ _) hj1, ?_⟩
    intro a ha
    have := Xo.univ.t.act.hom a
    have k1 := mono _ (le_max_left _ _) hj1 a ha
    have k2 := mono _ (le_max_right _ _) hj2 a ha
    have h1 : ((tp1 q b)⁻¹ ≫ Xo.univ.t.act.act a) * (tp1 q b ≫ Xo.univ.t.act.act a) = 1 := by
      rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
    rw [k1, _root_.mul_one] at h1
    rw [hu, MonObj.mul_comp, h1, k2, _root_.one_mul]
  have hInU : InZh Xo Λ N u := h56.2.2.2 hTr (ptO Xo y.x) u (fun b => by
    obtain ⟨j, -, hj⟩ := hkill b
    exact ⟨hu1 b, j, hj⟩)

  have hw : ∀ i, ∃ j, z1 j = fun b => u b * z2 i b := fun i =>
    hsurj _ (h56.2.1 _ u (z2 i) hInU (hz2 i))
  choose ρ hρ using hw
  have hρinj : Function.Injective ρ := by
    intro i i' h
    apply hz2inj
    funext b
    have hii := (hρ i).symm.trans ((congrArg z1 h).trans (hρ i'))
    exact mul_left_cancel (show u b * z2 i b = u b * z2 i' b from congrFun hii b)
  have hρbij : Function.Bijective ρ := Finite.injective_iff_bijective.mp hρinj

  have key : ∀ i, (∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) (colOf m b) := by
    intro i
    have he : ∀ b, ∃ e : Γ((ptO Xo y.x).left, ⊤)ˣ,
        WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (u b) (z2 i b) e := fun b =>
      (h57 (ptO Xo y.x) (u b) (z2 i b) (hsq _ (hu1 b)) ((hz2 i).1 b)).imp fun _ h => h.1
    choose e he using he
    have hpe : ∏ b, e b = 1 := h58.1 u (z2 i) e hInU (hz2 i) he
    have hr : ∀ b, ∃ r : T, (toΓ T r) ^ 2 = ((e b : Γ((ptO Xo y.x).left, ⊤))) ∧ r ^ (N ^ 2) = 1 ∧
        ∀ α, nab y ((N : ℤ) ^ 2) (F2 q i b) α = r * nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) α := by
      intro b
      obtain ⟨j, hj1, hj2⟩ := hkill b
      have hW1 := h58.2 (tp1 q b) (u b) j (ht2 b) (hsq _ (hu1 b)) hj1 hj2
      have hA : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp1 q b * u b) (F2 q i b) := by
        rw [← htp b]
        exact hF2 q i b
      have hB : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (u b * z2 i b) (tp1 q b) (F1 q (ρ i) b) := by
        have h1 := hF1 q (ρ i) b
        rw [hρ i] at h1
        exact h1
      obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.T.thetaGroup_shift_halfTorsion_root hL E H Dw l Xo T y.x N hNodd y.s (tp1 q b) (u b) (z2 i b)
        (e b) (ht2 b) (hsq _ (hu1 b)) ((hz2 i).1 b) hW1 (he b) _ _ hA hB
      exact ⟨r, hr1, hr2, GlobalTheory.T.connection_linear_in_section E H Dw l Xo c nab hnab T y N _ _ r hr3⟩
    choose r hr using hr
    have hprod : ∏ b, r b = 1 := by
      apply eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one _ N hNodd
      · apply shortSum_toΓ_injective T
        rw [map_one, map_pow, map_prod, ← Finset.prod_pow,
          Finset.prod_congr rfl (fun b _ => (hr b).1), ← Units.coe_prod, hpe, Units.val_one]
      · rw [← Finset.prod_pow]
        exact Finset.prod_eq_one (fun b _ => (hr b).2.1)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    rw [Finset.prod_congr rfl (fun b _ => (hr b).2.2 (colOf m b)), Finset.prod_mul_distrib, hprod, _root_.one_mul]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  exact (hρbij.sum_comp (fun j => ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
    ∏ b, nab y ((N : ℤ) ^ 2) (F1 q j b) (colOf m b))).symm

end GlobalTheory
end
