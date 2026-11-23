module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle114
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle012
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle100
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle101
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle102
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

open scoped ContDiff

namespace GlobalTheory.SepReal

theorem expS_mem_UJset {m : ℕ} {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.MainNotions.S.UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_right_inv hJJ
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩, rfl⟩
  have hXh : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by rw [h1, neg_mul]
  show (NormedSpace.exp (t • X))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (t • X) = Formalism.REAL.Jm ε
  have hc : (t • X)ᴴ = Formalism.REAL.Jm ε * (-(t • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXh, hJinv]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ hJu, hJinv]
  have hcomm : Commute (-(t • X)) (t • X) := (Commute.refl _).neg_left
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-(t • X)) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp (t • X)
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-(t • X)) * NormedSpace.exp (t • X)) := by
        rw [mul_assoc (Formalism.REAL.Jm ε * _) (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, mul_one, mul_assoc]
    _ = Formalism.REAL.Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem orbit_sub_le {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π) {X : Mat m}
    (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) {v : H} (hv : SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v) :
    ‖π (NormedSpace.exp X) v - v‖ ≤ ‖dR π X v‖ := by
  set f : ℝ → H := fun s => π (NormedSpace.exp (s • X)) v with hf
  have hcd : ContDiff ℝ ∞ f := by
    have h1 := hv 1 (fun _ => X) (fun _ => hX)
    have h2 : ContDiff ℝ ∞ (fun s : ℝ => (fun _ : Fin 1 => s)) := contDiff_pi.2 fun _ => contDiff_id
    have h3 := h1.comp h2
    convert h3 using 1
    funext s
    simp [f, List.ofFn_succ]
  have hdiff : Differentiable ℝ f := hcd.differentiable (by simp)
  have hder : ∀ t : ℝ, HasDerivAt f (π (NormedSpace.exp (t • X)) (dR π X v)) t := by
    intro t
    set Lt := π (NormedSpace.exp (t • X)) with hLt
    have h0 : HasDerivAt f (dR π X v) 0 := (hdiff 0).hasDerivAt
    have h1 : HasDerivAt (fun u : ℝ => (Lt.restrictScalars ℝ) (f u)) ((Lt.restrictScalars ℝ) (dR π X v)) (t - t) := by
      rw [sub_self]; exact (Lt.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h0
    have h2 := h1.comp_sub_const t t
    have hfun : f = fun s : ℝ => (Lt.restrictScalars ℝ) (f (s - t)) := by
      funext s
      have he : NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X) := by
        rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
        congr 2; ring
      simp only [f, he, hπ.1.2 _ (expS_mem_UJset hX t) _ (expS_mem_UJset hX (s - t))]
      rfl
    rw [hfun]
    exact h2
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f)
    (f' := fun t => π (NormedSpace.exp (t • X)) (dR π X v)) (C := ‖dR π X v‖)
    (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => le_of_eq (hπ.2.1 _ (expS_mem_UJset hX t) _))
  simpa [f, hπ.1.1] using hb

end GlobalTheory.SepReal

namespace GlobalTheory.SepReal

theorem exists_lowUnit {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Mat m → (H →L[ℂ] H)} (hds : IsDS ε lam π) : ∃ v, IsLowUnit ε lam π v := by
  obtain ⟨S, hS⟩ := hds.2.2.2.2.2.1
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  refine ⟨((‖v‖ : ℂ))⁻¹ • v, ?_, ?_⟩
  · have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    simp [norm_smul, this]
  · exact (le_sSup hS : S ≤ lowKSub ε lam π) (S.smul_mem _ hvS)

theorem one_le_eightMB {m : ℕ} {lam : Fin m → ℝ} {B : ℝ} (hm : 3 ≤ m) (hlam : IsHCParam lam)
    (hB : ∀ a, |lam a| ≤ B) : 1 ≤ 8 * (m : ℝ) * B := by
  have i0 : 0 < m := by omega
  have i1 : 1 < m := by omega
  have hlt : lam ⟨1, i1⟩ < lam ⟨0, i0⟩ := hlam.1 (show (⟨0, i0⟩ : Fin m) < ⟨1, i1⟩ from by simp [Fin.lt_def])
  obtain ⟨k0, hk0⟩ := hlam.2 ⟨0, i0⟩
  obtain ⟨k1, hk1⟩ := hlam.2 ⟨1, i1⟩
  have hk : (k1 : ℝ) < k0 := by linarith
  have hk' : k1 < k0 := by exact_mod_cast hk
  have hk'' : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast hk'
  have h0 := hB ⟨0, i0⟩
  have h1 := hB ⟨1, i1⟩
  rw [abs_le] at h0 h1
  have hB2 : 1 / 2 ≤ B := by linarith
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem degUpper_of (hlog : LogNear) (hlie : LieBound) (_hvol : VolBall) : DegUpper := by
  unfold DegUpper ForDS
  intro m ε lam B hm hlam hgap hB H _ _ π hds d hd
  obtain ⟨v₀, hv₀⟩ := exists_lowUnit hds
  obtain ⟨hsm, hbd⟩ := hlie m ε lam B hm hlam hgap hB H π hds v₀ hv₀
  have hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π := hds.2.2.1
  have hB1 := one_le_eightMB hm hlam hB
  set c : ℝ := (8 * (m : ℝ) * B) ^ 2 with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hcpos : 0 < c := by linarith
  set δ : ℝ := 1 / (4 * c) with hδ
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ]; apply one_div_le_one_div_of_le (by norm_num); linarith
  have hv1 : ‖v₀‖ = 1 := hv₀.1

  have key : ∀ g ∈ nbh ε δ, (1 / 4 : ℝ) ≤ ‖coefOn π v₀ v₀ g‖ ^ 2 := by
    intro g hg
    have hgU : umat g ∈ Formalism.MainNotions.S.UJset ε := g.2
    obtain ⟨X, hX, hXn, hXe⟩ := hlog m ε δ hδ4 (umat g) hgU hg
    have h1 := hbd [X] (by simpa using hX) (by simp)
    simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h1
    have h2 : ‖dR π X v₀‖ ≤ 1 / 2 := by
      calc ‖dR π X v₀‖ ≤ c * hsn X := h1
        _ ≤ c * (2 * δ) := by gcongr
        _ = 1 / 2 := by rw [hδ]; field_simp; ring
    have h3 : ‖π (umat g) v₀ - v₀‖ ≤ 1 / 2 := by
      rw [← hXe]; exact (orbit_sub_le hπ hX hsm).trans h2
    have h4 : coefOn π v₀ v₀ g = 1 + ⟪v₀, π (umat g) v₀ - v₀⟫_ℂ := by
      simp only [coefOn, inner_sub_right, inner_self_eq_norm_sq_to_K, hv1]
      push_cast; ring
    have h5 : ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ 1 / 2 := by
      calc ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ ‖v₀‖ * ‖π (umat g) v₀ - v₀‖ := norm_inner_le_norm _ _
        _ ≤ 1 / 2 := by rw [hv1, one_mul]; exact h3
    have h6 : 1 / 2 ≤ ‖coefOn π v₀ v₀ g‖ := by
      rw [h4]
      have := norm_sub_norm_le (1 : ℂ) (-⟪v₀, π (umat g) v₀ - v₀⟫_ℂ)
      rw [sub_neg_eq_add, norm_neg, norm_one] at this
      linarith
    nlinarith

  obtain ⟨hdpos, hI⟩ := hd
  obtain ⟨hint, hval⟩ := hI v₀ v₀ v₀ v₀
  have hpt : ∀ g : UJ ε, coefOn π v₀ v₀ g * star (coefOn π v₀ v₀ g) = ((‖coefOn π v₀ v₀ g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint' : Integrable (fun g => ‖coefOn π v₀ v₀ g‖ ^ 2) (muG ε) := by
    have := hint.re
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [hpt, RCLike.re_to_complex, Complex.ofReal_re]
  have hval' : ∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε = 1 / d := by
    have h := hval
    simp only [hpt, inner_self_eq_norm_sq_to_K, hv1] at h
    rw [integral_complex_ofReal] at h
    have h' : ((∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    exact_mod_cast h'
  have hlint : ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ) ≤ ENNReal.ofReal (1 / d) := by
    calc ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ)
        ≤ ENNReal.ofReal (1 / 4) * muG ε {g | ENNReal.ofReal (1 / 4) ≤ ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2)} := by
          gcongr
          intro g hg
          exact ENNReal.ofReal_le_ofReal (key g hg)
      _ ≤ ∫⁻ g, ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2) ∂muG ε :=
          mul_meas_ge_le_lintegral₀ hint'.aestronglyMeasurable.aemeasurable.ennreal_ofReal _
      _ = ENNReal.ofReal (1 / d) := by
          rw [← hval', ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun g => by positivity)]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by positivity)] at ht
  have : (muG ε (nbh ε δ)).toReal ≤ 4 * (1 / d) := by linarith
  rwa [mul_one_div] at this

end GlobalTheory.SepReal
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

namespace GlobalTheory.SepReal.RealAsm

variable {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isUnit_Jm' (ε : Fin m → Bool) : IsUnit (Jm ε) := by
  refine IsUnit.of_mul_eq_one (Jm ε) ?_
  simp only [Jm, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem umat_mem (ε : Fin m → Bool) (g : UJ ε) : umat g ∈ UJset ε := g.2

theorem one_mem (ε : Fin m → Bool) : (1 : Mat m) ∈ UJset ε := (1 : UJ ε).2

theorem continuous_umat (ε : Fin m → Bool) : Continuous (fun g : UJ ε => umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem smV_translate {ε : Fin m → Bool} {lam : Fin m → ℝ} {π : Mat m → (H →L[ℂ] H)} (hπ : IsDS ε lam π) {g : Mat m}
    (hg : g ∈ UJset ε) {v : H} (hv : SmV (lieOf (Jm ε)) π v) : SmV (lieOf (Jm ε)) π (π g v) :=
  GlobalTheory.SmLinSub.rep_mem (isUnit_Jm' ε) hπ.2.2.1 hv hg

theorem smV_const_smul {L : Set (Mat m)} {π : Mat m → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : SmV L π v) : SmV L π (a • v) :=
  fun k Xs hX => by simpa only [map_smul] using (hv k Xs hX).const_smul a

theorem integrable_low_coef (hD : DecPow) (hI : PowInt) {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (B : ℝ) (hn : 3 ≤ n)
    (hl : IsHCParam lam) (hg : GapAtLeast ε lam (1000 * (n : ℝ) ^ 3)) (hB : ∀ a, |lam a| ≤ B)
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w) :
    Integrable (fun h : UJ ε => ⟪w, σ (umat h) w⟫_ℂ) (muG ε) := by
  have hdec := hD n ε lam B hn hl hg hB H σ hσ w hw
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hA : 4 * (n : ℝ) ^ 2 + 1 ≤ 40 * (n : ℝ) ^ 2 := by nlinarith
  have hpow := (hI n ε (40 * (n : ℝ) ^ 2) (by omega) hA).1
  refine (hpow.const_mul (Real.exp (100 * (n : ℝ) ^ 3))).mono' ?_ (Filter.Eventually.of_forall fun h => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact continuous_const.inner ((hσ.2.2.1.2.2 w).comp_continuous (continuous_umat ε) (umat_mem ε))
  · exact hdec _ (umat_mem ε h)

theorem big_mul (a b : ℝ) (n : ℕ) (B : ℝ) : big a n B * big b n B = big (a + b) n B := by
  unfold big
  rw [← Real.exp_add]
  ring_nf

theorem big_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) {B : ℝ} (hB : 1 ≤ B) : big a n B ≤ big b n B := by
  unfold big
  apply Real.exp_le_exp.2
  have h1 : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith)
  have h2 : 0 ≤ ((n : ℝ) + 1) ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_right hab h2
  exact mul_le_mul_of_nonneg_right this h1

theorem big_pos (a : ℝ) (n : ℕ) (B : ℝ) : 0 < big a n B := Real.exp_pos _

theorem one_le_B {n : ℕ} {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
    {mu : Fin n → ℝ} {B : ℝ} (hP : Par e ε lam ε' mu B) : 1 ≤ B := by
  have hn := hP.three_le
  have h := hP.wide ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h0 := abs_le.1 (hP.bound.1 ⟨0, by omega⟩)
  have h1 := abs_le.1 (hP.bound.1 ⟨1, by omega⟩)
  linarith [h0.1, h0.2, h1.1, h1.2]

theorem gap_mono {k : ℕ} {ε : Fin k → Bool} {lam : Fin k → ℝ} {a b : ℝ} (hab : a ≤ b) (h : GapAtLeast ε lam b) :
    GapAtLeast ε lam a := fun x y hxy => hab.trans (h x y hxy)

end GlobalTheory.SepReal.RealAsm

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.RealAsm

end GlobalTheory.SepReal

end
end

section

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal.VolBallPf

theorem double_count {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E) (hφ : Continuous φ) (W : Set G) (R r : ℝ)
    (hR : 0 ≤ R) (hr : 0 < r) (hW : ∀ g h, ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ 2 * r → h⁻¹ * g ∈ W) :
    μ {g | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
  first
  | exact @_root_.GlobalTheory.SeparatedSetCardBound.main
  | exact _root_.GlobalTheory.SeparatedSetCardBound.main
  | (apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SeparatedSetCardBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SeparatedSetCardBound.main ..)

def toEuc {m : ℕ} (A : Mat m) : EuclideanSpace ℂ (Fin m × Fin m) := WithLp.toLp 2 fun p => A p.1 p.2

theorem norm_vec {m : ℕ} (A : Mat m) : ‖toEuc A‖ = hsn A := by
  simp [toEuc, hsn, EuclideanSpace.norm_eq, Fintype.sum_prod_type]

theorem toEuc_sub {m : ℕ} (A B : Mat m) : toEuc A - toEuc B = toEuc (A - B) := by
  ext p; simp [toEuc]

theorem continuous_vec {m : ℕ} : Continuous (toEuc : Mat m → _) := by
  unfold toEuc
  fun_prop

theorem hsn_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hsn (umat g⁻¹) = hsn (umat g) := by
  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h1 : umat g * umat g⁻¹ = 1 := determinant_character_mul_inv g
  have h2 : umat g⁻¹ = Jm ε * (umat g)ᴴ * Jm ε := by
    calc umat g⁻¹ = Jm ε * Jm ε * umat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
      _ = Jm ε * ((umat g)ᴴ * Jm ε * umat g) * umat g⁻¹ := by rw [hg]
      _ = Jm ε * (umat g)ᴴ * Jm ε * (umat g * umat g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [h2]
  unfold hsn
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem hsn_mul {m : ℕ} (A B : Mat m) : hsn (A * B) ≤ hsn A * hsn B := sqrt_frobenius_mul_le A B

theorem hsn_add {m : ℕ} (A B : Mat m) : hsn (A + B) ≤ hsn A + hsn B := sqrt_frobenius_add_le A B

end GlobalTheory.SepReal.VolBallPf

namespace GlobalTheory.SepReal

open VolBallPf

theorem volBall : VolBall := by
  intro m ε δ R hδ hR
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix m ε).1.continuous
  refine ⟨?_, ?_, ?_⟩
  · have hU : IsOpen {g : UJ ε | ‖toEuc (umat g - 1)‖ < δ} :=
      isOpen_lt (continuous_vec.comp (hu.sub continuous_const)).norm continuous_const
    refine lt_of_lt_of_le (hU.measure_pos (muG ε) ⟨1, ?_⟩) (measure_mono fun g hg => ?_)
    · simpa [norm_vec, hsn, umat] using hδ
    · have : ‖toEuc (umat g - 1)‖ < δ := hg
      rw [norm_vec] at this
      exact this.le
  · refine lt_of_le_of_lt (measure_mono fun g hg => ?_) (ball_finite_measure_holds m ε ((δ + hsn (1 : Mat m)) ^ 2))
    have h1 : hsn (umat g - 1) ≤ δ := hg
    have h2 := hsn_add (umat g - 1) 1
    rw [sub_add_cancel] at h2
    have h3 : hsn (umat g) ≤ δ + hsn (1 : Mat m) := by linarith
    exact (Real.sqrt_le_iff.1 h3).2
  · have key := double_count (muG ε) (fun g : UJ ε => toEuc (umat g)) (continuous_vec.comp hu) (nbh ε δ) R (δ / (2 * R)) hR.le
      (by positivity) (fun g h hh hgh => by
        rw [norm_vec] at hh
        rw [toEuc_sub, norm_vec] at hgh
        show hsn (umat (h⁻¹ * g) - 1) ≤ δ
        have h1 : umat h⁻¹ * umat h = 1 := by
          have := determinant_character_mul_inv h⁻¹
          rw [inv_inv] at this
          exact this
        have h2 : umat (h⁻¹ * g) - 1 = umat h⁻¹ * (umat g - umat h) := by
          rw [Matrix.mul_sub, h1]; rfl
        rw [h2]
        refine (hsn_mul _ _).trans ?_
        rw [hsn_inv]
        calc hsn (umat h) * hsn (umat g - umat h) ≤ R * (2 * (δ / (2 * R))) :=
              mul_le_mul hh hgh (Real.sqrt_nonneg _) hR.le
          _ = δ := by field_simp)
    have hfr : Module.finrank ℝ (EuclideanSpace ℂ (Fin m × Fin m)) = 2 * m ^ 2 := by
      rw [finrank_real_of_complex, finrank_euclideanSpace]; simp [sq]
    have hq : (R + δ / (2 * R)) / (δ / (2 * R)) = 1 + 2 * R ^ 2 / δ := by field_simp; ring
    simp only [norm_vec, hfr, hq] at key
    exact key

end GlobalTheory.SepReal

end
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.SepReal

theorem _root_.GlobalTheory.T.exists_indefiniteUnitary_boost_hilbertSchmidt : ∀ (m : ℕ) (ε : Fin m → Bool) (a b : Fin m → ℂ), (∀ i, ε i = false → a i = 0) → (∀ i, ε i = true → b i = 0) → ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 → ∃ A ∈ UJset ε, (∀ i, ∑ j, A i j * a j = (Real.sqrt (∑ j, ‖a j‖ ^ 2) : ℂ) * (a i + b i)) ∧ hsn A ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖a i + b i‖ ^ 2 := by
  first | exact @GlobalTheory.Boost.boost_exists | exact GlobalTheory.Boost.boost_exists | (intros; apply GlobalTheory.Boost.boost_exists <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv : ∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool), (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun i => ε' i = false).card → ∃ e : Option (Fin n) ≃ Fin (n + 1), GlobalTheory.SepReal.Signs e ε ε' := by
  first | exact @GlobalTheory.SepReal.exists_signs_equiv | exact GlobalTheory.SepReal.exists_signs_equiv | (intros; apply GlobalTheory.SepReal.exists_signs_equiv <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.det_adSqEigenvectorMatrix_ne_zero : ∀ (p q : ℕ), (Matrix.of fun (cd ab : PIx p q) => eigP ab.1 cd.1).det ≠ 0 := by
  first | exact @GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero | exact GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero | (intros; apply GlobalTheory.PolarU.det_eigenvectorMatrix_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.sinhcAdjointApplyMatrix_upperRightBlockElementP : ∀ (p q : ℕ) (B C : Fin p → Fin q → ℂ), sAd (pY B) (pY C) = pY (sP (pY B) C) := by
  first | exact @GlobalTheory.PolarU.SinhcPres.sAd_pY | exact GlobalTheory.PolarU.SinhcPres.sAd_pY | (intros; apply GlobalTheory.PolarU.SinhcPres.sAd_pY <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.adMat_sq_mulVec_adSqEigenvectorMatrixUnitP : ∀ (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q), (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  first | exact @GlobalTheory.PolarU.adMat_sq_mulVec_eigP | exact GlobalTheory.PolarU.adMat_sq_mulVec_eigP | (intros; apply GlobalTheory.PolarU.adMat_sq_mulVec_eigP <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_homeomorphic_action_of_cover_on_p : ∀ (p q : ℕ) (T : GrpData p q) (L : Mat p q → (Fin p → Fin q → ℂ)), ContinuousOn L {g | IsUnit g} → (∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B) → (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ g : T.G, ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧ ∀ B, ∃ κ ∈ T.Kset, T.expt (pY B) * g = κ * T.expt (pY (ψ B)) := by
  first | exact @GlobalTheory.PolarU.exists_action_on_p | exact GlobalTheory.PolarU.exists_action_on_p | (intros; apply GlobalTheory.PolarU.exists_action_on_p <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_unitaryCover_lift_blockDiagonal : ∀ (p q : ℕ) (T : GrpData p q), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  first | exact @GlobalTheory.PolarU.exists_lift_blocks | exact GlobalTheory.PolarU.exists_lift_blocks | (intros; apply GlobalTheory.PolarU.exists_lift_blocks <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.prod_sinhc_rootValueOfMatrixUnitP : ∀ (p q : ℕ) (h : ℕ → ℝ), ∏ ab : PIx p q, shc (rootP h ab.1) = (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  first | exact @GlobalTheory.PolarU.RootProd.prod_shc_rootP | exact GlobalTheory.PolarU.RootProd.prod_shc_rootP | (intros; apply GlobalTheory.PolarU.RootProd.prod_shc_rootP <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.det_sinhcAdjointUpperRightCoord_eq_polJ : ∀ (p q : ℕ) (Y : Mat p q), (∀ C : Fin p → Fin q → ℂ, sAd Y (pY C) = pY (sP Y C)) → LinearMap.det (sP Y) = polJ Y := by
  first | exact @GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | exact GlobalTheory.PolarU.det_sinhc_eq_polarJacobian | (intros; apply GlobalTheory.PolarU.det_sinhc_eq_polarJacobian <;> assumption)
end
