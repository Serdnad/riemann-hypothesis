module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle088
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle089
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bd_of_ubl {k r : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (z z' : Fin (2 * r + k + 1) → ℂ) (φ : B.Mat k r → F) (e γ : ℕ) (Bg : ℝ)
    (hBg : (e : ℝ) + γ ≤ Bg) (ε : ℝ)
    (h0 : ∃ C0 : ℝ, ∀ g ∈ geG k r z z' ε, ‖φ g‖ ≤ C0) (hU : ∀ n : ℕ, UBL φ (geG k r z z' ε) n e γ) (m : ℕ) :
    ∃ C : ℝ, ∀ u w : List (B.Mat k r),
      (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r z z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨C0, hC0⟩ := h0
    refine ⟨C0, fun u w _ _ hl g hg hgε => ?_⟩
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu hw
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    exact hC0 g ⟨hg, hgε⟩
  · obtain ⟨⟨C, hC0, hUB⟩, -⟩ := hU m
    refine ⟨C, fun u w hu hw hl g hg hgε => ?_⟩
    have hA : admitted m (wL u ++ wR w) := ⟨u, w, hu, hw, hl, rfl⟩
    have hb := hUB _ hA g ⟨hg, hgε⟩
    rw [dLR_eq]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have h1 : 1 ≤ B.gN g := gN_ge_one hg
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h1
    rw [len_LR]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hl' : ((u.length + w.length : ℕ) : ℝ) ≤ m := by exact_mod_cast hl
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
    push_cast at hl' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hl' hγ, mul_le_mul_of_nonneg_left hm1 he,
      mul_le_mul_of_nonneg_right hBg (by linarith : (0 : ℝ) ≤ m)]

theorem geometry_assembly_holds : GeomAssemble := by
  intro hS hEn hEi hAt hB0 hU
  refine ⟨6, by norm_num, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Bs := (T v).base with hBs
  have hk : 1 ≤ S.G.k := Bs.k_pos
  have hz : C2.StdZ S.G.k S.G.r Bs.z := ⟨Bs.z_mem, Bs.T_pos⟩
  have hz' : C2.StdZ S.G.k S.G.r Bs.z' := ⟨Bs.z'_mem, Bs.T'_pos⟩
  refine ⟨nuG Bs.z Bs.z', nuG' Bs.z Bs.z', ioG Bs.z Bs.z', ?_⟩
  obtain ⟨s1, s2, s3⟩ := hS _ _ _ _ hk hz hz'
  obtain ⟨C0, hC0⟩ := hB0 _ _ _ _ hk hz hz'
  have hr0 : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
  have hBg : ∀ e γ : ℕ, e ≤ 4 * (S.G.r + 1) → γ ≤ 2 * (S.G.r + 1) → (e : ℝ) + γ ≤ Cb * ((S.G.r : ℝ) + 1) := by
    intro e γ he hγ
    have he' : (e : ℝ) ≤ 4 * ((S.G.r : ℝ) + 1) := by exact_mod_cast he
    have hγ' : (γ : ℝ) ≤ 2 * ((S.G.r : ℝ) + 1) := by exact_mod_cast hγ
    nlinarith
  have hpos : ∀ ε : ℝ, 0 < ε → ∀ g ∈ geG S.G.k S.G.r Bs.z Bs.z' ε, g ∈ posG S.G.k S.G.r Bs.z Bs.z' :=
    fun ε hε g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2⟩
  refine ⟨s1, s2, s3, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp g hg
    obtain ⟨h1, h2⟩ := hEn _ _ _ _ hk hz hz' _ hp.1 _ hp.2.1 _ hp.2.2.1 _ hp.2.2.2 g hg
    exact ⟨h1, h2, hEi _ _ _ _ hk hz hz' _ hp.1 _ hp.2.1 _ hp.2.2.1 _ hp.2.2.2 g hg⟩
  · intro ε hε m
    obtain ⟨⟨e, γ, he, hγ, hu⟩, -, -⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).1⟩ hu m
  · intro ε hε m
    obtain ⟨-, ⟨e, γ, he, hγ, hu⟩, -⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).2.1⟩ hu m
  · intro ε hε m
    obtain ⟨-, -, ⟨e, γ, he, hγ, hu⟩⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).2.2⟩ hu m
  · intro q hq
    have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r Bs.z * Tz S.G.k S.G.r Bs.z' := by
      show (D.parOf S v).T * (D.parOf S v).T' = _
      rw [hPl.2.2.2.1, hPl.2.2.2.2.1]
    have hq2 : Tz S.G.k S.G.r Bs.z * Tz S.G.k S.G.r Bs.z' < Complex.normSq q.2 := hTT ▸ hq.2
    exact hAt _ _ _ _ Bs.μsec hk hz hz' Bs.sec q.1 q.2 hq.1 hq2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ContDiff Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def phiS (c t : ℝ) : ℝ := sc c t * (Real.sqrt t)⁻¹

def PhiS (c : ℝ) (w : ℂ) : ℂ := ((phiS c w.re : ℝ) : ℂ)

lemma phiS_cd {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (phiS c) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : c / 8 < t
  · have h1 : ContDiff ℝ ∞ (sc c) := by
      unfold sc
      exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    have hpos : 0 < t := by linarith
    have h2 : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.sqrt y)⁻¹) t :=
      (Real.contDiffAt_sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
    exact h1.contDiffAt.mul h2
  · have hev : phiS c =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (show t < c / 4 by linarith)] with y hy
      have hy' : y < c / 4 := hy
      have h0 : (y - c / 4) / (c / 4) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      simp [phiS, sc, Real.smoothTransition.zero_of_nonpos h0]
    exact contDiffAt_const.congr_of_eventuallyEq hev

lemma phiS_ev {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : c / 2 < t) :
    phiS c =ᶠ[𝓝 t] fun y => y ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds ht] with y hy
  have hy' : c / 2 < y := hy
  have hc4 : 0 < c / 4 := by positivity
  have h1 : 1 ≤ (y - c / 4) / (c / 4) := by
    rw [le_div_iff₀ hc4]
    linarith
  have hy0 : 0 ≤ y := by linarith
  simp only [phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]
  rw [Real.rpow_neg hy0, Real.sqrt_eq_rpow]

lemma phiS_bound {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∃ A : ℝ, ∀ t : ℝ, c ≤ t → ‖iteratedFDeriv ℝ j (phiS c) t‖ ≤ A := by
  refine ⟨|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * c ^ (-(1 / 2 : ℝ) - j), fun t ht => ?_⟩
  have hct : c / 2 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hev := phiS_ev hc hct
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_iterate]
  simp only [Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hq : -(1 / 2 : ℝ) - (j : ℝ) ≤ 0 := by linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc ht hq) (abs_nonneg _)

lemma PhiS_eq : ∀ c : ℝ, PhiS c = (Complex.ofRealCLM) ∘ (phiS c ∘ Complex.reCLM) := by
  intro c
  funext w
  simp [PhiS]

lemma PhiS_cd {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (PhiS c) := by
  rw [PhiS_eq]
  exact Complex.ofRealCLM.contDiff.comp ((phiS_cd hc).comp Complex.reCLM.contDiff)

lemma PhiS_bound {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∃ B : ℝ, ∀ w ∈ {w : ℂ | c ≤ w.re}, ‖iteratedFDeriv ℝ j (PhiS c) w‖ ≤ B := by
  obtain ⟨A, hA⟩ := phiS_bound hc j
  refine ⟨‖Complex.ofRealCLM‖ * (A * ∏ _i : Fin j, ‖Complex.reCLM‖), fun w hw => ?_⟩
  have hw' : c ≤ w.re := hw
  have hj : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rw [PhiS_eq]
  calc ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ (phiS c ∘ Complex.reCLM)) w‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (phiS c ∘ Complex.reCLM) w‖ :=
        Complex.ofRealCLM.norm_iteratedFDeriv_comp_left ((phiS_cd hc).comp Complex.reCLM.contDiff).contDiffAt hj
    _ ≤ ‖Complex.ofRealCLM‖ * (A * ∏ _i : Fin j, ‖Complex.reCLM‖) := by
        gcongr
        rw [Complex.reCLM.iteratedFDeriv_comp_right (phiS_cd hc) w hj]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        gcongr
        exact hA _ (by simpa using hw')

theorem unipotent_inverse_sqrt_bound : UBLInvSqrt := by
  intro k r d P hP S hSG c hc hSc n
  obtain ⟨hPcd, -⟩ := poly_adm (n := n) hP
  obtain ⟨M, hM⟩ := poly_H hP n
  have hU : UBL (fun g => PhiS c (P g)) S n 0 d :=
    ubl_fdb P hPcd S hSG {w : ℂ | c ≤ w.re} hSc d n M hM (PhiS c) (PhiS_cd hc) (PhiS_bound hc)
  refine ubl_congr (V := P ⁻¹' {w : ℂ | c / 2 < w.re}) ?_ ?_ hSG ?_ hU
  · exact (isOpen_lt continuous_const Complex.continuous_re).preimage hPcd.continuous
  · intro g hg
    have h := hSc g hg
    show c / 2 < (P g).re
    linarith
  · intro g _ hg
    have hg' : c / 2 < (P g).re := hg
    have hc4 : 0 < c / 4 := by positivity
    have h1 : 1 ≤ ((P g).re - c / 4) / (c / 4) := by
      rw [le_div_iff₀ hc4]
      linarith
    show (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ) = PhiS c (P g)
    rw [PhiS, phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeibOps_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem nfLeibOps_hsInner_smul_left (c : ℂ) (A B' : Wq →L[ℂ] Wp) : B.hsInner (c • A) B' = c * B.hsInner A B' := by
  unfold B.hsInner
  rw [nfLeibOps_hsVec_smul, inner_smul_right]

theorem nfLeibOps_hsInner_smul_right (c : ℂ) (A B' : Wq →L[ℂ] Wp) :
    B.hsInner A (c • B') = conj c * B.hsInner A B' := by
  unfold B.hsInner
  rw [nfLeibOps_hsVec_smul, inner_smul_left]

def nfLeibOps_sc (Bs : B.RealPlaceData k r Wp Wq) (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) (g : B.Mat k r) : ℂ :=
  t.2.1 g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1


open Classical in
def nfLeibOps_mk (Bs : B.RealPlaceData k r Wp Wq) (T : B.DTerm k r Wp Wq)
    (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef g := nfLeibOps_sc Bs t g • T.coef g
  coefAdj g := conj (nfLeibOps_sc Bs t g) • T.coefAdj g
  word := if ∀ X ∈ t.2.2.2, B.inLie k r X then t.2.2.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id x A B' := by
    simp only [ContinuousLinearMap.smul_apply]
    rw [nfLeibOps_hsInner_smul_left, nfLeibOps_hsInner_smul_right, T.adj_id, Complex.conj_conj]

theorem nfLeibOps_ckOn_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {UU : Set (B.Mat k r)}
    {c : B.Mat k r → ℂ} {f : B.Mat k r → E} (hc : B.CkOn ⊤ UU c) (hf : B.CkOn ⊤ UU f) :
    B.CkOn ⊤ UU (fun g => c g • f g) := by
  unfold B.CkOn at hc hf ⊢
  intro g₀ hg₀
  obtain ⟨U₁, c', hU₁, hg₁, hc', ec⟩ := hc g₀ hg₀
  obtain ⟨U₂, f', hU₂, hg₂, hf', ef⟩ := hf g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => c' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right), ?_⟩
  intro g hg hgG
  show c g • f g = c' g • f' g
  rw [ec g hg.1 hgG, ef g hg.2 hgG]

theorem nfLeibOps_ckOn_conj {UU : Set (B.Mat k r)} {c : B.Mat k r → ℂ} (hc : B.CkOn ⊤ UU c) :
    B.CkOn ⊤ UU (fun g => conj (c g)) := by
  unfold B.CkOn at hc ⊢
  intro g₀ hg₀
  obtain ⟨U, c', hU, hg, hc', ec⟩ := hc g₀ hg₀
  refine ⟨U, fun g => conj (c' g), hU, hg, ?_, ?_⟩
  · refine (Complex.conjCLE.contDiff.comp_contDiffOn hc').congr (fun g _ => ?_)
    simp
  · intro g hgU hgG
    show conj (c g) = conj (c' g)
    rw [ec g hgU hgG]

theorem nfLeibOps_ckOn_sc (Bs : B.RealPlaceData k r Wp Wq) (t : ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) (D : ℕ)
    (hP : ListSumSplittings.PolyClass D t.2.1) : B.CkOn ⊤ (C6.domL Bs ∅) (nfLeibOps_sc Bs t) := by
  intro g₀ hg₀
  obtain ⟨U1, c1, hU1, hg1, hc1, he1⟩ := hP.1 g₀ hg₀.1
  have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z')
  have hO : IsOpen {g : B.Mat k r | 0 < Gf k r Bs.z Bs.z' g} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  refine ⟨U1 ∩ {g | 0 < Gf k r Bs.z Bs.z' g},
    fun g => c1 g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1, hU1.inter hO, ⟨hg1, hg₀.2.1⟩, ?_, ?_⟩
  · refine (hc1.mono Set.inter_subset_left).mul ?_
    refine ContDiffOn.pow ?_ _
    refine (hGc.contDiffOn.inv fun g hg => ?_).mono Set.inter_subset_right
    · exact_mod_cast (ne_of_gt hg)
  · intro g hg hgG
    simp only [nfLeibOps_sc, he1 g hg.1 hgG]

end ops

theorem nfLeibOps_sum_key {E : Type*} [AddCommGroup E] [Module ℂ E] {α : Type*} (Q : ℕ) (key : α → ℕ)
    (f : ℕ → ℂ) (a : α → E) : ∀ l : List α, (∀ t ∈ l, key t ≤ Q) →
    (l.map fun t => f (key t) • a t).sum =
      ∑ q : Fin (Q + 1), f q • ((l.filter fun t => key t = (q : ℕ)).map a).sum := by
  intro l hl
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun t' ht' => hl t' (by simp [ht']))]
    have hq : key t < Q + 1 := Nat.lt_succ_of_le (hl t (by simp))
    have hsplit : ∀ q : Fin (Q + 1), f q • (((t :: l).filter fun t' => key t' = (q : ℕ)).map a).sum =
        (if key t = (q : ℕ) then f q • a t else 0) +
          f q • ((l.filter fun t' => key t' = (q : ℕ)).map a).sum := by
      intro q
      by_cases h : key t = (q : ℕ)
      · simp [List.filter_cons, h, smul_add]
      · simp [List.filter_cons, h]
    rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single ⟨key t, hq⟩]
    · simp
    · intro b _ hb
      have hne : key t ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [hne]
    · simp

theorem nfLeibOps_of (hE : NFLeibExp) : NFLeibOps := by
  intro k r Wp Wq _ _ _ _ _ Bs Dop hsm
  classical
  let terms : B.DTerm k r Wp Wq → List (ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)) :=
    fun T => (hE k r Wp Wq Bs T.word T.word_lie).choose
  have hspec := fun T : B.DTerm k r Wp Wq => (hE k r Wp Wq Bs T.word T.word_lie).choose_spec
  set Q : ℕ := (Dop.map fun T => T.word.length).sum with hQ
  have hQle : ∀ T ∈ Dop, T.word.length ≤ Q := fun T hT =>
    List.le_sum_of_mem (List.mem_map.2 ⟨T, hT, rfl⟩)
  let LT : B.DTerm k r Wp Wq → Fin (Q + 1) → B.DiffOp k r Wp Wq :=
    fun T q => ((terms T).filter fun t => t.1 = (q : ℕ)).map (nfLeibOps_mk Bs T)
  refine ⟨Q, fun q => Dop.flatMap fun T => LT T q, ?_, ?_, ?_⟩
  ·
    intro q T' hT'
    obtain ⟨T, hT, hT'T⟩ := List.mem_flatMap.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT'T
    have htm : t ∈ terms T := (List.mem_filter.1 ht).1
    have hP := ((hspec T).1 t htm).2.1
    exact ⟨nfLeibOps_ckOn_smul (nfLeibOps_ckOn_sc Bs t _ hP) (hsm T hT).1,
      nfLeibOps_ckOn_smul (nfLeibOps_ckOn_conj (nfLeibOps_ckOn_sc Bs t _ hP)) (hsm T hT).2⟩
  ·
    intro q T' hT'
    obtain ⟨T, hT, hT'T⟩ := List.mem_flatMap.1 hT'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hT'T
    have htm : t ∈ terms T := (List.mem_filter.1 ht).1
    obtain ⟨-, hP, hsub⟩ := (hspec T).1 t htm
    refine ⟨T, hT, t.2.1, t.2.2.1, hP, ?_, fun g _ => rfl⟩
    have hlie : ∀ X ∈ t.2.2.2, B.inLie k r X := fun X hX => T.word_lie X (hsub.subset hX)
    simp only [nfLeibOps_mk]
    rw [if_pos hlie]
    exact hsub
  ·
    intro Ψ hΨ F hF x hx
    have hT1 : ∀ T ∈ Dop, T.coef x (B.Rw T.word (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x) =
        ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (LT T q) F x := by
      intro T hT
      rw [(hspec T).2 Ψ hΨ F hF x hx, map_list_sum, List.map_map]
      have e1 : ((terms T).map ((T.coef x) ∘ fun t => ((((Ψ t.1 (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) * t.2.1 x *
            ((Gf k r Bs.z Bs.z' x : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F x))) =
          (terms T).map fun t => (fun n : ℕ => ((Ψ n (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ)) t.1 •
            (fun t => nfLeibOps_sc Bs t x • T.coef x (B.Rw t.2.2.2 F x)) t := by
        refine List.map_congr_left fun t _ => ?_
        simp only [Function.comp_apply, map_smul, nfLeibOps_sc, smul_smul, mul_assoc]
      rw [e1]
      refine (nfLeibOps_sum_key Q (fun t => t.1) (fun n : ℕ => ((Ψ n (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ))
        (fun t => nfLeibOps_sc Bs t x • T.coef x (B.Rw t.2.2.2 F x)) (terms T)
        (fun t ht => ((hspec T).1 t ht).1.trans (hQle T hT))).trans ?_
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      unfold B.opApply
      rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
      have htm : t ∈ terms T := (List.mem_filter.1 ht).1
      have hlie : ∀ X ∈ t.2.2.2, B.inLie k r X := fun X hX => T.word_lie X (((hspec T).1 t htm).2.2.subset hX)
      simp only [Function.comp_apply, nfLeibOps_mk, if_pos hlie, ContinuousLinearMap.smul_apply]
    have hall : ∀ D' : B.DiffOp k r Wp Wq, (∀ T ∈ D', T ∈ Dop) →
        B.opApply D' (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
          ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (D'.flatMap fun T => LT T q) F x := by
      intro D'
      induction D' with
      | nil => intro _; simp [B.opApply]
      | cons T D' ih =>
        intro hsub
        have eA : ∀ (D'' : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
            B.opApply (T :: D'') G x = T.coef x (B.Rw T.word G x) + B.opApply D'' G x := by
          intro D'' G; simp [B.opApply]
        have eB : ∀ (l1 l2 : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp)),
            B.opApply (l1 ++ l2) G x = B.opApply l1 G x + B.opApply l2 G x := by
          intro l1 l2 G; simp [B.opApply]
        rw [eA, hT1 T (hsub T List.mem_cons_self), ih fun T' hT' => hsub T' (List.mem_cons_of_mem _ hT'),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [List.flatMap_cons, eB, smul_add]
    exact hall Dop fun T hT => hT

end

end Formalism.FourierDecayAlt.P.CutBP
end
