module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle123
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle114
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle127
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle119
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDer
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompLie
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RJR

theorem le_inf (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : ((n : ℕ∞)) ≤ ⊤)

theorem zero_bilin {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {u : D → E} {v : D → F} {s : Set D} {x : D} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s) (n : ℕ) (hvz : ∀ j ≤ n, iteratedFDeriv ℝ j v x = 0) :
    ∀ j ≤ n, iteratedFDeriv ℝ j (fun y => B (u y) (v y)) x = 0 := by
  intro j hj
  have hus : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have key := B.norm_iteratedFDerivWithin_le_of_bilinear hu hv hus hx (n := j) (RJR.le_inf j)
  rw [← norm_le_zero_iff, ← iteratedFDerivWithin_of_isOpen j hs hx]
  refine key.trans (le_of_eq ?_)
  rw [Finset.sum_eq_zero, mul_zero]
  intro i _
  rw [iteratedFDerivWithin_of_isOpen (j - i) hs hx, hvz (j - i) (le_trans (Nat.sub_le _ _) hj),
    norm_zero, mul_zero]

theorem zero_comp {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ψ : ℂ → G} {ζ : D → ℂ} {s : Set D} {t : Set ℂ} {x : D} (hs : IsOpen s) (ht : IsOpen t) (hx : x ∈ s)
    (hmap : Set.MapsTo ζ s t) (hψ : ContDiffOn ℝ ∞ ψ t) (hζ : ContDiffOn ℝ ∞ ζ s) (n : ℕ)
    (hz : ∀ j ≤ n, iteratedFDeriv ℝ j ψ (ζ x) = 0) :
    ∀ j ≤ n, iteratedFDeriv ℝ j (ψ ∘ ζ) x = 0 := by
  intro j hj
  have hus : UniqueDiffOn ℝ s := hs.uniqueDiffOn
  have hut : UniqueDiffOn ℝ t := ht.uniqueDiffOn
  set Dd : ℝ := ∑ i ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ i ζ s x‖ + 1 with hDd
  have hD1 : 1 ≤ Dd := by
    have : 0 ≤ ∑ i ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ i ζ s x‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have key := norm_iteratedFDerivWithin_comp_le (n := j) hψ hζ (RJR.le_inf j) hut hus hmap hx
    (C := 0) (D := Dd)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i ht (hmap hx), hz i (le_trans hi hj), norm_zero])
    (fun i hi1 hij => by
      have h1 : ‖iteratedFDerivWithin ℝ i ζ s x‖ ≤ Dd := by
        have : ‖iteratedFDerivWithin ℝ i ζ s x‖ ≤ ∑ i ∈ Finset.range (j + 1), ‖iteratedFDerivWithin ℝ i ζ s x‖ :=
          Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i ζ s x‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hij))
        linarith
      refine h1.trans ?_
      first
        | exact le_self_pow₀ hD1 (by omega)
        | exact le_self_pow hD1 (by omega))
  rw [← norm_le_zero_iff, ← iteratedFDerivWithin_of_isOpen j hs hx]
  simpa using key

def Bc (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] :
    (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℂ).comp
    (ContinuousLinearMap.compL ℂ Wq Wp Wp)).restrictScalars ℝ

def Bd (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] :
    (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((ContinuousLinearMap.restrictScalarsL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) ℝ ℂ).comp
    (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip).restrictScalars ℝ

end RJR

open RJR in
theorem jet_radial_holds : GTCLRJetRad := by
  intro Wp Wq _ _ _ _ _ _ P Bs _ _ Φ q hq N hN
  have hq1 : q.1 ∈ OmX P.r := hq.1
  have hB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, Bs.sec, Bs.π_rep, Bs.π'_rep, Bs.π_cont,
      Bs.π'_cont⟩
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB Φ Φ.2
  have hΦe := (Φ.2).2.2
  let tt : Set ℂ := {ζ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ}
  have ht : IsOpen tt := isOpen_lt continuous_const Complex.continuous_normSq
  let ψ : ℂ → (Wq →L[ℂ] Wp) := fun ζ =>
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)
  have hmapQ : Set.MapsTo (fun ζ : ℂ => (q.1, ζ)) tt (NF.QR P.k P.r Bs.z Bs.z') :=
    fun ζ hζ => ⟨hq1, hζ⟩
  have hpair : ContDiff ℝ ∞ (fun ζ : ℂ => (q.1, ζ)) := by
    first
      | exact contDiff_const.prodMk contDiff_id
      | exact contDiff_const.prod contDiff_id
  have hψs : ContDiffOn ℝ ∞ ψ tt := hmem.1.comp hpair.contDiffOn hmapQ
  have hψval : ∀ ζ ∈ tt, ψ ζ = (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec ζ) := by
    intro ζ hζ
    simp only [ψ, NF.radR]
    rw [Set.indicator_of_mem (hmapQ hζ)]
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec hq
  obtain ⟨V, hV, hg₀V, a, b, ha, hb, hfac⟩ :=
    Formalism.FourierDecayAlt.P.local_smooth_section P.k P.r Bs.z Bs.z' Bs.μsec Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos
      Bs.T'_pos Bs.sec _ hdom.2.1 hdom.2.2
  have hf0 := hfac _ hg₀V hdom.2.1 hdom.2.2
  obtain ⟨Vp, hVp, haVp, Pp, hPp, hPpe⟩ :=
    Formalism.FourierDecayAlt.P.representation_smooth Wp P.k P.r Bs.z Bs.π Bs.z_mem Bs.T_pos Bs.π_rep Bs.π_cont _ hf0.1
  obtain ⟨Vq, hVq, hbVq, Pq, hPq, hPqe⟩ :=
    Formalism.FourierDecayAlt.P.representation_smooth Wq P.k P.r Bs.z' Bs.π' Bs.z'_mem Bs.T'_pos Bs.π'_rep Bs.π'_cont _
      hf0.2.1
  let zL := Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r)
  have hzL : ContDiff ℝ ∞ zL := Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff P.k P.r Bs.z Bs.z' (Fin.last P.r)
  have hz0 : zL (NF.muZ P.k P.r Bs.μsec q.2) = q.2 :=
    Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hq.2
  let W : Set (Q.Mx P.k P.r) := (V ∩ a ⁻¹' Vp) ∩ (V ∩ b ⁻¹' Vq) ∩ zL ⁻¹' tt
  have hW : IsOpen W :=
    ((ha.continuousOn.isOpen_inter_preimage hV hVp).inter
      (hb.continuousOn.isOpen_inter_preimage hV hVq)).inter (ht.preimage hzL.continuous)
  have hg₀W : NF.muZ P.k P.r Bs.μsec q.2 ∈ W := by
    refine ⟨⟨⟨hg₀V, haVp⟩, ⟨hg₀V, hbVq⟩⟩, ?_⟩
    show zL (NF.muZ P.k P.r Bs.μsec q.2) ∈ tt
    rw [hz0]
    exact hq.2
  have hu : ContDiffOn ℝ ∞ (fun g => Pp (a g)) W :=
    hPp.comp (ha.mono fun g hg => hg.1.1.1) fun g hg => hg.1.1.2
  have hu' : ContDiffOn ℝ ∞ (fun g => Pq (b g)) W :=
    hPq.comp (hb.mono fun g hg => hg.1.2.1) fun g hg => hg.1.2.2
  have hv' : ContDiffOn ℝ ∞ (ψ ∘ zL) W := hψs.comp hzL.contDiffOn fun g hg => hg.2
  have hv : ContDiffOn ℝ ∞ (fun g => Bd Wp Wq (Pq (b g)) ((ψ ∘ zL) g)) W :=
    ((Bd Wp Wq).contDiff.comp_contDiffOn hu').clm_apply hv'
  have hF : ContDiffOn ℝ ∞ (fun g => Bc Wp Wq (Pp (a g)) (Bd Wp Wq (Pq (b g)) ((ψ ∘ zL) g))) W :=
    ((Bc Wp Wq).contDiff.comp_contDiffOn hu).clm_apply hv
  have hz1 : ∀ j ≤ N, iteratedFDeriv ℝ j ψ (zL (NF.muZ P.k P.r Bs.μsec q.2)) = 0 := by
    rw [hz0]
    exact hN
  have hv'0 := zero_comp hW ht hg₀W (fun g hg => hg.2) hψs hzL.contDiffOn N hz1
  have hv0 := zero_bilin (Bd Wp Wq) hW hg₀W hu' hv' N hv'0
  have hF0 := zero_bilin (Bc Wp Wq) hW hg₀W hu hv N hv0
  refine ⟨W, _, hW, hg₀W, hF, ?_, hF0⟩
  intro g hg hGl
  have hgt : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq (zL g) := hg.2
  have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' g := by
    show 0 < Complex.normSq (zL g) - Tz P.k P.r Bs.z * Tz P.k P.r Bs.z'
    exact sub_pos.2 hgt
  obtain ⟨haU, hbU, hfg⟩ := hfac g hg.1.1.1 hGl hGG
  have hdom' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem Bs.sec (q := (q.1, zL g)) ⟨hq1, hgt⟩
  have he := hΦe (q.1, NF.muZ P.k P.r Bs.μsec (zL g)) hdom' (a g) haU (b g) hbU
  have hl : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 g =
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (a g * NF.muZ P.k P.r Bs.μsec (zL g) * b g) := by
    conv_lhs => rw [hfg]
  rw [hl, he]
  simp only
  rw [hPpe (a g) hg.1.1.2 haU, hPqe (b g) hg.1.2.2 hbU, ← hψval (zL g) hgt]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB

section id

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rel_id (A : Pr V) : Rel (LinearMap.id : V →ₗ[ℂ] V) A A :=
  ⟨by rw [LinearMap.comp_id, LinearMap.id_comp], by rw [LinearMap.comp_id, LinearMap.id_comp]⟩

theorem mrel_id (M : Matrix (Fin 2) (Fin 2) (Pr V)) : MRel (LinearMap.id : V →ₗ[ℂ] V) M M := fun _ _ => rel_id _

end id

theorem pairAt_smul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) (a : ℝ≥0)
    (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    P5.pairAt (a • μ) Φ Ψ c = ((a : ℝ) : ℂ) * P5.pairAt μ Φ Ψ c := by
  unfold P5.pairAt
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem glue_zero' {r : ℕ} (c : Fin r → ℂ) (c'' : Fin (r - 0) → ℂ) :
    P5.glue (⟨0, by omega⟩ : Fin (r + 1)) c (PTie.shiftCf ⟨0, by omega⟩ c'') = c'' := by
  funext l
  simp [P5.glue, PTie.shiftCf]

theorem glue_step {r : ℕ} (j : ℕ) (hj : j + 1 ≤ r) (c : Fin r → ℂ) (c'' : Fin (r - (j + 1)) → ℂ)
    (hn : r - j = 1 + (r - (j + 1))) :
    P5.glue (⟨j, by omega⟩ : Fin (r + 1)) c
        (PTie.shiftCf ⟨j, by omega⟩ (fun l => consC (c ⟨j, by omega⟩) c'' (Fin.cast hn l))) =
      P5.glue (⟨j + 1, by omega⟩ : Fin (r + 1)) c (PTie.shiftCf ⟨j + 1, by omega⟩ c'') := by
  funext l
  unfold P5.glue PTie.shiftCf consC
  by_cases h1 : j + 1 ≤ l.val
  · rw [dite_eq_left (show j ≤ l.val by omega), dite_eq_left h1]
    simp only [Fin.val_cast]
    rw [dite_eq_right (by omega)]
    congr 1
  · by_cases h2 : j ≤ l.val
    · rw [dite_eq_left h2, dite_eq_right h1]
      simp only [Fin.val_cast]
      rw [dite_eq_left (by omega)]
      congr 1
      ext
      simp only
      omega
    · rw [dite_eq_right h2, dite_eq_right h1]

theorem castM_iota0 {k r : ℕ} (h : 0 + (r - 0) = r) (g : B.Mat k (r - 0)) :
    D.castM h (ιLev k 0 (r - 0) g) = g := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev, finCongr_symm, finCongr_apply,
    Fin.val_cast]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem step_cast {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k n ρ : ℕ} (hn : n = 1 + ρ)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn.symm (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn.symm (liftVec k 1 ρ zs'))
    (hzs : inWb k ρ zs) (hzs' : inWb k ρ zs')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn.symm (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn.symm (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (st : Fr.Start (Pr (RadSp k n z z' π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ) (sts : Fr.Start (Pr (RadSp k ρ zs zs' πs πs')))
    (s : ℂ) (μ : Measure (Mt k n)) (μs : Measure (Mt k ρ))
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y)
    (hμ : B.IsHaarOn (Glev k n (Fin.last n)) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k n z z' (Fin.last n) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k n z) (Tz k n z') ζ) * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ zs zs' (Fin.last ρ) (Matrix.of x)) ∂μs =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ) * ψ ζ)
    (t : ℂ) (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g))) ∧
      (∀ l : Fin ρ, Rel T (L.p ⟨l.val + 1, by omega⟩) (Ls.p l) ∧ Rel T (L.c ⟨l.val + 1, by omega⟩) (Ls.c l) ∧
        Rel T (L.ci ⟨l.val + 1, by omega⟩) (Ls.ci l)) ∧
      (∀ (m : ℕ) (hm : m ≤ ρ) (Y : ℂ),
        MRel T (P5.QQi L st ⟨m + 1, by omega⟩ Y) (P5.QQi Ls sts ⟨m, by omega⟩ Y)) ∧
      ∀ Φ Ψ c, P5.pairAt μs (T Φ) (T Ψ) c = P5.pairAt μ Φ Ψ (fun l => consC t c (Fin.cast hn l)) := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k 1 ρ y) := funext fun y => by rw [hπ, P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k 1 ρ y) := funext fun y => by rw [hπ', P.JCTx5.castM_rfl]
  rw [tz_iota, tz_iota] at hlaw
  have hmap : μs.map (B2.levM k ρ) = μ := map_levM_eq hμ hμs _ (zWeight_fin _ _) hlaw hlaws
  refine ⟨trL ht zs zs' π π', fun Φ c g => ?_, fun l => site_ops ht hL hLs l,
    fun m hm Y => qqi_rel_n ht hzs hzs' hL hLs hst hsts m hm Y, fun Φ Ψ c => ?_⟩
  · rw [P.JCTx5.castM_rfl]; rfl
  · exact pairAt_tr ht hmap Φ Ψ c

end Formalism.FourierDecayAlt.P.PTieL

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k r : ℕ}

lemma block_embedding_mul_embed (g X : Mb k) : embWb k r g * e0 k r X = e0 k r (g * X) := by
  rw [emb_eq]
  unfold e0
  rw [Matrix.add_mul]
  have h1 : Em k r * g * (Em k r)ᵀ * (Em k r * X * (Em k r)ᵀ) = Em k r * (g * X) * (Em k r)ᵀ := by
    calc Em k r * g * (Em k r)ᵀ * (Em k r * X * (Em k r)ᵀ) = Em k r * g * ((Em k r)ᵀ * Em k r) * X * (Em k r)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Em k r * (g * X) * (Em k r)ᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have h2 : (1 - Em k r * (Em k r)ᵀ) * (Em k r * X * (Em k r)ᵀ) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Q_Em, Matrix.zero_mul, Matrix.zero_mul]
  rw [h1, h2, add_zero]

lemma embed_mul_block_embedding (g X : Mb k) : e0 k r X * embWb k r g = e0 k r (X * g) := by
  rw [emb_eq]
  unfold e0
  rw [Matrix.mul_add]
  have h1 : Em k r * X * (Em k r)ᵀ * (Em k r * g * (Em k r)ᵀ) = Em k r * (X * g) * (Em k r)ᵀ := by
    calc Em k r * X * (Em k r)ᵀ * (Em k r * g * (Em k r)ᵀ) = Em k r * X * ((Em k r)ᵀ * Em k r) * g * (Em k r)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Em k r * (X * g) * (Em k r)ᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have h2 : Em k r * X * (Em k r)ᵀ * (1 - Em k r * (Em k r)ᵀ) = 0 := by
    rw [Matrix.mul_assoc, EmT_Q, Matrix.mul_zero]
  rw [h1, h2, add_zero]

lemma single_wI (a b : Fin (k + 1)) : Matrix.single (wI k r a) (wI k r b) (1 : ℂ) = e0 k r (Su k a b) := by
  have hE : ∀ c : Fin (k + 1), Em k r *ᵥ Pi.single c 1 = Pi.single (wI k r c) 1 := by
    intro c
    funext i
    rw [Matrix.mulVec_single_one]
    show Em k r i c = _
    rw [Em, Pi.single_apply]
  unfold e0 Su
  rw [Matrix.single_eq_single_vecMulVec_single, Matrix.single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hE, hE]

def LS (k : ℕ) (p : Fin (k + 1) × Fin (k + 1)) : Mb k :=
  if p.1 = Fin.last k ∨ p.2 = Fin.last k then 0 else Su k p.1 p.2

lemma inL_LS (p : Fin (k + 1) × Fin (k + 1)) : InL k (LS k p) := by
  unfold LS
  split_ifs with h
  · exact inL_zero
  · exact inL_Su (not_or.1 h).1 (not_or.1 h).2

lemma sum_LS {n : ℕ} (e : Fin (k + 1) × Fin (k + 1) ≃ Fin n) (C : Mb k) (hC : InL k C) :
    ∑ t : Fin n, C (e.symm t).1 (e.symm t).2 • LS k (e.symm t) = C := by
  rw [e.symm.sum_comp (fun p => C p.1 p.2 • LS k p), Fintype.sum_prod_type]
  conv_rhs => rw [Matrix.matrix_eq_sum_single C]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold LS
  split_ifs with h
  · have : C i j = 0 := by
      rcases h with h | h
      · have h' : i = Fin.last k := h
        rw [h']; exact (hC j).2
      · have h' : j = Fin.last k := h
        rw [h']; exact (hC i).1
    rw [this, zero_smul, Matrix.single_zero]
  · unfold Su
    rw [Matrix.smul_single, smul_eq_mul, mul_one]

lemma embed_conj_finset_sum {n : ℕ} (g h : Mb k) (c : Fin n → ℂ) (X : Fin n → Mb k) :
    ∑ t, c t • e0 k r (g * X t * h) = e0 k r (g * (∑ t, c t • X t) * h) := by
  unfold e0
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma ringSpec_normalisedCharacter_eq (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) :
    mu0 k r z z' ζ = embWb k r (gA k (wbPart k r z) (Tz k r z) * nu k (wZ (Tz k r z) (Tz k r z') ζ) (sZ (Tz k r z) (Tz k r z') ζ) *
      gB k (wbPart k r z') (Tz k r z')) := rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2 Dc

noncomputable section

theorem radial_decomposition_holds : Decomp := by
  intro k r z z' hk hz hz' hT hT' a b
  have h0 : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  obtain ⟨hA, -⟩ := gA_spec k hT (herm_self k r z hz)
  obtain ⟨hB, -⟩ := gB_spec k hT' (herm_self k r z' hz')
  set T := Tz k r z with hTd
  set T' := Tz k r z' with hTd'
  set ga := gA k (wbPart k r z) T with hga
  set gb := gB k (wbPart k r z') T' with hgb
  have iA : ga⁻¹ * ga = 1 := unit_inv_mul hA
  have iB : gb⁻¹ * gb = 1 := unit_inv_mul hB
  obtain ⟨C₁, C₂, β₁, β₂, c1, c2, c3, c4, c5⟩ := dec_all (T := T) (T' := T') h0 hT hT' (gb * Su k a b * gb⁻¹)
  let e := Fintype.equivFin (Fin (k + 1) × Fin (k + 1))
  refine ⟨_, _, fun t => e0 k r (gb⁻¹ * LS k (e.symm t) * gb), fun t ζ => C₁ ζ (e.symm t).1 (e.symm t).2,
    fun t => e0 k r (ga * LS k (e.symm t) * ga⁻¹), fun t ζ => C₂ ζ (e.symm t).1 (e.symm t).2, β₁, β₂,
    fun t => gwc_right k r z' hz' hT' _ (inL_LS _), fun t => gwc_left k r z hz hT _ (inL_LS _),
    fun t => c1.1 _ _, fun t => c2.1 _ _, c3, c4, fun ζ hζ => ?_⟩
  have hν := nuI_mul (k := k) h0 hT hT' hζ
  set ν := nu k (wZ T T' ζ) (sZ T T' ζ) with hνd
  set νi := nuI k T T' ζ with hνi
  have hmu : mu0 k r z z' ζ = embWb k r (ga * ν * gb) := ringSpec_normalisedCharacter_eq z z' ζ
  have hinv : (mu0 k r z z' ζ)⁻¹ = embWb k r (gb⁻¹ * νi * ga⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [hmu, ← emb_mul]
    have : gb⁻¹ * νi * ga⁻¹ * (ga * ν * gb) = gb⁻¹ * (νi * ((ga⁻¹ * ga) * ν)) * gb := by simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul, hν, Matrix.mul_one, iB, emb_one]
  have s1 : ∑ t, C₁ ζ (e.symm t).1 (e.symm t).2 • e0 k r (gb⁻¹ * LS k (e.symm t) * gb) = e0 k r (gb⁻¹ * C₁ ζ * gb) := by
    rw [embed_conj_finset_sum, sum_LS e _ (c1.2 ζ)]
  have s2 : ∑ t, C₂ ζ (e.symm t).1 (e.symm t).2 • e0 k r (ga * LS k (e.symm t) * ga⁻¹) = e0 k r (ga * C₂ ζ * ga⁻¹) := by
    rw [embed_conj_finset_sum, sum_LS e _ (c2.2 ζ)]
  have s3 : (mu0 k r z z' ζ)⁻¹ * e0 k r (ga * C₂ ζ * ga⁻¹) * mu0 k r z z' ζ = e0 k r (gb⁻¹ * (νi * C₂ ζ * ν) * gb) := by
    rw [hinv, hmu, block_embedding_mul_embed, embed_mul_block_embedding]
    congr 1
    have : gb⁻¹ * νi * ga⁻¹ * (ga * C₂ ζ * ga⁻¹) * (ga * ν * gb) =
        gb⁻¹ * (νi * ((ga⁻¹ * ga) * C₂ ζ * (ga⁻¹ * ga)) * ν) * gb := by simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul, Matrix.mul_one]
  have s4 : etaZ k r z z' ζ = e0 k r (gb⁻¹ * H1 k T T' ζ * gb) := by
    unfold etaZ
    rw [dmu_eq k r z z' hT hT' ζ hζ, hinv, block_embedding_mul_embed]
    congr 1
    unfold H1
    have : ∀ D : Mb k, gb⁻¹ * νi * ga⁻¹ * (ga * D * gb) = gb⁻¹ * (νi * ((ga⁻¹ * ga) * D)) * gb := by
      intro D; simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul]
  have s5 : etaZb k r z z' ζ = e0 k r (gb⁻¹ * H2 k T T' ζ * gb) := by
    unfold etaZb
    rw [dmub_eq k r z z' hT hT' ζ hζ, hinv, block_embedding_mul_embed]
    congr 1
    unfold H2
    have : ∀ D : Mb k, gb⁻¹ * νi * ga⁻¹ * (ga * D * gb) = gb⁻¹ * (νi * ((ga⁻¹ * ga) * D)) * gb := by
      intro D; simp only [Matrix.mul_assoc]
    rw [this, iA, Matrix.one_mul]
  have s6 : Su k a b = gb⁻¹ * (gb * Su k a b * gb⁻¹) * gb := by
    have : gb⁻¹ * (gb * Su k a b * gb⁻¹) * gb = (gb⁻¹ * gb) * Su k a b * (gb⁻¹ * gb) := by simp only [Matrix.mul_assoc]
    rw [this, iB, Matrix.one_mul, Matrix.mul_one]
  rw [s1, s2, s3, s4, s5, single_wI, s6, c5 ζ hζ, ← embed_smul, ← embed_smul, ← embed_add, ← embed_add, ← embed_add]
  congr 1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end
