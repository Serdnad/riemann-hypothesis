module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle131
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hs_expand (A C : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec A) (B.hsVec C) =
      ∑ i, inner ℂ (A (stdOrthonormalBasis ℂ Wq i)) (C (stdOrthonormalBasis ℂ Wq i)) := by
  simp only [B.hsVec, PiLp.inner_apply, PiLp.toLp_apply]

theorem hs_comp_right (A C : Wq →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) (hQ : ∀ v w, inner ℂ (Q v) w = inner ℂ v (Q w)) :
    inner ℂ (B.hsVec A) (B.hsVec (C.comp Q)) = inner ℂ (B.hsVec (A.comp Q)) (B.hsVec C) := by
  rw [hs_expand, hs_expand]
  set b := stdOrthonormalBasis ℂ Wq
  have hQe : ∀ i, Q (b i) = ∑ j, inner ℂ (b j) (Q (b i)) • b j := fun i => (b.sum_repr' _).symm
  simp only [ContinuousLinearMap.comp_apply]
  conv_lhs => arg 2; ext i; rw [hQe i, map_sum, inner_sum]
  conv_rhs => arg 2; ext j; rw [hQe j, map_sum, sum_inner]
  simp only [map_smul, inner_smul_right, inner_smul_left]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [inner_conj_symm, hQ]

theorem hs_comp_sum {ι : Type} [Fintype ι] (A C : Wq →L[ℂ] Wp) (Q : ι → (Wq →L[ℂ] Wq)) (f : ι → ℂ) :
    inner ℂ (B.hsVec A) (B.hsVec (C.comp (∑ σ, f σ • Q σ))) =
      ∑ σ, f σ * inner ℂ (B.hsVec A) (B.hsVec (C.comp (Q σ))) := by

  simp only [hs_expand, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
  ContinuousLinearMap.smul_apply, map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
  exact Finset.sum_comm

theorem comp_sum_eq {ι : Type} [Fintype ι] (C : Wq →L[ℂ] Wp) (Q : ι → (Wq →L[ℂ] Wq)) :
    C.comp (∑ σ, Q σ) = ∑ σ, C.comp (Q σ) := by
  ext v

  simp [ContinuousLinearMap.sum_apply, map_sum]

end hs

theorem gauge_kappa_of_point_line : GTKapOfCut := by
  intro hPt hLine Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨Qr, hQ⟩ := hPt Wp Wq P Bs X d hH
  have hQQ := hQ.1
  have hQ1 := hQ.2.1
  have hQs := hQ.2.2.1
  have hQk := hQ.2.2.2
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hH.1
  have hcs : CSec P.k P.r Bs.z Bs.z' Bs.μsec := hH.2.2.1
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl

  set ζ0 : ℂ := ((Real.sqrt P.TT + 1 : ℝ) : ℂ) with hζ0def
  have hTT : 0 < P.TT := mul_pos hpl.1.T_pos hpl.1.T'_pos
  have hζ0 : P.TT < Complex.normSq ζ0 := by
    rw [hζ0def, Complex.normSq_ofReal]
    have hs := Real.sq_sqrt hTT.le
    nlinarith [Real.sqrt_nonneg P.TT]

  have hFib : ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro ζ hζ
    have hS : NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ = NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ0 :=
      hcs.2 ζ ζ0 (by rw [hTz]; exact hζ) (by rw [hTz]; exact hζ0)
    unfold NF.Fib
    rw [hS]
  choose E hEF hEQ hE1 hEu using fun ρ => hLine Wp Wq P Bs X d hH Qr hQ ζ0 hζ0 ρ

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨hpl.1.k_pos, hpl.2.1, hpl.2.2.1, by rw [hpl.2.2.2.1]; exact hpl.1.T_pos,
      by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos, Bs.sec, hpl.2.2.2.2.2.1.2.1, hpl.2.2.2.2.2.2.2.1,
      hpl.2.2.2.2.2.1.2.2.1, hpl.2.2.2.2.2.2.2.2.1⟩
  have hcomp : ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0, ∀ ρ,
      Z.comp (Qr ρ) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro Z hZ ρ
    let φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator fun _ => Z
    have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
      refine ⟨(contDiffOn_const (c := Z)).congr fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · simp [φ, Set.indicator_of_mem hx]
      · simp only [φ, Set.indicator_of_mem hx]
        rw [hFib x.2 (by rw [← hTz]; exact hx.2)]; exact hZ
      · simp [φ, Set.indicator_of_notMem hx]
    obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB φ hφ
    let c0 : Fin P.r → ℂ := fun _ => 1
    have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
    have hq0 : ((c0, ζ0) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ0⟩
    have hval : Φ c0 (NF.muZ P.k P.r Bs.μsec ζ0) = Z := by
      have h := congrFun hrad (c0, ζ0)
      simp only [NF.radR, Set.indicator_of_mem hq0, φ] at h
      exact h
    let q0 : MA.Qp P.r P.TT := ⟨(c0, ζ0), ⟨hc0, hζ0⟩⟩
    let f : M.Ty P → ℂ := fun σ => if σ = ρ then 1 else 0
    have hk := hQk f ⟨Φ, hΦ⟩ q0
    have hsum : (∑ σ, f σ • Qr σ) = Qr ρ := by
      simp [f, Finset.sum_ite_eq']
    rw [hsum] at hk
    have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _
      ((d.κ f).1 ⟨Φ, hΦ⟩).2
    have h2 := hmem.2.1 (c0, ζ0) hq0
    simp only [NF.radR, Set.indicator_of_mem hq0] at h2
    have hk' : (((d.κ f).1 ⟨Φ, hΦ⟩ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0
        (NF.muZ P.k P.r Bs.μsec ζ0) = Z.comp (Qr ρ) := by
      rw [← hval]; exact hk
    rw [hk'] at h2
    exact h2
  refine ⟨fun ρ _ => E ρ, ⟨fun ρ => contDiffOn_const, fun ζ hζ => ⟨fun ρ => ?_, fun ρ ρ' => ?_, fun Z hZ => ?_⟩⟩, ?_⟩
  · rw [hFib ζ hζ]; exact hEF ρ
  · split_ifs with h
    · subst h; exact hE1 ρ
    · calc inner ℂ (B.hsVec (E ρ)) (B.hsVec (E ρ'))
          = inner ℂ (B.hsVec (E ρ)) (B.hsVec ((E ρ').comp (Qr ρ'))) := by rw [hEQ ρ']
        _ = inner ℂ (B.hsVec ((E ρ).comp (Qr ρ'))) (B.hsVec (E ρ')) := hs_comp_right _ _ _ (hQs ρ')
        _ = 0 := by
          have h0 : (E ρ).comp (Qr ρ') = 0 := by
            rw [← hEQ ρ, ContinuousLinearMap.comp_assoc, hQQ ρ ρ', if_neg h, ContinuousLinearMap.comp_zero]
          rw [h0, VLem.hsV_zero, inner_zero_left]
  · have hZ0 : Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by rw [← hFib ζ hζ]; exact hZ
    have hdec : Z = ∑ ρ, Z.comp (Qr ρ) := by
      rw [← comp_sum_eq, hQ1]; rfl
    conv_lhs => rw [hdec]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hfix : (Z.comp (Qr ρ)).comp (Qr ρ) = Z.comp (Qr ρ) := by
      rw [ContinuousLinearMap.comp_assoc, hQQ ρ ρ, if_pos rfl]
    rw [hEu ρ _ (hcomp Z hZ0 ρ) hfix, hs_comp_right _ _ _ (hQs ρ), hEQ ρ]
  · intro f Φ
    funext ρ
    have hraw : rawR P Bs.μsec (fun ρ _ => E ρ)
        (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
        f ρ • rawR P Bs.μsec (fun ρ _ => E ρ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
      funext q
      simp only [rawR, Pi.smul_apply, smul_eq_mul]
      rw [hQk f Φ q, hs_comp_sum]
      have hterm : ∀ σ, f σ * inner ℂ (B.hsVec (E ρ))
          (B.hsVec (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)).comp (Qr σ))) =
          if σ = ρ then f ρ * inner ℂ (B.hsVec (E ρ))
            (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) else 0 := by
        intro σ
        rw [hs_comp_right _ _ _ (hQs σ)]
        split_ifs with h
        · subst h; rw [hEQ σ]
        · have h0 : (E ρ).comp (Qr σ) = 0 := by
            rw [← hEQ ρ, ContinuousLinearMap.comp_assoc, hQQ ρ σ, if_neg (Ne.symm h), ContinuousLinearMap.comp_zero]
          rw [h0, VLem.hsV_zero, inner_zero_left, mul_zero]
      simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    show MA.toSm P (rawR P Bs.μsec (fun ρ _ => E ρ)
        (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) = _
    rw [hraw, VLem.toSm_smul]
    have hkap : MA.kap P (MA.DQ P) f = Matrix.diagonal fun σ => algebraMap ℂ (MA.DQ P).Pr (f σ) := rfl
    rw [hkap, VLem.actA_diag]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jdc_thrW (o : ℕ) (A d : ℝ) (hd : 0 ≤ d)
    (h : 12 * ((r : ℝ) + 1) * nDim k r ^ 2 + 6 * (r : ℝ) * (o : ℝ) + d ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  unfold Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold
  have hn : nDim k r = 2 * (r : ℝ) + k + 1 := by unfold nDim; push_cast; ring
  rw [hn] at h
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have key : (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1) <
      12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by
    nlinarith [pow_nonneg hr 3, mul_nonneg hr (mul_nonneg hk hk), mul_nonneg (mul_nonneg hr hr) hk,
      mul_nonneg hr hr, mul_nonneg hr hk, mul_nonneg hk hk]
  have hpos : 0 < 12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by positivity
  constructor <;> linarith

theorem jdc_om_sub_gpos (Db : B.RealPlaceData k r Wp Wq) : JF.Om k r Db.z Db.z' ⊆ B.GPos Db := by
  intro g hg
  unfold JF.Om Q.OmPlus at hg
  unfold B.GPos
  exact ⟨hg.1, hg.2.2⟩

theorem jdc_om_of (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r)
    (h : 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0) :
    g ∈ JF.Om k r z z' := by
  refine ⟨hg, ?_, h.1⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l.val with h0 | h0
  · have e : l = ⟨0, by omega⟩ := Fin.ext h0
    rw [e]
    unfold Formalism.QuantumDeterminants.Dmin
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · have e : l = ⟨((⟨l.val - 1, by omega⟩ : Fin r) : ℕ) + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e]
    exact h.2 _

theorem jdc_of_om (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0 := by
  unfold JF.Om Q.OmPlus at hg
  obtain ⟨_, hD, hG⟩ := hg
  exact ⟨hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩

end gen

section gen2

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

theorem jdc_ckOn_mono {m : ℕ∞} {UU VV : Set (B.Mat k r)} (h : UU ⊆ VV) {f : B.Mat k r → E₁} (hf : B.CkOn m VV f) :
    B.CkOn m UU f := by
  intro g₀ hg₀
  exact hf g₀ (h hg₀)

theorem jdc_ckOn_ap {UU : Set (B.Mat k r)} {a : B.Mat k r → (E₁ →L[ℂ] E₂)} {Φ : B.Mat k r → E₁}
    (ha : B.CkOn ⊤ UU a) (hΦ : B.CkOn ⊤ UU Φ) : B.CkOn ⊤ UU (fun g => a g (Φ g)) := by
  unfold B.CkOn at *
  intro g₀ hg₀
  obtain ⟨U₁, a', hU₁, hg₁, ha', hea⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hg₂, hΦ', heΦ⟩ := hΦ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => a' g (Φ' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · have hr : ContDiffOn ℝ _ (fun g => (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ) (a' g)) (U₁ ∩ U₂) :=
      (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn (ha'.mono Set.inter_subset_left)
    exact hr.clm_apply (hΦ'.mono Set.inter_subset_right)
  · intro g hg hgG
    simp only [hea g hg.1 hgG, heΦ g hg.2 hgG]

theorem jdc_ckOn_Rw {UU : Set (B.Mat k r)} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    {f : B.Mat k r → E₁} (hf : B.CkOn ⊤ UU f) : B.CkOn ⊤ UU (B.Rw w f) := by
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  apply Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw (fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x
    (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx))
  have e : ((⊤ : ℕ∞) + ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w).length : ℕ∞)) = ⊤ := top_add _
  rw [e]; exact hf

end gen2

section gen3

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem jdc_ckOn_opApply {UU : Set (B.Mat k r)} {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : B.CkOn ⊤ UU J) :
    ∀ Θ : B.DiffOp k r Wp Wq, (∀ T ∈ Θ, B.CkOn ⊤ UU T.coef) → B.CkOn ⊤ UU (B.opApply Θ J)
  | [], _ => by
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) J = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, h => by
    have e : B.opApply (T :: Θ) J = fun g => T.coef g (B.Rw T.word J g) + B.opApply Θ J g := by
      funext g; simp [B.opApply]
    rw [e]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (jdc_ckOn_ap (h T (by simp)) (jdc_ckOn_Rw T.word_lie hJ))
      (jdc_ckOn_opApply hJ Θ (fun T' hT' => h T' (by simp [hT'])))

theorem jdc_ckOn_om (z z' : Fin (2 * r + k + 1) → ℂ) {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : Q.SmoothLev k r 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} J) :
    B.CkOn ⊤ (JF.Om k r z z') J := by
  unfold B.CkOn
  unfold Q.SmoothLev at hJ
  intro g₀ hg₀
  unfold JF.Om Q.OmPlus at hg₀
  obtain ⟨hgG, hD, hG⟩ := hg₀
  have hmem : g₀ ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} :=
    ⟨⟨hgG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hJ g₀ hmem
  refine ⟨U, F, hU, hgU, hF, ?_⟩
  intro g hg hgV
  exact hJF g hg ⟨hgV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

variable [FiniteDimensional ℂ Wp]

theorem jdc_ffl (Db : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (hSC : B.SmoothCoef (B.GPos Db) Θ)
    {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0})
    (H : B.Mat k r → (Wq →L[ℂ] Wp)) (hH : ∀ g ∈ JF.Om k r Db.z Db.z', B.opApply Θ J g = B.JF Db H g) :
    B.JF Db H ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Db.z Db.z' cStd Db.π Db.π' Db.μW Db.μN Db.μW' H Db.z_mem Db.z'_mem
    Db.haarN.conc (fun n₀ h => Db.haarN.left n₀ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    have hg₀O : g₀ ∈ JF.Om k r Db.z Db.z' := jdc_om_of _ _ hg₀.1.1 hg₀.2
    have hck := jdc_ckOn_opApply (jdc_ckOn_om Db.z Db.z' hJ.1) Θ
      (fun T hT => jdc_ckOn_mono (jdc_om_sub_gpos Db) (hSC T hT).1)
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hck g₀ hg₀O
    refine ⟨U ∩ Q.OmPlus k r Db.z Db.z', f', hU.inter (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _), ⟨hgU, hg₀O.2⟩,
      hc.mono Set.inter_subset_left, ?_⟩
    intro g hg hgG
    have hgO : g ∈ JF.Om k r Db.z Db.z' := ⟨hgG.1, hg.2⟩
    rw [← hH g hgO]
    exact he g hg.1 hgG.1
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.FourierDecayAlt.P5.jf_uEquiv Db H g hh hh'

end gen3

theorem transfer_commutation_holds : JDJComm := by
  refine ⟨12, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d A hd hSC hC _hG hA F _hCk hCC hJF
  have hT := jdc_thrW (k := S.G.k) (r := S.G.r) (B.opOrder Θ) A d hd hA
  have hCOm : B.Commutes (T v).base (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') Θ :=
    fun p hp f' hf' g hg => hC p hp f' hf' g (jdc_om_sub_gpos _ hg)
  have hth := Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ (T v).base A (B.opOrder Θ) F Θ _ subset_rfl le_rfl hT (hCC _) hCOm
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨jdc_ffl (T v).base Θ hSC hJF _ hth, ?_⟩
  intro x hx
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  exact hth _ (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq)

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

def Exh : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V F₂ (h ++ [(1, ζ)])) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

def HeadVecOfParts : Prop := HighestUnipotentIntegral → Exh → HeadVec

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem head_vector_of_parts : PBI.HeadVecOfParts := by
  intro hU5 hExh Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hζ hγF h hh Φ hΦ e
  obtain ⟨F₂, hF₂, hV, hJ⟩ := hExh Wp Wq P p F w X μ L st Cb hD hdd hF hcut e h hh
  set ζ := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζdef
  have hr : P.r - P.r = 0 := by omega
  have hGx : 0 < Complex.normSq ζ - Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' :=
    hx.2.2
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hGx
    nlinarith [mul_pos (p.T.bs P.r).T_pos (p.T.bs P.r).T'_pos]
  have hZ : Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ = D.ptMatN [(1, ζ)] (P.r - P.r + 1) := by
    ext a b
    have ha : a = Fin.last _ := Fin.ext (by have := a.isLt; simp only [Fin.val_last]; omega)
    have hb : b = Fin.last _ := Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
    subst ha hb
    rw [← PBI.zetaL_eq_zhat, hζ]
    simp [D.ptMatN, D.ptEntry, hr]
  have hγGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ := by
    show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
    rw [hζ]; exact hGx
  show p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = _
  rw [hV, hU5 Wp Wq P p F₂ h ζ hh ν'r m₀r hF₂ hζ0 hLev.1 hLev.2.1,
    PBM.vector_level_zero_eq_jacquet hr (p.T.bs P.r) ν'r m₀r hLev.2.2 _ ζ (by linarith) γ₀ hγG hZ hγF]
  exact hJ Φ hΦ x.1 γ₀ hγG hγGG

end Formalism.FourierDecayAlt.P
end
end
