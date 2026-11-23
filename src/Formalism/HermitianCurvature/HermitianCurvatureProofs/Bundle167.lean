module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle068
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle151
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle140
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle139
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle149
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_zero_holds : SAZero := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he X hX y hy h0
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hw : 0 < Real.sqrt (MA.wq S.G.k y (D.parOf S v).TT) := by
    apply Real.sqrt_pos.2
    unfold MA.wq
    exact mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hy.1 l)) _)
      (pow_pos (sub_pos.2 hy.2) _)
  have hin : ∀ π, inner ℂ (B.hsVec (e π y.2)) (B.hsVec (X (B.gq (T v).base y))) = 0 := by
    intro π
    have hsm := En.trace_smoothness E Wp Wq S T v hplace e he X hX π
    have h := h0 π
    unfold trJ at h
    rw [En.toSm_val_of_mem _ hsm] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (Complex.ofReal_ne_zero.2 hw.ne')
    · exact h
  have hfib := En.fibre_membership_holds E Wp Wq S T v hplace X hX y hy
  rw [(he.2 y.2 hy.2).2.2 _ hfib]
  simp [hin]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

private theorem hsVec_finset_sum_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} [Fintype ι]
    (c : ι → ℂ) (A : ι → Wq →L[ℂ] Wp) : B.hsVec (∑ i, c i • A i) = ∑ i, c i • B.hsVec (A i) := by
  ext j
  simp [B.hsVec]

private theorem hsVec_injective_apply {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A C : Wq →L[ℂ] Wp)
    (h : B.hsVec A = B.hsVec C) : A = C := by
  have h' : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = C (stdOrthonormalBasis ℂ Wq i) := fun i => by
    have := congrArg (fun v => v i) h
    simpa [B.hsVec] using this
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using h' i)

private theorem toSm_smul_hermitian_curvature (P : M.Par) (c : ℂ) (u : MA.Qp P.r P.TT → ℂ) :
    MA.toSm P (c • u) = c • MA.toSm P u := by
  unfold MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · rw [dite_eq_left hu, dite_eq_left (Subalgebra.smul_mem _ hu c)]
    rfl
  · rw [dite_eq_right hu]
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, smul_zero, dite_eq_left (Subalgebra.zero_mem _)]
      rfl
    · rw [smul_zero, dite_eq_right]
      intro hm
      apply hu
      have := Subalgebra.smul_mem _ hm c⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem radial_constant_of_point_and_line (hPt : GTKPt) (hLine : GTKLine) : GTRConst := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d h
  obtain ⟨Qr, hQ⟩ := hPt Wp Wq P Bs X d h
  obtain ⟨e1, he1F, -⟩ := gauge_kappa_of_point_line hPt hLine Wp Wq P Bs X d h
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [h.1.2.2.2.1, h.1.2.2.2.2.1]
    rfl
  set ζ0 : ℂ := ((|P.TT| + 1 : ℝ) : ℂ) with hζ0def
  have hζ0 : P.TT < Complex.normSq ζ0 := by
    rw [hζ0def, Complex.normSq_ofReal]
    nlinarith [le_abs_self P.TT, abs_nonneg P.TT]
  have hFib : ∀ ζ, P.TT < Complex.normSq ζ →
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro ζ hζ
    unfold NF.Fib
    rw [h.2.2.1.2 ζ ζ0 (hTT ▸ hζ) (hTT ▸ hζ0)]
  choose E hEmem hEQ hEnorm hEuniq using fun ρ => hLine Wp Wq P Bs X d h Qr hQ ζ0 hζ0 ρ
  have hEQ' : ∀ ρ σ, E ρ ∘SL Qr σ = if ρ = σ then E ρ else 0 := by
    intro ρ σ
    calc E ρ ∘SL Qr σ = (E ρ ∘SL Qr ρ) ∘SL Qr σ := by rw [hEQ ρ]
      _ = E ρ ∘SL (Qr ρ ∘SL Qr σ) := ContinuousLinearMap.comp_assoc _ _ _
      _ = _ := by
        rw [hQ.1 ρ σ]
        split_ifs <;> simp [hEQ ρ]
  have hinQ : ∀ ρ σ (C : Wq →L[ℂ] Wp), inner ℂ (B.hsVec (E ρ)) (B.hsVec (C ∘SL Qr σ)) =
      if ρ = σ then inner ℂ (B.hsVec (E ρ)) (B.hsVec C) else 0 := by
    intro ρ σ C
    rw [GTK.hs_comp_right _ _ _ (hQ.2.2.1 σ), hEQ' ρ σ]
    split_ifs
    · rfl
    · rw [GTK.hs_expand]
      simp
  have horth : ∀ ρ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (E σ)) = if ρ = σ then 1 else 0 := by
    intro ρ σ
    have hh := hinQ ρ σ (E σ)
    rw [hEQ σ] at hh
    rw [hh]
    split_ifs with hρσ
    · subst hρσ
      exact hEnorm ρ
    · rfl
  have hv : Orthonormal ℂ (fun σ => B.hsVec (E σ)) := orthonormal_iff_ite.mpr horth
  have hw : Orthonormal ℂ (fun σ => B.hsVec (e1 σ ζ0)) := orthonormal_iff_ite.mpr (he1F.2 ζ0 hζ0).2.1
  have hspan1 : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0,
      B.hsVec Y ∈ Submodule.span ℂ (Set.range (fun σ => B.hsVec (e1 σ ζ0))) := by
    intro Y hY
    rw [(he1F.2 ζ0 hζ0).2.2 Y hY, hsVec_finset_sum_smul]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hle : Submodule.span ℂ (Set.range (fun σ => B.hsVec (E σ))) ≤
      Submodule.span ℂ (Set.range (fun σ => B.hsVec (e1 σ ζ0))) := by
    rw [Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    exact hspan1 _ (hEmem σ)
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_span_eq_card hv.linearIndependent, finrank_span_eq_card hw.linearIndependent])
  have hexp : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0,
      Y = ∑ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) • E σ := by
    intro Y hY
    have hm : B.hsVec Y ∈ Submodule.span ℂ (Set.range (fun σ => B.hsVec (E σ))) := heq ▸ hspan1 Y hY
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
    have hcoef : ∀ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) = c σ := by
      intro σ
      rw [← hc]
      exact hv.inner_right_fintype c σ
    apply hsVec_injective_apply
    rw [hsVec_finset_sum_smul]
    simp only [hcoef]
    exact hc.symm
  refine ⟨fun ρ _ => E ρ, ⟨fun ρ => contDiffOn_const, fun ζ hζ =>
    ⟨fun ρ => (hFib ζ hζ).symm ▸ hEmem ρ, horth, fun Y hY => hexp Y (hFib ζ hζ ▸ hY)⟩⟩, ?_, fun ρ ζ ζ' => rfl⟩
  intro f Φ
  funext ρ
  unfold trR MA.actA
  simp only [MA.kap, AlgHom.comp_apply, Matrix.diagonalAlgHom_apply, Matrix.diagonal_apply]
  have hR : rawR P Bs.μsec (fun ρ _ => E ρ) (↑((d.κ f).1 Φ)) ρ =
      f ρ • rawR P Bs.μsec (fun ρ _ => E ρ) (↑Φ) ρ := by
    funext q
    simp only [rawR, Pi.smul_apply, smul_eq_mul]
    rw [hQ.2.2.2 f Φ q, GTK.hs_comp_sum]
    simp only [hinQ, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  symm
  refine (Finset.sum_eq_single ρ ?_ ?_).trans ?_
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    rfl
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ
  · rw [if_pos rfl, hR, toSm_smul_hermitian_curvature]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem radial_gauge_constant_holds : GTRConst := GTK.radial_constant_of_point_and_line gauge_kappa_pointwise_holds gauge_kappa_line_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  ext i
  simp

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem vl_add (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (Φ + Ψ) ρ q = SSC.vl P Bs e Φ ρ q + SSC.vl P Bs e Ψ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_add, Pi.add_apply, hsVec_add, inner_add_right, mul_add]

theorem vl_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (c • Φ) ρ q = c * SSC.vl P Bs e Φ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_smul, Pi.smul_apply, hsVec_smul, inner_smul_right]
  ring

end vals

theorem dzQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vz 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vz 1 =
        MA.eulerQ (TT := P.TT) M.vz 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzQ MA.DAlg.dzP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vz 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0
  rw [h0', map_zero]

theorem dzbQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzbQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vzb 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vzb 1 =
        MA.eulerQ (TT := P.TT) M.vzb 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzbQ MA.DAlg.dzbP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vzb 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0
  rw [h0', map_zero]

theorem theta_fst {V : Type} [AddCommGroup V] [Module ℂ V] (P : M.Par) (d : Q.NFData P (Q.Pr V)) (Φ : V) :
    (ThetaNF P d).1 Φ = d.L.ζ.1 (d.L.nab.1 Φ) + d.L.ζb.1 (d.L.nabs.1 Φ) +
      (d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Φ +
      d.L.TT • d.L.GGi.1 ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Φ) := by
  unfold ThetaNF
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

theorem radial_gauge_transition_holds : GTRTrans := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hC ρ m hm ζ hζ
  classical
  have hpl := hyp.1
  have hk2 := hyp.2.1
  have hTT : 0 ≤ P.TT := (mul_pos hpl.1.T_pos hpl.1.T'_pos).le
  have hLTT : d.L.TT = ((P.TT : ℝ) : ℂ) := by
    rw [hyp.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]
    rfl
  obtain ⟨Φ0, hΦ0, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  set Ψ0 := (d.κ (dTy P ρ)).1 Φ0 with hΨ0
  have t0 : trR P Bs e Ψ0 ρ = 1 := by
    rw [hΨ0, hk (dTy P ρ) Φ0, hΦ0, actA_kap]
    simp [dTy]
  let q0 : MA.Qp P.r P.TT := ⟨((fun _ => (1 : ℂ)), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have v0 : SSC.vl P Bs e Ψ0 ρ q0 = 1 := by
    unfold SSC.vl
    rw [t0]
    rfl
  have t1 : trR P Bs e (d.L.nab.1 Ψ0) ρ = fnZ P (A ρ) := by
    rw [(hC Ψ0 ρ).1, t0, GTRT.dzQ_one P hTT, mul_one, zero_add]
  have t2 : trR P Bs e (d.L.nabs.1 Ψ0) ρ = fnZ P (B ρ) := by
    rw [(hC Ψ0 ρ).2, t0, GTRT.dzbQ_one P hTT, mul_one, neg_zero, zero_add]
  have v1 : SSC.vl P Bs e (d.L.nab.1 Ψ0) ρ q0 = A ρ ζ := by
    unfold SSC.vl
    rw [t1, fnZ_val P (hAB ρ).1]
  have v2 : SSC.vl P Bs e (d.L.nabs.1 Ψ0) ρ q0 = B ρ ζ := by
    unfold SSC.vl
    rw [t2, fnZ_val P (hAB ρ).2]

  have vm : SSC.vl P Bs e ((ThetaNF P d).1 Ψ0) ρ q0 = m := by
    unfold SSC.vl
    rw [hm Ψ0, t0, GTRT.dzQ_one P hTT, GTRT.dzbQ_one P hTT, mul_zero, mul_zero, sub_zero, zero_add]
    show m * 1 = m
    ring
  have v3 : SSC.vl P Bs e ((d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Ψ0) ρ q0 = ((rhoSum P ρ : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  have v4 : SSC.vl P Bs e ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Ψ0) ρ q0 =
      ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  clear_value Ψ0

  have hfn := fun Ψ => SSC.vl_fn P Bs X d hyp e Ψ ρ q0
  rw [GTRT.theta_fst, GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_add P Bs hpl hk2 e he,
    GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_smul P Bs hpl hk2 e he, (hfn _).1, (hfn _).2.1, (hfn _).2.2,
    v3, v4, v1, v2, hLTT] at vm
  have hq : q0.1.2 = ζ := rfl
  rw [hq] at vm
  have hG : (Complex.normSq ζ : ℂ) - (P.TT : ℂ) ≠ 0 := by
    have : P.TT < Complex.normSq ζ := hζ
    intro h0
    have h1 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have : Complex.normSq ζ - P.TT = 0 := by exact_mod_cast h1
    linarith
  rw [← vm]
  push_cast
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def LimEvT (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N →
    Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (p.RR F 0 w [] []).re)

theorem limE_of_partsT (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y) (hEv : LimEvT p χ F Y N) (hPos : LimPos p F Y N)
    (hBd : LimBd p nn F Y N) : LimE p nn χ F Y N := by
  intro w hw hl
  have hE := hEv w hw hl
  have hP := hPos w hw hl
  have hB := hBd w hw hl
  have hN : 0 ≤ TBB.normC nn w := by
    unfold TBB.normC
    exact List.prod_nonneg (fun x hx => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
      exact hnn _)
  by_cases hb : 0 < (B.beta p.T.base F F).re
  · refine ⟨(p.RR F 0 w [] []).re / (B.beta p.T.base F F).re, div_nonneg hP hb.le, (div_le_iff₀ hb).2 hB, ?_⟩
    rw [div_mul_cancel₀ _ hb.ne']
    exact hE
  · have hb' : (B.beta p.T.base F F).re ≤ 0 := not_lt.1 hb
    have hR0 : (p.RR F 0 w [] []).re = 0 :=
      le_antisymm (hB.trans (mul_nonpos_of_nonneg_of_nonpos hN hb')) hP
    refine ⟨0, le_refl 0, hN, ?_⟩
    rw [zero_mul]
    rw [hR0] at hE
    exact hE

end place


end

end Formalism.FourierDecayAlt.P.CutBP
end
