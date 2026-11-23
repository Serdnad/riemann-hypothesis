module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle044
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCoefficientHasCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_locality_holds : FamLocal := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk X Dc Φ hΦ q
  have hk1 : 1 ≤ P.k := by omega
  have hz := hpl.2.1
  have hz' := hpl.2.2.1
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hpl.2.2.2.1]; exact hpl.1.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos
  have hsec := Bs.sec
  obtain ⟨hOpen, hIsDom, hMu, hFF⟩ := hΦ

  have hdom : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', x.2 ∈ Dc x.1 := by
    intro x hx
    obtain ⟨h, hh, h', hh', hg⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp hk1 hz hz' hT hT' hsec hx.2.1 hx.2.2
    set ζ := Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2 with hζ
    have hζT : P.TT < Complex.normSq ζ := by
      have h1 := hx.2.2
      unfold Q.GGl at h1
      show P.T * P.T' < _
      rw [← hpl.2.2.2.1, ← hpl.2.2.2.2.1]
      linarith
    let q' : MA.Qp P.r P.TT := ⟨(x.1, ζ), hx.1, hζT⟩
    have hmu : NF.muZ P.k P.r Bs.μsec ζ ∈ Dc x.1 := hMu q'
    have hmuG : NF.muZ P.k P.r Bs.μsec ζ ∈ Q.Glev P.k P.r (Fin.last P.r) :=
      Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem.muZ_glev hpl q'
    have hS : ∀ {w : Fin (2 * P.r + P.k + 1) → ℂ} {s : Q.Mx P.k P.r}, s ∈ UWset P.k P.r w →
        s ∈ Q.Slev P.k P.r w (Fin.last P.r) := by
      intro w s hs
      exact ⟨s, hs, 1, Formalism.FourierDecayAlt.P.Qx6.one_nlev _, by simp⟩
    rw [hg]
    exact (hIsDom x.1 hx.1).2 _ ⟨hmuG, hmu⟩ h (hS hh) h' (hS hh')

  let Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g => if (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ c g else 0
  have hΦt_mem : Φt ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0) = 0
      rw [if_neg hx]
    · obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := hFF.1 x₀ ⟨hx₀.1, hdom x₀ hx₀⟩ hx₀.2.1
      have hO : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r ∧ 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} := by
        have h1 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r} := by
          have : IsOpen (OmX P.r) := by
            have e : OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
            rw [e]
            exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
          exact this.preimage continuous_fst
        have h2 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} :=
          isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z').comp continuous_snd)
        exact h1.inter h2
      refine ⟨U ∩ {x | x.1 ∈ OmX P.r ∧ 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2}, F, hU.inter hO, ⟨hx₀U, hx₀.1, hx₀.2.2⟩,
        hF.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
      have hxD : x ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hx.2.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0) = F x
      rw [if_pos hxD]
      exact hΦF x hx.1 hxG
    · have hxD' := Formalism.FourierDecayAlt.P.Qx5.DomR_inv hh hh' hx
      show (if (x.1, h * x.2 * h') ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 (h * x.2 * h') else 0) =
        (Bs.π h).comp ((if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0).comp (Bs.π' h'))
      rw [if_pos hxD', if_pos hx]
      exact (hFF.2 x.1 hx.1).2.2.2 x.2 ⟨hx.2.1, hdom x hx⟩ h hh h' hh'
  refine ⟨⟨Φt, hΦt_mem⟩, {ζ' | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ'}, ?_, fun ζ' hζ' => ?_⟩
  · refine (isOpen_lt continuous_const Complex.continuous_normSq).mem_nhds ?_
    show Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact q.2.2
  have hqD : (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec (q := (q.1.1, ζ')) ⟨q.2.1, hζ'⟩
  have hval : Φt q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') = Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') := by
    show (if (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') ∈ Q.DomR P.k P.r Bs.z Bs.z' then _ else 0) = _
    rw [if_pos hqD]
  refine ⟨hval, fun Y a b => ?_⟩
  rw [X.t_apply Y a b ⟨Φt, hΦt_mem⟩ (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') hqD]
  show Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (Φt q.1.1) (NF.muZ P.k P.r Bs.μsec ζ') =
    Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (Φ q.1.1) (NF.muZ P.k P.r Bs.μsec ζ')
  have hDo : IsOpen {g : Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' g} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z')
  refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := Fin.last P.r) hDo Bs.z Bs.z' Y a b).1 (Φt q.1.1) (Φ q.1.1) (fun x hx => ?_)
    _ ⟨hqD.2.1, hqD.2.2⟩
  show (if (q.1.1, x) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ q.1.1 x else 0) = Φ q.1.1 x
  rw [if_pos ⟨q.2.1, hx.1, hx.2⟩]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

section sm

variable {r : ℕ} {TT : ℝ}

theorem smInv_mem (f : MA.SmQ r TT) (hf : ∀ q, (f : MA.Qp r TT → ℂ) q ≠ 0) :
    (fun q => ((f : MA.Qp r TT → ℂ) q)⁻¹) ∈ MA.smSub r TT := by
  have hsm : ContDiffOn ℝ MA.sm (MA.ext (f : MA.Qp r TT → ℂ)) (MA.Qset r TT) := f.2
  have hne : ∀ x ∈ MA.Qset r TT, MA.ext (f : MA.Qp r TT → ℂ) x ≠ 0 := by
    intro x hx
    simp only [MA.ext, dif_pos hx]
    exact hf _
  show ContDiffOn ℝ MA.sm (MA.ext (fun q => ((f : MA.Qp r TT → ℂ) q)⁻¹)) (MA.Qset r TT)
  exact (hsm.inv hne).congr fun x hx => by simp only [Pi.inv_apply, MA.ext, dif_pos hx]

theorem inverse_apply (f : MA.SmQ r TT) (hf : ∀ q, (f : MA.Qp r TT → ℂ) q ≠ 0) (q : MA.Qp r TT) :
    ((Ring.inverse f : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = ((f : MA.Qp r TT → ℂ) q)⁻¹ := by
  obtain ⟨g, hg⟩ : ∃ g : MA.SmQ r TT, ∀ q, (g : MA.Qp r TT → ℂ) q = ((f : MA.Qp r TT → ℂ) q)⁻¹ :=
    ⟨⟨_, smInv_mem f hf⟩, fun _ => rfl⟩
  have hfg : f * g = 1 := by
    apply Subtype.ext
    funext q'
    show (f : MA.Qp r TT → ℂ) q' * (g : MA.Qp r TT → ℂ) q' = 1
    rw [hg, mul_inv_cancel₀ (hf q')]
  have hu : IsUnit f := ⟨⟨f, g, hfg, by rw [mul_comm]; exact hfg⟩, rfl⟩
  have hinv : Ring.inverse f = g := by
    calc Ring.inverse f = Ring.inverse f * (f * g) := by rw [hfg, mul_one]
      _ = g := by rw [← mul_assoc, Ring.inverse_mul_cancel f hu, one_mul]
  rw [hinv, hg]

theorem coordQ_vz (q : MA.Qp r TT) : ((MA.coordQ (r := r) (TT := TT) M.vz : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = q.1.2 := by
  show MA.coordE (M.vz (r := r)) q.1 = q.1.2
  simp [MA.coordE, MA.zE, M.vz]

theorem coordQ_vzb (q : MA.Qp r TT) :
    ((MA.coordQ (r := r) (TT := TT) M.vzb : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = (starRingEnd ℂ) q.1.2 := by
  show MA.coordE (M.vzb (r := r)) q.1 = (starRingEnd ℂ) q.1.2
  simp [MA.coordE, MA.zE, M.vzb]

end sm

def ggS (P : M.Par) : MA.SmQ P.r P.TT := (MA.DQ P).gg P.TT

section tr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem trR_unit (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (φ : MA.SmQ P.r P.TT) (hφ : ∀ q, (φ : MA.Qp P.r P.TT → ℂ) q ≠ 0)
    (hΨ : ∀ q : MA.Qp P.r P.TT, (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
      (φ : MA.Qp P.r P.TT → ℂ) q • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)) :
    trR P Bs e Ψ = fun ρ => φ * trR P Bs e Φ ρ := by
  have hsm : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A
    unfold B.hsVec
    ext i
    simp
  funext ρ
  have hraw : rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      fun q => (φ : MA.Qp P.r P.TT → ℂ) q * rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
    funext q
    simp only [rawR]
    rw [hΨ q, hsm, inner_smul_right]
    ring
  show MA.toSm P (rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) =
    φ * MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)
  rw [hraw]
  generalize rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ = u
  unfold MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · have hmul : (fun q => (φ : MA.Qp P.r P.TT → ℂ) q * u q) ∈ MA.smSub P.r P.TT :=
      (MA.smSub P.r P.TT).mul_mem φ.2 hu
    rw [dif_pos hmul, dif_pos hu]
    rfl
  · have hmul : (fun q => (φ : MA.Qp P.r P.TT → ℂ) q * u q) ∉ MA.smSub P.r P.TT := by
      intro hm
      apply hu
      have h2 := (MA.smSub P.r P.TT).mul_mem (smInv_mem φ hφ) hm
      convert h2 using 1
      funext q
      simp [hφ q]
    rw [dite_eq_right hmul, dite_eq_right hu, mul_zero]

theorem sec_pt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (q : MA.Qp P.r P.TT) :
    (q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' ∧
      Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) (NF.muZ P.k P.r Bs.μsec q.1.2) = q.1.2 := by
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact q.2.2
  have hq : (q.1.1, q.1.2) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨q.2.1, hζ⟩
  exact ⟨Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq,
    Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ⟩

theorem tt_pos (P : M.Par) (hP : P.OK) : 0 < P.TT := by
  show 0 < P.T * P.T'
  exact mul_pos hP.T_pos hP.T'_pos

theorem zeta_ne (P : M.Par) (hP : P.OK) (q : MA.Qp P.r P.TT) : q.1.2 ≠ 0 := by
  have h2 : P.TT < Complex.normSq q.1.2 :=
    (q.2 : (∀ l, q.1.1 l ≠ 0) ∧ P.TT < Complex.normSq q.1.2).2
  intro h
  rw [h, map_zero] at h2
  linarith [tt_pos P hP]

theorem gg_ne (P : M.Par) (q : MA.Qp P.r P.TT) : (q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ)) ≠ 0 := by
  have h2 : P.TT < Complex.normSq q.1.2 :=
    (q.2 : (∀ l, q.1.1 l ≠ 0) ∧ P.TT < Complex.normSq q.1.2).2
  rw [Complex.mul_conj]
  intro h
  have h3 : ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ) = 0 := by
    push_cast
    exact h
  rw [Complex.ofReal_eq_zero] at h3
  linarith

theorem trR_fn (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (j : Fin 6)
    (φ : MA.SmQ P.r P.TT) (hφ : ∀ q, (φ : MA.Qp P.r P.TT → ℂ) q ≠ 0)
    (hv : ∀ q : MA.Qp P.r P.TT, Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec q.1.2) = (φ : MA.Qp P.r P.TT → ℂ) q)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    trR P Bs e (X.fn j Φ) =
      fun ρ => φ * trR P Bs e Φ ρ := by
  refine trR_unit P Bs e Φ (X.fn j Φ) φ hφ fun q => ?_
  have h := X.fn_apply j Φ _ (sec_pt P Bs hpl q).1
  dsimp only at h
  rw [h, hv q]

end tr

theorem gauge_function_holds : GTFn := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e Φ
  obtain ⟨hpl, -, -, hL, -, -, -⟩ := hH
  have hP : P.OK := hpl.1
  have hz := fun q => (sec_pt P Bs hpl q).2
  have hzv : ∀ q : MA.Qp P.r P.TT, ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) q ≠ 0 := fun q => by rw [coordQ_vz]; exact zeta_ne P hP q
  have hzbv : ∀ q : MA.Qp P.r P.TT, ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) q ≠ 0 := fun q => by
    rw [coordQ_vzb]; exact (map_ne_zero _).2 (zeta_ne P hP q)
  have hgg : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    show ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q *
        ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q - (P.TT : ℂ) = _
    rw [coordQ_vz, coordQ_vzb]
  have hggv : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q ≠ 0 :=
    fun q => by rw [hgg]; exact gg_ne P q
  have hGG : ∀ q : MA.Qp P.r P.TT, ((Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) : ℝ) : ℂ) =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    rw [Complex.mul_conj]
    unfold Q.GGl
    rw [hz q, hpl.2.2.2.1, hpl.2.2.2.2.1]
    have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * (P.T' : ℂ) := by
      show (((P.T * P.T' : ℝ)) : ℂ) = _
      push_cast; ring
    rw [hT]
    push_cast
    ring
  have hsc : ∀ (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT),
      MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := VLem.actA_sc P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 0 _ hzv (fun q => by rw [coordQ_vz]; exact hz q) Φ).trans ?_
    exact (hsc ((MA.DQ P).zP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 1 (Ring.inverse (MA.coordQ M.vz))
      (fun q => by rw [inverse_apply _ hzv]; exact inv_ne_zero (hzv q))
      (fun q => by rw [inverse_apply _ hzv, coordQ_vz]; show (Q.zetaL _ _ _ _ _ _)⁻¹ = _; rw [hz q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ziP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 2 _ hzbv (fun q => by
      rw [coordQ_vzb]; show star (Q.zetaL _ _ _ _ _ _) = _; rw [hz q]; rfl) Φ).trans ?_
    exact (hsc ((MA.DQ P).zbP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 3 (Ring.inverse (MA.coordQ M.vzb))
      (fun q => by rw [inverse_apply _ hzbv]; exact inv_ne_zero (hzbv q))
      (fun q => by
        rw [inverse_apply _ hzbv, coordQ_vzb]; show (star (Q.zetaL _ _ _ _ _ _))⁻¹ = _; rw [hz q]; rfl) Φ).trans ?_
    exact (hsc ((MA.DQ P).zbiP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 4 _ hggv (fun q => by rw [hgg]; exact hGG q) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggP P.TT) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 5 (Ring.inverse (ggS P))
      (fun q => by rw [inverse_apply _ hggv]; exact inv_ne_zero (hggv q))
      (fun q => by rw [inverse_apply _ hggv, hgg]; show ((Q.GGl _ _ _ _ _ : ℝ) : ℂ)⁻¹ = _; rw [hGG q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ)).symm

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT
end

section

open MeasureTheory
open scoped ComplexConjugate ContDiff Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PBI Formalism.FourierDecayAlt.P.PBI.Sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_castM_sfg {k a b : ℕ} (e : a = b) : ContDiff ℝ ∞ (fun g : B.Mat k a => D.castM e g) := by
  subst e
  have h1 : (fun g : B.Mat k a => D.castM rfl g) = fun g => g := by
    funext g
    simp [D.castM]
  rw [h1]
  exact contDiff_id

theorem castM_pt_sfg {k a b : ℕ} (h : a = b) (A M C : B.Mat k a) :
    (D.castM h A)⁻¹ * D.castM h M * D.castM h C = D.castM h (A⁻¹ * M * C) := by
  subst h
  simp [D.castM]

theorem contDiff_radial_embedding {k ρ m : ℕ} (e : ρ + 1 = m) : ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => rn1 e x) := by
  refine contDiff_iff_contDiffAt.2 fun x₀ => ?_
  have hR : ContDiffAt ℝ ∞ (fun x : U.RC k 1 ρ => U.Rn k 1 ρ x) x₀ :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => ms_rnC (f := fun y : U.RC k 1 ρ => y) contDiffAt_id i l
  unfold rn1
  exact ((contDiff_castM_sfg e).comp (contDiff_castM_sfg (Nat.add_comm 1 ρ))).contDiffAt.comp x₀ hR

theorem point_smooth : PtSmooth := by
  intro k ρ m e
  constructor
  · have hfun : (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => pt e q.1.1 q.1.2 q.2) =
        fun q => D.castM e (D.castM (Nat.add_comm 1 ρ)
          ((U.Rn k 1 ρ q.2.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => q.1.1) q.1.2 * U.Rn k 1 ρ q.2.2)) := by
      funext q
      unfold pt rn1 mc
      rw [castM_pt_sfg, castM_pt_sfg]
    rw [hfun]
    refine ((contDiff_castM_sfg e).comp (contDiff_castM_sfg (Nat.add_comm 1 ρ))).comp_contDiffOn ?_
    intro q₀ hq₀
    have ht : q₀.1.1 ≠ 0 := hq₀.1
    have hx : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.2.1) q₀ :=
      contDiffAt_fst.comp q₀ contDiffAt_snd
    have hx' : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.2.2) q₀ :=
      contDiffAt_snd.comp q₀ contDiffAt_snd
    have htc : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.1.1) q₀ :=
      contDiffAt_fst.comp q₀ contDiffAt_fst
    have hZ : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) =>
        Matrix.of fun (_ : Fin 1) (_ : Fin 1) => q.1.1) q₀ :=
      ms_ofC (f := fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => fun (_ : Fin 1) (_ : Fin 1) => q.1.1)
        (contDiffAt_pi.2 fun _ => contDiffAt_pi.2 fun _ => htc)
    have hγc : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.1.2) q₀ :=
      contDiffAt_snd.comp q₀ contDiffAt_fst
    have hμ : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.1.2) q₀ := fun i l =>
      contDiffAt_pi.1 (contDiffAt_pi.1 hγc i) l
    have hdet : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => q₀.1.1).det ≠ 0 := by
      rw [Matrix.det_unique]; exact ht
    have hZi : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) =>
        (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => q.1.1)ᴴ⁻¹) q₀ :=
      ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hdet)
    have hm : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) =>
        U.mMap k 1 ρ (Matrix.of fun _ _ => q.1.1) q.1.2) q₀ := by
      unfold U.mMap
      exact measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hμ (ms_const _)
        (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)
    have hall := ms_mul (ms_mul (ms_rnC_inv hx) hm) (ms_rnC hx')
    exact (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => hall i l).contDiffWithinAt
  · intro z
    have hg := contDiff_radial_embedding (k := k) e
    have hE : ∀ i l, ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => rn1 e x i l) := fun i l =>
      contDiff_pi.1 (contDiff_pi.1 hg i) l
    have hell : ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => ell k m z (rn1 e x)) := by
      unfold ell
      refine ContDiff.sum fun a _ => ?_
      by_cases h : a.val + 1 < m
      · simp only [dif_pos h]
        exact hE _ _
      · simp only [dif_neg h, Matrix.mulVec, dotProduct]
        exact ContDiff.sum fun b _ => (hE _ _).mul contDiff_const
    unfold psi
    have hre : ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => (((cStd * ell k m z (rn1 e x)).re : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (contDiff_const.mul hell))
    exact Complex.contDiff_exp.comp (contDiff_const.mul hre)

end Formalism.FourierDecayAlt.P.CutSH.SFG
end
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

def mLev (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) (τ : ℂ) (γ : B.Mat P.k (P.r - (j + 1))) : B.Mat P.k (P.r - j) :=
  D.castM (by omega : 1 + (P.r - (j + 1)) = P.r - j) (U.mMap P.k 1 (P.r - (j + 1)) (Matrix.of fun _ _ => τ) γ)

def kapJ (P : M.Par) (j : ℕ) : ℂ := ((P.r - j : ℕ) : ℂ) + (P.k : ℂ) / 2

def HeadJ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ φ : Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp),
    (∀ e τ, τ ≠ 0 → (φ e).1 τ = B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 e) (mLev P j hj τ γ)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        (oneBT (kapJ P j) (D.positionted w) φ e).1 t

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end
