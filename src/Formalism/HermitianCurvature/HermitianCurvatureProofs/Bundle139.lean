module

public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle091
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle123
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle114
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle133
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW

noncomputable section

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P

theorem eb_intertwine {k r m : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {y z z' : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (h : IsFrameOf k r [y, z'] Bs)
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (hR : IsRepW k r z π) (hR' : IsRepW k r z' π')
    {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (hgB : IsFrameOf k r [z] (fun a => g *ᵥ Bs a)) (A : Wq →L[ℂ] Wp)
    (hint : ∀ h' ∈ UWset k r z', h' *ᵥ y = y → ∀ v, A (π' h' v) = π (g * h' * g⁻¹) (A v)) (a b : Fin m) (v : Wq) :
    A (EB π' Bs a b v) = EB π (fun a => g *ᵥ Bs a) a b (A v) := by
  have hB' : IsFrameOf k r [z'] Bs := Qx8.frame_sub h (by simp)
  have l' := QrD.frame_lie hB' a b
  have l := QrD.frame_lie hgB a b
  show A (QrD.ecOp π' _ v) = QrD.ecOp π _ (A v)
  rw [← QrD.ecRep_eq hR'.1 hR'.2 l'.1 l'.2, ← QrD.ecRep_eq hR.1 hR.2 l.1 l.2]
  have hU := Qx8.frame_InU h (z := z') (by simp) a b
  have hky := Qx8.hpart_kill Bs a b (Qx8.frame_orth h (v := y) (by simp))
  have hc := Qx8.hpart_conj Bs a b hg
  show A (dRep π' _ v + Complex.I • dRep π' _ v) = dRep π _ (A v) + Complex.I • dRep π _ (A v)
  rw [map_add (f := _), map_smul, hc.1, hc.2]
  congr 1
  · refine Qx8.dRep_intertwine A (Qx8.rep_hasDeriv hR'.1 hR'.2 hU.1 v) fun t => ?_
    rw [Qx8.exp_conj_uh hg]
    exact hint _ (hU.1 t) (Qx8.exp_fix hky.1 t) v
  · congr 1
    refine Qx8.dRep_intertwine A (Qx8.rep_hasDeriv hR'.1 hR'.2 hU.2 v) fun t => ?_
    rw [Qx8.exp_conj_uh hg]
    exact hint _ (hU.2 t) (Qx8.exp_fix hky.2 t) v

theorem hyp_snoc {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {n r : ℕ}
    {z e : Fin (2 * r + (n + 1) + 1) → ℂ} {π : Mx (n + 1) r → (W →L[ℂ] W)} {u : ℕ → ℝ} {β : ℂ}
    {L : Fin (n + 1) → ℤ} (hz : inWb (n + 1) r z) (hT : 0 < Tz (n + 1) r z) (hty : IsType (n + 1) r z π u)
    (hL : StrictAnti L)
    (hu : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ))
    (he : inWb (n + 1) r e) (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1)
    {Bs₀ : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ} (hB₀ : IsFrameOf (n + 1) r [z, e] Bs₀) :
    Hyp (EB π (Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e)) β L := by
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  obtain ⟨hgl, hq⟩ := frame_general_linear W (n + 1) r (n + 1) z π Bs₁ hR hB₁
  refine ⟨hgl, ⟨hnt, fun S hS => hirr S (lie_stabilizer W (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
  intro w v
  rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
  congr 1
  unfold cpol shf
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← hu j]
  ring

theorem labels2 {n r : ℕ} {T T' : ℝ} {u u' : ℕ → ℝ} (hOK : (⟨n + 1, r, T, T', u, u'⟩ : M.Par).OK)
    (ρ : M.Ty ⟨n + 1, r, T, T', u, u'⟩) (L L' : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hL' : ∀ j : Fin (n + 1), u' ((j : ℕ) + 1) - u 1 = (L' j : ℝ)) (lab : Fin n → ℤ)
    (hlab : ∀ j : Fin n, (lab j : ℝ) = M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) - u 1 + 1 / 2) :
    Box L lab ∧ Box L' lab ∧
      ∀ Y : ℂ, cpol (shf ((u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) lab) (Y + (((n + 1 : ℕ) : ℂ) - 2) / 2) =
        Formalism.FourierDecayAlt.M.xC ⟨n + 1, r, T, T', u, u'⟩ ρ Y := by
  have hmem : ∀ j : Fin n, (j : ℕ) + 1 ∈ Finset.Icc 1 ((⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1) := fun j =>
    Finset.mem_Icc.2 ⟨by omega, by show (j : ℕ) + 1 ≤ n + 1 - 1; omega⟩
  have hI := types_interlace _ hOK ρ
  have hI' : ∀ j : Fin n, M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u ((j : ℕ) + 1) ∧
      M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) + 1 / 2 ≤ u' ((j : ℕ) + 1) ∧ u ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) ∧
      u' ((j : ℕ) + 1 + 1) + 1 / 2 ≤ M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) := fun j => hI _ (hmem j)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have h1 := hL j.succ
    have h2 := hL j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hlab j
    constructor
    · have : (L j.succ : ℝ) < (lab j : ℝ) := by linarith
      exact_mod_cast this
    · have : (lab j : ℝ) ≤ (L j.castSucc : ℝ) := by linarith
      exact_mod_cast this
  · intro j
    have h1 := hL' j.succ
    have h2 := hL' j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    have h3 := hI' j
    have h4 := hlab j
    constructor
    · have : (L' j.succ : ℝ) < (lab j : ℝ) := by linarith
      exact_mod_cast this
    · have : (lab j : ℝ) ≤ (L' j.castSucc : ℝ) := by linarith
      exact_mod_cast this
  · intro Y
    unfold M.xC cpol
    rw [show (⟨n + 1, r, T, T', u, u'⟩ : M.Par).k - 1 = n from rfl, ProductIntervalFrames.prod_Icc_one]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h4 : (lab j : ℂ) = (M.rho ⟨n + 1, r, T, T', u, u'⟩ ρ ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) + 1 / 2 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) (hlab j)
      push_cast at this
      exact this
    simp only [shf]
    rw [h4]
    push_cast
    ring

section io

variable {k r : ℕ}

theorem section_embedding_mul_vec (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ)
    (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.io0 k r z z' μsec ζ *ᵥ v = NF.muZ k r μsec ζ *ᵥ (SSn.prWv k r z' v -
      herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ) := by
  set ν := SSn.nu0' k r z z' μsec ζ with hν
  let f : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    { toFun := fun v => NF.muZ k r μsec ζ *ᵥ (SSn.prWv k r z' v - herm (Hpk k r) (SSn.prWv k r z' v) ν • ν)
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add, TF.prWv_add, DU.hadd_l, add_smul]
        congr 1
        abel
      map_smul' := fun c x => by
        rw [TF.prWv_smul, DU.hsmul_l, RingHom.id_apply, ← Matrix.mulVec_smul, smul_sub, smul_smul] }
  have e : SSn.io0 k r z z' μsec ζ = LinearMap.toMatrix' f := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [e, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

end io

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsL : (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := B.hsVec
  map_add' := VLem.hsV_add
  map_smul' := VLem.hsV_smul

theorem hsVec_sum {ι : Type} (s : Finset ι) (f : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, f i) = ∑ i ∈ s, B.hsVec (f i) := map_sum (hsL (Wp := Wp) (Wq := Wq)) f s

theorem fib_sum_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (ζ : ℂ) (a : M.Ty P → ℂ)
    (X : M.Ty P → (Wq →L[ℂ] Wp)) (hX : ∀ ρ, X ρ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ) :
    ∑ ρ, a ρ • X ρ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
  intro p hp
  ext v

  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have h := congrArg (fun L : Wq →L[ℂ] Wp => L v) (hX ρ p hp)
  simp only [ContinuousLinearMap.comp_apply] at h
  simp only [ContinuousLinearMap.smul_apply, map_smul, h]

theorem wR_pos (P : M.Par) {ζ : ℂ} (hζ : P.TT < Complex.normSq ζ) : 0 < wR P.k P.TT ζ := by
  unfold wR
  exact Real.sqrt_pos.2 (pow_pos (sub_pos.2 hζ) _)

theorem trR_apply (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) q = rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
  have h := radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  show (MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) : MA.Qp P.r P.TT → ℂ) q = _
  rw [Gauge.toSm_of_mem P h]

theorem radBase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
  ⟨hpl.1.k_pos, hpl.2.1, hpl.2.2.1, by rw [hpl.2.2.2.1]; exact hpl.1.T_pos,
    by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos, Bs.sec, hpl.2.2.2.2.2.1.2.1, hpl.2.2.2.2.2.2.2.1,
    hpl.2.2.2.2.2.1.2.2.1, hpl.2.2.2.2.2.2.2.2.1⟩

theorem tz_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem qr_iff (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × ℂ) : x ∈ NF.QR P.k P.r Bs.z Bs.z' ↔ x ∈ MA.Qset P.r P.TT := by
  show (x.1 ∈ OmX P.r ∧ _) ↔ ((∀ l, x.1 l ≠ 0) ∧ _)
  rw [tz_eq P Bs hpl]
  rfl

theorem exists_tr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (F : M.Ty P → MA.SmQ P.r P.TT) :
    ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', trR P Bs e Φ = F ∧
      ∀ q : MA.Qp P.r P.TT, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
        ∑ ρ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * (F ρ : MA.Qp P.r P.TT → ℂ) q) • e ρ q.1.2 := by
  classical
  let g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := fun x =>
    ∑ ρ, ((((wR P.k P.TT x.2)⁻¹ : ℝ) : ℂ) * MA.ext (F ρ : MA.Qp P.r P.TT → ℂ) x) • e ρ x.2
  let φ := (NF.QR P.k P.r Bs.z Bs.z').indicator g
  have hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT := Set.ext (qr_iff P Bs hpl)
  have hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT) := by
    refine ContDiffOn.sum fun ρ _ => ?_
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((wR P.k P.TT x.2)⁻¹ : ℝ) : ℂ)) (MA.Qset P.r P.TT) := by
      refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
      refine ContDiffOn.inv ?_ fun x hx => (wR_pos P hx.2).ne'
      unfold wR
      refine (((Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_normSq.comp contDiff_snd).sub contDiff_const).pow _).contDiffOn.sqrt
        fun x hx => ?_
      have h2 : P.TT < Complex.normSq x.2 := hx.2
      exact (pow_pos (show (0 : ℝ) < Complex.normSq x.2 - P.TT by linarith) _).ne'
    have hF : ContDiffOn ℝ ∞ (MA.ext (F ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := (F ρ).2
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    exact (hw.mul hF).smul he'
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hQR]
      exact hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]
    · simp only [φ, Set.indicator_of_mem hx]
      have hx' : P.TT < Complex.normSq x.2 := ((qr_iff P Bs hpl x).1 hx).2
      exact fib_sum_smul P Bs x.2 _ _ fun ρ => (he.2 x.2 hx').1 ρ
    · simp [φ, Set.indicator_of_notMem hx]
  obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'
    (radBase P Bs hpl) φ hφ
  have hval : ∀ q : MA.Qp P.r P.TT, Φ q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
        ∑ ρ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * (F ρ : MA.Qp P.r P.TT → ℂ) q) • e ρ q.1.2 := by
    intro q
    have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := (qr_iff P Bs hpl q.1).2 q.2
    have h := congrFun hrad q.1
    simp only [NF.radR, Set.indicator_of_mem hq, φ] at h
    rw [h]
    simp only [g]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 2
    simp [MA.ext, q.2]
  refine ⟨⟨Φ, hΦ⟩, ?_, hval⟩
  funext ρ
  apply Subtype.ext
  funext q
  rw [trR_apply P Bs hpl hk e he]
  simp only [rawR]
  rw [hval q, hsVec_sum, inner_sum]
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  have horth := (he.2 q.1.2 hζ).2.1
  simp only [VLem.hsV_smul, inner_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hw : ((wR P.k P.TT q.1.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (wR_pos P hζ).ne'
  push_cast
  field_simp

theorem trR_inj (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) {Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'} (h : trR P Bs e Φ = trR P Bs e Ψ) :
    Φ = Ψ := by
  have hRB := radBase P Bs hpl
  apply Subtype.ext
  refine Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2 _ Ψ.2 ?_
  funext x
  by_cases hx : x ∈ NF.QR P.k P.r Bs.z Bs.z'
  · have hxQ : x ∈ MA.Qset P.r P.TT := (qr_iff P Bs hpl x).1 hx
    let q : MA.Qp P.r P.TT := ⟨x, hxQ⟩
    have hζ : P.TT < Complex.normSq x.2 := hxQ.2
    simp only [NF.radR, Set.indicator_of_mem hx]
    have hmΦ := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2).2.1 x hx
    have hmΨ := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Ψ.2).2.1 x hx
    simp only [NF.radR, Set.indicator_of_mem hx] at hmΦ hmΨ
    rw [(he.2 x.2 hζ).2.2 _ hmΦ, (he.2 x.2 hζ).2.2 _ hmΨ]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 1
    have h1 := trR_apply P Bs hpl hk e he Φ ρ q
    have h2 := trR_apply P Bs hpl hk e he Ψ ρ q
    rw [h] at h1
    rw [h1] at h2
    simp only [rawR, q] at h2
    have hw : ((wR P.k P.TT x.2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (wR_pos P hζ).ne'
    exact mul_left_cancel₀ hw h2
  · simp [NF.radR, Set.indicator_of_notMem hx]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

theorem transport_gen {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * r' + k + 1) → ℂ}
    (hz : D.castV hn (liftVec k i r' zs) = z) (hz' : D.castV hn (liftVec k i r' zs') = z')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)} {πs : Mx k r' → (Wp →L[ℂ] Wp)}
    {πs' : Mx k r' → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn (ιLev k i r' y))) (hπ' : ∀ y, πs' y = π' (D.castM hn (ιLev k i r' y)))
    (X₀ : ActualOps k n z z' π π') (L₀ : R.LevelData (Pr (RadSp k n z z' π π')) n)
    (st₀ : Fr.Start (Pr (RadSp k n z z' π π')))
    (X : ActualOps k r' zs zs' πs πs') (L : R.LevelData (Pr (RadSp k r' zs zs' πs πs')) r')
    (st : Fr.Start (Pr (RadSp k r' zs zs' πs πs')))
    (hL₀ : IsActualLevel X₀ L₀) (hL : IsActualLevel X L) (s : ℂ) (hst₀ : ∀ Y, st₀.QQ Y = s • X₀.QQ Y)
    (hst : ∀ Y, st.QQ Y = s • X.QQ Y) (hq : st₀.q = st.q) (hinv : st₀.inv = st.inv)
    (hSL₀ : Fr.IsStarLevel L₀) (hSL : Fr.IsStarLevel L) (hs₀ : Fr.IsLevelStart L₀ st₀) (hs : Fr.IsLevelStart L st)
    (c : Fin n → ℂ) (hc : c ∈ OmX n) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k r' zs zs' πs πs',
      (∀ Ψ c' g, (T Ψ : Fn k r' (Wq →L[ℂ] Wp)) c' g = (Ψ : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g))) ∧
      ∀ (w : List C.Letter), Fr.admitted st₀ (D.positionted w) → Fr.admitted st (D.positionted w) →
      ∀ (Ψ : Wd.Ix (Fin w.length) → RadSp k n z z' π π') (e : Wd.Ix (Fin w.length)) (c' : Fin r' → ℂ)
        (g : B.Mat k r'),
        (P5.act (Fr.ofWord L₀ st₀ (D.positionted w)).F Ψ e : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g)) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => T (Ψ e')) e : Fn k r' (Wq →L[ℂ] Wp)) c' g := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k i r' y) := funext fun y => by rw [hπ, P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k i r' y) := funext fun y => by rw [hπ', P.JCTx5.castM_rfl]
  have fr := fun (j : Fin 6) v => fn_rs hr' hc X₀ X j v
  have tr := fun Y (a b : Fin 2) v => t_rs hr' hc X₀ X Y a b v
  obtain ⟨-, -, -, -, -, -, h0ζ, h0ζi, h0ζb, h0ζbi, h0G, h0Gi, h0TT⟩ := hL₀
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hG, hGi, hTT⟩ := hL
  have G : Gen (rsL hr' hc zs zs' π π') L₀ L :=
    { ζ := by rw [h0ζ, hζ]; exact rel_mk (fr 0) (fr 2)
      ζi := by rw [h0ζi, hζi]; exact rel_mk (fr 1) (fr 3)
      ζb := by rw [h0ζb, hζb]; exact rel_mk (fr 2) (fr 0)
      ζbi := by rw [h0ζbi, hζbi]; exact rel_mk (fr 3) (fr 1)
      GG := by rw [h0G, hG]; exact rel_mk (fr 4) (fr 4)
      GGi := by rw [h0Gi, hGi]; exact rel_mk (fr 5) (fr 5)
      TT := by rw [h0TT, hTT, tz_lift, tz_lift] }
  have hQ : ∀ Y, MRel (rsL hr' hc zs zs' π π') (st₀.QQ Y) (st.QQ Y) := fun Y => by
    rw [hst₀, hst]
    exact mrel_smul s fun a b => rel_mk (fun v => tr Y a b v) (fun v => tr (star Y) b a v)
  refine ⟨rsL hr' hc zs zs' π π', fun Ψ c' g => by rw [P.JCTx5.castM_rfl]; rfl, fun w h₀ h Ψ e c' g => ?_⟩
  rw [P.JCTx5.castM_rfl]
  have key := act_frame G hQ hq hinv hSL₀ hSL hs₀ hs (D.positionted w) h₀ h Ψ e
  exact congrArg (fun v : RadSp k r' zs zs' _ _ => (v : Fn k r' (Wq →L[ℂ] Wp)) c' g) key

end Formalism.FourierDecayAlt.P.WordCorrespondence

theorem Formalism.FourierDecayAlt.P.frame_transport_to_last_level : Formalism.FourierDecayAlt.P.PBI.FrameTransport := by
  intro Wp Wq _ _ _ _ _ _ P p X₀ μ₀ L₀ st₀ X μ L st hD₀ hD c hc
  obtain ⟨T, hT, hact⟩ := Formalism.FourierDecayAlt.P.WordCorrespondence.transport_gen P.k P.r P.r (P.r - P.r) (by omega) (by omega)
    (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) (p.T.π_lev P.r le_rfl) (p.T.π'_lev P.r le_rfl)
    X₀ L₀ st₀ X L st hD₀.2.2.1 hD.2.2.1 (Formalism.FourierDecayAlt.M.sgn P p.l0) hD₀.2.2.2.1 hD.2.2.2.1
    (hD₀.2.2.2.2.1.trans hD.2.2.2.2.1.symm) (hD₀.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm)
    hD₀.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.1 hD₀.2.2.2.2.2.2.2 hD.2.2.2.2.2.2.2 c hc
  exact ⟨T, hT, fun w h₀ h Ψ e c' g _ _ => hact w h₀ h Ψ e c' g⟩
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

def GQBridge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → GQQ P Bs e →
    ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (X.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)

def GQKap : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    ∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)

def GQSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    (∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1),
      Gauge.GC.Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) ∧
      Gauge.GC.Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l))

def GQQSSFOfCut : Prop := GQBridge → GQKap → GQSS → GQQSSF

theorem gQQSSF_of_cut : GQQSSFOfCut := by
  intro hB hK hS Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg
  have hQ : ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b) := by
    intro Y a b
    rw [← hA.2.2.2.2 (Y : ℂ)]
    exact hB Wp Wq P Bs hk X d hA e he hg Y a b
  have hκ := hK Wp Wq P Bs hk X d hA e he hQ
  intro l hl Φ
  exact ⟨(hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).1 Φ, (hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).2 Φ⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end
