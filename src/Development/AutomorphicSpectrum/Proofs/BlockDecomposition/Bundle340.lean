module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle323
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle243
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle148
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle319
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem qO_extTensor_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (u : MirUin k (i + 1)) (hu : mirChar k ψ i u = 1) (v : τ.V ⊗[ℂ] σ.V),
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1) v) = qO τ σ ψ v := by
  intro k _ _ _ _ i t ψ τ σ u hu v
  let L : (τ.V ⊗[ℂ] σ.V) →ₗ[ℂ] (τ.V ⊗[ℂ] σ.V) :=
    extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ ((u : Mir k (i + 1)), 1)
  have hd : ((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (u : Mir k (i + 1)) : ℂˣ) : ℂ) = 1 := by
    have := GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_unip (k := k) (i + 1) (((t + 1 : ℕ) : ℝ) / 2) u
    simpa using congrArg Units.val this
  have ha : ∀ a : τ.V, (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (u : Mir k (i + 1)) a = τ.ρ (u : Mir k (i + 1)) a := by
    intro a
    refine (twist_apply τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) _ a).trans ?_
    rw [hd, one_smul]
  have hρ : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 = 1 := map_one _
  have hb : ∀ b : σ.V, (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 b = b := fun b => LinearMap.congr_fun hρ b
  have e : ∀ (a : τ.V) (b : σ.V), L (a ⊗ₜ[ℂ] b) = (τ.ρ (u : Mir k (i + 1)) a) ⊗ₜ[ℂ] b := fun a b =>
    (extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
      ((u : Mir k (i + 1)), 1) a b).trans (congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) (ha a) (hb b))
  have hq : ∀ a : τ.V, (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ (τ.ρ (u : Mir k (i + 1)) a) =
      (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ a := by
    intro a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    unfold twKer
    apply Submodule.subset_span
    exact ⟨u, a, by simp [hu]⟩
  have key : ∀ w : τ.V ⊗[ℂ] σ.V, qO τ σ ψ (L w) = qO τ σ ψ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b =>
      rw [e]
      exact congrArg (fun x => TensorProduct.tmul ℂ x b) (hq a)
  exact key v

end GlobalTheory.CompanionTheory.BZPhiPG
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Coinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cls {i : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (x : τ.V) : (phiN ψ τ).V :=
  (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ x

theorem phiN_cls {i : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (a : Mir k i) (x : τ.V) :
    (phiN ψ τ).ρ a (cls ψ τ x) = ((dpowM i (-1 / 2) a : ℂˣ) : ℂ) • cls ψ τ (τ.ρ (sEmb k i a) x) :=
  twist_apply _ _ _ _

theorem dpowM_half (i : ℕ) (a : Mir k i) :
    ((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpowM i (-1 / 2) a : ℂˣ) : ℂ) = 1 := by
  have h : dpow (k := k) (i + 1) (1 / 2 + -1 / 2) = dpow (i + 1) (1 / 2) * dpow (i + 1) (-1 / 2) :=
    GlobalTheory.CompanionTheory.LeibPhi.dpow_add k (i + 1) _ _
  have h0 : dpow (k := k) (i + 1) (1 / 2 + -1 / 2) = 1 := by
    rw [show ((1 / 2 + -1 / 2 : ℝ)) = 0 by norm_num]
    ext g
    simp [dpow, detChar, absPow]
  have h1 := congrArg (fun f => ((f (a : GL (Fin (i + 1)) k) : ℂˣ) : ℂ)) (h.symm.trans h0)
  simpa [dpowM] using h1

theorem dpow_step (i t : ℕ) (w : GL (Fin (t + 1)) k) :
    ((dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ) =
      ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ) * ((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ) := by
  have e : (-((i + 1 + 1 : ℕ) : ℝ) / 2) = -1 / 2 + (-((i + 1 : ℕ) : ℝ) / 2) := by
    push_cast; ring
  rw [e, GlobalTheory.CompanionTheory.LeibPhi.dpow_add]
  simp

theorem smul_tmul_scal {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : X) (q : Y)
    (c d e f f' g : ℂ) (h : c * d = e * (f * f' * g)) :
    (c • p) ⊗ₜ[ℂ] (d • q) = e • ((f • f' • p) ⊗ₜ[ℂ] (g • q)) := by
  rw [smul_smul f f' p]
  generalize f * f' = f at h
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
    smul_smul, smul_smul, smul_smul, mul_comm d c, h, mul_comm f g, mul_assoc]

theorem intertwine (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (a : Mir k i) (w : GL (Fin (t + 1)) k) (v : τ.V ⊗[ℂ] σ.V) :
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w) v) =
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w) (qO τ σ ψ v) := by
  let L : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V := (qO τ σ ψ) ∘ₗ
    (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w))
  let R : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      ((extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w)) ∘ₗ (qO τ σ ψ))
  have hLR : L = R := by
    refine TensorProduct.ext' fun x y => ?_
    have hl : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a) x =
        ((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) • τ.ρ (sEmb k i a) x :=
      (twist_apply _ _ _ _).trans (by
        rw [show sEmb k i a = (levi k (i + 1)).comp (Mir k i).subtype a from rfl, GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_levi]
        rfl)
    have hr : ∀ s : ℝ, (σ.tw s).ρ w y = ((dpow (t + 1) s w : ℂˣ) : ℂ) • σ.ρ w y := fun s => twist_apply _ _ _ _
    have hm : (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ a (cls ψ τ x) =
        ((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) • (phiN ψ τ).ρ a (cls ψ τ x) := twist_apply _ _ _ _
    have hc : ∀ (c : ℂ) (z : τ.V), cls ψ τ (c • z) = c • cls ψ τ z := fun c z => map_smul _ c z
    have eL : L (x ⊗ₜ[ℂ] y) = cls ψ τ ((mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a) x) ⊗ₜ[ℂ]
        (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ w y := rfl
    have eR : R (x ⊗ₜ[ℂ] y) = (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
        ((mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ a (cls ψ τ x) ⊗ₜ[ℂ] (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ w y) := rfl
    rw [eL, eR, hl, hm, phiN_cls, hr, hr, hc, dpow_step]
    have hh := dpowM_half i a
    refine smul_tmul_scal (X := (phiN ψ τ).V) (Y := σ.V) _ _ _ _ _ _ _ _ ?_
    linear_combination (-(((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ) * ((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ))) * hh
  exact LinearMap.congr_fun hLR v

end GlobalTheory.CompanionTheory.BZPhiPG.Coinv

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.QLevi

theorem tmul_scalars {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (x : A) (y : B)
    (c d d' e f : ℂ) (hd : d * d' = 1) :
    (c * (e * f)) • (x ⊗ₜ[ℂ] y) = (d * e) • ((c • d' • x) ⊗ₜ[ℂ] (f • y)) := by
  rw [smul_smul, TensorProduct.smul_tmul_smul, smul_smul]
  congr 1
  linear_combination (-(c * e * f)) * hd

theorem qC_sigX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (h : MirabolicParabolic k (i + 1) t) (η : HPG k (i + 1) (t + 1)) (hη : pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k))) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ η w) = ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 * dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • sigC τ σ h (qC τ σ w) := by
  intro k _ _ _ _ i t τ σ h η hη w
  generalize hgdef : (gpProj k (i + 1) t h).1 = g at *
  generalize hpdef : (gpProj k (i + 1) t h).2 = p at *
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a b =>
    have hL : sigX τ σ η (a ⊗ₜ[ℂ] b) =
        (((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (levi k (i + 1) g) : ℂˣ) : ℂ) • τ.ρ (levi k (i + 1) g) a) ⊗ₜ[ℂ]
        (((dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • σ.ρ (p : GL (Fin (t + 1)) k) b) := by
      show extTensor _ _ (pgProj k (i + 1) (t + 1) η) _ = _
      rw [hη]
      exact extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (levi k (i + 1) g, (p : GL (Fin (t + 1)) k)) a b
    have hR : sigC τ σ h (qC τ σ (a ⊗ₜ[ℂ] b)) =
        (((dpow (i + 1) (((t + 1 : ℕ) : ℝ) / 2) g : ℂˣ) : ℂ) • ((dpow (i + 1) (-1 / 2) g : ℂˣ) : ℂ) •
          ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (levi k (i + 1) g) a) : (psiN τ).V)) ⊗ₜ[ℂ]
        (((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • σ.ρ (p : GL (Fin (t + 1)) k) b) := by
      show extTensor _ _ (gpProj k (i + 1) t h) (qC τ σ (a ⊗ₜ[ℂ] b)) = _
      have hq : qC τ σ (a ⊗ₜ[ℂ] b) = ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a : (psiN τ).V) ⊗ₜ[ℂ] b := rfl
      have hgp : gpProj k (i + 1) t h = (g, p) := Prod.ext hgdef hpdef
      rw [hq, hgp]
      exact extTensor_tmul ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((i + 1 : ℕ) : ℝ) / 2)).ρ (g, p)
        ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a : (psiN τ).V) b
    have hg : dpow (i + 1) (1 / 2) g * dpow (i + 1) (-1 / 2) g = (1 : ℂˣ) := by
      have e := DFunLike.congr_fun (GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_add (k := k) (i + 1) (-1 / 2) (1 / 2)) g
      rw [MonoidHom.mul_apply] at e
      rw [← e, show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_zero]
      rfl
    have hp : dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) =
        dpow (t + 1) (-1 / 2) (p : GL (Fin (t + 1)) k) * dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) := by
      have e := DFunLike.congr_fun (GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_add (k := k) (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (-1 / 2))
        (p : GL (Fin (t + 1)) k)
      rw [MonoidHom.mul_apply] at e
      rw [← e]
      congr 2
      push_cast
      ring
    have hg' : ((dpow (i + 1) (1 / 2) g : ℂˣ) : ℂ) * ((dpow (i + 1) (-1 / 2) g : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, hg, Units.val_one]
    have hq : qC τ σ ((τ.ρ (levi k (i + 1) g) a) ⊗ₜ[ℂ] (σ.ρ (p : GL (Fin (t + 1)) k) b)) =
        ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (levi k (i + 1) g) a) : (psiN τ).V) ⊗ₜ[ℂ] (σ.ρ (p : GL (Fin (t + 1)) k) b) := rfl
    rw [hL, hR, GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpowM_levi, hp, TensorProduct.smul_tmul_smul, map_smul, hq]
    exact tmul_scalars _ _ _ _ _ _ _ hg'

end GlobalTheory.CompanionTheory.BZPhiPG.QLevi

end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg TensorProduct

namespace GlobalTheory.CompanionTheory.ACrisMod

variable {l : ℕ} [Fact l.Prime]


variable (l) in
abbrev Qt : Type := Ob l ⧸ Ideal.span {pFlat l ^ l}


variable (l) in
abbrev Nm : Type := ℕ →₀ Qt l

@[reducible] def modAcr (A : PAlg l) : Module (Ob l) (A.Acr 1) := Module.compHom _ (A.aTo1.comp A.s)

attribute [local instance] modAcr

theorem smul_acr (A : PAlg l) (c : Ob l) (y : A.Acr 1) : c • y = A.aTo1 (A.s c) * y := rfl

def mulDxi (A : PAlg l) (k : ℕ) : A.A →ₗ[Ob l] A.Acr 1 where
  toFun a := A.aTo1 a * A.dxi 1 (l * k)
  map_add' x y := by rw [map_add (f := _), add_mul]
  map_smul' c a := by
    rw [Algebra.smul_def, map_mul, RingHom.id_apply, smul_acr, mul_assoc]; rfl

theorem mulDxi_apply (A : PAlg l) (k : ℕ) (a : A.A) : mulDxi A k a = A.aTo1 a * A.dxi 1 (l * k) := rfl

theorem pow_smul_mulDxi (A : PAlg l) (k : ℕ) : pFlat l ^ l • mulDxi A k = 0 := by
  ext a
  have h := (GlobalTheory.T.expansion_surjective_additive_linear A).2.2.2 (l * k)
  rw [LinearMap.smul_apply, smul_acr, mulDxi_apply, LinearMap.zero_apply, map_pow, mul_left_comm]
  have e : A.aTo1 (A.s (pFlat l) ^ l) * A.dxi 1 (l * k) = 0 := h
  rw [e, mul_zero]

def tk (A : PAlg l) (k : ℕ) : Qt l →ₗ[Ob l] (A.A →ₗ[Ob l] A.Acr 1) :=
  (Ideal.span {pFlat l ^ l}).liftQ (LinearMap.toSpanSingleton (Ob l) _ (mulDxi A k)) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, mul_smul, pow_smul_mulDxi, smul_zero])

def tauL (A : PAlg l) : Nm l ⊗[Ob l] A.A →ₗ[Ob l] A.Acr 1 :=
  TensorProduct.lift (Finsupp.lsum ℕ (tk A))

theorem tauL_one (A : PAlg l) (k : ℕ) (a : A.A) :
    tauL A (Finsupp.single k 1 ⊗ₜ a) = A.aTo1 a * A.dxi 1 (l * k) := by
  have : (1 : Qt l) = Submodule.Quotient.mk (1 : Ob l) := rfl
  rw [tauL, TensorProduct.lift.tmul, Finsupp.lsum_single, this, tk, Submodule.liftQ_apply,
    LinearMap.toSpanSingleton_apply, one_smul, mulDxi_apply]

theorem smul_one_Qt (r : Ob l) : r • (1 : Qt l) = Submodule.Quotient.mk r := by
  change r • (Submodule.Quotient.mk (1 : Ob l) : Qt l) = _
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

theorem pow_smul_Qt (q : Qt l) : pFlat l ^ l • q = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def gen (A : PAlg l) (c : ℕ →₀ A.A) : Nm l ⊗[Ob l] A.A := c.sum fun k a => Finsupp.single k 1 ⊗ₜ a

theorem gen_zero (A : PAlg l) : gen A 0 = 0 := Finsupp.sum_zero_index

theorem gen_add (A : PAlg l) (c d : ℕ →₀ A.A) : gen A (c + d) = gen A c + gen A d :=
  Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _)

theorem gen_single (A : PAlg l) (k : ℕ) (a : A.A) : gen A (Finsupp.single k a) = Finsupp.single k 1 ⊗ₜ a :=
  Finsupp.sum_single_index (TensorProduct.tmul_zero _ _)

theorem tauL_gen (A : PAlg l) (c : ℕ →₀ A.A) : tauL A (gen A c) = A.expand c := by
  rw [gen, map_finsuppSum, expand]
  exact Finsupp.sum_congr fun k _ => tauL_one A k (c k)

theorem exists_gen (A : PAlg l) (x : Nm l ⊗[Ob l] A.A) : ∃ c, gen A c = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, gen_zero A⟩
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, gen_add A c d⟩
  | tmul n a =>
    induction n using Finsupp.induction_linear with
    | zero => exact ⟨0, by rw [gen_zero, TensorProduct.zero_tmul]⟩
    | add f g hf hg =>
      obtain ⟨c, hc⟩ := hf
      obtain ⟨d, hd⟩ := hg
      exact ⟨c + d, by rw [gen_add, hc, hd, TensorProduct.add_tmul]⟩
    | single k q =>
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨Finsupp.single k (r • a), ?_⟩
      rw [gen_single, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Finsupp.smul_single]
      congr 2
      exact smul_one_Qt r

theorem gen_eq_zero (A : PAlg l) (c : ℕ →₀ A.A) (h : ∀ k, c k ∈ Ideal.span {A.pi ^ l}) : gen A c = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h k)
  have e : c k = pFlat l ^ l • b := by
    rw [Algebra.smul_def, ← hb, mul_comm]
    congr 1
    exact (map_pow A.s _ _).symm
  have z : pFlat l ^ l • (Finsupp.single k 1 : Nm l) = 0 := by
    rw [Finsupp.smul_single, pow_smul_Qt, Finsupp.single_zero]
  change Finsupp.single k 1 ⊗ₜ[Ob l] (c k) = 0
  rw [e, ← TensorProduct.smul_tmul, z, TensorProduct.zero_tmul]

theorem tauL_bijective (A : PAlg l) : Function.Bijective (tauL A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_gen A x
    rw [tauL_gen] at hx
    exact gen_eq_zero A c ((GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem A c).1 hx)
  · obtain ⟨c, rfl⟩ := (GlobalTheory.T.expansion_surjective_additive_linear A).1 y
    exact ⟨gen A c, tauL_gen A c⟩

def tau (A : PAlg l) : Nm l ⊗[Ob l] A.A ≃+ A.Acr 1 :=
  { Equiv.ofBijective (tauL A) (tauL_bijective A) with map_add' := map_add (tauL A) }

theorem tau_apply (A : PAlg l) (x : Nm l ⊗[Ob l] A.A) : tau A x = tauL A x := rfl

theorem map_gen {A B : PAlg l} (f : A ⟶ B) (c : ℕ →₀ A.A) :
    ((D.toPf l ⋙ D.tensF l (Ob l) (Nm l)).map f).hom (gen A c) =
      gen B (c.mapRange (Hom.f f) (map_zero _)) := by
  rw [gen, map_finsuppSum, gen, Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]
  rfl

theorem pow_smul_Nm (x : Nm l) : pFlat l ^ l • x = 0 :=
  Finsupp.ext fun k => (Finsupp.smul_apply _ _ _).trans (pow_smul_Qt (x k))

theorem algebraMap_eq (A : PAlg l) (a : Ainf l) (y : A.Acr 1) :
    algebraMap (Ainf l) (A.Acr 1) a * y = a.coeff 0 • y := by
  rw [(GlobalTheory.T.functoriality_of_period_ring_maps A A (𝟙 A)).2.2.2.2.2 a]
  rfl

theorem tau_smul (A : PAlg l) (a : Ainf l) (x : Nm l ⊗[Ob l] A.A) :
    tau A (a.coeff 0 • x) = algebraMap (Ainf l) (A.Acr 1) a * tau A x :=
  ((tauL A).map_smul (a.coeff 0) x).trans (algebraMap_eq A a (tauL A x)).symm

theorem tau_map (A B : PAlg l) (f : A ⟶ B) (x : Nm l ⊗[Ob l] A.A) :
    tau B (((D.toPf l ⋙ D.tensF l (Ob l) (Nm l)).map f).hom x) = mapAcr f 1 (tau A x) := by
  obtain ⟨c, rfl⟩ := exists_gen A x
  rw [tau_apply, tau_apply, map_gen, tauL_gen, tauL_gen]
  exact ((GlobalTheory.T.functoriality_of_period_ring_maps A B f).2.1 c).symm

theorem acr1 (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RAcr1 l :=
  ⟨Nm l, inferInstance, inferInstance, l, tau, pow_smul_Nm, tau_smul, tau_map⟩

end GlobalTheory.CompanionTheory.ACrisMod
end
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

theorem _root_.GlobalTheory.T.polynomial_transfer : KH.PolyTf := by
  first | exact @GlobalTheory.CompanionTheory.PolyTfCon.polyTf | exact GlobalTheory.CompanionTheory.PolyTfCon.polyTf | (intros; apply GlobalTheory.CompanionTheory.PolyTfCon.polyTf <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cech_refinement_cohomology_bijective : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 𝒲 : Set X.Opens) (h : St Q₀ 𝒱 ≤ St Q₀ 𝒲) (hc : ∀ W ∈ 𝒲, W ≤ sSup 𝒱) (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := by
  first | exact @GlobalTheory.CompanionTheory.NlZar.zariski_descent | exact GlobalTheory.CompanionTheory.NlZar.zariski_descent | (intros; apply GlobalTheory.CompanionTheory.NlZar.zariski_descent <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds

theorem finite_and_finrank_le {k V : Type} [Field k] [AddCommGroup V] [Module k V] (g : ℕ)
    (h : ∀ x : Fin (g + 1) → V, ¬ LinearIndependent k x) :
    Module.Finite k V ∧ Module.finrank k V ≤ g := by
  classical
  let b := Module.Basis.ofVectorSpace k V
  have hemb : ∀ e : Fin (g + 1) ↪ Module.Basis.ofVectorSpaceIndex k V, False :=
    fun e => h _ (b.linearIndependent.comp e e.injective)
  haveI : Finite (Module.Basis.ofVectorSpaceIndex k V) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hemb (Fin.valEmbedding.trans (Infinite.natEmbedding _))
  haveI hfin : Module.Finite k V := Module.Finite.of_basis b
  refine ⟨hfin, ?_⟩
  rw [Module.finrank_eq_nat_card_basis b]
  by_contra hlt
  rw [not_le] at hlt
  exact hemb ((Fin.castLEEmb (Nat.succ_le_of_lt hlt)).trans (Finite.equivFin _).symm.toEmbedding)

theorem h1Le : DescentSt → LowSt → SteinSt → VanSt → HopfSt → HopfLeSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe := by
  intro hD hL hS hV hH hHL k _ A _ g hA hsm
  haveI : AlgebraicGeometry.IsProper A.hom := ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme.proper (self := hA)
  haveI : CompactSpace A.left := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨P, _, _, ⟨S⟩⟩ := GlobalTheory.CompanionTheory.Hodge.WedgeField.exists_finite_sys A.hom
  have hfield : IsField k := Field.toIsField k
  have hq : MainStatements.Hodge.AllQIso (MainStatements.Hodge.resSys A.hom S) := hD k A.left A.hom inferInstance P S
  obtain ⟨hb1, -, hst⟩ := hL k _ _ _ _ (MainStatements.Hodge.resSys A.hom S) hq
  have hstein : MainStatements.Hodge.Stein (MainStatements.Hodge.OSys A.hom S) := hst.mp (hS k A g hA hsm)
  have hexact := hV k A g hA hsm hfield P S
  have hhopf : MainStatements.Hodge.Hopf (MainStatements.Hodge.OSys A.hom S) True := by
    have h := hH k A g hA hsm P S
    rwa [eq_true hfield] at h
  have hno := hHL k P (MainStatements.Hodge.OSys A.hom S) g hfield hstein hexact hhopf
  refine finite_and_finrank_le g (fun x hx => ?_)
  exact hno (⇑(MainStatements.Hodge.resSys A.hom S).pull1 ∘ x)
    (hx.map' (MainStatements.Hodge.resSys A.hom S).pull1 (LinearMap.ker_eq_bot.mpr hb1.1))

end GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

theorem _root_.GlobalTheory.T.whittaker_rank_standard_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.WhitRankStd k := by
  first | exact @GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity | exact GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity | (intros; apply GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity <;> assumption)
end
