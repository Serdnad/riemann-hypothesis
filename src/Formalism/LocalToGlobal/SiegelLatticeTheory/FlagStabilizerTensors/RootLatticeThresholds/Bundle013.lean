module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.StatementMA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Eqv Formalism.IndefR
open scoped TensorProduct

namespace Formalism.L2.SG.EvalTIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def uM' (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) (v : InfinitePlace D.host.F) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ := uMat (x.1 v)

def Pi (v : InfinitePlace D.host.F) : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
  (Formalism.IndefR.RationalEmbedding.inst D).P v

theorem P_isUnit_det' (v : InfinitePlace D.host.F) : IsUnit (Pi (D := D) v).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp ((Formalism.IndefR.RationalEmbedding.inst D).P_unit v)

theorem thetaV_eq_psiT_i (ρ : D.what₂.Tau) :
    Formalism.L2.SG.AdBridge.thetaV (Formalism.IndefR.RationalEmbedding.inst D) (Formalism.L2.Host.tauPl D ρ) = psiT D ρ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x =>
    have h1 := Formalism.L2.SG.AdBridge.thetaV_tmul (Formalism.IndefR.RationalEmbedding.inst D) (Formalism.L2.Host.tauPl D ρ) a x
    have h2 : ∀ (a : AF D.host.F) (x : D.host.E),
        psiT D ρ (a ⊗ₜ[D.host.F] x) = gW D (plW D ρ) (fstA D.host.F a) * tauE D ρ x := fun a x => by
      show thetaC D ρ ((fstA D.host.F a) ⊗ₜ[D.host.F] x) = _
      rw [thetaC_tmul]
    refine h1.trans (Eq.trans ?_ (h2 a x).symm)
    have h3 : (Formalism.IndefR.RationalEmbedding.inst D).φ (Formalism.L2.Host.tauPl D ρ) x = tauE D ρ x := by
      show Formalism.MainNotions.S.embS D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)) x = _
      rw [Equiv.symm_apply_apply]
      rfl
    exact congrArg₂ (· * ·) rfl h3
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem infMat_brg_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig (D.sp.Y 0).gram (thetaC D ρ) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) =
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
  have hb : uM' x (Formalism.L2.Host.tauPl D ρ) = (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ *
      (matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (psiT D ρ) *
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) := by
    have h := ((Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) x).1 (Formalism.L2.Host.tauPl D ρ)
    have h2 := thetaV_eq_psiT_i ρ
    unfold Formalism.L2.SG.AdBridge.ofHAInf at h
    rw [h2] at h
    exact h
  rw [hb, infMat_thetaC]
  have hu := P_isUnit_det' (Formalism.L2.Host.tauPl D ρ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem mat_eq_one_of_thetaC_i {M : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ ρ, M.map (thetaC D ρ) = 1) : M = 1 := by
  ext i j
  have hz : M i j - (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j = 0 := by
    apply thetaC_inj
    intro ρ
    have := congrFun (congrFun (h ρ) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact sub_eq_zero.mp hz

theorem uM_one_iff_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : x.1 = 1 ↔ ∀ v, uM' x v = 1 := by
  constructor
  · intro h v
    show uMat (x.1 v) = 1
    rw [h]
    rfl
  · intro h
    funext v
    exact Subtype.ext (Units.ext (h v))

theorem brg_mem_GfC_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GfC (D.sp.Y 0) ↔ x.1 = 1 := by
  have key : (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GfC (D.sp.Y 0) ↔ (matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (infPart D) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun u : GL (Fin (D.sp.Y 0).rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1) (MonoidHom.mem_ker.mp hh)
    · intro hh
      exact MonoidHom.mem_ker.mpr (Units.ext hh)
  rw [key, uM_one_iff_i]
  have hc : ∀ ρ, ((matA D (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x)).map (infPart D)).map (thetaC D ρ) =
      Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
    intro ρ
    rw [← infMat_brg_i, infMat_thetaC, Matrix.map_map]
    rfl
  constructor
  · intro h1 v
    obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
    have hu := P_isUnit_det' (Formalism.L2.Host.tauPl D ρ)
    have e' : Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ = 1 := by
      rw [← hc ρ, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc uM' x (Formalism.L2.Host.tauPl D ρ)
        = (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹ * (Pi (D := D) (Formalism.L2.Host.tauPl D ρ) * uM' x (Formalism.L2.Host.tauPl D ρ) *
          (Pi (D := D) (Formalism.L2.Host.tauPl D ρ))⁻¹) * Pi (D := D) (Formalism.L2.Host.tauPl D ρ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      _ = 1 := by rw [e', Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  · intro h1
    apply mat_eq_one_of_thetaC_i
    intro ρ
    rw [hc ρ, h1, Matrix.mul_one, Matrix.mul_nonsing_inv _ (P_isUnit_det' _)]

theorem tauF_eq_i : Formalism.L2.SG.AdBridge.tauF (Formalism.IndefR.RationalEmbedding.inst D) =
    (Lev.swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x => exact (Formalism.L2.SG.AdBridge.tauF_tmul (Formalism.IndefR.RationalEmbedding.inst D) a x).trans rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem finE_brg_i (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) : Lev.finE (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) = (x.2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) := by
  apply Units.ext
  have hb := ((Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) x).2
  unfold Formalism.L2.SG.AdBridge.ofHAFin at hb
  rw [tauF_eq_i] at hb
  exact hb.symm

theorem iota_symm_mem_GinfC (x : (Formalism.IndefR.RationalEmbedding.inst D).GA) :
    (Formalism.IndefR.RationalEmbedding.iota D).symm x ∈ GinfC (D.sp.Y 0) ↔ x.2 = 1 := by
  show finHom (D.sp.Y 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm x) = 1 ↔ _
  rw [Formalism.IndefR.Eqv.finHom_eq_one_iff, finE_brg_i]
  constructor
  · intro e
    exact Subtype.ext e
  · intro e
    rw [e]
    rfl

end Formalism.L2.SG.EvalTIota

end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def instCMT2 (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

attribute [local instance] instCMT2

section hermitianSpaces

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuilt_of_builtPlace {Cb Cc : ℝ} {S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq}
    {p : ∀ v, Formalism.FourierDecayAlt.KB.Pl (Formalism.FourierDecayAlt.D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (h : Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc S p f χ A₀) :
    Formalism.FourierDecayAlt.D.IsBuilt S (Formalism.FourierDecayAlt.KB.plT S p) f χ (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p)
      (Formalism.FourierDecayAlt.KB.plTop S p) A₀ := by
  obtain ⟨⟨-, -, -, hχ, -, -, -, -, -, -, -, -, -, -, -, hv⟩, hE, -⟩ := h
  exact ⟨hχ, fun v => ⟨(hv v).2.2.1, (p v).hT, (p v).hF, (p v).hP, (hv v).2.2.2.2, hE v⟩⟩

end hermitianSpaces

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def CarrierDataBound (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn CA : ℝ)
    (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ) (C₆ Cc Cb : ℝ) : Prop :=
  ∃ (Wp Wq : InfinitePlace D.host.E → Type) (_ : ∀ x, NormedAddCommGroup (Wp x)) (_ : ∀ x, InnerProductSpace ℂ (Wp x))
    (_ : ∀ x, NormedAddCommGroup (Wq x)) (_ : ∀ x, InnerProductSpace ℂ (Wq x)) (_ : ∀ x, FiniteDimensional ℂ (Wp x))
    (_ : ∀ x, FiniteDimensional ℂ (Wq x))
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (p : ∀ v, Formalism.FourierDecayAlt.KB.Pl (Formalism.FourierDecayAlt.D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) (χ : ℝ → ℝ)
    (A₀ : ℝ) (c : Formalism.FourierDecayAlt.LE.Cut)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v),
    S.CA = CA ∧ S.G = G0 ∧ S.de = de ∧ S.de' = de' ∧ S.l = l ∧ Formalism.L2.SG.DataInst.Compat S u u' ∧
    Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc S p f χ A₀ ∧ Formalism.FourierDecayAlt.JCT.SliceBudget S A₀ ∧ c.χ = χ ∧
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) ∧
    Formalism.FourierDecayAlt.JCT.VtTensor S (Formalism.FourierDecayAlt.KB.plT S p) f (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p)
      (VtPt X u u' sc i0 i0' FdN FdN' νq) ∧
    BuiltFromX X S u u' (Formalism.FourierDecayAlt.KB.plT S p) f τ Q Qi eP eQ ∧
    BaseFromX X S u u' i0 i0' τ Q Qi (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p) ∧
    TopTie X S u u' sc i0 i0' FdN FdN' νq τ ∧
    VJoint X S u u' sc i0 i0' νq (Formalism.FourierDecayAlt.KB.plT S p) f (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p) τ eP eQ ∧
    ∀ (L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
        (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r)
      (j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
        Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT)
      (lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ)
      (Cm σ : Fin S.f → ℝ),
      (∀ v, Formalism.FourierDecayAlt.JC.IsModelPlace S (Formalism.FourierDecayAlt.KB.plT S p) f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) →
      (∏ v, Formalism.FourierDecayAlt.JCT.jvModel S j Cm v) = jn

end Formalism.L2.SG.Pf.CarrierT
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def instCM (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

attribute [local instance] instCM

structure Parts {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Type 1 where
  Wp : InfinitePlace D.host.E → Type
  Wq : InfinitePlace D.host.E → Type
  [pN : ∀ x, NormedAddCommGroup (Wp x)]
  [pI : ∀ x, InnerProductSpace ℂ (Wp x)]
  [qN : ∀ x, NormedAddCommGroup (Wq x)]
  [qI : ∀ x, InnerProductSpace ℂ (Wq x)]
  [pF : ∀ x, FiniteDimensional ℂ (Wp x)]
  [qF : ∀ x, FiniteDimensional ℂ (Wq x)]
  S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq
  T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j))
  f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))
  χ : ℝ → ℝ
  ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ
  m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r
  top : ∀ j : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) → List Formalism.FourierDecayAlt.C.Letter →
    Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ
  A₀ : ℝ
  τ : Fin S.f ≃ InfinitePlace X.B.I.F
  Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ
  Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ
  eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v
  eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v
  L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r
  j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
    Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT
  lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ
  c : Formalism.FourierDecayAlt.LE.Cut
  Cm : Fin S.f → ℝ
  σ : Fin S.f → ℝ
  Lw : ℕ → Fin S.f → ℝ
  Ll : ℕ → ℕ → Fin S.f → ℝ
  Ll' : ℕ → ℕ → Fin S.f → ℝ

attribute [instance] Parts.pN Parts.pI Parts.qN Parts.qI Parts.pF Parts.qF

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.Pins (P : Parts X u u') (CA : ℝ) (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ)
    (l : ℕ) : Prop :=
  P.S.CA = CA ∧ P.S.G = G0 ∧ P.S.de = de ∧ P.S.de' = de' ∧ P.S.l = l ∧ Formalism.L2.SG.DataInst.Compat P.S u u'

def Parts.Built (P : Parts X u u') : Prop := Formalism.FourierDecayAlt.D.IsBuilt P.S P.T P.f P.χ P.ν' P.m₀ P.top P.A₀

def Parts.FromX (P : Parts X u u') : Prop := BuiltFromX X P.S u u' P.T P.f P.τ P.Q P.Qi P.eP P.eQ

def Parts.Base (P : Parts X u u') (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  BaseFromX X P.S u u' i0 i0' P.τ P.Q P.Qi P.ν' P.m₀

end Formalism.L2.SG.Pf.Carrier
end
end
