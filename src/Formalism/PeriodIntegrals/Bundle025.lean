module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.PeriodIntegrals.Bundle023
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace PI.AdBridgeSteps

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

def IsFormula (I : AutInst) (f : HAd I → I.GA) : Prop :=
  ∀ h, (∀ v, uMat ((f h).1 v) = ofHAInf I h v) ∧ I.fmat (f h).2 = ofHAFin I h

def RealK : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε k →
    (kᴴ * k = 1 ↔ ∀ a b, ε a ≠ ε b → k a b = 0)

def FinK : Prop :=
  ∀ (I : AutInst) (h : HAd I),
    (∀ x, x ∈ I.Lf ↔ ofHAFin I h *ᵥ x ∈ I.Lf) ↔
      ∀ v : HeightOneSpectrum (𝓞 I.F),
        Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) ∈
          Formalism.L2.SG.Sub.Kloc v (I.L : Set (Fin I.n → I.E))

end PI.AdBridgeSteps
end
end

section

noncomputable section

open NumberField Formalism.MainNotions.S PI.ScRefExists
open scoped TensorProduct
open Matrix

namespace PI.ScXuExists

def OneOff (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (x : I.Gf) : Prop :=
  ∀ m : ℕ, Nat.Coprime m g → ∀ y ∈ I.Lf, InAt I m m ((I.fmat x - 1) *ᵥ y)

def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), 1 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) →
    (∃ t : ℕ, t ≡ 1 [MOD g] ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E)) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    InAt I g 1 (incl I z) →
    ∃ x : I.Gf, (∀ a, I.fmat x *ᵥ incl I (e a) = incl I (e a) ∧ I.fmat x *ᵥ incl I (f a) = incl I (f a)) ∧
      InAt I g g (I.fmat x⁻¹ *ᵥ incl I z - Rf.z0) ∧ OneOff I g x ∧ x ∈ I.Kset

end PI.ScXuExists
end
end

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.InHHClassFin

section Defs

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

abbrev VA : Type := Fin I.n → I.E ⊗[I.F] Af I.F

def incl (x : Fin I.n → I.E) : VA I := fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)

def HinfS (S : Set (Fin I.n → I.E)) : Subgroup I.Ginf where
  carrier := {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}
  one_mem' := by
    intro v x _
    simp [uMat]
  mul_mem' := by
    intro s t hs ht v x hx
    have e1 : uMat ((s * t) v) = uMat (s v) * uMat (t v) := by simp [uMat]
    rw [e1, ← Matrix.mulVec_mulVec, ht v x hx, hs v x hx]
  inv_mem' := by
    intro s hs v x hx
    have e1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by simp [uMat]
    calc uMat (s⁻¹ v) *ᵥ rv I v x = uMat (s⁻¹ v) *ᵥ (uMat (s v) *ᵥ rv I v x) := by rw [hs v x hx]
      _ = rv I v x := by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]

def HfinS (S : Set (Fin I.n → I.E)) : Subgroup I.Gf where
  carrier := {x | ∀ y ∈ S, I.fmat x *ᵥ incl I y = incl I y}
  one_mem' := by
    intro y _
    simp [AutInst.fmat]
  mul_mem' := by
    intro a b ha hb y hy
    have e1 : I.fmat (a * b) = I.fmat a * I.fmat b := by simp [AutInst.fmat]
    rw [e1, ← Matrix.mulVec_mulVec, hb y hy, ha y hy]
  inv_mem' := by
    intro a ha y hy
    have e1 : I.fmat a⁻¹ * I.fmat a = 1 := by simp [AutInst.fmat]
    calc I.fmat a⁻¹ *ᵥ incl I y = I.fmat a⁻¹ *ᵥ (I.fmat a *ᵥ incl I y) := by rw [ha y hy]
      _ = incl I y := by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]

def GamS (S : Set (Fin I.n → I.E)) : Subgroup I.GA :=
  Formalism.MainNotions.LeviCoordinates.rr_GF I ⊓ (HinfS I S).prod (HfinS I S)

def iotaFS (S : Set (Fin I.n → I.E)) : GamS I S →* HfinS I S :=
  MonoidHom.codRestrict ((MonoidHom.snd _ _).comp (GamS I S).subtype) (HfinS I S)
    (fun γ => (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).2)

end Defs

def DefiniteCompl (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)) : Prop :=
  ∀ ι : I.F →+* ℝ,
    (∀ x : Fin I.n → I.E, x ≠ 0 → (∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s x = 0) →
      ∃ a : I.F, algebraMap I.F I.E a = Formalism.UG.hform (starRingEnd I.E) I.J x x ∧ 0 < ι a) ∨
    (∀ x : Fin I.n → I.E, x ≠ 0 → (∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s x = 0) →
      ∃ a : I.F, algebraMap I.F I.E a = Formalism.UG.hform (starRingEnd I.E) I.J x x ∧ ι a < 0)

def StabClassFinite : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (S : Set (Fin I.n → I.E)), DefiniteCompl I S →
    ∀ (K : Subgroup (HfinS I S)) (g : ℕ) (x : I.Gf), 1 ≤ g →
      (∀ h : HfinS I S, x⁻¹ * (h : I.Gf) * x ∈ I.Kg g → h ∈ K) →
      Finite (Formalism.UG.ClassSet (iotaFS I S).range K)

end PI.InHHClassFin
end
end
