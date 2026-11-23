module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle026
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle022
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle028
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle025
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle020
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle027

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {D : D7} {n : ℕ}

theorem pLaw (hN : LawN) (hMul : LocMul) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}
    (hL : IsLocFact ω τ fr ι L) {e : ℤ}
    (hLev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (Z : Matrix (Fin n) (Fin n) ℂ)
    (hG : IsSch (gZf ε (tLoc l τ) (cLoc l τ) Z)) :
    L q (gZf ε (tLoc l τ) (cLoc l τ) Z) = fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) q Z *
      gZf ε (tLoc l τ) (cLoc l τ) (actZ q Z) u := by
  obtain ⟨hA, hDd, hb⟩ := siegelP_data q hq
  have hAh : IsUnit ((mR q).toBlocks₁₁ᴴ).det := by rw [Matrix.det_conjTranspose]; exact hA.star
  set q1 := mkGR (nU ((mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ)) (by rw [det_nU]; exact one_ne_zero) (inG_nU hb)
  set q2 := mkGR (mM (mR q).toBlocks₁₁) (det_mM hA) (inG_mM hA)
  have hq12 : q = q1 * q2 := by
    apply GR_ext
    rw [mR_mul, mR_mkGR, mR_mkGR]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q), hq, hDd]
    unfold nU mM
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAh]
  have h2 := hLev q2 (mR q).toBlocks₁₁ hA (mR_mkGR _ _ _) _ hG
  have hs2 : IsSch (levF e (mR q).toBlocks₁₁ (gZf ε (tLoc l τ) (cLoc l τ) Z)) := by rw [← h2]; exact hL.1 q2 _ hG
  have h1 := hN D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL q1 _ hb (mR_mkGR _ _ _) _ hs2
  have hm := hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL q1 q2 _ hG
  rw [hq12, hm, h2, h1, ← hq12]
  funext u
  simp only [levF, gZf_mul]
  rw [siegelP_actZ q hq Z, siegelP_jF q hq, cnt_add, ← chN_mul_gZf ε (abs_tLoc l τ) _ _ hb u]
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

def qF (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) : ℂ :=
  -(Complex.I * c * ∑ a ∈ S, star (u a) ⬝ᵥ (Zᵀ *ᵥ v a) - Complex.I * c * ∑ a ∈ S', star (u a) ⬝ᵥ (Z'ᵀ *ᵥ v a))

def qL (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (qF S S' c Z Z')
    (fun u₁ u₂ v => by
      simp only [qF, Pi.add_apply, star_add, add_dotProduct, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct, Complex.real_smul, ← Finset.mul_sum]
      ring)
    (fun u v₁ v₂ => by
      simp only [qF, Pi.add_apply, Matrix.mulVec_add, dotProduct_add, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul, ← Finset.mul_sum]
      ring)

def qB (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ qL S S' c Z Z')

theorem qB_apply (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) :
    qB S S' c Z Z' u v = qF S S' c Z Z' u v := rfl

theorem re_I_mul (c : ℝ) (z : ℂ) : (Complex.I * c * z).re = -(c * z.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem quad_nonneg {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) (y : Fin n → ℂ) : 0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.nonneg_iff.mp (hP.posSemidef.dotProduct_mulVec_nonneg y)).1

theorem quad_pos {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) {y : Fin n → ℂ} (hy : y ≠ 0) :
    0 < (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.pos_iff.mp (hP.dotProduct_mulVec_pos hy)).1

end PositivityTheory.Rg.Sw.Glob.GCSchH
end
end
