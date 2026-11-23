module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.MemSpanOfSharpG
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006

@[expose] public section

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def uV (g : SplitG M.L) (l : Fin (r + 1) → M.R) : Ix r → F :=
  Sum.elim (fun a => ph1 g (l a)) (fun a => ph2 g (l a))

def qM (r : ℕ) (x : F) : Matrix (Ix r) (Ix r) F := Matrix.fromBlocks 1 1 0 (x • 1)

theorem pM_mul_qM (x : F) (hx : x ≠ 0) : pM r x⁻¹ * qM r x = 1 := by
  rw [pM, qM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> simp [smul_smul, mul_inv_cancel₀ hx]

theorem firstProj_iotaOne_cases (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph1 g (iota1 hs l i : E) = match i with
      | Sum.inl a => ph1 g (l a)
      | Sum.inr a => (ph2 g (l a) - ph1 g (l a)) / (g.q : F) := by
  rcases i with a | a <;> simp [iota1, firstProj_apply, secondProj_apply]

theorem secondProj_iotaOne_eq_zero (hs : M.split = some g) (l : Fin (r + 1) → M.R) (i : Ix r) :
    ph2 g (iota1 hs l i : E) = 0 := by
  rcases i with a | a <;> simp [iota1, secondProj_apply]

theorem vecMul_qM (hs : M.split = some g) (l : Fin (r + 1) → M.R) :
    Matrix.vecMul (fun i => ph1 g (iota1 hs l i : E)) (qM r (g.q : F)) = uV g l := by
  have hq := q_ne g
  funext k
  rcases k with a | a
  · simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, qM, firstProj_iotaOne_cases, uV, Matrix.one_apply]
  · simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, qM, firstProj_iotaOne_cases, uV, Matrix.one_apply]
    field_simp
    ring

theorem splitForm_iota_secondProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (l w : Fin (r + 1) → M.R) :
    ph2 g (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') (iota1 hs l) (iota2 hs w)) = 0 := by
  unfold formG

  simp [map_sum, map_mul, secondProj_iotaOne_eq_zero]

theorem splitForm_iota_firstProj (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hG : IsUnit (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T')).det)
    (l w : Fin (r + 1) → M.R) :
    ph1 g (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') (iota1 hs l) (iota2 hs w)) =
      dotProduct (uV g l) (Matrix.mulVec (gHat g Zh T T')⁻¹ (uV g w)) := by
  set G := gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')
  have hq := q_ne g
  have hcw : ∀ j, ph1 g ((M.L.cj : E →+* E) (iota2 hs w j : E)) = ph1 g (iota1 hs w j : E) := by
    intro j
    show ph1 g (M.L.cj (M.L.cj (iota1 hs w j : E))) = _
    rw [M.L.cj_cj]
  have h1 : ph1 g (formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T)
      (algebraMap F E T') (iota1 hs l) (iota2 hs w)) =
      dotProduct (fun i => ph1 g (iota1 hs l i : E)) (Matrix.mulVec (G.map (ph1 g))⁻¹ fun j => ph1 g (iota1 hs w j : E)) := by
    rw [← map_inv_of (ph1 g) G hG]
    unfold formG

    simp only [map_sum, map_mul, hcw, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hP : (pM r (g.q : F)⁻¹)⁻¹ = qM r (g.q : F) := Matrix.inv_eq_right_inv (pM_mul_qM _ hq)
  have hPt : ((pM r (g.q : F)⁻¹).transpose)⁻¹ = (qM r (g.q : F)).transpose := by
    rw [← Matrix.transpose_nonsing_inv, hP]
  rw [h1, map_gramG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hP, hPt, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, vecMul_qM, vecMul_qM]

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def cjT (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) O :=
  fun a b => ⟨cj (Z b a), hO _ (Z b a).2⟩

def bRaw (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y y' : Fin (r + 1) → O) : E :=
  ∑ j, cj (y' j) * ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E))) j

def lamS (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y' : Fin (r + 1) → O) : E :=
  lamStarC cj (Z.map O.subtype) (fun b => (y' b : E))

def PairSet (hO : ∀ x ∈ O, cj x ∈ O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O) : Type :=
  {p : (MbMod Z₁ ≃ₗ[O] MbMod Z₂) × (MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂)) //
    (p.1 (bCls Z₁) = bCls Z₂ ∧ p.1 (eCl Z₁) = eCl Z₂) ∧
    (∀ y' y₂' : Fin (r + 1) → O, p.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      lamS O cj Z₂ y₂' = lamS O cj Z₁ y') ∧
    (∀ y y' y₂ y₂' : Fin (r + 1) → O, p.1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂ →
      p.2 (Submodule.Quotient.mk y') = Submodule.Quotient.mk y₂' →
      bRaw O cj Z₂ y₂ y₂' - bRaw O cj Z₁ y y' ∈ O)}

def projP (hO : ∀ x ∈ O, cj x ∈ O) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (p : PairSet O cj hO Z₁ Z₂) : IsoMbe Z₁ Z₂ :=
  (⟨p.1.1, p.2.1⟩ : {γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂ // γ (bCls Z₁) = bCls Z₂ ∧ γ (eCl Z₁) = eCl Z₂})

def StepPair : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (T T' : E), T ∈ O → T' ∈ O → cj T = T → cj T' = T' →
    ∀ (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    IsUnit (gramC cj (Z₁.map O.subtype) T T').det → IsUnit (gramC cj (Z₂.map O.subtype) T T').det →
    Nat.card (ThetaC O cj (Z₁.map O.subtype) (Z₂.map O.subtype) T T') =
      Nat.card (PairSet O cj hO Z₁ Z₂)

def StepInj : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    Function.Injective (projP O cj hO Z₁ Z₂)

def StepAdj : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det = 0 →
    Function.Surjective (projP O cj hO Z₁ Z₂)

theorem unramifiedIsoCount_of_pair_inj_adj (h1 : StepPair) (hi : StepInj) (h2 : StepAdj) : UnramifiedIsoCountZero := by
  intro E _ O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hd₁ hd₂ hg₁ hg₂
  rw [h1 E O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hd₁ hd₂ hg₁ hg₂]
  exact Nat.card_congr (Equiv.ofBijective _
    ⟨hi E O cj hcj hO r Z₁ Z₂ hu₁ hu₂, h2 E O cj hcj hO r Z₁ Z₂ hu₁ hu₂ hd₁ hd₂⟩)

theorem locCnt0L_of_pair (h1 : StepPair) (hi : StepInj) (h2 : StepAdj) :
    Formalism.L2.SG.LocalCountModules.LocCnt0L.LocCnt0L :=
  Formalism.L2.SG.LocalCountModules.LocCnt0LWork.locCnt0L_of_alg (unramifiedIsoCount_of_pair_inj_adj h1 hi h2)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end
