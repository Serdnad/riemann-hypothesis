module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle185
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLayerCoordsToBlocks
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle180
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFineSubgroupMovesAtLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentLieLatticeDomainVolumeBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle181
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlagConj

section Linear

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem exists_unitary_of_gram {κ : Type} [Fintype κ] [DecidableEq κ] (hκ : Fintype.card κ = n)
    (J : Matrix (Fin n) (Fin n) E) (B B' : Matrix (Fin n) κ E) (G G' : Matrix κ κ E) (hG : G' * G = 1)
    (hB : Bᴴ * J * B = G) (hB' : B'ᴴ * J * B' = G) :
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * γ = J ∧ (γ : Matrix (Fin n) (Fin n) E) * B = B' := by
  have e : κ ≃ Fin n := Fintype.equivFinOfCardEq hκ
  have h1 : G' * Bᴴ * J * B = 1 := by rw [← hG, ← hB]; simp only [Matrix.mul_assoc]
  have h2 : G' * B'ᴴ * J * B' = 1 := by rw [← hG, ← hB']; simp only [Matrix.mul_assoc]
  generalize G' * Bᴴ * J = C at h1
  generalize G' * B'ᴴ * J = C' at h2
  have h3 : B * C = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  have h4 : B' * C' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h2
  refine ⟨⟨B' * C, B * C', ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h1, Matrix.one_mul, h4]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C', h2, Matrix.one_mul, h3]
  · change (B' * C)ᴴ * J * (B' * C) = J
    calc (B' * C)ᴴ * J * (B' * C) = Cᴴ * (B'ᴴ * J * B') * C := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B * C)ᴴ * J * (B * C) := by
          rw [hB', ← hB]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [h3, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · change B' * C * B = B'
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]

def cat {a : ℕ} {j : Fin a → ℕ} (T : ∀ i, Matrix (Fin n) (Fin (j i)) E) :
    Matrix (Fin n) (Σ i, Fin (j i)) E := Matrix.of fun r p => T p.1 r p.2

theorem gram_adapted {a m : ℕ} {j : Fin a → ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J)
    (J₀ : Matrix (Fin m) (Fin m) E) (T T' : ∀ i, Matrix (Fin n) (Fin (j i)) E) (T₀ : Matrix (Fin n) (Fin m) E)
    (h1 : ∀ i k, (T i)ᴴ * J * T k = 0 ∧ (T' i)ᴴ * J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * J * T' k = 0))
    (h2 : ∀ i, (T i)ᴴ * J * T' i = 1 ∧ (T i)ᴴ * J * T₀ = 0 ∧ (T' i)ᴴ * J * T₀ = 0)
    (h3 : T₀ᴴ * J * T₀ = J₀) :
    (fromCols (fromCols (cat T) (cat T')) T₀)ᴴ * J * fromCols (fromCols (cat T) (cat T')) T₀ =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 J₀ := by
  have sw : ∀ {α β : Type} (A : Matrix (Fin n) α E) (B : Matrix (Fin n) β E),
      Bᴴ * J * A = (Aᴴ * J * B)ᴴ := by
    intro α β A B
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  have a11 : (cat T)ᴴ * J * cat T = 0 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    exact congrFun (congrFun (h1 i k).1 s) t
  have a22 : (cat T')ᴴ * J * cat T' = 0 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    exact congrFun (congrFun (h1 i k).2.1 s) t
  have a12 : (cat T)ᴴ * J * cat T' = 1 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    by_cases h : i = k
    · subst h
      refine (congrFun (congrFun (h2 i).1 s) t).trans ?_
      simp [Matrix.one_apply]
    · refine (congrFun (congrFun ((h1 i k).2.2 h) s) t).trans ?_
      simp [Matrix.one_apply, h]
  have a13 : (cat T)ᴴ * J * T₀ = 0 := by
    ext ⟨i, s⟩ t
    exact congrFun (congrFun (h2 i).2.1 s) t
  have a23 : (cat T')ᴴ * J * T₀ = 0 := by
    ext ⟨i, s⟩ t
    exact congrFun (congrFun (h2 i).2.2 s) t
  have a21 : (cat T')ᴴ * J * cat T = 1 := by rw [sw, a12, Matrix.conjTranspose_one]
  have a31 : T₀ᴴ * J * cat T = 0 := by rw [sw, a13, Matrix.conjTranspose_zero]
  have a32 : T₀ᴴ * J * cat T' = 0 := by rw [sw, a23, Matrix.conjTranspose_zero]
  ext ((p | p) | p) ((q | q) | q)
  · exact congrFun (congrFun a11 p) q
  · exact congrFun (congrFun a12 p) q
  · exact congrFun (congrFun a13 p) q
  · exact congrFun (congrFun a21 p) q
  · exact congrFun (congrFun a22 p) q
  · exact congrFun (congrFun a23 p) q
  · exact congrFun (congrFun a31 p) q
  · exact congrFun (congrFun a32 p) q
  · exact congrFun (congrFun h3 p) q

theorem exists_unitary_adapted {a m : ℕ} {j : Fin a → ℕ} (hn : n = m + 2 * ∑ i, j i)
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (J₀ : Matrix (Fin m) (Fin m) E) (hJ₀ : J₀.det ≠ 0)
    (T T' U U' : ∀ i, Matrix (Fin n) (Fin (j i)) E) (T₀ U₀ : Matrix (Fin n) (Fin m) E)
    (h1 : ∀ i k, (T i)ᴴ * J * T k = 0 ∧ (T' i)ᴴ * J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * J * T' k = 0))
    (h2 : ∀ i, (T i)ᴴ * J * T' i = 1 ∧ (T i)ᴴ * J * T₀ = 0 ∧ (T' i)ᴴ * J * T₀ = 0)
    (h3 : T₀ᴴ * J * T₀ = J₀)
    (g1 : ∀ i k, (U i)ᴴ * J * U k = 0 ∧ (U' i)ᴴ * J * U' k = 0 ∧ (i ≠ k → (U i)ᴴ * J * U' k = 0))
    (g2 : ∀ i, (U i)ᴴ * J * U' i = 1 ∧ (U i)ᴴ * J * U₀ = 0 ∧ (U' i)ᴴ * J * U₀ = 0)
    (g3 : U₀ᴴ * J * U₀ = J₀) :
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * γ = J ∧
      (∀ i, (γ : Matrix (Fin n) (Fin n) E) * T i = U i) ∧ (∀ i, (γ : Matrix (Fin n) (Fin n) E) * T' i = U' i) ∧
      (γ : Matrix (Fin n) (Fin n) E) * T₀ = U₀ := by
  obtain ⟨γ, hγ, hB⟩ := exists_unitary_of_gram
    (κ := ((Σ i, Fin (j i)) ⊕ (Σ i, Fin (j i))) ⊕ Fin m) (by simp [hn]; ring) J _ _ _
    (fromBlocks (fromBlocks 0 1 1 0) 0 0 J₀⁻¹)
    (by simp [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ₀)])
    (gram_adapted J hJ J₀ T T' T₀ h1 h2 h3) (gram_adapted J hJ J₀ U U' U₀ g1 g2 g3)
  refine ⟨γ, hγ, fun i => ?_, fun i => ?_, ?_⟩
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inl (Sum.inl ⟨i, s⟩))
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inl (Sum.inr ⟨i, s⟩))
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inr s)

end Linear

theorem unitary_map {E A : Type} [CommRing E] [CommRing A] {n : ℕ} (σ : E →+* E) (s : A →+* A) (φ : E →+* A)
    (h : ∀ e, s (φ e) = φ (σ e)) (J g : Matrix (Fin n) (Fin n) E) (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT s (g.map φ) * J.map φ * g.map φ = J.map φ := by
  have e : Formalism.UG.cT s (g.map φ) = (Formalism.UG.cT σ g).map φ := by
    ext i k
    simp [Formalism.UG.cT, h]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hg]

theorem exists_point (I : AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    ∃ a : I.GA,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  apply GlobalTheory.RadCov.RatElt.exists_point <;> assumption

theorem mem_ratIso (I : AutInst) (γ : GL (Fin I.n) I.E) (N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (z : Fin I.n → I.E) :
    z ∈ GlobalTheory.PointEquivariance.ratIso I γ N ↔ ∃ y ∈ N, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y = z := Iff.rfl

theorem conjugate_of_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (xf' : I.Gf) (S' : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (U U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf' j S' Λ x₀ U U' U₀ → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * xf = xf' * k ∧ ∀ g : I.Ginf, sizesAt I xf' S' (γ.1 * g) = sizesAt I xf S g := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ _ ⟨_, hn, _, h1, h2, h3, h4, h5⟩ xf' S' U U' U₀ ⟨_, _, _, g1, g2, g3, g4, g5⟩
  have hcT : ∀ M : Matrix (Fin I.n) (Fin I.n) I.E, Formalism.UG.cT (starRingEnd I.E) M = Mᴴ := fun M => rfl
  have hJ : I.Jᴴ = I.J := (hcT _).symm.trans I.J_herm
  have hJ₀ : (I₀.J.map e).det ≠ 0 := by
    have := RingHom.map_det (e : I₀.E →+* I.E) I₀.J
    change e _ = (I₀.J.map e).det at this
    rw [← this]
    exact (map_ne_zero e).2 I₀.J_det
  obtain ⟨γ, hγ, c1, c2, c3⟩ := exists_unitary_adapted hn I.J hJ _ hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3
  have hγ' : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := hγ
  obtain ⟨c, hc1, hc2⟩ := exists_point I γ hγ'
  have d1 : ∀ u : ∀ i, Fin (j i) → I.E,
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T i *ᵥ u i = ∑ i, U i *ᵥ u i := by
    intro u
    simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c1]
  have d2 : ∀ u : ∀ i, Fin (j i) → I.E,
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T' i *ᵥ u i = ∑ i, U' i *ᵥ u i := by
    intro u
    simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c2]
  have hS : ∀ k, S' k = GlobalTheory.PointEquivariance.ratIso I γ (S k) := by
    intro k
    ext z
    rw [g5, mem_ratIso]
    constructor
    · rintro ⟨u, p1, p2, rfl⟩
      exact ⟨_, (h5 k _).2 ⟨u, p1, p2, rfl⟩, d1 u⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, p1, p2, rfl⟩ := (h5 k y).1 hy
      exact ⟨u, p1, p2, d1 u⟩
  have hL : lamX I (c * (1, xf)) = lamX I (1, xf') := by
    rw [GlobalTheory.PointEquivariance.lamX_rat I _ c γ hc2]
    ext z
    rw [g4, mem_ratIso]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, u', w, p1, p2, p3, rfl⟩ := (h4 y).1 hy
      refine ⟨u, u', w, p1, p2, p3, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]
    · rintro ⟨u, u', w, p1, p2, p3, rfl⟩
      refine ⟨_, (h4 _).2 ⟨u, u', w, p1, p2, p3, rfl⟩, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]
  refine ⟨c, ⟨γ, hγ', hc1, hc2⟩, xf'⁻¹ * (c.2 * xf), ?_, (mul_inv_cancel_left _ _).symm, fun g => ?_⟩
  · have := (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, xf') (((1, xf') : I.GA)⁻¹ * (c * (1, xf)))).2
      (by rw [mul_inv_cancel_left, hL])
    exact this
  · funext i
    have hfr : frm I (c.1 * g, xf') = frm I (c * (g, xf)) := rfl
    unfold sizesAt
    rw [hfr, hS, hS]
    exact GlobalTheory.PointEquivariance.sizeQ_eq _ _ _ _ (GlobalTheory.PointEquivariance.zl_ratIso I (g, xf) c γ hc1)
      (GlobalTheory.PointEquivariance.rkK_ratIso I γ) _ _

end GlobalTheory.FlagConj
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.LowDim

variable {n m : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
  {U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ}

theorem block_eq_zero (hB : Biorth r m U (fun b => (U b)ᴴ)) {s : ℕ} (hs : m ≤ s) : U s = 0 := by
  obtain ⟨-, h2, h3⟩ := hB
  calc U s = (∑ b ∈ range m, U b * (U b)ᴴ) * U s := by rw [h3, Matrix.one_mul]
    _ = 0 := by
      rw [Matrix.sum_mul]
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' : b ≠ s := by have := Finset.mem_range.1 hb; omega
      rw [Matrix.mul_assoc, h2 b s hb', Matrix.mul_zero]

theorem mem_lowers_iff_blocks (hB : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ lowers W c ↔ ∀ s t, t ≤ s + c → (U s)ᴴ * Y * U t = 0 := by
  apply GlobalTheory.LayerIso.mem_lowers_iff <;> assumption

noncomputable def layer (m : ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (c : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) ℂ where
  toFun Y b := (U b)ᴴ * Y * U (b + c + 1)
  map_add' Y Z := by
    funext b
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a Y := by
    funext b
    simp

end GlobalTheory.RadCov.LowDim

namespace GlobalTheory.RadCov


open LowDim in
theorem finrank_lowers_eq_succ_add (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ)
    (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (hB : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) :
    Module.finrank ℂ (lowers W c) = Module.finrank ℂ (lowers W (c + 1)) +
      ∑ b ∈ Finset.range m, r b * r (b + c + 1) := by
  have hle : lowers W (c + 1) ≤ lowers W c := by
    intro Y hY
    rw [mem_lowers_iff_blocks hB hW] at hY ⊢
    exact fun s t hst => hY s t (by omega)
  let φ := (layer m U c).domRestrict (lowers W c)
  have hker : LinearMap.ker φ = (lowers W (c + 1)).comap (lowers W c).subtype := by
    ext ⟨Y, hY⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      mem_lowers_iff_blocks hB hW]
    rw [mem_lowers_iff_blocks hB hW] at hY
    constructor
    · intro h s t hst
      by_cases h' : t ≤ s + c
      · exact hY s t h'
      · obtain rfl : t = s + c + 1 := by omega
        by_cases hs : s < m
        · exact congrFun h ⟨s, hs⟩
        · rw [block_eq_zero hB (not_lt.1 hs)]
          simp
    · intro h
      funext b
      exact h b (b + c + 1) le_rfl
  have hrange : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro Z
    obtain ⟨h1, h2, -⟩ := id hB
    have key : ∀ s t, (U s)ᴴ * (∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ) * U t
        = ∑ b : Fin m, ((U s)ᴴ * U b) * Z b * ((U (b + c + 1))ᴴ * U t) := by
      intro s t
      rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by simp only [Matrix.mul_assoc]
    refine ⟨⟨∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ, ?_⟩, ?_⟩
    · rw [mem_lowers_iff_blocks hB hW]
      intro s t hst
      rw [key]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : s = b
      · rw [h2 (b + c + 1) t (by omega), Matrix.mul_zero]
      · rw [h2 s b hb, Matrix.zero_mul, Matrix.zero_mul]
    · funext s
      change (U s)ᴴ * (∑ b : Fin m, U b * Z b * (U (b + c + 1))ᴴ) * U (s + c + 1) = Z s
      rw [key, Finset.sum_eq_single s]
      · rw [h1, h1, Matrix.one_mul, Matrix.mul_one]
      · intro b _ hb
        rw [h2 s b (fun h => hb (Fin.ext h.symm)), Matrix.zero_mul, Matrix.zero_mul]
      · simp
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, hrange, finrank_top, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
    Module.finrank_pi_fintype] at h
  rw [← h, add_comm, ← Fin.sum_univ_eq_sum_range (fun b => r b * r (b + c + 1)) m]
  simp [Module.finrank_matrix]

end GlobalTheory.RadCov
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.fundamental_set_measure_commensurable_index_ratio : ∀ (G α : Type) [Group G] [MulAction G α] [MeasurableSpace α] (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α), (∀ s : G, Measurable fun x : α => s • x) → Countable A → Countable B → μ Rᶜ = 0 → (∀ s ∈ A ⊔ B, (∀ x ∈ R, s • x ∈ R) ∧ μ.map (fun x => s • x) = μ) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → MeasurableSet Ω → MeasurableSet K → (∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) → (∀ x ∈ R, ∃! s, s ∈ B ∧ s • x ∈ K) → μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  first | exact @GlobalTheory.CovolIdx.measure_eq_invVol_mul | exact GlobalTheory.CovolIdx.measure_eq_invVol_mul | (intros; apply GlobalTheory.CovolIdx.measure_eq_invVol_mul <;> assumption)
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

variable {k r : ℕ}

def rep (L : LocBessel k r) : BranchingSupport.Rep k r := ⟨L.Hs, L.σ⟩

def BeTK (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) : Prop :=
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def SmCW (L : LocBessel k r) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (l : L.Hs → V) : Prop :=
  (∀ v ∈ (rep L).sm, ∀ w ∈ (rep L).sm, l (v + w) = l v + l w) ∧ (∀ (a : ℂ), ∀ v ∈ (rep L).sm, l (a • v) = a • l v) ∧
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) L.σ l

def OneAt (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) : Prop :=
  ∃ A : L.Wq →L[ℂ] L.Wp, ∀ F s, IsCoef (rep L) l l' F s → OrbInt L F g ν = s • A

theorem J_eq_orbInt (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.J F g = OrbInt L F g (pairMeas L) := rfl

end GlobalTheory.AmpTK
end
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter : ∀ (k r : ℕ) (c : ℂ), c ≠ 0 → ∃ t ∈ GG k r, (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) ∧ (∀ z, inWb k r z → t *ᵥ z = z ∧ (∀ h ∈ UWset k r z, t * h = h * t) ∧ ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) ∧ ∀ a : Fin (r + 1), ∃ s : ℂ, s ≠ 0 ∧ ‖s‖ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ‖s‖⁻¹ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ∀ z, inWb k r z → t⁻¹ *ᵥ fvec k r z a = s • fvec k r z a := by
  first | exact @GlobalTheory.TorusScale.exists_torus_scale | exact GlobalTheory.TorusScale.exists_torus_scale | (intros; apply GlobalTheory.TorusScale.exists_torus_scale <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.few_orbits_subspaces_hermitian_lattice_discriminant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (j n : ℕ), 1 ≤ n → ∃ s : Finset (Submodule K V), (s.card : ℝ) ≤ (n : ℝ) ^ (1 + Real.logb 2 (Module.finrank ℚ K)) ∧ (∀ U ∈ s, Module.finrank K U = j) ∧ ∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) n).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U := by
  first | exact @GlobalTheory.Mass.FewOrbits.main | exact GlobalTheory.Mass.FewOrbits.main | (intros; apply GlobalTheory.Mass.FewOrbits.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_fineSubgroup_moves_at_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∃ B : AddSubgroup S.MW, Fine (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ)) B ∧ ∀ w, S.Mv (j + 1) d Λ w → ∀ b ∈ B, S.moved Λ (w + b).1.1 (w + b).2.1 (S.sOf (w + b)) = S.moved Λ w.1.1 w.2.1 (S.sOf w) ∧ S.chiM j d Λ (w + b).1 (w + b).2.1 = S.chiM j d Λ w.1 w.2.1 ∧ (S.NoLeak Λ (w + b).2.1 ↔ S.NoLeak Λ w.2.1) := by
  first | exact @GlobalTheory.MoveFine.main | exact GlobalTheory.MoveFine.main | (intros; apply GlobalTheory.MoveFine.main <;> assumption)
end

section

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.gramUnipotentLieLattice_domain_volume_bound : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N) (B : ℝ) (Bv : ι → ℝ), (∀ v a, τ v (star a) = starRingEnd ℂ (τ v a)) → (∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) → finrank ℚ K = 2 * Fintype.card ι → IsLoUni L → IsUpUni U → EntIn ⊤ (L * ptMat p * U) → 1 ≤ B → (∀ (t : ℕ) (I J : Fin t → Fin N) (v : ι), ‖τ v (((L * ptMat p * U).submatrix I J).det)‖ ≤ Bv v) → ∏ v, max 1 (Bv v) ≤ B → ∀ Λ : Submodule ℤ (ι → roots (ptMat p) → ℂ), (∀ c, c ∈ Λ ↔ ∃ x ∈ lieU (L * ptMat p * U), EntIn ⊤ x ∧ ∀ v (q : roots (ptMat p)), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) → ∃ Ω : Set (ι → roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.IsAddFundamentalDomain Λ Ω MeasureTheory.volume ∧ MeasureTheory.volume Ω ≤ ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) * ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2)) := by
  first | exact @GlobalTheory.LieCovol.lie_lattice_domain | exact GlobalTheory.LieCovol.lie_lattice_domain | (intros; apply GlobalTheory.LieCovol.lie_lattice_domain <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm


open MeasureTheory NumberField Matrix Finset in
open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL : ∀ (E : Type) [Field E] [NumberField E],
    IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ →
      ∀ γ ∈ _root_.GlobalTheory.FlagMeas.autGL E j Λ, _root_.GlobalTheory.FlagMeas.detNorm E j γ = 1 := by
  intro E _ _ hE j Λ hΛ γ hγ
  obtain ⟨κ, hκ, hcov⟩ := (_root_.GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  have hpos := _root_.GlobalTheory.OrbitTerm.detNorm_pos_of_mem_autGL hγ
  have h1 := (hcov γ hpos).2.1
  have h2 := (hcov (_root_.GlobalTheory.OrbitTerm.oneInf E j) (by
    rw [_root_.GlobalTheory.OrbitTerm.detNorm_oneInf]; exact one_pos)).2.1
  rw [_root_.GlobalTheory.OrbitTerm.detNorm_oneInf, div_one] at h2
  have hmul := _root_.GlobalTheory.FlagBase.Test.latAt_aut_mul E j Λ hγ (_root_.GlobalTheory.OrbitTerm.oneInf E j)
  rw [_root_.GlobalTheory.OrbitTerm.mul_oneInf] at hmul
  rw [hmul, h2] at h1
  field_simp at h1
  linarith

end GlobalTheory.OrbitTerm
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.pointsOfFlagTypeSet_measurable_and_invariant : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)), MeasurableSet B → MeasurableSet (typeSet I j B) ∧ (∀ γ ∈ I.GFset, ∀ x ∈ typeSet I j B, γ * x ∈ typeSet I j B) ∧ ∀ x ∈ typeSet I j B, ∀ k ∈ I.Kset, (x.1, x.2 * k) ∈ typeSet I j B := by
  first | exact @GlobalTheory.FlagMeas.typeSet_measurable_invariant | exact GlobalTheory.FlagMeas.typeSet_measurable_invariant | (intros; apply GlobalTheory.FlagMeas.typeSet_measurable_invariant <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.isotropicFlag_dimension_count : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → p + q = n ∧ n ^ 2 = 2 * dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) ∧ p ^ 2 + q ^ 2 = dimN n j + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
  first | exact @GlobalTheory.IwConst.flag_dims | exact GlobalTheory.IwConst.flag_dims | (intros; apply GlobalTheory.IwConst.flag_dims <;> assumption)
end
