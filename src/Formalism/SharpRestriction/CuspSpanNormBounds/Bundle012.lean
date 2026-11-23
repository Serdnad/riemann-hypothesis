module

import CompanionTheory.AutomorphicTheory.BesselWaveGrids.Bundle002
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle011
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.SharpRestriction.ParamsHeightRankConstant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle010
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan
public import Formalism.SharpRestriction.ParConsts
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.NearParameterGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.OnePlaceEstimates

theorem consts (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ (2 * (r : ℝ) + 2) ^ 2 / 2 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
  apply CompanionTheory.WaveGrid.GapSizes.consts <;> assumption

end Formalism.MainNotions.NearParameterGap
end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Conj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem unimodAt_of_unimod {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (hlat : Submodule.IsLattice E L) (hu : IsUnimodular h L)
    (p : Ideal (𝓞 E)) : IsUnimodularAt h p L := by
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective _ _
  have hst : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
    fun r => cyc_star_int r
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) (self := hlat)
  unfold IsUnimodularAt
  rw [locDual_dualAt_loc h hinj hst]
  have e1 := locDual_loc_dual_le h p L
  have e2 := locDual_dualAt_le h hst p L hfg
  unfold IsUnimodular at hu
  rw [hu] at e1 e2
  exact le_antisymm e2 e1

private theorem rows_span_eq_top_of_unimodular (S : Formalism.BasicNotions.HSpace E) {Λ : Submodule (𝓞 E) S.V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) :
    Submodule.span E (Λ : Set S.V) = ⊤ := by
  exact Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hU S.herm hL


theorem unimod_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (L M : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (hM : Submodule.IsLattice E M)
    (huL : IsUnimodular S.hT L) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT L :=
  ⟨{ toIsLattice := hM, span_eq_top := rows_span_eq_top_of_unimodular S hM.fg huM }, fun p hp => hU F E hc S L M hL hM p hp (unimodAt_of_unimod S.hT L hL huL p) (unimodAt_of_unimod S.hT M hM huM p)⟩

theorem unimodular_mem_genus (hU : LocUnimod) (hc : Formalism.BasicNotions.CMData F E) (S : Formalism.BasicNotions.HSpace E)
    (M : Submodule (𝓞 E) S.V) (hM : Submodule.IsLattice E M) (huM : IsUnimodular S.hT M) : M ∈ genus S.hT S.L0 :=
  unimod_mem_genus hU hc S S.L0 M S.standardTuple_isLattice hM S.baseLattice_isUnimodular huM

end Conj

section Rows

open Formalism.BasicNotions Formalism.MainNotions.BridgeLemma₂

end Rows

end Formalism.MainNotions.BridgeRowsGenus

end
end

section

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def tF (r : ℕ) (κ τ : ℝ) (a : ℕ) : ℝ := τ * κ ^ (r - a)

def tV (k r : ℕ) (κ τ : ℝ) (i : Fin (2 * r + k + 1)) : ℝ :=
  if i.val < r then tF r κ τ i.val
  else if i.val ≤ r + k then 1 else (tF r κ τ (2 * r + k - i.val))⁻¹

def dM (k r : ℕ) (κ τ : ℝ) : Mx k r := Matrix.diagonal fun i => ((tV k r κ τ i : ℝ) : ℂ)

def dMi (k r : ℕ) (κ τ : ℝ) : Mx k r := Matrix.diagonal fun i => (((tV k r κ τ i)⁻¹ : ℝ) : ℂ)

def cj (k r : ℕ) (κ τ : ℝ) (x : Mx k r) : Mx k r := dMi k r κ τ * x * dM k r κ τ

def cjI (k r : ℕ) (κ τ : ℝ) (x : Mx k r) : Mx k r := dM k r κ τ * x * dMi k r κ τ

def cjT (k r : ℕ) (κ τ : ℝ) (x : Mt k r) : Mt k r := fun i j => cj k r κ τ (Matrix.of x) i j

def cjIT (k r : ℕ) (κ τ : ℝ) (x : Mt k r) : Mt k r := fun i j => cjI k r κ τ (Matrix.of x) i j

section Alg

variable {k r : ℕ} {κ τ : ℝ}

theorem tF_pos (hκ : 0 < κ) (hτ : 0 < τ) (a : ℕ) : 0 < tF r κ τ a := mul_pos hτ (pow_pos hκ _)

theorem tV_pos (hκ : 0 < κ) (hτ : 0 < τ) (i : Fin (2 * r + k + 1)) : 0 < tV k r κ τ i := by
  unfold tV; split_ifs
  · exact tF_pos hκ hτ _
  · exact one_pos
  · exact inv_pos.mpr (tF_pos hκ hτ _)

theorem dMi_mul_dM (hκ : 0 < κ) (hτ : 0 < τ) : dMi k r κ τ * dM k r κ τ = 1 := by
  rw [dMi, dM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (tV_pos hκ hτ i).ne', Complex.ofReal_one]

theorem dM_mul_dMi (hκ : 0 < κ) (hτ : 0 < τ) : dM k r κ τ * dMi k r κ τ = 1 := by
  rw [dMi, dM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (tV_pos hκ hτ i).ne', Complex.ofReal_one]

theorem cj_apply (x : Mx k r) (i j : Fin (2 * r + k + 1)) :
    cj k r κ τ x i j = ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) * x i j := by
  simp only [cj, dMi, dM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  push_cast; ring

theorem cjI_apply (x : Mx k r) (i j : Fin (2 * r + k + 1)) :
    cjI k r κ τ x i j = (((tV k r κ τ i * (tV k r κ τ j)⁻¹ : ℝ)) : ℂ) * x i j := by
  simp only [cjI, dMi, dM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  push_cast; ring

theorem cj_cjI (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) : cj k r κ τ (cjI k r κ τ x) = x := by
  simp only [cj, cjI, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dMi k r κ τ) (dM k r κ τ), dMi_mul_dM hκ hτ, Matrix.one_mul, Matrix.mul_one]

theorem cjI_cj (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) : cjI k r κ τ (cj k r κ τ x) = x := by
  simp only [cj, cjI, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dM k r κ τ) (dMi k r κ τ), dM_mul_dMi hκ hτ, Matrix.one_mul, Matrix.mul_one]

theorem cj_mul (hκ : 0 < κ) (hτ : 0 < τ) (x y : Mx k r) :
    cj k r κ τ (x * y) = cj k r κ τ x * cj k r κ τ y := by
  simp only [cj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dM k r κ τ) (dMi k r κ τ), dM_mul_dMi hκ hτ, Matrix.one_mul]

theorem dM_inv (hκ : 0 < κ) (hτ : 0 < τ) : (dM k r κ τ)⁻¹ = dMi k r κ τ :=
  Matrix.inv_eq_left_inv (dMi_mul_dM hκ hτ)

theorem dMi_inv (hκ : 0 < κ) (hτ : 0 < τ) : (dMi k r κ τ)⁻¹ = dM k r κ τ :=
  Matrix.inv_eq_left_inv (dM_mul_dMi hκ hτ)

theorem cj_inv (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) : cj k r κ τ x⁻¹ = (cj k r κ τ x)⁻¹ := by
  rw [cj, cj, Matrix.mul_inv_rev, Matrix.mul_inv_rev, dM_inv hκ hτ, dMi_inv hκ hτ, Matrix.mul_assoc]

theorem of_cjT (x : Mt k r) : Matrix.of (cjT k r κ τ x) = cj k r κ τ (Matrix.of x) := by
  ext i j; rfl

theorem of_cjIT (x : Mt k r) : Matrix.of (cjIT k r κ τ x) = cjI k r κ τ (Matrix.of x) := by
  ext i j; rfl

theorem cjT_cjIT (hκ : 0 < κ) (hτ : 0 < τ) (x : Mt k r) : cjT k r κ τ (cjIT k r κ τ x) = x := by
  funext i j; simp only [cjT, of_cjIT, cj_cjI hκ hτ]; rfl

theorem cjIT_cjT (hκ : 0 < κ) (hτ : 0 < τ) (x : Mt k r) : cjIT k r κ τ (cjT k r κ τ x) = x := by
  funext i j; simp only [cjIT, of_cjT, cjI_cj hκ hτ]; rfl

theorem continuous_cjT : Continuous (cjT k r κ τ) := by
  have : cjT k r κ τ = fun x i j => ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) * x i j := by
    funext x i j; exact cj_apply (Matrix.of x) i j
  rw [this]; fun_prop

theorem continuous_cjIT : Continuous (cjIT k r κ τ) := by
  have : cjIT k r κ τ = fun x i j => (((tV k r κ τ i * (tV k r κ τ j)⁻¹ : ℝ)) : ℂ) * x i j := by
    funext x i j; exact cjI_apply (Matrix.of x) i j
  rw [this]; fun_prop

def cjE (hκ : 0 < κ) (hτ : 0 < τ) : Mt k r ≃ᵐ Mt k r where
  toFun := cjT k r κ τ
  invFun := cjIT k r κ τ
  left_inv := cjIT_cjT hκ hτ
  right_inv := cjT_cjIT hκ hτ
  measurable_toFun := continuous_cjT.measurable
  measurable_invFun := continuous_cjIT.measurable

theorem tV_mul_of_Hpk (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) (h : Hpk k r i j ≠ 0) :
    tV k r κ τ i * tV k r κ τ j = 1 := by
  have hti := tF_pos (r := r) hκ hτ i.val
  have htj := tF_pos (r := r) hκ hτ j.val
  unfold tV
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · have e : 2 * r + k - j.val = i.val := by omega
    rw [if_pos h1.1, if_neg (by omega), if_neg (by omega), e, mul_inv_cancel₀ hti.ne']
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · have e : 2 * r + k - i.val = j.val := by omega
    rw [if_neg (by omega), if_neg (by omega), if_pos h2.1, e, inv_mul_cancel₀ htj.ne']
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · rw [h3.2.2]; rw [if_neg (by omega), if_pos (by omega), mul_one]
  · exfalso; apply h; unfold Hpk; rw [if_neg h1, if_neg h2, if_neg h3]

theorem diag_mem_UH (s : Fin (2 * r + k + 1) → ℝ)
    (hs : ∀ i j, Hpk k r i j ≠ 0 → s i * s j = 1) :
    Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) ∈ UH (Hpk k r) := by
  show (Matrix.diagonal fun i => ((s i : ℝ) : ℂ))ᴴ * Hpk k r * Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) = Hpk k r
  rw [Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : Hpk k r i j = 0
  · rw [h]; simp
  · have := hs i j h
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    calc (s i : ℂ) * Hpk k r i j * (s j : ℂ) = ((s i * s j : ℝ) : ℂ) * Hpk k r i j := by push_cast; ring
      _ = Hpk k r i j := by rw [this]; simp

theorem dM_mem_UH (hκ : 0 < κ) (hτ : 0 < τ) : dM k r κ τ ∈ UH (Hpk k r) :=
  diag_mem_UH _ (tV_mul_of_Hpk hκ hτ)

theorem dMi_mem_UH (hκ : 0 < κ) (hτ : 0 < τ) : dMi k r κ τ ∈ UH (Hpk k r) := by
  refine diag_mem_UH _ fun i j h => ?_
  rw [← mul_inv, tV_mul_of_Hpk hκ hτ i j h, inv_one]

theorem UH_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

theorem cj_mem_UH_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) :
    cj k r κ τ g ∈ UH (Hpk k r) ↔ g ∈ UH (Hpk k r) := by
  constructor
  · intro h
    have := UH_mul (UH_mul (dM_mem_UH hκ hτ) h) (dMi_mem_UH hκ hτ)
    rwa [← cjI, cjI_cj hκ hτ] at this
  · intro h; exact UH_mul (UH_mul (dMi_mem_UH hκ hτ) h) (dM_mem_UH hκ hτ)

end Alg

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₄

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def DDsp {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => σ g w0) '' UH (Hpk k r))

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.BridgeLemma₄
end
end

section

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.MainNotions

variable {eps : ℝ}

def sC' (Fm : FamP eps) : ℝ := Fm.CkLow

def sCl (Fm : FamP eps) : ℝ :=
  min Fm.CfL (min Fm.Cw (min Fm.CDel (min Fm.CCount (min Fm.Ch0r Fm.Cgap))))

def scT : ℝ := 1 / 2

def OwnEv (Fm : FamP eps) (P : ℝ → ℝ → ∀ x, Fm.Ix x → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, P (sC' Fm) (sCl Fm) x i

theorem OwnEv.mono {Fm : FamP eps} {P Q : ℝ → ℝ → ∀ x, Fm.Ix x → Prop}
    (h : ∀ C' Cl x i, P C' Cl x i → Q C' Cl x i) (hP : OwnEv Fm P) : OwnEv Fm Q := by
  obtain ⟨x0, hx⟩ := hP
  exact ⟨x0, fun x hx' i => h _ _ _ _ (hx x hx' i)⟩

theorem OwnEv.and {Fm : FamP eps} {P Q : ℝ → ℝ → ∀ x, Fm.Ix x → Prop}
    (hP : OwnEv Fm P) (hQ : OwnEv Fm Q) : OwnEv Fm (fun C' Cl x i => P C' Cl x i ∧ Q C' Cl x i) := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  exact ⟨max a b, fun x hx i => ⟨ha x (le_of_max_le_left hx) i, hb x (le_of_max_le_right hx) i⟩⟩

theorem le_sC'_sCl {Fm : FamP eps} {K : TransportedAlt} {CH : ℝ} (h : Fm.Large K CH) :
    K.last (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm ∧ K.last (Fm.cOut ++ Fm.cMid CH) ≤ sCl Fm := by
  have H := h.2.2.2
  refine ⟨H _ (by simp [sC', FamP.cLast]), ?_⟩
  simp only [sCl, le_min_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact H _ (by simp [FamP.cLast])

end Formalism.MainNotions.S
end
end
