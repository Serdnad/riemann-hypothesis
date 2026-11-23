module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

section cont
variable {p m : ℕ}

theorem cont_ite {β : Type} [TopologicalSpace β] [Zero β] (c : Prop) [Decidable c] {f : Xp p m → β}
    (hf : Continuous f) : Continuous (fun x => if c then f x else 0) := by
  by_cases h : c
  · simp only [h, if_true]; exact hf
  · simp only [h, if_false]; exact continuous_const

theorem cont_Lsq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold Lsq
  exact continuous_const.fun_add (continuous_finsetSum _ fun j _ =>
    cont_ite _ (((continuous_apply j).comp continuous_fst).norm.pow 2))

theorem cont_rhoSq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  unfold rhoSq
  refine ((cont_Lsq _).add (continuous_finsetSum _ fun i _ => ?_)).add (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2)

theorem cont_bco (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  unfold bco
  refine ((Complex.continuous_ofReal.comp ((continuous_finsetSum _ fun i _ => ?_).fun_neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      continuous_const)).sub (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_fst).star)

theorem cont_de (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold de
  exact Real.continuous_sqrt.comp (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

theorem cont_linF (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (fun x : Xp p m => linF η η' ζ x) := by
  unfold linF
  refine (continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun i _ => ?_)
  · exact (((continuous_apply j).comp continuous_fst).mul continuous_const).add
      (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul continuous_const)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul continuous_const

def GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) (x : Xp p m) : ℝ≥0∞ :=
  (∏ l, ENNReal.ofReal (de x l ^ (-s l))) * ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))

theorem meas_GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) :
    Measurable (GI s δ η η' ζ c₀) := by
  unfold GI
  refine (Finset.measurable_prod _ fun l _ => ?_).mul ?_
  · exact ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)
  · exact ENNReal.measurable_ofReal.comp ((continuous_const.add ((continuous_const.mul
      (Complex.continuous_im.comp (cont_linF η η' ζ))).add continuous_const).abs).measurable.pow_const _)

end cont

theorem mp_unitary {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun y : Fin N → ℂ => U *ᵥ y) volume volume := by
  set f : (Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) := (Matrix.toLin' U).restrictScalars ℝ with hf
  have hfU : (fun y : Fin N → ℂ => U *ᵥ y) = ⇑f := by funext y; simp [hf, Matrix.toLin'_apply]
  have hn : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]; exact_mod_cast hn
  rw [hfU]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

theorem mp_hpar {k n : ℕ} (U : Mat k n) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun X : HPar k n => (U *ᵥ X.1, X.2)) volume volume :=
  (mp_unitary U hU).prod (MeasurePreserving.id volume)

theorem os_q (hOS : OS) (q p m : ℕ) (hq : q = p + 1) (δ γ : ℝ) (e : Fin (q + 1) → ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hγ : 0 < γ) (hγ8 : γ ≤ δ / 8) (he : ∀ l, 0 < e l) (hsum : e 0 + 2 * ∑ i : Fin q, e i.succ < γ / 2) :
    ∃ C : ℝ, ∀ (η η' : Fin q → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI (fun l => s0N q m l - e l) δ η η' ζ c₀ x ≤
        ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
  subst hq
  obtain ⟨C, hC⟩ := hOS p m δ γ e hδ hδ2 hγ hγ8 he hsum
  refine ⟨C, fun η η' ζ c₀ h0 => ?_⟩
  have e0 : (⟨0, by omega⟩ : Fin (p + 1)) = 0 := Fin.ext (by simp)
  rw [e0] at h0 ⊢
  exact hC η η' ζ c₀ h0

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def Kset (k r : ℕ) : Set (Mat k r) := {g | g ∈ GV k r ∧ gᴴ * g = 1}

def epsV (k r : ℕ) : Fin (2 * r + k + 1) → ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (bvec (wI k r 0) + bvec (wI k r (Fin.last k)))

def phiV (k r : ℕ) (a : Fin (r + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : a.val < r then bvec (esI k r ⟨a.val, h⟩) else epsV k r

def phiV' (k r : ℕ) (a : Fin (r + 1)) : Fin (2 * r + k + 1) → ℂ := Hpk k r *ᵥ phiV k r a

def Ga (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : ℝ :=
  (Matrix.det (Matrix.of fun a b : Fin (l.val + 1) =>
    star (Y (Fin.castLE (by omega) a)) ⬝ᵥ Y (Fin.castLE (by omega) b))).re

def Del (k r : ℕ) (l : Fin (r + 1)) (x : Mat k r) : ℝ := Real.sqrt (Ga k r l fun a => x *ᵥ phiV k r a)

def Dl (k r : ℕ) (l : Fin (r + 1)) (g : Mat k r) : ℂ :=
  Matrix.det (Matrix.of fun a b : Fin (l.val + 1) =>
    herm (Hpk k r) (g *ᵥ phiV' k r (Fin.castLE (by omega) b)) (phiV' k r (Fin.castLE (by omega) a)))

def s0 (k r : ℕ) (l : Fin (r + 1)) : ℝ := if l.val < r then 2 else (k : ℝ)

def SAdm (k r : ℕ) (s : Fin (r + 1) → ℝ) : Prop := ∀ l, 0 < s0 k r l - s l ∧ s0 k r l - s l ≤ 1 / 10

def xiR (k r : ℕ) (s : Fin (r + 1) → ℝ) (x : Mat k r) : ℝ := ∏ l, Del k r l x ^ (-s l)

def xiN (k r : ℕ) (s : Fin (r + 1) → ℝ) (x : Mat k r) : ℝ≥0 := Real.toNNReal (xiR k r s x)

def FsE (k r : ℕ) (s : Fin (r + 1) → ℝ) (g : Mat k r) : ℝ≥0∞ := ∏ l, (‖Dl k r l g‖₊ : ℝ≥0∞) ^ (-s l)

def fsR (k r : ℕ) (s : Fin (r + 1) → ℝ) (x : Mat k r) : ℝ := ∏ l, Ga k r l (fun a => x *ᵥ phiV' k r a) ^ (-s l / 2)

def JInt {k r : ℕ} (μG : Measure (Mt k r)) (A : ℝ) (s : Fin (r + 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s (Matrix.of g) ∂μG

def IInt {k r : ℕ} (μN : Measure (Mt k r)) (z : Fin (2 * r + k + 1) → ℂ) (s : Fin (r + 1) → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ n : Mt k r, ENNReal.ofReal (xiR k r s (Matrix.of n)) *
    ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-δ)) ∂μN

def AAt (k r : ℕ) : Prop :=
  ∀ s, SAdm k r s → ∀ μG : Measure (Mt k r), IsHaarOn (GV k r) μG → ∀ A : ℝ, AB k r ≤ A → JInt μG A s < ∞

def BAt (k r : ℕ) (δ : ℝ) : Prop :=
  ∃ eS : ℝ, 0 < eS ∧ ∀ s : Fin (r + 1) → ℝ, (∀ l, 0 < s0 k r l - s l ∧ s0 k r l - s l ≤ eS) →
    ∀ z : Fin (2 * r + k + 1) → ℂ, inWb k r z → 0 < Tz k r z →
      ∀ μN : Measure (Mt k r), IsHaarOn (Nset k r) μN → IInt μN z s δ < ∞

def InductiveHeisenbergInputs : Prop :=
  OneStepInt ∧ OneStepCoord ∧ OneStepMem ∧ NRecHaar ∧ NBase ∧ HeisConjLev ∧ HeisConjLevMeas ∧ HeisInv ∧ HeisMul ∧
    HeisMem ∧ HeisClosed ∧ HeisHaar ∧ ConjInvAll ∧ CompactW ∧ GNIntSharp ∧ GNLower ∧ HaarUnique ∧ HaarInv ∧
    CompactHaarExists ∧ ClosedG ∧ ClosedN ∧ ClosedW ∧ LevHaar ∧ HaarWExists ∧ HaarNExists ∧
    HaarGExists ∧ HeisAct

def IW : Prop :=
  ∀ (k r : ℕ) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ), 1 ≤ k → LinearIndependent ℂ Y →
    (∀ a b, herm (Hpk k r) (Y a) (Y b) = 0) →
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, Y a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l Y

def TLeft : Prop :=
  ∀ (k r : ℕ) (s : Fin (r + 1) → ℝ) (μG : Measure (Mt k r)) (Φ : Mt k r → ℝ≥0∞), 1 ≤ k → IsHaarOn (GV k r) μG →
    Measurable Φ → (∀ κ ∈ Kset k r, ∀ g, Φ (lmulM κ g) = Φ g) → ∀ x ∈ GV k r,
      (∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG) = ENNReal.ofReal (fsR k r s x) * ∫⁻ g, Φ g * FsE k r s (Matrix.of g) ∂μG

def TBoth : Prop :=
  ∀ (k r : ℕ) (s : Fin (r + 1) → ℝ) (μG : Measure (Mt k r)) (Φ : Mt k r → ℝ≥0∞), 1 ≤ k → IsHaarOn (GV k r) μG →
    Measurable Φ → (∀ κ ∈ Kset k r, ∀ g, Φ (lmulM κ g) = Φ g ∧ Φ (rmulF κ g) = Φ g) → ∀ x ∈ GV k r, ∀ y ∈ GV k r,
      (∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * y) ∂μG) =
        ENNReal.ofReal (fsR k r s x * fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (Matrix.of g) ∂μG

def DET : Prop :=
  ∀ (k r : ℕ) (s : Fin (r + 1) → ℝ) (A : ℝ), 1 ≤ k → (∀ l, 0 ≤ s l) → ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ A →
    ∃ C : ℝ≥0, ∀ h ∈ GV k r, ENNReal.ofReal (gN h ^ (-A)) ≤ (C : ℝ≥0∞) * FsE k r s h

def CoefStep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ)
    (s : Fin (r + 1) → ℝ), SAdm k r s → AB k r ≤ A → JInt D.μG A s < ∞ → CoefBound D (xiN k r s) A

def XiIntStep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (s : Fin (r + 1) → ℝ), SAdm k r s → IInt D.μN D.z s (1 / 2) < ∞ → IInt D.μN D.z' s (1 / 2) < ∞ →
      XiInt D (xiN k r s) 2

def hcoord (k r' : ℕ) (x : HPar k r') : Xp (1 + r') (k - 1) :=
  let a : Fin (1 + r') → ℂ := fun j => herm (Hpk k r') x.1 (phiV k r' (Fin.cast (by omega) j))
  let a' : Fin (1 + r') → ℂ := fun j => herm (Hpk k r') x.1 (phiV' k r' (Fin.cast (by omega) j))
  (a, a', (fun i : Fin (k - 1) => x.1 (wI k r' ⟨i.val + 1, by omega⟩)),
    x.2 + (∑ j, a' j * star (a j)).im)

def FormulaF : Prop :=
  ∀ k r' : ℕ, 1 ≤ k →
    (∀ (x : HPar k r') (l : Fin (1 + r' + 1)), Del k (1 + r') l (heis0 k r' x) = de (hcoord k r' x) l) ∧
    MeasurePreserving (hcoord k r') volume volume

def AStepSucc : Prop := ∀ k r r' : ℕ, r = 1 + r' → 1 ≤ k → AAt k r' → AAt k r

def AStepBase : Prop := ∀ k : ℕ, 1 ≤ k → AAt k 0

def BStepSucc : Prop := ∀ k r r' : ℕ, r = 1 + r' → 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r' (δ / 4) → BAt k r δ

def BStepBase : Prop := ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → BAt k 0 δ

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
