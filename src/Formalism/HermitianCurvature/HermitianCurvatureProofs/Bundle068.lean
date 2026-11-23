module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormCvecSq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle063
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Formalism.HermitianCurvature.Bundle004
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem norm_sum_le_of_gram' {ι κ I : Type} [Fintype I] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (v : ι → H) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Y : I → ι → W) (J : Finset κ) (P : κ → ι)
    (hk : ∀ j ∈ J, ∀ l ∈ J, ⟪v (P j), v (P l)⟫_ℂ = ∑ i, (c i : ℂ) * ⟪Y i (P j), Y i (P l)⟫_ℂ) (a : κ → ℂ) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ ∑ i, √(c i) * ‖∑ j ∈ J, a j • Y i (P j)‖ := by
  set u := ∑ j ∈ J, a j • v (P j) with hu
  set y : I → W := fun i => ∑ j ∈ J, a j • Y i (P j) with hy
  have hinner : ⟪u, u⟫_ℂ = ∑ i, (c i : ℂ) * ⟪y i, y i⟫_ℂ := by
    have e1 : ⟪u, u⟫_ℂ = ∑ j ∈ J, ∑ l ∈ J, ∑ i,
        (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) := by
      show ⟪∑ j ∈ J, a j • v (P j), ∑ j ∈ J, a j • v (P j)⟫_ℂ = _
      rw [sum_inner]
      simp_rw [inner_sum, inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
      rw [hk j hj l hl, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have e2 : ∑ i, (c i : ℂ) * ⟪y i, y i⟫_ℂ = ∑ i, ∑ j ∈ J, ∑ l ∈ J,
        (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      show (c i : ℂ) * ⟪∑ j ∈ J, a j • Y i (P j), ∑ j ∈ J, a j • Y i (P j)⟫_ℂ = _
      rw [sum_inner]
      simp_rw [inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
    rw [e1, e2]
    calc _ = ∑ j ∈ J, ∑ i, ∑ l ∈ J, (c i : ℂ) * (conj (a j) * (a l * ⟪Y i (P j), Y i (P l)⟫_ℂ)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hsq : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E), ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
    intro E _ _ x
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hle : ‖u‖ ^ 2 ≤ ∑ i, (√(c i) * ‖y i‖) ^ 2 := by
    rw [← hsq u, hinner]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, hsq, mul_pow, Real.sq_sqrt (hc i), Complex.norm_real, Real.norm_of_nonneg (hc i)]
  have hsum : ∑ i, (√(c i) * ‖y i‖) ^ 2 ≤ (∑ i, √(c i) * ‖y i‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hnn : 0 ≤ ∑ i, √(c i) * ‖y i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  calc ‖u‖ = √(‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √((∑ i, √(c i) * ‖y i‖) ^ 2) := Real.sqrt_le_sqrt (hle.trans hsum)
    _ = ∑ i, √(c i) * ‖y i‖ := Real.sqrt_sq hnn

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]

theorem cvec_utT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (x : ℂ) (hx : x ≠ 0) (cc : ℂ) :
    PBK.cvec s (utT p N c Fi L s h) x cc = vecT p N c Fi L ((h ++ [(s - 1, x⁻¹)]) ++ [(1, cc)]) := by
  have hx' : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hn : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  rw [PBK.cvec, utT, smul_smul, mul_div_cancel₀ cc hx', ← Complex.ofReal_mul, inv_mul_cancel₀ hn,
    Complex.ofReal_one, one_smul]
  simp

theorem inner_vecT_np (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq)
    (hV : VecHyp p nn F w c Fi L) (Q Q' : C.LPt) :
    ⟪vecT p w.length c Fi L Q, vecT p w.length c Fi L Q'⟫_ℂ = TBB.NP p nn F (P.r + 1) w Q' Q := by
  rw [inner_vecT p w.length c hV.hc Fi L Q Q', hV.gram Q' Q]

end place

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section

open Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SAPairOne : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), IsAAOp S T v Θ →
      ∀ K ∈ smoothFormsPositiveCone S T v, ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ K ∈ smoothFormsPositiveCone S T v → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
        (∀ π, trJ S T v e K π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) →
        (∀ π, trJ S T v e (B.opApply Θ K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (B.opAdj Θ J))

def SAZero : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ X ∈ smoothFormsPositiveCone S T v, ∀ y (hy : y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
        (∀ π, ((trJ S T v e X π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) ⟨y, hy⟩ = 0) →
          X (B.gq (T v).base y) = 0

def SALocal : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ → ∀ K ∈ smoothFormsPositiveCone S T v,
      ∀ V : Set (MA.E (D.parOf S v).r), IsOpen V → V ⊆ MA.Qset (D.parOf S v).r (D.parOf S v).TT → (∀ y ∈ V, K (B.gq (T v).base y) = 0) →
        ∀ y ∈ V, B.opApply Θ K (B.gq (T v).base y) = 0

def SAExh : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ X ∈ smoothFormsPositiveCone S T v, ∀ Cs : Set (MA.E (D.parOf S v).r), IsCompact Cs → Cs ⊆ MA.Qset (D.parOf S v).r (D.parOf S v).TT →
      ∃ (F : GFn S v) (U : Set (MA.E (D.parOf S v).r)), IsOpen U ∧ Cs ⊆ U ∧ B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧
        HasCompactSupport F ∧ tsupport F ⊆ OmP S T v ∧
        ∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, (y ∈ U → B.JF (T v).base F (B.gq (T v).base y) = X (B.gq (T v).base y)) ∧
          (X (B.gq (T v).base y) = 0 → B.JF (T v).base F (B.gq (T v).base y) = 0)

def SAJCommC : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ →
      ∀ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F → HasCompactSupport F → tsupport F ⊆ OmP S T v →
      ∀ (U : Set (MA.E (D.parOf S v).r)) (X : GFn S v), IsOpen U → X ∈ smoothFormsPositiveCone S T v →
        (∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, y ∈ U → X (B.gq (T v).base y) = B.JF (T v).base F (B.gq (T v).base y)) →
        ∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, y ∈ U →
          B.opApply Θ X (B.gq (T v).base y) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base y) ∧
          B.opAdj Θ X (B.gq (T v).base y) = B.JF (T v).base (B.opAdj Θ F) (B.gq (T v).base y)

def CompactSupportClassMembership : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ →
      ∀ F F' : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F → HasCompactSupport F → tsupport F ⊆ OmP S T v →
        B.CkOn ⊤ (B.GV S.G.k S.G.r) F' → HasCompactSupport F' → tsupport F' ⊆ OmP S T v →
        B.InCC (B.AB S.G.k S.G.r) 5 F ∧ B.InCC (B.AB S.G.k S.G.r) 5 F' ∧
          B.InCC (B.AB S.G.k S.G.r) 5 (B.opApply Θ F) ∧ B.InCC (B.AB S.G.k S.G.r) 5 (B.opAdj Θ F') ∧
          B.beta (T v).base (B.opApply Θ F) F' = B.beta (T v).base F (B.opAdj Θ F')

theorem sAPairL_of_one (hF : JAFFStable) (h1 : SAPairOne) : SAPairL := by
  obtain ⟨C1, hF'⟩ := hF
  obtain ⟨C2, h1'⟩ := h1
  refine ⟨max C1 C2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he Θs hΘs K hK J hJ hKt
  have hB1 : BuiltOW C1 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_left _ _) hB.1, hB.2⟩
  have hB2 : BuiltOW C2 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_right _ _) hB.1, hB.2⟩
  have stab := hF' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v
  have hmem : ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      applyL S v Θs K ∈ smoothFormsPositiveCone S T v := by
    intro Θs
    induction Θs with
    | nil => intro _; exact hK
    | cons Θ Θs ih =>
      intro h
      exact (stab Θ (h Θ (by simp)) _ (ih fun Θ' hΘ' => h Θ' (by simp [hΘ']))).1
  have key : ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      ∀ J ∈ smoothFormsPositiveCone S T v,
        (∀ π, trJ S T v e (applyL S v Θs K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (applyL S v Θs K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v Θs J)) := by
    intro Θs
    induction Θs with
    | nil => intro _ J _; exact ⟨hKt, rfl⟩
    | cons Θ Θs ih =>
      intro h J hJ
      have hΘ : IsAAOp S T v Θ := h Θ (by simp)
      have hrest : ∀ Θ' ∈ Θs, IsAAOp S T v Θ' := fun Θ' hΘ' => h Θ' (by simp [hΘ'])
      have hX := hmem Θs hrest
      obtain ⟨ihT, ihE⟩ := ih hrest (B.opAdj Θ J) (stab Θ hΘ J hJ).2
      obtain ⟨hT, hE⟩ := h1' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e he Θ hΘ (applyL S v Θs K) hX J hJ
        (stab Θ hΘ _ hX).1 (stab Θ hΘ J hJ).2 ihT
      exact ⟨hT, hE.trans ihE⟩
  exact key Θs hΘs J hJ

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MeasureTheory
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.MAx2.Adj

noncomputable section

section fund

variable {r : ℕ} {TT : ℝ}

theorem dR_pos {x : E r} (hx : x ∈ Qset r TT) : 0 < dR x := by
  unfold dR
  exact Finset.prod_pos fun l _ => inv_pos.2 (Complex.normSq_pos.2 (hx.1 l))

theorem dR_nonneg (x : E r) : 0 ≤ dR x := by
  unfold dR
  exact Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)

theorem dR_continuousAt {x : E r} (hx : x ∈ Qset r TT) : ContinuousAt (dR (r := r)) x := by
  unfold dR
  refine tendsto_finsetProd _ fun l _ => ?_
  exact ((Complex.continuous_normSq.comp ((continuous_apply l).comp continuous_fst)).continuousAt).inv₀
    (Complex.normSq_pos.2 (hx.1 l)).ne'

def ofAmb (χ : E r → ℝ) (hχ : ContDiff ℝ sm χ) : SmQ r TT :=
  ⟨fun q => ((χ q.1 : ℝ) : ℂ),
    ((Complex.ofRealCLM.contDiff.comp hχ).contDiffOn).congr fun x hx => by simp [MA.ext, hx]⟩

theorem fund0 (h : SmQ r TT) (hh : ∀ V ∈ Test r TT, ip0 h V = 0) : h = 0 := by
  apply S_ext
  intro q0
  show (h : Qp r TT → ℂ) q0 = 0
  by_contra hne
  have hQ : Qset r TT ∈ nhds q0.1 := (Qset_open r TT).mem_nhds q0.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hQ
  let b : ContDiffBump q0.1 := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩
  have hts : tsupport b ⊆ Qset r TT := fun x hx => by
    rw [b.tsupport_eq] at hx
    exact hball (Metric.closedBall_subset_ball (show (2 * ε / 3 : ℝ) < ε by linarith) hx)
  have hbc : ContDiff ℝ sm (fun x => b x) := b.contDiff
  set χQ : SmQ r TT := ofAmb (fun x => b x) hbc with hχQ
  have hextχ : MA.ext (χQ : Qp r TT → ℂ) = fun x => ((b x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ Qset r TT
    · simp [MA.ext, hx, hχQ, ofAmb]
    · have : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hx (hts h'))
      simp [MA.ext, hx, this]
  have hχT : χQ ∈ Test r TT := by
    refine ⟨?_, ?_⟩
    · rw [hextχ]; exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · rw [hextχ]; exact (tsupport_comp_subset Complex.ofReal_zero _).trans hts
  have hVT : χQ * h ∈ Test r TT := test_mul_right hχT h
  have h0 := hh _ hVT

  set G : E r → ℝ := fun x => dR x * (b x * ‖MA.ext (h : Qp r TT → ℂ) x‖ ^ 2) with hG
  have hint : ip0 h (χQ * h) = ((∫ x, G x : ℝ) : ℂ) := by
    unfold ip0
    rw [integral_base_measure, ← integral_complex_ofReal]
    congr 1
    funext x
    by_cases hx : x ∈ Qset r TT
    · simp only [MA.ext, hx, dif_pos, hG, hχQ, ofAmb]
      simp only [Subalgebra.coe_mul, Pi.mul_apply, map_mul, Complex.conj_ofReal]
      push_cast
      rw [← Complex.mul_conj']
      ring
    · simp [MA.ext, hx, hG]
  rw [hint] at h0
  have hG0 : (∫ x, G x) = 0 := by exact_mod_cast h0
  have hcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ Qset r TT
    · have hh' : ContinuousAt (MA.ext (h : Qp r TT → ℂ)) x :=
        ((h.2 : ContDiffOn ℝ sm (MA.ext (h : Qp r TT → ℂ)) (Qset r TT)).continuousOn.continuousAt
          ((Qset_open r TT).mem_nhds hx))
      exact (dR_continuousAt hx).mul (b.continuous.continuousAt.mul (hh'.norm.pow 2))
    · have hx' : x ∉ tsupport b := fun h' => hx (hts h')
      have hev : G =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hx')] with y hy
        simp [hG, show b y = 0 from hy]
      exact (continuousAt_const).congr hev.symm
  have hcs : HasCompactSupport G := by
    apply HasCompactSupport.intro (isCompact_closedBall q0.1 (2 * ε / 3))
    intro x hx
    have : b x = 0 := by
      by_contra hb
      have hxs : x ∈ Function.support b := Function.mem_support.2 hb
      rw [b.support_eq] at hxs
      exact hx (Metric.ball_subset_closedBall hxs)
    simp [hG, this]
  have hnn : 0 ≤ G := fun x => mul_nonneg (dR_nonneg x) (mul_nonneg b.nonneg (sq_nonneg _))
  have hpos0 : G q0.1 ≠ 0 := by
    have hb1 : b q0.1 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    have he : MA.ext (h : Qp r TT → ℂ) q0.1 = (h : Qp r TT → ℂ) q0 := by simp [MA.ext, q0.2]
    simp only [hG, hb1, one_mul, he]
    exact (mul_pos (dR_pos q0.2) (pow_pos (norm_pos_iff.2 hne) 2)).ne'
  have := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure (E r))) hcs hnn hpos0
  linarith

theorem inner_product_sub_left {f g V : SmQ r TT} (hV : V ∈ Test r TT) : ip0 (f - g) V = ip0 f V - ip0 g V := by
  rw [inner_conj_symm_alt, sub_eq_add_neg, inner_add_right_alt hV, inner_neg_right_alt, map_add (f := _), map_neg, ← inner_conj_symm_alt, ← inner_conj_symm_alt,
    ← sub_eq_add_neg]

end fund

open Classical in
theorem fundamental_quadratic_identity : SAFundQ := by
  intro P u w h
  funext π
  have key : ∀ V ∈ MA.Test P.r P.TT, MA.ip0 (u π - w π) V = 0 := by
    intro V hV
    have hU : ∀ π', (fun π'' => if π'' = π then V else 0) π' ∈ MA.Test P.r P.TT := by
      intro π'
      by_cases hπ : π' = π
      · simp [hπ, hV]
      · simp [hπ, test_zero]
    have h1 := h _ hU
    have hs : ∀ x : M.Ty P → MA.SmQ P.r P.TT,
        MA.ipA P x (fun π'' => if π'' = π then V else 0) = MA.ip0 (x π) V := by
      intro x
      unfold MA.ipA
      rw [Finset.sum_eq_single π (fun b _ hb => by simp [hb, inner_zero_right_alt]) (by simp)]
      simp
    rw [hs, hs] at h1
    rw [inner_product_sub_left hV, h1, sub_self]
  exact sub_eq_zero.1 (fund0 _ key)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordIntegralScaling

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem int_list {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (L : ι → E →L[ℂ] E) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => L i (φ i p)).sum) μ ∧
      ∫ p, (l.map fun i => L i (φ i p)).sum ∂μ = (l.map fun i => L i (∫ p, φ i p ∂μ)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : Integrable (φ i) μ := h i (by simp)
    obtain ⟨hl1, hl2⟩ := ih (fun j hj => h j (by simp [hj]))
    have hLi : Integrable (fun p => L i (φ i p)) μ := (L i).integrable_comp hi
    simp only [List.map_cons, List.sum_cons]
    refine ⟨hLi.add hl1, ?_⟩
    rw [integral_add hLi hl1, hl2, ContinuousLinearMap.integral_comp_comm _ hi]

theorem smul_list {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (L : ι → E →L[ℂ] E)
    (x : ι → E) : c • (l.map fun i => L i (x i)).sum = (l.map fun i => L i (c • x i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, smul_add, ih, List.map_cons, List.sum_cons, map_smul]

variable {k r : ℕ}

theorem lr_nrm (v : List (Mat k r)) :
    (B4.lr [] v).map B4.nrm = B4.lr [] (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) := by
  simp [B4.lr, B4.nrm, List.map_map, Function.comp_def]

theorem rw_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (Mat k r)) (f : Mat k r → E) :
    Rw v f = B4.pn (B4.lr [] v) • Rw (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) f := by
  have h := B4.W_nrm (B4.lr [] v) f
  rw [lr_nrm, ← B4.dLR_eq, ← B4.dLR_eq] at h
  exact h

end Formalism.FourierDecayAlt.P.WordIntegralScaling

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end
