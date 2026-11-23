module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SquareIntegrableGammaZetabarInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SAModelAdj : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ a ∈ Submonoid.closure (MA.hatSet P L ∪ MA.bddSet P L), ∀ u U : M.Ty P → MA.SmQ P.r P.TT,
      (∀ π, U π ∈ MA.Test P.r P.TT) → MA.ipA P (MA.actA P (star a) u) U = MA.ipA P u (MA.actA P a U)

def SASection : Prop :=
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
      ∀ U : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT,
        (∀ π, U π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) → ∃ K ∈ smoothFormsPositiveCone S T v, trJ S T v e K = U

def SAPairL : Prop :=
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
      ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      ∀ K ∈ smoothFormsPositiveCone S T v, ∀ J ∈ smoothFormsPositiveCone S T v, (∀ π, trJ S T v e K π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) →
        (∀ π, trJ S T v e (applyL S v Θs K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (applyL S v Θs K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v Θs J))

def SAFundQ : Prop :=
  ∀ (P : M.Par) (u w : M.Ty P → MA.SmQ P.r P.TT),
    (∀ U : M.Ty P → MA.SmQ P.r P.TT, (∀ π, U π ∈ MA.Test P.r P.TT) → MA.ipA P u U = MA.ipA P w U) → u = w

section lin

variable {P : M.Par}

open Formalism.FourierDecayAlt.P.MAx2.Adj

theorem ipA_add_left (u w U : M.Ty P → MA.SmQ P.r P.TT) (hU : ∀ π, U π ∈ MA.Test P.r P.TT) :
    MA.ipA P (u + w) U = MA.ipA P u U + MA.ipA P w U := by
  unfold MA.ipA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  calc MA.ip0 ((u + w) π) (U π) = conj (MA.ip0 (U π) (u π + w π)) := inner_conj_symm_alt _ _
    _ = conj (MA.ip0 (U π) (u π)) + conj (MA.ip0 (U π) (w π)) := by rw [inner_add_right_alt (hU π), map_add (f := _)]
    _ = MA.ip0 (u π) (U π) + MA.ip0 (w π) (U π) := by rw [← inner_conj_symm_alt, ← inner_conj_symm_alt]

theorem ipA_add_right (u X Y : M.Ty P → MA.SmQ P.r P.TT) (hX : ∀ π, X π ∈ MA.Test P.r P.TT)
    (hY : ∀ π, Y π ∈ MA.Test P.r P.TT) : MA.ipA P u (X + Y) = MA.ipA P u X + MA.ipA P u Y := by
  unfold MA.ipA
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  calc MA.ip0 (u π) ((X + Y) π) = conj (MA.ip0 (X π + Y π) (u π)) := inner_conj_symm_alt _ _
    _ = conj (MA.ip0 (X π) (u π)) + conj (MA.ip0 (Y π) (u π)) := by rw [inner_add_left_alt (hX π) (hY π), map_add (f := _)]
    _ = MA.ip0 (u π) (X π) + MA.ip0 (u π) (Y π) := by rw [← inner_conj_symm_alt, ← inner_conj_symm_alt]

theorem ipA_smul_left (c : ℂ) (u U : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P (c • u) U = c * MA.ipA P u U := by
  unfold MA.ipA
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun π _ => inner_smul_left_alt c (u π) (U π)

theorem ipA_smul_right (c : ℂ) (u U : M.Ty P → MA.SmQ P.r P.TT) :
    MA.ipA P u (c • U) = conj c * MA.ipA P u U := by
  unfold MA.ipA
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun π _ => inner_smul_right_alt c (u π) (U π)

theorem ipA_conj (u U : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P u U = conj (MA.ipA P U u) := by
  unfold MA.ipA

  rw [map_sum]
  exact Finset.sum_congr rfl fun π _ => inner_conj_symm_alt _ _

theorem sumAdj (u Ku : M.Ty P → MA.SmQ P.r P.TT) (hKu : ∀ π, Ku π ∈ MA.Test P.r P.TT) {α : Type*} (l : List α)
    (c : α → ℂ) (X Y : α → M.Ty P → MA.SmQ P.r P.TT)
    (h : ∀ x ∈ l, (∀ π, X x π ∈ MA.Test P.r P.TT) ∧ MA.ipA P (X x) u = MA.ipA P Ku (Y x)) :
    (∀ π, (l.map fun x => c x • X x).sum π ∈ MA.Test P.r P.TT) ∧
      MA.ipA P u (l.map fun x => c x • X x).sum = MA.ipA P (l.map fun x => conj (c x) • Y x).sum Ku := by
  induction l with
  | nil =>
    refine ⟨fun π => ?_, ?_⟩
    · simpa using (test_zero : (0 : MA.SmQ P.r P.TT) ∈ MA.Test P.r P.TT)
    · simp [MA.ipA, inner_zero_left_alt, inner_zero_right_alt]
  | cons x l ih =>
    obtain ⟨hX, hXe⟩ := h x (by simp)
    obtain ⟨ihT, ihE⟩ := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨fun π => test_add (test_smul _ (hX π)) (ihT π), ?_⟩
    rw [ipA_add_right u (c x • X x) _ (fun π => test_smul (c x) (hX π)) ihT, ipA_add_left (conj (c x) • Y x) _ Ku hKu, ipA_smul_right,
      ipA_smul_left, ihE, ipA_conj u (X x), hXe, ← ipA_conj]

end lin

theorem jAStarOp_of_parts (hM : SAModelAdj) (hS : SASection) (hP : SAPairL) (hF : SAFundQ) : JAStarOp := by
  obtain ⟨C1, hS'⟩ := hS
  obtain ⟨C2, hP'⟩ := hP
  refine ⟨max C1 C2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L he _ hL a ha ts hts hrep J hJ
  have hB1 : BuiltOW C1 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_left _ _) hB.1, hB.2⟩
  have hB2 : BuiltOW C2 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_right _ _) hB.1, hB.2⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hTTpos : 0 < (D.parOf S v).TT := by rw [hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  apply hF (D.parOf S v)
  intro U hU
  obtain ⟨K, hK, hKU⟩ := hS' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v e he U hU
  subst hKU
  rw [hM _ L hTTpos hL a ha (trJ S T v e J) (trJ S T v e K) hU, (hrep K hK).2]
  exact (sumAdj (trJ S T v e J) (trJ S T v e K) hU ts (fun t => t.1) (fun t => trJ S T v e (applyL S v t.2 K))
    (fun t => trJ S T v e (adjL S v t.2 J))
    (fun t ht => hP' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e he t.2 (hts t ht) K hK J hJ hU)).2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem mulQ_zbP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zbP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = star q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := mul_conjCoordinate_apply P f q

theorem mulQ_zP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := algebraMap_comp_ofPadicInt_apply P f q

theorem mulQ_ggiP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P ((MA.DQ P).ggiP P.TT) f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (f : MA.Qp P.r P.TT → ℂ) q := ggiP_apply P f q

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nabF_phase (P : M.Par) (hTT : 0 ≤ P.TT) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A B u : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hC : ConnF P Bs d e A B) (hu : PhaseEq P A B u) :
    NabF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  intro Φ
  constructor
  · funext ρ
    rw [actA_nabA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).1]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, hA, _⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).1
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Pi.add_apply, Pi.mul_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zbP, mulQ_ggiP, dzQ_apply P hTT, dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).1, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modA at hA
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hA
  · funext ρ
    rw [actA_nabsA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).2]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, _, hB⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).2
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Subalgebra.coe_neg, Pi.add_apply,
      Pi.mul_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zP, mulQ_ggiP, dzbQ_apply P hTT, dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).2, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modB at hB
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hB

end main

theorem gauge_transform_holds : GTCGauge := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk A B' u hAB hC hu
  have hTT : 0 ≤ P.TT := torus_parameter Wp Wq P Bs X d hH
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  exact ⟨isFrameB_phase P Bs e u he hu', kapF_phase P Bs d e u hu' hk,
    nabF_phase P hTT Bs d e A B' u hAB hC hu⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def BddReal (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (Cb : ℝ)
    (b : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) : Prop :=
  ∃ Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), B.opOrder Θ = 0 ∧ IsAAOp S T v Θ ∧
    CutCoef S T v Θ 0 (Cb * ((S.G.r : ℝ) + 1)) ∧
    ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v ∧
      MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J)

end defs

def scalSet (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  {L.ζi, L.ζbi, L.D * L.Dbi, L.Db * L.Di}

def ssnSet (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  (fun i => L.Drb * L.Dri * MA.SS P (MA.DQ P) i) '' Set.Icc 1 (P.k - 1)

def ssnStarSet (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  (fun i => star (L.Drb * L.Dri * MA.SS P (MA.DQ P) i)) '' Set.Icc 1 (P.k - 1)

def BddClassOp (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P))) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc Cb : ℝ, K ≤ Cc → K ≤ Cb → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ b ∈ cls (D.parOf S v) L, BddReal S T v e Cb b

def JABddScal : Prop := BddClassOp scalSet

theorem bddSet_cases (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (b : MA.A P (MA.DQ P))
    (hb : b ∈ MA.bddSet P L) :
    b ∈ scalSet P L ∨ b ∈ Set.range (MA.kap P (MA.DQ P)) ∨ b ∈ ssnSet P L ∨ b ∈ ssnStarSet P L := by
  unfold MA.bddSet at hb
  rcases hb with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

def JABddOpQQ : Prop :=
  ∃ Cc Cb : ℝ, 0 ≤ Cb ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ b ∈ MA.bddSet (D.parOf S v) L, ∃ Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), B.opOrder Θ = 0 ∧ IsAAOp S T v Θ ∧
        CutCoef S T v Θ 0 (Cb * ((S.G.r : ℝ) + 1)) ∧
        ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v ∧
          MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J)

def BddClassOpQQ (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P))) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc Cb : ℝ, K ≤ Cc → K ≤ Cb → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ b ∈ cls (D.parOf S v) L, BddReal S T v e Cb b

theorem bddClassOpQQ_of (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P)))
    (h : BddClassOp cls) : BddClassOpQQ cls := by
  obtain ⟨K, hK, h⟩ := h
  exact ⟨K, hK, fun Cc Cb h1 h2 E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa _ hL =>
    h Cc Cb h1 h2 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL⟩

def JABddKapQQ : Prop := BddClassOpQQ fun P _ => Set.range (MA.kap P (MA.DQ P))

def JABddSSnQQ : Prop := BddClassOpQQ ssnSet

def JABddSSnStarQQ : Prop := BddClassOpQQ ssnStarSet

theorem jABddOpQQ_of_bddLeaves (h1 : JABddScal) (h2 : JABddKapQQ) (h3 : JABddSSnQQ) (h4 : JABddSSnStarQQ) :
    JABddOpQQ := by
  obtain ⟨K1, hK1, h1⟩ := bddClassOpQQ_of scalSet h1
  obtain ⟨K2, hK2, h2⟩ := h2
  obtain ⟨K3, hK3, h3⟩ := h3
  obtain ⟨K4, hK4, h4⟩ := h4
  set K := max (max K1 K2) (max K3 K4) with hK
  have e1 : K1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have e2 : K2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have e3 : K3 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have e4 : K4 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨K, K, le_trans hK1 e1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  rcases bddSet_cases _ L b hb with h | h | h | h
  · exact h1 K K e1 e1 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h
  · exact h2 K K e2 e2 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h
  · exact h3 K K e3 e3 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h
  · exact h4 K K e4 e4 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem hat_nodes_decay_holds : JDHatNodes := by
  intro P
  classical
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = 1 + ∑ π : M.Ty P, ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i| := ⟨_, rfl⟩
  refine ⟨fun j => Mb + ((j : ℕ) : ℝ), fun a b h => ?_, fun j π => ?_⟩
  · dsimp only at h
    have h' : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := add_left_cancel h
    exact Fin.ext (by exact_mod_cast h')
  · unfold M.xC
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have hle : |M.rho P π i| ≤ ∑ π' : M.Ty P, ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π' i'| := by
      calc |M.rho P π i| ≤ ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i'| :=
            Finset.single_le_sum (f := fun i' => |M.rho P π i'|) (fun _ _ => abs_nonneg _) hi
        _ ≤ _ := Finset.single_le_sum (f := fun π' => ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π' i'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ π)
    have hpos : 0 < Mb + ((j : ℕ) : ℝ) + M.rho P π i := by
      have h1 := neg_abs_le (M.rho P π i)
      linarith
    have hc : (((Mb + ((j : ℕ) : ℝ) : ℝ) : ℂ) + ((M.rho P π i : ℝ) : ℂ)) =
        ((Mb + ((j : ℕ) : ℝ) + M.rho P π i : ℝ) : ℂ) := by push_cast; ring
    rw [hc]
    exact Complex.ofReal_ne_zero.2 (ne_of_gt hpos)

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem gl_isLocPt_snoc {a : C.LPt} {j m : ℕ} (ha : D.IsLocPt a j) (hm : 1 ≤ m) {c : ℂ} (hc : c ≠ 0) :
    D.IsLocPt (a ++ [(m, c)]) (j + m) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact ha.1 x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hm, hc⟩
  · rw [← ha.2]
    simp [D.ptSize, List.map_append, List.sum_append]

theorem gl_fsv (σ z : ℂ) : P5.fsv σ z = G.psi (-U.betaU) (1 * σ * z) := by
  rw [TBBx1.fsv_eq]
  unfold G.psi U.betaU Formalism.QuantumDeterminants.cStd
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
  push_cast
  ring

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gl_inner_self (u : H) : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

end vec

end

end Formalism.FourierDecayAlt.P.CutBP
end
