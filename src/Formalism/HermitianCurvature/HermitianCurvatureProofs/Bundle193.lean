module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle182
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatQMinOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle183
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def colsVm (k r m : ℕ) (j : Fin m) : Fin (2 * r + k + 1) := ⟨2 * r + k - (r - 1 - j.val), by omega⟩

def kvM (k r m : ℕ) (w : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  qminorOp (Q.EH k r) (colsVm k r m) (colsVm k r m) w F

def kvTop (k r : ℕ) (y : ℂ) : ℂ := (y - ((2 * r + k : ℕ) : ℂ) / 2) + ((r : ℕ) : ℂ) - 1

def pbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then pbOp ⟨i, h⟩ f else 0

def cbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbOp ⟨i, h⟩ f else 0

def cbiN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbiOp ⟨i, h⟩ f else 0

def kvP (r : ℕ) (w : ℂ) : ℕ → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X) × (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0 => (fun f => f, fun _ => 0)
  | m + 1 =>
    (fun f => (kvP r w m).1 (fun c => (w - (m : ℂ)) • f c - pbN r (r - m - 1) f c) -
        cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f)),
      (kvP r w m).1)

def kvC (r : ℕ) (w : ℂ) (m : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := (kvP r w m).1 f

def gaugeF (k r : ℕ) (c : Fin r → ℂ) : ℂ := Q.resG k r (Fin.last r) (fun _ => (1 : ℂ)) c 1

end defs

def TVCoef : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          drbF P.r c • kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g)

def TVGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) c

def TVCrd : Prop :=
  ∀ (k r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (y : ℂ) (Φ : (Fin r → ℂ) → X)
    (U : Set (Fin r → ℂ)) (c : Fin r → ℂ), IsOpen U → U ⊆ OmX r → c ∈ U →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c' => gaugeF k r c' • Φ c') U →
      gaugeF k r c • kvC r (kvTop k r y) r Φ c = (vABm r y r).1 (fun c' => gaugeF k r c' • Φ c') c


open scoped ContDiff in
theorem jDACapTodaV_of_parts (h1 : TVCoef) (h2 : TVGrp) (h3 : TVCrd) : JDACapTodaV := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have e1 := h1 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have e2 := h2 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (Gauge.OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Gauge.OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
    (Fin.last P.r)).1
  obtain ⟨U, F, hUo, hx0, hF, hFeq⟩ := hfam (c, g) ⟨hc, hcg⟩ hg
  have hemb : ContDiff ℝ ∞ (fun c' : Fin P.r → ℂ => (c', g)) := contDiff_id.prodMk contDiff_const
  set U' : Set (Fin P.r → ℂ) := {c' | (c', g) ∈ U} ∩ OmX P.r with hU'
  have hU'o : IsOpen U' := (hUo.preimage hemb.continuous).inter (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX P.r)
  have hgauge : ∀ c' : Fin P.r → ℂ, gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g) =
      Q.resG P.k P.r (Fin.last P.r) J c' g := by
    intro c'
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' := by
    refine ((hF.comp (s := U') hemb.contDiffOn (fun c' hc' => hc'.1))).congr (fun c' hc' => ?_)
    rw [hgauge c']
    exact hFeq (c', g) hc'.1 hg
  have e3 := h3 P.k P.r (Wq →L[ℂ] Wp) y (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' c hU'o
    (fun _ h => h.2) ⟨hx0, hc⟩ hsm
  have hfun : (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) =
      fun c' => Q.resG P.k P.r (Fin.last P.r) J c' g := funext hgauge
  rw [hfun] at e3
  simp only [dMul, Q.crd, Q.cmp, if_true]
  rw [← e3]
  have hres : Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
      gaugeF P.k P.r c • capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) := by
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  rw [hres, e1, e2, smul_comm]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

theorem exists_polyOp_qminor_sum {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : ι → Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) (a j) (b j) u F g := by
  have h := fun j => qminorWordSum k r t (a j) (b j) u
  choose L hL hE using h
  let Θ₁ : B.DiffOp k r Wp Wq :=
    s.toList.flatMap fun j => (L j).map fun cw => pTerm (fun g => β j g * cw.1) cw.2
  let T₀ : B.DTerm k r Wp Wq := pTerm (fun _ => 0) (List.replicate t 0)
  have hT₀ : T₀.word = List.replicate t 0 := pTerm_word (fun X hX => by
    rw [List.eq_of_mem_replicate hX]; exact inLie_zero)
  refine ⟨Θ₁ ++ [T₀], ?_, ?_, ?_⟩
  · intro Tm hTm
    rcases List.mem_append.1 hTm with h1 | h1
    · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h1
      obtain ⟨j, hj, cw, hcw, rfl⟩ := h1
      refine ⟨(pTerm_word_le _ _).trans (hL j cw hcw).2, fun g => β j g * cw.1, ?_, fun g => rfl, fun g => rfl⟩
      have := Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (hβ j hj) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const cw.1 0)
      simpa using this
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => ?_, fun g => ?_⟩
      · simp [T₀, pTerm]
      · simp [T₀, pTerm]
  · unfold B.opOrder
    apply foldr_max_eq
    · intro x hx
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨Tm, hTm | rfl, rfl⟩ := hx
      · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hTm
        obtain ⟨j, _, cw, hcw, rfl⟩ := hTm
        exact (pTerm_word_le _ _).trans (hL j cw hcw).2
      · rw [hT₀]; simp
    · simp only [List.mem_map, List.mem_append, List.mem_singleton]
      exact ⟨T₀, Or.inr rfl, by rw [hT₀]; simp⟩
  · intro UU F hF g hgU hg
    have hT₀a : T₀.coef g (B.Rw T₀.word F g) = 0 := by
      simp [T₀, pTerm]
    simp only [B.opApply, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hT₀a,
      add_zero, Θ₁]
    rw [sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE j _ UU F hF g hgU hg, List.map_map, ← sum_map_mul_smul]
    congr 1
    apply List.map_congr_left
    intro cw hcw
    simp only [Function.comp_apply]
    rw [pTerm_word (fun X hX => ((hL j cw hcw).1 X hX).1)]
    change ((β j g * cw.1) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw cw.2 F g) = _
    rfl

end Formalism.FourierDecayAlt.P.CutMP.QMinOp

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

noncomputable section

theorem capBeta_pd (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capBeta k r c) := by
  unfold capBeta
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a)))) fun a l => ?_
  simp only [Matrix.of_apply, herm, dotProduct, Matrix.mulVec]
  refine pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun j _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun c _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul (pd_entry _ _) (pd_const _ 0))

theorem capAlphaV_pd (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capAlphaV k r B) := by
  unfold capAlphaV
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)) fun a l => ?_
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine pd_sum _ fun m _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  refine pd_sum _ fun l _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem capelli_representation_holds : JDACapRep := by
  intro k r Wp Wq _ _ _ _ _ y
  classical
  have hκ : r ≤ (r + 1) * (2 * r + k + 1) := by nlinarith
  have ho : r ≤ 2 * r + k + 1 := by omega
  obtain ⟨Θ, hP, hO, hE⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun c : Fin r → Fin (2 * r + k + 1) => StrictMono c) (fun _ => C3.xR k r r le_rfl)
    (fun c => c) (capBeta k r) (fun c _ => capBeta_pd k r c) (Q.uC k r 0 y)
  obtain ⟨Θv, hPv, hOv, hEv⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun B : Fin r → Fin (2 * r + k + 1) => StrictMono fun l => C3.keyS k r (B l)) (fun B => B)
    (fun _ => C3.sR k r r le_rfl) (capAlphaV k r) (fun B _ => capAlphaV_pd k r B)
    (y - ((2 * r + k : ℕ) : ℂ) / 2 + (r : ℂ) - 1)
  refine ⟨Θ, Θv, QMinOp.polyOp_mono hP ho hκ, QMinOp.polyOp_mono hPv ho hκ, hO, hOv, fun F g hg hF => ?_,
    fun F g hg hF => ?_⟩
  · rw [hO] at hF
    rw [hE {g} F hF g rfl hg, Finset.sum_filter]
    rfl
  · rw [hOv] at hF
    rw [hEv {g} F hF g rfl hg, Finset.sum_filter]
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hg
    simp only [capAv, C3.AAvop, capAlphaV, hinv]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section vfw

variable {d : ℕ}

def vfD (V : (Fin d → ℝ) → (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  fun x => fderiv ℝ u x (V x)

def vfW : List ((Fin d → ℝ) → (Fin d → ℝ)) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | V :: Vs, u => vfD V (vfW Vs u)

abbrev WOp (d : ℕ) := List (ℂ × List ((Fin d → ℝ) → (Fin d → ℝ)))

def WOp.app (P : WOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  (P.map fun t => t.1 * vfW t.2 u x).sum

def WOp.symb (P : WOp d) (m : ℕ) (x ξ : Fin d → ℝ) : ℂ :=
  (P.map fun t => if t.2.length = m then t.1 * (t.2.map fun V => ((ξ ⬝ᵥ V x : ℝ) : ℂ)).prod else 0).sum

end vfw

def VOpToSOp : Prop :=
  ∀ (d m : ℕ) (P : WOp d) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ t ∈ P, t.2.length ≤ m ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) →
    ∃ S : SOp d, S.ord = m ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ (m : WithTop ℕ∞) u O → ∀ x ∈ O, S.app u x = WOp.app P u x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb P m x ξ

def IsChart (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)) : Prop :=
  IsOpen O ∧ IsOpen U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def VR {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (κ x * X)

def VL {k r d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (X : B.Mat k r) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  fun x => fderiv ℝ Φ (κ x) (X * κ x)

def ChartSysW : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → WOp d) (m : ι → ℕ),
      (∀ j, m j ≤ 2 * r + k + 1) ∧ (∀ j, ∀ t ∈ P j, t.2.length ≤ m j ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, WOp.app (P j) (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, WOp.symb (P j) (m j) x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

theorem chartEqs_of (hA : ChartSysW) (hB : VOpToSOp) : ChartEqs := by
  intro k r z z' d O U κ Φ u hk hz hz' hT hT' hO hU hκ hΦ hκO hΦU hOm hG
  obtain ⟨ι, hι, P, m, hm, hP, huc, hPu, hsym⟩ :=
    hA k r z z' d O U κ Φ u hk hz hz' hT hT' ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ hOm hG
  have hS : ∀ j, ∃ S : SOp d, S.ord = m j ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ v : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((m j : ℕ) : WithTop ℕ∞) v O → ∀ x ∈ O,
        S.app v x = WOp.app (P j) v x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = WOp.symb (P j) (m j) x ξ :=
    fun j => hB d (m j) (P j) O hO (hP j)
  choose S hSo hSc hSa hSs using hS
  refine ⟨ι, hι, S, fun j => hSc j, fun j => by rw [hSo j]; exact hm j, huc, ?_, ?_⟩
  · intro j x hx
    rw [hSa j _ (huc.of_le (by exact_mod_cast hm j)) x hx]
    exact hPu j x hx
  · intro x hx ξ hξ hall
    exact hsym x hx ξ hξ (fun j => by rw [← hSs j x hx ξ]; exact hall j)

def ChartCov : Prop :=
  ∀ (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)), IsChart k r d O U κ Φ →
    ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ∃ Ξ₀ : B.Mat k r, B.inLie k r Ξ₀ ∧ (ξ ≠ 0 → Ξ₀ ≠ 0) ∧
      ∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re

def RwChart : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u →
    ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
    (∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VR κ Φ X) O ∧ ContDiffOn ℝ ∞ (VL κ Φ X) O) ∧
    ∀ Xs : List (B.Mat k r), (∀ X ∈ Xs, B.inLie k r X) → Xs.length ≤ 2 * r + k + 1 → ∀ x ∈ O,
      B.Rw Xs u (κ x) = vfW (Xs.map (VR κ Φ)) (fun y => u (κ y)) x ∧
      Xs.foldr Q.LdV u (κ x) = vfW (Xs.map (VL κ Φ)) (fun y => u (κ y)) x

def LieNFin : Prop :=
  ∀ (k r : ℕ), ∃ (q : ℕ) (Xs : Fin q → B.Mat k r), (∀ i, Xs i ∈ JfS.lieOf (Nset k r)) ∧
    ∀ X ∈ JfS.lieOf (Nset k r), B.inLie k r X ∧ ∃ a : Fin q → ℝ, X = ∑ i, ((a i : ℝ) : ℂ) • Xs i

def CapWords : Prop :=
  ∀ (k r j : ℕ), 1 ≤ j → j ≤ 2 * r + k + 1 →
    ∃ (Ys : Fin (2 * r + k + 2) → ℝ) (lam : Fin (2 * r + k + 2) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.CV k r (Ys i : ℂ) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * Ξ.charpoly.coeff (2 * r + k + 1 - j)

def cmp {k r : ℕ} (Ξ : B.Mat k r) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun a b => Matrix.trace (Ξ * Q.unitB (Hpk k r) Bs a b)

def CapRWords : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z'] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capR k r Bs (ws i) f g = (L.map fun t => t.1 • B.Rw t.2 f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CapLWords : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), Q.IsFrameOf k r [z] Bs →
    ∀ j, 1 ≤ j → j ≤ k →
    ∃ (ws : Fin (k + 1) → ℂ) (lam : Fin (k + 1) → ℂ) (L : List (ℂ × List (B.Mat k r))) (cj : ℂ),
      cj ≠ 0 ∧ (∀ t ∈ L, t.2.length ≤ j ∧ ∀ X ∈ t.2, B.inLie k r X) ∧
      (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          ∑ i, lam i • Q.capLft k r Bs (ws i) f g = (L.map fun t => t.1 • t.2.foldr Q.LdV f g).sum) ∧
      ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
        (L.map fun t => if t.2.length = j then t.1 * (t.2.map fun X => Matrix.trace (Ξ * X)).prod else 0).sum =
          cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def CmpZero : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    Q.IsFrameOf k r [z] Bs → ∀ Ξ : B.Mat k r, B.inLie k r Ξ →
    (∀ j, 1 ≤ j → j ≤ k → (cmp Ξ Bs).charpoly.coeff (k - j) = 0) →
    ∀ X ∈ JfS.lieOf (UWset k r z), (Matrix.trace (Ξ * X)).re = 0

def FrameEx : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs

def ChartSysWOfParts : Prop :=
  ChartCov → RwChart → LieNFin → CapWords → CapRWords → CapLWords → CmpZero → FrameEx → ChartSysW

theorem chartEqs_of_parts (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hB : VOpToSOp) : ChartEqs :=
  chartEqs_of (hJ h1 h2 h3 h4 h5 h6 h7 h8) hB

def SOpField : Prop :=
  ∀ (d : ℕ) (S : SOp d) (V : (Fin d → ℝ) → (Fin d → ℝ)) (O : Set (Fin d → ℝ)), IsOpen O →
    (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) → ContDiffOn ℝ ∞ V O →
    ∃ S' : SOp d, S'.ord = S.ord + 1 ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ ((S.ord + 1 : ℕ) : WithTop ℕ∞) u O → ∀ x ∈ O,
        S'.app u x = vfD V (S.app u) x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S'.symb x ξ = ((ξ ⬝ᵥ V x : ℝ) : ℂ) * S.symb x ξ

def SOpLift : Prop :=
  ∀ (d : ℕ) (S : SOp d) (m' : ℕ) (O : Set (Fin d → ℝ)), S.ord ≤ m' → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    ∃ S' : SOp d, S'.ord = m' ∧ (∀ i w, ContDiffOn ℝ ∞ (S'.a i w) O) ∧ (∀ u x, S'.app u x = S.app u x) ∧
      ∀ x ξ, S'.symb x ξ = if S.ord = m' then S.symb x ξ else 0

def SOpLin : Prop :=
  ∀ (d : ℕ) (S T : SOp d) (c : ℂ) (O : Set (Fin d → ℝ)), S.ord = T.ord → (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) →
    (∀ i w, ContDiffOn ℝ ∞ (T.a i w) O) →
    ∃ R : SOp d, R.ord = S.ord ∧ (∀ i w, ContDiffOn ℝ ∞ (R.a i w) O) ∧
      (∀ u x, R.app u x = c * S.app u x + T.app u x) ∧ ∀ x ξ, R.symb x ξ = c * S.symb x ξ + T.symb x ξ

def VOpToSOpOfSteps : Prop := SOpField → SOpLift → SOpLin → VOpToSOp

theorem chartEqs_of_all (hJ : ChartSysWOfParts) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords)
    (h5 : CapRWords) (h6 : CapLWords) (h7 : CmpZero) (h8 : FrameEx) (hS : VOpToSOpOfSteps) (s1 : SOpField)
    (s2 : SOpLift) (s3 : SOpLin) : ChartEqs :=
  chartEqs_of_parts hJ h1 h2 h3 h4 h5 h6 h7 h8 (hS s1 s2 s3)

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem coefficient_vector_commutation : CVComm := by
  intro k r Wp Wq _ _ _ _ _ _ s Y Y' F hF g hg
  have hs : ∀ (Z α : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)),
      Q.CV k r Z (α • f) = α • Q.CV k r Z f := fun Z => P5.tL_smulC 0 0 0 Z 0 0
  have hsm : Q.SmoothLev k r 0 Set.univ F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hF g₀ ((CapelliUnderIntegral.glev0 g₀).1 hg₀.1)
    exact ⟨U, f', hU, hgU, hc, fun x hx hxl => he x hx ((CapelliUnderIntegral.glev0 x).1 hxl)⟩
  have hc := capelli_commutation _ k r 0 Set.univ F isOpen_univ hsm g
    ⟨(CapelliUnderIntegral.glev0 g).2 hg, trivial⟩ (Q.uC k r 0 Y) (Q.uC k r 0 Y')
  simp only [Pi.smul_apply, hs]
  exact congrArg (fun t => s • s • t) hc

end Formalism.FourierDecayAlt.P.CutMP.ER
end
