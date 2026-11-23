module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle060
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymExp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle054
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormBasics
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle042
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace FlagGramRestriction

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts

variable {k r : ℕ}

lemma col_mul (M : B.Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (M * gnB k r z z' γ) a j) = M *ᵥ gramVec k r z z' γ j := by
  funext a; simp [gnB, Matrix.mul_apply, Matrix.mulVec, dotProduct]

end FlagGramRestriction

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellOpenDomain

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem qdom_open (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (QDom k r z z') := by
  have h1 : IsOpen {q : (Fin r → ℂ) × ℂ | ∀ a, q.1 a ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
  have h2 : IsOpen {q : (Fin r → ℂ) × ℂ | Tz k r z * Tz k r z' < Complex.normSq q.2} :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  exact h1.inter h2

theorem c_apply (n : ℕ) (a : Fin r) (s : Set ((Fin r → ℂ) × ℂ)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => q.1 a) s :=
  ((contDiff_apply ℝ (fun _ => ℂ) a).comp contDiff_fst).contDiffOn

theorem c_inv (z z' : Fin (2 * r + k + 1) → ℂ) (n : ℕ) (a : Fin r) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => (star (q.1 a))⁻¹) (QDom k r z z') := by
  have h0 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => q.1 a) :=
    (contDiff_apply ℝ (fun _ => ℂ) a).comp contDiff_fst
  have hc : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => star (q.1 a)) :=
    Complex.conjCLE.contDiff.comp h0
  exact hc.contDiffOn.inv (fun q hq => star_ne_zero.2 ((show (∀ a, q.1 a ≠ 0) ∧ _ from hq).1 a))

theorem mu_entry (D : RealPlaceData k r Wp Wq) (n : ℕ) (a b : Fin (k + 1)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => D.μsec q.2 a b) (QDom k r D.z D.z') := by
  have hle : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  exact ((D.sec.1 a b).of_le hle).comp (s := QDom k r D.z D.z') contDiff_snd.contDiffOn fun q hq => hq.2

theorem gq_contDiffOn (D : RealPlaceData k r Wp Wq) (n : ℕ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q => gq D q) (QDom k r D.z D.z') := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  show ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => bigCell k r q.1 (D.μsec q.2) i j) _
  unfold bigCell
  split_ifs <;> first
    | exact contDiffOn_const
    | exact c_apply n _ _
    | exact c_inv D.z D.z' n _
    | exact mu_entry D n _ _

end Formalism.FourierDecayAlt.P.BigCellOpenDomain

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bessel_smooth_of_parts : Formalism.FourierDecayAlt.JF.JqSmoothOfParts := by
  intro hW hGD k r Wp Wq _ _ _ _ _ _ D A m F hT hF
  have hg := BigCellOpenDomain.gq_contDiffOn D m
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hG := hGD k r Wp Wq D q hq
  obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 (gq D q) ⟨WordKeyIdentity.glev0 hG.1, hG.2⟩
  refine ⟨QDom k r D.z D.z' ∩ (fun q => gq D q) ⁻¹' U,
    hg.continuousOn.isOpen_inter_preimage (BigCellOpenDomain.qdom_open D.z D.z') hU, ⟨hq, hgU⟩, ?_⟩
  have hcomp : ContDiffOn ℝ (m : WithTop ℕ∞) (F' ∘ fun q => gq D q)
      (QDom k r D.z D.z' ∩ (QDom k r D.z D.z' ∩ (fun q => gq D q) ⁻¹' U)) :=
    hc.comp (hg.mono Set.inter_subset_left) fun x hx => hx.2.2
  refine hcomp.congr fun x hx => ?_
  exact he _ hx.2.2 (WordKeyIdentity.glev0 (hGD k r Wp Wq D x hx.1).1)

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem np_top_two (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (a a' : C.LPt)
    (ha : D.IsLocPt a P.r) (ha' : D.IsLocPt a' P.r) (w : List C.Letter) (c : ℂ) :
    ((√(C.nAux P.k P.r 0 (fun _ _ => 1) 1 a) * √(C.nAux P.k P.r 0 (fun _ _ => 1) 1 a') / TBB.normC nn w : ℝ) : ℂ) *
        ((KB.levW P (P.r + 1) c : ℂ) * p.RR F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])) =
      TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) := by
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a with hAdef
  set A' := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a' with hA'def
  have hA : 0 ≤ A := TBBx5.weighted_auxiliary_norm_nonneg P P.r le_rfl a ha
  have hA' : 0 ≤ A' := TBBx5.weighted_auxiliary_norm_nonneg P P.r le_rfl a' ha'
  have hn : ∀ (b : C.LPt), D.IsLocPt b P.r → TBB.nPt P.k P.r (TBB.TTp p) (b ++ [(1, c)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 b *
        C.nAux P.k P.r (D.ptGG (TBB.TTp p) (b ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] := by
    intro b hb
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hb.2,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) b 1 le_rfl (by rw [hb.2]; omega)]
  unfold TBB.NP
  rw [hn a ha, hn a' ha']
  by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
  · have h0 : p.RR F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) = 0 :=
      Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w a (a' ++ [(1, c)]) c ha.2 hc2
    rw [h0]
    simp
  · push Not at hc2
    have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
    have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
    have hlast : ∀ b : C.LPt, D.ptGG (TBB.TTp p) (b ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
      intro b
      simp [D.ptGG, D.ptLast]
    have hTT : TBB.TTp p = P.T * P.T' := by
      unfold TBB.TTp
      rw [hT, hT']
    have hfac : ∀ b : C.LPt, C.nAux P.k P.r (D.ptGG (TBB.TTp p) (b ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
        KB.levW P (P.r + 1) c := by
      intro b
      rw [hlast, hTT]
      rw [hT, hT'] at hc2
      simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
      rw [if_pos ⟨by omega, trivial⟩]
      simp
    have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
      rw [← hfac a, hlast]
      simp only [C.nAux]
      rw [if_pos ⟨by omega, trivial⟩]
      have : 0 ≤ Complex.normSq c - TBB.TTp p := by
        unfold TBB.TTp; linarith
      simpa using pow_nonneg this _
    rw [hfac a, hfac a', Real.sqrt_mul hA, Real.sqrt_mul hA']
    have hs : √(KB.levW P (P.r + 1) c) * √(KB.levW P (P.r + 1) c) = KB.levW P (P.r + 1) c :=
      Real.mul_self_sqrt hlev
    have : √A * √(KB.levW P (P.r + 1) c) * (√A' * √(KB.levW P (P.r + 1) c)) / TBB.normC nn w =
        √A * √A' / TBB.normC nn w * KB.levW P (P.r + 1) c := by
      have e : √A * √(KB.levW P (P.r + 1) c) * (√A' * √(KB.levW P (P.r + 1) c)) / TBB.normC nn w =
          √A * √A' / TBB.normC nn w * (√(KB.levW P (P.r + 1) c) * √(KB.levW P (P.r + 1) c)) := by ring
      rw [e, hs]
    rw [this]
    push_cast
    ring

end place

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_lieW {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hW : ∀ X ∈ lieOf (UWset k r z), (Matrix.trace (ζ * X)).re = 0)
    (u v : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hv : inWb k r v)
    (huz : herm (Hpk k r) u z = 0) (hvz : herm (Hpk k r) v z = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  refine herm_zero_of_trace hζ u v (hW _ (xuv_lieW z u v hu hv huz hvz)) (hW _ ?_)
  refine xuv_lieW z u _ hu (inWb_smul _ hv) huz ?_
  rw [herm_smul_left, hvz, mul_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

end Formalism.FourierDecayAlt.P.CutMP.JfS
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

def GTConnOfLeaves : Prop := GTCLocal → GTCReal → GTCCurv → GTCHol → GTCAnnulus → GTConn

theorem gTConn_of_leaves : GTConnOfLeaves := fun hL hR hC hH hA =>
  gTConn_of_cut hL (gTCPhase_of_cut hR hC hH hA torus_parameter) gauge_transform_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutBP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

theorem ccleQ_nonneg {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F : B.Mat k r → E} {b : ℝ} (h : B.CCle A m F b) : 0 ≤ b := by
  obtain ⟨g, hg⟩ : ∃ g, g ∈ B.GV k r := ⟨1, by simp [B.GV, Formalism.QuantumDeterminants.UH]⟩
  have h1 := h.2 [] [] (by simp) (by simp) (by simp) g hg
  have h2 : 0 ≤ B.gN g ^ A * ‖B.dLR [] [] F g‖ :=
    mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)
  linarith

theorem ccleQ_mono_c {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F : B.Mat k r → E} {b b' : ℝ} (h : B.CCle A m F b) (hb : b ≤ b') : B.CCle A m F b' := ⟨h.1, fun u v hu hv hl g hg => (h.2 u v hu hv hl g hg).trans hb⟩

private theorem le_foldr_max_zero_of_mem : ∀ (l : List ℕ), ∀ x ∈ l, x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons y t ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih x h) (le_max_right _ _)

theorem word_le_opOrder {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) :
    ∀ T ∈ Θ, T.word.length ≤ B.opOrder Θ := by
  intro T hT
  unfold B.opOrder
  exact le_foldr_max_zero_of_mem _ _ (List.mem_map_of_mem hT)

theorem jdCCLowerQ {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ)
    (hd : 0 ≤ d) (hG : CutMP.GlobCoef Θ d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CkOn ⊤ (B.GV k r) F →
      B.CCle A (m + B.opOrder Θ) F b → B.CCle (A - d) m (B.opApply Θ F) (K * b) := by
  have _hd := hd
  set o := B.opOrder Θ with ho
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg

  have hterm : ∀ T ∈ Θ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ),
      B.CCle A (m + o) F b → B.CCle (A - d) m (ap T.coef (B.Rw T.word F)) (K * b) := by
    intro T hT
    obtain ⟨hc1, -, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    set s : ℂ := (((T.word.map nz).prod : ℝ) : ℂ) with hs
    refine ⟨2 ^ m * (|C| * ‖s‖), by positivity, fun F b hF => ?_⟩
    have hb0 : 0 ≤ b := ccleQ_nonneg hF
    have hlen : T.word.length ≤ o := word_le_opOrder Θ T hT
    have hF1 : B.CCle A (m + (T.word.map nrm).length) F b :=
      CCle_mono_m (by simp; omega) hF
    have hunit : ∀ X ∈ T.word.map nrm, unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact nrm_unit (T.word_lie Y hY)
    have hR : B.CCle A m (B.Rw T.word F) (‖s‖ * b) := by
      rw [Rw_scale]
      exact CCle_smul s (CCle_Rw hunit hF1)
    have hR' : B.CCle (A - d + d) m (B.Rw T.word F) (‖s‖ * b) := by rw [sub_add_cancel]; exact hR
    have hP := prodBound hO hcov (sCkOn_mono le_top hc1)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hR' (fun g _ hg => by simp at hg)
    refine ccleQ_mono_c hP (le_of_eq ?_)
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) hb0)]
    ring

  have hsum : ∀ L : List (B.DTerm k r Wp Wq), (∀ T ∈ L, T ∈ Θ) → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CCle A (m + o) F b →
        B.CCle (A - d) m (fun g => (L.map fun T => ap T.coef (B.Rw T.word F) g).sum) (K * b) := by
    intro L
    induction L with
    | nil =>
      intro _
      refine ⟨0, le_rfl, fun F b _ => ?_⟩
      simpa using (CCle_zero : B.CCle (A - d) m (fun _ : B.Mat k r => (0 : Wq →L[ℂ] Wp)) 0)
    | cons T L ih =>
      intro hL
      obtain ⟨K₁, hK₁, h₁⟩ := hterm T (hL T (by simp))
      obtain ⟨K₂, hK₂, h₂⟩ := ih fun S hS => hL S (by simp [hS])
      refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun F b hF => ?_⟩
      have h := CCle_add (h₁ F b hF) (h₂ F b hF)
      have e : (K₁ + K₂) * b = K₁ * b + K₂ * b := by ring
      rw [e]
      simpa using h
  obtain ⟨K, hK, hKb⟩ := hsum Θ fun T hT => hT
  refine ⟨K, hK, fun F b _ hF => ?_⟩
  have hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum := rfl
  rw [hop]
  exact hKb F b hF

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

theorem class_lower_decay_holds : JDCCLower := by
  intro k r Wp Wq _ _ _ _ _ _ Θ d A hd hG F hF hFA
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg
  have hΦck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word F) := by
    intro T hT
    rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) T.word_lie x (by simpa [wL] using hx))
    simpa using hF
  have hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum := rfl
  refine ⟨?_, fun m => ?_⟩
  · rw [hop]
    clear hop
    induction Θ with
    | nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))
    | cons T Θ ih =>
      have h1 : B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F)) :=
        Pr.ck hO hcov ⟨(hG T (by simp)).1, hΦck T (by simp), fun g _ hg => by simp at hg⟩
      have h2 := ih (fun S hS => hG S (by simp [hS])) (fun S hS => hΦck S (by simp [hS]))
      simpa using CkOn_add h1 h2
  · rw [hop]
    refine InCC_opsum Θ (fun T => ap T.coef (B.Rw T.word F)) ?_
    intro T hT
    obtain ⟨hc1, -, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    obtain ⟨c, hc⟩ : B.InCC (A - d + d) m (B.Rw T.word F) := by
      rw [sub_add_cancel]; exact InCC_Rw T.word_lie (hFA _)
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top hc1)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hc (fun g _ hg => by simp at hg)⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem reference_annulus_holds : GTCRefAn := by
  intro TT α c hTT hα hre R hR hR2
  have hpt : ∀ θ : ℝ, TT < Complex.normSq (circleMap 0 R θ) := by
    intro θ
    have h1 : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    rw [Complex.normSq_eq_norm_sq, h1]
    exact hR2
  have hcα : Continuous (fun θ : ℝ => α (circleMap 0 R θ)) :=
    hα.continuousOn.comp_continuous (continuous_circleMap 0 R) hpt
  have hd : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
    funext θ
    exact deriv_circleMap 0 R θ
  have hF : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) := by
    have h2 : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ) := by
      rw [hd]
      exact (continuous_circleMap 0 R).mul continuous_const
    exact h2.smul hcα
  have key : ∀ θ : ℝ, Complex.imCLM (deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) = c := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul, Complex.imCLM_apply]
    rw [← hre (circleMap 0 R θ) (hpt θ)]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  unfold circleIntegral
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hF.intervalIntegrable _ _)]
  simp only [key]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
