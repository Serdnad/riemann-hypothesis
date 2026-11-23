module

public import Formalism.HermitianCurvature.StatementPB
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle001
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRWeyl
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.FormalDegreeBessel.Bundle002
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

open Formalism.FourierDecayAlt.PB Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem localCores : Formalism.FourierDecayAlt.PB.LocalCores :=
  ⟨Formalism.FourierDecayAlt.Final.jx_pSDAgree,
   Formalism.FourierDecayAlt.Final.jx_schurProduct,
   Formalism.FourierDecayAlt.Final.jx_productDomination,
   Formalism.FourierDecayAlt.Final.jx_diagScale,
   Formalism.FourierDecayAlt.Final.jx_diagPhase,
   Formalism.FourierDecayAlt.Final.jx_blockDiagPSD,
   Formalism.FourierDecayAlt.Final.jx_productLemma,
   Formalism.FourierDecayAlt.Final.jx_scaleOk,
   Formalism.FourierDecayAlt.Final.jx_phaseOk,
   Formalism.FourierDecayAlt.Final.jx_outsideSysOk,
   Formalism.FourierDecayAlt.Final.jx_outsideDomination,
   Formalism.FourierDecayAlt.Final.jx_localPullback,
   Formalism.FourierDecayAlt.Final.jx_localUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_topPullback,
   Formalism.FourierDecayAlt.Final.jx_topUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_globalOfLocal,
   Formalism.FourierDecayAlt.Final.jx_uniformMajorantOn,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromSystems,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromFamilies,
   Formalism.FourierDecayAlt.Final.jx_kernelOfLocal,
   Formalism.FourierDecayAlt.Final.jx_localKernelPSD,
   Formalism.FourierDecayAlt.Final.tc_domMinOfText,
   Formalism.FourierDecayAlt.Final.tc_domAfterOfLocal,
   Formalism.FourierDecayAlt.Final.gram_determinant_dual_bound_a,
   Formalism.FourierDecayAlt.Final.parahoric_gram_matrix,
   Formalism.FourierDecayAlt.Final.zero_level_ones_vector,
   Formalism.FourierDecayAlt.Final.singleBlockParseval_true,
   Formalism.FourierDecayAlt.Final.theta_equality_first,
   Formalism.FourierDecayAlt.Final.singleBlockThetaProps_true,
   Formalism.FourierDecayAlt.Final.ns_support,
   Formalism.FourierDecayAlt.Final.ns_block_diagonal,
   Formalism.FourierDecayAlt.Final.latticeAverage_of_gram⟩

theorem globalCores : Formalism.FourierDecayAlt.PB.GlobalCores :=
  ⟨Formalism.FourierDecayAlt.Final.tc_theoremAAfter,
   Formalism.FourierDecayAlt.Final.tc_recursionWithDens,
   Formalism.FourierDecayAlt.Final.tc_domScaleTop,
   Formalism.FourierDecayAlt.Final.tc_sumBoundMax,
   Formalism.FourierDecayAlt.Final.tc_recHypScaleTop,
   Formalism.FourierDecayAlt.Final.tc_densSum,
   Formalism.FourierDecayAlt.Final.tc_densLeTwo,
   Formalism.FourierDecayAlt.Final.tc_densSize,
   Formalism.FourierDecayAlt.Final.tc_densChain,
   Formalism.FourierDecayAlt.Final.poisson_summation_text,
   Formalism.FourierDecayAlt.Final.jx_poissonJoint,
   Formalism.FourierDecayAlt.Final.jx_poissonStepJoint,
   Formalism.SA.P.smoothedSumBound,
   Formalism.FourierDecayAlt.Final.lattices_general_position_bound,
   Formalism.FourierDecayAlt.Final.ideals_match,
   Formalism.FourierDecayAlt.Final.ideal_norm_formula,
   Formalism.FourierDecayAlt.Final.field_extension_degree_facts,
   Formalism.FourierDecayAlt.Final.jx_frameProducts,
   Formalism.FourierDecayAlt.Final.jx_xIsLamOne,
   Formalism.FourierDecayAlt.Final.jx_latticeSumsJoint,
   Formalism.FourierDecayAlt.Final.jx_instSizes,
   Formalism.FourierDecayAlt.Final.jx_instLatticeSums,
   Formalism.FourierDecayAlt.Final.sz_sizesMain,
   Formalism.FourierDecayAlt.Final.jx_sizesToRecursion,
   Formalism.FourierDecayAlt.Final.jx_globPositive,
   Formalism.FourierDecayAlt.Final.counting_theorem,
   Formalism.FourierDecayAlt.Final.jx_formGivesMain⟩

end Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cell

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]


open Classical in
def resW (h : Mx k r → V) (g : Mx k r) : (Fin r → ℂ) → V :=
  fun c' => if c' ∈ OmX r then resG k r (Fin.last r) h c' g else 0

theorem resG_contDiffAt (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V}
    (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hG : 0 < GGl k r Bs.z Bs.z' g) {c₀ : Fin r → ℂ} (hc₀ : c₀ ∈ OmX r) :
    ContDiffAt ℝ ∞ (fun c' => resG k r (Fin.last r) h c' g) c₀ := by
  have hsf := Formalism.FourierDecayAlt.P5.Rad.sf_resG hh
  obtain ⟨U, F, hU, hxU, hF, hE⟩ := hsf (c₀, g)
    ⟨hc₀, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc₀ hg hG⟩ hg
  have hpre : IsOpen ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) := hU.preimage (by fun_prop)
  have hmem : c₀ ∈ (fun c : Fin r → ℂ => (c, g)) ⁻¹' U := hxU
  have hcd : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) c₀ := by
    have h1 : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => F (c, g)) ((fun c : Fin r → ℂ => (c, g)) ⁻¹' U) :=
      hF.comp (by fun_prop : ContDiff ℝ ∞ (fun c : Fin r → ℂ => (c, g))).contDiffOn (fun c hc => hc)
    exact h1.contDiffAt (hpre.mem_nhds hmem)
  refine hcd.congr_of_eventuallyEq ?_
  filter_upwards [hpre.mem_nhds hmem] with c hc
  exact hE (c, g) hc hg

theorem resG_wsm (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) :
    resW h g ∈ WSm r V := by
  refine ⟨?_, fun x hx => by simp [resW, hx]⟩
  intro c hc
  have h1 := (resG_contDiffAt Bs hh hg hG hc).contDiffWithinAt (s := OmX r)
  refine h1.congr (fun c' hc' => by simp [resW, hc']) (by simp [resW, hc])

theorem wsm_resG_eq (h : Mx k r → V) (g : Mx k r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    resW h g c = resG k r (Fin.last r) h c g := by
  simp [resW, hc]

theorem cell_diff (Bs : B.RealPlaceData k r Wp Wq) {h : Mx k r → V} (hh : SmoothLev k r 0 (OmPlus k r Bs.z Bs.z') h)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r Bs.z Bs.z' g) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : DifferentiableAt ℝ (fun c' => h (wCell k r (Fin.last r) c' * g)) c := by
  have hgl : ∀ c' ∈ OmX r, wCell k r (Fin.last r) c' * g ∈ Glev k r 0 := fun c' hc' =>
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc' _) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg)
  obtain ⟨U, F, hU, hgU, hF, hE⟩ := hh (wCell k r (Fin.last r) c * g)
    ⟨hgl c hc, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hg hG⟩
  have hw : ContDiffOn ℝ ∞ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) (OmX r) :=
    Formalism.FourierDecayAlt.P.Qx3.cdo_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _) contDiffOn_const
  have hwc : ContinuousAt (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
    (hw.continuousOn).continuousAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
  have hd : DifferentiableAt ℝ (fun c' => F (wCell k r (Fin.last r) c' * g)) c := by
    have hFd : DifferentiableAt ℝ F (wCell k r (Fin.last r) c * g) :=
      (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
    have hwd : DifferentiableAt ℝ (fun c' : Fin r → ℂ => wCell k r (Fin.last r) c' * g) c :=
      (hw.differentiableOn (by simp)).differentiableAt ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc)
    exact hFd.comp c hwd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc, hwc.preimage_mem_nhds (hU.mem_nhds hgU)]
    with c' h1 h2
  exact hE _ h2 (hgl c' h1)

end cell

section chain

variable {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem wsm_sub {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) : f - g ∈ WSm r V :=
  (WSm r V).sub_mem hf hg

theorem opL_mem (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) : opL l i f ∈ WSm r V :=
  preserved_operators_holds r V l i f hf

theorem opL_sub (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f - g) = opL l i f - opL l i g := by
  have hng : (-1 : ℂ) • g ∈ WSm r V := (WSm r V).smul_mem _ hg
  have e : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, (linear_operators_holds r V l i f _ 1 hf hng).1, (linear_operators_holds r V l i g g (-1) hg hg).2, neg_one_smul,
    sub_eq_add_neg]

theorem opL_add (l : Fin r) (i : Fin 6) {f g : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (hg : g ∈ WSm r V) :
    opL l i (f + g) = opL l i f + opL l i g :=
  (linear_operators_holds r V l i f g 1 hf hg).1

theorem opL_smul (l : Fin r) (i : Fin 6) {f : (Fin r → ℂ) → V} (hf : f ∈ WSm r V) (a : ℂ) :
    opL l i (a • f) = a • opL l i f :=
  (linear_operators_holds r V l i f f a hf hf).2

theorem pOp_zero (l : Fin r) : pOp l (fun _ : Fin r → ℂ => (0 : V)) = fun _ => 0 := by
  funext x; unfold pOp wirt; split_ifs <;> simp

theorem vAB_mem (y : ℂ) : ∀ (i : ℕ) {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V := by
  intro i
  induction i with
  | zero =>
    intro G hG
    exact ⟨hG, (WSm r V).zero_mem⟩
  | succ i ih =>
    intro G hG
    obtain ⟨hA, hB⟩ := ih hG
    by_cases hi : i < r
    · simp only [vAB, dite_eq_left hi]
      refine ⟨wsm_sub ((WSm r V).add_mem ((WSm r V).smul_mem y hA) (opL_mem ⟨i, hi⟩ 0 hA))
        (opL_mem ⟨i, hi⟩ 1 hB), opL_mem ⟨i, hi⟩ 2 hA⟩
    · simp only [vAB, dite_eq_right hi]
      exact ⟨hA, hB⟩

theorem vAB_lin (y : ℂ) : ∀ (i : ℕ) {G₁ G₂ : (Fin r → ℂ) → V}, G₁ ∈ WSm r V → G₂ ∈ WSm r V → ∀ s : ℂ,
    (vAB r y i).1 (G₁ + s • G₂) = (vAB r y i).1 G₁ + s • (vAB r y i).1 G₂ ∧
      (vAB r y i).2 (G₁ + s • G₂) = (vAB r y i).2 G₁ + s • (vAB r y i).2 G₂ := by
  intro i
  induction i with
  | zero =>
    intro G₁ G₂ _ _ s
    exact ⟨rfl, by show (0 : (Fin r → ℂ) → V) = 0 + s • 0; simp⟩
  | succ i ih =>
    intro G₁ G₂ h₁ h₂ s
    obtain ⟨ih1, ih2⟩ := ih h₁ h₂ s
    obtain ⟨hA₁, hB₁⟩ := vAB_mem y i h₁
    obtain ⟨hA₂, hB₂⟩ := vAB_mem y i h₂
    have hsA := (WSm r V).smul_mem s hA₂
    have hsB := (WSm r V).smul_mem s hB₂
    by_cases hi : i < r
    · simp only [vAB, dite_eq_left hi]
      rw [ih1, ih2]
      refine ⟨?_, ?_⟩
      · have e1 : pOp ⟨i, hi⟩ ((vAB r y i).1 G₁ + s • (vAB r y i).1 G₂) =
            pOp ⟨i, hi⟩ ((vAB r y i).1 G₁) + s • pOp ⟨i, hi⟩ ((vAB r y i).1 G₂) := by
          rw [show pOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 0 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
        have e2 : cOp ⟨i, hi⟩ ((vAB r y i).2 G₁ + s • (vAB r y i).2 G₂) =
            cOp ⟨i, hi⟩ ((vAB r y i).2 G₁) + s • cOp ⟨i, hi⟩ ((vAB r y i).2 G₂) := by
          rw [show cOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 1 from rfl, opL_add _ _ hB₁ hsB, opL_smul _ _ hB₂]
        rw [e1, e2]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_add, smul_sub]
        rw [smul_comm y s]
        abel
      · rw [show ciOp ⟨i, hi⟩ = opL ⟨i, hi⟩ 2 from rfl, opL_add _ _ hA₁ hsA, opL_smul _ _ hA₂]
    · simp only [vAB, dite_eq_right hi]
      exact ⟨ih1, ih2⟩

theorem vAB_comm (y : ℂ) (j : Fin r) : ∀ (i : ℕ), i ≤ j.val → ∀ {G : (Fin r → ℂ) → V}, G ∈ WSm r V →
    (vAB r y i).1 G ∈ WSm r V ∧ (vAB r y i).2 G ∈ WSm r V ∧
      (vAB r y i).1 (pOp j G) = pOp j ((vAB r y i).1 G) ∧ (vAB r y i).2 (pOp j G) = pOp j ((vAB r y i).2 G) := by
  intro i
  induction i with
  | zero =>
    intro _ G hG
    exact ⟨hG, (WSm r V).zero_mem, rfl, by simp only [vAB]; exact (pOp_zero j).symm⟩
  | succ i ih =>
    intro hij G hG
    obtain ⟨hA, hB, c1, c2⟩ := ih (by omega) hG
    have hi : i < r := by have := j.isLt; omega
    have hne : (⟨i, hi⟩ : Fin r) ≠ j := by intro h; rw [← h] at hij; simp at hij
    obtain ⟨hm1, hm2⟩ := vAB_mem y (i + 1) hG
    refine ⟨hm1, hm2, ?_, ?_⟩
    · simp only [vAB, dite_eq_left hi]
      rw [c1, c2]
      have hpA : pOp ⟨i, hi⟩ ((vAB r y i).1 G) ∈ WSm r V := opL_mem _ 0 hA
      have hcB : cOp ⟨i, hi⟩ ((vAB r y i).2 G) ∈ WSm r V := opL_mem _ 1 hB
      have hyA : y • (vAB r y i).1 G ∈ WSm r V := (WSm r V).smul_mem y hA
      rw [show pOp j = opL j 0 from rfl, opL_sub _ _ ((WSm r V).add_mem hyA hpA) hcB,
        opL_add _ _ hyA hpA, opL_smul _ _ hA]
      have k1 : opL j 0 (pOp ⟨i, hi⟩ ((vAB r y i).1 G)) = pOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).1 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 0 _ hA (Or.inl (Ne.symm hne)))
      have k2 : opL j 0 (cOp ⟨i, hi⟩ ((vAB r y i).2 G)) = cOp ⟨i, hi⟩ (opL j 0 ((vAB r y i).2 G)) :=
        (commuting_functional_holds r V j ⟨i, hi⟩ 0 1 _ hB (Or.inl (Ne.symm hne)))
      rw [k1, k2]
    · simp only [vAB, dite_eq_left hi]
      rw [c1]
      exact (commuting_functional_holds r V j ⟨i, hi⟩ 0 2 _ hA (Or.inl (Ne.symm hne))).symm

end chain

end Formalism.FourierDecayAlt.P.PBN.MC
end
end

section

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

theorem big_cell_values : TL.CellVals := by
  intro k r Wp Wq _ _ _ _ _ Bs x hx
  obtain ⟨hc, hg, hG⟩ := hx
  obtain ⟨μ, -, hμ⟩ := (TwoByOneBlock.UWb_iff x.2).1 (NFRadRedA.glev_uwb hg)
  have hGV : wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by
    have h1 : wCell k r (Fin.last r) x.1 ∈ Glev k r 0 := by
      unfold wCell
      exact Qx3.wlist_glev hc _
    exact (Qx5.Glev_mul h1 (Qx4.glev0 hg.1)).1
  have hM : wCell k r (Fin.last r) x.1 * x.2 = bigCell k r x.1 μ := by
    rw [P5.Rad.wCell_last_eq, hμ, ← (bruhat_big_cell_factorization k r x.1 μ).1]
  rw [hM] at hGV ⊢
  set ζ := zetaL k r Bs.z Bs.z' (Fin.last r) x.2 with hζdef
  have hz : ζ = herm (Hb k) (μ *ᵥ wbPart k r Bs.z') (wbPart k r Bs.z) := by
    rw [hζdef, P5.Rad.zetaL_last, hμ]
    have e1 : B2.embWb k r μ *ᵥ Bs.z' = TwoByOneBlock.jV k r (μ *ᵥ wbPart k r Bs.z') := by
      conv_lhs => rw [← TwoByOneBlock.jV_wbPart Bs.z'_mem]
      exact TwoByOneBlock.emb_mulVec_jV _ _
    rw [e1]
    conv_lhs => rw [← TwoByOneBlock.jV_wbPart Bs.z_mem]
    rw [TwoByOneBlock.herm_jV]
  let d : Fin (r + 1) → ℂ := fun a => if h : (a : ℕ) < r then x.1 ⟨a, h⟩ else ζ
  have hZ : Zhat k r Bs.z Bs.z' (bigCell k r x.1 μ) = diagonal d := by
    rw [bigCellZhat k r Bs.z Bs.z' x.1 μ Bs.z_mem Bs.z'_mem]
    congr 1
    funext a
    by_cases h : (a : ℕ) < r
    · simp [d, h]
    · simp only [d, h, dite_false]
      rw [BigCellHermitian.herm_bigCell x.1 μ Bs.z_mem Bs.z'_mem, hz]
  have hD := BruhatBigCell.dmin_diag Bs.z Bs.z' _ d hZ
  have hTT : 0 < Tz k r Bs.z * Tz k r Bs.z' := mul_pos Bs.T_pos Bs.T'_pos
  have hζ : ζ ≠ 0 := by
    intro h0
    have : GGl k r Bs.z Bs.z' x.2 = Complex.normSq ζ - Tz k r Bs.z * Tz k r Bs.z' := rfl
    rw [this, h0, map_zero] at hG
    linarith
  have hd0 : ∀ a, d a ≠ 0 := by
    intro a
    by_cases h : (a : ℕ) < r
    · simp only [d, h, dite_true]
      exact hc _
    · simp only [d, h, dite_false]
      exact hζ
  have hP : ∏ a : Fin r, x.1 a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc a
  have hDr : Dmin k r Bs.z Bs.z' (bigCell k r x.1 μ) ⟨r, by omega⟩ = ∏ a : Fin r, x.1 a := by
    rw [hD]
    refine Finset.prod_congr rfl ?_
    intro i _
    have hi : ((Fin.castLE (by omega) i : Fin (r + 1)) : ℕ) < r := i.isLt
    simp only [d, hi, dite_true]
    rfl
  have hDl : Dmin k r Bs.z Bs.z' (bigCell k r x.1 μ) (Fin.last (r + 1)) = (∏ a : Fin r, x.1 a) * ζ := by
    rw [hD]
    show ∏ i : Fin (r + 1), d (Fin.castLE (by omega) i) = _
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl ?_
      intro i _
      have hi : ((Fin.castLE (by omega) i.castSucc : Fin (r + 1)) : ℕ) < r := i.isLt
      simp only [d, hi, dite_true]
      rfl
    · have hi : ¬ ((Fin.castLE (by omega) (Fin.last r) : Fin (r + 1)) : ℕ) < r := by simp
      simp only [d, hi, dite_false]
  have hGf : Gf k r Bs.z Bs.z' (bigCell k r x.1 μ) = Complex.normSq (∏ a : Fin r, x.1 a) * GGl k r Bs.z Bs.z' x.2 := by
    unfold Gf
    rw [hDl, hDr]
    show _ = _ * (Complex.normSq ζ - Tz k r Bs.z * Tz k r Bs.z')
    rw [map_mul]
    ring
  refine ⟨⟨hGV, ?_, ?_⟩, hDr, hDl, hGf⟩
  · rw [hGf]
    exact mul_pos (Complex.normSq_pos.mpr hP) hG
  · intro l _
    rw [hD]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _

end

end Formalism.FourierDecayAlt.P
end
