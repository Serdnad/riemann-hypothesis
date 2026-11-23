module

public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle159
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle237
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChainPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle234
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalProof
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle173
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle239
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle105
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPWordAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle245
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle066
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle162
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle174
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialSideRaising
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle216
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle233
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle243
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle244
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle242
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SiteZeroMatrixEntry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P

theorem pb_builtBounds2Cpt_of_mkTop (hM : CutEX.MkTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt :=
  built_bounds_compact_of_head_top (pb_headTop_of_mkTop hM)

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem kappa_quadratic_bound_holds : JABddKapQQ :=
  jABddKapQQ_of_shared second_shift_geometry_holds rho_projection_existence gauge_lines_holds SSn.Rep.datum_unit_norm_holds

theorem jABddOpQQ_of_ssnRep (h : SSn.SSnRep) : JABddOpQQ :=
  jABddOpQQ_of_bddLeaves bounded_scalar_transfer_holds kappa_quadratic_bound_holds
    (SSn.jABddSSnQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)
    (SSn.jABddSSnStarQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)

end Formalism.FourierDecayAlt.P.CutMP.JA

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_ssnRep (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_bdd hJ hG (JA.jABddOpQQ_of_ssnRep h)

end Formalism.FourierDecayAlt.P.CutMP
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem polynomial_radial_holds : PolyRadialS := polyRadialS_of CP.radial_decomposition_holds CP.word_polynomial_vector_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants

section loc

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rds_pbOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pbOp l f₁ c = pbOp l f₂ c := by
  have hopen : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have hev : f₁ =ᶠ[nhds c] f₂ := Filter.eventuallyEq_of_mem (hopen.mem_nhds hc) h
  unfold pbOp wirtBar
  rw [if_pos hc, if_pos hc, hev.fderiv_eq]

theorem rds_vABm_loc (Y : ℂ) : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (CutMP.vABm r Y i).1 f₁ c = (CutMP.vABm r Y i).1 f₂ c ∧
      (CutMP.vABm r Y i).2 f₁ c = (CutMP.vABm r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    have ih := rds_vABm_loc Y i f₁ f₂ h
    by_cases hi : i < r
    · simp only [CutMP.vABm, dif_pos hi]
      refine ⟨?_, ?_⟩
      · simp only [Pi.sub_apply, Pi.smul_apply, cbOp]
        rw [(ih c hc).1, (ih c hc).2, rds_pbOp_locO _ (fun c' hc' => (ih c' hc').1) hc]
      · simp only [cbiOp]
        rw [(ih c hc).1]
    · simp only [CutMP.vABm, dif_neg hi]
      exact ih c hc

end loc

theorem spectral_action_locality : RDSALoc := by
  intro r E _ _ y f f' h c hc
  have hopen : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have hpO : ∀ (l : Fin r) (g₁ g₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r,
      pOp l g₁ c = pOp l g₂ c := by
    intro l g₁ g₂ hg c hc
    have hev : g₁ =ᶠ[nhds c] g₂ := Filter.eventuallyEq_of_mem (hopen.mem_nhds hc) hg
    unfold pOp Formalism.QuantumDeterminants.wirt
    rw [if_pos hc, if_pos hc, hev.fderiv_eq]
  have hA : ∀ i : ℕ, ∀ g₁ g₂ : (Fin r → ℂ) → E, (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r,
      (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c ∧ (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c := by
    intro i
    induction i with
    | zero =>
      intro g₁ g₂ hg c hc
      simp only [Q.vAB]
      exact ⟨hg c hc, by trivial⟩
    | succ i ih =>
      intro g₁ g₂ hg c hc
      have ih1 : ∀ c ∈ OmX r, (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c := fun c hc => (ih g₁ g₂ hg c hc).1
      have ih2 : ∀ c ∈ OmX r, (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c := fun c hc => (ih g₁ g₂ hg c hc).2
      simp only [Q.vAB]
      split_ifs with hi
      · refine ⟨?_, ?_⟩
        · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          rw [ih1 c hc, hpO ⟨i, hi⟩ _ _ ih1 c hc]
          simp only [cOp]
          rw [ih2 c hc]
        · simp only [ciOp]
          rw [ih1 c hc]
      · exact ih g₁ g₂ hg c hc
  exact ⟨(hA r f f' h c hc).1, (rds_vABm_loc y r f f' h c hc).1⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rdsp_opApply_vanish (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opApply Θ F g = 0 := by
  intro g hg hgO
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO T.word_lie hz g hg hgO, map_zero]

theorem rdsp_adjFn_vanish (T : B.DTerm k r Wp Wq) {O : Set (B.Mat k r)}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → ap T.coefAdj F g = 0 := by
  intro g hg hgO
  simp only [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap]
  rw [hz g hg hgO, map_zero]

theorem rdsp_lie_rev (T : B.DTerm k r Wp Wq) : ∀ X ∈ T.word.reverse, inLie k r X := by
  intro X hX
  exact T.word_lie X (List.mem_reverse.mp hX)

theorem rdsp_opAdj_eq (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.opAdj Θ F = fun g => (Θ.map fun T => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g).sum := rfl

theorem rdsp_opAdj_vanish (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opAdj Θ F g = 0 := by
  intro g hg hgO
  rw [rdsp_opAdj_eq]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO (rdsp_lie_rev T) (rdsp_adjFn_vanish T hz) g hg hgO, smul_zero]

theorem rdsp_opAdj_cc (Θ : B.DiffOp k r Wp Wq) (d : ℝ) (hG : CutMP.GlobCoef Θ d) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : B.CkOn ⊤ (B.GV k r) F) (A : ℝ) (hFA : ∀ m : ℕ, B.InCC (A + d) m F) :
    B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧ ∀ m : ℕ, B.InCC A m (B.opAdj Θ F) := by
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg
  have hz0 : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) → F g = 0 := fun g _ hg => by simp at hg
  have hapck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (ap T.coefAdj F) := fun T hT =>
    Pr.ck hO hcov ⟨(hG T hT).2.1, hF, hz0⟩
  have hRck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word.reverse (ap T.coefAdj F)) := by
    intro T hT
    rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) (rdsp_lie_rev T) x (by simpa [wL] using hx))
    simpa using hapck T hT
  have hapcc : ∀ T ∈ Θ, ∀ m : ℕ, B.InCC A m (ap T.coefAdj F) := by
    intro T hT m
    obtain ⟨hc1, hc2, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    obtain ⟨c, hc⟩ := hFA m
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top hc2)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).2) hc hz0⟩
  rw [rdsp_opAdj_eq]
  refine ⟨?_, fun m => ?_⟩
  · clear hapcc
    induction Θ with
    | nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))
    | cons T Θ ih =>
      have h1 : B.CkOn ⊤ (B.GV k r) (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g) :=
        CkOn_smul _ (hRck T (by simp))
      have h2 := ih (fun S hS => hG S (by simp [hS])) (fun S hS => hapck S (by simp [hS]))
        (fun S hS => hRck S (by simp [hS]))
      simpa using CkOn_add h1 h2
  · refine InCC_opsum Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g) ?_
    intro T hT
    obtain ⟨c, hc⟩ : B.InCC A m (B.Rw T.word.reverse (ap T.coefAdj F)) :=
      InCC_Rw (rdsp_lie_rev T) (hapcc T hT _)
    exact ⟨_, CCle_smul _ hc⟩

end

theorem spectral_polynomial_property : RDSPolyProp := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ hC
  obtain ⟨hS, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  refine ⟨hS _, hC, fun ε _ => ⟨κ, hκ, fun T hT => ?_⟩, fun F hF => ?_⟩
  · obtain ⟨-, -, hb⟩ := hG T hT
    obtain ⟨Cb, hCb⟩ := hb (B.opOrder Θ + 5)
    exact ⟨Cb, fun u v hu hv hl g hg _ => hCb u v hu hv hl g hg⟩
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    have := hFs g hg hne
    exact absurd hgO (not_lt.2 this)
  refine ⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩
  · exact (CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1
  · intro A' m'
    have h := (CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'
    rwa [add_sub_cancel_right] at h
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))
  · exact (rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1
  · intro A' m'
    exact (rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

namespace RhRPf

section pair

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem fst_mul_apply (p q : Pr V) (v : V) : (p * q).1 v = p.1 (q.1 v) := rfl
theorem fst_mkP (a a' : Module.End ℂ V) : (mkP a a').1 = a := rfl

end pair

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem list_cb_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) : ∀ (ls : List (Fin r)) (Ψ : RadSp k r z z' π π'),
    ((((ls.map L.cb).prod).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => (ls.map fun a => star (c a)).prod • (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g
  | [], Ψ => by
    funext c g
    simp only [List.map_nil, List.prod_nil, one_smul]
    rfl
  | a :: ls, Ψ => by
    funext c g
    rw [List.map_cons, List.prod_cons, fst_mul_apply, hL.2.2.2.2.1 a, fst_mkP, X.op_apply,
      list_cb_apply X L hL ls Ψ]
    simp only [crd, opL, cbOp, List.map_cons, List.prod_cons, mul_smul]

theorem list_c_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) : ∀ (ls : List (Fin r)) (Ψ : RadSp k r z z' π π'),
    ((((ls.map L.c).prod).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => (ls.map fun a => c a).prod • (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g
  | [], Ψ => by
    funext c g
    simp only [List.map_nil, List.prod_nil, one_smul]
    rfl
  | a :: ls, Ψ => by
    funext c g
    rw [List.map_cons, List.prod_cons, fst_mul_apply, hL.2.2.1 a, fst_mkP, X.op_apply,
      list_c_apply X L hL ls Ψ]
    simp only [crd, opL, cOp, List.map_cons, List.prod_cons, mul_smul]

theorem drb_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Ψ : RadSp k r z z' π π') :
    (((L.Drb).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      CutMP.dMul (CutMP.drbF r) (Ψ : Fn k r (Wq →L[ℂ] Wp)) := by
  have e : L.Drb = ((List.finRange r).map L.cb).prod := by
    rw [R.LevelData.Drb, List.ofFn_eq_map]
  rw [e, list_cb_apply X L hL]
  funext c g
  simp only [CutMP.dMul, CutMP.drbF, map_prod]
  congr 1

theorem dr_apply (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hL : IsActualLevel X L) (Ψ : RadSp k r z z' π π') :
    (((L.Dr).1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      CutMP.dMul (CutMP.drF r) (Ψ : Fn k r (Wq →L[ℂ] Wp)) := by
  have e : L.Dr = ((List.finRange r).map L.c).prod := by
    rw [R.LevelData.Dr, List.ofFn_eq_map]
  rw [e, list_c_apply X L hL]
  funext c g
  simp only [CutMP.dMul, CutMP.drF]
  congr 1

theorem st_fst {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} (X : ActualOps P.k P.r z z' π π')
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (hQQ : ∀ Y, st.QQ Y = M.sgn P l0 • X.QQ Y)
    (Y : ℂ) (a b : Fin 2) : (st.QQ Y a b).1 = M.sgn P l0 • X.t Y a b := by
  rw [hQQ Y, Matrix.smul_apply, ActualOps.QQ, Matrix.of_apply, Qx8.smul_mkP]
  rfl

theorem t_slice_congr (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) (Ψ : RadSp k r z z' π π')
    (F : Fn k r (Wq →L[ℂ] Wp)) (x : (Fin r → ℂ) × Mx k r) (hx : x ∈ DomR k r z z')
    (hF : ∀ y ∈ Glev k r (Fin.last r) ∩ Qx8.Dp k r z z', (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 y = F x.1 y) :
    tL k r z z' (Fin.last r) Y a b ((Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1) x.2 =
      tL k r z z' (Fin.last r) Y a b (F x.1) x.2 := by
  have hs := Qx8.slice_smooth Ψ.2 hx.1
  exact (transfer_linear_local _ k r z z' (Fin.last r) (Qx8.Dp k r z z') Y a b _ _ 0 (Qx8.Dp_open k r z z') hs
    (Qx8.smoothLev_congr (Qx8.Dp_open k r z z') hs (fun y hy => (hF y hy).symm)) x.2
    ⟨hx.2.1, hx.2.2⟩).2 hF

end RhRPf

open RhRPf in
theorem spectral_right_rho_action : RDSRhR := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD hl1 hl2 hr Y hY
  obtain ⟨_, _, hL, hQQ, -⟩ := hD
  refine ⟨M.sgn P l0, ?_⟩
  intro J hJ Φ hΦ x hx
  have eT : L.Tprod Y = Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y P.r := by
    rw [Formalism.FourierDecayAlt.P.TLB.rma_pref_take, ← Formalism.FourierDecayAlt.P.TLB.tprod_take_all]
  have hch := PBN.radSide_chain X L hL Y P.r le_rfl

  have hA : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Ar Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vAB P.r Y P.r) 0) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    have h1 := (hch Φ (x.1, y) hxy).1
    rw [← eT] at h1
    rw [R.LevelData.Ar, h1]
    simp only [crd, Q.cmp, if_true]
    exact (PBN.vAB_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).1
  have hB : ∀ y ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx8.Dp P.k P.r z z',
      (((L.Br Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y =
        crd (Q.cmp (vAB P.r Y P.r) 1) (resG P.k P.r (Fin.last P.r) J) x.1 y := by
    intro y hy
    have hxy : (x.1, y) ∈ DomR P.k P.r z z' := ⟨hx.1, hy.1, hy.2⟩
    have h1 := (hch Φ (x.1, y) hxy).2
    rw [← eT] at h1
    rw [R.LevelData.Br, h1]
    simp only [crd, Q.cmp, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    exact (PBN.vAB_loc Y P.r _ _ (fun c' hc' => hΦ (c', y) ⟨hc', hy.1, hy.2⟩) x.1 hx.1).2
  have e1 : (((RhR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
      (((L.Drb).1 ((st.QQ Y 1 0).1 ((L.Ar Y).1 Φ) + (st.QQ Y 1 1).1 ((L.Br Y).1 Φ)) :
        RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, drb_apply X L hL, st_fst X st l0 hQQ, st_fst X st l0 hQQ]
  simp only [CutMP.dMul, CutMP.rhGrp, Submodule.coe_add, Pi.add_apply, LinearMap.smul_apply,
    Submodule.coe_smul, Pi.smul_apply, QL, grp]
  rw [X.t_apply Y 1 0 _ x hx, X.t_apply Y 1 1 _ x hx,
    t_slice_congr X Y 1 0 _ _ x hx hA, t_slice_congr X Y 1 1 _ _ x hx hB]
  simp only [smul_add, smul_comm (CutMP.drbF P.r x.1) (M.sgn P l0)]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_pairing_locality : RDSPLoc := by
  intro k r Wp Wq _ _ _ _ _ _ Θ U X Y hU hXY g hgU hgV
  have h : ∀ x ∈ B.GV k r, x ∈ U → X x = Y x := fun x hx hxU => hXY x hxU hx
  exact ⟨Formalism.FourierDecayAlt.P.MinorPolynomials.opApply_congr Θ hU h hgV hgU,
    Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opAdj_congr_GV Θ hU h g hgV hgU⟩

end Formalism.FourierDecayAlt.P.CutSE
end

section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem radial_identity_of_spectral_data : RDRadIdOfSpec :=
  rDRadIdOfSpec_of_grpId_theta
    (rDGrpIdOfSpec_of_radIdAlg (rDRadIdAlg_of_collapse_gauge_rearr radial_collapse radial_gauge_identity radial_rearrangement)
      radial_start_coordinates radial_wave_radial Formalism.FourierDecayAlt.P5.waveCExists radial_residue_formula radial_wave_function_field radial_operator_function_field radial_group_residue)
    (Formalism.FourierDecayAlt.P.CutMP.JA.LT.thetaJ_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds)
    radial_orbital_niceness radial_wave_orbital radial_operator_locality

theorem radDecay_of_spec (h : RDIdentSpec) : RadDecay :=
  radDecay_of_ABQ (rDIdentABQ_of_spec h radial_identity_of_spectral_data)

end Formalism.FourierDecayAlt.P.CutSE
end
