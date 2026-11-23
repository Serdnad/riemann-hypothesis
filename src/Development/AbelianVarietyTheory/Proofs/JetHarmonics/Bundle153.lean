module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle147
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosed
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateCoprimeOrderNotIncreaseThetaCombNorm
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle150
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExistsAndVectorEqSmulTranslate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle134
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle118
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle151
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem exists_shifted_types_lower_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp) (Vm : Type) (_ : NormedAddCommGroup Vm) (_ : InnerProductSpace ℂ Vm) (_ : FiniteDimensional ℂ Vm) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), IsType k r z πp (Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ))) ∧ IsType k r z πm (Function.update u l (u l - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ k r z π u l n₀ b hz hT hπ hreg hl1 hlk hgap hb hn hb1
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hm : m < n := by omega
  let i : Fin n := ⟨m, hm⟩
  obtain ⟨β, L, hL, hu, hd⟩ := GlobalTheory.exists_int_coords_of_regular_param n u (by simpa using hreg)
  obtain ⟨B, hB⟩ := (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).1
  have hgapZ : L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc := by
    have h := hd i.castSucc i.succ
    simp only [Fin.val_succ, Fin.val_castSucc, i] at h
    have : ((L i.succ + 2 * (n₀ : ℤ) + 1 : ℤ) : ℝ) ≤ ((L i.castSucc : ℤ) : ℝ) := by
      push_cast
      simp only [i]
      linarith
    exact_mod_cast this
  have hwide : (L 0 : ℝ) - (L (Fin.last n) : ℝ) ≤ 2 * b := by
    rw [hd]
    have h1 := abs_le.mp (hb (((0 : Fin (n + 1)) : ℕ) + 1) (by simp))
    have h2 := abs_le.mp (hb (((Fin.last n : Fin (n + 1)) : ℕ) + 1) (by simp))
    linarith [h1.2, h2.1]
  obtain ⟨Vp, iP1, iP2, iP3, πp, Ap, hπp, hAp, hwp⟩ :=
    GlobalTheory.T.exists_wignerContraction_chain_raising V n r z π u β L B i.succ n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : j ≤ i.castSucc := Fin.le_castSucc_iff.mpr hj
      have := hL.antitone hj'
      omega)
  obtain ⟨Vm, familyMassRatio, familyMassSecondLine, iM3, πm, Am, hπm, hAm, hwm⟩ :=
    GlobalTheory.T.exists_wignerContraction_chain_lowering V n r z π u β L B i.castSucc n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hj
      have := hL.antitone hj'
      omega)
  refine ⟨Vp, iP1, iP2, iP3, Vm, familyMassRatio, familyMassSecondLine, iM3, πp, πm, Ap, Am, hπp, hπm, hAp, hAm, ?_⟩
  refine GlobalTheory.WigSh.lower_bound_spreads V Vp Vm n r z π πp πm B Ap Am n₀ b hz hT hπ.2.2.2.1 hπp.2.2.2.1
    hπm.2.2.2.1 hB hAp hAm ?_
  intro v
  have hyp := (GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB).1
  have hdec := (Formalism.FourierDecayAlt.P.branching_decomposition V n (EB π B) β L hyp).2
  have hspan : ⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA (EB π B)) (shf β M.1) = ⊤ := by
    rw [← hdec, iSup_subtype]
  have key := GlobalTheory.norm_sq_adjoint_add_ge_of_joint_eigenspaces V Vp Vm {M : Fin n → ℤ // Box L M}
    (fun M => CapSp (subA (EB π B)) (shf β M.1)) (Ap (B (Fin.last n))) (Am (B (Fin.last n))) _ _
    ((3 * b) ^ (2 * n₀))⁻¹ hspan (fun M w hw => ⟨hwp M.1 w hw, hwm M.1 w hw⟩)
    (fun M => GlobalTheory.WigSh.chain_lower_bound n L M.1 i n₀ b hL M.2 hgapZ hb1 hn hwide) v
  have hpos : 0 < (3 * b) ^ (2 * n₀) := by positivity
  rwa [inv_mul_le_iff₀ hpos] at key

end GlobalTheory.WigSh
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace GlobalTheory.TopVec

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
private lemma vecV_cutoff_lemma {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (B : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : _root_.Formalism.FourierDecayAlt.B.Mat k r)
    (H : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (q : _root_.Formalism.FourierDecayAlt.C.LPt) (ψ : ℝ → ℝ) (t : ℝ) :
    _root_.Formalism.FourierDecayAlt.D.vecV B ν' m₀ (_root_.Formalism.FourierDecayAlt.D.cutF B ψ H t) q =
      ((ψ (_root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r B.z * _root_.Formalism.QuantumDeterminants.Tz k r B.z') r q / t) : ℝ) : ℂ) •
        _root_.Formalism.FourierDecayAlt.D.vecV B ν' m₀ H q := by
  unfold _root_.Formalism.FourierDecayAlt.D.vecV
  split_ifs with h h'
  · rw [_root_.Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF, _root_.Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat _ _ _ _ h'.choose_spec.2.1]
  · simp
  · simp

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
private lemma foldr_RdV_zero {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : List (_root_.Formalism.FourierDecayAlt.B.Mat k r)) : List.foldr _root_.Formalism.REAL.RdV (fun _ => (0 : E)) w = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    rw [List.foldr_cons, ih]
    funext g
    unfold _root_.Formalism.REAL.RdV
    simp

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
private lemma opApply_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (D : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply D (fun _ => 0) g = 0 := by
  unfold _root_.Formalism.FourierDecayAlt.B.opApply
  apply List.sum_eq_zero
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨T, -, rfl⟩ := hx
  unfold _root_.Formalism.FourierDecayAlt.B.Rw
  rw [foldr_RdV_zero]
  simp

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
theorem _root_.GlobalTheory.TopVec.tv_cutF (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    (Cb : ℝ) (χ : ℝ → ℝ) (δ ε : ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List _root_.Formalism.FourierDecayAlt.C.Letter)
    (c : Fin (P.r + 1) → ℂ) (hD : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hw : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w)
    (hχ : _root_.Formalism.FourierDecayAlt.C6.IsCut0 χ) (hδ : ∀ x, x < δ → χ x = 0) (hε : 0 < ε)
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F) :
    (ε < _root_.Formalism.FourierDecayAlt.TBB.Gp p (_root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c) →
      _root_.GlobalTheory.TopVec.tv p (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) w c = _root_.GlobalTheory.TopVec.tv p F w c) ∧
    (_root_.Formalism.FourierDecayAlt.TBB.Gp p (_root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c) < δ * ε →
      _root_.GlobalTheory.TopVec.tv p (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) w c = 0) ∧
    (_root_.Formalism.FourierDecayAlt.TBB.Gp p (_root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c) ≤ 0 → _root_.GlobalTheory.TopVec.tv p F w c = 0) := by
  set q := _root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c with hq
  set G := _root_.Formalism.FourierDecayAlt.TBB.Gp p q with hGdef
  have hG : G = _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z * _root_.Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z') P.r q := rfl
  have hV : ∀ H, p.V H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q := fun H => rfl
  have hcut : ∀ (ψ : ℝ → ℝ) (H : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp) (t : ℝ) (g : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r),
      _root_.Formalism.FourierDecayAlt.D.cutF p.T.base ψ H t g =
        ((ψ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / t) : ℝ) : ℂ) • H g := fun _ _ _ _ => rfl
  have hcont : Continuous (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z') := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont _ _
  have hzero : ∀ F' : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp,
      (∀ e, p.V (p.Θ.Θ w e F') q = 0) → _root_.GlobalTheory.TopVec.tv p F' w c = 0 := by
    intro F' h
    unfold _root_.GlobalTheory.TopVec.tv
    simp [← hq, h, _root_.Formalism.FourierDecayAlt.B.hsVec]
    funext x
    try simp only [Pi.zero_apply]
    rw [← Pi.zero_def, WithLp.toLp_zero, smul_zero]
  have htv : ∀ F₁ F₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp,
      (∀ e, p.V (p.Θ.Θ w e F₁) q = p.V (p.Θ.Θ w e F₂) q) →
        _root_.GlobalTheory.TopVec.tv p F₁ w c = _root_.GlobalTheory.TopVec.tv p F₂ w c := by
    intro F₁ F₂ h
    unfold _root_.GlobalTheory.TopVec.tv
    simp only [← hq, h]
  have hV0 : G ≤ 0 → ∀ H, p.V H q = 0 := by
    intro h H
    rw [hV]
    unfold _root_.Formalism.FourierDecayAlt.D.vecV
    rw [dite_eq_right]
    rintro ⟨-, h'⟩
    rw [← hG] at h'
    linarith
  refine ⟨?_, ?_, fun h => hzero F fun e => hV0 h _⟩
  · intro hlt
    have hGpos : 0 < G := hε.trans hlt
    apply htv
    intro e
    obtain ⟨nf, fib, o, κ, Dop, -, -, -, -, hDop⟩ := hD w hw e
    rw [hV, hV]
    have h1 : ∀ H, _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀
        (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if ε / G < x then 1 else 0) H G) q := by
      intro H
      rw [vecV_cutoff_lemma, ← hG, div_self hGpos.ne', if_pos ((div_lt_one hGpos).mpr hlt)]
      simp
    rw [h1, h1 (p.Θ.Θ w e F)]
    apply _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos
    intro g hg
    rw [hcut, hcut]
    by_cases hgε : ε < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g
    · have hOQ : g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ := ⟨hg.1, hg.2, by simp⟩
      have hloc : _root_.Formalism.FourierDecayAlt.B.opApply Dop (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) g = _root_.Formalism.FourierDecayAlt.B.opApply Dop F g := by
        apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Dop (isOpen_lt continuous_const hcont) _ g hgε
        intro x hx
        have hx' : ε < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' x := hx
        rw [hcut, hχ.2.2 _ ((le_div_iff₀ hε).mpr (by linarith))]
        simp
      rw [hDop _ g hOQ, hDop _ g hOQ, hloc]
    · have : ¬ (ε / G < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / G) := by
        rw [div_lt_div_iff_of_pos_right hGpos]; exact hgε
      simp [this]
  · intro hlt
    rcases le_or_gt G 0 with hG0 | hGpos
    · exact hzero _ fun e => hV0 hG0 _
    apply hzero
    intro e
    obtain ⟨nf, fib, o, κ, Dop, -, -, -, -, hDop⟩ := hD w hw e
    rw [hV]
    have h1 : ∀ H, _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀
        (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if x < δ * ε / G then 1 else 0) H G) q := by
      intro H
      rw [vecV_cutoff_lemma, ← hG, div_self hGpos.ne', if_pos ((one_lt_div hGpos).mpr hlt)]
      simp
    rw [h1]
    have h2 : _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base
          (fun x => if x < δ * ε / G then 1 else 0) (p.Θ.Θ w e (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε)) G) q =
        _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base
          (fun x => if x < δ * ε / G then 1 else 0) (fun _ => 0) G) q := by
      apply _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos
      intro g hg
      rw [hcut, hcut]
      by_cases hgd : _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g < δ * ε
      · have hOQ : g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ := ⟨hg.1, hg.2, by simp⟩
        have hloc : _root_.Formalism.FourierDecayAlt.B.opApply Dop (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) g = _root_.Formalism.FourierDecayAlt.B.opApply Dop (fun _ => 0) g := by
          apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Dop (isOpen_lt hcont continuous_const) _ g hgd
          intro x hx
          have hx' : _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' x < δ * ε := hx
          rw [hcut, hδ _ ((div_lt_iff₀ hε).mpr hx')]
          simp
        rw [hDop _ g hOQ, hloc, opApply_zero]
      · have : ¬ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / G < δ * ε / G) := by
          rw [div_lt_div_iff_of_pos_right hGpos]; exact hgd
        simp [this]
    have h3 : _root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if x < δ * ε / G then 1 else 0)
        (fun _ => (0 : Wq →L[ℂ] Wp)) G = _root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun _ => 0) (fun _ => 0) G := by
      funext g
      rw [hcut, hcut]
      simp
    rw [h2, h3, vecV_cutoff_lemma]
    simp

end GlobalTheory.TopVec
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem vecV_theta_approx_tendsto (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ w, KB.CutWord P p.l0 w → w.length ≤ N → ∀ (e : Wd.Ix (Fin w.length)) (q : C.LPt), Tendsto
        (fun n => D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (fun g => cut n g • D.cutF p.T.base χ f ε g)) q) atTop
        (𝓝 (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (D.cutF p.T.base χ f ε)) q)) := by
  obtain ⟨c₂, hc₂⟩ := vecV_cut_op
  refine ⟨5 * max Cb 0 + max Cb 0 ^ 2 + 1 + |c₂|, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut w hw hwN e q
  have hXn : ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) = 2 * (P0.r : ℝ) + P0.k + 1 := by push_cast; ring
  have hr0 : (0 : ℝ) ≤ P0.r := Nat.cast_nonneg _
  have hrX : (P0.r : ℝ) + 1 ≤ 2 * (P0.r : ℝ) + P0.k + 1 := by
    have : (0 : ℝ) ≤ P0.k := Nat.cast_nonneg _
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hCb0 : (0 : ℝ) ≤ max Cb 0 := le_max_right _ _
  have hcut' : ∀ n g, cut n g = 1 - P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    rw [hcut n g]
    simp [P.JCx2.pdPsi, P.JCx2.pdPhi, P.JCx2.pdChi, P.JCx2.pdSq]
  have hFck : B.CkOn ⊤ (B.GV P0.k P0.r) (D.cutF p.T.base χ f ε) :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf ε
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  have hFv : ∀ g, Gf P0.k P0.r p.T.base.z p.T.base.z' g < ε * δ → D.cutF p.T.base χ f ε g = 0 := by
    intro g hg
    show ((χ (Gf P0.k P0.r p.T.base.z p.T.base.z' g / ε) : ℝ) : ℂ) • f g = 0
    rw [hχ0 _ (by rw [div_lt_iff₀ hε]; linarith), Complex.ofReal_zero, zero_smul]
  obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hDD w hw e
  have hcongr : ∀ G, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e G) q =
      D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop G) q :=
    fun G => vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => hΘ G g ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
  simp only [hcongr]
  have ho' : (o : ℝ) ≤ max Cb 0 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
    calc (o : ℝ) ≤ Cb * w.length * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) := ho
      _ ≤ max Cb 0 * w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by
        rw [hXn]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
          (by linarith)
      _ ≤ max Cb 0 * N * (2 * (P0.r : ℝ) + P0.k + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hwN) hCb0) (by linarith)
  have hκ' : (κ : ℝ) ≤ max Cb 0 * ((P0.r : ℝ) + 1) * o :=
    hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
      (Nat.cast_nonneg _))
  have hthr := thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 0) c₂ o κ A hr0 hrX hN0 hCb0
    (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
  obtain ⟨bF, hbF⟩ := cutF_inCC p.T.base hχ hfA hε (A - 2 * ((P0.r : ℝ) + 1) * o) o (by linarith)
  exact hc₂ P0.k P0.r Wp Wq p.T.base p.ν' p.m₀ q _ cut nf fib o κ Dop (ε * δ)
    (A - 2 * ((P0.r : ℝ) + 1) * o) bF hfib hIn (mul_pos hε hδ) hFv hFck hbF hcut'
    (by rw [hXn]; linarith [hthr])

theorem tv_approx_tendsto : ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ, Tendsto (fun n : ℕ => tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w c) atTop (𝓝 (tv p (D.cutF p.T.base χ f ε) w c)) := by
  intro Cb
  obtain ⟨Cc, hC⟩ := vecV_theta_approx_tendsto Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ A N w hDD hχ hf hfA hA hw hwN ε hε c
  have h := hC Wp Wq P0 p f χ ε A N _ hDD hχ hε hf hfA hA (fun _ _ => rfl) w hw hwN
  unfold tv
  refine ((PiLp.continuous_toLp 2 _).tendsto _).comp ?_
  refine tendsto_pi_nhds.2 fun x => ?_
  apply Tendsto.const_smul
  refine (P.BetaSesquilinearity.hsVec_cont.tendsto _).comp ?_
  exact ((continuous_const.clm_comp continuous_id).tendsto _).comp (h x.1 (TBB.bigPt P0.r c))

end GlobalTheory.TopVec
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.hatLetters_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  first | exact @GlobalTheory.HatNF.hats_mem_nfSpan | exact GlobalTheory.HatNF.hats_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_mem_nfSpan <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.list_prod_hatLetters_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ H : List A, (∀ h ∈ H, h ∈ hats d.L) → H.prod ∈ nfSpan d T 0 (a * H.length) H.length := by
  first | exact @GlobalTheory.HatNF.hats_prod_mem_nfSpan | exact GlobalTheory.HatNF.hats_prod_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_prod_mem_nfSpan <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.wordOperator_column_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ e : Ix S, ((ofWord L st w).F * TL.bTA L w) e e1 ∈ nfSpan d (hats d.L) w.length 0 w.length := by
  first | exact @GlobalTheory.HatNF.word_mem_nfSpan | exact GlobalTheory.HatNF.word_mem_nfSpan | (intros; apply GlobalTheory.HatNF.word_mem_nfSpan <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.polyLift_one_mono_mul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), PolyLift P Bs 0 0 1 ∧ (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → PolyLift P Bs o κ a → PolyLift P Bs o' κ' a) ∧ ∀ o₁ κ₁ o₂ κ₂ a b, PolyLift P Bs o₁ κ₁ a → PolyLift P Bs o₂ κ₂ b → PolyLift P Bs (o₁ + o₂) (κ₁ + κ₂) (a * b) := by
  first | exact @GlobalTheory.HatNF.polyLift_closed | exact GlobalTheory.HatNF.polyLift_closed | (intros; apply GlobalTheory.HatNF.polyLift_closed <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good M.ι d n s y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ hat M.ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) (U1 d t θ)) := by
  first | exact @GlobalTheory.MomOne.TranslateLaw.main | exact GlobalTheory.MomOne.TranslateLaw.main | (intros; apply GlobalTheory.MomOne.TranslateLaw.main <;> assumption)
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.translate_coprime_order_not_increase_theta_comb_norm : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  first | exact @GlobalTheory.MomOne.TranslNorm.translate_bd | exact GlobalTheory.MomOne.TranslNorm.translate_bd | (intros; apply GlobalTheory.MomOne.TranslNorm.translate_bd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.integralChart_columns_to_tuple_harmonicValues : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (tors : P.TorsionIso) (ϖ : T.V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v), letI := io.toAlgebra; ∃ x hx j hj u hu B hB ρ hρ, B.G.F = C.FT ∧ B.A.act = C.actT ∧ ∀ (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (s : Fin n → Fam P.D.toPre F g') (s' t : Fin n → Fam P.D.toPre F (g' * g)) (f : Fin n → PS F 1 (chD C.ch)), (∀ b, NuGe P.D Q F v g' (s b) 0 ∧ PullAl P.D F P.oD (star π) g' g (s b) (s' b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Transl (g' * g) π (s' b) (t b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Germ (g' * g) (t b) (f b)) → ∃ (S : Fam D'.toPre F g') (S₂ : Fam D'.toPre F (g' * g)) (p' : QkPt D'.toPre F (g' * g)) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε (g' * g)))) (ζ' : F) (x' : TFK (R := T.V) F ⟶ A'.A) (T₀ T₁ : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) (un : PS T.V 1 (chD C.ch)), BoxTup C P Q F v g g' π pG PU oD' S S₂ p' w' ζ' x' T₀ T₁ σ' h ∧ MvPowerSeries.constantCoeff un = 1 ∧ h = boxSer (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un) ∧ ∀ h₀ : PS F 2 (chD C.ch), B.IsCanonGauge F h₀ → ∀ (rk : (E →+* ℂ) → ℕ) (hrk : ∀ τ, rk τ ≤ Dw.mult τ) (Pp : MvPolynomial ((Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n) F), (∀ (τ : E →+* ℂ) (i : Fin (rk τ)) (i' : Fin (rk (ComplexEmbedding.conjugate τ))), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) (MvPolynomial.pderiv ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) Pp) = 0) → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.rename (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n)) Pp) = (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).colVal h₀ (g' * g) (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) Pp f := by
  first | exact @GlobalTheory.transfer_columns | exact GlobalTheory.transfer_columns | (intros; apply GlobalTheory.transfer_columns <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_setting_uniform_constant : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
  first | exact @GlobalTheory.BesselNormSq.normSq_coef | exact GlobalTheory.BesselNormSq.normSq_coef | (intros; apply GlobalTheory.BesselNormSq.normSq_coef <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.family_exists_unit_product_moment_le_Hsq_pow : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (l ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a, lenA k r z (Matrix.of x) a ^ 2) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1)) := by
  first | exact @GlobalTheory.MomProd.product_moment | exact GlobalTheory.MomProd.product_moment | (intros; apply GlobalTheory.MomProd.product_moment <;> assumption)
end
