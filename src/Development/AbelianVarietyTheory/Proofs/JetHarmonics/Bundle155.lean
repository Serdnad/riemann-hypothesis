module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivativeCongruenceGermIntegralTranslate
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle153
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle149
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerate
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle077
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialRaisingOperatorsPointwiseAdjointPair
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

theorem _root_.GlobalTheory.T.exists_shifted_types_lower_bound_alt : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp) (Vm : Type) (_ : NormedAddCommGroup Vm) (_ : InnerProductSpace ℂ Vm) (_ : FiniteDimensional ℂ Vm) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), IsType k r z πp (Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ))) ∧ IsType k r z πm (Function.update u l (u l - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  first | exact @GlobalTheory.WigSh.exists_shifted_types_lower_bound | exact GlobalTheory.WigSh.exists_shifted_types_lower_bound | (intros; apply GlobalTheory.WigSh.exists_shifted_types_lower_bound <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.derivative_congruence_germ_integral_translate : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt → JetSer.SerExSt → JetSer.RosIdSt → JetSer.ChartBCSt → FamGerm.GermExSt → EigGermSt := by
  first | exact @GlobalTheory.EigenGerm.eigen_germ | exact GlobalTheory.EigenGerm.eigen_germ | (intros; apply GlobalTheory.EigenGerm.eigen_germ <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem aesm_pi_of_finite {α ι E : Type} [MeasurableSpace α] {μ : Measure α} [Finite ι] [NormedAddCommGroup E]
    (f : α → ι → E) (hf : ∀ i, AEStronglyMeasurable (fun a => f a i) μ) : AEStronglyMeasurable f μ := by
  classical
  have := Fintype.ofFinite ι
  have e : f = fun a => ∑ i, (Pi.single i (f a i) : ι → E) := by
    funext a; rw [Finset.univ_sum_single]
  rw [e]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (continuous_single (A := fun _ : ι => E) i).comp_aestronglyMeasurable (hf i)

theorem measurable_nPt_bigPt (k r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) = fun c =>
      ∏ i : Fin (r + 1), (if 1 + (i : ℕ) = r + 1 then (‖c (Fin.last r)‖ ^ 2 - TT) ^ (k - 1)
        else ‖c i‖ ^ (2 * (C.Mlev k r (1 + (i : ℕ)) - 2))) := by
    funext c
    unfold TBB.nPt D.ptGG
    rw [Formalism.FourierDecayAlt.P.CutBP.ptLast_bigPt, Complex.normSq_eq_norm_sq]
    unfold TBB.bigPt
    rw [Formalism.FourierDecayAlt.P.CutBP.level_product_of_constant_weights]
  rw [e]
  refine Finset.measurable_prod _ fun i _ => ?_
  split_ifs
  · fun_prop
  · exact ((measurable_pi_apply i).norm).pow_const _

theorem measurable_wPt_bigPt (r : ℕ) (TT : ℝ) :
    Measurable fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c) := by
  have e : (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c)) = fun c =>
      ‖∏ i, c i‖ ^ 2 / (‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2) := by
    funext c
    show Top.wPt TT r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold Top.wPt D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [e]
  refine Measurable.div ?_ ?_
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ => ‖∏ i, c i‖ ^ 2).measurable
  · exact (by fun_prop : Continuous fun c : Fin (r + 1) → ℂ =>
      ‖∏ i, c i‖ ^ 2 - TT * ‖∏ i : Fin r, c i.castSucc‖ ^ 2).measurable

theorem aestronglyMeasurable_tv : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) H →
    AEStronglyMeasurable (tv p H w) volume := by
  intro Wp Wq _ _ _ _ _ _ P p Cb H w hD hw hH
  unfold tv
  refine (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable (aesm_pi_of_finite _ fun x => ?_)
  have hV := GlobalTheory.bigCell_vector_aestronglyMeasurable Wp Wq P p _ (GlobalTheory.liftedWord_continuousOn_GPos Wp Wq P p Cb w x.1 H hD hw hH)
  have hc : Continuous fun X : Wq →L[ℂ] Wp => B.hsVec ((p.TP.E x.2).comp X) := by
    unfold B.hsVec
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (p.TP.E x.2).continuous.comp
      (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  refine AEStronglyMeasurable.smul (f := fun c : Fin (P.r + 1) → ℂ =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ)) ?_ (hc.comp_aestronglyMeasurable hV)
  refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
  refine (measurable_nPt_bigPt _ _ _).sqrt.mul ?_
  unfold Top.dH
  exact (((measurable_wPt_bigPt _ _).pow_const _).mul_const _).sqrt

end GlobalTheory.TopVec
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.tendsto_topVector_compactApproximants_bigCell : ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ, Tendsto (fun n : ℕ => tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w c) atTop (𝓝 (tv p (D.cutF p.T.base χ f ε) w c)) := by
  first | exact @GlobalTheory.TopVec.tv_approx_tendsto | exact GlobalTheory.TopVec.tv_approx_tendsto | (intros; apply GlobalTheory.TopVec.tv_approx_tendsto <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.topVector_cutoff_eq_and_vanish : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (χ : ℝ → ℝ) (δ ε : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) F → (ε < TBB.Gp p (TBB.bigPt P.r c) → tv p (D.cutF p.T.base χ F ε) w c = tv p F w c) ∧ (TBB.Gp p (TBB.bigPt P.r c) < δ * ε → tv p (D.cutF p.T.base χ F ε) w c = 0) ∧ (TBB.Gp p (TBB.bigPt P.r c) ≤ 0 → tv p F w c = 0) := by
  first | exact @GlobalTheory.TopVec.tv_cutF | exact GlobalTheory.TopVec.tv_cutF | (intros; apply GlobalTheory.TopVec.tv_cutF <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → NonDeg X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H := by
  first | exact @GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg | exact GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg | (intros; apply GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

open Filter Topology MeasureTheory in
private lemma opApply_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (c : ℂ)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply Θ (c • F) g = c • _root_.Formalism.FourierDecayAlt.B.opApply Θ F g := by
  unfold _root_.Formalism.FourierDecayAlt.B.opApply
  simp only [_root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, Pi.smul_apply, map_smul]
  rw [List.smul_sum, List.map_map]
  rfl

open Filter Topology MeasureTheory in
private lemma vecV_smul_jet_harmonics {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν : Fin (2 * r + k + 1) → ℂ) (m : _root_.Formalism.FourierDecayAlt.B.Mat k r) (c : ℂ)
    (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m (fun g => c • G g) q = c • _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m G q := by
  unfold _root_.Formalism.FourierDecayAlt.D.vecV
  split_ifs with h h'
  · apply _root_.Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae
    refine MeasureTheory.ae_of_all _ fun x => ?_
    unfold _root_.Formalism.FourierDecayAlt.D.orbIntegrand _root_.Formalism.FourierDecayAlt.B.rho
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    exact smul_comm _ _ _
  · simp
  · simp

open Filter Topology MeasureTheory in
private lemma topLift_vecV_add_smul_lemma {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : _root_.Formalism.FourierDecayAlt.M.Par} (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    {Cb : ℝ} (a : ℂ) {H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List _root_.Formalism.FourierDecayAlt.C.Letter}
    (hdom : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hcut : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w)
    (h₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁) (h₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂) (i : _root_.Formalism.FourierDecayAlt.Wd.Ix (Fin w.length))
    (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    p.V (p.Θ.Θ w i (H₁ + a • H₂)) q = p.V (p.Θ.Θ w i H₁) q + a • p.V (p.Θ.Θ w i H₂) q := by
  obtain ⟨nf, fib, o, κ, D, -, hD, -, -, hΘ⟩ := hdom w hcut i
  have hlen : ∀ T ∈ D, T.word.length ≤ o := fun T hT => by
    obtain ⟨_, _, _, _, es, -, -, hl, -⟩ := hD.2.2 T hT
    omega
  have hpos : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GPos p.T.base, g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ :=
    fun g hg => ⟨hg.1, hg.2, by simp⟩
  have hc₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₁ hD.1
  have hc₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₂ hD.1
  have e₁ : p.V (p.Θ.Θ w i H₁) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₁ g (hpos g hg)
  have e₂ : p.V (p.Θ.Θ w i H₂) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₂ g (hpos g hg)
  have e₃ : p.V (p.Θ.Θ w i (H₁ + a • H₂)) q =
      p.V (fun g => _root_.Formalism.FourierDecayAlt.B.opApply D H₁ g - (fun g => (-a) • _root_.Formalism.FourierDecayAlt.B.opApply D H₂ g) g) q := by
    refine _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => ?_
    have hsum : H₁ + a • H₂ = H₁ - (-a) • H₂ := by rw [neg_smul, sub_neg_eq_add]
    rw [hΘ _ g (hpos g hg), hsum,
      _root_.Formalism.FourierDecayAlt.P.PBE.opApply_subGV D hlen (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₁.1 o) (_root_.Formalism.FourierDecayAlt.P.B4.ckOn_smul (-a) (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₂.1 o)) g hg.1, opApply_smul]
  have e₄ := _root_.Formalism.FourierDecayAlt.P.PBN.vecV_sub p.T.base p.ν' p.m₀ q hc₁ (_root_.Formalism.FourierDecayAlt.P.PBN.cpt_smul p.T.base (-a) hc₂)
  have e₅ := vecV_smul_jet_harmonics p.T.base p.ν' p.m₀ (-a) (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q
  rw [e₁, e₂, e₃]
  change _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q = _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q + a • _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q
  rw [e₄, e₅, neg_smul, sub_neg_eq_add]

open Filter Topology MeasureTheory in
private lemma hsVec_add_jet_harmonics {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (A B : Wq →L[ℂ] Wp) : _root_.Formalism.FourierDecayAlt.B.hsVec (A + B) = _root_.Formalism.FourierDecayAlt.B.hsVec A + _root_.Formalism.FourierDecayAlt.B.hsVec B := by
  unfold _root_.Formalism.FourierDecayAlt.B.hsVec
  rfl


open Filter Topology MeasureTheory in
theorem _root_.GlobalTheory.TopVec.tv_add_smul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (Cb : ℝ) (a : ℂ) (H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (c : Fin (P.r + 1) → ℂ), _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁ → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂ → _root_.GlobalTheory.TopVec.tv p (H₁ + a • H₂) w c = _root_.GlobalTheory.TopVec.tv p H₁ w c + a • _root_.GlobalTheory.TopVec.tv p H₂ w c := by
  intro Wp Wq _ _ _ _ _ _ P p Cb a H₁ H₂ w c hdom hcut h₁ h₂
  unfold _root_.GlobalTheory.TopVec.tv
  rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  funext x
  rw [topLift_vecV_add_smul_lemma p a hdom hcut h₁ h₂, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, hsVec_add_jet_harmonics, _root_.Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, smul_add, Pi.add_apply, Pi.smul_apply,
    smul_comm a]

end GlobalTheory.TopVec
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.radialMultipliers_satisfy_normalForm_relations : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  first | exact @GlobalTheory.HatNF.MulRelActual.mulRel_actual | exact GlobalTheory.HatNF.MulRelActual.mulRel_actual | (intros; apply GlobalTheory.HatNF.MulRelActual.mulRel_actual <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.radialRaisingOperators_pointwiseAdjointPair : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), PtAdj P Bs (d.SS l) := by
  first | exact @GlobalTheory.HatNF.RaiseAdj.ptAdj_SS | exact GlobalTheory.HatNF.RaiseAdj.ptAdj_SS | (intros; apply GlobalTheory.HatNF.RaiseAdj.ptAdj_SS <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.PtBBasic

open Formalism.FourierDecayAlt.P.TLB

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nv_of_mulAt {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {s : ℂ} (h : MulAt x T s)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : nv (T Φ) x = ‖s‖ * nv Φ x := by
  unfold nv
  rw [h Φ, ← norm_smul]
  rfl

theorem nv_nonneg {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) : 0 ≤ nv Φ x := norm_nonneg _

theorem ptB_of_mulAt {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (b : RA P Bs) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', ∃ s : ℂ, MulAt x b.1 s ∧ ‖s‖ ≤ C) : PtB P Bs b := by
  refine ⟨C, hC, fun Φ x hx => ?_⟩
  obtain ⟨s, hs, hle⟩ := h x hx
  rw [nv_of_mulAt hs]
  exact mul_le_mul_of_nonneg_right hle (nv_nonneg Φ x)

theorem ptB_mul {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (a b : RA P Bs) (ha : PtB P Bs a) (hb : PtB P Bs b) :
    PtB P Bs (a * b) := by
  obtain ⟨C, hC, ha⟩ := ha
  obtain ⟨C', hC', hb⟩ := hb
  refine ⟨C * C', mul_nonneg hC hC', fun Φ x hx => ?_⟩
  rw [pr_mul_fst, Module.End.mul_apply, mul_assoc]
  exact (ha _ x hx).trans (mul_le_mul_of_nonneg_left (hb Φ x hx) hC)

theorem norm_ratio_le (a b : ℂ) (h : ‖a‖ = ‖b‖) : ‖a * b⁻¹‖ ≤ 1 := by
  rw [norm_mul, norm_inv, h]
  exact mul_inv_le_one

theorem sqrt_lt_zeta {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') :
    Real.sqrt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') < ‖Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2‖ := by
  have h := hx.2.2
  unfold Q.GGl at h
  rw [Complex.normSq_eq_norm_sq] at h
  have hn := norm_nonneg (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)
  rw [← Real.sqrt_sq hn]
  exact Real.sqrt_lt_sqrt (mul_pos Bs.T_pos Bs.T'_pos).le (by linarith)

end GlobalTheory.HatNF.PtBBasic

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt.P.TLB PtBBasic

theorem ptB_basic : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → (PtB P Bs 1 ∧ (∀ a b, PtB P Bs a → PtB P Bs b → PtB P Bs (a * b))) ∧ PtB P Bs d.L.ζi ∧ PtB P Bs d.L.ζbi ∧ PtB P Bs (d.L.D * d.L.Dbi) ∧ PtB P Bs (d.L.Db * d.L.Di) ∧ PtB P Bs (d.L.Drb * d.L.Dri) ∧ PtB P Bs (d.L.Dr * d.L.Drbi) ∧ ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < dR P Bs x.1 x.2 ∧ 0 < gR P Bs x.1 x.2 ∧ nv (d.L.Di.1 Φ) x = (dR P Bs x.1 x.2)⁻¹ * nv Φ x ∧ nv ((TL.gI d.L).1 Φ) x = (gR P Bs x.1 x.2)⁻¹ * nv Φ x := by
  intro Wp Wq _ _ _ _ _ _ Pa Bs X μ L0 st l0 d _ hd
  have hL := hd.1
  set L := d.L with hLdef
  have hDr : ∀ x, MulAt x L.Dr.1 (∏ a, x.1 a) := fun x =>
    mulAt_ofFn L.c _ fun l => act_c X L hL x l
  have hDri : ∀ x, MulAt x L.Dri.1 (∏ a, x.1 a)⁻¹ := fun x => by
    rw [← Finset.prod_inv_distrib]
    exact mulAt_ofFn L.ci _ fun l => act_ci X L hL x l
  have hDrb : ∀ x, MulAt x L.Drb.1 (star (∏ a, x.1 a)) := fun x => by
    rw [star_prod]
    exact mulAt_ofFn L.cb _ fun l => act_cb X L hL x l
  have hDrbi : ∀ x, MulAt x L.Drbi.1 (star (∏ a, x.1 a))⁻¹ := fun x => by
    rw [star_prod, ← Finset.prod_inv_distrib]
    exact mulAt_ofFn L.cbi _ fun l => act_cbi X L hL x l
  have hz : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζ.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) := by
    intro x hx; rw [hL.2.2.2.2.2.2.1]; exact act_fn X x hx 0
  have hzi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζi.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.1]; exact act_fn X x hx 1
  have hzb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζb.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 2
  have hzbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζbi.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 3
  have hGGi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.GGi.1 ((Q.GGl Pa.k Pa.r Bs.z Bs.z' x.2 : ℂ))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 5
  have hD : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.D.1 ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) :=
    fun x hx => mulAt_mul (hDr x) (hz x hx)
  have hDb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Db.1 (star ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx
    rw [star_mul']
    exact mulAt_mul (hDrb x) (hzb x hx)
  have hDi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Di.1 ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx
    rw [mul_inv, mul_comm]
    exact mulAt_mul (hzi x hx) (hDri x)
  have hDbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Dbi.1 (star ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx
    rw [star_mul', mul_inv, mul_comm]
    exact mulAt_mul (hzbi x hx) (hDrbi x)
  have hsq : 0 < Real.sqrt (Tz Pa.k Pa.r Bs.z * Tz Pa.k Pa.r Bs.z') :=
    Real.sqrt_pos.2 (mul_pos Bs.T_pos Bs.T'_pos)
  refine ⟨⟨?_, ptB_mul⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ => ⟨1, mulAt_one x, by simp⟩
  · refine ptB_of_mulAt _ _ (inv_pos.2 hsq).le fun x hx => ⟨_, hzi x hx, ?_⟩
    rw [norm_inv]
    exact inv_anti₀ hsq (sqrt_lt_zeta Bs hx).le
  · refine ptB_of_mulAt _ _ (inv_pos.2 hsq).le fun x hx => ⟨_, hzbi x hx, ?_⟩
    rw [norm_inv, norm_star]
    exact inv_anti₀ hsq (sqrt_lt_zeta Bs hx).le
  · exact ptB_of_mulAt _ 1 zero_le_one fun x hx =>
      ⟨_, mulAt_mul (hD x hx) (hDbi x hx), norm_ratio_le _ _ (norm_star _).symm⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x hx =>
      ⟨_, mulAt_mul (hDb x hx) (hDi x hx), norm_ratio_le _ _ (norm_star _)⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ =>
      ⟨_, mulAt_mul (hDrb x) (hDri x), norm_ratio_le _ _ (norm_star _)⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ =>
      ⟨_, mulAt_mul (hDr x) (hDrbi x), norm_ratio_le _ _ (norm_star _).symm⟩
  · intro Φ x hx
    have hc : (∏ a, x.1 a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a
    have hζ : Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2 ≠ 0 :=
      norm_pos_iff.1 (hsq.trans (sqrt_lt_zeta Bs hx))
    have hG := hx.2.2
    refine ⟨norm_pos_iff.2 (mul_ne_zero hc hζ), mul_pos (Complex.normSq_pos.2 hc) hG, ?_, ?_⟩
    · rw [nv_of_mulAt (hDi x hx), norm_inv]
      rfl
    · have h : MulAt x (TL.gI L).1 _ := mulAt_mul (mulAt_mul (hDri x) (hDrbi x)) (hGGi x hx)
      rw [nv_of_mulAt h]
      congr 1
      unfold gR
      rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_inv, norm_star, Complex.norm_real, Real.norm_of_nonneg hG.le,
        Complex.normSq_eq_norm_sq, sq, mul_inv, mul_inv]

end GlobalTheory.HatNF
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.bessel_gap_exists_functional : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  first | exact @GlobalTheory.exists_normalised_bessel_map | exact GlobalTheory.exists_normalised_bessel_map | (intros; apply GlobalTheory.exists_normalised_bessel_map <;> assumption)
end
