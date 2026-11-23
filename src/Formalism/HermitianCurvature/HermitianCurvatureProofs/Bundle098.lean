module

public import Formalism.HermitianCurvature.Bundle005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.Bundle007
public import Formalism.HermitianCurvature.Bundle008
public import Mathlib.Topology.Separation.CompletelyRegular
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle014
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.StatementB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

@[expose] public section

section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem measurable_of_continuousOn_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {s : Set X} (hs : MeasurableSet s) {f : X → ℂ} (hf : ContinuousOn f s) (h0 : ∀ x ∉ s, f x = 0) : Measurable f := by
  classical
  have e : f = s.piecewise f (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ s <;> simp [Set.piecewise, hx, h0]
  rw [e]
  exact hf.measurable_piecewise continuousOn_const hs

section Meas

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem radSp_continuousOn (Φ : RadSp k r z z' π π') :
    ContinuousOn (fun x : (Fin r → ℂ) × Mx k r => (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) (DomR k r z z') := by
  obtain ⟨-, hs, -⟩ := Φ.2
  intro x₀ hx₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
  have hFc : ContinuousAt F x₀ := hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hΦ x₀ hxU hx₀.2.1)
  filter_upwards [inter_mem_nhdsWithin (DomR k r z z') (hU.mem_nhds hxU)] with x hx
  exact hΦ x hx.2 hx.1.2.1

theorem radSp_zero_off (Φ : RadSp k r z z' π π') {x : (Fin r → ℂ) × Mx k r} (hx : x ∉ DomR k r z z') :
    (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 :=
  Φ.2.1 x hx

def glueMap (c : Fin r → ℂ) (q : Cf r 0 × Mt k r) : (Fin r → ℂ) × Mx k r := (glue 0 c q.1, Matrix.of q.2)

theorem glueMap_continuous (c : Fin r → ℂ) : Continuous (glueMap (k := k) c) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun l => ?_
    have : (fun q : Cf r 0 × Mt k r => glue 0 c q.1 l) = fun q => q.1 ⟨l, Nat.zero_le _⟩ := by
      funext q
      simp [glue]
    rw [this]
    exact (continuous_apply _).comp continuous_fst
  · exact continuous_snd

theorem DomR_eq : DomR k r z z' = P.Qx5.OpR k r z z' ∩ (Prod.snd ⁻¹' Glev k r (Fin.last r)) := by
  ext x
  simp only [DomR, P.Qx5.OpR, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
  tauto

theorem measurableSet_glueMap_DomR (c : Fin r → ℂ) :
    MeasurableSet (glueMap (k := k) c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((P.Qx5.isOpen_OpR k r z z').preimage (glueMap_continuous c)).measurableSet.inter
    (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (glueMap_continuous c)).measurableSet

theorem pair_measurable (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r 0 × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2))) := by
  have hmaps : Set.MapsTo (glueMap (k := k) c) (glueMap (k := k) c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMap_continuous c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMap_continuous c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMap_DomR c)
    ((P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2) = 0 := radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue 0 c q.1) (Matrix.of q.2)) _ = 0
  rw [h0, P.B6.hilbert_schmidt_inner_basis_sum]
  simp

end Meas

theorem topDensMeasAll : TopDensMeasAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K w u v _ _ c
  refine Measurable.stronglyMeasurable ?_
  unfold topDens
  exact Finset.measurable_sum _ fun e _ => pair_measurable c _ _

end Formalism.FourierDecayAlt.P5
end
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBB

open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate

noncomputable section
open Classical

theorem integrable_decay3 : Integrable (fun c : ℂ => ((1 + ‖c‖) ^ 3)⁻¹) := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  simp only
  rw [Real.rpow_neg (by positivity)]
  norm_cast

section limB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem ae_coords_ne (S : C.HidaSetting E Wp Wq) : ∀ᵐ c : J.CV E, ∀ v, c (S.pl v) ≠ 0 := by
  have hnull : volume (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S ⁻¹' (⋃ v, {y : Fin S.f → ℂ | y v = 0})) = 0 := by
    rw [(Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S).measure_preimage (MeasurableSet.iUnion fun v =>
      measurableSet_eq_fun (measurable_pi_apply v) measurable_const).nullMeasurableSet]
    exact measure_iUnion_null fun v => Measure.pi_hyperplane _ v 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with c hc
  intro v hv
  exact hc (Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨v, by simp [Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply, hv]⟩))

theorem continuous_coord (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Continuous fun c : J.CV E => c (S.pl v) :=
  (EuclideanSpace.proj (𝕜 := ℂ) (S.pl v)).continuous

theorem continuous_psiInf (S : C.HidaSetting E Wp Wq) (l : E) : Continuous fun c : J.CV E => S.psiInf l c := by
  have : (fun c : J.CV E => S.psiInf l c) = fun c => ∏ v, KB.psiL S (S.σ v l) (c (S.pl v)) :=
    funext fun c => psiInf_eq_prod S l c
  rw [this]
  exact continuous_finsetProd _ fun v _ => (continuous_psiL S _).comp (continuous_coord S v)

theorem norm_psiInf (S : C.HidaSetting E Wp Wq) (l : E) (c : J.CV E) : ‖S.psiInf l c‖ = 1 := by
  rw [psiInf_eq_prod, norm_prod]
  simp [norm_psiL]

theorem aestronglyMeasurable_level_norm (S : C.HidaSetting E Wp Wq) (hInt : KB.IntAll S) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (hi1 : 1 ≤ i)
    (hi2 : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E)) (hY : ∀ h ∈ Y, TB.level h = i - 1)
    (κ : TB.Pt E → TB.Pt E → ℂ) : AEStronglyMeasurable (S.N1 ε i w.1 Y κ) volume := by
  have H : ∀ (v : Fin S.f) (h h' : Y), ∃ φ : ℂ → ℂ, Continuous φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = S.gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c)])
        (C.loc (S.σ v) h' ++ [(1, c)])) := by
    intro v h h'
    obtain ⟨φ, hc, he, -, -⟩ := hInt v ε hε i hi1 hi2 w (C.loc (S.σ v) h) (C.loc (S.σ v) h')
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h h.2)
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h' h'.2)
    exact ⟨φ, hc, he⟩
  choose φ hφc hφe using H
  set Φ : J.CV E → ℂ := fun c =>
    (∑ h : Y, ∑ h' : Y, κ h h' * ∏ v, φ v h h' (c (S.pl v))) / (C.Word.size S.P w.1 : ℂ) with hΦ
  have hΦc : Continuous Φ := by
    apply Continuous.div_const
    exact continuous_finsetSum _ fun h _ => continuous_finsetSum _ fun h' _ =>
      continuous_const.mul (continuous_finsetProd _ fun v _ => (hφc v h h').comp (continuous_coord S v))
  refine hΦc.aestronglyMeasurable.congr ?_
  filter_upwards [ae_coords_ne S] with c hc
  simp only [hΦ, C.HidaSetting.N1]
  congr 1
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun h' _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hφe v h h' _ (hc v)]

end limB

section limB2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem gram_withRR (S : C.HidaSetting E Wp Wq) (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (ε : ℝ) (k : ℕ) (w : C.Word S.f) (h h' : TB.Pt E) :
    (KB.withRR S RR).gram ε k w h h' = if k ≤ S.G.r + 1 then
      ∏ v, (KB.withRR S RR).gramLoc v ε k (w v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') else 0 := rfl

theorem level_norm_of_regularization_eq (S : C.HidaSetting E Wp Wq) (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (ε : ℝ) (i : ℕ) (w : C.Word S.f) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (c : J.CV E) :
    (KB.withRR S RR).N1 ε i w Y κ c = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (KB.withRR S RR).gramLoc v ε i (w v)
      (C.loc (S.σ v) h ++ [(1, c (S.pl v))]) (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
        (C.Word.size S.P w : ℂ) := rfl

variable (S : C.HidaSetting E Wp Wq) (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
  (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
    Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))

include hconv

theorem tendsto_gramLoc' (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (a : List C.Letter) (ha : D.AdmAt S v a)
    (p q : C.LPt) :
    Tendsto (fun n => ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G p) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G q) : ℝ) : ℂ) *
      RR n v ε i a p q) atTop (𝓝 (S.gramLoc v ε i a p q)) :=
  (hconv v ε hε i a ha p q).const_mul _

theorem tendsto_gram (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : k ≤ S.G.r + 1) (w' : S.W) (h h' : TB.Pt E) :
    Tendsto (fun n => (KB.withRR S (RR n)).gram ε k w'.1 h h') atTop (𝓝 (S.gram ε k w'.1 h h')) := by
  have e1 : (fun n => (KB.withRR S (RR n)).gram ε k w'.1 h h') = fun n =>
      ∏ v : Fin S.f, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h)) *
        √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h')) : ℝ) : ℂ) *
          RR n v ε k (w'.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') :=
    funext fun n => by rw [gram_withRR, if_pos hk]; rfl
  have e2 : S.gram ε k w'.1 h h' = ∏ v, S.gramLoc v ε k (w'.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') := by
    simp only [C.HidaSetting.gram, if_pos hk]
  rw [e1, e2]
  exact tendsto_finsetProd _ fun v _ => tendsto_gramLoc' S RR hconv v ε hε k (w'.1 v) ⟨w', rfl⟩ _ _

theorem tendsto_base_norm_of_regularization (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : k ≤ S.G.r + 1) (w' : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.N0 ε k w' Y κ) atTop (𝓝 (S.base.N0 ε k w' Y κ)) := by
  have e : ∀ n, (KB.withRR S (RR n)).base.N0 ε k w' Y κ =
      (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * (KB.withRR S (RR n)).gram ε k w'.1 h h').re / C.Word.size S.P w'.1 :=
    fun n => rfl
  simp only [e]
  show Tendsto _ atTop (𝓝 ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w'.1 h h').re / C.Word.size S.P w'.1))
  exact ((Complex.continuous_re.tendsto _).comp (tendsto_finsetSum _ fun h _ => tendsto_finsetSum _
    fun h' _ => tendsto_const_nhds.mul (tendsto_gram S RR hconv ε hε k hk w' h h'))).div_const _

theorem tendsto_level_norm_of_regularization (ε : ℝ) (hε : 0 < ε) (i : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (c : J.CV E) :
    Tendsto (fun n => (KB.withRR S (RR n)).N1 ε i w.1 Y κ c) atTop (𝓝 (S.N1 ε i w.1 Y κ c)) := by
  have e1 : (fun n => (KB.withRR S (RR n)).N1 ε i w.1 Y κ c) = fun n =>
      (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v : Fin S.f,
        ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h ++ [(1, c (S.pl v))])) *
          √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) : ℝ) : ℂ) *
          RR n v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c (S.pl v))]) (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
          (C.Word.size S.P w.1 : ℂ) := funext fun n => rfl
  have e2 : S.N1 ε i w.1 Y κ c = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
        (C.loc (S.σ v) h ++ [(1, c (S.pl v))]) (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
          (C.Word.size S.P w.1 : ℂ) := rfl
  rw [e1, e2]
  exact (tendsto_finsetSum _ fun h _ => tendsto_finsetSum _ fun h' _ => tendsto_const_nhds.mul
    (tendsto_finsetProd _ fun v _ => tendsto_gramLoc' S RR hconv v ε hε i (w.1 v) ⟨w, rfl⟩ _ _)).div_const _

theorem tendsto_Nhat (hInt : ∀ n, KB.IntAll (KB.withRR S (RR n)))
    (hbd : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 → ∃ C : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
        ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹)
    (ε : ℝ) (hε : 0 < ε) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E))
    (hY : ∀ h ∈ Y, TB.level h = i - 1) (κ : TB.Pt E → TB.Pt E → ℂ) (l : E) :
    Tendsto (fun n => (KB.withRR S (RR n)).Nhat ε i w.1 Y κ l) atTop (𝓝 (S.Nhat ε i w.1 Y κ l)) := by
  have e : ∀ n, (KB.withRR S (RR n)).Nhat ε i w.1 Y κ l =
      ((ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) : ℝ) : ℂ)⁻¹ *
        ∫ c : J.CV E, (KB.withRR S (RR n)).N1 ε i w.1 Y κ c * S.psiInf l c := fun n => rfl
  simp only [e]
  unfold C.HidaSetting.Nhat
  refine Tendsto.const_mul _ ?_
  have hB : ∀ v (h h' : Y), ∃ Cc : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
      ‖(KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c)])
        (C.loc (S.σ v) h' ++ [(1, c)])‖ ≤ Cc * ((1 + ‖c‖) ^ 3)⁻¹ :=
    fun v h h' => hbd v ε hε i hi1 hi2 (w.1 v) ⟨w, rfl⟩ _ _
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h h.2)
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h' h'.2)
  choose Cb hCb using hB
  set sz : ℂ := (C.Word.size S.P w.1 : ℂ) with hsz
  let g : (Fin S.f → ℂ) → ℝ := fun y =>
    (∑ h : Y, ∑ h' : Y, ‖κ h h'‖ * ∏ v, (Cb v h h' * ((1 + ‖y v‖) ^ 3)⁻¹)) / ‖sz‖
  have hgi : Integrable g := by
    refine Integrable.div_const (integrable_finsetSum _ fun h _ => integrable_finsetSum _ fun h' _ =>
      Integrable.const_mul (Integrable.fintype_prod (f := fun v c => Cb v h h' * ((1 + ‖c‖) ^ 3)⁻¹)
        fun v => integrable_decay3.const_mul _) _) _
  have hbi : Integrable (fun c : J.CV E => g (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S c)) :=
    (Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S).integrable_comp_of_integrable hgi
  refine tendsto_integral_of_dominated_convergence (fun c => g (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S c)) (fun n => ?_) hbi
    (fun n => ?_) ?_
  · exact (aestronglyMeasurable_level_norm (KB.withRR S (RR n)) (hInt n) ε hε i hi1 hi2 w Y hY κ).mul
      (continuous_psiInf S l).aestronglyMeasurable
  · filter_upwards [ae_coords_ne S] with c hc
    rw [norm_mul, norm_psiInf, mul_one, level_norm_of_regularization_eq, norm_div]
    simp only [g, Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    rw [← Finset.sum_coe_sort Y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    rw [← Finset.sum_coe_sort Y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h' _ => ?_)
    rw [norm_mul, norm_prod]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _)
      fun v _ => hCb v h h' _ _ (hc v)) (norm_nonneg _)
  · exact Eventually.of_forall fun c => (tendsto_level_norm_of_regularization S RR hconv ε hε i w Y κ c).mul_const _

end limB2

end

end Formalism.FourierDecayAlt.P.PBB
end

section

open Finset NumberField MeasureTheory Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

noncomputable section

theorem jct_parts_loc_cpt (hPA : P5.ThmPActualCpt) (hRMF : JC.RadialModuleForm) (hPD : JC.PosDensityCpt)
    (hFS : JC.FormLevSesqMM) (hMA : JC.ThmPModuleOfActualCpt) (hMu : D.MuRHaar)
    (C₄ C₆ : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ)
    (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
    (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : Fin S.f → ℝ)
    (Lw : ℕ → Fin S.f → ℝ) (Ll Ll' : ℕ → ℕ → Fin S.f → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hU : S6.Unram E) (hB : D.IsBuilt S T f χ ν' m₀ top A₀)
    (hIBl : ∃ dl : ℕ → Fin S.f → ℝ,
      (∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
        ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1)) ∧
      ∀ v, JC.ThmPIntPlace S v fun i => dl i v)
    (hIn : JCT.BuiltInputs C₄ C₆ S T f χ ν' m₀ top L j lam c Cm σ Lw Ll Ll' Vt) :
    C.ThmPPos S ∧ C.GridsOK S ∧ C.ThmPInt S ∧ C.PlaneWaveBoundAllPlaces S ∧ C.OffDiagonalLiftBound S ∧ C.CorollaryT S C₄ ∧
      C.PropGram S Vt := by
  obtain ⟨hl1, hl2, hLA, hSl, htop, hGr, hW, hTW, hLB, hLT, hTL, hSF, -, -, -, hVt⟩ := hIn
  have hlen : ∀ v, ∀ w, D.AdmAt S v w → w.length ≤ S.Ntop := by
    rintro v w ⟨w', rfl⟩
    exact le_trans (Finset.le_sup (f := fun u => (w'.1 u).length) (Finset.mem_univ v)) w'.2.2
  have hPos : C.ThmPPos S := by
    refine positivity_of_module E Wp Wq S T f χ ν' m₀ top A₀ hB (fun v => ?_) htop
    obtain ⟨KK, hKK, hmem⟩ := hMA hPA hRMF hPD hFS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v) (S.l + 1) S.Ntop
      (D.AdmAt S v) (P5.Auser (D.parOf S v) S.Ntop + 1) (P5.mmUser (D.parOf S v) S.Ntop) (by omega)
      (by change S.l + 1 ≤ S.G.k; omega) (hlen v) le_rfl
      le_rfl (hLA v)
    refine ⟨KK, hKK, fun ε hε i hi w hw p hp a => ?_⟩
    obtain ⟨ε', hε', hCk, hCC, hs⟩ := hSl v ε hε i hi w hw p hp a
    exact hmem ⟨i, Nat.lt_succ_of_le hi⟩ _ ε' hε' hCC hCk hs
  have hInt : C.ThmPInt S := by
    obtain ⟨dl, hdl, hpl⟩ := hIBl
    refine theorem_P_integral_of_places E Wp Wq S dl hPos hdl (fun i _ _ => ?_) hpl
    have hg : 0 < S.g := Nat.mul_pos hg1 hg2
    have hrd := jct_rd_pos E
    rw [unipotent_dual_lattice_covolume E hU S.g _ 1 hg]
    positivity
  refine ⟨hPos, hGr, hInt, ?_, ?_, ?_, ?_⟩
  · exact plane_exponential_bound_of_places gram_positive_semidefinite words_pos_of_parts E Wp Wq S Lw hPos hGr hW hTW
  · exact off_diagonal_lift_bound_of_places third_polynomial_prime_combine gram_positive_semidefinite words_pos_of_parts
      E Wp Wq S Ll Ll' hPos hGr hLB hLT hTL
  · exact corollary_T_of_sum_form blockEstimateOfCosetSum gram_positive_semidefinite words_pos_of_parts
      E Wp Wq S C₄ hPos hGr hSF
  · exact gram_proposition_of_places E Wp Wq S
      (fun v => PiLp 2 (fun _ : Fin (Module.finrank ℂ (Wq (S.pl v))) => Wp (S.pl v))) (JC.vecPlace S T f ν' m₀)
      H Vt hVt (gram_at_built_place ptPerm_spec ptG_spec relevant_points_holds hMu
        orbital_integral_cutoff_scalar E Wp Wq S T f χ ν' m₀ top A₀ hg1 hg2 hB)

end

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.RealInputsCompactSupport

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJoint

noncomputable section

theorem real_inputs_closed_compact_support_of : KB.ArchimedeanUniformConstantsCompactSupport := by
  intro hPA hRMF hPD hFS hMA hMu hLEM hLA hSL hMP hTP hBB Cb
  obtain ⟨C₆, hC₆, hLE⟩ := lemma_E_of_model lemma_E_of_residue level_zero_holds good_of_admissible hLEM
  obtain ⟨c1, hLA⟩ := hLA
  obtain ⟨c2, hSL⟩ := hSL
  obtain ⟨c7, hMP⟩ := hMP
  obtain ⟨c3, C₄, hC₄, hBB⟩ := hBB hPA Cb
  refine ⟨C₆, max c1 (max c2 (max c3 c7)), C₄, hC₆, hC₄, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ c H _ _ Vt hBPT hSB hc hcut hVt
  obtain ⟨-, -, -, -, hOk, hWd, hWd', -⟩ := hBPT.1
  have hBP := toBuiltPlace hBPT
  have m1 := jct_isBuiltPlace_mono (by simp) hBP (c := c1)
  have m2 := jct_isBuiltPlace_mono (by simp) hBP (c := c2)
  have m7 := jct_isBuiltPlace_mono (by simp) hBP (c := c7)
  have hB2 : KB.IsLeadingFormSetting Cb c3 S p f χ A₀ := built_setting_to_model_place (by simp) hBPT.1
  obtain ⟨-, hIA, ⟨Lw, hW, hTW⟩, ⟨Ll, Ll', hLB, hLT, hTL⟩, hSF⟩ := hBB E Wp Wq S p f χ A₀ hB2
  have htop : ∀ v, D.TopPSD (KB.plT S p v) (f v) χ (D.AdmAt S v) (KB.plTop S p v) := fun v =>
    hTP (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (S.l + 1) (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP (f v) χ
      (D.AdmAt S v)
  obtain ⟨hg1, hg2, hU, hB, hl1, hl2, hGr, -, -, hsm, -, -, -⟩ := hBP
  choose L j lam Cm σ hmod using
    hMP E Wp Wq S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p) (KB.plTop S p) A₀ m7 hOk hWd hWd' c hc
  have hIn : JCT.BuiltInputs C₄ C₆ S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p) (KB.plTop S p) L j lam c Cm σ
      Lw Ll Ll' Vt :=
    ⟨hl1, hl2, hLA E Wp Wq S _ f χ _ _ _ A₀ m1, hSL E Wp Wq S _ f χ _ _ _ A₀ m2 hSB, htop, hGr, hW, hTW, hLB, hLT,
      hTL, hSF, hsm, hcut, hmod, hVt⟩
  refine ⟨L, j, lam, Cm, σ, hmod, ?_⟩
  intro Kr hK0 Th e
  have hg : 0 < S.g := Nat.mul_pos hg1 hg2
  have hIBl : ∃ dl : ℕ → Fin S.f → ℝ,
      (∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
        ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1)) ∧
      ∀ v, JC.ThmPIntPlace S v fun i => dl i v :=
    ⟨fun i _ => KB.dlB S i 1, fun i _ _ => prod_dlB S hU hg i, hIA⟩
  obtain ⟨hPos, hGr', hInt, hP1, hP23, hT, hPG⟩ :=
    jct_parts_loc_cpt hPA hRMF hPD hFS hMA hMu C₄ C₆ E Wp Wq S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p)
      (KB.plTop S p) A₀ L j lam c Cm σ Lw Ll Ll' H Vt hg1 hg2 hU hB hIBl hIn
  have hE : C.LemmaE S (JCT.jvModel S j Cm) :=
    hLE E Wp Wq S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p) (KB.plTop S p) A₀ L j lam c Cm σ hB
      (fun v ε hε => cutoff_smooth _ _ _ _ (KB.plT S p v).base χ (f v) ε hB.1 (hsm v) hε) hcut hmod
  exact real_inputs_concrete_holds E Wp Wq S (JCT.jvModel S j Cm) H Vt C₄ hg1 hg2 hPos hGr' hInt hP1 hP23 hT hE
    hPG Kr hK0 Th e

end

end Formalism.FourierDecayAlt.P.RealInputsCompactSupport

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P

theorem exists_auxiliary_xi : Formalism.FourierDecayAlt.B.XiExists := ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end Formalism.FourierDecayAlt.P
end
