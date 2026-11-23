module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CuspReadPTrue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle402
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PTestVeryCuspMulConst
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.GrowthOut
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfFiniteInputs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IntegrableCut
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PGrowth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Count1
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem rSpec_of (h1 : PeakRun) (h2 : GenSt) (h3 : PtOk) (h4 : HkMul) (h5 : RepAlg) (h6 : PositionTest) : RSpec := by
  intro P hR E _ _ _ a b l₁ l₂ D A S Z L hS hZ X hX hXc Q _ hK hg
  obtain ⟨W, hW, hR⟩ := hR E a b l₁ l₂
  obtain ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, a3⟩ := hR D A S Z L hS hZ X hX hXc
  obtain ⟨g, hg1, hg2⟩ := hg W hW
  refine ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, fun T e₁ e₂ ρ hT hd hρ hv => ?_⟩
  obtain ⟨hG, hC⟩ := h2 E a b l₁ l₂ D A S Z L hS hZ T e₁ e₂
  obtain ⟨p1, p2, -, p4, -⟩ := h3 E a b l₁ l₂ D A
  obtain ⟨-, m2, m3, -, -, m6, -⟩ := h4 E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨-, r2, -, r4⟩ := h5 E A.blk (chi l₁) (chi l₂)
  obtain ⟨V, R, hR0, hV, hn⟩ := h1 E A.blk Q (chi l₁) (chi l₂) (Gam a b S Z) (A.gen S L T e₁ e₂) Gam.arch (.inl ())
    (.inr (.inr (.inr ()))) g ρ hG hK hg1 p1 p2 trivial (p4 _)
    (fun γ hγ => by rcases γ with _ | _ | _ <;> first | rfl | exact hγ.elim) m2 m3 hρ
    (fun s hs hr => by
      obtain ⟨j, hj⟩ := a3 T e₁ e₂ g s hT hd hg2 hs hr
      rw [hj]
      exact hv j)
  have hx := hG.ok (.inr (.inr (.inr ())))
  have h := r4 _ _ _ _ _ _ _ _ (r2 _ hx) hV
  have e1 : mulF A.blk.ν (A.gen S L T e₁ e₂ (.inr (.inr (.inr ())))).ψ (A.gen S L T e₁ e₂ (.inl ())).ψ = A.hk S L T e₁ e₂ :=
    (m6 T L.ln e₁ e₂ (h6 E a b S Z L hZ).1).2.1
  have e2 : (A.gen S L T e₁ e₂ (.inr (.inr (.inr ())))).val (chi l₁) (chi l₂) = 1 := p4 _
  rw [e1, e2, one_mul] at h
  exact ⟨_, _, add_nonneg (add_nonneg (le_max_of_le_left hx.T) hR0) A.c_nonneg, h, hn⟩

theorem haarEx (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : ∃ μ : Measure (GA E n), μ.IsHaarMeasure := by
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem rEndo_of (h1 : ArEx) (h2 : LvEx) (h3 : PowRep) (h4 : CmbTest) (h5 : CmbEll) (h6 : RepAlg) (h7 : PowNorm) : REndo := by
  intro P hSp E _ _ _ hE a b _ S hS l₁ l₂ Z hZ φ hφ hreg
  haveI : Nontrivial (InfinitePlace E) := GlobalTheory.T.nontrivial_infinite_place_of_unramified E hE
  haveI : BorelSpace (GA E a) := ⟨rfl⟩
  haveI : BorelSpace (GA E b) := ⟨rfl⟩
  obtain ⟨μ₁, hμ₁⟩ := haarEx E a
  obtain ⟨μ₂, hμ₂⟩ := haarEx E b
  obtain ⟨D, hD⟩ := PositivityTheory.Rg.BcB.E1.growthJ_holds E a b μ₁ μ₂
  obtain ⟨A⟩ := h1 E a b l₁ l₂ D
  obtain ⟨L, hL⟩ := h2 E a b Z φ hφ
  obtain ⟨u₁, hu₁⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E a
  obtain ⟨u₂, hu₂⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E b
  obtain ⟨κ, hκ, hell⟩ := h5 E hE a b l₁ l₂ D A μ₁ μ₂ hμ₁ hμ₂
  obtain ⟨c, hc, htest⟩ := h4 E a b l₁ l₂ D A S Z L hS hZ u₁ u₂ hu₁ hu₂
  haveI : CompleteSpace (⊤ : Submodule ℂ A.blk.Hb) := (isClosed_univ.completeSpace_coe : CompleteSpace (Set.univ : Set A.blk.Hb))
  obtain ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, a3⟩ := hSp E a b l₁ l₂ D A S Z L hS hZ ∅ Set.subsingleton_empty
    (fun _ h => h.elim) ⊤ (fun _ _ _ _ _ _ => Submodule.mem_top)
    (fun W _ => ⟨fun _ => 0, ⟨fun _ => Submodule.zero_mem _, fun j i M => by
      have : ((0 : A.blk.Hb) i : H E a b → ℂ) =ᵐ[D.ν] 0 := Lp.coeFn_zero _ _ _
      rw [lintegral_congr_ae (g := fun _ => 0) (this.mono fun x hx => by
        show _ * ‖((0 : A.blk.Hb) i : H E a b → ℂ) x‖ₑ ^ 2 = 0
        rw [hx]
        simp)]
      simp⟩, fun _ _ _ _ _ _ _ _ _ h => h.elim⟩)
  refine ⟨J, hJ, D₁, D₂, B₁, B₂, fun j => (a1 j).2, a2, fun T hT hd e₁ e₂ ρ hT' hρ hv => ?_⟩
  obtain ⟨U, R, hR, hU, hn⟩ := a3 T e₁ e₂ ρ ⟨hT, hT'⟩ hd hρ hv
  obtain ⟨o₁, o₂, r₀, r₁, hr₀, hr₁, hk⟩ := h3 E a b l₁ l₂ D A S Z L hS hZ u₁ u₂ φ T e₁ e₂ U R hL hR hU
  have b₁ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₁ o₁
  have b₂ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₂ o₂
  obtain ⟨C, N, hb⟩ := hD A.blk.I _ _ _ _ A.tw (c * (1 + r₀)) (c * r₁) b₁.1 b₂.1 b₁.2.1 b₂.2.1 (by positivity) (by positivity)
  refine ⟨‖κ‖⁻¹ * |C|, N, fun k => ?_⟩
  obtain ⟨Cm, c1, c2, c3⟩ := hk k
  have hrk : 0 ≤ r₀ + k * r₁ := by positivity
  obtain ⟨q1, q2⟩ := (h6 E A.blk (chi l₁) (chi l₂)).1 Cm _ _ c1
  have ht := (htest φ T _ _ Cm _ hL hreg hrk c1).2
  have he := hell S Z L hS hZ u₁ u₂ hu₁ hu₂ φ T e₁ e₂ k Cm _ hL hreg ⟨hT, hT'⟩ hrk c1
  rw [c3] at q2
  have hb' := hb k (U ^ k) Cm.Φ q1 q2 (by rw [show c * (1 + r₀) + k * (c * r₁) = c * (1 + (r₀ + k * r₁)) by ring]; exact ht)
  have hp : ‖U ^ k‖ ≤ ρ ^ k := by
    have h := (h7 A.blk.Hb ⊤ U ρ (fun _ _ => Submodule.mem_top) hn.le k).2
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    exact (((U ^ k) ∘L (⊤ : Submodule ℂ A.blk.Hb).subtypeL).le_opNorm ⟨x, Submodule.mem_top⟩).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  rw [he, c2, mul_one, norm_mul] at hb'
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  have h9 : C * (1 + k) ^ N * ‖U ^ k‖ ≤ |C| * (1 + k) ^ N * ρ ^ k :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) hp (norm_nonneg _) (by positivity)
  rw [mul_assoc, mul_assoc, ← mul_assoc |C|, le_inv_mul_iff₀ hκ']
  exact hb'.trans h9

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem trM_pt {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a}
    {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b} (A : Ar l₁ l₂ D) (S : Set (Pl E)) (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E)
    (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (t : PT A.blk) (ht : t.ψ = rt u₁ u₂ (A.ff S φ₁ φ₂)) :
    trM t.Φ A.tw = A.blk.vol⁻¹ • adel S u₁ u₂ (t.arch (Tl l₁) (Tl l₂)) φ₁ φ₂ := by
  funext g
  have hT3 : F.trM t.Φ (opM (Tl l₁) (Tl l₂) (1 : Matrix Unit Unit ℂ)) g = _ :=
    tensTr E a b (Ml l₁) (Ml l₂) Unit t.ka t.kb (Tl l₁) (Tl l₂) t.ψ 1 g
  have hA : ∏ v, t.arch (Tl l₁) (Tl l₂) v (GeneralLinearGroup.map (cV v) g.1, GeneralLinearGroup.map (cV v) g.2) =
      (∏ v, phiOf (Ml l₁ v) (Tl l₁ v) (t.ka v) (gInf v g.1)) * ∏ v, phiOf (Ml l₂ v) (Tl l₂ v) (t.kb v) (gInf v g.2) := by
    simp only [PT.arch]
    exact Finset.prod_mul_distrib
  have hF : finFn S φ₁ φ₂ (hFin g * (ratF E a u₁, ratF E b u₂)⁻¹) =
      ∏ᶠ v ∈ S, φ₁ v (cpt v u₁ g.1, cpt v u₂ g.2) * if IsSplitAt v then φ₂ v (cpt' v u₁ g.1, cpt' v u₂ g.2) else 1 := by
    simp only [finFn, Adel.cpt_eq, Adel.cpt'_eq]
    rfl
  refine hT3.trans ?_
  rw [ht, Pi.smul_apply, smul_eq_mul, adel, hA, ← hF]
  simp only [F.rt, Ar.ff, Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq]
  ring

theorem cmbEll_of (hT : CmbTest) (hS : SeenFam) (hSl : PositionTest) (hL : LefL) (hF : FfAlg) : CmbEll := by
  intro E _ _ _ hU a b l₁ l₂ D A μ₁ μ₂ h₁ h₂
  haveI := GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace E hU
  haveI := A.ha
  haveI := A.hb
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (GA E a) := ⟨rfl⟩
  haveI : BorelSpace (GA E b) := ⟨rfl⟩
  obtain ⟨c, hc, h4⟩ := global_character_holds E hU a b μ₁ μ₂ A.μa A.μb
  by_cases hv : A.blk.vol = 0
  · exact ⟨1, one_ne_zero, fun S _ _ hS' => absurd hv (hF E a b l₁ l₂ D A S hS').1⟩
  refine ⟨A.blk.vol⁻¹ * c * 2 ^ ((a + b) * Fintype.card (InfinitePlace E)),
    mul_ne_zero (mul_ne_zero (inv_ne_zero hv) hc) (pow_ne_zero _ two_ne_zero), ?_⟩
  intro S Z L hSec hZ u₁ u₂ hu₁ hu₂ φ T e₁ e₂ k C R hφ hreg hIn hR hC
  obtain ⟨c₀, hc₀, ht⟩ := hT E a b l₁ l₂ D A S Z L hSec hZ u₁ u₂ hu₁ hu₂
  have ht' := (ht φ T _ _ C R hφ hreg hR hC).1
  have hr : 0 ≤ c₀ * (1 + R) := mul_nonneg hc₀ (by linarith)
  obtain ⟨-, hseen, htest, -⟩ := (hS E a b S Z L hZ φ T e₁ e₂ hφ hIn).2 k
  obtain ⟨hln, -, hsl⟩ := hSl E a b S Z L hZ
  have h3 := G3.g3 E hU a b S hSec l₁ l₂ _ htest (by
    obtain ⟨w, hw, hw'⟩ := hreg
    exact ⟨w, (hZ w hw).1, by rw [fam, if_pos hw]; exact hw'⟩)
  have one : ∀ j ∈ C.s, ellSum2 μ₁ μ₂ (trM (C.t j).Φ A.tw) =
      A.blk.vol⁻¹ * c * 2 ^ ((a + b) * Fintype.card (InfinitePlace E)) * (C.t j).val (chi l₁) (chi l₂) *
        geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) := fun j hj => by
    obtain ⟨ok, hψ, -, -⟩ := hC j hj
    have e := trM_pt A S u₁ u₂ _ _ (C.t j) hψ
    have e' : adel S u₁ u₂ ((C.t j).arch (Tl l₁) (Tl l₂)) (intersection_update_fsHerm_neg_one Z T φ fun w => (e₁ w).pow k)
        (intersection_update_fsHerm_neg_one Z T L.ln fun w => (e₂ w).pow k) = ∑ _i ∈ ({()} : Finset Unit), A.blk.vol • trM (C.t j).Φ A.tw := by
      rw [Finset.sum_singleton, e, smul_smul, mul_inv_cancel₀ hv, one_smul]
    have h5 := h4 S hSec u₁ u₂ hu₁ hu₂ l₁ l₂ (fun v => (C.t j).va v (chi l₁ v) * (C.t j).vb v (chi l₂ v))
      ((C.t j).arch (Tl l₁) (Tl l₂)) _ _
      (fun v => (hL E a b l₁ l₂ D A).2 v _ _ _ _ _ (ok.ka v) (ok.kb v)) ((hsl φ hφ).2 T fun w => (e₁ w).pow k)
      ((hsl _ hln).2 T fun w => (e₂ w).pow k)
    rw [e', ellLin_holds E a b μ₁ μ₂ Unit _ _ _ _ hr (fun _ _ => ht' j hj), Finset.sum_singleton, hseen, h3,
      Finset.prod_mul_distrib] at h5
    have hval : (C.t j).val (chi l₁) (chi l₂) = (∏ v, (C.t j).va v (chi l₁ v)) * ∏ v, (C.t j).vb v (chi l₂ v) := rfl
    rw [hval, ← inv_mul_cancel_left₀ hv (ellSum2 μ₁ μ₂ (trM (C.t j).Φ A.tw)), h5]
    ring
  rw [Cmb.Φ, Growth.trM_sum, ellLin_holds E a b μ₁ μ₂ _ _ _ _ _ hr ht', Cmb.val, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [one j hj]
  ring

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
