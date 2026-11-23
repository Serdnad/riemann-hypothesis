module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle620
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle976
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormLevelInvariantMemSpanBaseForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle947
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle926
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle881
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle037
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverReadingEqPowMulMovedFrameReading
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle089
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle975
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle950
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle891
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle591
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.coverForm_levelInvariant_mem_span_baseForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ φ ∈ C.ratForms a n, (∀ k ∈ T.Kf j σ, ∀ h, φ (h * k) = φ h) → φ ∈ Submodule.span ℂ (baseForms T j σ a n) := by
  first | exact @GlobalTheory.CoverDescSpan.mem_span_baseForms | exact GlobalTheory.CoverDescSpan.mem_span_baseForms | (intros; apply GlobalTheory.CoverDescSpan.mem_span_baseForms <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries



theorem cc_unique_of_pinned : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ c : C.U₂.Comp → ℂ, (∀ a, Dom a (κ i).n → C.IsPinned a (κ i).n) → (∀ a, Dom a (κ i).n → ({ C with cc₂ := c } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n) → ∀ h, C.cc₂ (C.dict₂ h).1 = c (C.dict₂ h).1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hT _ _ _ _ _ _ i _ _ C hC c hP hP' h
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hr, -⟩ := hT.modelW _ hj _ hσ

  obtain ⟨a, ha, hk⟩ := GlobalTheory.T.exists_nonzero_dominant_section_each_component D T hT _ hj _ hσ (κ i).n (κ i).n_even
  set k₀ := (T.dict ((i : ℕ) + 1) T.σ₀ h).1 with hk₀
  obtain ⟨f, hf, x, hx, hne⟩ := hk k₀
  have hU := hT.unf _ hj _ hσ
  have hS := hU.2.2.2.2.1 a _ ha f hf k₀

  obtain ⟨x₁, b, hb, ho, hx₁⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E _ _ _ _
    ((T.U ((i : ℕ) + 1) T.σ₀).X k₀).Gm_herm).1 x hx
  have hne₁ : rdU (T.U ((i : ℕ) + 1) T.σ₀) f k₀ x₁ ≠ 0 := by
    rw [hx₁, hS.2.1 x hx b hb]
    exact mul_ne_zero (GlobalTheory.CoverIndep.bchar_ne_zero' _ hb) hne
  have ho' : GlobalTheory.CoverDescSpan.IsOrthFr ((T.U ((i : ℕ) + 1) T.σ₀).X k₀) x₁ := ho

  obtain ⟨u, hu, hxu⟩ := (GlobalTheory.CoverDescSpan.base_orth hT hj hσ hr hθ h).2 x₁ ho'
  obtain ⟨γ, hγ, hdu⟩ := GlobalTheory.CoverDescSpan.base_real hT hj hσ hr hθ h u hu
  rw [← hxu] at hdu
  have hne₂ : rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1
      (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).2 ≠ 0 := by
    rw [hdu]
    show rdU (T.U ((i : ℕ) + 1) T.σ₀) f k₀ (lact γ x₁) ≠ 0
    rw [hS.2.2 γ hγ x₁ ho'.mem_dom]
    refine mul_ne_zero ?_ hne₁
    obtain ⟨N, hN, hN1⟩ := ((T.U ((i : ℕ) + 1) T.σ₀).X k₀).χ_fin (laU (T.U ((i : ℕ) + 1) T.σ₀) a (κ i).n k₀)
    intro h0
    have := hN1 γ hγ
    rw [h0, zero_pow hN.ne'] at this
    exact zero_ne_one this
  have hl : ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have hphi : T.phiJ ((i : ℕ) + 1) T.σ₀ a f (h * u) ≠ 0 := by
    have eb : T.phiJ ((i : ℕ) + 1) T.σ₀ a f (h * u) = ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
        ((T.cE ((i : ℕ) + 1) T.σ₀ (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
          rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1
            (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).2) := rfl
    rw [eb]
    refine mul_ne_zero hl (mul_ne_zero (mul_ne_zero ?_ ?_) hne₂)
    · exact norm_ne_zero_iff.1 (by rw [hT.cUnit _ hj _ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(hT.muVal _ hj _ hσ).norm]; exact one_ne_zero)

  have hcomp : (C.dict₂ (h * u)).1 = (C.dict₂ h).1 := by
    have := (GlobalTheory.CoverDescSpan.cover_real hT hj hσ hr hθ C hC h 1 u (one_mem _) hu).1
    rwa [one_mul] at this

  obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.CovPull.exists_pull D T hT _ hj _ hσ C hC.1 a (κ i).n f hf
  have e1 := congrFun ((hP a ha).2 f hf f₂ hf₂ hpull) (h * u)
  have e2 := congrFun ((hP' a ha).2 f hf f₂ hf₂ hpull) (h * u)
  have ec : C.rd a f₂ (h * u) = ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      ((C.cc₂ (C.dict₂ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
        rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := rfl
  have ec' : ({ C with cc₂ := c } : Cover T ((i : ℕ) + 1) T.σ₀).rd a f₂ (h * u) =
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      ((c (C.dict₂ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
        rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := rfl
  rw [ec] at e1
  rw [ec'] at e2
  have hne₃ := e1 ▸ hphi
  have hm : T.mu ((i : ℕ) + 1) T.σ₀ (h * u) ≠ 0 := by
    intro h0; rw [h0] at hne₃; simp at hne₃
  have hX : rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2 ≠ 0 := by
    intro h0; rw [h0] at hne₃; simp at hne₃
  have key := e1.trans e2.symm
  rw [← hcomp]
  have k2 : C.cc₂ (C.dict₂ (h * u)).1 * (((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      T.mu ((i : ℕ) + 1) T.σ₀ (h * u) * rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) =
      c (C.dict₂ (h * u)).1 * (((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      T.mu ((i : ℕ) + 1) T.σ₀ (h * u) * rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := by
    linear_combination key
  exact mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hl hm) hX) k2

end GlobalTheory.LevelSeries
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrameOver

open GlobalTheory.CoverFrameRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem un_over : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r) (hx : x ∈ (C.U₂.X (C.dict₂ h).1).dom) (hx' : x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom), (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).x : Sp ℂ ⟶ C.d.Xo₂.X) C.d.r = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).x : Sp ℂ ⟶ (T.Q.Xo j).X) ∧ ∀ (τ : D.host.E →+* ℂ) (i : Fin ((T.Q.Dw j).mult τ)), CategoryTheory.CategoryStruct.comp ((C.U₂.un (C.dict₂ h).1 ⟨x, hx⟩).u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) C.d.m.φ = (((T.U j σ).un (T.dict j σ h).1 ⟨x', hx'⟩).u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left) := by
  intro D T hT j hj σ hσ C hC h γ hlat hiso hfr x x' hx hx' hxx
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, ⟨hEF₁, hper₁⟩, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨hlev, hA₂, hσ₂, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, ⟨hEF₂, hper₂⟩, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  obtain ⟨-, hpq, -, hq⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hT.pins j hj
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, -, hm₂, hf₂⟩ := hd₂ h
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := fun τ =>
    ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  obtain ⟨δ, hδf, hδm⟩ := move_mark (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ hL₁
  have hγδ : (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = δ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h).1).cmType _).2 h0)⟩
    have t₁ := (hΨ τ).2 t₂
    have a₂ := hf₂ ⟨τ, t₂⟩
    have a₁ := hf₁ ⟨τ, t₁⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have a₃ := a₁.trans ((hδf τ _ (hth₁ _ ⟨τ, t₁⟩) _).trans (congrArg (_ * ·) a₂.symm))
    have a₄ := (hfr τ t₂ t₁).symm.trans a₃
    have hu : IsUnit (mat (C.dict₂ h).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h ⟨τ, t₂⟩).1)
    exact Matrix.map_injective τ.injective (hu.mul_right_cancel a₄)
  obtain ⟨f, hf⟩ := exists_latEquiv _ _ γ hlat
  let gam := (φ₂ (C.dict₂ h).1).trans (f.trans (φ₁ (T.dict j σ h).1).symm)
  have hgam : ∀ a, (φ₁ (T.dict j σ h).1 (gam a) : Fin D.R.r → D.host.E) =
      (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (φ₂ (C.dict₂ h).1 a : Fin D.R.r → D.host.E) := fun a =>
    (congrArg Subtype.val ((φ₁ (T.dict j σ h).1).apply_symm_apply _)).trans (hf _)
  obtain ⟨P₁, hP₁, hp₁, hu₁, hv₁⟩ := hper₁ _ ⟨x', hx'⟩
  obtain ⟨P₂, hP₂, hp₂, hu₂, hv₂⟩ := hper₂ _ ⟨x, hx⟩
  have hle : KA T.Q.l ≤ KA C.d.l₂ := by rw [KA, KA, hA, hA₂]
  have hrel : ∀ τ : D.host.E →+* ℂ, relab T.Q.c σ τ = relab C.d.c₂ C.σ₂ τ := fun τ => by
    ext a
    exact (RingHom.congr_fun hσ₂ _).symm.trans (congrArg C.σ₂ (Subtype.ext rfl))
  obtain ⟨k₁, k₂⟩ := point_over C.d hlev (by omega) hA hle
    (RingHom.ext fun a => (congrArg C.σ₂ (Subtype.ext rfl)).trans
      (RingHom.congr_fun hσ₂ ((IntermediateField.inclusion T.Q.c.le).toRingHom a)))
    e₁ e₂ F₁ F₂ _ _ hp₁ hp₂ gam
    (fun a b => by
      have := (hEF₁ _ (gam a) (gam b)).trans (Eq.trans (by rw [hgam, hgam, hiso, (hW₁ _).2, (hW₂ _).2])
        (hEF₂ _ a b).symm)
      exact_mod_cast this)
    (fun a ha => by
      have b₂ := hm₂ a ha
      rw [hlev.2.1] at b₂
      obtain ⟨u, hu, e⟩ := hδm T.Q.l.M C.d.pd (by have := T.Q.l.three_le; omega) _ _ _
        (hm₁ a (Submodule.smul_mono_left (Ideal.map_mono hlev.1.2.1) ha)) b₂
      refine ⟨(φ₁ _).symm ⟨u, hu⟩, (φ₁ (T.dict j σ h).1).injective (Subtype.ext ?_)⟩
      rw [hgam, hγδ, e, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
      rfl)
    (fun a i => by
      rw [hP₁, hP₂, hgam, Equiv.apply_symm_apply, hrel]
      exact perFr_move _ _ hΨ ((hU₁.2.1 _).1.trans (hU₂.2.1 _).1.symm) ((hW₁ _).1.trans (hW₂ _).1.symm) γ hiso x x'
        hxx _ _ _)
  exact ⟨by rw [hu₁, hu₂]; exact k₁, fun τ i => k₂ ⟨τ, i⟩ _ _ (hv₁ τ i) (hv₂ τ i)⟩

end GlobalTheory.CoverFrameOver
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.coverReading_eq_pow_mul_movedFrameReading : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) → ∀ (x : Frame (C.U₂.X (C.dict₂ h).1).Ψ D.R.r) (x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r), x ∈ (C.U₂.X (C.dict₂ h).1).dom → x' ∈ ((T.U j σ).X (T.dict j σ h).1).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → ∃ t : ℂ, t ≠ 0 ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ (C.dict₂ h).1 x = t ^ n * rdU (T.U j σ) f (T.dict j σ h).1 x' := by
  first | exact @GlobalTheory.CoverFrameRead.rdU_cover_eq | exact GlobalTheory.CoverFrameRead.rdU_cover_eq | (intros; apply GlobalTheory.CoverFrameRead.rdU_cover_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical



theorem GlobalTheory.FlatConj.flat_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (t t' : T0), VStd D i → FixBase T R i τ → ConjTup R τ t t' → ∀ f f', IsFlatVec R i t f → IsFlatVec R i t' f' → ∃ (z : GA D (Vc D i)) (c c' : ℂ) (s : (AE D)ˣ), IsCentAt i (R.Q t) z ∧ f = c • R.ωP i t (z, 1) (R.vP i t) ∧ f' = c' • R.ωP i t' (z, 1) (R.vP i t') ∧ c' = ((R.xi t' s : Circle) : ℂ) * τ c := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hQG i τ t t' hV hFix hct f f' hf hf'
  obtain ⟨z, B, ε, r, ψP, hz, hB, hprim, hform⟩ := GlobalTheory.T.heckeChoice_flatVector_factoredForm D G Pl0 T0 A T R F hC hQG i t hV
  obtain ⟨s1, e1⟩ := hform t rfl f hf
  obtain ⟨s2, e2⟩ := hform t' hct.1 f' hf'
  obtain ⟨h1, hne, -, -⟩ := GlobalTheory.ConjRes.conj_res D G Pl0 T0 A T R F κ v₀ hC τ t t' hct
  have hg : ∀ PP ∈ R.Q t, ∃ a : (kP PP)ˣ, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      ((R.xiR t' PP a : ℂˣ) : ℂ) ^ r * GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    intro PP hP
    obtain ⟨a, -, ha⟩ := (@GlobalTheory.complexMatrixGaussSum_norm_integral_galois (kP PP) (GlobalTheory.FlatConj.resField PP) (GlobalTheory.FlatConj.resFintype PP) (Classical.decEq _)
      (ψP PP) (R.xiR t PP) r (hprim PP hP) (hne PP hP) _ rfl).2.2.2 τ (R.xiR t' PP) (h1 PP hP)
    exact ⟨a, ha⟩
  choose a ha using hg
  let v : Pl D.host.E → ℂ := fun PP => if h : PP ∈ R.Q t then ((R.xiR t' PP (a PP h) : ℂˣ) : ℂ) else 1
  obtain ⟨s3, e3⟩ := GlobalTheory.FlatConj.prod_val (R.xi t') (R.Q t) v fun PP hP => by
    simp only [v, dif_pos hP]
    exact GlobalTheory.FlatConj.xiR_val hC t' PP (hct.1 ▸ hP) _
  have hprod : ∏ PP ∈ R.Q t, τ (GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) =
      (∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP hP => ?_
    simp only [v, dif_pos hP]
    exact ha PP hP
  refine ⟨z, _, _, s2 * s1⁻¹ * s3 ^ (-((r : ℤ) * ε)), hz, e1, e2, ?_⟩
  have hX : ((R.xi t' s1 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hV3 : ((R.xi t' s3 : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have key : τ (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t PP) r) ^ ε * ((R.xi t s1 : Circle) : ℂ)) =
      B * ((∏ PP ∈ R.Q t, v PP) ^ r * ∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε *
        ((R.xi t' s1 : Circle) : ℂ) := by
    rw [map_mul, map_mul, map_zpow₀, map_prod, hprod, hB τ hFix, ← hct.2 s1]
  rw [key, e3]
  simp only [map_mul, map_inv, map_zpow, Circle.coe_mul, Circle.coe_inv, Circle.coe_zpow]
  rw [mul_zpow, ← zpow_natCast, ← _root_.zpow_mul, _root_.zpow_neg]
  have hW : ((R.xi t' s3 : Circle) : ℂ) ^ ((r : ℤ) * ε) ≠ 0 := zpow_ne_zero _ hV3
  field_simp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaLift_extremalVector_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      X.R.thF j t y (X.geo.v₀ j _) = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) F := by
  first | exact @GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum | exact GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum | (intros; apply GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLocInt

theorem rd_sum {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (s : Fin m → C.d.c₂.F) (g : Fin m → Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (∑ b, s b • g b) = ∑ b, C.σ₂ (s b) • C.rd a (g b) := by
  unfold Cover.rd

  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smulₛₗ, map_smul, smul_comm]

theorem rd_sub {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (g h : Rul C.d.Xo₂ C.d.c₂) : C.rd a (g - h) = C.rd a g - C.rd a h := by
  unfold Cover.rd
  rw [map_sub, map_sub, smul_sub]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem bddAll_of_mem_intForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (la' : HeightOneSpectrum (𝓞 C.c'.F)), (∀ y : C.c'.F, la'.valuation C.c'.F y = la.valuation C.d.c₂.F (C.d.eF y)) → ∀ (m : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → (∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b)) ∈ C.intForms a n {la} → GlobalTheory.GoodPts.BddAll (T.Q.Xo j) C.c' la' 1 (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
  intro D T hL j hj σ hσ C hU a n hdom hPin la la' hval m x f hf hmem
  obtain ⟨g₂, ⟨hcs, hint⟩, hrd⟩ := hmem
  have hex : ∀ b, ∃ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull (f b) f₂ := fun b =>
    GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n (f b) (hf b)
  choose f₂ hf₂ using hex
  have hpin : ∀ b, C.rd a (f₂ b) = T.phiJ j σ a (f b) := fun b => hPin.2 (f b) (hf b) (f₂ b) (hf₂ b).1 (hf₂ b).2
  have hG : g₂ = ∑ b, C.d.eF (x b) • f₂ b := by
    by_contra hne
    have h0 : g₂ - ∑ b, C.d.eF (x b) • f₂ b ≠ 0 := sub_ne_zero.2 hne
    have hsec : g₂ - ∑ b, C.d.eF (x b) • f₂ b ∈ sec C.d.Xo₂ C.d.c₂ a n :=
      sub_mem hcs.1 (sum_mem fun b _ => Submodule.smul_mem _ _ (hf₂ b).1)
    have hli : LinearIndependent C.d.c₂.F ![g₂ - ∑ b, C.d.eF (x b) • f₂ b] :=
      linearIndependent_unique_iff.2 h0
    have hli2 := GlobalTheory.T.coverSections_linearIndependent_adelicReadings D T hL j hj σ hσ C hU hPin.1 a n hdom 1 ![g₂ - ∑ b, C.d.eF (x b) • f₂ b]
      (fun i => by fin_cases i; exact hsec) hli
    have hz : C.rd a (g₂ - ∑ b, C.d.eF (x b) • f₂ b) = 0 := by
      rw [rd_sub, rd_sum, hrd]
      simp only [hpin, sub_self]
    exact hli2.ne_zero 0 (by simpa using hz)
  intro Tv io e ho y hy
  obtain ⟨T', iT, e', y', io₂, y₂, hext, hfin', hio₂, hover⟩ :=
    GlobalTheory.CoverPoint.exists_ext_lift_to_cover _ _ _ _ (T.Q.Xo j) C.c' 0 C.d hU.1 Tv io y hy
  have ho₂ : OverLa la T'.V io₂ (e' * e) := by
    refine ⟨Nat.mul_pos hext.1 ho.1, fun z => ?_⟩
    have h1 := hio₂ (C.d.eF.symm z)
    rw [C.d.eF.apply_symm_apply] at h1
    have h2 : vLa la z = vLa la' (C.d.eF.symm z) := by
      simp only [vLa, hval, C.d.eF.apply_symm_apply]
    rw [h1, hext.2.1, ho.2, h2]
    push_cast
    ring
  have hB := (GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg _ _ _ _ C.d.Xo₂ C.d.c₂ la g₂).2 (hint la (Set.mem_singleton la)) T' io₂ (e' * e) ho₂
    y₂ hfin'
  rw [map_one, one_mul] at hB
  have laws := GlobalTheory.firstFiveLaws.1
  letI a1 : Algebra C.c'.F T'.Fr := (iT.comp io).toAlgebra
  letI a2 : Algebra C.d.c₂.F T'.Fr := io₂.toAlgebra
  letI a0 : Algebra T.Q.c.F T'.Fr := ((iT.comp io).comp (incF T.Q.c C.c' C.hle)).toAlgebra
  have hAO : AlgOver T.Q.c C.c' C.hle T'.Fr := fun _ => rfl
  have hcomp : ∀ z : C.c'.F, algebraMap C.d.c₂.F T'.Fr (C.d.eF z) = algebraMap C.c'.F T'.Fr z := hio₂
  have e1 : ∀ b, evI y₂ (f₂ b) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    (hf₂ b).2 T'.Fr hAO hcomp y₂.1 y'.1 hover
  have e2 : ∀ b, evI y' (GlobalTheory.FieldBC.rulBC C.hle (f b)) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf b).1 hAO y'.1
  have e3 : evI y₂ g₂ = evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
    rw [hG, GlobalTheory.GalSup.evI_sum, GlobalTheory.GalSup.evI_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [e1, e2, hio₂]
    rfl
  have hgs : (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) ∈ sec (T.Q.Xo j) C.c' a n :=
    sum_mem fun b _ => Submodule.smul_mem _ _ (GlobalTheory.FieldBCModel.rulBC_mem_sec C.hle (hf b))
  obtain ⟨φ, hφ, hm⟩ := hext.2.2
  letI a3 : Algebra C.c'.F Tv.Fr := io.toAlgebra
  have e4 : evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) =
      iT (evI y (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b))) := by
    have := GlobalTheory.PlaceInt.evR_of_frMap_fromTest
      (GlobalTheory.Frames.algebraic_laws laws.secBaseChange _ _ _ _ (T.Q.Xo j) C.c').2.2.1 _ hgs.1 φ y.1 y.2.1 y'.1 hm
    exact this.trans (congrArg (fun r : Tv.Fr →+* T'.Fr => r (evR (T.Q.Xo j) C.c' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) y.1)) hφ)
  rw [map_one, one_mul, ← GlobalTheory.CoverBound.inV_map_iff iT hext.1 hext.2.1, ← e4, ← e3]
  exact hB

end GlobalTheory.CoverLocInt
end
end
