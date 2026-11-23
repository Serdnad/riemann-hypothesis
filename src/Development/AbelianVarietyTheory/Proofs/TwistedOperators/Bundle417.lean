module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem isSelfDualC_span_of_norm {D : D7} (S : HSp D) (hS : S.rank = 1) (ζ : Fin S.rank → D.host.E)
    (hζ : star ζ ⬝ᵥ (HSpace.gram S *ᵥ ζ) = -1) :
    IsSelfDualC S (Submodule.span (𝓞 D.host.E) {ζ}) := by
  have hform : ∀ x y : Fin S.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * HSpace.gram S i j * y j = star x ⬝ᵥ (HSpace.gram S *ᵥ y) := by
    intro x y
    simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  have hne : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  haveI : Subsingleton (Fin S.rank) := by rw [hS]; infer_instance
  obtain ⟨i₀, hi₀⟩ : ∃ i, ζ i ≠ 0 := Function.ne_iff.mp hne
  have hall : ∀ y : Fin S.rank → D.host.E, ∃ c : D.host.E, y = c • ζ := by
    intro y
    refine ⟨y i₀ / ζ i₀, funext fun i => ?_⟩
    rw [Subsingleton.elim i i₀, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi₀]
  have hpair : ∀ a c : D.host.E, star (a • ζ) ⬝ᵥ (HSpace.gram S *ᵥ (c • ζ)) = -(star a * c) := by
    intro a c
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, hζ, smul_eq_mul, smul_eq_mul]
    ring
  have hstar : ∀ a : 𝓞 D.host.E, IsIntegral ℤ (star (a : D.host.E)) := fun a =>
    (map_isIntegral_int (starRingEnd D.host.E) a.2 : )
  refine ⟨⟨Submodule.fg_span_singleton _, ?_⟩, fun y => ?_⟩
  · exact fun _ _ => (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp
  · obtain ⟨c, rfl⟩ := hall y
    constructor
    · intro hy x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
      rw [← hb, hform]
      refine ⟨-(⟨_, hstar a⟩ * b), ?_⟩
      have := hpair a b
      simp only [← algebraMap_smul D.host.E a, ← algebraMap_smul D.host.E b]
      rw [this]
      rfl
    · intro h
      obtain ⟨b, hb⟩ := h ζ (Submodule.mem_span_singleton_self _)
      have h1 := hpair 1 c
      rw [one_smul, star_one, one_mul] at h1
      rw [hform, h1] at hb
      refine Submodule.mem_span_singleton.mpr ⟨-b, ?_⟩
      rw [← algebraMap_smul D.host.E (-b)]
      congr 1
      rw [map_neg]
      exact neg_eq_iff_eq_neg.mpr hb

theorem isSelfDualC_line : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G), Std F → IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
  intro D T L sc G F hF
  refine isSelfDualC_span_of_norm (negSp F.Lz) F.rk (F.ζ 0) ?_
  have h1 := congrFun (congrFun G.sp.dec0.gram 0) 0
  have h2 : star (fun i => G.sp.dec0.a i 0) ⬝ᵥ (HSpace.gram (G.V (Node.core 0)) *ᵥ (fun i => G.sp.dec0.a i 0)) = 1 := by
    have h3 : antiDiagonalSignGramMatrix 1 (1 : D.host.E) 0 0 = 1 := by simp [antiDiagonalSignGramMatrix]
    rw [h3, Matrix.mul_assoc] at h1
    exact h1
  rw [← hF.zB, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, F.oz.isoB] at h2
  rw [negSp_gram, neg_mulVec, dotProduct_neg]
  exact congrArg Neg.neg h2

end GlobalTheory.AscFin

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
noncomputable section

namespace GlobalTheory.AscFin.IsoDiag



theorem last_diag_int_iso : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ ξ ∈ p.B₁, ∀ ξ' : Mx D ρ V₀.rank, MxAt (· = v) ξ → mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ ξ' → ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ')) = ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ))) → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ hstd V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast t ht htG hiso i hi
  obtain ⟨eV, heV_int, heV_act, heV_cA, -⟩ := GlobalTheory.FinPl.LastDiag.exists_idemAt D v
  have heV_id : eV ∈ idAt D (· = v) := heV_int.1
  have hcA : ∀ c ∈ idAt D (· = v), cA D c ∈ idAt D (· = v) := fun c hc => by
    rw [← heV_act c hc, map_mul, heV_cA]; exact Ideal.mul_mem_left _ _ heV_id
  have hMx : ∀ c ∈ idAt D (· = v), MxAt (· = v) (dW.incAdj V₀ (c • yZero V₀ ρ z)) :=
    fun c hc k l => by
      rw [GlobalTheory.FinPl.LastDiag.incAdj_smul, Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (hcA c hc)
  have hcong := (GlobalTheory.IwaPlace.mem_congGrp_iff W (idAt D (· = v)) _).1 htG
  have hM : MxAt (· = v) (mt W (dW.levi t) - 1) := fun k l => by rw [Matrix.sub_apply]; exact hcong k l
  have htM : t.1 - 1 = dW.pX ⬝ (mt W (dW.levi t) - 1) ⬝ dW.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, dW.pX_levi t, Matrix.mul_one, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have ha : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := GlobalTheory.FinPl.LastDiag.mxAt_mul_right (GlobalTheory.FinPl.LastDiag.mxAt_mul_left dW.pX hM) dW.jX i i
    rwa [← htM, Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hρ : 0 < ρ := by omega
  rw [← hlast hρ _ ha]
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hstd V₀ W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ ha)).2 fun u' hu' => ?_
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = dW.pX ⬝ u' := ⟨_, rfl⟩
  have hξ : MxAt (· = v) ξ := hξdef ▸ GlobalTheory.FinPl.LastDiag.mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu')
  have hu : dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) :=
    hξdef ▸ GlobalTheory.FinPl.LastDiag.wittExtZero_inclusionX_mem_homLatticeCompletion dV dW hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hu'
  have hB : ξ ∈ p.B₁ := (hS.b ξ hξ).2 hu
  have hact : mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ (t.1 ⬝ ξ) := by
    rw [HypDec.incX_apply, HypDec.incX_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, HypDec.levi_jX]
  have hχ := hiso ξ hB (t.1 ⬝ ξ) hξ hact
  rw [GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc,
    GlobalTheory.FinPl.LastDiag.yZero_mul_diag _ _ t.1 ht i hi, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj] at hχ
  rw [GlobalTheory.FinPl.LastDiag.symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sub_mul, one_mul,
    map_sub, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, hχ, ← AddChar.map_add_eq_mul]
  rw [add_neg_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.AscFin.IsoDiag
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.CondCut

variable {D : D7}

theorem idOff_sub {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v) {a : AE D} (ha : a ∈ idOff D P) : a ∈ idOff D Q := by
  unfold GlobalTheory.FinPl.idOff at ha ⊢
  rw [Submodule.mem_iInf] at ha ⊢
  exact fun w => ha ⟨w.1, h w.1 w.2⟩

theorem idAt_sup {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v) {a : AE D} (ha : a ∈ idAt D Q) : a ∈ idAt D P := by
  unfold GlobalTheory.FinPl.idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  refine Ideal.mem_inf.2 ⟨h0, ?_⟩
  rw [Submodule.mem_iInf] at hw ⊢
  exact fun w => hw ⟨w.1, fun hq => w.2 (h w.1 hq)⟩

theorem mt_mul_of_grpOff {W : HSp D} {Q : GlobalTheory.FinPl.Pl D → Prop} {b : GA D W} (hb : b ∈ grpOff W Q) {k : ℕ}
    (M : Matrix (Fin W.rank) (Fin k) (AE D)) (hM : ∀ i j, M i j ∈ idAt D Q) : mt W b * M = M := by
  have hb' := (GlobalTheory.FinPlLoc.mem_congGrp _ b).1 hb
  have key : (mt W b - 1) * M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h1 := (GlobalTheory.FinPlLoc.mem_idOff_iff Q _).1 (hb' i l)
    have h2 := (GlobalTheory.FinPlLoc.mem_idAt_iff Q _).1 (hM l j)
    rw [Matrix.sub_apply, ← h2]
    calc (mt W b i l - (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i l) * (GlobalTheory.FinPlLoc.idem D Q * M l j)
        = (GlobalTheory.FinPlLoc.idem D Q * (mt W b i l - (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i l)) * M l j := by ring
      _ = 0 := by rw [h1, zero_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at key
  exact key

theorem mul_mem_idAt {Q : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE D))
    (B : Matrix (Fin n) (Fin k) (AE D)) (hB : ∀ i j, B i j ∈ idAt D Q) (i : Fin m) (j : Fin k) : (A * B) i j ∈ idAt D Q := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hB l j)

end GlobalTheory.AscFin.CondCut


open GlobalTheory.AscFin.CondCut in
theorem GlobalTheory.AscFin.Cond.of_mul_grpOff : ∀ {D : D7} {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (P Q : GlobalTheory.FinPl.Pl D → Prop) (g₁ g₂ : GA D W), (∀ v, Q v → P v) → g₁ ∈ grpAt W Q → g₂ ∈ grpOff W Q → g₁ * g₂ = g₂ * g₁ → Cond dW p x y ψ P (g₁ * g₂) → Cond dW p x y ψ Q g₁ := by
  intro D V₀ W W₀ ρ σ dW p x y ψ P Q g₁ g₂ hQP _hg₁ hg₂ _hcomm H
  have hg₂i : g₂⁻¹ ∈ grpOff W Q := inv_mem hg₂
  have emt : ∀ {k : ℕ} (M : Matrix (Fin W.rank) (Fin k) (AE D)),
      mt W (g₁ * g₂)⁻¹ * M = mt W g₂⁻¹ * (mt W g₁⁻¹ * M) := by
    intro k M
    rw [_root_.mul_inv_rev]
    exact Matrix.mul_assoc _ _ _
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, a, ha, hoff⟩ := H.pt
    refine ⟨u, a, ha, fun i j => ?_⟩
    have h1 := idOff_sub hQP (hoff i j)
    have h2 : (((mt W g₂⁻¹ - 1) * (mt W g₁⁻¹ * (x * u.1.1)) : Matrix (Fin W.rank) (Fin ρ) (AE D))) i j ∈ idOff D Q := by
      rw [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (by
        rw [Matrix.sub_apply]; exact (GlobalTheory.FinPlLoc.mem_congGrp _ _).1 hg₂i i l)
    have e : mt W g₁⁻¹ * (x * u.1.1) - x - a =
        (mt W (g₁ * g₂)⁻¹ * (x * u.1.1) - x - a) - (mt W g₂⁻¹ - 1) * (mt W g₁⁻¹ * (x * u.1.1)) := by
      rw [emt, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, Matrix.sub_apply]
    exact sub_mem h1 h2
  · intro N hN hlow hA
    refine H.shift N (fun i j => idAt_sup hQP (hN i j)) hlow ?_
    rw [emt, mt_mul_of_grpOff hg₂i _ (mul_mem_idAt _ _ (mul_mem_idAt _ _ hN))]
    exact hA
  · intro ξ hξ ξ' hξQ he
    refine H.iso ξ hξ ξ' (fun i j => idAt_sup hQP (hξQ i j)) ?_
    have hinc : ∀ i j, (dW.incX V₀ ξ) i j ∈ idAt D Q := mul_mem_idAt _ _ hξQ
    show mt W g₁ * mt W g₂ * dW.incX V₀ ξ = _
    rw [Matrix.mul_assoc, mt_mul_of_grpOff hg₂ _ hinc]
    exact he

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section




namespace GlobalTheory.PrincipalMove

open GlobalTheory.FinPlLoc

theorem exists_move : ∀ {D : D7} (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (Q : GlobalTheory.FinPl.Pl D → Prop) (g k : GA D W) (u : UX D ρ), g ∈ grpAt W Q → k ∈ grpAt W Q → MxOff Q (mt W k * x - mt W g⁻¹ * (x * u.1.1)) → ∃ r ∈ Rgrp W x, r ∈ grpAt W Q ∧ g = r * k⁻¹ := by
  intro D W ρ x Q g k u hg hk hM
  set e : AE D := idem D Q with he_def
  have he : e * e = e := idem_mul_self Q
  have hr : g * k ∈ grpAt W Q := mul_mem hg hk
  set U : Matrix (Fin ρ) (Fin ρ) (AE D) := u.1.1 with hU
  have hu : ∀ i j : Fin ρ, (j < i → U i j = 0) ∧ U i i = 1 := fun i j => u.2 i j
  let u' : GL (Fin ρ) (AE D) := mixGL he u.1 1
  have hu'v : u'.val = e • U + (1 - e) • (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) := rfl
  have hu' : u' ∈ UX D ρ := by
    intro i j
    refine ⟨fun hij => ?_, ?_⟩
    · show u'.val i j = 0
      rw [hu'v]
      simp [Matrix.add_apply, Matrix.smul_apply, (hu i j).1 hij, Matrix.one_apply_ne hij.ne']
    · show u'.val i i = 1
      rw [hu'v]
      simp [Matrix.add_apply, Matrix.smul_apply, (hu i i).2]
  refine ⟨g * k, ⟨u', hu', ?_⟩, hr, by group⟩
  have heM : e • (mt W k * x - mt W g⁻¹ * (x * U)) = 0 := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    exact (mem_idOff_iff Q _).1 (hM i j)
  have hgg : mt W g * mt W g⁻¹ = 1 := by
    rw [← FinPlLoc.mt_mul, mul_inv_cancel, FinPlLoc.mt_one]
  have h1 : e • (mt W (g * k) * x) = e • (x * U) := by
    have : mt W (g * k) * x = x * U + mt W g * (mt W k * x - mt W g⁻¹ * (x * U)) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc (mt W g) (mt W g⁻¹), hgg, Matrix.one_mul, FinPlLoc.mt_mul, Matrix.mul_assoc]
      abel
    rw [this, smul_add, ← Matrix.mul_smul (mt W g), heM, Matrix.mul_zero, add_zero]
  have h2 : (1 - e) • (mt W (g * k) * x) = (1 - e) • x := by
    have hm := (mem_grpAt_iff Q (g * k)).1 hr
    have : (1 - e) • mt W (g * k) = (1 - e) • (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) := by
      conv_lhs => rw [← hm]
      simp only [mix, smul_add, smul_smul]
      have h3 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
      have h4 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
      rw [h3, h4, zero_smul, zero_add]
    rw [← Matrix.smul_mul, this, Matrix.smul_mul, Matrix.one_mul]
  show mt W (g * k) * x = x * u'.val
  rw [hu'v]
  calc mt W (g * k) * x = e • (mt W (g * k) * x) + (1 - e) • (mt W (g * k) * x) := by
        rw [← add_smul, add_sub_cancel, one_smul]
    _ = e • (x * U) + (1 - e) • x := by rw [h1, h2]
    _ = x * (e • U + (1 - e) • (1 : Matrix (Fin ρ) (Fin ρ) (AE D))) := by
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]

end GlobalTheory.PrincipalMove
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.LocCond

variable {D : D7}

theorem idAt_mul_idOff {P : GlobalTheory.FinPl.Pl D → Prop} {a b : AE D} (ha : a ∈ idAt D P) (hb : b ∈ idOff D P) :
    a * b = 0 := by
  have h1 := (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 ha
  have h2 := (GlobalTheory.FinPlLoc.mem_idOff_iff P b).1 hb
  calc a * b = (GlobalTheory.FinPlLoc.idem D P * a) * b := by rw [h1]
    _ = a * (GlobalTheory.FinPlLoc.idem D P * b) := by ring
    _ = 0 := by rw [h2, mul_zero]

theorem idOff_true_le {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ idOff D (fun _ => True)) : a ∈ idOff D P := by
  unfold GlobalTheory.FinPl.idOff at *
  rw [Submodule.mem_iInf] at *
  intro w
  exact ha ⟨w.1, trivial⟩

theorem idAt_le_true {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D (fun _ => True) := by
  unfold GlobalTheory.FinPl.idAt at *
  obtain ⟨h0, -⟩ := Ideal.mem_inf.1 ha
  exact Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w => absurd trivial w.2⟩

theorem mul_mem_left' {I : Ideal (AE D)} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hE : ∀ i j, E i j ∈ I) : ∀ i j, (E ⬝ Z) i j ∈ I := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hE i l)

theorem mul_mem_right' {I : Ideal (AE D)} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hZ : ∀ i j, Z i j ∈ I) : ∀ i j, (E ⬝ Z) i j ∈ I := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hZ l j)

theorem mul_eq_zero_of {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hE : ∀ i j, E i j ∈ idOff D P) (hZ : ∀ i j, Z i j ∈ idAt D P) :
    E ⬝ Z = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [mul_comm]; exact idAt_mul_idOff (hZ l j) (hE i l)

theorem off_entries {P : GlobalTheory.FinPl.Pl D → Prop} {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) :
    ∀ i j, (mt S g - 1) i j ∈ idOff D P := fun i j => by
  rw [Matrix.sub_apply]
  exact (GlobalTheory.FinPlLoc.mem_congGrp _ g).1 hg i j

theorem mt_off_mul {P : GlobalTheory.FinPl.Pl D → Prop} {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) {k : ℕ}
    (Z : Matrix (Fin S.rank) (Fin k) (AE D)) (hZ : ∀ i j, Z i j ∈ idAt D P) : mt S g ⬝ Z = Z := by
  calc mt S g ⬝ Z = (mt S g - 1) ⬝ Z + Z := by rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
    _ = Z := by rw [mul_eq_zero_of _ _ (off_entries hg) hZ, zero_add]

end GlobalTheory.AscFin.LocCond


open GlobalTheory.AscFin.LocCond in
theorem GlobalTheory.AscFin.cond_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (P : GlobalTheory.FinPl.Pl D → Prop) (h₁ h₂ : GA D W), h₁ ∈ grpAt W P → h₂ ∈ grpOff W P → Cond dW p x y ψ (fun _ => True) (h₁ * h₂) → Cond dW p x y ψ P h₁ := by
  intro D ψ _ V V₀ W W₀ ρ σ dV dW p x y P h₁ h₂ _ h2 hc
  have e2 := off_entries (inv_mem h2)
  have hinv : mt W (h₁ * h₂)⁻¹ = mt W h₂⁻¹ ⬝ mt W h₁⁻¹ := by
    rw [_root_.mul_inv_rev, GlobalTheory.FinPlLoc.mt_mul]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, a, ha, hoff⟩ := hc.pt
    refine ⟨u, a, ha, fun i j => ?_⟩
    have hk := idOff_true_le (P := P) (hoff i j)
    have hm := mul_mem_left' (mt W h₂⁻¹ - 1) (mt W h₁⁻¹ ⬝ (x ⬝ u.1.1)) e2 i j
    have eq : mt W h₁⁻¹ ⬝ (x ⬝ u.1.1) - x - a =
        (mt W (h₁ * h₂)⁻¹ ⬝ (x ⬝ u.1.1) - x - a) - (mt W h₂⁻¹ - 1) ⬝ (mt W h₁⁻¹ ⬝ (x ⬝ u.1.1)) := by
      rw [hinv, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      abel
    rw [eq, Matrix.sub_apply]
    exact sub_mem hk hm
  · intro N hN hlow hA
    refine hc.shift N (fun i j => idAt_le_true (hN i j)) hlow ?_
    have hZ : ∀ i j, (mt W h₁⁻¹ ⬝ (x ⬝ N)) i j ∈ idAt D P := mul_mem_right' _ _ (mul_mem_right' _ _ hN)
    rw [hinv, Matrix.mul_assoc, mt_off_mul (inv_mem h2) _ hZ]
    exact hA
  · intro ξ hξ ξ' hP heq
    refine hc.iso ξ hξ ξ' (fun i j => idAt_le_true (hP i j)) ?_
    have hZ : ∀ i j, (dW.incX V₀ ξ) i j ∈ idAt D P := by
      rw [HypDec.incX_apply]
      exact mul_mem_right' _ _ hP
    rw [GlobalTheory.FinPlLoc.mt_mul, Matrix.mul_assoc, mt_off_mul h2 _ hZ]
    exact heq

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapAdjLine

theorem kap_starAdj : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (x : WO (negSp F.Lz) (G.V (.core (2 * ρ + 1)))), (F.lnk ρ).κ _ (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ x) = x := by
  unfold OnStd
  intro D _ _ _ _ _ _ G _ _ _ F hF ρ x
  have hτ : (F.lnk ρ).τ = D.host.xi0 • (1 : Matrix (Fin (negSp F.Lz).rank) (Fin (negSp F.Lz).rank) D.host.E) := by
    have hl := F.line ρ
    have hu : Unique (Fin (negSp F.Lz).rank) := by rw [hl.1]; infer_instance
    have hz : F.ζ (ρ + 1) = (-D.host.xi0) • F.ζ ρ := by rw [hF.ζ, hF.ζ (ρ), pow_succ', mul_smul]
    have e : (F.lnk ρ).τ *ᵥ F.ζ ρ = -((-D.host.xi0) • F.ζ ρ) := by rw [← hz]; exact (F.lnk ρ).map
    have h2 := hl.2
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at h2
    have b : F.ζ ρ default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
    have e1 := congrFun e default
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_unique, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul, neg_neg] at e1
    funext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact mul_right_cancel₀ b e1
  rw [Lnk.κ, hτ, rat_smul, rat_one, Matrix.smul_mul, Matrix.one_mul, smul_smul, ← map_mul,
    mul_inv_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one, one_smul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

end GlobalTheory.KapAdjLine
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.card_negativeSigns_diagonalFrame_eq_signature : ∀ {D : D7} (V : HSp D), V.SigOK → ∀ (A : Fr V) (τ : D.what₂.Tau), (Finset.univ.filter fun a => A.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  first | exact @GlobalTheory.FrameSylvester.neg_card_eq_sig | exact GlobalTheory.FrameSylvester.neg_card_eq_sig | (intros; apply GlobalTheory.FrameSylvester.neg_card_eq_sig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockVectors_overVacua_dense_thetaFunctions : ∀ D : D7, GlobalTheory.ChainFr.FockDense D := by
  first | exact @GlobalTheory.FockDensity.fockDense | exact GlobalTheory.FockDensity.fockDense | (intros; apply GlobalTheory.FockDensity.fockDense <;> assumption)
end
