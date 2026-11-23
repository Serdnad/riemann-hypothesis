module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDataAtRealPlaceNegFirstLowEndLtCloud
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle461
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle439
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Std.Tactic.BVDecide.Normalize.Bool
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.KFinDecomp

variable {D : D7}

def Cls (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) : Set (GA D N.V → ℂ) :=
  {f | GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N f ∧ ∀ k ∈ U, k ∈ GfC N.V → ∀ g, f (g * k) = f g}

structure IsOpAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) (A : (GA D N.V → ℂ) → (GA D N.V → ℂ)) : Prop where

  cont : ∀ f, Continuous f → Continuous (A f)

  add : ∀ f f', Continuous f → Continuous f' → A (f + f') = A f + A f'

  smul : ∀ (c : ℂ) f, Continuous f → A (c • f) = c • A f

  maps : ∀ f ∈ 𝒞, A f ∈ 𝒞

  keep : ∀ τ', τ' ≠ τ → ∀ f ∈ 𝒞, Ty τ' f → Ty τ' (A f)

  tr : ∀ τ', τ' ≠ τ → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ'), ∀ f ∈ 𝒞,
    A (rTr N.V (atTau θ N.V τ' g) f) = rTr N.V (atTau θ N.V τ' g) (A f)

  lie : ∀ τ', τ' ≠ τ → ∀ X ∈ lieAt N.V τ', ∀ f ∈ 𝒞, A (Rder θ N.V τ' X f) = Rder θ N.V τ' X (A f)

def DecompAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) : Prop :=
  ∃ (m : ℕ) (a : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ)
    (A : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → (GA D N.V → ℂ) → (GA D N.V → ℂ)),
    (∀ j u, IsOpAt θ N 𝒞 Ty τ (A j u)) ∧
    (∀ j, ∀ f ∈ 𝒞, (∀ u u', A j (u + u') f = A j u f + A j u' f) ∧ (∀ (c : ℂ) u, A j (c • u) f = c • A j u f) ∧
      (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ,
        (w : N.M.H τ) = N.M.rep τ k u → A j w f = rTr N.V (atTau θ N.V τ k) (A j u f)) ∧
      (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ,
        (w : N.M.H τ) = dRep (N.M.rep τ) X u → A j w f = Rder θ N.V τ X (A j u f))) ∧
    ∀ f ∈ 𝒞, Ty τ f → f = ∑ j, A j (a j) f

theorem isOpAt_id (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) : IsOpAt θ N 𝒞 Ty τ id :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl⟩

end GlobalTheory.KFinDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Formalism.IndefR.Mult GlobalTheory.Grid

namespace GlobalTheory.FinLift

variable {D : D7}

theorem autCusp_of_mem_cusp (N : Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFun N.V (Φ v) ∧ IsCuspFun N.V (Φ v) := by
  obtain ⟨T, hT, rfl⟩ := Submodule.mem_map.1 hΦ
  replace hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨(GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f)).toIsAutFun, GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

theorem autCusp_sum (V : HSp D) {ι : Type} (s : Finset ι) (φ : ι → GA D V → ℂ) (h : ∀ i ∈ s, IsAutFun V (φ i) ∧ IsCuspFun V (φ i)) :
    IsAutFun V (∑ i ∈ s, φ i) ∧ IsCuspFun V (∑ i ∈ s, φ i) :=
  Finset.sum_induction φ (fun ψ => IsAutFun V ψ ∧ IsCuspFun V ψ)
    (fun a b ha hb => ⟨GlobalTheory.RowLift.isAutFun_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1 hb.1 ha.2 hb.2⟩)
    ⟨GlobalTheory.RowLift.isAutFun_zero V, fun r C hC μ 𝓕 hμ h𝓕 g => by simp⟩ h

end GlobalTheory.FinLift

namespace GlobalTheory.FinLift

variable {D : D7}

theorem thetaKO_sum {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    {ι : Type} (s : Finset ι) (x : ι → WO S T → ℂ) : thetaKO om g h (∑ i ∈ s, x i) = ∑ i ∈ s, thetaKO om g h (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaKO, map_sum, Finset.sum_apply]

theorem lift_finSum {θ : InfFam D} {A B : Node D} {P : Type} {m : A.MeasDat} {n : ℕ}
    (K : Fin n → P → GA D B.V → GA D A.V → ℂ) (It : P → SmT A.M → SmT B.M)
    (hK : ∀ l, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsMult θ m (K l) It) (ps : Fin n → P) {n' : ℕ} (Fs : Fin n' → A.Maps)
    (vs : Fin n' → SmT A.M) (hF : ∀ k, Fs k ∈ A.Cusp θ) :
    (∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν) ∧
    IsAutFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) ∧
    IsCuspFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) := by
  choose F' h using fun l k => hK l (Fs k) (hF k)
  have hF' := fun l k => (h l k).1
  have hI := fun l k => (h l k).2
  have hsplit : ∀ h g, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g = ∑ l, ∑ k, K l (ps l) h g * Fs k (vs k) g :=
    fun h g => by rw [Finset.sum_mul_sum]
  have hint : ∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν := fun h => by
    simp_rw [hsplit]
    exact integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1
  have heq : (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) =
      ∑ l, ∑ k, F' l k (It (ps l) (vs k)) := by
    funext h
    simp_rw [hsplit]
    rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    exact Finset.sum_congr rfl fun k _ => (hI l k (ps l) (vs k) h).2
  rw [heq]
  exact ⟨hint, autCusp_sum B.V _ _ fun l _ => by
    simpa only [Finset.sum_apply] using autCusp_sum B.V _ _ fun k _ => autCusp_of_mem_cusp B θ (hF' l k) _⟩

end GlobalTheory.FinLift
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

theorem pairPar_X : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i < D.R.m → j ≤ D.R.m →
    PairPar (GlobalTheory.SignedHC.flip (parV D (i + 1) j τ)) (parV D i j τ) (att (cen D τ (D.R.m - i)) (rkV D (i + 1) j))
      (att (cen D τ (D.R.m - i)) (rkV D i j)) := by
  intro D hS i j τ hi hj
  have hnear := grid_nearMid D τ
  have hB1 := gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ
  have hbe := grid_hbe D τ
  have heb := grid_heb D τ
  have hbb := grid_hbb D τ hS
  have hga := grid_hga D τ
  have hN0 : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
  have hs2 : ((grid D τ).s : ℚ) + 2 ≤ (grid D τ).ga := by linarith
  have hsOdd := odd_sLen D
  have hle := entries_parD_le (grid D τ) hi hj hnear hB1 hbe hs2
  have hgap : ∀ i', GapOver ((grid D τ).parD i' j) (2 * (bigN D : ℚ) ^ 3) := fun i' =>
    gapOver_parD (grid D τ) i' j hN0 hnear hB1 heb hbb hga
  have hlt : ∀ x ∈ (grid D τ).parD i j, x.1 + ((sLen D : ℚ) + 1) / 2 ≤ (cen D τ (D.R.m - i) : ℚ) := fun x hx =>
    hle x.1 (fst_mem_entries hx)
  have hs0 : (0 : ℚ) ≤ sLen D := by positivity
  set c : ℚ := (cen D τ (D.R.m - i) : ℚ) with hc
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδdef
  set δ' : ℚ := if Odd (i + 1 + j) then -(1 / 2) else 0 with hδ'def
  have e1 : Odd (i + 1 + j) ↔ ¬ Odd (i + j) := by
    rw [show i + 1 + j = (i + j) + 1 by ring]; exact Nat.odd_add_one
  have hδ : att c (rkV D (i + 1) j) = c + δ := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδdef, sub_eq_add_neg]
    · simp [att, odd_rkV_iff, e1, h, hδdef]
  have hδ' : att c (rkV D i j) = c + δ' := by
    by_cases h : Odd (i + j)
    · simp [att, odd_rkV_iff, e1, h, hδ'def]
    · simp [att, odd_rkV_iff, e1, h, hδ'def, sub_eq_add_neg]
  have key : partner (sLen D) false (c + δ) (c + δ') (shift δ ((grid D τ).parD i j)) =
      flip (shift δ' ((grid D τ).parD (i + 1) j)) := by
    rw [parD_succ _ hi]
    ext y
    simp only [partner, Finset.mem_union, Finset.mem_image, mem_flip, mem_shift, mem_plus]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩)
      · have := hlt _ hx
        left
        rw [if_pos (by simp only at this; linarith)]
        simp only [Bool.not_not]
        convert hx using 2
        ring
      · right
        refine ⟨?_, rfl⟩
        show z - δ' ∈ TPar.block c (sLen D)
        exact sub_mem_block.2 (by simpa [add_comm] using hz)
    · rintro (h | ⟨h1, h2⟩)
      · left
        refine ⟨(y.1 - δ' + δ, !y.2), by simpa using h, ?_⟩
        have := hlt _ h
        rw [if_pos (by simp only at this ⊢; linarith)]
        ext
        · simp only; ring
        · simp
      · right
        refine ⟨y.1, ?_, ?_⟩
        · have : y.1 - δ' ∈ TPar.block c (sLen D) := h1
          simpa [add_comm] using sub_mem_block.1 this
        · ext
          · rfl
          · simpa using h2
  refine ⟨sLen D, flip (shift δ' ((grid D τ).parD (i + 1) j)), shift δ ((grid D τ).parD i j), ?_, rfl, Or.inr ?_⟩
  · exact flip_dualPar _
  · rw [hδ, hδ', ← key]
    have hX : ((grid D τ).parD i j).Nonempty :=
      ⟨((grid D τ).v 2, true), GridData.mem_parD.2 (Or.inl ⟨GridData.mem_cloud.2 ⟨2, le_rfl, (grid D τ).two_le_k, rfl⟩, rfl⟩)⟩
    have hinj : Function.Injective fun x : ℚ × Bool => (x.1 + δ, x.2) := by
      intro a b e
      simp only [Prod.mk.injEq, add_left_inj] at e
      exact Prod.ext e.1 e.2
    have hcard : (shift δ ((grid D τ).parD i j)).card + sLen D ≤ bigN D := by
      rw [shift, card_image_of_injective _ hinj]
      have h1 := card_parD_le (grid D τ) (i := i) (j := j) hi.le
      have h2 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
      have h3 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      change _ ≤ D.R.r + j * D.R.t + i * sLen D at h1
      unfold bigN
      nlinarith
    have hN : 1800 < bigN D := by
      have := hS.1
      have hr : D.R.r + 1 = D.R.k + D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
      unfold bigN
      nlinarith
    refine GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter (sLen D) false (c + δ) (c + δ') _ (bigN D) (by unfold sLen; omega) (hX.image _)
      (GapOver.isRegular hN0 (gapOver_shift δ (hgap i))) ?_ ?_ hcard hN (gapOver_shift δ (hgap i))
      (by rw [key]; exact gapOver_flip (gapOver_shift δ' (hgap (i + 1))))
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := mem_shift.1 hsg
      obtain ⟨z, hz⟩ := int_of_mem_entries_parD (grid D τ) D.R.t_odd hsOdd (fst_mem_entries h)
      obtain ⟨w, hw⟩ := hsOdd
      simp only at hz
      refine ⟨z - cen D τ (D.R.m - i) - (w + 1), ?_⟩
      rw [hw]
      push_cast
      linarith
    · intro x hx
      obtain ⟨sg, hsg⟩ := mem_entries.1 hx
      have h := hlt _ (mem_shift.1 hsg)
      simp only at h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith

end GlobalTheory.GridParD

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PureLinear

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finite_of_eq_off {ι : Type} {a b : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite)
    (h : ∀ p, p ≠ q → b p = a p) : (Function.mulSupport b).Finite := by
  refine (ha.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    rw [Function.mem_mulSupport] at hp ⊢
    rwa [h p hpq] at hp

theorem exists_cofactor {ι : Type} {a : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite) :
    ∃ C : ℂ, ∀ b : ι → ℂ, (∀ p, p ≠ q → b p = a p) → ∏ᶠ p, b p = b q * C := by
  refine ⟨∏ᶠ (p) (_ : p ≠ q), a p, fun b hb => ?_⟩
  rw [← mul_finprod_cond_ne q (finite_of_eq_off q ha hb)]
  congr 1
  exact finprod_congr fun p => finprod_congr fun hp => hb p hp

private theorem lineAt_fin_eq_zero_and_inf_other_eq_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) (i : Fin m) (j : Fin n) :
    finPart D (lineAt θ τ z t i j) = 0 ∧ ∀ ρ, ρ ≠ τ → θ ρ (infPart D (lineAt θ τ z t i j)) = 0 := by
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  set_option synthInstance.maxHeartbeats 200000 in
    refine ⟨by simpa using congrFun (congrFun (hfin t) i) j, fun ρ hρ => ?_⟩
  have h := congrFun (congrFun (hcomp t ρ) i) j
  simp only [hρ, if_false] at h
  simpa [compAt] using h

private theorem ae_eq_zero_of_fin_zero_of_theta_inf_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (a : AE D) (h1 : finPart D a = 0)
    (h2 : ∀ ρ, θ ρ (infPart D a) = 0) : a = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  exact hσ.ext a h1 h2

variable {D : D7}

theorem wAt_lineAt_self {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) : wAt (.inr τ) (lineAt θ τ z t) = lineAt θ τ z t := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  simp only [wAt]
  rw [← sub_eq_zero]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_sub, map_mul, hf]
  · intro ρ
    rw [map_sub, map_sub, map_mul, map_mul]
    by_cases hρ : ρ = τ
    · subst hρ
      rw [(hid.2.2.2.2.2.2 θ hθ ρ).1, one_mul, sub_self]
    · rw [hr ρ hρ, mul_zero, sub_zero]

theorem wAt_lineAt_ne {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) {p : Place D} (hp : p ≠ .inr τ) : wAt p (lineAt θ τ z t) = 0 := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  simp only [wAt, Matrix.zero_apply, Pi.zero_apply]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_mul, hf]
  · intro ρ
    rw [map_mul, map_mul]
    rcases p with v | τ'
    · rw [(hid.2.2.2.1 v).1, map_zero, zero_mul]
    · have hτ' : τ' ≠ τ := fun h => hp (by rw [h])
      by_cases hρ : ρ = τ'
      · subst hρ
        rw [hr ρ hτ', mul_zero]
      · rw [(hid.2.2.2.2.2.2 θ hθ ρ).2 τ' (Ne.symm hρ), zero_mul]

theorem finite_ne_of_eq_off {ι X : Type} {x y : ι → X} {f₀ : X} (q : ι) (hx : {p | x p ≠ f₀}.Finite)
    (h : ∀ p, p ≠ q → y p = x p) : {p | y p ≠ f₀}.Finite := by
  refine (hx.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    simp only [Set.mem_setOf_eq] at hp ⊢
    rwa [h p hpq] at hp

theorem isPure_linear_and_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → (∀ (x y z : Place D → WO S T → ℂ) (f g : WO S T → ℂ) (q : Place D) (c : ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → y p = x p) → (∀ p, p ≠ q → z p = x p) → z q = c • x q + y q → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • f + g)) ∧ ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → (∀ p, p ≠ .inr τ → x' p = x p) → x' (.inr τ) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ)) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) :=
    Formalism.IndefR.Fock.CCR.theta_add hf hg
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) :=
    Formalism.IndefR.Fock.CCR.theta_smul hf c
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hthH : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  refine ⟨fun x y z f g q c hx hy hyx hzx hzq => ?_, fun x x' f τ z hx hx' hxτ => ?_⟩
  · unfold IsPure IsRestricted at hx hy ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx
    obtain ⟨⟨hyl, -⟩, hgθ, hyw⟩ := hy
    have hzl : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (z p) := by
      intro p
      by_cases hp : p = q
      · rw [hp, hzq]
        exact ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x q) (hxl q).1).2 q (hxl q)).2.1 c (y q) (hyl q)
      · rw [hzx p hp]
        exact hxl p
    refine ⟨⟨hzl, finite_ne_of_eq_off q hxfin hzx⟩,
      theta_add (theta_smul c hfθ) hgθ, fun w => ?_⟩
    obtain ⟨hxs, hxe⟩ := hxw w
    obtain ⟨-, hye⟩ := hyw w
    obtain ⟨C, hC⟩ := exists_cofactor q hxs
    have ha := hC (fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) (fun _ _ => rfl)
    have hb := hC (fun p => ipO μ 𝓕 (y p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hyx p hp])
    have hd := hC (fun p => ipO μ 𝓕 (z p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hzx p hp])
    beta_reduce at ha hb hd
    refine ⟨finite_of_eq_off q hxs (fun p hp => by simp only [hzx p hp]), ?_⟩
    have hG := hthH w f₀ hf₀
    have hGq := hthH (wAt q w) f₀ hf₀
    have e1 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (c • f) (heisO ψ S T w f₀) (theta_smul c hfθ) hG
    have e2 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w f₀) hfθ hG
    have e3 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (c • x q) (heisO ψ S T (wAt q w) f₀)
      (theta_smul c (hxl q).1) hGq
    have e4 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x q) (heisO ψ S T (wAt q w) f₀) (hxl q).1 hGq
    rw [hd, hzq, (e3.2.2.2.1 (y q) (hyl q).1).1, (e4.2.2.1 c).1, (e1.2.2.2.1 g hgθ).1, (e2.2.2.1 c).1,
      hxe, hye, ha, hb]
    ring
  · have hx1 := hx
    unfold IsPure IsRestricted at hx1 ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx1
    have hx'l : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (x' p) := by
      intro p
      by_cases hp : p = .inr τ
      · rw [hp, hxτ]
        exact ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x (.inr τ)) (hxl _).1).2 (.inr τ) (hxl _)).2.2 τ rfl z
      · rw [hx' p hp]
        exact hxl p
    refine ⟨⟨hx'l, finite_ne_of_eq_off (.inr τ) hxfin hx'⟩,
      GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hfθ, fun w => ?_⟩
    obtain ⟨hxs, -⟩ := hxw w
    obtain ⟨C, hC⟩ := exists_cofactor (.inr τ) hxs
    have key : ∀ t : ℝ, ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀) =
        ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C := by
      intro t
      have hP := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx (lineAt θ τ z t)
      unfold IsPure at hP
      have e := hC (fun p => ipO μ 𝓕 (heisO ψ S T (wAt p (lineAt θ τ z t)) (x p)) (heisO ψ S T (wAt p w) f₀))
        (fun p hp => by simp only [wAt_lineAt_ne hθ τ z t hp, GlobalTheory.WeilVacMove.heisO_zero])
      beta_reduce at e
      rw [(hP.2.2 w).2, e, wAt_lineAt_self hθ τ z t]
    have hG := hthH w f₀ hf₀
    have h1 := (GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ f (heisO ψ S T w f₀) hfθ hG τ z).1
    have h2 := ((GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ (x (.inr τ)) (heisO ψ S T (wAt (.inr τ) w) f₀)
      (hxl _).1 (hthH _ _ hf₀) τ z).1).mul_const C
    have h3 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀))
        (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C) 0 := by
      simpa only [key] using h2
    have hd := hC (fun p => ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hx' p hp])
    beta_reduce at hd
    refine ⟨finite_of_eq_off (.inr τ) hxs (fun p hp => by simp only [hx' p hp]), ?_⟩
    rw [hd, hxτ, h1.unique h3]

end GlobalTheory.PureLinear

end
end
