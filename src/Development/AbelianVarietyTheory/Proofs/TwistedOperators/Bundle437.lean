module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle108
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SetAtOfSizeAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle423
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle400
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopCoefPair

open GlobalTheory.CoefSpace Matrix
open scoped TensorProduct

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem descEnum_cast {n m : ℕ} (E : Finset ℚ) (h1 : E.card = n) (h2 : E.card = m) (hnm : n = m) (a : Fin n) :
    GlobalTheory.SignedHC.descEnum E h1 a = GlobalTheory.SignedHC.descEnum E h2 (Fin.cast hnm a) := by
  subst hnm
  rfl

theorem par_core_top (G : GridData L sc) (τ : D.what₂.Tau) :
    Node.par D sc.cGap (.core D.R.m) τ = GlobalTheory.SignedHC.plus ((num D sc.cGap τ).weightX 0) :=
  (num D sc.cGap τ).parPi_m

theorem sign_top (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)))
    (τ : D.what₂.Tau) : M.ε τ = fun _ => true := funext fun a => by
  obtain ⟨-, q, -, hS⟩ := M.enum τ
  have hx : (q a, M.ε τ a) ∈ Node.par D sc.cGap (.core D.R.m) τ :=
    hS ▸ Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
  rw [par_core_top G τ] at hx
  obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hx
  exact (congrArg Prod.snd hy).symm

theorem lam_top (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)))
    (τ : D.what₂.Tau) (a : Fin (G.V (.core D.R.m)).rank) :
    M.lam τ a = ((LaP G τ).w a : ℝ) + ((rhoVec (G.V (.core D.R.m)).rank a : ℚ) : ℝ) := by
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hn : (G.V (.core D.R.m)).rank = rankP D D.R.m := rank_Xp G
  have hE := card_weight D sc.cGap τ
  have hmem : ∀ i, q i ∈ (num D sc.cGap τ).weightX 0 := fun i => by
    have hx : (q i, M.ε τ i) ∈ Node.par D sc.cGap (.core D.R.m) τ :=
      hS ▸ Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
    rw [par_core_top G τ] at hx
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 hx
    rw [← (Prod.mk.inj e).1]
    exact hy
  have hqa : StrictAnti q := fun i j hij => by
    have := hanti hij
    rw [hq, hq] at this
    exact_mod_cast this
  have hd := GlobalTheory.SignedHC.descEnum_unique (hE.trans hn.symm) hqa hmem
  have hw := La_cast D sc.cGap τ (Fin.cast hn a)
  have e1 : q a = ((LaP G τ).w a : ℚ) + rhoVec (G.V (.core D.R.m)).rank a := by
    rw [← hd, descEnum_cast _ _ hE hn a]
    show _ = ((La D sc.cGap τ).w (Fin.cast hn a) : ℚ) + _
    have hc : ((G.V (.core D.R.m)).rank : ℚ) = (rankP D D.R.m : ℚ) := by exact_mod_cast hn
    rw [hw, GlobalTheory.SignedHC.highestWeight, rhoVec, Fin.coe_cast, hc]
    ring
  rw [hq, e1]
  push_cast
  ring

theorem polyAction_conj {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (B g : ι → GL (Fin n) ℂ)
    (F : Pol ℂ ι n) : actP lam B⁻¹ (actP lam (B * g * B⁻¹) F) = actP lam g (actP lam B⁻¹ F) := by
  rw [← polyAction_mul, ← polyAction_mul, show B⁻¹ * (B * g * B⁻¹) = g * B⁻¹ by simp only [mul_assoc, inv_mul_cancel_left]]

theorem polyAction_inv_cancel {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ)
    (F : Pol ℂ ι n) : actP lam B (actP lam B⁻¹ F) = F := by
  rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]

theorem exists_model (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)))
    (τ : D.what₂.Tau) :
    ∃ A : M.H τ →ₗ[ℂ] MvPolynomial (Fin (G.V (.core D.R.m)).rank × Fin (G.V (.core D.R.m)).rank) ℂ,
      Function.Injective A ∧ (∀ x, A x ∈ nablaSq ℂ _ (LaP G τ)) ∧
      ∀ k : GL (Fin (G.V (.core D.R.m)).rank) ℂ,
        (k : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) ∈ Matrix.unitaryGroup _ ℂ →
        ∀ x, A (M.σ τ (k : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) x) =
          sqAct ℂ _ (LaP G τ) k (A x) := by
  obtain ⟨H', _, _, π', e, h1, h2, h3, h4⟩ := GlobalTheory.NablaType.exists_isHCTypeU_nablaSq _ (LaP G τ)
  have hds : Formalism.MainNotions.S.IsHCTypeU _ (M.lam τ) (M.σ τ) :=
    (GlobalTheory.RealPar.isDS_const_iff true _ _).1 (sign_top G M τ ▸ M.ds τ)
  rw [show M.lam τ = _ from funext (lam_top G M τ)] at hds
  obtain ⟨A, hA⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU _ _ _ _ _ _ hds h1
  refine ⟨e ∘ₗ A.toLinearMap, h2.comp A.injective, fun x => h3 _, fun k hk x => ?_⟩
  show e (A (M.σ τ k x)) = _
  rw [hA _ hk, h4 _ hk]
  rfl

theorem exists_dualPair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D),
    IsInfFam θ → ∀ (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m))),
    ∃ pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ, IsDualPair θ M (coefPlus G θ) pr := by
  intro D T L sc G θ hθ M
  classical
  have hε := sign_top G M
  let hP := GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.posDef_dual G
  let B : D.what₂.Tau → GL (Fin (G.V (.core D.R.m)).rank) ℂ := fun τ => (M.fr_unit τ).unit
  have hG : ∀ τ, gramOf B τ = gramAt D (G.V (.core D.R.m)) τ := fun τ => by
    rw [← M.fr_gram τ, hε]
    simp [gramOf, B, Formalism.REAL.Jm]
  choose A h1 h2 h3 using exists_model G M
  let T0 : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau (G.V (.core D.R.m)).rank :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau _).compLinearMap fun τ =>
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ).toLinearMap ∘ₗ A τ ∘ₗ (M.sm τ).subtype)
  have hT0 : ∀ v : M.Vec, T0 (PiTensorProduct.tprod ℂ v) = ten fun τ => A τ (v τ) := fun v => by
    simp [T0, ten]
  let T1 : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau (G.V (.core D.R.m)).rank := actP (LaP G) B⁻¹ ∘ₗ T0
  have hT1 : ∀ t, T1 t = actP (LaP G) B⁻¹ (T0 t) := fun _ => rfl
  let pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ :=
    (pairB (LaP G)).compl₁₂ ((VV ℂ (LaP G)).subtype ∘ₗ (GlobalTheory.CoefModel.toHilb (LaP G) hP).symm.toLinearMap) T1
  have hpr : ∀ w t, pr w t = pairB (LaP G) ((GlobalTheory.CoefModel.toHilb (LaP G) hP).symm w).1 (T1 t) := fun _ _ => rfl
  refine ⟨pr, fun h0 => ?_, fun τ g hg w v u hu => ?_⟩
  · have hv : ∀ τ, ∃ v : M.sm τ, (v : M.H τ) ≠ 0 := fun τ => by
      have := (M.ds τ).1
      have := (M.ds τ).2.1
      obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_smoothVec (M.ds τ).2.2.1 (M.fr_unit τ) (M.fr_gram τ)
      exact ⟨⟨v, Submodule.subset_span hs⟩, hv⟩
    choose v hv using hv
    have hten : ten (fun τ => A τ (v τ)) ≠ 0 :=
      GlobalTheory.Proof.TensorMapDescent.ten_ne_zero (fun τ => A τ (v τ)) (fun τ h => hv τ (h1 τ (h.trans (map_zero _).symm)))
    have hmem : T1 (PiTensorProduct.tprod ℂ v) ∈ VV ℂ (LaP G) := by
      rw [hT1, hT0]
      exact polyAction_mem_VV _ _ (GlobalTheory.Proof.TensorMapDescent.ten_mem (LaP G) _ fun τ => h2 τ (v τ))
    have hz : T1 (PiTensorProduct.tprod ℂ v) = 0 := congrArg Subtype.val ((pairingBNondegenerate_holds ℂ _ _ (LaP G)).2
      ⟨_, hmem⟩ fun y => by
        have h4 : pr (GlobalTheory.CoefModel.toHilb (LaP G) hP y) (PiTensorProduct.tprod ℂ v) = 0 := by
          rw [show pr = 0 from h0]
          rfl
        rw [pairBK_apply]
        exact h4)
    rw [hT1, hT0] at hz
    have := congrArg (actP (LaP G) B) hz
    exact hten ((polyAction_inv_cancel (LaP G) B _).symm.trans (this.trans (map_zero _)))
  · have ha : IsAtTau θ (G.V (.core D.R.m)) τ g (atTau θ (G.V (.core D.R.m)) τ g) := by
      have hex := (GlobalTheory.PointAtPlace.existsUnique_isAtTau (G.V (.core D.R.m)) τ θ hθ g hg).exists
      rw [atTau, dite_eq_left hex]
      exact hex.choose_spec
    set Gh := infGL θ (G.V (.core D.R.m)) (atTau θ (G.V (.core D.R.m)) τ g) with hGd
    let k := B * Gh * B⁻¹
    have hk : ∀ ρ, (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) ∈
        Matrix.unitaryGroup _ ℂ := fun ρ =>
      GlobalTheory.CoefSpace.conj_unitary (by
        have := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (G.V (.core D.R.m)) (atTau θ (G.V (.core D.R.m)) τ g) ρ
        rwa [← hG] at this)
    have hup : ∀ ρ, (Function.update v τ u ρ : M.H ρ) =
        M.σ ρ (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) (v ρ) := by
      intro ρ
      by_cases hρ : ρ = τ
      · subst hρ
        have e : (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) =
            M.fr ρ * g * (M.fr ρ)⁻¹ := by
          show ((B ρ * Gh ρ * (B ρ)⁻¹ : GL (Fin (G.V (.core D.R.m)).rank) ℂ) :
            Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) = _
          rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hGd, infGL_coe, ha.2.1]
          rfl
        rw [Function.update_self, hu, e]
        rfl
      · have e : k ρ = 1 := by
          have : Gh ρ = 1 := Units.ext (ha.2.2 ρ hρ)
          show B ρ * Gh ρ * (B ρ)⁻¹ = 1
          rw [this, mul_one, mul_inv_cancel]
        rw [Function.update_of_ne hρ, e, Units.val_one, (M.ds ρ).2.2.1.1.1]
        rfl
    have e0 : T0 (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
        actP (LaP G) k (T0 (PiTensorProduct.tprod ℂ v)) := by
      rw [hT0, hT0]
      refine Eq.trans ?_ (actTen ℂ _ _ (LaP G) k _).symm
      congr 1
      funext ρ
      rw [hup, h3 ρ _ (hk ρ)]
    have e1 : T1 (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
        actP (LaP G) Gh (T1 (PiTensorProduct.tprod ℂ v)) := by
      rw [hT1, hT1, e0]
      exact polyAction_conj (LaP G) B Gh _
    obtain ⟨x, rfl⟩ := (GlobalTheory.CoefModel.toHilb (LaP G) hP).surjective w
    calc _ = pairB (LaP G) (actP (LaP G) (invTrK Gh) x.1) (actP (LaP G) Gh (T1 (PiTensorProduct.tprod ℂ v))) := by
          rw [← e1]
          rfl
      _ = pairB (LaP G) x.1 (T1 (PiTensorProduct.tprod ℂ v)) := pairingBInvariantK_holds ℂ _ _ (LaP G) Gh _ _
      _ = _ := rfl

end GlobalTheory.TopCoefPair
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.LedSize



theorem evG_exists_sizeRows : EvG fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → (∀ w j, X.toD7.what₂.Aj j w = 0) → ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := GlobalTheory.EX.szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max (max x0 x1) (max (44 ^ 4) ((8 : ℝ) ^ (4 / eps))), ?_⟩
  rintro K rfl rfl rfl hs hx hG X hO heta hA
  have hx' := (le_max_left _ _).trans hx
  have hxL := (le_max_right _ _).trans hx
  have hP := K.ok
  have hOk := hG.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (GlobalTheory.EX.Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx') hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GlobalTheory.EX.OB.GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) (fun w _ j _ _ => hA w j)
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx') e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  refine ⟨L, e1, ?_⟩
  have hq : ((GlobalTheory.ChiGrid.q0 D : ℕ) : ℝ) < L.sc.X' := by
    have hmem := hOk.small.1
    rcases hOk.lev _ hmem with ⟨i, hi⟩ | hlt
    · exact absurd hi (hOk.small.2.2.2.1 i)
    · rw [e1]; exact hlt
  have xe : L.sc.x = K.s.x := by rw [e1]
  have ee : L.sc.eps = eps := by rw [e1]; exact hs
  refine GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_of M.params M.parT (M.CnW_eq.trans hC.1.2.2.2.2.2.2.2.1) M.sizes
    M.win.1.1 M.win.2.1.1 M.win.2.1.2 M.win.2.2.1 M.g_le hq M.ccK_top ?_ (by rw [xe]; exact le_of_max_le_left hxL)
  rw [xe, ee]
  have e2 : (8 : ℝ) = ((8 : ℝ) ^ (4 / eps)) ^ (eps / 4) := by
    rw [← Real.rpow_mul (by norm_num), show 4 / eps * (eps / 4) = 1 by field_simp, Real.rpow_one]
  rw [e2]
  exact Real.rpow_le_rpow (by positivity) (le_of_max_le_right hxL) (by positivity)

end GlobalTheory.Mem.R3.LedSize

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselPeriodCorank_converges_column : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (_hM : M.IsRow) (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W)
    (Ψ : Bridge.Gf (G.V (.top 0)) → (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W) (_hΨ : Ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.Cols G W.θ)
    (F : GA D (G.V (.grid D.R.m 0)) → ℂ) (_hF : IsAutFun (G.V (.grid D.R.m 0)) F),
    BplusConv W M (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ) ξ Ψ) F := by
  first | exact @GlobalTheory.RowBplus.bplusConv_col | exact GlobalTheory.RowBplus.bplusConv_col | (intros; apply GlobalTheory.RowBplus.bplusConv_col <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.gaussianVacuum_heisenbergDerivative_complexStructure_cancel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), M.IsGauss Bs.ψ Bs.emb g →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ g₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
            (M.heisLine Bs.ψ (cS.symm (lineAt θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) 1))) g g₁' →
          g₁ + Complex.I • g₁' = 0 := by
  first | exact @GlobalTheory.GaussCancel.heis_cancel | exact GlobalTheory.GaussCancel.heis_cancel | (intros; apply GlobalTheory.GaussCancel.heis_cancel <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbitReal

theorem orbit_heis_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) →
          (∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) →
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ →
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  intro F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hW τ _ _ γ hγ T hTa u hu f hf hsm hder f₁ hf₁
  obtain ⟨f', hf'P, hf'd⟩ := hder
  have hstab : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) v → ∀ g ∈ M.Pol ψ τ,
      ∃ g₁ ∈ M.Pol ψ τ, ∀ y, g₁ y = dOp (archCo M.co v).1 (archCo M.co v).2 g y := by
    intro v hv g hg
    obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J)
      M.co hψ
    have h0 : ∀ t, M.heisLine ψ v t 0 = 0 := fun t => by
      funext x
      simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hA : ActsD (evI F) (M.heisLine ψ v) g (D v g) :=
      (GlobalTheory.RealLift.actsLaws F _ g (D v g) (D v g)).1 _ h0 (hD v hv g).1
    refine ⟨D v g, Submodule.mem_sInf.2 fun N hN => hN.2 v hv g (Submodule.mem_sInf.1 hg N hN) _ hA, fun y => ?_⟩
    rw [(hD v hv g).2 y]
    rfl
  have hrel : ∀ t y, T t f₁ y = dOp (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1
      (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2 (T t f) y := fun t =>
    GlobalTheory.T.weil_operator_right_intertwines_heisenberg_derivative M ψ χX χW om hψ hW (γ (Multiplicative.ofAdd t)) (T t) (hTa t) u hu f f₁ hf₁
  obtain ⟨hφ, u', hu', hφd⟩ := GlobalTheory.T.heisenberg_orbit_coefficient_smooth M γ hγ u hu
  have hfun : (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) =
      fun p => dOp (archCo M.co (u * (mat (γ (Multiplicative.ofAdd p.1)))ᵀ)).1
        (archCo M.co (u * (mat (γ (Multiplicative.ofAdd p.1)))ᵀ)).2 (T p.1 f) p.2 :=
    funext fun p => hrel p.1 p.2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GlobalTheory.HeisOrbit.dOp_contDiff_family (fun t => T t f) (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1)
      (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2) hsm hφ.fst hφ.snd
  have hT0 : T 0 f = f := by
    have h1 : om (1, γ (Multiplicative.ofAdd 0)) = 1 := by
      rw [ofAdd_zero, map_one]
      exact map_one om
    have hA : Acts (evI F) (om (1, γ (Multiplicative.ofAdd 0))) f f := by
      rw [h1]
      intro r _
      rfl
    exact (GlobalTheory.RealLift.actsLaws F _ f (T 0 f) f).2.2.2.1 _ (hTa 0 f) hA
  have hφ0 : archCo M.co (u * (mat (γ (Multiplicative.ofAdd (0 : ℝ))))ᵀ) = archCo M.co u := by
    rw [ofAdd_zero, map_one]
    simp [mat]
  obtain ⟨g₁, hg₁P, hg₁⟩ := hstab u hu f' hf'P
  obtain ⟨g₂, hg₂P, hg₂⟩ := hstab u' hu' f hf
  refine ⟨g₁ + g₂, add_mem hg₁P hg₂P, fun x => ?_⟩
  have hP := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have hQ := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have h4 := GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt (fun t => T t f) (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1)
    (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2) f' _ _ hsm hf'd hP hQ x
  simp only [hφ0, hT0] at h4
  rw [SchwartzMap.add_apply, hg₁, hg₂]
  exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hrel t x)

end GlobalTheory.HeisOrbitReal
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitLatSelfDual

theorem latAtV_selfDual_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY v _ _ z hz
  exact GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X Y r s r' s' hB hX hY v z hz

end GlobalTheory.SplitLatSelfDual
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerRestrict

theorem res_indep_covol : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ (μ μ' : Measure (Mx D W.rank r)) (𝓨 𝓨' : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ' 𝓨' → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ' 𝓨' f = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs d _ _ ψ f hf μ μ' 𝓨 𝓨' h h'
  funext x
  exact GlobalTheory.MixModel.covolOne_integral_eq h h' (fun y => f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x))
    (fun γ hγ y => periodic_iso hs hf x γ hγ y)

end GlobalTheory.TowerRestrict
end
