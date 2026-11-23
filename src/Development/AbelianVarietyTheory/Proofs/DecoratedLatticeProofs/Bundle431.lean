module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle406
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle407
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateTsumLeOfThetaLevelMultiple
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiVacuumOperatorZeroOrLeftInvertible
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle408
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.otherPlacesConvolution_finite_away_orthogonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ ∀ x ∈ (Q 0).D₁.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)).support, symplO _ _ x y = 0) ∧ (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ ∀ x ∈ (Q 0).D₂.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)).support, symplO _ _ x y = 0) := by
  first | exact @GlobalTheory.QVal.inner_supp | exact GlobalTheory.QVal.inner_supp | (intros; apply GlobalTheory.QVal.inner_supp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_besselEmbedding_eq_lastGL_rootExchange : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (g : GL Q.n₂ Q.k), ∃ a₀ : GA D S.B'.A, GlobalTheory.MixPer.embA S.B'.d S.B'.o a₀ = Q.gl₂ (embX (Q.c + 1) g) ∧ (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g := by
  exact @GlobalTheory.QPl.QStep.gl₂_embX_eq_embA
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.heisenbergComb_awayFromPlace_keeps_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q₀ : QStep S) (c₁ : WO S.B.V S.J.W →₀ ℂ) (c₂ : WO S.J.W S.B'.V →₀ ℂ), IsFinComb c₁ → IsFinComb c₂ → Q₀.Away c₁ → Q₀.Away c₂ → ∀ f₁ f₂, IsThetaFunO ψ _ _ f₁ → IsThetaFunO ψ _ _ f₂ → Q₀.Vac f₁ f₂ → Q₀.Vac (comb ψ _ _ c₁ f₁) (comb ψ _ _ c₂ f₂) := by
  first | exact @GlobalTheory.VacAway.vac_comb | exact GlobalTheory.VacAway.vac_comb | (intros; apply GlobalTheory.VacAway.vac_comb <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped ENNReal

namespace GlobalTheory.HaarIdx

open MeasureTheory

theorem inv_toReal_eq_relIndex {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ] (μ : Measure Γ) [μ.IsMulLeftInvariant]
    (K H : Subgroup Γ) (hHK : H ≤ K) (hH : MeasurableSet (H : Set Γ)) (hK : μ (K : Set Γ) = 1)
    (hn : H.relIndex K ≠ 0) : ((μ (H : Set Γ)).toReal)⁻¹ = (H.relIndex K : ℝ) := by
  have hmeas : ∀ g : Γ, AEMeasurable (fun x => g * x) μ :=
    fun g => (measurable_const_mul g).aemeasurable
  have hpre : ∀ g : Γ, μ ((fun x => g * x) ⁻¹' (H : Set Γ)) = μ H := by
    intro g
    rw [← Measure.map_apply_of_aemeasurable (hmeas g) hH, map_mul_left_eq_self μ g]
  set L := H.subgroupOf K
  haveI : L.FiniteIndex := ⟨hn⟩
  haveI : Fintype (K ⧸ L) := Fintype.ofFinite _
  let C : (K ⧸ L) → Set Γ := fun q => (fun x => ((q.out : K) : Γ)⁻¹ * x) ⁻¹' (H : Set Γ)
  have hcov : (K : Set Γ) = ⋃ q, C q := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, C]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : K) : K ⧸ L), ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L (⟨x, hx⟩ : K)
      rw [hh]
      have : (((⟨x, hx⟩ : K) * (h : K) : K) : Γ)⁻¹ * x = ((h : K) : Γ)⁻¹ := by
        simp [_root_.mul_inv_rev, mul_assoc]
      rw [this]
      exact H.inv_mem (Subgroup.mem_subgroupOf.mp h.2)
    · rintro ⟨q, hq⟩
      have h1 : ((q.out : K) : Γ)⁻¹ * x ∈ K := hHK hq
      have h2 : ((q.out : K) : Γ) ∈ K := (q.out : K).2
      have := K.mul_mem h2 h1
      simpa [mul_assoc] using this
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) C) := by
    intro q q' hqq'
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro y hy hy'
    simp only [Set.mem_preimage, SetLike.mem_coe, C] at hy hy'
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change (QuotientGroup.mk q.out : K ⧸ L) = QuotientGroup.mk q'.out
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := H.mul_mem hy (H.inv_mem hy')
    simpa [_root_.mul_inv_rev, mul_assoc] using this
  have hnull : ∀ q, NullMeasurableSet (C q) μ := fun q =>
    (hmeas _).nullMeasurableSet_preimage hH
  have hsum : μ (K : Set Γ) = (Fintype.card (K ⧸ L) : ℝ≥0∞) * μ H := by
    rw [hcov, measure_iUnion₀ hdisj hnull, tsum_fintype]
    simp [C, hpre, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (K ⧸ L) : ℕ) = H.relIndex K := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hK, hcard] at hsum
  have hne : μ (H : Set Γ) ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by exact_mod_cast hn)] at hsum; exact ENNReal.one_ne_top hsum
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at hr
  have hpos : (μ (H : Set Γ)).toReal ≠ 0 := by
    intro h; rw [h, mul_zero] at hr; exact one_ne_zero hr
  field_simp
  linarith [hr]

end GlobalTheory.HaarIdx

namespace GlobalTheory


theorem QTw.QExt.m_inv_toReal_eq_relIndex : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GlobalTheory.QTw.QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : GlobalTheory.QTw.QExt G χ) (j : ℕ) (H : Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)), H ≤ KO G.k _ → MeasurableSet (H : Set (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)) → H.relIndex (KO G.k _) ≠ 0 → ((((E.m j H).toReal)⁻¹ : ℝ) : ℂ) = (H.relIndex (KO G.k _) : ℂ) := by
  intro D c v B PP G χ E j H hHK hH hn
  letI : MeasurableSpace (Matrix (XIx (Fin D.R.k) (Fin D.R.t) j) (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := Formalism.DoubleCosetMeasures.instMeasMat
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := G.k)
  haveI : BorelSpace (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : MeasurableMul (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := ⟨
    fun g => (continuous_const.mul continuous_id).measurable,
    fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI := (E.haar j).1
  rw [HaarIdx.inv_toReal_eq_relIndex (E.m j) _ H hHK hH (E.haar j).2 hn]
  push_cast
  rfl

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomWt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem relIndex_KO_ne_zero {n : Type} [Fintype n] [DecidableEq n] {J : Subgroup (GL n k)}
    (hJ : J ≤ KO k n) (ho : IsOpen (J : Set (GL n k))) : J.relIndex (KO k n) ≠ 0 := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 SplitFlip.isCompact_KO
  haveI : Finite ((KO k n) ⧸ J.subgroupOf (KO k n)) :=
    Subgroup.quotient_finite_of_isOpen _ (ho.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem N_one_apply_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (a b : n) : u.val (Sum.inl a) (Sum.inl b) = (1 : Matrix n n k) a b := by
  have := GlobalTheory.RootEx.prodN_inN_of_mem hu (Sum.inl a) (Sum.inl b) le_rfl
  simpa [Matrix.one_apply] using this

theorem mul_embX_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (u * embX c g).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem embX_mul_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (embX c g * u).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem intM_embX {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {g : GL n k} (h : IntM g.val) :
    IntM (embX c g : GL (n ⊕ Fin c) k).val := by
  rintro (a | a) (b | b)
  · simpa [embX] using h a b
  · simp [embX]
  · simp [embX]
  · by_cases e : a = b
    · subst e; simp [embX]
    · simp [embX, Matrix.one_apply, e]

theorem prX_Cgrp_KO_one (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) :
    prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  ext g
  rw [mem_prX]
  constructor
  · rintro ⟨u, hu, hC⟩
    have hw : u * embX c g ∈ KO k (n ⊕ Fin c) := by simpa using (mem_Cgrp.1 hC).2
    obtain ⟨h1, h2⟩ := mem_KO.1 hw
    refine mem_KO.2 ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [← mul_embX_inl hu g a b]; exact h1 _ _
    · have hu' : u⁻¹ ∈ N k n c 1 := inv_mem hu
      have e : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      rw [← embX_mul_inl hu' g⁻¹ a b, ← e]; exact h2 _ _
  · intro hg
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, mem_Cgrp]
    refine ⟨Subgroup.mem_sup_left ⟨g, rfl⟩, ?_⟩
    simp only [inv_one, one_mul, mul_one]
    obtain ⟨h1, h2⟩ := mem_KO.1 hg
    refine mem_KO.2 ⟨intM_embX h1, ?_⟩
    rw [← map_inv]; exact intM_embX h2

theorem reGL_symm_mem_KO_iff {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    {x : GL b k} : (reGL e).symm x ∈ KO k a ↔ x ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem twistChain_lev_zero {s : ℕ} {t κ : Type} [Fintype t] [DecidableEq t] [Fintype κ] [DecidableEq κ]
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (h : 0 + c = s + 1) :
    ((twistChain s t κ δ hδ η).lev 0 c h).J = KO k _ := by
  ext x
  change (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x ∈ (parahoric (κ ⊕ Fin (s + 1)) (Fin 0 × t) δ hδ).J ↔ _
  rw [mem_parahoric]
  have e : (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x = (reGL (stdOrd κ t 0 c h)).symm x := by
    simp [LatFrame.conj, plainFrame]
    rfl
  rw [e, reGL_symm_mem_KO_iff]
  exact ⟨fun H => H.1, fun H => ⟨H, fun i _ => i.1.elim0⟩⟩

end GlobalTheory.BottomWt

namespace GlobalTheory.QTw
open GlobalTheory.BottomWt

theorem QExt.bottom_one : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : QExt G χ), Fintype.card (E.Ch 0) = 1 ∧ (∀ α, E.wt 0 α = 1) ∧ E.idx 0 = 1 ∧ ∀ j, j ≤ G.s + 1 + 1 → E.idx j ≠ 0 := by
  intro D c v B PP G χ E
  have hz : E.A 0 G.s (zero_add _) = {1} := E.reps.zero _ _
  have hrep : ∀ α, E.rep 0 G.s (zero_add _) α = 1 := fun α => by
    have := (E.rep_bij 0 G.s (zero_add _)).mapsTo (Set.mem_univ α)
    rw [hz] at this
    exact this
  have hJ0 : ∀ c h, ((G.T E.δ E.tame E.η).lev 0 c h).J = KO G.k _ := fun c h =>
    twistChain_lev_zero E.δ E.tame E.η c h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_eq_one_iff]
    have h1 : (1 : GL _ G.k) ∈ E.A 0 G.s (zero_add _) := by rw [hz]; rfl
    obtain ⟨x, -, -⟩ := (E.rep_bij 0 G.s (zero_add _)).surjOn h1
    exact ⟨x, fun y => (E.rep_bij 0 G.s (zero_add _)).injOn (Set.mem_univ _) (Set.mem_univ _)
      ((hrep y).trans (hrep x).symm)⟩
  · intro α
    rw [E.wt_mid 0 G.s (zero_add _) α, hrep α, hJ0, prX_Cgrp_KO_one, (E.haar 0).2]
    simp
  · rw [E.idx_mid 0 (G.s + 1) (zero_add _), hJ0]
    exact Subgroup.relIndex_self _
  · intro j hj
    rcases Nat.lt_or_ge j (G.s + 2) with hl | hl
    · rw [E.idx_mid j (G.s + 1 - j) (by omega)]
      exact relIndex_KO_ne_zero (E.le _ _ _) (E.reg.2.2 _ _ _).1
    · obtain rfl : j = G.s + 1 + 1 := by omega
      rw [E.idx_top]
      exact relIndex_KO_ne_zero E.leT E.openT

end GlobalTheory.QTw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopConv

variable {D : D7}

theorem exists_finComb_of_mem_span (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {f g : WO S T → ℂ}
    (hg : g ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f)) :
    ∃ b : WO S T →₀ ℂ, IsFinComb b ∧ comb ψ S T b f = g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨Finsupp.single a.1 1, fun u hu => ?_, by rw [GlobalTheory.StepComb.comb_single', one_smul]⟩
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
    exact a.2
  | zero => exact ⟨0, fun u hu => absurd hu (Finsupp.notMem_support_iff.2 rfl), GlobalTheory.StepComb.comb_zero' ψ f⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨b', hb', rfl⟩ := hy
    exact ⟨b + b', fun u hu => (Finset.mem_union.1 (Finsupp.support_add hu)).elim (hb u) (hb' u),
      GlobalTheory.StepComb.comb_add' ψ b b' f⟩
  | smul a x _ hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨a • b, fun u hu => hb u (Finsupp.support_smul hu), GlobalTheory.StepComb.comb_smul' ψ a b f⟩

theorem isFinComb_comp (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {b b' : WO S T →₀ ℂ} (hb : IsFinComb b)
    (hb' : IsFinComb b') : ∃ c : WO S T →₀ ℂ, IsFinComb c ∧ ∀ f, comb ψ S T c f = comb ψ S T b (comb ψ S T b' f) := by
  obtain ⟨c, h1, h2⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 b b'
  refine ⟨c, fun w hw => ?_, h2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := h1 w hw
  ext i j
  have e1 := congrFun (congrFun (hb x hx) i) j
  have e2 := congrFun (congrFun (hb' y hy) i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at e1 e2 ⊢
  rw [Matrix.add_apply, RingHom.map_add (f := _), e1, e2, add_zero]

end GlobalTheory.TopConv

end

noncomputable section

namespace GlobalTheory.TopConv

theorem comb_mem_span {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {b : WO S T →₀ ℂ} (hb : IsFinComb b)
    (f : WO S T → ℂ) :
    comb ψ S T b f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  unfold comb
  exact Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨u, hb u hu⟩, rfl⟩)


end GlobalTheory.TopConv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.mixedCoordinate_tsum_le_of_theta_level_multiple : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ), ∃ k : ℕ, ∀ K₀ ∈ nhds (0 : WO S T), ∃ C : ℝ≥0, ∀ n : ℕ, 0 < n → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → ∀ w, (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ) ≤ C * (n : ℝ≥0∞) ^ k * supSob ψ θ k f := by
  first | exact @GlobalTheory.MixSumBound.mixS_tsum_le | exact GlobalTheory.MixSumBound.mixS_tsum_le | (intros; apply GlobalTheory.MixSumBound.mixS_tsum_le <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.biVacuumOperator_zero_or_left_invertible : ∀ D : D7, GlobalTheory.FinPl.BiInv D := by
  first | exact @GlobalTheory.FinPl.biInv_main | exact GlobalTheory.FinPl.biInv_main | (intros; apply GlobalTheory.FinPl.biInv_main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ c : AE D, c ∈ idAt D P → ((fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k])) := by
  first | exact @GlobalTheory.LineIdeal.mem_latV_iff | exact GlobalTheory.LineIdeal.mem_latV_iff | (intros; apply GlobalTheory.LineIdeal.mem_latV_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselPeriod_double_step_iterated_quotient_integral : ∀ (D : D7) (c : Comm D) (t : Tup c), DoubleStep D → c.Is → t.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ), (∀ a, IsContAut (c.X j) (φ a)) → RapidDec _ f → RapidDec _ (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) → ∃ F₁ : GA D (c.V (j + 1)) → ℂ, IsQuotIntL1 (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ F₁ (t.perF j (σ + 1) h φ (liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS (t.om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 f (t.pt (j + 1) P₂)) (t.pt j P₁))) ∧ ∀ h₁, IsQuotIntL1 (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ (t.integrand j σ h P₁ P₂ φ f h₁) (F₁ h₁) := by
  first | exact @GlobalTheory.SeeSaw.Assemble.doubleStep_tuple | exact GlobalTheory.SeeSaw.Assemble.doubleStep_tuple | (intros; apply GlobalTheory.SeeSaw.Assemble.doubleStep_tuple <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.principalLevel_fixes_fockVectors_finiteDatum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, ∀ k ∈ levW R i, ω (1, k) (ptAt R i σ BW f Q) = ptAt R i σ BW f Q := by
  first | exact @GlobalTheory.PrincipalLevelFock.levW_fix_ptAt | exact GlobalTheory.PrincipalLevelFock.levW_fix_ptAt | (intros; apply GlobalTheory.PrincipalLevelFock.levW_fix_ptAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf


theorem _root_.GlobalTheory.T.movedVacuum_invariant_under_stdLattice_stabilizers : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ k ∈ GfC _, ∀ k' ∈ GfC _, Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) k (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) k' (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g * k) (h * k') := by
  first | exact @GlobalTheory.AdForm.StabMoveTup.moveT_mul_stab | exact GlobalTheory.AdForm.StabMoveTup.moveT_mul_stab | (intros; apply GlobalTheory.AdForm.StabMoveTup.moveT_mul_stab <;> assumption)
end
