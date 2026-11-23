module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowRealParameterSuccAllPlusLowestWeights
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle127
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle183
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.FockTDec

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

section General

variable {σ : Type}

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  zero_mem' := fun P => by simp
  add_mem' := fun {L L'} h h' P => by
    rw [LinearMap.add_apply]
    exact (totalDegree_add _ _).trans (max_le (h P) (h' P))
  smul_mem' := fun c L h P => by
    rw [LinearMap.smul_apply]
    exact (totalDegree_smul_le _ _).trans (h P)

theorem one_mem : (1 : Module.End ℂ (MvPolynomial σ ℂ)) ∈ nonRaising σ := fun _ => le_rfl

theorem mul_mem {L L' : Module.End ℂ (MvPolynomial σ ℂ)} (h : L ∈ nonRaising σ) (h' : L' ∈ nonRaising σ) :
    L * L' ∈ nonRaising σ := fun P => (h _).trans (h' P)

theorem totalDegree_X_mul_pderiv (x y : σ) (P : MvPolynomial σ ℂ) :
    (X x * pderiv y P).totalDegree ≤ P.totalDegree := by
  classical

  conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s y = 0
  · simp [h0]
  · have hs' : (Finsupp.single y 1) + (s - Finsupp.single y 1) = s := by
      rw [add_tsub_cancel_of_le]
      rw [Finsupp.single_le_iff]; omega
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    refine le_trans ?_ (le_totalDegree hs)
    have h1 := totalDegree_monomial_le (s - Finsupp.single y 1) (AddMonoidAlgebra.coeff P s * (s y : ℂ))
    have h2 : (s.sum fun _ e => e) = 1 + (s - Finsupp.single y 1).sum fun _ e => e := by
      conv_lhs => rw [← hs']
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [h2]
    exact Nat.add_le_add_left h1 1

theorem pderiv_mem (y : σ) : (pderiv y).toLinearMap ∈ nonRaising σ := by
  intro P
  change (pderiv y P).totalDegree ≤ _
  by_cases h : pderiv y P = 0
  · simp [h]
  · refine le_trans ?_ (totalDegree_X_mul_pderiv y y P)
    rw [totalDegree_mul_of_isDomain (X_ne_zero y) h]
    omega

theorem mul_pderiv_mem (x y : σ) :
    LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) * (pderiv y).toLinearMap ∈ nonRaising σ :=
  fun P => totalDegree_X_mul_pderiv x y P

theorem pderiv_mul_mem (x y : σ) :
    (pderiv y).toLinearMap * LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) ∈ nonRaising σ := by
  classical
  intro P
  have e : ((pderiv y).toLinearMap * LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) :
      Module.End ℂ (MvPolynomial σ ℂ)) P = pderiv y (X x * P) := rfl
  rw [e]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (totalDegree_add _ _).trans (max_le (totalDegree_X_mul_pderiv x y P) ?_)
  by_cases h : x = y
  · subst h; rw [pderiv_X_self, mul_one]
  · rw [pderiv_X_of_ne h, mul_zero, totalDegree_zero]; exact Nat.zero_le _

end General

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def quad (i l : Fin b) (j : Fin a) : PolF D b a :=
  if ε' i = ε j ∧ ε' l ≠ ε j then X (τ, i, j) * X (τ, l, j) else 0

theorem sgn_mul_self (e : Bool) : sgn e * sgn e = 1 := by
  cases e <;> simp [sgn]

theorem term_mem (i l : Fin b) (j : Fin a) :
    raiO τ ε ε' i j * lowO τ ε ε' l j - LinearMap.mulLeft ℂ (quad τ ε ε' i l j) ∈ nonRaising (FVar D b a) := by
  unfold raiO lowO quad
  rw [smul_mul_smul_comm, sgn_mul_self, one_smul]
  by_cases hi : ε' i = ε j <;> by_cases hl : ε' l = ε j
  · simp only [hi, hl, if_true, ne_eq, not_true, and_false, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero]
    exact mul_pderiv_mem _ _
  · simp only [hi, hl, if_true, ne_eq, not_false_iff, and_self, if_false]
    rw [LinearMap.mulLeft_mul, Module.End.mul_eq_comp, sub_self]
    exact Submodule.zero_mem _
  · simp only [hi, hl, if_true, false_and, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero, neg_mul]
    exact Submodule.neg_mem _ (mul_mem (pderiv_mem _) (pderiv_mem _))
  · simp only [hi, hl, if_true, false_and, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero, neg_mul]
    exact Submodule.neg_mem _ (pderiv_mul_mem _ _)

def quadAll (Y : Matrix (Fin b) (Fin b) ℂ) : PolF D b a :=
  ∑ i, ∑ l, Y i l • ∑ j, quad τ ε ε' i l j

theorem quadAll_hom (Y : Matrix (Fin b) (Fin b) ℂ) : (quadAll τ ε ε' Y).IsHomogeneous 2 := by
  rw [← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => ?_)
  unfold quad
  split_ifs
  · exact (isHomogeneous_X ℂ _).mul (isHomogeneous_X ℂ _)
  · exact Submodule.zero_mem _

theorem fockQuadraticPart_ne_zero_of_offBlock_entry (Y : Matrix (Fin b) (Fin b) ℂ) (i₀ l₀ : Fin b) (j₀ : Fin a) (hi : ε' i₀ = ε j₀)
    (hl : ε' l₀ ≠ ε j₀) (hY : Y i₀ l₀ ≠ 0) : quadAll τ ε ε' Y ≠ 0 := by
  classical
  intro h0
  let pt : FVar D b a → ℂ := fun v => if v = (τ, i₀, j₀) ∨ v = (τ, l₀, j₀) then 1 else 0
  have hq : ∀ i l j, eval pt (quad τ ε ε' i l j) = if j = j₀ ∧ l = l₀ ∧ i = i₀ then 1 else 0 := by
    intro i l j
    unfold quad
    by_cases hc : ε' i = ε j ∧ ε' l ≠ ε j
    · rw [if_pos hc, map_mul, eval_X, eval_X]
      by_cases hj : j = j₀
      · subst hj
        have h1 : i ≠ l₀ := fun h => hl (h ▸ hc.1)
        have h2 : l ≠ i₀ := fun h => hc.2 (h ▸ hi)
        by_cases h3 : i = i₀ <;> by_cases h4 : l = l₀ <;> simp [pt, h1, h2, h3, h4]
      · simp [pt, hj]
    · rw [if_neg hc, map_zero, if_neg]
      rintro ⟨rfl, rfl, rfl⟩
      exact hc ⟨hi, hl⟩
  have := congrArg (eval pt) h0
  unfold quadAll at this

  simp only [map_sum, smul_eval, hq, map_zero, ite_and] at this
  apply hY
  simpa using this

theorem sub_mem (Y : Matrix (Fin b) (Fin b) ℂ) :
    fockT τ ε ε' Y - LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) ∈ nonRaising (FVar D b a) := by
  have : fockT τ ε ε' Y - LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) =
      ∑ i, ∑ l, Y i l • ∑ j, ((raiO τ ε ε' i j * lowO τ ε ε' l j - LinearMap.mulLeft ℂ (quad τ ε ε' i l j)) +
        if i = l then (1 / 2 : ℂ) • 1 else 0) := by
    have hm : LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) =
        ∑ i, ∑ l, Y i l • ∑ j, LinearMap.mulLeft ℂ (quad τ ε ε' i l j) := by
      refine LinearMap.ext fun P => ?_
      simp [quadAll, Finset.sum_mul, LinearMap.sum_apply]
    rw [hm]
    unfold fockT
    simp only [← Finset.sum_sub_distrib, ← smul_sub]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    abel
  rw [this]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ (term_mem τ ε ε' i l j) ?_)
  split_ifs
  · exact Submodule.smul_mem _ _ one_mem
  · exact Submodule.zero_mem _

theorem fockT_decomp : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin b) (Fin b) ℂ), 0 < a → (∃ i l, ε' i ≠ ε' l ∧ Y i l ≠ 0 ∧ Y l i ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y = LinearMap.mulLeft ℂ Q + L := by
  rintro D a b τ ε ε' Y ha ⟨i, l, hil, h1, h2⟩
  refine ⟨quadAll τ ε ε' Y, _, ?_, quadAll_hom τ ε ε' Y, sub_mem τ ε ε' Y, by abel⟩
  by_cases h : ε' i = ε ⟨0, ha⟩
  · exact fockQuadraticPart_ne_zero_of_offBlock_entry τ ε ε' Y i l ⟨0, ha⟩ h (fun h' => hil (h.trans h'.symm)) h1
  · refine fockQuadraticPart_ne_zero_of_offBlock_entry τ ε ε' Y l i ⟨0, ha⟩ ?_ h h2
    revert h hil
    cases ε' i <;> cases ε' l <;> cases ε ⟨0, ha⟩ <;> simp

end GlobalTheory.Chain.FockTDec

end
end

section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

noncomputable section

namespace GlobalTheory.NoExcl

open Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHermND_gram (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem chart (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) :
    (∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v := by
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨⟨e, he, -⟩, w', -, -, h1, -⟩ := SplitChart.split_chart_and_places (isCMExt_host D) (isHermND_gram V)
    (frameLat_fg V) hspan h hv (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨⟨e, he⟩, h1⟩

section Param

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {W : Submodule ℂ (DividedPowerChartLift V ν)}

end Param

section Chars

open Formalism.L2.Host

variable {T : Type} {L : LevCh D T} {t₀ : T}

end Chars

section Zero

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {σ π : Submodule ℂ (DividedPowerChartLift V ν)}

end Zero

end GlobalTheory.NoExcl

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryAdelicHeight_orthogonalEmbedding_le_pow : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ g : GA D A, GlobalTheory.Grow.height S (o.emb (g, 1)) ≤ C * GlobalTheory.Grow.height A g ^ a := by
  first | exact @GlobalTheory.EmbHeight.height_emb_le | exact GlobalTheory.EmbHeight.height_emb_le | (intros; apply GlobalTheory.EmbHeight.height_emb_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gridRowRealParameter_succ_allPlus_lowestWeights : ∀ (D : D7) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) (n N : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool) (lam' : Fin N → ℝ) (ε' : Fin N → Bool), Formalism.L2.Theta.IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.L2.Theta.IsEnum (GlobalTheory.Grid.parXp D (j + 1) τ) lam' ε' → ε = Formalism.MainNotions.S.allPos n ∧ ε' = Formalism.MainNotions.S.allPos N ∧ ∃ x₁ x₃ : ℤ, (x₁ : ℚ) = -(D.hc τ).e ⟨j, hj⟩ + (n : ℚ) / 2 ∧ (x₃ : ℚ) = -((N : ℚ) / 2 + -(D.hc τ).e ⟨j, hj⟩) ∧ ∃ (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν ∧ (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lam a = -(x₃ : ℝ) + ν (Fin.castLE hn a)) ∧ ∀ b, Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos N) lam' b = (x₁ : ℝ) + ν b := by
  first | exact @GlobalTheory.ColParam.colPar | exact GlobalTheory.ColParam.colPar | (intros; apply GlobalTheory.ColParam.colPar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links

theorem _root_.GlobalTheory.T.gridParam_regular_card_minusCount : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (i : ℕ), i ≤ D.R.m → GlobalTheory.SignedHC.IsRegular ((GlobalTheory.Grid.grid D τ).parPi i) ∧ ((GlobalTheory.Grid.grid D τ).parPi i).card = GlobalTheory.Grid.rkP D i ∧ GlobalTheory.SignedHC.nMinus ((GlobalTheory.Grid.grid D τ).parPi i) = (D.R.m - i + 1) / 2 := by
  first | exact @GlobalTheory.Grid.parPi_counts | exact GlobalTheory.Grid.parPi_counts | (intros; apply GlobalTheory.Grid.parPi_counts <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.IntKeepConj

theorem mulVec_conj_col {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (π : R →+* S)
    (b : GL (Fin d) S) (A : Matrix (Fin d) (Fin d) R) (z : Fin d → R) (k : Fin d)
    (hz : (fun j => π (z j)) = (b : Matrix (Fin d) (Fin d) S) *ᵥ Pi.single k 1) :
    (((b⁻¹ : GL (Fin d) S) : Matrix (Fin d) (Fin d) S) *ᵥ fun j => π ((A *ᵥ z) j)) =
      fun i => (((b⁻¹ : GL (Fin d) S) : Matrix (Fin d) (Fin d) S) * A.map π *
        (b : Matrix (Fin d) (Fin d) S)) i k := by
  have h1 : (fun j => π ((A *ᵥ z) j)) = A.map π *ᵥ (fun j => π (z j)) := by
    funext j; exact RingHom.map_mulVec π A z j
  rw [h1, hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  funext i
  simp [Matrix.mulVec_single]

theorem single_mem {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {d : ℕ} (k i : Fin d) :
    (Pi.single k (1 : Fv F v) : Fin d → Fv F v) i ∈ v.adicCompletionIntegers F := by
  by_cases h : i = k
  · subst h; simp only [Pi.single_eq_same]; exact (v.adicCompletionIntegers F).one_mem
  · rw [Pi.single_eq_of_ne h]; exact (v.adicCompletionIntegers F).zero_mem

end GlobalTheory.IntKeepConj

open GlobalTheory.IntKeepConj in
theorem GlobalTheory.IntKeepConj.conj_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ A : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) ∧ (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ d W v π₁ π₂ b₁ b₂ hchar hsurj A hA
  constructor
  · intro i k
    choose z hzA hz1 hz2 using fun j => hsurj (((b₁ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1) j) 0
    have hzL : z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [hchar]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu; funext j; exact hzA j u hu
      · intro i'
        have e : (fun j => π₁ (z j)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1 := funext hz1
        rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        exact single_mem v k i'
      · intro i'
        have e : (fun j => π₂ (z j)) = 0 := funext hz2
        rw [e, Matrix.mulVec_zero]; exact (v.adicCompletionIntegers F).zero_mem
    have h := ((hchar _).1 (hA z hzL)).2.1 i
    rw [mulVec_conj_col π₁ b₁ A z k (funext hz1)] at h
    exact h
  · intro i k
    choose z hzA hz1 hz2 using fun j => hsurj 0 (((b₂ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1) j)
    have hzL : z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [hchar]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu; funext j; exact hzA j u hu
      · intro i'
        have e : (fun j => π₁ (z j)) = 0 := funext hz1
        rw [e, Matrix.mulVec_zero]; exact (v.adicCompletionIntegers F).zero_mem
      · intro i'
        have e : (fun j => π₂ (z j)) = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ Pi.single k 1 := funext hz2
        rw [e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        exact single_mem v k i'
    have h := ((hchar _).1 (hA z hzL)).2.2 i
    rw [mulVec_conj_col π₂ b₂ A z k (funext hz2)] at h
    exact h
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.KeepInt

theorem mulVec_conj_mem {d : ℕ} {K : Type} [Field K] (S : ValuationSubring K)
    (b : GL (Fin d) K) (M : Matrix (Fin d) (Fin d) K) (w : Fin d → K)
    (hM : ∀ i j, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M * (b : Matrix (Fin d) (Fin d) K)) i j ∈ S)
    (hw : ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) i ∈ S) :
    ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (M *ᵥ w)) i ∈ S := by
  intro i
  have key : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (M *ᵥ w) =
      (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M * (b : Matrix (Fin d) (Fin d) K)) *ᵥ
        (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) := by
    have h1 : (b : Matrix (Fin d) (Fin d) K) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (b : Matrix (Fin d) (Fin d) K), h1, Matrix.mul_one]
  rw [key]
  simp only [Matrix.mulVec, dotProduct]
  exact S.sum_mem (fun j _ => mul_mem (hM i j) (hw j))

end GlobalTheory.KeepInt

theorem GlobalTheory.KeepInt.keepLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) →
  ∀ A : Matrix (Fin d) (Fin d) (AE F E), (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) → (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  intro F E _ _ _ _ _ d W v π₁ π₂ b₁ b₂ hiff A hA₁ hA₂ z hz
  obtain ⟨hAt, h₁, h₂⟩ := (hiff z).1 hz
  refine (hiff _).2 ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [← Matrix.mulVec_smul, hAt u hu, Matrix.mulVec_zero]
  · have e : (fun j => π₁ ((A *ᵥ z) j)) = (A.map π₁) *ᵥ (fun j => π₁ (z j)) := by
      funext j; exact RingHom.map_mulVec π₁ A z j
    rw [e]
    exact GlobalTheory.KeepInt.mulVec_conj_mem (v.adicCompletionIntegers F) b₁ _ _ hA₁ h₁
  · have e : (fun j => π₂ ((A *ᵥ z) j)) = (A.map π₂) *ᵥ (fun j => π₂ (z j)) := by
      funext j; exact RingHom.map_mulVec π₂ A z j
    rw [e]
    exact GlobalTheory.KeepInt.mulVec_conj_mem (v.adicCompletionIntegers F) b₂ _ _ hA₂ h₂
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicVectorSize_seen_orthogonalSummand_le : ∀ (D : D7) (S A B : HSp D) (o : GlobalTheory.MixModel.OrthDec S A B), ∃ C : ℝ, ∀ (h : GA D A) (η : Fin A.rank → D.host.E), GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen S (o.emb (h, 1)) (o.iA *ᵥ η)) ≤ C * GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen A h η) := by
  first | exact @GlobalTheory.HtOrth.Transp.vsize_seen_emb_le | exact GlobalTheory.HtOrth.Transp.vsize_seen_emb_le | (intros; apply GlobalTheory.HtOrth.Transp.vsize_seen_emb_le <;> assumption)
end
