module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle034
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle344
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.WittSig

open Matrix
open scoped ComplexOrder

theorem cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; simp [Formalism.UG.cT, conjTranspose_apply]

theorem Jpq_conjTranspose (q p : ℕ) : (Formalism.UG.Jpq q p)ᴴ = Formalism.UG.Jpq q p := by
  simp [Formalism.UG.Jpq, fromBlocks_conjTranspose]

theorem le_of_isotropic {n : Type} [Fintype n] [DecidableEq n] {q p r : ℕ} (J : Matrix n n ℂ)
    (hS : Formalism.UG.HasSignature J q p) (X Y : Matrix n (Fin r) ℂ) (hxx : Xᴴ * J * X = 0)
    (hxy : Xᴴ * J * Y = 1) : r ≤ p := by
  obtain ⟨e, P, hP⟩ := hS
  rw [cT_conj_eq] at hP
  set Q : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ := (↑(P⁻¹) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) with hQdef
  have hPQ : (P : Matrix _ _ ℂ) * Q = 1 := by simp [Q]
  have hJ : J.reindex e e = Qᴴ * Formalism.UG.Jpq q p * Q := by
    rw [← hP]
    have h1 : Qᴴ * (P : Matrix _ _ ℂ)ᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
    calc J.reindex e e = (Qᴴ * (P : Matrix _ _ ℂ)ᴴ) * J.reindex e e * ((P : Matrix _ _ ℂ) * Q) := by
          rw [h1, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  set Z := Q * X.reindex e (Equiv.refl _) with hZdef
  set W := Q * Y.reindex e (Equiv.refl _) with hWdef
  have key : ∀ A B : Matrix n (Fin r) ℂ,
      (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) = Aᴴ * J * B := by
    intro A B
    have : (Q * A.reindex e (Equiv.refl _))ᴴ * Formalism.UG.Jpq q p * (Q * B.reindex e (Equiv.refl _)) =
        (A.reindex e (Equiv.refl _))ᴴ * (Qᴴ * Formalism.UG.Jpq q p * Q) * B.reindex e (Equiv.refl _) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, ← hJ]
    ext i j
    simp [Matrix.mul_apply, Matrix.reindex_apply, conjTranspose_apply]
    rw [← Fintype.sum_sum_type (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k (e.symm x)) * B (e.symm x) j)]
    exact e.symm.sum_comp (fun x => (∑ k, (starRingEnd ℂ) (A k i) * J k x) * B x j)
  have hZZ : Zᴴ * Formalism.UG.Jpq q p * Z = 0 := by rw [hZdef, key, hxx]
  have hWZ : Wᴴ * Formalism.UG.Jpq q p * Z = 1 := by
    have h := key X Y
    rw [hxy, ← hZdef, ← hWdef] at h
    have h2 := congrArg conjTranspose h
    simpa [conjTranspose_mul, Jpq_conjTranspose, Matrix.mul_assoc] using h2
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin p → ℂ) := (Z.submatrix Sum.inr id).mulVecLin
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    set u := Z *ᵥ c with hu
    have hlow : ∀ i, u (Sum.inr i) = 0 := fun i => by
      have := congrFun hc i
      simpa [L, u, mulVec, dotProduct, submatrix] using this
    have h0 : star u ⬝ᵥ (Formalism.UG.Jpq q p *ᵥ u) = 0 := by
      have : star c ⬝ᵥ ((Zᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c) = 0 := by rw [hZZ]; simp
      rw [← this, hu, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    have hup : (fun i => u (Sum.inl i)) = 0 := by
      rw [← dotProduct_star_self_eq_zero, ← h0]
      simp [Formalism.UG.Jpq, dotProduct, mulVec, Fintype.sum_sum_type, hlow, Matrix.one_apply]
    have hu0 : u = 0 := by
      funext x
      rcases x with i | i
      · exact congrFun hup i
      · exact hlow i
    calc c = (Wᴴ * Formalism.UG.Jpq q p * Z) *ᵥ c := by rw [hWZ, one_mulVec]
      _ = (Wᴴ * Formalism.UG.Jpq q p) *ᵥ u := by rw [hu, mulVec_mulVec]
      _ = 0 := by rw [hu0, mulVec_zero]
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem wittIndex_le_neg {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}
    (hS : Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) {r : ℕ}
    {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf) : r ≤ p := by
  have hc := (GlobalTheory.AdelicU.isCMExt_host D).2.2.2 (tauE D τ)
  have hmap : ∀ {a b : ℕ} (A : Matrix (Fin M.rank) (Fin a) D.host.E)
      (B : Matrix (Fin M.rank) (Fin b) D.host.E),
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * M.gram * B).map (tauE D τ) =
        (A.map (tauE D τ))ᴴ * gramAt D M τ * B.map (tauE D τ) := by
    intro a b A B
    rw [Matrix.map_mul, Matrix.map_mul, gramAt]
    congr 2
    ext i j
    simp [Formalism.UG.cT, conjTranspose_apply, hc]
  apply le_of_isotropic (gramAt D M τ) hS (Xf.map (tauE D τ)) (Yf.map (tauE D τ))
  · rw [← hmap, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [← hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.WittSig
end

section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.SiegelSet.ConeConv

theorem lintegral_Ici_rpow {b p : ℝ} (hb : 0 < b) (hp : p < 0) :
    ∫⁻ x, (Set.Ici b).indicator (fun x => ENNReal.ofReal (x ^ (p - 1))) x = ENNReal.ofReal (b ^ p / (-p)) := by
  rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici.symm]
  have hlt : p - 1 < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hlt hb)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x (hx : b < x) =>
      Real.rpow_nonneg (le_of_lt (lt_trans hb hx)) _)), integral_Ioi_rpow_of_lt hlt hb]
  congr 1
  have : p - 1 + 1 = p := by ring
  rw [this, div_neg, neg_div]

theorem mem_cone_cons {m : ℕ} {c x : ℝ} (y : Fin (m + 1) → ℝ) :
    (Fin.cons x y : Fin (m + 2) → ℝ) ∈ GlobalTheory.SiegelSet.cone (m + 2) c ↔
      (0 < x ∧ c * y 0 ≤ x) ∧ y ∈ GlobalTheory.SiegelSet.cone (m + 1) c := by
  simp only [GlobalTheory.SiegelSet.cone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpos, hstep, hlast⟩
    refine ⟨⟨by simpa using hpos 0, by simpa using hstep 0 1 (by simp)⟩, fun i => by simpa using hpos i.succ,
      fun i j hij => by simpa using hstep i.succ j.succ (by simp [hij]),
      fun i hi => by simpa using hlast i.succ (by simp; omega)⟩
  · rintro ⟨⟨h0, h01⟩, hpos, hstep, hlast⟩
    refine ⟨fun i => Fin.cases (by simpa using h0) (fun i => by simpa using hpos i) i, fun i j hij => ?_,
      fun i hi => ?_⟩
    · induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        induction i using Fin.cases with
        | zero =>
          have : j = 0 := Fin.ext (by simpa using hij)
          subst this; simpa using h01
        | succ i => simpa using hstep i j (by simpa using hij)
    · induction i using Fin.cases with
      | zero => simp at hi
      | succ i => simpa using hlast i (by simpa using hi)

theorem mem_cone_one {c x : ℝ} (hc : 0 < c) :
    (fun _ => x : Fin 1 → ℝ) ∈ GlobalTheory.SiegelSet.cone 1 c ↔ c ≤ x := by
  simp only [GlobalTheory.SiegelSet.cone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, _, hlast⟩
    exact hlast 0 rfl
  · intro h
    refine ⟨fun _ => lt_of_lt_of_le hc h, fun i j hij => ?_, fun _ _ => h⟩
    exact absurd hij (by omega)

theorem lintegral_cone_lt_top {c : ℝ} (hc : 0 < c) : ∀ (m : ℕ) (a : ℕ → ℝ),
    (∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a i < 0) →
    ∫⁻ t, (GlobalTheory.SiegelSet.cone (m + 1) c).indicator
      (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) t < ⊤ := by
  intro m
  induction m with
  | zero =>
    intro a ha
    have ha0 : a 0 < 0 := by simpa using ha 0 le_rfl
    change ∫⁻ t : Fin 1 → ℝ, (GlobalTheory.SiegelSet.cone 1 c).indicator
      (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) t < ⊤
    have key := (MeasurePreserving.symm _ (volume_preserving_funUnique (Fin 1) ℝ)).lintegral_comp_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
      (fun t : Fin 1 → ℝ => (GlobalTheory.SiegelSet.cone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) t)
    refine lt_of_eq_of_lt key.symm ?_
    have : ∀ x : ℝ, (GlobalTheory.SiegelSet.cone 1 c).indicator
        (fun t => ∏ i : Fin 1, ENNReal.ofReal (t i ^ (a i.val - 1))) ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm x)
        = (Set.Ici c).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x := by
      intro x
      have hx : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm x = fun _ => x := by
        funext i; simp [MeasurableEquiv.funUnique_symm_apply]
      rw [hx]
      by_cases h : c ≤ x
      · rw [Set.indicator_of_mem ((mem_cone_one hc).2 h), Set.indicator_of_mem (Set.mem_Ici.2 h)]
        simp
      · rw [Set.indicator_of_notMem (fun h' => h ((mem_cone_one hc).1 h')),
          Set.indicator_of_notMem (fun h' => h (Set.mem_Ici.1 h'))]
    simp_rw [this]
    rw [lintegral_Ici_rpow hc ha0]
    exact ENNReal.ofReal_lt_top
  | succ m ih =>
    intro a ha
    have ha0 : a 0 < 0 := by simpa using ha 0 (Nat.zero_le _)
    set a' : ℕ → ℝ := fun i => if i = 0 then a 0 + a 1 else a (i + 1) with ha'
    have hsum : ∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a' i < 0 := by
      intro k hk
      have h := ha (k + 1) (by omega)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
      rw [Finset.sum_range_succ']
      simp only [ha', if_pos, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] at *
      linarith
    set K : ℝ≥0∞ := ENNReal.ofReal (c ^ a 0 / (-a 0))
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0
    rw [← (MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) 0)).lintegral_comp_emb
      e.symm.measurableEmbedding, Measure.volume_eq_prod, ← lintegral_prod_swap]
    refine lt_of_le_of_lt (lintegral_prod_le _) ?_
    have hpt : ∀ y : Fin (m + 1) → ℝ, ∫⁻ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
        (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (e.symm (Prod.swap (y, x)))
        ≤ K * (GlobalTheory.SiegelSet.cone (m + 1) c).indicator
          (fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a' i.val - 1))) y := by
      intro y
      have he : ∀ x, e.symm (Prod.swap (y, x)) = Fin.cons x y := by
        intro x; simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero'] <;> rfl
      simp_rw [he]
      by_cases hy : y ∈ GlobalTheory.SiegelSet.cone (m + 1) c
      · have hy0 : 0 < y 0 := hy.1 0
        have hb : 0 < c * y 0 := mul_pos hc hy0
        set T : ℝ≥0∞ := ∏ i : Fin (m + 1), ENNReal.ofReal (y i ^ (a (i.val + 1) - 1))
        have hfun : ∀ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (Fin.cons x y)
            = (Set.Ici (c * y 0)).indicator (fun x => ENNReal.ofReal (x ^ (a 0 - 1))) x * T := by
          intro x
          by_cases hx : c * y 0 ≤ x
          · rw [Set.indicator_of_mem ((mem_cone_cons y).2 ⟨⟨lt_of_lt_of_le hb hx, hx⟩, hy⟩),
              Set.indicator_of_mem (Set.mem_Ici.2 hx), Fin.prod_univ_succ]
            simp [T, Fin.val_succ]
          · rw [Set.indicator_of_notMem (fun h' => hx ((mem_cone_cons y).1 h').1.2),
              Set.indicator_of_notMem (fun h' => hx (Set.mem_Ici.1 h')), zero_mul]
        simp_rw [hfun]
        rw [lintegral_mul_const' _ _ (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top),
          lintegral_Ici_rpow hb ha0, Set.indicator_of_mem hy]
        apply le_of_eq
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        have hrest : ∏ j : Fin m, ENNReal.ofReal (y j.succ ^ (a (j.succ.val + 1) - 1))
            = ∏ j : Fin m, ENNReal.ofReal (y j.succ ^ (a' j.succ.val - 1)) :=
          Finset.prod_congr rfl fun j _ => by simp [ha', Fin.val_succ]
        have h1 : 0 ≤ (c * y 0) ^ a 0 / (-a 0) := div_nonneg (Real.rpow_nonneg hb.le _) (by linarith)
        have h2 : 0 ≤ c ^ a 0 / (-a 0) := div_nonneg (Real.rpow_nonneg hc.le _) (by linarith)
        have h0 : ENNReal.ofReal ((c * y 0) ^ a 0 / (-a 0)) * ENNReal.ofReal (y 0 ^ (a ((0 : Fin (m + 1)).val + 1) - 1))
            = K * ENNReal.ofReal (y 0 ^ (a' (0 : Fin (m + 1)).val - 1)) := by
          simp only [K, ha', Fin.val_zero, zero_add, if_true]
          rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2]
          congr 1
          rw [Real.mul_rpow hc.le hy0.le, show a 0 + a 1 - 1 = (a 1 - 1) + a 0 by ring, Real.rpow_add hy0]
          ring
        rw [hrest, ← mul_assoc, ← mul_assoc, h0]
      · have hz : ∀ x, (GlobalTheory.SiegelSet.cone (m + 1 + 1) c).indicator
            (fun t => ∏ i : Fin (m + 1 + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) (Fin.cons x y) = 0 :=
          fun x => Set.indicator_of_notMem (fun h' => hy ((mem_cone_cons y).1 h').2) _
        simp_rw [hz, lintegral_zero]
        exact bot_le
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ih a' hsum)

theorem measurableSet_cone (r : ℕ) (c : ℝ) : MeasurableSet (GlobalTheory.SiegelSet.cone r c) := by
  simp only [GlobalTheory.SiegelSet.cone, Set.setOf_and, Set.setOf_forall]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_const.mul (measurable_pi_apply j)) (measurable_pi_apply i)).inter
     (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_le measurable_const (measurable_pi_apply i)))

end GlobalTheory.SiegelSet.ConeConv


open GlobalTheory.SiegelSet.ConeConv in
theorem GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top : ∀ (F : Type) [Field F] [NumberField F] (n r d : ℕ) {c : ℝ}, 0 < c →
    d < 2 * (n - r) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n r d c hc hd
  have hf : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos
  cases r with
  | zero =>
    simp only [GlobalTheory.SiegelSet.modulus, Finset.univ_eq_empty, Finset.prod_empty, mul_one, inv_one, ENNReal.ofReal_one,
      lintegral_const, one_mul]
    rw [Measure.restrict_apply MeasurableSet.univ]
    change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) _ < ⊤
    rw [Measure.pi_of_empty]
    simp only [Set.univ_inter]
    exact measure_lt_top _ _
  | succ m =>
    set f := Module.finrank ℚ F with hfdef
    set a : ℕ → ℝ := fun i => (f : ℝ) * d - 2 * f * ((n : ℝ) - 2 * i - 1) with hadef
    have closed : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), a i = f * (k + 1) * (d - 2 * n + 2 * (k + 1)) := by
      intro k
      induction k with
      | zero => rw [Finset.sum_range_one]; simp only [hadef]; push_cast; ring
      | succ k ih => rw [Finset.sum_range_succ, ih]; simp only [hadef]; push_cast; ring
    have hsum : ∀ k ≤ m, ∑ i ∈ Finset.range (k + 1), a i < 0 := by
      intro k hk
      rw [closed]
      have h1 : d + 2 * (k + 1) < 2 * n := by omega
      have h2 : (d : ℝ) + 2 * (k + 1) < 2 * n := by exact_mod_cast h1
      exact mul_neg_of_pos_of_neg (mul_pos hf (by positivity)) (by linarith)
    have hmeas := measurableSet_cone (m + 1) c
    rw [setLIntegral_congr_fun hmeas (g := fun t => ∏ i : Fin (m + 1), ENNReal.ofReal (t i ^ (a i.val - 1))) ?_,
      ← lintegral_indicator hmeas]
    · exact lintegral_cone_lt_top hc m a hsum
    intro t ht
    have hpos : ∀ i, 0 < t i := ht.1
    dsimp only
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => pow_nonneg (hpos i).le _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hpos i).le _)]
    congr 1
    unfold GlobalTheory.SiegelSet.modulus
    rw [← hfdef]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hti := hpos i
    rw [← Real.rpow_natCast, ← Real.rpow_intCast,
      show a i.val - 1 = ((f * d : ℕ) : ℝ) - ((2 * (f : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1 by
        simp only [hadef]; push_cast; ring,
      Real.rpow_sub hti, Real.rpow_sub hti, Real.rpow_one]
    field_simp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SchwartzSlope

open Filter Topology
open scoped SchwartzMap RealInnerProductSpace

theorem lintegral_of_integral (l : Type) [Fintype l] (f g : GlobalTheory.RealWeil.Sch l)
    (h : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2) : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have key : ∀ u : GlobalTheory.RealWeil.Sch l, ∫ x, ‖u x‖ ^ 2 = (∫⁻ x, ‖u x‖ₑ ^ 2).toReal := by
    intro u
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖u x‖ ^ 2) (Eventually.of_forall fun x => sq_nonneg ‖u x‖)
      ((by fun_prop : Continuous fun x => ‖u x‖ ^ 2).aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have fin : ∀ u : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖u x‖ₑ ^ 2 ≠ ⊤ := by
    intro u
    rw [GlobalTheory.MetaplecticScalarDeriv.lintegral_sq_eq]
    exact ENNReal.pow_ne_top (Lp.eLpNorm_ne_top _)
  rw [key, key] at h
  exact (ENNReal.toReal_eq_toReal_iff' (fin f) (fin g)).1 h


end GlobalTheory.SchwartzSlope

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ArchCont

open scoped SchwartzMap

theorem lintegral_of_integral {l : Type} [Fintype l] (f g : GlobalTheory.RealWeil.Sch l)
    (h : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2) : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have hi : ∀ u : GlobalTheory.RealWeil.Sch l, MeasureTheory.Integrable (fun x => ‖u x‖ ^ 2) MeasureTheory.volume := fun u =>
    (u.memLp 2 MeasureTheory.volume).integrable_norm_pow two_ne_zero
  have e : ∀ u : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖u x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖u x‖ ^ 2) := fun u => by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hi u) (.of_forall fun x => by positivity)]
    congr 1
    funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, h]

end GlobalTheory.ArchCont

namespace GlobalTheory.ArchCont

open scoped SchwartzMap RealInnerProductSpace

end GlobalTheory.ArchCont

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DerPol

end GlobalTheory.DerPol

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

theorem _root_.GlobalTheory.T.exists_baseIdempotent_of_splitIdempotentSum : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D}, IsIdemSum e P →
    ∃ ε : AF D.host.F, IsIdempotentElem ε ∧ algebraMap (AF D.host.F) (AE D) ε = e + cA D e := by
  first | exact @GlobalTheory.IdemSumF.exists_idem_below | exact GlobalTheory.IdemSumF.exists_idem_below | (intros; apply GlobalTheory.IdemSumF.exists_idem_below <;> assumption)
end

end

section

@[expose] public section

open MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil : ∀ (F : Type) [Field F] [NumberField F] (n r d : ℕ) {c : ℝ}, 0 < c → d < 2 * (n - r) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) * ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top | exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top | (intros; apply GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

theorem _root_.GlobalTheory.T.hermitianWittIndex_le_negative_signature : ∀ {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p → ∀ {r : ℕ} {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}, GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf → r ≤ p := by
  first | exact @GlobalTheory.WittSig.wittIndex_le_neg | exact GlobalTheory.WittSig.wittIndex_le_neg | (intros; apply GlobalTheory.WittSig.wittIndex_le_neg <;> assumption)

end
end
