module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfApprox
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MultiplicityMeasurability.MeasurableMult
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.Pf.RationalApproximateSolutions

variable {ι K L : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Field L]

def condMat (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) : Matrix ((ι × ι) ⊕ (ι × ι)) (ι × ι) K :=
  Matrix.of fun r q => Sum.elim (fun p : ι × ι => if lv p.2 < lv p.1 + k ∧ q = p then (1 : K) else 0)
    (fun p => if lv p.2 < lv p.1 + 1 then G' p.1 q.1 * G q.2 p.2 else 0) r

def matOf (z : ι × ι → L) : Matrix ι ι L := Matrix.of fun a b => z (a, b)

theorem condMat_inl (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) (f : K →+* L) (z : ι × ι → L) (i j : ι) :
    ((condMat lv k G G').map f *ᵥ z) (Sum.inl (i, j)) = if lv j < lv i + k then z (i, j) else 0 := by
  first
    | simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inl]
    | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inl]
  by_cases h : lv j < lv i + k
  · rw [if_pos h, Finset.sum_eq_single (i, j)]
    · simp [h]
    · intro q _ hq
      simp [hq]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    simp [h]

theorem condMat_inr (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) (f : K →+* L) (z : ι × ι → L) (i j : ι) :
    ((condMat lv k G G').map f *ᵥ z) (Sum.inr (i, j)) =
      if lv j < lv i + 1 then (G'.map f * matOf z * G.map f) i j else 0 := by
  first
    | simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inr]
    | simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.map_apply, condMat, Matrix.of_apply, Sum.elim_inr]
  by_cases h : lv j < lv i + 1
  · simp only [h, ↓reduceIte, map_mul]
    rw [Fintype.sum_prod_type]
    simp only [Matrix.mul_apply, Matrix.map_apply, matOf, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  · simp [h]

theorem cond_iff (lv : ι → ℕ) (k : ℕ) (G G' : Matrix ι ι K) (f : K →+* L) (z : ι × ι → L) :
    (condMat lv k G G').map f *ᵥ z = 0 ↔
      InPat lv k (matOf z) ∧ InPat lv 1 (G'.map f * matOf z * G.map f) := by
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · intro i j hij
      have := congrFun hz (Sum.inl (i, j))
      rw [condMat_inl, if_pos hij] at this
      simpa [matOf] using this
    · intro i j hij
      have := congrFun hz (Sum.inr (i, j))
      rw [condMat_inr, if_pos hij] at this
      simpa using this
  · rintro ⟨h1, h2⟩
    funext r
    rcases r with ⟨i, j⟩ | ⟨i, j⟩
    · rw [condMat_inl]
      split_ifs with hij
      · simpa [matOf] using h1 i j hij
      · rfl
    · rw [condMat_inr]
      split_ifs with hij
      · simpa using h2 i j hij
      · rfl

end Formalism.L2.SG.Pf.RationalApproximateSolutions

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.RationalApproximateSolutions

theorem ratSolApprox_holds : RatSolApprox := by
  intro D X G G' k N hN
  obtain ⟨P0, hMP0, hfix0⟩ :=
    Formalism.L2.SG.Pf.RCoc.kerBaseChange_holds X.B.I.E X.B.I.E (RingHom.id _) _ _ (condMat (lvk X) k G G')
  have hfixE : ∀ w : Kap X × Kap X → X.B.I.E, condMat (lvk X) k G G' *ᵥ w = 0 → P0 *ᵥ w = w := by
    intro w hw
    have e := hfix0 w (by simpa using hw)
    simpa using e
  have hfixV : ∀ v (z : Kap X × Kap X → ℂ), (condMat (lvk X) k G G').map (X.B.I.φ v) *ᵥ z = 0 →
      P0.map (X.B.I.φ v) *ᵥ z = z := by
    intro v z hz
    obtain ⟨Pv, hMPv, hfixv⟩ :=
      Formalism.L2.SG.Pf.RCoc.kerBaseChange_holds X.B.I.E ℂ (X.B.I.φ v) _ _ (condMat (lvk X) k G G')
    have hPP : P0 * Pv = Pv := by
      refine Matrix.ext_of_mulVec_single fun q => ?_
      rw [← Matrix.mulVec_mulVec]
      apply hfixE
      rw [Matrix.mulVec_mulVec, hMPv, Matrix.zero_mulVec]
    have e := hfixv z hz
    calc P0.map (X.B.I.φ v) *ᵥ z = P0.map (X.B.I.φ v) *ᵥ (Pv.map (X.B.I.φ v) *ᵥ z) := by rw [e]
      _ = (P0 * Pv).map (X.B.I.φ v) *ᵥ z := by rw [Matrix.mulVec_mulVec, Matrix.map_mul]
      _ = z := by rw [hPP, e]
  obtain ⟨c, hc, hcI⟩ := exists_common_den (E := X.B.I.E)
    (fun q : (Kap X × Kap X) × (Kap X × Kap X) => P0 q.1 q.2)
  let Q : Matrix (Kap X × Kap X) (Kap X × Kap X) (𝓞 X.B.I.E) :=
    Matrix.of fun a b => ⟨(c : X.B.I.E) * P0 a b, hcI (a, b)⟩
  have hQ : ∀ a b, algebraMap (𝓞 X.B.I.E) X.B.I.E (Q a b) = (c : X.B.I.E) * P0 a b := fun a b => rfl
  obtain ⟨R0, hR0⟩ := Formalism.L2.SG.Pf.oeApprox_holds X.B.I.F X.B.I.E X.B.I.cm.totReal X.B.I.cm.cmUnram.1
    X.B.I.cm.deg2 X.B.I.φ X.B.I.φ_over
  obtain ⟨Nc, hNcd⟩ : ∃ Nc : ℕ, Nc = N * c := ⟨_, rfl⟩
  have hNc0 : (Nc : ℂ) ≠ 0 := by
    rw [hNcd]
    exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨((Nc : ℝ) * max R0 0) * ∑ v, ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖, fun P hP => ?_⟩
  choose y hy using fun q : Kap X × Kap X => hR0 (fun v => P v q.1 q.2 / (Nc : ℂ))
  set Yv : Kap X × Kap X → X.B.I.E := (Nc : X.B.I.E) • (P0 *ᵥ fun q => (y q : X.B.I.E)) with hYvd
  have hYv : condMat (lvk X) k G G' *ᵥ Yv = 0 := by
    rw [hYvd, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMP0, Matrix.zero_mulVec, smul_zero]
  have hcond := (cond_iff (lvk X) k G G' (RingHom.id X.B.I.E) Yv).1 (by simpa using hYv)
  refine ⟨matOf Yv, hcond.1, by simpa using hcond.2, ?_, ?_⟩
  · refine ⟨Matrix.of fun a b => (Q *ᵥ y) (a, b), ?_⟩
    ext a b
    have e := RingHom.map_mulVec (algebraMap (𝓞 X.B.I.E) X.B.I.E) Q y (a, b)
    simp only [matOf, hYvd, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    change _ = (N : X.B.I.E) * algebraMap (𝓞 X.B.I.E) X.B.I.E ((Q *ᵥ y) (a, b))
    rw [e]
    simp only [mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hNcd]
    rw [show algebraMap (𝓞 X.B.I.E) X.B.I.E (y r) = (y r : X.B.I.E) from rfl]
    push_cast
    ring
  · intro v i j
    have hm : matOf (fun q : Kap X × Kap X => P v q.1 q.2) = P v := by
      ext a b
      rfl
    have hz : (condMat (lvk X) k G G').map (X.B.I.φ v) *ᵥ (fun q : Kap X × Kap X => P v q.1 q.2) = 0 :=
      (cond_iff (lvk X) k G G' (X.B.I.φ v) _).2 (by rw [hm]; exact ⟨(hP v).1, (hP v).2⟩)
    have hfz := congrFun (hfixV v _ hz) (i, j)
    simp only [mulVec, dotProduct, Matrix.map_apply] at hfz
    have key : ((matOf Yv).map (X.B.I.φ v) - P v) i j =
        ∑ r, X.B.I.φ v (P0 (i, j) r) * ((Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2) := by

      simp only [Matrix.sub_apply, Matrix.map_apply, matOf, Matrix.of_apply, hYvd, Pi.smul_apply, smul_eq_mul,
      mulVec, dotProduct, map_mul, map_sum, map_natCast]
      conv_lhs => rw [← hfz]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    have hM0 : 0 ≤ (Nc : ℝ) * max R0 0 := mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
    rw [key]
    calc ‖∑ r, X.B.I.φ v (P0 (i, j) r) * ((Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2)‖
        ≤ ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ * ((Nc : ℝ) * max R0 0) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 : ‖P v r.1 r.2 / (Nc : ℂ) - X.B.I.φ v (y r : X.B.I.E)‖ ≤ R0 := hy r v
          have h2 : (Nc : ℂ) * (P v r.1 r.2 / (Nc : ℂ)) = P v r.1 r.2 := by field_simp
          have e2 : (Nc : ℂ) * X.B.I.φ v (y r : X.B.I.E) - P v r.1 r.2 =
              -((Nc : ℂ) * (P v r.1 r.2 / (Nc : ℂ) - X.B.I.φ v (y r : X.B.I.E))) := by
            rw [mul_sub, h2]
            ring
          rw [e2, norm_neg, norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (Nat.cast_nonneg _)
      _ = ((Nc : ℝ) * max R0 0) * ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ ((Nc : ℝ) * max R0 0) * ∑ v, ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hM0
          calc ∑ r, ‖X.B.I.φ v (P0 (i, j) r)‖ ≤ ∑ q, ∑ r, ‖X.B.I.φ v (P0 q r)‖ :=
                Finset.single_le_sum (f := fun q => ∑ r, ‖X.B.I.φ v (P0 q r)‖)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
            _ ≤ ∑ v', ∑ q, ∑ r, ‖X.B.I.φ v' (P0 q r)‖ :=
                Finset.single_le_sum (f := fun v' => ∑ q, ∑ r, ‖X.B.I.φ v' (P0 q r)‖)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
                  (Finset.mem_univ v)

end Formalism.L2.SG.TermOp.Vanish
end
end

section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section SlabAbsGen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]

theorem lintegral_le_of_uniq (Γ : Subgroup G) [Countable Γ] (FS : Set G) (hFS : IsFundamentalDomain Γ FS μ)
    (P : Set G) (hP : MeasurableSet P) (f : G → ℝ≥0∞) (hfm : Measurable f)
    (hfi : ∀ s ∈ Γ, ∀ y, f (s * y) = f y) (huniq : ∀ y ∈ P, ∀ s ∈ Γ, s * y ∈ P → s = 1) :
    ∫⁻ x in P, f x ∂μ ≤ ∫⁻ x in FS, f x ∂μ := by
  have hinv : ∀ (g : Γ) (x : G), f (g⁻¹ • x) = f x := by
    intro g x
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hfi _ (g⁻¹).2 x
  rw [hFS.setLIntegral_eq_tsum']
  simp_rw [hinv]
  rw [← lintegral_iUnion₀]
  · exact lintegral_mono_set (Set.iUnion_subset fun g => Set.inter_subset_right)
  · intro g
    exact (hP.const_smul g).nullMeasurableSet.inter hFS.nullMeasurableSet
  · intro g h hgh
    apply Disjoint.aedisjoint
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨⟨p, hp, rfl⟩, -⟩ ⟨⟨q, hq, hqx⟩, -⟩
    apply hgh
    have e : (h : G) * q = (g : G) * p := by simpa [Subgroup.smul_def] using hqx
    have hsq : ((h⁻¹ * g : Γ) : G) * p = q := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, ← e, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 : ((h⁻¹ * g : Γ) : G) = 1 := huniq p hp _ (h⁻¹ * g).2 (by rw [hsq]; exact hq)
    have h2 : h⁻¹ * g = 1 := Subtype.ext h1
    exact (inv_mul_eq_one.mp h2).symm

end SlabAbsGen

theorem lintegral_slab (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsMulLeftInvariant]
    (K : Set I.Gf) (hK : MeasurableSet K) (Ω : Set I.Ginf) (hΩ : MeasurableSet Ω) (a : I.Gf) (f : I.GA → ℝ≥0∞)
    (hfm : Measurable f) (hf : ∀ y : I.Ginf, ∀ k ∈ K, f (y, a * k) = f (y, a)) :
    ∫⁻ x in Ω ×ˢ ((a * ·) '' K), f x ∂(I.muA μf) =
      μf K * ∫⁻ y in Ω, f (y, a) ∂(Formalism.L2.SG.ProjRows.muInf I) := by
  have hs : MeasurableSet ((a * ·) '' K) := by
    rw [Set.image_mul_left]
    exact measurable_const_mul a⁻¹ hK
  have hvol : μf ((a * ·) '' K) = μf K := by
    rw [Set.image_mul_left]
    exact measure_preimage_mul μf a⁻¹ K
  have hin : ∀ y ∈ Ω, ∫⁻ x in (a * ·) '' K, f (y, x) ∂μf = f (y, a) * μf K := by
    intro y _
    rw [← hvol, ← setLIntegral_const]
    first
      | exact setLIntegral_congr_fun hs (fun x hx => by obtain ⟨k, hk, rfl⟩ := hx; exact hf y k hk)
      | exact setLIntegral_congr_fun hs (Filter.Eventually.of_forall fun x hx => by
          obtain ⟨k, hk, rfl⟩ := hx; exact hf y k hk)
  have hfa : Measurable fun y : I.Ginf => f (y, a) := by fun_prop
  unfold Formalism.MainNotions.S.AutInst.muA
  rw [← Measure.prod_restrict, lintegral_prod _ hfm.aemeasurable]
  have hout : ∫⁻ y in Ω, ∫⁻ x in (a * ·) '' K, f (y, x) ∂μf ∂(Measure.pi fun v => Formalism.REAL.muG (I.ε v)) =
      ∫⁻ y in Ω, f (y, a) * μf K ∂(Measure.pi fun v => Formalism.REAL.muG (I.ε v)) := by
    first
      | exact setLIntegral_congr_fun hΩ hin
      | exact setLIntegral_congr_fun hΩ (Filter.Eventually.of_forall hin)
  rw [hout, lintegral_mul_const _ hfa, mul_comm]

section SlabAbsPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

theorem slabAbsC_of (hW : PhWellDefC) (hSC : Formalism.L2.SG.Pf.Slab.SlabCoverC)
    (hR : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), X.LevelSubgroupNormalized → FoldReadyX X)
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      NeatKu X u Y.hK) :
    SlabAbsC := by
  intro D X Y u u' hH Ωs hΩ T T' ρ
  obtain ⟨hKL, hOK, hOK', -⟩ := hH
  have hRX := hR D X hKL
  have hWD := hW D X Y u hKL
  have hWD' := hW D X Y u' hKL
  obtain ⟨⟨FS, hFS⟩, Ω₀, a, hc0, h10, hT⟩ := hOK
  obtain ⟨⟨F', hF'⟩, Ω₀', a', hc0', h10', hT'⟩ := hOK'
  have hΩc : IsCompact (Ω₀ ∪ Ω₀') := hc0.union hc0'
  have h1 : (1 : X.B.I.GA) ∈ Ω₀ ∪ Ω₀' := Or.inl h10
  have hFD := (hT T).1 _ hΩc Set.subset_union_left
  have hFD' := (hT' T').1 _ hΩc Set.subset_union_right
  have : LocallyCompactSpace X.B.I.GA := hRX.1
  have : SecondCountableTopology X.B.I.GA := hRX.2.1
  have : T2Space X.B.I.GA := hRX.2.2.1
  have : BorelSpace X.B.I.GA := hRX.2.2.2.1
  have : DiscreteTopology (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := hRX.2.2.2.2
  have : Countable (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) := Formalism.L2.SG.Pf.countable_of_discrete _
  have : Countable (Srat X u) := Formalism.L2.SG.Pf.Slab.countable_of_le (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) inf_le_left
  have : SigmaFinite X.B.μf := X.B.sf
  have : X.B.μf.IsHaarMeasure := X.B.haar
  have := @muA_isHaar' X.B.I X.B.μf X.B.sf X.B.haar
  have hD' : IsRightTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u') (Y.Dt u') := Y.reps u'
  have : Countable (Y.Dt u') := by
    have hinj : Function.Injective
        (fun d : Y.Dt u' => (⟨d.1, hD'.1 d.2⟩ : Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)) := by
      intro d e h
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    exact hinj.countable
  set ph := Ph X u Y.hK T with hph
  set ph' := Ph X u' Y.hK T' with hph'
  set g : X.B.I.GA → ℝ≥0∞ := fun x => ‖ph x‖ₑ * ∑' δ : Y.Dt u', ‖ph' ((δ : X.B.I.GA) * x)‖ₑ with hg
  have hgm : Measurable g :=
    hFD.1.enorm.mul (Measurable.tsum fun δ => hFD'.1.enorm.comp (measurable_const_mul _))

  have hb := foldBound_holds X.B.I.GA (X.B.I.muA X.B.μf) (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u')
    inferInstance inf_le_left (Ω₀ ∪ Ω₀') hΩc.isClosed.measurableSet a' ph' hFD'.1 hFD'.2.1 hFD'.2.2 F' hF'
    (Y.Dt u') hD'
  have hm1 : ∀ x, 1 ≤ mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Ω₀ ∪ Ω₀') x :=
    fun x => PI.FoldMult.UnitaryGroupMassFormula.one_le_mult _ _ h1 x
  have hq' : quotientLIntegral (X.B.I.muA X.B.μf) F' ph' ≠ ⊤ := by
    refine ne_top_of_le_ne_top ((hT' T').2 _ hΩc F' hF').ne (lintegral_mono fun y => ?_)
    calc ‖ph' y‖ₑ = 1 * ‖ph' y‖ₑ := (one_mul _).symm
      _ ≤ _ := by gcongr; exact hm1 y
  have hfinFS : ∫⁻ x in FS, g x ∂(X.B.I.muA X.B.μf) < ⊤ := by
    calc ∫⁻ x in FS, g x ∂(X.B.I.muA X.B.μf)
        ≤ ∫⁻ x in FS, ((a' : ℝ≥0∞) * quotientLIntegral (X.B.I.muA X.B.μf) F' ph') *
            (mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Ω₀ ∪ Ω₀') x * ‖ph x‖ₑ) ∂(X.B.I.muA X.B.μf) :=
          lintegral_mono fun x => by
            calc g x ≤ ‖ph x‖ₑ * ((a' : ℝ≥0∞) * mult (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Ω₀ ∪ Ω₀') x *
                  quotientLIntegral (X.B.I.muA X.B.μf) F' ph') := by
                  simp only [hg]; gcongr; exact hb x
              _ = _ := by ring
      _ = ((a' : ℝ≥0∞) * quotientLIntegral (X.B.I.muA X.B.μf) F' ph') *
            multiplicityLIntegral (X.B.I.muA X.B.μf) (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Ω₀ ∪ Ω₀') FS ph := by
          rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hq')]
          rfl
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hq'.lt_top)
          ((hT T).2 _ hΩc FS hFS)

  have hgi : ∀ s ∈ Srat X u, ∀ y, g (s * y) = g y := by
    intro s hs y
    simp only [hg]
    rw [hFD.2.1 s hs y]
    congr 1
    have e := PI.FoldDCUnfold.W.translation_independent X.B.I.GA (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u')
      (Y.Dt u') (Y.Dt u') hD' hD' s (Subgroup.mem_inf.1 hs).1 (fun z => ‖ph' (z * y)‖ₑ)
      (fun t ht z => by simp only [mul_assoc]; rw [hFD'.2.1 t ht])
    simpa [mul_assoc] using e

  have hKm := level_subgroup_measurable X Y.hK hKL
  have hsm : MeasurableSet (slab (Y.cs u) ρ (Ωs ρ)) :=
    (hΩ ρ).1.prod ((MeasurableEquiv.mulLeft (aC (Y.cs u) ρ)).measurableSet_image.2 hKm)
  have huniq := (hSC D X Y u Ωs hKL (hN D X Y u hKL) hΩ).2
  have hslab := lintegral_le_of_uniq (X.B.I.muA X.B.μf) (Srat X u) FS hFS (slab (Y.cs u) ρ (Ωs ρ)) hsm g hgm
    hgi (fun y hy s hs hsy => (huniq ρ ρ y s hs hy hsy).1)

  have hK2 : ∀ y : X.B.I.Ginf, ∀ k ∈ X.K2, g (y, aC (Y.cs u) ρ * k) = g (y, aC (Y.cs u) ρ) := by
    intro y k hk
    have hyk : ((y, aC (Y.cs u) ρ * k) : X.B.I.GA) = (y, aC (Y.cs u) ρ) * (1, k) := by simp
    have hn : ‖X.chi2 k‖ₑ = 1 := by
      rw [← ofReal_norm, Y.hK.2.2.2.2 k hk, ENNReal.ofReal_one]
    simp only [hg]
    rw [hyk, hph, ph_right_K X u Y.hK hWD T _ k hk, enorm_mul, hn, one_mul]
    congr 1
    refine tsum_congr fun δ => ?_
    rw [hph', ← mul_assoc, ph_right_K X u' Y.hK hWD' T' _ k hk, enorm_mul, hn, one_mul]
  have hEq := lintegral_slab X.B.I X.B.μf X.K2 hKm (Ωs ρ) (hΩ ρ).1 (aC (Y.cs u) ρ) g hgm hK2
  have hlt : X.B.μf X.K2 * ∫⁻ y in Ωs ρ, g (y, aC (Y.cs u) ρ) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
    rw [← hEq]
    exact lt_of_le_of_lt hslab hfinFS
  have key : ∫⁻ y in Ωs ρ, g (y, aC (Y.cs u) ρ) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.1 hlt with h | h | h
    · exact h.2
    · exact absurd h hKL.2.2.1.ne'
    · rw [h]; exact ENNReal.zero_lt_top
  exact key

end SlabAbsPf

end Formalism.L2.SG.Pf.RegroupPf
end
end

section

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section ColCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
open Matrix

def NStrongApproxC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized →
    ∀ n ∈ X.NfinU u, ∀ c : X.B.I.Gf, ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧
      c⁻¹ * ((ν.2)⁻¹ * n) * c ∈ X.K2

theorem hfin_le_sfinU {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (x : X.B.I.Gf)
    (hx : x ∈ Hfin X u) : x ∈ SfinU X u := by
  refine ⟨fun a => ?_, ?_⟩
  · have h1 : X.B.I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.eR a) := hx (X.eR a) (Or.inl (Or.inl ⟨a, rfl⟩))
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    exact Submodule.zero_mem _
  · have h1 : X.B.I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u) =
        Formalism.L2.SG.HidaSetting.incl X.B.I (X.zR u) := hx (X.zR u) (Or.inr rfl)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    exact Submodule.zero_mem _

theorem colCoverC_of (hSA : NStrongApproxC) : ColCoverC := by
  intro D X Y u u' hH ρ δ hδ hdec
  obtain ⟨n, h, k, hn, hk, hy⟩ := hdec
  obtain ⟨ρ', ⟨γ0, κ, hh⟩, -⟩ := Y.colReps u' h
  have hK := Y.hK
  have hγ := Subgroup.mem_inf.mp γ0.2
  have hγp := Subgroup.mem_prod.mp hγ.2
  have hh' : (h : X.B.I.Gf) = (γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) *
      ((κ : Hfin X u') : X.B.I.Gf) := by
    rw [hh]
    rfl
  have hκ : (X.xu u')⁻¹ * ((κ : Hfin X u') : X.B.I.Gf) * X.xu u' ∈ X.K2 := κ.2
  obtain ⟨ν, hν, hν1, hν2, hνk⟩ := hSA D X u' hK hH.1 n hn
    ((γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')
  have hd2 := eq_mul_inv_of_mul_eq hy
  refine ⟨ρ', δ⁻¹ * ν * (γ0 : X.B.I.GA), ⟨?_, ?_⟩, ?_⟩
  · exact mul_mem (mul_mem (inv_mem hδ) hν) hγ.1
  · show (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (δ⁻¹ * ν * (γ0 : X.B.I.GA)).2 *
        (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') ∈ X.K2
    have hT : (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (δ⁻¹ * ν * (γ0 : X.B.I.GA)).2 *
        (((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u') =
        k⁻¹ * ((X.xu u')⁻¹ * ((κ : Hfin X u') : X.B.I.Gf) * X.xu u')⁻¹ *
          (((γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u')⁻¹ * (ν.2⁻¹ * n) *
            ((γ0 : X.B.I.GA).2 * ((Y.cs u').h ρ' : X.B.I.Gf) * X.xu u'))⁻¹ := by
      simp only [Prod.snd_mul, Prod.snd_inv]
      rw [hd2, hh']
      simp only [aC]
      group
    rw [hT]
    exact hK.2.1 _ (hK.2.1 _ (hK.2.2.1 _ hk) _ (hK.2.2.1 _ hκ)) _ (hK.2.2.1 _ hνk)
  · have hcancel : δ * (δ⁻¹ * ν * (γ0 : X.B.I.GA)) = ν * (γ0 : X.B.I.GA) := by group
    rw [hcancel]
    refine Subgroup.mem_inf.mpr ⟨mul_mem hν hγ.1, mul_mem ?_ ?_⟩
    · exact Subgroup.subset_closure ⟨fun v => (hν1 v).1, ⟨hν2.1, hν2.2.1⟩⟩
    · exact Subgroup.subset_closure ⟨hinf_le_sinf X u' _ hγp.1, hfin_le_sfinU X u' _ hγp.2⟩

end ColCoverPf

end Formalism.L2.SG.Pf.RegroupPf
end
end
