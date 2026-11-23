module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle129
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Formalism.HermitianCurvature.StatementB
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.UniformSpace.Matrix
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009

@[expose] public section

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

private lemma Hpk_apply_of_lt_eq_ite (k r : ℕ) (c s : Fin (2 * r + k + 1)) (hc : c.val < r) :
    Formalism.QuantumDeterminants.Hpk k r c s = if c.val + s.val = 2 * r + k then 1 else 0 := by
  by_cases h : c.val + s.val = 2 * r + k
  · simp [Formalism.QuantumDeterminants.Hpk, hc, h]
  · have h' : ¬ r ≤ c.val := Nat.not_le.mpr hc
    simp [Formalism.QuantumDeterminants.Hpk, h, h']

private lemma Hpk_mul_apply_eq_Hpk_apply_of_lt_val (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r)
    (hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (Formalism.QuantumDeterminants.eI k r a) = if i = Formalism.QuantumDeterminants.eI k r a then 1 else 0)
    (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    ∀ c : ℕ, ∀ hc : c + q.val ≤ 2 * r + k,
      (Formalism.QuantumDeterminants.Hpk k r * g) ⟨c, by omega⟩ q = Formalism.QuantumDeterminants.Hpk k r ⟨c, by omega⟩ q := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    have hcr : c < r := by omega
    have hE : Formalism.QuantumDeterminants.eI k r ⟨c, hcr⟩ = ⟨c, by omega⟩ := Fin.ext rfl
    have h1 : (gᴴ * (Formalism.QuantumDeterminants.Hpk k r * g)) ⟨c, by omega⟩ q = Formalism.QuantumDeterminants.Hpk k r ⟨c, by omega⟩ q := by
      rw [← Matrix.mul_assoc, hU]
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨c, by omega⟩ : Fin (2 * r + k + 1))] at h1
    · have hd := hcol ⟨c, hcr⟩ ⟨c, by omega⟩ le_rfl
      rw [hE, if_pos rfl] at hd
      rw [Matrix.conjTranspose_apply, hd, star_one, one_mul] at h1
      exact h1
    · intro t _ htc
      rw [Matrix.conjTranspose_apply]
      have htc' : t.val ≠ c := fun h => htc (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne htc' with hlt | hgt
      · have h2 := ih t.val hlt (by omega)
        simp only [Fin.eta] at h2
        rw [h2, Hpk_apply_of_lt_eq_ite k r t q (by omega), if_neg (by omega), mul_zero]
      · have hz := hcol ⟨c, hcr⟩ t (by simp; omega)
        rw [hE, if_neg htc] at hz
        rw [hz, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem nset_block_unitriangular : ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ i j : Fin (2 * r + k + 1),
    lev k r j ≤ lev k r i → g i j = (1 : Mat k r) i j := by
  intro k r g hg i j hlev
  obtain ⟨hU, hcol, hmid⟩ := hg
  have hU' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hU
  rw [Matrix.one_apply]
  unfold GlobalTheory.CellDens.lev at hlev
  by_cases hj : j.val < r
  · have hij : j.val ≤ i.val := by split_ifs at hlev <;> omega
    have h := hcol ⟨j.val, hj⟩ i hij
    have he : Formalism.QuantumDeterminants.eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
    rw [he] at h
    exact h
  · by_cases hj2 : j.val ≤ r + k
    · have hi : r ≤ i.val := by split_ifs at hlev <;> omega
      exact hmid i j (by omega) hj2 hi
    · have hi : r + k < i.val ∧ j.val ≤ i.val := by split_ifs at hlev <;> omega
      have hC : 2 * r + k - i.val < r := by omega
      have h := Hpk_mul_apply_eq_Hpk_apply_of_lt_val k r g hU' hcol j (by omega) (2 * r + k - i.val) (by omega)
      rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
      · rw [Hpk_apply_of_lt_eq_ite k r _ i hC, if_pos (by simp; omega), one_mul] at h
        rw [h, Hpk_apply_of_lt_eq_ite k r _ j hC]
        by_cases hij : i = j
        · subst hij
          rw [if_pos (by simp; omega), if_pos rfl]
        · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
          rw [if_neg (by simp; omega), if_neg hij]
      · intro s _ hs
        have hv : s.val ≠ i.val := fun h => hs (Fin.ext h)
        rw [Hpk_apply_of_lt_eq_ite k r _ s hC, if_neg (by simp; omega), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ _) h'

end GlobalTheory.CellDens
end

section

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace GlobalTheory.TubeDeriv

section Jet

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Jet (f : E → ℂ) (a : ℂ) (d : E → ℂ) : Prop :=
  ∃ D : E →L[ℝ] ℂ, HasStrictFDerivAt f D 0 ∧ f 0 = a ∧ ∀ v, D v = d v

theorem Jet.congr {f g : E → ℂ} {a b : ℂ} {d e : E → ℂ} (h : Jet f a d) (h1 : ∀ x, g x = f x) (h2 : b = a)
    (h3 : ∀ v, e v = d v) : Jet g b e := by
  obtain ⟨D, hD, h0, hd⟩ := h
  have hg : g = f := funext h1
  subst hg
  exact ⟨D, hD, by rw [h0, h2], fun v => by rw [hd, h3]⟩

theorem Jet.const (a : ℂ) : Jet (fun _ : E => a) a (fun _ => 0) := ⟨0, hasStrictFDerivAt_const a 0, rfl, fun _ => rfl⟩

theorem Jet.clm (L : E →L[ℝ] ℂ) : Jet (fun x => L x) 0 (fun x => L x) := ⟨L, L.hasStrictFDerivAt, by simp, fun _ => rfl⟩

theorem Jet.sub {f g : E → ℂ} {a b : ℂ} {d e : E → ℂ} (h : Jet f a d) (h' : Jet g b e) :
    Jet (fun x => f x - g x) (a - b) (fun v => d v - e v) := by
  obtain ⟨D, hD, h0, hd⟩ := h
  obtain ⟨D', hD', h0', hd'⟩ := h'
  exact ⟨D - D', hD.sub hD', by simp [h0, h0'], fun v => by simp [hd, hd']⟩

theorem Jet.mul {f g : E → ℂ} {a b : ℂ} {d e : E → ℂ} (h : Jet f a d) (h' : Jet g b e) :
    Jet (fun x => f x * g x) (a * b) (fun v => a * e v + b * d v) := by
  obtain ⟨D, hD, h0, hd⟩ := h
  obtain ⟨D', hD', h0', hd'⟩ := h'
  refine ⟨_, hD.mul hD', by simp [h0, h0'], fun v => ?_⟩
  simp [h0, h0', hd, hd']

theorem Jet.sum {ι : Type} [Fintype ι] {f : ι → E → ℂ} {a : ι → ℂ} {d : ι → E → ℂ}
    (h : ∀ i, Jet (f i) (a i) (d i)) : Jet (fun x => ∑ i, f i x) (∑ i, a i) (fun v => ∑ i, d i v) := by
  choose D hD h0 hd using h
  exact ⟨∑ i, D i, HasStrictFDerivAt.fun_sum fun i _ => hD i, by simp [h0], fun v => by simp [hd]⟩

theorem Jet.conj {f : E → ℂ} {a : ℂ} {d : E → ℂ} (h : Jet f a d) :
    Jet (fun x => conj (f x)) (conj a) (fun v => conj (d v)) := by
  obtain ⟨D, hD, h0, hd⟩ := h
  exact ⟨_, hD.star, by simp [h0], fun v => by simp [hd]⟩

theorem Jet.comp_zero {f : E → ℂ} {a : ℂ} (h : Jet f a fun _ => 0) {g : ℂ → ℂ} (hg : ContDiffAt ℝ 1 g a) :
    Jet (fun x => g (f x)) (g a) (fun _ => 0) := by
  obtain ⟨D, hD, h0, hd⟩ := h
  have hg' : HasStrictFDerivAt g (fderiv ℝ g a) (f 0) := by
    rw [h0]
    exact hg.hasStrictFDerivAt_fderiv one_ne_zero
  exact ⟨_, hg'.comp 0 hD, by simp [h0], fun v => by simp [hd]⟩

theorem Jet.cexp {f : E → ℂ} {d : E → ℂ} (h : Jet f 0 d) : Jet (fun x => Complex.exp (f x)) 1 d := by
  obtain ⟨D, hD, h0, hd⟩ := h
  exact ⟨_, hD.cexp, by simp [h0], fun v => by simp [h0, hd]⟩

theorem Jet.matExp [FiniteDimensional ℝ E] {k : ℕ} (L : E →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ) (i j : Fin k) :
    Jet (fun x => NormedSpace.exp (L x) i j) ((1 : Matrix (Fin k) (Fin k) ℂ) i j) (fun v => L v i j) := by
  let _ : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix (Fin k) (Fin k) ℂ) := FiniteDimensional.complete ℝ _
  let Lc : E →L[ℝ] Matrix (Fin k) (Fin k) ℂ := LinearMap.toContinuousLinearMap L
  let P : Matrix (Fin k) (Fin k) ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Fin k → ℂ) i)
  have hE : HasStrictFDerivAt (fun x => NormedSpace.exp (Lc x))
      ((1 : Matrix (Fin k) (Fin k) ℂ →L[ℝ] Matrix (Fin k) (Fin k) ℂ).comp Lc) 0 := by
    have h0 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin k) (Fin k) ℂ → _)
        (1 : Matrix (Fin k) (Fin k) ℂ →L[ℝ] Matrix (Fin k) (Fin k) ℂ) (Lc 0) := by
      rw [map_zero]
      exact hasStrictFDerivAt_exp_zero
    exact h0.comp 0 Lc.hasStrictFDerivAt
  refine ⟨P.comp ((1 : Matrix (Fin k) (Fin k) ℂ →L[ℝ] Matrix (Fin k) (Fin k) ℂ).comp Lc),
    P.hasStrictFDerivAt.comp 0 hE, ?_, fun v => rfl⟩
  simp [NormedSpace.exp_zero]

theorem Jet.lin [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] ℂ) : Jet (fun x => L x) 0 (fun x => L x) := Jet.congr (Jet.clm (LinearMap.toContinuousLinearMap L)) (fun _ => rfl) rfl (fun _ => rfl)

end Jet

variable {k : ℕ}

def matL (k : ℕ) : Par k →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ where
  toFun x := unrealify (x.1 : EuclideanSpace ℝ _)
  map_add' x y := by
    ext i j
    apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by
    ext i j
    apply Complex.ext <;> simp [unrealify]

theorem jet_hv (j : Fin k) : Jet (fun x : Par k => hv x.2.2 j) 0 (fun x => hv x.2.2 j) := by
  have h := Jet.lin (E := Par k)
    { toFun := fun x : Par k => hv x.2.2 j
      map_add' := fun x y => by simp [hv, add_div]
      map_smul' := fun c x => by simp [hv]; ring }
  exact Jet.congr h (fun _ => rfl) rfl (fun _ => rfl)

theorem jet_angle : Jet (fun x : Par k => (x.2.1 : ℂ) * Complex.I) 0 (fun x => (x.2.1 : ℂ) * Complex.I) := by
  have h := Jet.lin (E := Par k)
    { toFun := fun x : Par k => (x.2.1 : ℂ) * Complex.I
      map_add' := fun x y => by simp only [Prod.snd_add, Prod.fst_add, Complex.ofReal_add]; ring
      map_smul' := fun c x => by simp [Complex.real_smul, mul_assoc] }
  exact Jet.congr h (fun _ => rfl) rfl (fun _ => rfl)

theorem jet_prod (i j : Fin k) : Jet (fun x : Par k => conj (hv x.2.2 i) * hv x.2.2 j) 0 (fun _ => 0) := Jet.congr ((jet_hv i).conj.mul (jet_hv j)) (fun _ => rfl) (by simp) (fun _ => by simp)

theorem jet_nsq : Jet (fun x : Par k => (nsq (hv x.2.2) : ℂ)) 0 (fun _ => 0) := by
  refine Jet.congr (Jet.sum fun j => jet_prod (k := k) j j) (fun x => ?_) (by simp) (fun _ => by simp)
  simp only [nsq]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_mul']

theorem contDiffAt_root (η : ℝ) : ContDiffAt ℝ 1 (fun z : ℂ => Real.sqrt (1 - η * z.re)) 0 := by
  have h1 : ContDiffAt ℝ 1 (fun z : ℂ => 1 - η * z.re) 0 :=
    contDiffAt_const.sub (contDiffAt_const.mul Complex.reCLM.contDiff.contDiffAt)
  exact h1.sqrt (by simp)

theorem jet_dd (η : ℝ) : Jet (fun x : Par k => (dd η (hv x.2.2) : ℂ)) 1 (fun _ => 0) := by
  have hg : ContDiffAt ℝ 1 (fun z : ℂ => ((Real.sqrt (1 - η * z.re) : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (0 : ℂ) (contDiffAt_root η)
  exact Jet.congr ((jet_nsq (k := k)).comp_zero hg) (fun x => by simp [dd]) (by simp) (fun _ => rfl)

theorem jet_coef (η : ℝ) :
    Jet (fun x : Par k => ((η / (1 + dd η (hv x.2.2)) : ℝ) : ℂ)) ((η / 2 : ℝ) : ℂ) (fun _ => 0) := by
  have h1 : ContDiffAt ℝ 1 (fun z : ℂ => η / (1 + Real.sqrt (1 - η * z.re))) 0 :=
    contDiffAt_const.div (contDiffAt_const.add (contDiffAt_root η)) (by norm_num)
  have hg : ContDiffAt ℝ 1 (fun z : ℂ => ((η / (1 + Real.sqrt (1 - η * z.re)) : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (0 : ℂ) h1
  exact Jet.congr ((jet_nsq (k := k)).comp_zero hg) (fun x => by simp [dd]) (by norm_num) (fun _ => rfl)

theorem jet_kap (i j : Fin (k + 1)) :
    Jet (fun x : Par k => kap (NormedSpace.exp (unrealify (x.1 : EuclideanSpace ℝ _)))
        (Complex.exp (x.2.1 * Complex.I)) i j) ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j)
      (fun x => kap (unrealify (x.1 : EuclideanSpace ℝ _)) (x.2.1 * Complex.I) i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      exact Jet.congr (Jet.cexp (jet_angle (k := k))) (fun x => by simp [kap, blk])
        (Matrix.one_apply_eq _) (fun v => by simp [kap, blk])
    | cast j =>
      exact Jet.congr (Jet.const 0) (fun x => by simp [kap, blk])
        (Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne') (fun v => by simp [kap, blk])
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      exact Jet.congr (Jet.const 0) (fun x => by simp [kap, blk])
        (Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne) (fun v => by simp [kap, blk])
    | cast j =>
      exact Jet.congr (Jet.matExp (matL k) i j) (fun x => by simp [kap, blk]; rfl)
        (by simp [Matrix.one_apply]) (fun v => by simp [kap, blk]; rfl)

theorem jet_sec (η : ℝ) (i j : Fin (k + 1)) :
    Jet (fun x : Par k => sec η (hv x.2.2) i j) ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j)
      (fun x => blk 0 (fun i => -(η : ℂ) * conj (hv x.2.2 i)) (hv x.2.2) 0 i j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      exact Jet.congr (jet_dd (k := k) η) (fun x => by simp [sec, blk])
        (Matrix.one_apply_eq _) (fun v => by simp [blk])
    | cast j =>
      exact Jet.congr (jet_hv j) (fun x => by simp [sec, blk])
        (Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne') (fun v => by simp [blk])
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      exact Jet.congr ((Jet.const (-(η : ℂ))).mul (jet_hv i).conj) (fun x => by simp [sec, blk])
        (by simp [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]) (fun v => by simp [blk])
    | cast j =>
      exact Jet.congr ((Jet.const ((1 : Matrix (Fin k) (Fin k) ℂ) i j)).sub ((jet_coef η).mul (jet_prod i j)))
        (fun x => by simp [sec, blk]) (by simp [Matrix.one_apply]) (fun v => by simp [blk])

theorem chart_hasStrictFDerivAt (k : ℕ) (η : ℝ) (i j : Fin (k + 1)) :
    ∃ D : Par k →L[ℝ] ℂ, HasStrictFDerivAt (fun x : Par k => chart η x i j) D 0 ∧ ∀ v, D v = tang η v i j := by
  have h : Jet (fun x : Par k => chart η x i j) (∑ l, (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i l * (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) l j)
      (fun v => tang η v i j) := by
    refine Jet.congr (Jet.sum fun l => (jet_kap (k := k) i l).mul (jet_sec η l j))
      (fun x => by unfold chart; rw [Matrix.mul_apply]) rfl (fun v => ?_)
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    unfold tang kap blk
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp
  obtain ⟨D, hD, -, hd⟩ := h
  exact ⟨D, hD, hd⟩

end GlobalTheory.TubeDeriv
end
end

section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.Dec

theorem projAbs_holds : ProjAbs := by
  intro G _ _ _ _ _ _ μ _ _ H _ _ _ σ hσ hσc d hd hS w hw hint
  have hcont : ∀ x y : H, Continuous fun g => ⟪y, σ g x⟫_ℂ := fun x y =>
    continuous_const.inner (hσc x)
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hm1 : ⟪w, σ 1 w⟫_ℂ = 1 := by
    rw [map_one, ContinuousLinearMap.one_apply, hww]
  obtain ⟨hsf, hinv⟩ := GlobalTheory.sigmaFinite_and_isInvInvariant_of_continuous_integrable G μ (fun g => ⟪w, σ g w⟫_ℂ) (hcont w w)
    (by show ⟪w, σ 1 w⟫_ℂ ≠ 0; rw [hm1]; exact one_ne_zero) hint
  have hpol := GlobalTheory.polarised_schur_relations G μ H σ d (fun x y => (hcont x y).aestronglyMeasurable) hS
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.matrixCoeff_idempotent_of_orthogonality G μ H σ d hd hσ (fun v w v' w' => (hpol v w v' w').2) w hw
  have hφ : Integrable (phG d σ w) μ := by
    have : Integrable (fun g => star ⟪w, σ g w⟫_ℂ) μ :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hint
    exact this.const_mul (d : ℂ)
  refine ⟨h1, h2, ?_⟩
  intro Hp _ _ _ π hπ hπc
  refine ⟨?_, ?_⟩
  · obtain ⟨P, -, hP⟩ := GlobalTheory.absOpInt G μ Hp π hπ hπc (phG d σ w) hφ
    exact ⟨P, hφ, hP⟩
  intro P hP
  obtain ⟨hsp, hPxP⟩ := GlobalTheory.integratedOperator_isStarProjection_and_sandwich G μ Hp π hπ hπc (phG d σ w) (fun x => ⟪w, σ x w⟫_ℂ) hφ h1 h2 hm1
    P hP.2
  have hfix : ∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), P v = v := by
    rintro _ ⟨u, rfl⟩
    have := congrArg (fun T : Hp →L[ℂ] Hp => T u) hsp.isIdempotentElem.eq
    simpa using this
  have hunit : ∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), ‖v‖ = 1 →
      (∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) ∧
      ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u) := by
    intro v hv hn
    have hPv := hfix v hv
    have hc : ∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ := by
      intro g
      have hvv : ⟪v, v⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hn]; simp
      have e1 : P (π g v) = ⟪w, σ g w⟫_ℂ • v := by
        have := congrArg (fun T : Hp →L[ℂ] Hp => T v) (hPxP g)
        simpa [hPv] using this
      have hadj : ContinuousLinearMap.adjoint P = P := by
        rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsp.isSelfAdjoint
      calc ⟪v, π g v⟫_ℂ = ⟪ContinuousLinearMap.adjoint P v, π g v⟫_ℂ := by rw [hadj, hPv]
        _ = ⟪v, P (π g v)⟫_ℂ := ContinuousLinearMap.adjoint_inner_left _ _ _
        _ = ⟪w, σ g w⟫_ℂ := by rw [e1, inner_smul_right, hvv, mul_one]
    exact ⟨hc, GlobalTheory.exists_isometric_intertwiner_of_matrixCoeff_eq G H σ Hp π hσ hπ w v h4 hc⟩
  refine ⟨hsp, hPxP, hunit, ?_⟩
  ext v
  constructor
  · intro hv
    by_cases h0 : v = 0
    · exact ⟨0, fun g => by simp, by simp [h0]⟩
    · have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hv' : ((‖v‖ : ℂ)⁻¹ • v) ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp) := Submodule.smul_mem _ _ hv
      obtain ⟨-, io, hio, hint'⟩ := hunit _ hv' (norm_smul_inv_norm h0)
      refine ⟨(‖v‖ : ℂ) • io.toContinuousLinearMap, fun g => ?_, ?_⟩
      · ext u
        simp [hint']
      · show v = (‖v‖ : ℂ) • io w
        rw [hio, smul_smul, mul_inv_cancel₀ hn, one_smul]
  · rintro ⟨io, hio, rfl⟩
    refine ⟨io w, ?_⟩
    show P (io w) = io w
    refine ext_inner_left ℂ fun x => ?_
    have e : ∀ g, ⟪x, π g (io w)⟫_ℂ = ⟪ContinuousLinearMap.adjoint io x, σ g w⟫_ℂ := by
      intro g
      rw [ContinuousLinearMap.adjoint_inner_left]
      have := congrArg (fun T : H →L[ℂ] Hp => T w) (hio g)
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this]
    rw [hP.2]
    simp only [e]
    have := h3 w (ContinuousLinearMap.adjoint io x)
    rw [hww, one_mul, ContinuousLinearMap.adjoint_inner_left] at this
    exact this

end GlobalTheory.Dec
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Deep

theorem ptBound_of_decGap : GlobalTheory.DSId.DecGap → GlobalTheory.Deep.PtBound := by
  intro hD B d p q h hDS hsig hgap hh
  obtain ⟨him, hre, hle, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hrk : ∀ v, rkR (B.I.ε v) = min p q := fun v => by
    rw [← (hsig v).1, ← (hsig v).2]; rfl
  have hw : ∀ v, ‖B.w v‖ = 1 := fun v => (hDS v).2.2.1.1
  have hdec := fun v (g : UJ (B.I.ε v)) =>
    hD B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) (hDS v).1 (hDS v).2.1 h (hgap v)
      (by rw [hrk v]; exact hh) (uMat g) g.2 (B.w v) (hDS v).2.2.1.2 (B.w v) (hDS v).2.2.1.2
  have hd : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hDS v).2.2.2.1.le
  have key : ∀ (y : B.I.GA) (c : InfinitePlace B.I.F → ℝ),
      (∀ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ c v) →
      ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re * ∏ v, c v := by
    intro y c hc
    have h1 : ∏ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ ∏ v, c v :=
      Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hc v
    have h0 : 0 ≤ ∏ v, c v := (Finset.prod_nonneg fun v _ => norm_nonneg _).trans h1
    unfold phe ph
    rw [norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hd, mul_right_comm]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hle _) hd) h1
      (Finset.prod_nonneg fun v _ => norm_nonneg _) (mul_nonneg hd hre)
  refine ⟨fun _ y => key y _ fun v => ?_, fun y => ?_, ?_, him, hre, fun y hy => ?_, fun v g => ?_⟩
  · have := (hdec v (y.1 v)).1
    rw [hw, mul_one, mul_one, hrk] at this
    exact this
  · have := key y (fun _ => 1) fun v => by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [(hDS v).2.1.2.2.1.2.1 _ (y.1 v).2, hw, mul_one]
    simpa using this
  · have h1 : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.GA).1 v)) (B.w v)⟫_ℂ = 1 := fun v => by
      have e : uMat ((1 : B.I.GA).1 v) = 1 := rfl
      rw [e, (hDS v).2.1.2.2.1.1.1]
      simp [inner_self_eq_norm_sq_to_K, hw]
    unfold phe ph
    simp only [h1, Finset.prod_const_one, star_one, mul_one]
    rfl
  · exact B.e_adm.2.2.2.2.1 _ (right_ne_zero_of_mul hy)
  · have := (hdec v g).2
    rwa [hw, mul_one, mul_one] at this

end GlobalTheory.Deep
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory

theorem upqRep_vocabulary_agree : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : B.Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), (Formalism.MainNotions.S.IsDSHpk k r ε lam σ ↔ PI.UpqRep.IsDSHpk k r ε lam σ) ∧ (∀ v, Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ v ↔ PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) ∧ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ = PI.UpqRep.smoothVecs (k := k) (r := r) σ ∧ (Formalism.QuantumDeterminants.IsHCParam lam ↔ PI.UpqRep.IsHCParam lam) ∧ (∀ P, Formalism.MainNotions.S.IsCayleyU k r ε P ↔ PI.UpqRep.IsCayleyU k r ε P) ∧ Formalism.MainNotions.S.lowKSub ε lam σ = PI.UpqRep.lowKSub ε lam σ := by
  intro k r H _ _ _ σ ε lam
  exact ⟨Iff.rfl, fun _ => Iff.rfl, rfl, Iff.rfl, fun _ => Iff.rfl, rfl⟩

end GlobalTheory
end
