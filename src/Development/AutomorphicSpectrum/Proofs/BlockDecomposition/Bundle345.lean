module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Mathlib.Data.Fin.Tuple.Basic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InstBorelUK
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BetaWeightOfTorusFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicFunctionFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KeyPropositionOfComponents
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeAlgebraFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferStatement
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle322
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.Zcore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAdmissible_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) : IsAdmissible x.rep := by
  exact hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr

theorem isIrreducible_contra_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    (contra x.rep).IsIrreducible := by
  exact GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (isAdmissible_rep hA x) x.2.rep.irr

theorem dualCl_eq_of (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    dualCl x = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) (isIrreducible_contra_rep hA x) := by
  unfold dualCl
  rw [dite_eq_left (isIrreducible_contra_rep hA x)]

private theorem dualCl_eq_of_eq_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x y : IrrGL (k := k))
    (hy : y = IrrGL.of (contra x.rep) (isSmooth_smoothRep _) (isIrreducible_contra_rep hA x)) :
    dualCl y = x := by
  subst hy
  rw [dualCl_eq_of hA]
  conv_rhs => rw [← IrrGL.of_rep x]
  exact IrrGL.of_eq_of.mpr ⟨(GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf (contra x.rep) _ _)).trans
    (GlobalTheory.ContraRefl.evEquiv (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (isAdmissible_rep hA x)).symm⟩

theorem dualCl_dualCl : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)),
    dualCl (dualCl x) = x := by
  intro k _ _ _ _ hA x
  exact dualCl_eq_of_eq_contra hA x _ (dualCl_eq_of hA x)

end GlobalTheory.CompanionTheory.Zcore

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd

namespace GlobalTheory.CompanionTheory.WordProd.Intl

def consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin (m + 1) ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono
    (Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ)) (by
      intro a b hab
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => exact absurd hab (lt_irrefl _)
        | succ b => simp [Fin.succ_pos]
      | succ a =>
        induction b using Fin.cases with
        | zero => exact absurd hab (Fin.not_lt_zero _)
        | succ b => simpa using hab)

def shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) : Fin m ↪o Fin (k + 1) :=
  OrderEmbedding.ofStrictMono (fun a => (σ a).succ) (fun a b h => by simpa using h)

@[simp] theorem consEmb_zero {m k : ℕ} (σ : Fin m ↪o Fin k) : consEmb σ 0 = 0 := by
  first
    | rfl
    | exact Fin.cons_zero (α := fun _ => Fin (k + 1)) _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) 0 = 0; simp)

@[simp] theorem consEmb_succ {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    consEmb σ a.succ = (σ a).succ := by
  first
    | rfl
    | exact Fin.cons_succ (α := fun _ => Fin (k + 1)) _ _ _
    | (show Fin.cons (α := fun _ => Fin (k + 1)) 0 (fun a => (σ a).succ) a.succ = (σ a).succ; simp)

@[simp] theorem shiftEmb_apply {m k : ℕ} (σ : Fin m ↪o Fin k) (a : Fin m) :
    shiftEmb σ a = (σ a).succ := rfl

theorem zero_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) :
    (0 : Fin (k + 1)) ∈ Set.range (consEmb σ) := ⟨0, consEmb_zero σ⟩

theorem succ_mem_range_consEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (consEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    cases a using Fin.cases with
    | zero =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero] at ha
      exact absurd ha.symm (Fin.succ_ne_zero j)
    | succ a =>
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ] at ha
      exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.succ, GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ σ a⟩

theorem succ_mem_range_shiftEmb {m k : ℕ} (σ : Fin m ↪o Fin k) (j : Fin k) :
    j.succ ∈ Set.range (shiftEmb σ) ↔ j ∈ Set.range σ := by
  constructor
  · rintro ⟨a, ha⟩
    rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at ha
    exact ⟨a, Fin.succ_injective _ ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply σ a⟩

theorem interleave_embeddings : ∀ {T : Type 1} {u v w : List T}, Zc.Comb.Interleave u v w →
    ∃ (r : Fin w.length → Fin 2) (σ₀ : Fin u.length ↪o Fin w.length)
      (σ₁ : Fin v.length ↪o Fin w.length),
      (∀ j, r j = 0 ↔ j ∈ Set.range σ₀) ∧ (∀ j, r j = 1 ↔ j ∈ Set.range σ₁) ∧
      (∀ a, w.get (σ₀ a) = u.get a) ∧ (∀ a, w.get (σ₁ a) = v.get a) := by
  intro T u v w h
  induction h with
  | nil =>
    refine ⟨fun j => Fin.elim0 j, (OrderIso.refl _).toOrderEmbedding,
      (OrderIso.refl _).toOrderEmbedding, ?_, ?_, ?_, ?_⟩ <;> intro j <;> exact Fin.elim0 j
  | @left a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (0 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₀
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h1 j
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := u.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hu x
          | simpa using hu x
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hv x
        | simpa using hv x
  | @right a u v w _ ih =>
    obtain ⟨r, σ₀, σ₁, h0, h1, hu, hv⟩ := ih
    refine ⟨(Fin.cons (1 : Fin 2) r : Fin (w.length + 1) → Fin 2), GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb σ₀,
      GlobalTheory.CompanionTheory.WordProd.Intl.consEmb σ₁, ?_, ?_, ?_, ?_⟩
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero]
        constructor
        · intro hc
          exact absurd hc (by decide)
        · rintro ⟨x, hx⟩
          rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply] at hx
          exact absurd hx (Fin.succ_ne_zero _)
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_shiftEmb]
        exact h0 j
    · intro j
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ (n := w.length) j
      · simp only [Fin.cons_zero, true_iff]
        exact GlobalTheory.CompanionTheory.WordProd.Intl.zero_mem_range_consEmb σ₁
      · rw [Fin.cons_succ, GlobalTheory.CompanionTheory.WordProd.Intl.succ_mem_range_consEmb]
        exact h1 j
    · intro x
      rw [GlobalTheory.CompanionTheory.WordProd.Intl.shiftEmb_apply]
      first
        | exact hu x
        | simpa using hu x
    · intro x
      obtain rfl | ⟨x, rfl⟩ := Fin.eq_zero_or_eq_succ (n := v.length) x
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_zero]
        simp
      · rw [GlobalTheory.CompanionTheory.WordProd.Intl.consEmb_succ]
        first
          | exact hv x
          | simpa using hv x

end GlobalTheory.CompanionTheory.WordProd.Intl
end

section

noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def XA (lam : Fin n → ℤ) (B : Mat n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  fun i j => fderiv ℂ (fun x : Mat n => Rm lam x i j) 1 B

def Xu (lam : Fin n → ℤ) (a b : Fin n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  XA lam (Matrix.single a b 1)

def HolRm (lam : Fin n → ℤ) : Prop :=
  ∀ (i j : Jd n lam), ∀ g ∈ GLs n, DifferentiableAt ℂ (fun x : Mat n => Rm lam x i j) g

theorem XA_add (lam : Fin n → ℤ) (B B' : Mat n) : XA lam (B + B') = XA lam B + XA lam B' := by
  ext i j; simp [XA]

theorem XA_smul (lam : Fin n → ℤ) (c : ℂ) (B : Mat n) : XA lam (c • B) = c • XA lam B := by
  ext i j; simp [XA]

theorem XA_sum (lam : Fin n → ℤ) {ι : Type} (s : Finset ι) (B : ι → Mat n) :
    XA lam (∑ r ∈ s, B r) = ∑ r ∈ s, XA lam (B r) := by
  ext i j; simp [XA, Matrix.sum_apply]

theorem Rm_of_unit (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) :
    Rm lam x = LinearMap.toMatrix (wb lam) (wb lam) (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h)) := by
  rw [Rm, dite_eq_left h]

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : Mat n) = 1 := by
  have h : IsUnit (1 : Mat n).det := by simp
  rw [Rm_of_unit lam h]
  have e : Matrix.nonsingInvUnit (1 : Mat n) h = 1 := Units.ext rfl
  rw [e, map_one]
  exact LinearMap.toMatrix_one _

theorem Rm_mul (lam : Fin n → ℤ) {x y : Mat n} (hx : IsUnit x.det) (hy : IsUnit y.det) :
    Rm lam (x * y) = Rm lam x * Rm lam y := by
  have h : IsUnit (x * y).det := by rw [Matrix.det_mul]; exact hx.mul hy
  rw [Rm_of_unit lam h, Rm_of_unit lam hx, Rm_of_unit lam hy]
  have e : Matrix.nonsingInvUnit (x * y) h = Matrix.nonsingInvUnit x hx * Matrix.nonsingInvUnit y hy := Units.ext rfl
  rw [e, map_mul]
  exact LinearMap.toMatrix_mul _ _ _

theorem isUnit_det_of_mem {g : Mat n} (hg : g ∈ GLs n) : IsUnit g.det := isUnit_iff_ne_zero.2 hg

theorem mem_GLs_of_isUnit {g : Mat n} (hg : IsUnit g.det) : g ∈ GLs n := hg.ne_zero

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by simp [GLs]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne_fun this continuous_const

theorem hasDerivAt_line {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (i j : Jd n lam) :
    HasDerivAt (fun t : ℂ => Rm lam (1 + t • B) i j) (XA lam B i j) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => (1 : Mat n) + t • B) B 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const B).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have h2 := (hD i j 1 one_mem_GLs).hasFDerivAt
  exact h2.comp_hasDerivAt_of_eq (0 : ℂ) h1 (by simp)

theorem eventually_line_unit (B : Mat n) : ∀ᶠ t : ℂ in 𝓝 0, IsUnit ((1 : Mat n) + t • B).det := by
  have hc : Continuous fun t : ℂ => (1 : Mat n) + t • B := continuous_const.add (continuous_id.smul continuous_const)
  have : ∀ᶠ t : ℂ in 𝓝 0, (1 : Mat n) + t • B ∈ GLs n :=
    hc.continuousAt.eventually_mem (isOpen_GLs.mem_nhds (by simpa using one_mem_GLs))
  exact this.mono fun t ht => isUnit_det_of_mem ht

theorem conj_XA {lam : Fin n → ℤ} (hD : HolRm lam) {x B B' : Mat n} (hx : IsUnit x.det) (h : x * B = B' * x) :
    Rm lam x * XA lam B = XA lam B' * Rm lam x := by
  ext i j
  have hev : ∀ᶠ t : ℂ in 𝓝 0, ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j = ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j := by
    filter_upwards [eventually_line_unit B, eventually_line_unit B'] with t h1 h2
    have e : x * (1 + t • B) = (1 + t • B') * x := by
      simp only [mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, h]
    have := Rm_mul lam hx h1
    rw [e, Rm_mul lam h2 hx] at this
    have := congrFun (congrFun this i) j
    simpa [Matrix.mul_apply] using this.symm
  have hL : HasDerivAt (fun t : ℂ => ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam x i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hR : HasDerivAt (fun t : ℂ => ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j)
      (∑ k, XA lam B' i k * Rm lam x k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B' i k).mul_const _
  simpa [Matrix.mul_apply] using (hL.congr_of_eventuallyEq (hev.mono fun t ht => ht.symm)).unique hR |>.symm ▸ rfl

theorem fderiv_Rm {lam : Fin n → ℤ} (hD : HolRm lam) {g : Mat n} (hg : g ∈ GLs n) (B : Mat n) (i j : Jd n lam) :
    fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B) = (Rm lam g * XA lam B) i j := by
  have hu := isUnit_det_of_mem hg
  have hline : HasDerivAt (fun t : ℂ => g + t • (g * B)) (g * B) 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const (g * B)).const_add g
    rw [one_smul] at h
    exact h
  have h1 : HasDerivAt (fun t : ℂ => Rm lam (g + t • (g * B)) i j)
      (fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B)) 0 :=
    (hD i j g hg).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  have h2 : HasDerivAt (fun t : ℂ => ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam g i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hev : ∀ᶠ t : ℂ in 𝓝 0, Rm lam (g + t • (g * B)) i j = ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j := by
    filter_upwards [eventually_line_unit B] with t ht
    have e : g + t • (g * B) = g * (1 + t • B) := by
      simp only [mul_add, mul_one, Matrix.mul_smul]
    rw [e, Rm_mul lam hu ht, Matrix.mul_apply]
  simpa [Matrix.mul_apply] using h1.unique (h2.congr_of_eventuallyEq hev)

end GlobalTheory.CompanionTheory.RmHol
end
end

section


theorem _root_.GlobalTheory.T.beta_weight_of_torus_facts : PositivityTheory.RgDs.K.HolFacts → PositivityTheory.RgDs.K.RhoTorus → PositivityTheory.RgDs.K.TorW → PositivityTheory.RgDs.K.BetaWeight := by
  first | exact @GlobalTheory.CompanionTheory.TorusSymbol.betaWeight | exact GlobalTheory.CompanionTheory.TorusSymbol.betaWeight | (intros; apply GlobalTheory.CompanionTheory.TorusSymbol.betaWeight <;> assumption)
end

section


theorem _root_.GlobalTheory.T.compact_exhaustion_statement : PositivityTheory.RgDs.K.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.WordFam.exhaust | exact GlobalTheory.CompanionTheory.WordFam.exhaust | (intros; apply GlobalTheory.CompanionTheory.WordFam.exhaust <;> assumption)
end

section


theorem _root_.GlobalTheory.T.torus_restriction_representation : PositivityTheory.RgDs.K.RhoTorus := by
  first | exact @GlobalTheory.CompanionTheory.RgTorus.rhoTorus | exact GlobalTheory.CompanionTheory.RgTorus.rhoTorus | (intros; apply GlobalTheory.CompanionTheory.RgTorus.rhoTorus <;> assumption)
end

section


theorem _root_.GlobalTheory.T.torus_weight_decomposition : PositivityTheory.RgDs.K.TorW := by
  first | exact @GlobalTheory.CompanionTheory.RgDsTor.torW | exact GlobalTheory.CompanionTheory.RgDsTor.torW | (intros; apply GlobalTheory.CompanionTheory.RgDsTor.torW <;> assumption)
end

section


theorem _root_.GlobalTheory.T.holomorphic_function_facts : PositivityTheory.RgDs.K.HolFacts := by
  first | exact @GlobalTheory.CompanionTheory.HolOm.holFacts | exact GlobalTheory.CompanionTheory.HolOm.holFacts | (intros; apply GlobalTheory.CompanionTheory.HolOm.holFacts <;> assumption)
end

section


theorem _root_.GlobalTheory.T.key_proposition_of_components : PositivityTheory.RgDs.K.LowAlg → PositivityTheory.RgDs.K.HolFacts → PositivityTheory.RgDs.K.EquivSection → PositivityTheory.RgDs.K.RhoRep → PositivityTheory.RgDs.K.ActEquiv → PositivityTheory.RgDs.K.RhoTorus → PositivityTheory.RgDs.K.TorW → PositivityTheory.RgDs.K.Transfer → PositivityTheory.RgDs.K.Exhaust → PositivityTheory.RgDs.K.BetaWeight → PositivityTheory.RgDs.Key := by
  first | exact @GlobalTheory.CompanionTheory.KeyAsm.key_of_steps | exact GlobalTheory.CompanionTheory.KeyAsm.key_of_steps | (intros; apply GlobalTheory.CompanionTheory.KeyAsm.key_of_steps <;> assumption)
end

section


theorem _root_.GlobalTheory.T.low_degree_algebra_facts : PositivityTheory.RgDs.K.LowAlg := by
  first | exact @GlobalTheory.CompanionTheory.GlLowest.lowAlg | exact GlobalTheory.CompanionTheory.GlLowest.lowAlg | (intros; apply GlobalTheory.CompanionTheory.GlLowest.lowAlg <;> assumption)
end

section


theorem _root_.GlobalTheory.T.transfer_statement : PositivityTheory.RgDs.K.Transfer := by
  first | exact @GlobalTheory.CompanionTheory.RgKeyTransfer.transfer | exact GlobalTheory.CompanionTheory.RgKeyTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.RgKeyTransfer.transfer <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unlinked_layers_hold : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], UnlinkedLayers k := by
  first | exact @GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | exact GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers | (intros; apply GlobalTheory.CompanionTheory.SegLayers.unlinkedLayers <;> assumption)
end
