module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle475
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle463
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.SpinRel

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def quadM (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b

theorem term_comm {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g e : Fin n) :
    c a e * c e b * c d g - c d g * (c a e * c e b) =
      (if b = d then (if e = g then (2 : ℂ) • c a g else 0) else 0) -
        (if a = g then (if e = d then (2 : ℂ) • c d b else 0) else 0) := by
  have h1 := hc.1 e b d g
  have h2 := hc.1 a e d g
  have h : c a e * c e b * c d g - c d g * (c a e * c e b) =
      c a e * (c e b * c d g + c d g * c e b) - (c a e * c d g + c d g * c a e) * c e b := by
    noncomm_ring
  rw [h, h1, h2]
  by_cases hbd : b = d <;> by_cases heg : e = g <;> by_cases hag : a = g <;> by_cases hed : e = d <;>
    simp only [hbd, heg, hag, hed, and_self, and_true, and_false, true_and, false_and, if_true, if_false,
      mul_zero, zero_mul, sub_zero, two_smul, mul_two, two_mul] <;> simp_all [two_smul, mul_two, two_mul]

theorem quad_c {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g : Fin n) :
    quadM c a b * c d g - c d g * quadM c a b =
      (if b = d then c a g else 0) - (if a = g then c d b else 0) := by
  have h : quadM c a b * c d g - c d g * quadM c a b =
      (1 / 2 : ℂ) • ∑ e, (c a e * c e b * c d g - c d g * (c a e * c e b)) := by
    simp only [quadM, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h]
  simp only [term_comm hc, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hag : a = g <;>
    simp [hbd, hag, smul_sub, smul_smul]

theorem quad_quad {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d e : Fin n) :
    quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (if b = d then quadM c a e else 0) - (if e = a then quadM c d b else 0) := by
  have h : ∀ f, quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b =
      ((if b = d then c a f else 0) - (if a = f then c d b else 0)) * c f e +
        c d f * ((if b = f then c a e else 0) - (if a = e then c f b else 0)) := by
    intro f
    rw [← quad_c hc a b d f, ← quad_c hc a b f e]
    noncomm_ring
  have h2 : quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (1 / 2 : ℂ) • ∑ f, (quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b) := by
    conv_lhs => rw [show quadM c d e = (1 / 2 : ℂ) • ∑ f, c d f * c f e from rfl]
    simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h2]
  simp only [h, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hae : a = e
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel

theorem spinM_eq (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    spinM c a b = quadM c a b - (if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0) := rfl

theorem spin_glRel {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) : Formalism.REAL.GlRel (spinM c) := by
  intro a b d e
  have h := quad_quad hc a b d e
  have hcomm : spinM c a b * spinM c d e - spinM c d e * spinM c a b =
      quadM c a b * quadM c d e - quadM c d e * quadM c a b := by
    simp only [spinM_eq]
    by_cases hab : a = b <;> by_cases hde : d = e <;>
      simp only [hab, hde, if_true, if_false, sub_zero, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one] <;> module
  rw [hcomm, h]
  by_cases hbd : b = d
  · by_cases hea : e = a
    · subst hbd
      subst hea
      simp [spinM_eq]
    · have hae : ¬ a = e := fun h => hea h.symm
      subst hbd
      simp [spinM_eq, hea, hae]
  · by_cases hea : e = a
    · have hdb : ¬ d = b := fun h => hbd h.symm
      simp [spinM_eq, hbd, hea, hdb]
    · simp [hbd, hea]

theorem spin_conjTranspose {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b : Fin n) :
    (spinM c a b)ᴴ = spinM c b a := by
  simp only [spinM_eq, quadM]
  by_cases hab : a = b
  · subst hab
    simp [conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul, Complex.conj_ofNat]
  · simp [hab, Ne.symm hab, conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul]

theorem spinRel : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a :=
  fun _ hc => ⟨spin_glRel hc, spin_conjTranspose hc⟩

end GlobalTheory.CompanionTheory.RealCount.SpinRel
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiracK

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]

def lft (ι : Type) [Fintype ι] [DecidableEq ι] : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun T :=
    { toFun := fun x i => T (x i)
      map_add' := fun x y => by funext i; simp
      map_smul' := fun s x => by funext i; simp }
  map_one' := by ext x i; simp
  map_mul' S T := by ext x i; simp
  map_zero' := by ext x i; simp
  map_add' S T := by ext x i; simp
  commutes' s := by ext x i; simp [Module.algebraMap_end_apply]

def rgt (V : Type) [AddCommGroup V] [Module ℂ V] : Matrix ι ι ℂ →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun M :=
    { toFun := fun x i => ∑ j, M i j • x j
      map_add' := fun x y => by funext i; simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun s x => by
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }
  map_one' := by
    ext x i
    simp [Matrix.one_apply]
  map_mul' M N := by
    apply LinearMap.ext
    intro x
    funext i
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
      smul_smul]
    exact Finset.sum_comm
  map_zero' := by ext x i; simp
  map_add' M N := by
    apply LinearMap.ext
    intro x
    funext i
    simp [add_smul, Finset.sum_add_distrib]
  commutes' s := by
    apply LinearMap.ext
    intro x
    funext i
    simp [Module.algebraMap_end_apply, Matrix.algebraMap_matrix_apply, ite_smul]

theorem lft_apply (T : Module.End ℂ V) (x : ι → V) (i : ι) : lft ι T x i = T (x i) := rfl

theorem rgt_apply (M : Matrix ι ι ℂ) (x : ι → V) (i : ι) : rgt V M x i = ∑ j, M i j • x j := rfl

theorem lft_mul_rgt (T : Module.End ℂ V) (M : Matrix ι ι ℂ) : lft ι T * rgt V M = rgt V M * lft ι T := by
  apply LinearMap.ext
  intro x
  funext i

  simp [lft_apply, rgt_apply, map_sum]

theorem yF_eq (Kf : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    yF Kf c a b = lft ι (Kf a b) + rgt V (spinM c a b) := rfl

def dirac (P : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) : Module.End ℂ (ι → V) :=
  ∑ a, ∑ b, lft ι (P a b) * rgt V (c b a)

end GlobalTheory.CompanionTheory.DiracK
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.Tope

variable {n : ℕ}

abbrev TorPt (n : ℕ) := {z : Fin n → ℂ // ∀ a, ‖z a‖ = 1}

def diagU (z : TorPt n) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨diagonal z.1, by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, z.2 a]
    simp⟩

def dualAct (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) : Module.End ℂ (E.V →L[ℂ] ℂ) where
  toFun ξ := ξ ∘L E.ρ k⁻¹
  map_add' x y := ContinuousLinearMap.add_comp _ _ _
  map_smul' c x := ContinuousLinearMap.smul_comp _ _ _

theorem diagU_comm (z w : TorPt n) : diagU z * diagU w = diagU w * diagU z := by
  apply Subtype.ext
  show diagonal z.1 * diagonal w.1 = diagonal w.1 * diagonal z.1
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

theorem dualAct_comm (E : KMod n) (z w : TorPt n) : Commute (dualAct E (diagU z)) (dualAct E (diagU w)) := by
  apply LinearMap.ext
  intro ξ
  show (ξ ∘L E.ρ (diagU w)⁻¹) ∘L E.ρ (diagU z)⁻¹ = (ξ ∘L E.ρ (diagU z)⁻¹) ∘L E.ρ (diagU w)⁻¹
  rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
  congr 1
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul, ← map_mul, ← _root_.mul_inv_rev,
    ← _root_.mul_inv_rev, diagU_comm]

def torChar (μ : Fin n → ℤ) (z : TorPt n) : ℂ := ∏ a, z.1 a ^ μ a

theorem torChar_injective : Function.Injective (torChar (n := n)) := by
  intro μ ν h
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := Function.ne_iff.1 hne
  have hd : (μ a - ν a : ℤ) ≠ 0 := sub_ne_zero.2 ha
  set w : ℂ := Complex.exp (((Real.pi / ((μ a - ν a : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) with hw
  have hw1 : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  let z : TorPt n := ⟨fun b => if b = a then w else 1, fun b => by by_cases hb : b = a <;> simp [hb, hw1]⟩
  have hval : ∀ m : Fin n → ℤ, torChar m z = w ^ m a := by
    intro m
    unfold torChar
    rw [Fintype.prod_eq_single a (fun b hb => by simp [z, hb])]
    simp [z]
  have h1 := congrFun h z
  rw [hval, hval] at h1
  have h2 : w ^ (μ a - ν a) = 1 := by
    rw [zpow_sub₀ hw0, h1, div_self (zpow_ne_zero _ hw0)]
  have h3 : w ^ (μ a - ν a) = -1 := by
    rw [hw, ← Complex.exp_int_mul]
    have hd' : ((μ a - ν a : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 hd
    have : (((μ a - ν a : ℤ)) : ℂ) * (((Real.pi / ((μ a - ν a : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) =
        (Real.pi : ℂ) * Complex.I := by
      push_cast at hd' ⊢
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  rw [h3] at h2
  norm_num at h2

theorem wtDual_le_joint (E : KMod n) (μ : Fin n → ℤ) :
    wtDual E μ ≤ ⨅ z : TorPt n, (dualAct E (diagU z)).maxGenEigenspace (torChar μ z) := by
  intro ξ hξ
  refine (Submodule.mem_iInf _).2 fun z => ?_
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  exact hξ (diagU z) z.1 rfl

theorem wtDual_iSupIndep : ∀ {n : ℕ} (E : KMod n), iSupIndep (wtDual E) := by
  intro n E
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun z : TorPt n => dualAct E (diagU z))
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (dualAct_comm E j i) φ)
  exact (hind.comp torChar_injective).mono fun μ => wtDual_le_joint E μ

end GlobalTheory.CompanionTheory.RealCount.Tope
end
end

section

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

def SmF (n : ℕ) : Submodule ℂ (Mat n → ℂ) where
  carrier := {h | ContDiffOn ℝ ∞ h (GLs n) ∧ ∀ g, g ∉ GLs n → h g = 0}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g hg => by simp [ha.2 g hg, hb.2 g hg]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' c a ha := ⟨contDiffOn_const.smul ha.1, fun g hg => by simp [ha.2 g hg]⟩

theorem indicator_Rd_mem (X : Mat n) (h : SmF n) : (GLs n).indicator (Rd X h.1) ∈ SmF n := by
  refine ⟨(GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X h.2.1).congr fun g hg => Set.indicator_of_mem hg _,
    fun g hg => Set.indicator_of_notMem hg _⟩

def DR (X : Mat n) : Module.End ℂ (SmF n) where
  toFun h := ⟨(GLs n).indicator (Rd X h.1), indicator_Rd_mem X h⟩
  map_add' a b := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      have db := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth b.2.1 hg
      simp only [Submodule.coe_add, Pi.add_apply, Set.indicator_of_mem hg, Rd]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_add_apply' da db _
    · simp [Set.indicator_of_notMem hg]
  map_smul' c a := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      simp only [Submodule.coe_smul, Pi.smul_apply, Set.indicator_of_mem hg, Rd, RingHom.id_apply, smul_eq_mul]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply da c _
    · simp [Set.indicator_of_notMem hg]

def Kf (a b : Fin n) : Module.End ℂ (SmF n) := e1 DR a b + e2 DR a b

def ev1 : SmF n →ₗ[ℂ] ℂ where
  toFun h := h.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Pb (lev : Fin n → ℕ) : Set (Mat n) := {p | p ∈ GLs n ∧ ∀ a b, lev a < lev b → p a b = 0}

def Eqv (lev : Fin n → ℕ) (φ : Mat n → ℂ) : Submodule ℂ (SmF n) where
  carrier := {h | ∀ p ∈ Pb lev, ∀ g ∈ GLs n, h.1 (p * g) = φ p * h.1 g}
  add_mem' {a b} ha hb p hp g hg := by
    simp only [Submodule.coe_add, Pi.add_apply, ha p hp g hg, hb p hp g hg, mul_add]
  zero_mem' p _ g _ := by simp
  smul_mem' c a ha p hp g hg := by
    simp only [Submodule.coe_smul, Pi.smul_apply, ha p hp g hg, smul_eq_mul]
    ring

def muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a =>
  2 * lam a + ((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ)

def yZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a => lam a - muZ lam lev a

def dif (v : Fin n → ℤ) (j : Fin n) : ℤ := v j - if h : (j : ℕ) + 1 < n then v ⟨j + 1, h⟩ else 0

def ini (j : Fin n) : Fin (j + 1) → Fin n := Fin.castLE j.isLt

def lm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) (ini j)).det

def gm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ).det

def fRaw (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Mat n → ℂ :=
  (GLs n).indicator fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j

def cyc (f : SmF n) : Submodule ℂ (SmF n) :=
  (Algebra.adjoin ℂ {T : Module.End ℂ (SmF n) | ∃ a b, T = e1 DR a b ∨ T = e2 DR a b}).toSubmodule.map
    (LinearMap.applyₗ f)

theorem unit_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n :=
  (Matrix.UnitaryGroup.det_isUnit k).ne_zero

theorem DR_apply (X : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (DR X h).1 g = Rd X h.1 g :=
  Set.indicator_of_mem hg _

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (e1 DR a b h).1 g = Eu true a b h.1 g := by
  simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, DR_apply _ _ hg, Eu, Pi.add_apply, if_true, smul_eq_mul]
  ring

theorem liftOneFormsToCompatible_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (f1 DR a b h).1 g = Eu false a b h.1 g := by
  simp [f1, DR_apply _ _ hg, Eu]
  ring

section K

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]

def ipK (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) (x y : SmF n) : ℂ := ∫ k, conj (x.1 k.1) * y.1 k.1 ∂κ

end K

end GlobalTheory.CompanionTheory.ModelS
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem _root_.GlobalTheory.T.dehomogenized_eval_eq_ratio : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    ∀ (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder w z → w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) →
    ev (mpStr ℤ m n) σ₀ (mchart c) (dehomog c f) w =
      eval z (map (Int.castRingHom ℂ) f) / ∏ k, z ⟨k, c k⟩ ^ a k := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ev_dehomog_of_isUnder | exact GlobalTheory.CompanionTheory.MixZ.ev_dehomog_of_isUnder | (intros; apply GlobalTheory.CompanionTheory.MixZ.ev_dehomog_of_isUnder <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem _root_.GlobalTheory.T.restricted_form_nonzero_on_generic_point : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    f ∉ ptIdeal (i (genericPoint X)) → fnAt i c h f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal | exact GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal | (intros; apply GlobalTheory.CompanionTheory.MixZ.FnForm.fnAt_ne_zero_of_notMem_ptIdeal <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.finite_adelic_lattice_open_compact : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)), (∀ w ∈ S, IsOpen (B w : Set (w.adicCompletion E))) → (∀ w ∈ S, (B w : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E))) → IsOpen (latS S B : Set (Af E)) ∧ IsCompact (latS S B : Set (Af E)) := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact | exact GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact <;> assumption)
end
