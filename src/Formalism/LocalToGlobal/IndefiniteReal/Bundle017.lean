module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hanti, Q, hQ, rfl⟩, ⟨_, hint⟩, hp, hq⟩ := h
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a),
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a), fun a => by simp [hQ], ?_⟩,
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩, ?_, ?_⟩
  · unfold dualPar
    rw [Finset.image_image]
    ext ⟨x, s⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.rev a, by simpa using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨_, ha⟩
  · obtain ⟨z, hz⟩ := hint (Fin.rev a)
    refine ⟨-z - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)

theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) : StrictAnti fun a : Fin R.r => lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have := lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at this
  have h1 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith

def sgA (R : Ranks) (a : ℕ) : Bool := decide (a < R.k - 1 ∨ Even (a - (R.k - 1)))

theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin R.r => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := hpq ▸ odd_r R
  ext ⟨x, s⟩
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    cases a with
    | inl i => exact ⟨⟨i, by have := i.2; omega⟩, rfl, by simp⟩
    | inr c => exact ⟨⟨p + c, by have := c.2; omega⟩, rfl, by simp⟩
  · rintro ⟨a, rfl, rfl⟩
    by_cases hc : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hc⟩, rfl, by simp [hc]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_, by simp [hc]⟩
      simp only [Sum.elim_inr]
      rw [show p + ((a : ℕ) - p) = a by omega]

end Formalism.IndefR.Mult
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem rder_zero (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (0 : GA D V → ℂ) = 0 := by
  funext g
  simp [Rder]

theorem rderC_zero (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (0 : GA D V → ℂ) = 0 := by
  simp [RderC, rder_zero]

theorem gelf_zero (τ : D.what₂.Tau) (k : ℕ) : gelf θ V τ k (0 : GA D V → ℂ) = 0 := by
  unfold gelf
  refine Finset.sum_eq_zero fun idx _ => ?_
  have h : ∀ l : List ((GA D V → ℂ) → GA D V → ℂ), (∀ f ∈ l, f 0 = 0) →
      l.foldr (fun f acc => f acc) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons f l ih =>
      rw [List.foldr_cons, ih (fun f' hf' => hl f' (by simp [hf']))]
      exact hl f (by simp)
  apply h
  intro f hf
  rw [List.mem_ofFn] at hf
  obtain ⟨a, rfl⟩ := hf
  exact rderC_zero θ V τ _

theorem foldr_rder_zero (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, ih]
    exact rder_zero θ V p.1 p.2

theorem isAutFunSm_zero : IsAutFunSm θ V (fun _ => 0) := {
  left _ _ _ := rfl
  level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const
  zfin := by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, fun τ k f hf => ?_⟩
    rw [Submodule.mem_bot] at hf
    subst hf
    rw [gelf_zero]
    exact Submodule.zero_mem _
  growth := by
    refine ⟨0, fun l _ x => ⟨0, fun g _ => ?_⟩⟩
    have h := foldr_rder_zero θ V l
    change ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ)) (x * g)‖ ≤ _
    rw [h]
    simp }

theorem isCuspFun_zero : IsCuspFun V (fun _ => 0) := by
  intro r C _ μ 𝓕 _ _ g
  simp

variable {V} {S : D.what₂.Tau → SPar}

theorem isMultMap_zero (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : IsMultMap θ M J χ 0 := {
  aut v := by
    show IsAutFunSm θ V (fun _ => 0)
    exact isAutFunSm_zero θ V
  cusp v := by
    show IsCuspFun V (fun _ => 0)
    exact isCuspFun_zero V
  lev v k _ g := by simp
  equiv τ g _ v w _ := by
    funext x
    simp [rTr]
  cont τ v x := by
    refine ⟨0, ⟨[], 0, by simp, fun w _ => by simp⟩, fun w => by simp⟩ }


variable (V) in
theorem rder_smul (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  simp only [Rder, Pi.smul_apply, smul_eq_mul]
  first
    | exact deriv_const_mul_field c
    | simp

variable (V) in
theorem foldr_rder_smul (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (c • φ) = c • l.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact rder_smul θ V p.1 p.2 c _


variable (V) in
theorem isAutFunSm_smul {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (c : ℂ) : IsAutFunSm θ V (c • φ) := {
  left γ hγ g := by simp only [Pi.smul_apply, h.left γ hγ g]
  level := by
    obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k hk1 hk2 g => by simp only [Pi.smul_apply, hk k hk1 hk2 g]⟩
  cont := h.cont.const_smul c
  smooth k τs Xs hX g := (h.smooth k τs Xs hX g).const_smul c
  zfin := by
    obtain ⟨W, hW, hφ, hg⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c hφ, hg⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [foldr_rder_smul, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c) }


variable (V) in
theorem isCuspFun_smul {φ : GA D V → ℂ} (h : IsCuspFun V φ) (c : ℂ) : IsCuspFun V (c • φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simp only [Pi.smul_apply]
  rw [MeasureTheory.integral_smul, h r C hC μ 𝓕 hμ h𝓕 g, smul_zero]

theorem isMultMap_smul {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : IsMultMap θ M J χ T) (c : ℂ) : IsMultMap θ M J χ (c • T) := {
  aut v := by
    show IsAutFunSm θ V (c • T v)
    exact isAutFunSm_smul θ V (hT.aut v) c
  cusp v := by
    show IsCuspFun V (c • T v)
    exact isCuspFun_smul V (hT.cusp v) c
  lev v k hk g := by
    simp only [_root_.smul_apply, Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]
    ring
  equiv τ g hg v w hw := by
    rw [_root_.smul_apply, _root_.smul_apply, hT.equiv τ g hg v w hw]
    rfl
  cont τ v x := by
    obtain ⟨ℓ, ⟨L, C, hL, hC⟩, hℓ⟩ := hT.cont τ v x
    refine ⟨c • ℓ, ⟨L, ‖c‖ * C, hL, fun w hw => ?_⟩, fun w => ?_⟩
    · rw [LinearMap.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, _root_.smul_apply, Pi.smul_apply, hℓ w] }

end Formalism.IndefR.Mult

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def ev (M : DSModel V S) (v₀ : M.Vec) : MMap M →ₗ[ℂ] (GA D V → ℂ) where
  toFun T := T v₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_apply (M : DSModel V S) (v₀ : M.Vec) (T : MMap M) : ev M v₀ T = T v₀ := rfl


end Formalism.IndefR.AutomorphicEvaluation

end
end
