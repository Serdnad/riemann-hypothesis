module

public import Formalism.RealPlaceAnalysis.Bundle003
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TF

theorem coef {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (d : ℕ) (y : ℕ → Y) (S : Set ℂ) (hS : S.Infinite)
    (h : ∀ u ∈ S, ∑ i ∈ Finset.range d, u ^ i • y i = 0) : ∀ i ∈ Finset.range d, y i = 0 := by
  intro i hi
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  set p : Polynomial ℂ := ∑ j ∈ Finset.range d, Polynomial.C (f (y j)) * Polynomial.X ^ j with hp
  have hroot : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply hS.mono
    intro u hu
    have hfu := congrArg f (h u hu)

    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hfu
    show Polynomial.eval u p = 0
    simp only [hp, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hfu]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q i) hroot
  simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [hi] using hc

theorem qdet_mem {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (B : Subalgebra ℂ A)
    (hF : ∀ a b, F a b ∈ B) (u : ℂ) : qdet F u ∈ B := by
  unfold qdet qminor
  refine B.sum_mem fun σ _ => B.mul_mem ?_ (B.list_prod_mem ?_)
  · exact intCast_mem B _
  · intro z hz
    rw [List.mem_ofFn] at hz
    obtain ⟨k, rfl⟩ := hz
    unfold Tm
    refine B.add_mem ?_ (hF _ _)
    split_ifs
    · exact B.algebraMap_mem _
    · exact B.zero_mem

theorem inv_aux {A : Type*} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (x : A) (hx : x ∈ B) (u : ℂ) :
    ∀ L : List ℂ, (∀ c ∈ L, u + c ≠ 0) → ∃ h ∈ B, Commute h x ∧ ∃ β : ℂ, β ≠ 0 ∧
      (L.map fun c => x - algebraMap ℂ A c).prod = (algebraMap ℂ A u + x) * h + algebraMap ℂ A β := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨0, B.zero_mem, Commute.zero_left x, 1, one_ne_zero, ?_⟩
    simp
  | cons c L ih =>
    intro hL
    obtain ⟨h, hB, hc, β, hβ, heq⟩ := ih (fun d hd => hL d (List.mem_cons_of_mem _ hd))
    have hs : u + c ≠ 0 := hL c (by simp)
    have hcm : Commute ((x - algebraMap ℂ A c) * h + algebraMap ℂ A β) x :=
      (((Commute.refl x).sub_left (Algebra.commute_algebraMap_left c x)).mul_left hc).add_left
        (Algebra.commute_algebraMap_left β x)
    refine ⟨(x - algebraMap ℂ A c) * h + algebraMap ℂ A β,
      B.add_mem (B.mul_mem (B.sub_mem hx (B.algebraMap_mem c)) hB) (B.algebraMap_mem β),
      hcm, -((u + c) * β), neg_ne_zero.mpr (mul_ne_zero hs hβ), ?_⟩
    rw [List.map_cons, List.prod_cons, heq]
    have hq : x - algebraMap ℂ A c = (algebraMap ℂ A u + x) - algebraMap ℂ A (u + c) := by
      rw [map_add (f := _)]; abel
    rw [hq, map_neg, map_mul]
    have ht := Algebra.commutes (u + c) (algebraMap ℂ A u + x)
    generalize algebraMap ℂ A u + x = v at ht ⊢
    generalize algebraMap ℂ A (u + c) = t at ht ⊢
    generalize algebraMap ℂ A β = w
    calc (v - t) * (v * h + w) = v * v * h + v * w - t * v * h - t * w := by noncomm_ring
      _ = v * v * h + v * w - v * t * h - t * w := by rw [ht]
      _ = v * ((v - t) * h + w) + -(t * w) := by noncomm_ring

theorem inv_of_alg {A : Type*} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (x : A) (hx : x ∈ B) (u : ℂ)
    (L : List ℂ) (h0 : (L.map fun c => x - algebraMap ℂ A c).prod = 0) (hu : ∀ c ∈ L, u + c ≠ 0) :
    ∃ h ∈ B, h * (algebraMap ℂ A u + x) = 1 := by
  obtain ⟨h, hB, hc, β, hβ, heq⟩ := inv_aux B x hx u L hu
  rw [h0] at heq
  have hv : h * (algebraMap ℂ A u + x) = (algebraMap ℂ A u + x) * h :=
    ((Algebra.commute_algebraMap_left u h).symm.add_right hc).eq
  have hvh : (algebraMap ℂ A u + x) * h = -algebraMap ℂ A β := eq_neg_of_add_eq_zero_left heq.symm
  refine ⟨algebraMap ℂ A (-β⁻¹) * h, B.mul_mem (B.algebraMap_mem _) hB, ?_⟩
  rw [mul_assoc, hv, hvh, mul_neg, ← map_mul]
  simp [hβ]

theorem left_inv_prod {A : Type*} [Ring A] (B : Subring A) :
    ∀ l : List A, (∀ a ∈ l, ∃ h ∈ B, h * a = 1) → ∃ h ∈ B, h * l.prod = 1 := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, B.one_mem, by simp⟩
  | cons a l ih =>
    intro hl
    obtain ⟨ha, hB, hae⟩ := hl a (List.mem_cons_self ..)
    obtain ⟨h, hB', he⟩ := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
    refine ⟨h * ha, B.mul_mem hB' hB, ?_⟩
    rw [List.prod_cons, mul_assoc, ← mul_assoc ha, hae, one_mul, he]

theorem eig_prod {W : Type*} [AddCommGroup W] [Module ℂ W] (φ : W →ₗ[ℂ] ℂ) :
    ∀ l : List (Module.End ℂ W), (∀ a ∈ l, ∃ μ : ℂ, μ ≠ 0 ∧ φ ∘ₗ a = μ • φ) →
      ∃ μ : ℂ, μ ≠ 0 ∧ φ ∘ₗ l.prod = μ • φ := by
  intro l hl
  induction l with
  | nil => exact ⟨1, one_ne_zero, by ext; simp⟩
  | cons a l ih =>
    obtain ⟨μa, hμa, ha⟩ := hl a (by simp)
    obtain ⟨μl, hμl, hl1⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    refine ⟨μa * μl, mul_ne_zero hμa hμl, LinearMap.ext fun w => ?_⟩
    have e1 := LinearMap.congr_fun ha (l.prod w)
    have e2 := LinearMap.congr_fun hl1 w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [List.prod_cons, Module.End.mul_apply, e1, e2, mul_assoc]

end TF

end PositivityTheory.Rg.Cz
end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ChainP

section gen
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem intCast_comp (f : V →ₗ[ℂ] W) (z : ℤ) :
    f ∘ₗ ((z : Module.End ℂ V)) = ((z : Module.End ℂ W)) ∘ₗ f := by
  refine LinearMap.ext fun v => ?_
  simp [Module.End.intCast_apply]

theorem ofFn_comp (f : V →ₗ[ℂ] W) {t : ℕ} (A : Fin t → Module.End ℂ V) (B : Fin t → Module.End ℂ W)
    (h : ∀ k, f ∘ₗ A k = B k ∘ₗ f) : f ∘ₗ (List.ofFn A).prod = (List.ofFn B).prod ∘ₗ f := by
  induction t with
  | zero => refine LinearMap.ext fun v => ?_; simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc,
      ih (fun k => A k.succ) (fun k => B k.succ) (fun k => h _), LinearMap.comp_assoc]

theorem qdet_comp {n : ℕ} (f : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b, f ∘ₗ E a b = F a b ∘ₗ f) (u : ℂ) :
    f ∘ₗ qdet E u = qdet F u ∘ₗ f := by
  unfold qdet qminor
  have key : ∀ σ : Equiv.Perm (Fin n), f ∘ₗ (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ V) *
      (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod) =
      (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) *
      (List.ofFn fun k : Fin n => Tm F (u - (k : ℂ)) (id (σ k)) (id k)).prod) ∘ₗ f := fun σ => by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, intCast_comp,
    LinearMap.comp_assoc, ofFn_comp f _ _ (fun k => ?_), LinearMap.comp_assoc]
    simp only [Tm]
    rw [LinearMap.comp_add, LinearMap.add_comp, h]
    congr 1
    split_ifs
    · refine LinearMap.ext fun v => ?_; simp
    · simp
  refine LinearMap.ext fun v => ?_

  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun σ _ => LinearMap.congr_fun (key σ) v

theorem listSub_comp (f : V →ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : f ∘ₗ A = B ∘ₗ f)
    (L : List ℂ) :
    f ∘ₗ (L.map fun r => A - algebraMap ℂ _ r).prod = (L.map fun r => B - algebraMap ℂ _ r).prod ∘ₗ f := by
  have key : ∀ r : ℂ, f ∘ₗ (A - algebraMap ℂ _ r) = (B - algebraMap ℂ _ r) ∘ₗ f := by
    intro r
    ext v
    have hv := LinearMap.congr_fun h v
    simp only [LinearMap.comp_apply] at hv
    simp [hv]
  induction L with
  | nil =>
    ext v
    simp
  | cons r L ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, key r,
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

theorem listSub_commute (A T : Module.End ℂ V) (h : Commute A T) (L : List ℂ) :
    Commute (L.map fun r => A - algebraMap ℂ _ r).prod T := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  exact h.sub_left (Algebra.commutes r T)

theorem listSub_pairwise (A : Module.End ℂ V) (L : List ℂ) :
    (L.map fun r => A - algebraMap ℂ _ r).Pairwise Commute := by
  rw [List.pairwise_map]
  exact List.pairwise_of_forall fun r s =>
    ((Commute.refl A).sub_left (Algebra.commutes r A)).sub_right (Algebra.commutes s _).symm

theorem listSub_kill (A : Module.End ℂ V) {n : ℕ} (l : Fin n → ℂ) (c : Fin n)
    (h0 : (List.ofFn fun k => A - algebraMap ℂ _ (l k)).prod = 0) :
    (((List.ofFn l).erase (l c)).map fun r => A - algebraMap ℂ _ r).prod * (A - algebraMap ℂ _ (l c)) = 0 := by
  have hm : l c ∈ List.ofFn l := by simp
  have h1 : ((List.ofFn l).map fun r => A - algebraMap ℂ (Module.End ℂ V) r).prod = 0 := by
    rw [List.map_ofFn]
    exact h0
  rw [((List.perm_cons_erase hm).map _).prod_eq' (listSub_pairwise A _), List.map_cons,
    List.prod_cons] at h1
  rw [(listSub_commute A _ ((Commute.refl A).sub_right (Algebra.commutes _ A).symm) _).eq]
  exact h1

theorem adjoin_commute {A : Type} [Ring A] [Algebra ℂ A] (s : Set A) (T : A) (hs : ∀ x ∈ s, Commute x T) :
    ∀ g ∈ Algebra.adjoin ℂ s, Commute g T := by
  intro g hg
  have hle : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {T} :=
    Algebra.adjoin_le fun x hx => by
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hs x hx).symm.eq
  have h2 := hle hg
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact (h2 T (Set.mem_singleton T)).symm

end gen

end ChainP

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

abbrev TV (n : ℕ) (M P : Type) : Type := (P → Fin n) → M

def lift (B : Module.End ℂ M) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => B ∘ₗ LinearMap.proj I

def eAt (p : P) (a b : Fin n) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => if I p = a then LinearMap.proj (Function.update I p b) else 0

def tE (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (TV n M P) :=
  lift (E a b) + ∑ p ∈ S, eAt p a b

def Om (E : Fin n → Fin n → Module.End ℂ M) (p : P) : Module.End ℂ (TV n M P) :=
  ∑ a, ∑ b, lift (E a b) * eAt p b a

def pm (σ : Equiv.Perm P) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => LinearMap.proj (I ∘ σ)

def alt (G : Finset (Equiv.Perm P)) : Module.End ℂ (TV n M P) :=
  ∑ σ ∈ G, ((Equiv.Perm.sign σ : ℤ) : ℂ) • pm σ

def colG {C : Type} [DecidableEq C] (col : P → C) : Finset (Equiv.Perm P) :=
  Finset.univ.filter fun σ => ∀ p, col (σ p) = col p

def firstG (m k : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  Finset.univ.filter fun σ => ∀ j : Fin m, k ≤ (j : ℕ) → σ j = j

def xJ {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) : Module.End ℂ (TV n M (Fin m)) :=
  Om E j + ∑ i ∈ Finset.univ.filter (· < j), pm (Equiv.swap i j)

def PiJ (m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) : Module.End ℂ (TV n M (Fin m)) :=
  (List.ofFn fun j : Fin m => algebraMap ℂ _ u + xJ E j).prod

def HasChar (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) : Prop :=
  ∀ u : ℂ, qdet E u = algebraMap ℂ _ (∏ k, (u + l k))

def IsWh (E : Fin n → Fin n → Module.End ℂ M) (ℓ : M →ₗ[ℂ] ℂ) : Prop :=
  ∃ ψ : Fin n → Fin n → ℂ, (∀ a b : Fin n, (a : ℕ) + 1 = b → ψ a b ≠ 0) ∧
    (∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) ∧ ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ

def IsTab {C : Type} (col : P → C) (b : P → Fin n) : Prop :=
  (∀ p q, col p = col q → b p = b q → p = q) ∧ ∀ p i, b p < i → ∃ q, col q = col p ∧ b q = i

def cA {C : Type} [DecidableEq C] (col : P → C) (b : P → Fin n) : TV n M P →ₗ[ℂ] M :=
  LinearMap.proj b ∘ₗ alt (colG col)

def envAlg {ι : Type} (E : ι → Fin n → Fin n → Module.End ℂ M) : Subalgebra ℂ (Module.End ℂ M) :=
  Algebra.adjoin ℂ {T | ∃ τ a b, T = E τ a b}

def fib {ι : Type} [DecidableEq ι] (lab : P → ι) (τ : ι) : Finset P := Finset.univ.filter fun p => lab p = τ

def actT {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) :
    Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ J : P → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) • (ρ γ ∘ₗ LinearMap.proj J)

structure IsKD {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) :
    Prop where
  invol : ∀ τ, bar (bar τ) = τ
  ne : ∀ τ, bar τ ≠ τ
  one : ∀ τ, κ τ 1 = 1
  mul : ∀ τ γ δ, κ τ (γ * δ) = κ τ γ * κ τ δ
  unit : ∀ τ γ, κ τ γ * (κ τ γ)ᴴ = 1
  conj : ∀ τ γ i j, κ (bar τ) γ i j = star (κ τ γ i j)
  cont : ∀ τ i j, Continuous fun γ => κ τ γ i j
  sep : ∀ γ δ, (∀ τ, κ τ γ = κ τ δ) → γ = δ

structure IsGK {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M) : Prop where
  gl : ∀ τ, GlRel (E τ)
  comm : ∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)
  one : ρ 1 = 1
  mul : ∀ γ δ, ρ (γ * δ) = ρ γ * ρ δ
  ad : ∀ γ τ a b, ρ γ * E τ a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E τ c d) * ρ γ
  fin : ∀ y, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y))
  cont : ∀ y (lam : M →ₗ[ℂ] ℂ), Continuous fun γ => lam (ρ γ y)
  der : ∀ τ (X : Matrix (Fin n) (Fin n) ℂ), Xᴴ = -X → ∃ c : ℝ → Γ, c 0 = 1 ∧
    (∀ i j, HasDerivAt (fun t => κ τ (c t) i j) (X i j) 0) ∧
    (∀ τ', τ' ≠ τ → τ' ≠ bar τ → ∀ t, κ τ' (c t) = 1) ∧
    ∀ y (lam : M →ₗ[ℂ] ℂ), HasDerivAt (fun t => lam (ρ (c t) y))
      (lam ((∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)) y)) 0

def dbl {Q : Type} {N : ℕ} (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Q ⊕ (Fin N ⊕ Fin N)) :=
  Equiv.sumCongr (Equiv.refl Q) (Equiv.sumCongr σ σ)

def altPair {Q ι : Type} [Fintype Q] [DecidableEq Q] [DecidableEq ι] {N : ℕ} (tl : Fin N → ι) :
    Module.End ℂ (TV n M (Q ⊕ (Fin N ⊕ Fin N))) :=
  ∑ σ ∈ colG tl, ((Equiv.Perm.sign σ : ℤ) : ℂ) • pm (dbl σ)

def lab3 {Q ι : Type} {N : ℕ} (bar : ι → ι) (lab : Q → ι) (tl : Fin N → ι) : Q ⊕ (Fin N ⊕ Fin N) → ι :=
  Sum.elim lab (Sum.elim tl (bar ∘ tl))

def KTypeData {ι Γ : Type} [DecidableEq ι] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (l : ι → Fin n → ℤ) (s : ℤ) : Prop :=
  ∃ (q N : ℕ) (lab : Fin q → ι) (col : Fin q → ℕ) (b : Fin q → Fin n) (tl : Fin N → ι)
    (η : TV n M (Fin q ⊕ (Fin N ⊕ Fin N))),
    (∀ p p', col p = col p' → lab p = lab p') ∧ IsTab col b ∧ (∀ k k', tl k ≠ bar (tl k')) ∧
    (∀ τ, ∃ w : Equiv.Perm (Fin n), ∀ i : Fin n,
      s - l τ (w i) = ((Finset.univ.filter fun p => lab p = τ ∧ b p = i).card : ℤ) + (i : ℕ)) ∧
    (∀ γ, actT (lab3 bar lab tl) κ ρ γ η = η) ∧
    (∀ p p', col p = col p' → p ≠ p' → pm (Equiv.swap (Sum.inl p) (Sum.inl p')) η = -η) ∧
    altPair tl η ≠ 0

end PositivityTheory.Rg.Cz

end
end
