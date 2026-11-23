module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Continuity
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.LocalField.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Data.List.Sort

@[expose] public section

section

open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryBlock

theorem block_diagonal_of_keeps_frame : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ)
    (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 →
    J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J →
    g * C = C * h → gᴴ * C = C * hᴴ →
    IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧
      (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by
  intro n D m J J' C R hJJ hJh hC hR hJR hCR hsum g h hg hgC hgHC
  have hl : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have hr : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.mp hl
  have hgJ : g * J * gᴴ = J := by
    calc g * J * gᴴ = g * (J * gᴴ * J) * J := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = J := by rw [hr, Matrix.one_mul]

  obtain ⟨k, hkdef⟩ : ∃ k, k = Cᴴ * (J * gᴴ * J) * C := ⟨_, rfl⟩
  have hk : k * h = 1 := by
    calc k * h = Cᴴ * (J * gᴴ * J) * (C * h) := by
          rw [hkdef]; simp only [Matrix.mul_assoc]
      _ = Cᴴ * ((J * gᴴ * J) * g) * C := by
          rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hl, Matrix.mul_one, hC]
  have hk' : h * k = 1 := mul_eq_one_comm.mp hk
  have hunit : IsUnit h := ⟨⟨h, k, hk', hk⟩, rfl⟩
  have hdet : IsUnit hᴴ.det := by
    have : IsUnit hᴴ := by
      refine ⟨⟨hᴴ, kᴴ, ?_, ?_⟩, rfl⟩
      · rw [← Matrix.conjTranspose_mul, hk, Matrix.conjTranspose_one]
      · rw [← Matrix.conjTranspose_mul, hk', Matrix.conjTranspose_one]
    exact (Matrix.isUnit_iff_isUnit_det _).mp this
  have hJC : g * (J * C) * hᴴ = J * C := by
    calc g * (J * C) * hᴴ = g * J * (C * hᴴ) := by simp only [Matrix.mul_assoc]
      _ = g * J * gᴴ * C := by rw [← hgHC]; simp only [Matrix.mul_assoc]
      _ = J * C := by rw [hgJ]
  have hsecond : g * (J * C) = (J * C) * (hᴴ)⁻¹ := by
    calc g * (J * C) = g * (J * C) * (hᴴ * (hᴴ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (g * (J * C) * hᴴ) * (hᴴ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (J * C) * (hᴴ)⁻¹ := by rw [hJC]

  have hgpC : (J * gᴴ * J) * C = C * k := by
    calc (J * gᴴ * J) * C = (J * gᴴ * J) * C * (h * k) := by rw [hk', Matrix.mul_one]
      _ = (J * gᴴ * J) * (C * h) * k := by simp only [Matrix.mul_assoc]
      _ = ((J * gᴴ * J) * g) * C * k := by rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = C * k := by rw [hl, Matrix.one_mul]
  have hCgR : Cᴴ * (g * R) = 0 := by
    have hadj : Cᴴ * g = h * Cᴴ := by
      have := congrArg Matrix.conjTranspose hgHC
      simpa [Matrix.conjTranspose_mul] using this
    calc Cᴴ * (g * R) = (Cᴴ * g) * R := by simp only [Matrix.mul_assoc]
      _ = h * (Cᴴ * R) := by rw [hadj, Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero]
  have hgHJC : gᴴ * J * C = J * C * k := by
    calc gᴴ * J * C = (J * J) * (gᴴ * J * C) := by rw [hJJ, Matrix.one_mul]
      _ = J * ((J * gᴴ * J) * C) := by simp only [Matrix.mul_assoc]
      _ = J * C * k := by rw [hgpC, Matrix.mul_assoc]
  have hCJg : Cᴴ * J * g = kᴴ * Cᴴ * J := by
    have := congrArg Matrix.conjTranspose hgHJC
    simpa [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hCJgR : Cᴴ * J * (g * R) = 0 := by
    calc Cᴴ * J * (g * R) = (Cᴴ * J * g) * R := by simp only [Matrix.mul_assoc]
      _ = kᴴ * Cᴴ * (J * R) := by rw [hCJg]; simp only [Matrix.mul_assoc]
      _ = kᴴ * (Cᴴ * R) * J' := by rw [hJR]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero, Matrix.zero_mul]
  have hthird : g * R = R * (Rᴴ * g * R) := by
    calc g * R = (C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ) * (g * R) := by rw [hsum, Matrix.one_mul]
      _ = C * (Cᴴ * (g * R)) + J * C * (Cᴴ * J * (g * R)) + R * (Rᴴ * g * R) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = R * (Rᴴ * g * R) := by rw [hCgR, hCJgR]; simp
  refine ⟨hunit, hsecond, hthird, ?_⟩
  have hRJ : R * J' = J * R := hJR.symm
  have hRhJR : Rᴴ * J * R = J' := by
    calc Rᴴ * J * R = Rᴴ * (J * R) := by rw [Matrix.mul_assoc]
      _ = Rᴴ * R * J' := by rw [hJR, Matrix.mul_assoc]
      _ = J' := by rw [hR, Matrix.one_mul]
  calc (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R)
      = Rᴴ * gᴴ * (R * J') * (Rᴴ * g * R) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = Rᴴ * gᴴ * J * (R * (Rᴴ * g * R)) := by rw [hRJ]; simp only [Matrix.mul_assoc]
    _ = Rᴴ * (gᴴ * J * g) * R := by rw [← hthird]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg, hRhJR]

end GlobalTheory.CompanionTheory.UnitaryBlock
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryAssembly

theorem exists_unitary_assemble : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  intro n D m J J' C R hJJ hJh hCC hCJC hRR hJR hCR hsum k₀ hk₀ kR hkR hkRJ
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at hk₀ hkR
  have hRC : Rᴴ * C = 0 := by
    have h := congrArg conjTranspose hCR
    simpa [conjTranspose_mul] using h
  have hJ'h : J'ᴴ = J' := by
    have h1 : J' = Rᴴ * (J * R) := by
      rw [hJR, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
    rw [h1]
    simp [conjTranspose_mul, hJh, Matrix.mul_assoc]
  have hRJ : Rᴴ * J = J' * Rᴴ := by
    have h := congrArg conjTranspose hJR
    simpa only [conjTranspose_mul, hJh, hJ'h] using h
  have c2 : Cᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCJC
  have a1 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]
  have a2 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (J * (C * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc J C X, ← Matrix.mul_assoc, c2, Matrix.zero_mul]
  have a3 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Cᴴ * (R * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
  have a4 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Rᴴ * (R * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hRR, Matrix.one_mul]
  have a5 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Rᴴ * (C * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hRC, Matrix.zero_mul]
  have a6 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have a7 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), J * (R * X) = R * (J' * X) := fun X => by
    rw [← Matrix.mul_assoc, hJR, Matrix.mul_assoc]
  have a8 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), Rᴴ * (J * X) = J' * (Rᴴ * X) := fun X => by
    rw [← Matrix.mul_assoc, hRJ, Matrix.mul_assoc]
  have a9 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), k₀ * (k₀ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hk₀, Matrix.one_mul]
  have a10 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (kRᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hkR, Matrix.one_mul]
  have a11 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (J' * X) = J' * (kR * X) := fun X => by
    rw [← Matrix.mul_assoc, hkRJ, Matrix.mul_assoc]
  have hs : C * Cᴴ + J * (C * (Cᴴ * J)) + R * Rᴴ = 1 := by
    simpa only [Matrix.mul_assoc] using hsum
  refine ⟨C * k₀ * Cᴴ + J * C * k₀ * Cᴴ * J + R * kR * Rᴴ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    rw [← hs]
  all_goals
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, hkRJ, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    try abel

end GlobalTheory.CompanionTheory.UnitaryAssembly
end

section

namespace GlobalTheory.CompanionTheory.HeckeSum

theorem finsum_coset_smul_linear :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (K : Subgroup G) (J : Type) [Fintype J] (c : J → ℂ) (f : J → G → ℂ),
      (∀ j, (Function.support fun q : G ⧸ K => f j q.out).Finite) → ∀ v : V,
      ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
        = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
  intro G V _ _ _ ρ K J _ c f hf v
  have hs : ∀ j, (Function.support fun q : G ⧸ K => f j q.out • ρ q.out v).Finite := by
    intro j
    refine (hf j).subset ?_
    intro q hq h0
    apply hq
    show f j q.out • ρ q.out v = 0
    have h0' : f j q.out = 0 := h0
    rw [h0', zero_smul]
  have hs' : ∀ j ∈ (Finset.univ : Finset J),
      (Function.support fun q : G ⧸ K => c j • (f j q.out • ρ q.out v)).Finite := by
    intro j _
    refine (hs j).subset ?_
    intro q hq h0
    apply hq
    show c j • (f j q.out • ρ q.out v) = 0
    have h0' : f j q.out • ρ q.out v = 0 := h0
    rw [h0', smul_zero]
  calc ∑ᶠ q : G ⧸ K, (∑ j, c j * f j q.out) • ρ q.out v
      = ∑ᶠ q : G ⧸ K, ∑ j, c j • (f j q.out • ρ q.out v) := by
        refine finsum_congr fun q => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    _ = ∑ j, ∑ᶠ q : G ⧸ K, c j • (f j q.out • ρ q.out v) :=
        finsum_sum_comm _ _ hs'
    _ = ∑ j, c j • ∑ᶠ q : G ⧸ K, f j q.out • ρ q.out v := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_finsum' (c j) (hs j)]

end GlobalTheory.CompanionTheory.HeckeSum
end

section

namespace GlobalTheory.CompanionTheory.Smooth

def linearFormStabiliser {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {g : G | l ∘ₗ ρ g = l}
  mul_mem' := by
    intro a b ha hb
    have ha' : l ∘ₗ ρ a = l := ha
    have hb' : l ∘ₗ ρ b = l := hb
    show l ∘ₗ ρ (a * b) = l
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha', hb']
  one_mem' := by
    show l ∘ₗ ρ 1 = l
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    have ha' : l ∘ₗ ρ a = l := ha
    show l ∘ₗ ρ a⁻¹ = l
    conv_lhs => rw [← ha']
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem isOpen_linearForm_stabiliser {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (l : Module.Dual ℂ V)
    (hl : ∀ x ∈ K, l ∘ₗ ρ x = l) : IsOpen {g : G | l ∘ₗ ρ g = l} :=
  Subgroup.isOpen_mono (H₁ := K) (H₂ := linearFormStabiliser ρ l) (fun x hx => hl x hx) hK

end GlobalTheory.CompanionTheory.Smooth
end

section

namespace GlobalTheory.CompanionTheory.Multiset

theorem exists_antitone_listing {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop)
    (hP : ∀ a b, P a b → f a < f b) :
    ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧
      ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  classical
  obtain ⟨l, rfl⟩ := Quot.exists_rep m
  let r : α → α → Prop := fun a b => f b ≤ f a
  haveI : DecidableRel r := fun _ _ => Classical.dec _
  haveI : Std.Total r := ⟨fun a b => le_total (f b) (f a)⟩
  haveI : IsTrans α r := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  let l' := l.insertionSort r
  have hperm : l'.Perm l := List.perm_insertionSort r l
  have hsort : l'.Pairwise r := List.pairwise_insertionSort r l
  have hlt : ∀ i j : Fin l'.length, i < j → f (l'.get j) ≤ f (l'.get i) := by
    intro i j hij
    exact (List.pairwise_iff_get.mp hsort) i j hij
  refine ⟨l'.length, l'.get, ?_, ?_, ?_⟩
  · have h1 : (Finset.univ : Finset (Fin l'.length)).val.map l'.get = ((List.ofFn l'.get : List α) : Multiset α) := by
      rw [Fin.univ_val_map]
    rw [h1, List.ofFn_get]
    exact Quot.sound hperm
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact hlt i j h
    · subst h; exact le_rfl
  · intro i j hij hp
    exact absurd (hP _ _ hp) (not_lt.mpr (hlt i j hij))

end GlobalTheory.CompanionTheory.Multiset
end

section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CFin

abbrev Idx (r m : ℕ) : Type := Fin r ⊕ Fin m ⊕ Fin r

def frm {A : Type} {n r m : ℕ} (X : Matrix (Fin n) (Fin r) A) (Z : Matrix (Fin n) (Fin m) A)
    (Y : Matrix (Fin n) (Fin r) A) : Matrix (Fin n) (Idx r m) A :=
  Matrix.fromCols X (Matrix.fromCols Z Y)

def cnt {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : ℤ := ((S.filter (· < i)).card : ℤ)

def lev {r : ℕ} (m : ℕ) (S : Finset (Fin r)) : Idx r m → ℤ
  | .inl i => cnt S i - S.card
  | .inr (.inl _) => 0
  | .inr (.inr i) => S.card - cnt S i

def wt {r : ℕ} (m : ℕ) (t : Fin r → ℝ) : Idx r m → ℝ
  | .inl i => t i
  | .inr (.inl _) => 1
  | .inr (.inr i) => (t i)⁻¹

def bd {ι A : Type} [Zero A] (b : ι → ℤ) (M : Matrix ι ι A) : Matrix ι ι A :=
  Matrix.of fun u v => if b u = b v then M u v else 0


open Classical in
def deep {r : ℕ} (t₁ : ℝ) (t : Fin r → ℝ) : Finset (Fin r) :=
  Finset.univ.filter fun j => t₁ < t j ∧ ∀ j' : Fin r, j'.val = j.val + 1 → t₁ * t j' < t j

def StabUpTo {L : Type} [CommRing L] {n r : ℕ} (X : Matrix (Fin n) (Fin r) L) (g : Matrix (Fin n) (Fin n) L)
    (j : Fin r) : Prop :=
  ∀ l : Fin r, l ≤ j → ∃ b : Fin r → L, g *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0

theorem bd_map {ι A B : Type} [Zero A] [Zero B] (b : ι → ℤ) (φ : A → B) (h0 : φ 0 = 0) (M : Matrix ι ι A) :
    (bd b M).map φ = bd b (M.map φ) := by
  ext u v
  by_cases h : b u = b v <;> simp [bd, h, h0]

theorem bd_mul {ι A : Type} [Fintype ι] [CommRing A] {b : ι → ℤ} {M N : Matrix ι ι A}
    (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) : bd b (M * N) = bd b M * bd b N := by
  ext u v
  simp only [bd, Matrix.of_apply, Matrix.mul_apply]
  by_cases h : b u = b v
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h1 : b u = b w
    · rw [if_pos h1, if_pos (h1.symm.trans h)]
    · rw [if_neg h1]
      rcases lt_or_gt_of_ne h1 with h2 | h2
      · rw [show N w v = 0 from hN (by omega), mul_zero, zero_mul]
      · rw [show M u w = 0 from hM h2, zero_mul, zero_mul]
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun w _ => ?_).symm
    by_cases h1 : b u = b w
    · rw [if_neg (fun e => h (h1.trans e)), mul_zero]
    · rw [if_neg h1, zero_mul]

end GlobalTheory.CompanionTheory.CFin

end
end

section

open MeasureTheory Topology Filter
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

variable {A : Type} [CommRing A]

structure IsFieldIdem (f : A) : Prop where
  idem : f * f = f
  ne : f ≠ 0
  inv : ∀ x, f * x ≠ 0 → ∃ y, f * x * y = f

structure IsFieldDec {ι : Type} [Fintype ι] (e : A) (f : ι → A) : Prop where
  field : ∀ i, IsFieldIdem (f i)
  orth : ∀ i j, i ≠ j → f i * f j = 0
  sum : ∑ i, f i = e

def NonDiscreteAt [TopologicalSpace A] (f : A) : Prop := ∀ V ∈ 𝓝 (0 : A), ∃ x ∈ V, x ≠ 0 ∧ f * x = x

def IsHaarMod [TopologicalSpace A] [MeasurableSpace A] (md : Aˣ →* ℝ≥0) : Prop :=
  ∀ h : Measure A, h.IsAddHaarMeasure → ∀ u : Aˣ, h.map (fun x => (u : A) * x) = ((md u : ℝ≥0∞))⁻¹ • h

abbrev Fx (A : Type) (m n : ℕ) : Type := Matrix (Fin m) (Fin n) A

variable {a r t : ℕ}

def yc (P : Fx A a r → Fx A r a) (z : Fx A a r × Fx A a t) : Fx A r t := P z.1 * z.2

def vc (P : Fx A a r → Fx A r a) (z : Fx A a r × Fx A a t) : Fx A a t := z.2 - z.1 * yc P z

def admitted (e : A) (P : Fx A a r → Fx A r a) : Set (Fx A a r × Fx A a t) :=
  {z | e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ P z.1 * z.1 = e • (1 : Fx A r r)}

def Piece (e f : A) (P : Fx A a r → Fx A r a) (i : Fin t) (C : Set A) : Set (Fx A a r × Fx A a t) :=
  {z | z ∈ admitted e P ∧ (∀ p q, z.1 p q ∈ C) ∧ (∀ l k, f * yc P z l k ∈ C ∧ (1 - f) * yc P z l k ∈ C) ∧
    (∀ p k, k ≠ i → vc P z p k ∈ C) ∧ (∀ p, (1 - f) * vc P z p i ∈ C) ∧
    ∃ c : Fin t → A, c i = 0 ∧ (∀ k, f * c k = c k ∧ c k ∈ C) ∧ ∀ p, f * vc P z p i = ∑ k, c k * vc P z p k}

def gU (i : Fin t) (c₀ : Fin t → A) : Fx A t t := 1 + Matrix.of fun k j => if j = i then c₀ k else 0

def gD (i : Fin t) (u : A) : Fx A t t := Matrix.diagonal (Function.update 1 i u)

def yU (i : Fin t) (y₀ : Fin r → A) : Fx A r t := Matrix.of fun l j => if j = i then y₀ l else 0

end GlobalTheory.CompanionTheory.NullFr
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Transversal

theorem card_eq_relIndex (X : Type) [AddCommGroup X] (A L : AddSubgroup X) (T : Finset X)
    (_hLA : L ≤ A) (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) :
    T.card = L.relIndex A := by
  classical
  let f : T → A ⧸ L.addSubgroupOf A := fun t => QuotientAddGroup.mk ⟨t.1, hT t.1 t.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
      have h' : -(⟨t, hT t ht⟩ : A) + ⟨t', hT t' ht'⟩ ∈ L.addSubgroupOf A := QuotientAddGroup.eq.mp h
      rw [AddSubgroup.mem_addSubgroupOf] at h'
      have hL : t - t' ∈ L := by
        have h2 := L.neg_mem h'
        convert h2 using 1
        push_cast
        abel
      obtain ⟨u, _, hu'⟩ := hu t (hT t ht)
      have e1 : t = u := hu' t ⟨ht, by simp⟩
      have e2 : t' = u := hu' t' ⟨ht', hL⟩
      exact Subtype.ext (e1.trans e2.symm)
    · intro q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨t, ⟨ht, hat⟩, _⟩ := hu a.1 a.2
      refine ⟨⟨t, ht⟩, QuotientAddGroup.eq.mpr ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf]
      have e : ((-(⟨t, hT t ht⟩ : A) + a : A) : X) = a.1 - t := by
        push_cast
        abel
      rw [e]
      exact hat
  calc T.card = Nat.card T := (Nat.card_eq_finsetCard T).symm
    _ = Nat.card (A ⧸ L.addSubgroupOf A) := Nat.card_congr (Equiv.ofBijective f hf)
    _ = L.relIndex A := by simp only [AddSubgroup.relIndex, AddSubgroup.index]

end GlobalTheory.CompanionTheory.Transversal
end

section

namespace GlobalTheory.CompanionTheory.LocalFieldValuationRing

theorem isFractionRing_integer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsFractionRing (ValuativeRel.valuation k).integer k :=
  (Valuation.integer.integers (ValuativeRel.valuation k)).isFractionRing

end GlobalTheory.CompanionTheory.LocalFieldValuationRing
end
