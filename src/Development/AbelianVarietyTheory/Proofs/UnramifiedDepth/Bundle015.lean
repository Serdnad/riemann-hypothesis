module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorOfGeneralizedEigenUnramified
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.IncomingBounds.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.DualLattices.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CongruentCharacters

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM; rw [V.v.map_neg]; exact ha

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  have ha' : (0 : WithTop ℝ) ≤ V.v a := by simpa [VF.Ge] using ha
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem cancel_unit {u a : C} {w : ℝ} (hu : V.MM (u - 1)) (h : V.Ge w (u * a)) : V.Ge w a := by
  have h0 : V.v u = 0 := by
    have h1 : V.v (1 : C) < V.v (u - 1) := by rw [V.v.map_one]; exact hu
    have h2 := V.v.map_add_eq_of_lt_left h1
    rw [V.v.map_one] at h2
    simpa using h2
  unfold VF.Ge at *
  rwa [V.v.map_mul, h0, zero_add] at h

theorem pow_sub_pow_factor {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (hab : V.MM (a - b)) (n : ℕ) :
    ∃ S : C, a ^ (n + 1) - b ^ (n + 1) = (a - b) * S ∧
      V.MM (S - ((n + 1 : ℕ) : C) * b ^ n) := by
  induction n with
  | zero => exact ⟨1, by ring, by simp [VF.MM]⟩
  | succ n ih =>
    obtain ⟨S, h1, h2⟩ := ih
    refine ⟨a * S + b ^ (n + 1), by linear_combination a * h1, ?_⟩
    have h3 := mm_add (mm_int_mul ha h2)
      (mm_int_mul (VF.Ge.mul_int (VF.ge_natCast (n + 1)) (hb.pow n)) hab)
    convert h3 using 1
    push_cast; ring

theorem eq_zero_of_ge_all {a : C} (h : ∀ n : ℕ, V.Ge n a) : a = 0 := by
  apply (AddValuation.top_iff V.v).1
  induction hv : V.v a using WithTop.recTopCoe with
  | top => rfl
  | coe t =>
    exfalso
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have := h n
    unfold VF.Ge at this
    rw [hv] at this
    have h' : (n : ℝ) ≤ t := WithTop.coe_le_coe.1 this
    linarith

theorem eq_of_congruent : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ), 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ ψ φ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, V.Ge 0 (φ x)) → V.MM (ψ ε - 1) → (∀ x, V.MM (ψ x - φ x)) → ψ = φ := by
  intro C _ V O _ d hd ε ⟨y, hy⟩ hx ψ φ hψ hφ hε hc
  have hl0 : 0 < V.l := V.l_prime.pos
  obtain ⟨m, hm⟩ : ∃ m, V.l ^ d = m + 1 := ⟨V.l ^ d - 1, by have := pow_pos hl0 d; omega⟩
  have hq : V.MM ((m + 1 : ℕ) : C) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [← hm, pow_succ, Nat.cast_mul]
    exact mm_int_mul (VF.ge_natCast _) mm_l
  have key : ∀ n : ℕ, ∀ x, V.Ge n (ψ x - φ x) := by
    intro n
    induction n with
    | zero => intro x; simpa using (hψ x).sub (hφ x)
    | succ n ih =>
      have hl : ∀ z, V.Ge ((n + 1 : ℕ) : ℝ) ((V.l : C) * (ψ z - φ z)) := fun z => by
        have := (ih z).l_mul
        convert this using 1
        push_cast; ring
      have hδε : V.Ge ((n + 1 : ℕ) : ℝ) (ψ ε - φ ε) := by
        have e1 := congrArg ψ hy
        have e2 := congrArg φ hy
        simp only [map_sub, map_mul, map_natCast] at e1 e2
        apply cancel_unit (u := ψ ε + φ ε - 1)
        · have := mm_add (mm_add hε hε) (mm_neg (hc ε))
          convert this using 1; ring
        · convert hl y using 1
          linear_combination e1 - e2
      intro x
      obtain ⟨z, hz⟩ := hx x
      have e1 := congrArg ψ hz
      have e2 := congrArg φ hz
      simp only [map_sub, map_mul, map_natCast, map_pow, hm] at e1 e2
      obtain ⟨S, hS1, hS2⟩ := pow_sub_pow_factor (hψ x) (hφ x) (hc x) m
      have hS : V.MM S := by
        have := mm_add hS2 (mm_int_mul ((hφ x).pow m) hq)
        convert this using 1; ring
      have ht : V.Ge 0 (φ x ^ (m + 1) - φ x) := ((hφ x).pow _).sub (hφ x)
      apply cancel_unit (u := 1 - S)
      · have := mm_neg hS
        convert this using 1; ring
      apply cancel_unit hε
      have := (VF.Ge.mul_int ht hδε).sub (hl z)
      convert this using 1
      linear_combination ψ ε * hS1 - e1 + e2
  ext x
  exact sub_eq_zero.1 (eq_zero_of_ge_all fun n => key n x)

end GlobalTheory.CongruentCharacters
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.GenChar

theorem step {C : Type} [Field C] {O κ : Type} [Fintype κ] [DecidableEq κ]
    (n : O → Matrix κ κ C) (hc : ∀ x y, Commute (n x) (n y)) (w : κ → C) (hw : w ≠ 0)
    (hn : ∀ x, ∃ k : ℕ, ((n x) ^ k).mulVec w = 0) (x₀ : O) :
    ∃ u : κ → C, u ≠ 0 ∧ (∀ x, ∃ k : ℕ, ((n x) ^ k).mulVec u = 0) ∧ (n x₀).mulVec u = 0 ∧
      ∀ y, (n y).mulVec w = 0 → (n y).mulVec u = 0 := by
  classical
  have hk := Nat.find_spec (hn x₀)
  have hk0 : Nat.find (hn x₀) ≠ 0 := by
    intro h
    rw [h, pow_zero, Matrix.one_mulVec] at hk
    exact hw hk
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hlt : ¬ ((n x₀) ^ j).mulVec w = 0 := Nat.find_min (hn x₀) (by omega)
  have key : ∀ (y : O) (k : ℕ), ((n y) ^ k).mulVec w = 0 →
      ((n y) ^ k).mulVec (((n x₀) ^ j).mulVec w) = 0 := by
    intro y k h
    rw [Matrix.mulVec_mulVec, ((hc y x₀).pow_pow k j).eq, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]
  refine ⟨((n x₀) ^ j).mulVec w, hlt, fun x => ?_, ?_, fun y hy => ?_⟩
  · obtain ⟨k, h⟩ := hn x
    exact ⟨k, key x k h⟩
  · rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hj] at hk
    exact hk
  · have := key y 1 (by rwa [pow_one])
    rwa [pow_one] at this

theorem ge_of_eigen {C : Type} [Field C] (V : VF C) {κ : Type} [Fintype κ]
    (A : Matrix κ κ C) (hA : ∀ i j, V.Ge 0 (A i j)) (c : C) (u : κ → C) (hu : u ≠ 0)
    (h : A.mulVec u = c • u) : V.Ge 0 c := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => V.v (u i))
    ⟨i₀, Finset.mem_univ _⟩
  have h0 : V.v (u i₀) ≠ ⊤ := by
    intro h
    exact hi₀ (by simpa using h)
  have h1 : V.v (u i) ≠ ⊤ := ne_top_of_le_ne_top h0 (hi i₀ (Finset.mem_univ _))
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h1
  have h2 : V.Ge t (c * u i) := by
    have : c * u i = ∑ j, A i j * u j := by
      have := congrFun h i
      simpa [Matrix.mulVec, dotProduct] using this.symm
    rw [this]
    refine VF.Ge.sum fun j _ => (hA i j).mul_int ?_
    unfold VF.Ge
    rw [ht]
    exact hi j (Finset.mem_univ _)
  unfold VF.Ge at h2 ⊢
  rw [V.v.map_mul, ← ht] at h2
  induction hv : V.v c using WithTop.recTopCoe with
  | top => exact le_top
  | coe s =>
    rw [hv] at h2
    have h' : ((t : ℝ) : WithTop ℝ) ≤ ((s + t : ℝ) : WithTop ℝ) := by
      simpa [WithTop.coe_add] using h2
    have h'' : t ≤ s + t := by exact_mod_cast h'
    have : (0 : ℝ) ≤ s := by linarith
    exact_mod_cast this

theorem exists_character : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (χ : O → C) (w : κ → C), w ≠ 0 → (∀ x, ∃ k : ℕ, ((L x - χ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → ∃ ψ : O →+* C, (∀ x, ψ x = χ x) ∧ ∀ x, V.Ge 0 (ψ x) := by
  intro C _ V O _ κ _ _ L hL χ w hw hn
  set n : O → Matrix κ κ C := fun x => L x - χ x • (1 : Matrix κ κ C) with hndef
  have hLc : ∀ x y, Commute (L x) (L y) := fun x y => (Commute.all x y).map L
  have hc : ∀ x y, Commute (n x) (n y) := fun x y =>
    ((hLc x y).sub_right ((Commute.one_right _).smul_right _)).sub_left
      ((Commute.one_left _).smul_left _)
  have heig : ∀ (x : O) (u : κ → C), (n x).mulVec u = 0 → (L x).mulVec u = χ x • u := by
    intro x u h
    simp only [hndef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact sub_eq_zero.mp h
  have three : ∀ x y z : O, ∃ u : κ → C, u ≠ 0 ∧ (L x).mulVec u = χ x • u ∧
      (L y).mulVec u = χ y • u ∧ (L z).mulVec u = χ z • u := by
    intro x y z
    obtain ⟨u₁, h1, h1n, h1x, -⟩ := step n hc w hw hn x
    obtain ⟨u₂, h2, h2n, h2y, h2p⟩ := step n hc u₁ h1 h1n y
    obtain ⟨u₃, h3, -, h3z, h3p⟩ := step n hc u₂ h2 h2n z
    exact ⟨u₃, h3, heig _ _ (h3p _ (h2p _ h1x)), heig _ _ (h3p _ h2y), heig _ _ h3z⟩
  have h1 : χ 1 = 1 := by
    obtain ⟨u, hu, h, -, -⟩ := three 1 1 1
    rw [map_one, Matrix.one_mulVec] at h
    apply smul_left_injective C hu
    simpa using h.symm
  have h0 : χ 0 = 0 := by
    obtain ⟨u, hu, h, -, -⟩ := three 0 0 0
    rw [map_zero, Matrix.zero_mulVec] at h
    apply smul_left_injective C hu
    simpa using h.symm
  have hadd : ∀ x y, χ (x + y) = χ x + χ y := by
    intro x y
    obtain ⟨u, hu, hx, hy, h⟩ := three x y (x + y)
    rw [map_add (f := _), Matrix.add_mulVec, hx, hy, ← add_smul] at h
    exact smul_left_injective C hu h.symm
  have hmul : ∀ x y, χ (x * y) = χ x * χ y := by
    intro x y
    obtain ⟨u, hu, hx, hy, h⟩ := three x y (x * y)
    rw [map_mul, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, hx, smul_smul, mul_comm (χ y)] at h
    exact smul_left_injective C hu h.symm
  refine ⟨⟨⟨⟨χ, h1⟩, hmul⟩, h0, hadd⟩, fun _ => rfl, fun x => ?_⟩
  obtain ⟨u, hu, h, -, -⟩ := three x x x
  exact ge_of_eigen V (L x) (hL x) (χ x) u hu h

end GlobalTheory.GenChar
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.eigenvector_of_generalized_eigen_unramified : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ d : ℕ, 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ (ψ : O →+* C) (w : κ → C), (∀ x, V.Ge 0 (ψ x)) → (∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → (∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i)) → ∀ x, (L x).mulVec w = ψ x • w := by
  first | exact @GlobalTheory.GenEigen.eigen_of_gen_eigen | exact GlobalTheory.GenEigen.eigen_of_gen_eigen | (intros; apply GlobalTheory.GenEigen.eigen_of_gen_eigen <;> assumption)
end

section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem finSplit_max_eq {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] (φ : A →ₐ[O] O) (N : Ideal A) (hN : N.IsMaximal)
    (h : RingHom.ker φ ≤ N) : N = (maximalIdeal O).comap φ := by
  refine hN.eq_of_le ?_ ?_
  · intro htop
    have h1 : (1 : A) ∈ (maximalIdeal O).comap φ := htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h1) isUnit_one
  · intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hN.ne_top
    rw [Ideal.eq_top_iff_one]
    have hy : algebraMap O A (↑hu.unit⁻¹) * x ∈ N := N.mul_mem_left _ hx
    have hφy : φ (algebraMap O A (↑hu.unit⁻¹) * x) = 1 := by
      rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      exact hu.val_inv_mul
    have hk : 1 - algebraMap O A (↑hu.unit⁻¹) * x ∈ N :=
      h (by rw [RingHom.mem_ker, map_sub, map_one, hφy, sub_self])
    simpa using N.add_mem hk hy

private theorem finSplit_exists {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [Finite (A →ₐ[O] O)] (M : Ideal A) :
    ∃ e : A, ∀ φ : A →ₐ[O] O, ((maximalIdeal O).comap φ = M → φ e = 1) ∧
      ((maximalIdeal O).comap φ ≠ M → φ e = 0) := by
  classical
  have := Fintype.ofFinite (A →ₐ[O] O)
  have key : ∀ φ ψ : A →ₐ[O] O, ∃ x : A, (maximalIdeal O).comap φ = M →
      (maximalIdeal O).comap ψ ≠ M → φ x = 1 ∧ ψ x = 0 := by
    intro φ ψ
    by_cases hφ : (maximalIdeal O).comap φ = M
    swap
    · exact ⟨0, fun h => absurd h hφ⟩
    by_cases hψ : (maximalIdeal O).comap ψ = M
    · exact ⟨0, fun _ h => absurd hψ h⟩
    have htop : RingHom.ker φ ⊔ RingHom.ker ψ = ⊤ := by
      by_contra hne
      obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal _ hne
      have e1 := finSplit_max_eq φ N hN (le_sup_left.trans hle)
      have e2 := finSplit_max_eq ψ N hN (le_sup_right.trans hle)
      exact hψ (e2.symm.trans (e1.trans hφ))
    have h1 : (1 : A) ∈ RingHom.ker φ ⊔ RingHom.ker ψ := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨b, fun _ _ => ⟨?_, RingHom.mem_ker.1 hb⟩⟩
    have hφab := congrArg φ hab
    rw [map_add (f := _), RingHom.mem_ker.1 ha, zero_add, map_one] at hφab
    exact hφab
  choose x hx using key
  refine ⟨1 - ∏ φ ∈ Finset.univ.filter (fun φ : A →ₐ[O] O => (maximalIdeal O).comap φ = M),
      (1 - ∏ ψ ∈ Finset.univ.filter (fun ψ : A →ₐ[O] O => (maximalIdeal O).comap ψ ≠ M), x φ ψ),
      fun φ0 => ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
  · rw [map_sub, map_one, map_prod, sub_eq_self]
    apply Finset.prod_eq_zero (i := φ0) (by simp [h0])
    rw [map_sub, map_one, map_prod, sub_eq_zero, eq_comm]
    apply Finset.prod_eq_one
    intro ψ hψ
    exact (hx φ0 ψ h0 (Finset.mem_filter.1 hψ).2).1
  · rw [map_sub, map_one, map_prod, sub_eq_zero, eq_comm]
    apply Finset.prod_eq_one
    intro φ hφ
    rw [map_sub, map_one, map_prod, sub_eq_self]
    apply Finset.prod_eq_zero (i := φ0) (by simp [h0])
    exact (hx φ φ0 (Finset.mem_filter.1 hφ).2 h0).2

theorem finite_algebra_split_local :
  (∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Finite (A →ₐ[O] O)],
    (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) →
    ∃ (n : ℕ) (ε : Fin n → A), CompleteOrthogonalIdempotents ε ∧ ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})) := by
  intro O A _ _ _ _ _ _ hsep
  classical
  have := Fintype.ofFinite (A →ₐ[O] O)
  have hone : (1 : O) ∉ maximalIdeal O := fun h =>
    mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h) isUnit_one
  let Pts := Set.range (fun φ : A →ₐ[O] O => (maximalIdeal O).comap φ)
  let eqv : Fin (Fintype.card Pts) ≃ Pts := (Fintype.equivFin Pts).symm
  choose e he using fun M : Ideal A => finSplit_exists (O := O) M
  have hval : ∀ (M : Ideal A) (φ : A →ₐ[O] O),
      φ (e M) = if (maximalIdeal O).comap φ = M then 1 else 0 := by
    intro M φ
    split_ifs with h
    · exact (he M φ).1 h
    · exact (he M φ).2 h
  have ext : ∀ a b : A, (∀ φ : A →ₐ[O] O, φ a = φ b) → a = b := fun a b h =>
    sub_eq_zero.1 (hsep _ fun φ => by rw [map_sub, h φ, sub_self])
  have hmax : ∀ N : Ideal A, N.IsMaximal → ∃ φ : A →ₐ[O] O, (maximalIdeal O).comap φ = N := by
    intro N hN
    by_contra hcon
    simp only [not_exists] at hcon
    have hnot : ∀ φ : A →ₐ[O] O, ¬ RingHom.ker φ ≤ N := fun φ hle =>
      hcon φ (finSplit_max_eq φ N hN hle).symm
    simp only [SetLike.not_le_iff_exists] at hnot
    choose a ha haN using hnot
    have := hN.isPrime
    have h0 : ∏ φ, a φ = 0 := hsep _ fun ψ => by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ ψ) (RingHom.mem_ker.1 (ha ψ))
    have hin : ∏ φ, a φ ∈ N := h0 ▸ N.zero_mem
    obtain ⟨φ, -, hφ⟩ := Ideal.IsPrime.prod_mem_iff.1 hin
    exact haN φ hφ
  refine ⟨Fintype.card Pts, fun i => e (eqv i).1, ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩
  · show e (eqv i).1 * e (eqv i).1 = e (eqv i).1
    apply ext
    intro φ
    rw [map_mul, hval]
    split_ifs <;> simp
  · show e (eqv i).1 * e (eqv j).1 = 0
    have hne : (eqv i).1 ≠ (eqv j).1 := fun h => hij (eqv.injective (Subtype.ext h))
    apply ext
    intro φ
    rw [map_mul, hval, hval, map_zero]
    split_ifs with h1 h2 h2
    · exact absurd (h1.symm.trans h2) hne
    all_goals simp
  · apply ext
    intro φ

    rw [map_sum, map_one]
    simp only [hval]
    rw [Fintype.sum_equiv eqv _
      (fun M : Pts => if (maximalIdeal O).comap φ = M.1 then (1 : O) else 0) (fun _ => rfl)]
    rw [Finset.sum_eq_single ⟨(maximalIdeal O).comap φ, φ, rfl⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · obtain ⟨φ0, hφ0⟩ := (eqv i).2
    replace hφ0 : (maximalIdeal O).comap φ0 = (eqv i).1 := hφ0
    have hmem : ∀ ψ : A →ₐ[O] O,
        1 - e (eqv i).1 ∈ (maximalIdeal O).comap ψ ↔ (maximalIdeal O).comap ψ = (eqv i).1 := by
      intro ψ
      rw [Ideal.mem_comap, map_sub, map_one, hval]
      split_ifs with h
      · simp [h]
      · simp only [sub_zero, h, iff_false]
        exact hone
    have hJM : Ideal.span {1 - e (eqv i).1} ≤ (eqv i).1 := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have h := (hmem φ0).2 hφ0
      rw [hφ0] at h
      exact h
    have hMtop : (eqv i).1 ≠ ⊤ := by
      rw [← hφ0]
      intro h
      have h1 : (1 : A) ∈ (maximalIdeal O).comap φ0 := h ▸ Submodule.mem_top
      rw [Ideal.mem_comap, map_one] at h1
      exact hone h1
    have hJ : Ideal.span {1 - e (eqv i).1} ≠ ⊤ := fun h => hMtop (top_le_iff.1 (h ▸ hJM))
    have := Ideal.Quotient.nontrivial_iff.2 hJ
    obtain ⟨Q0, hQ0⟩ := Ideal.exists_maximal (A ⧸ Ideal.span {1 - e (eqv i).1})
    have hcomap : ∀ Q : Ideal (A ⧸ Ideal.span {1 - e (eqv i).1}), Q.IsMaximal →
        Q = (eqv i).1.map (Ideal.Quotient.mk _) := by
      intro Q hQ
      have := hQ
      have hQ' : (Q.comap (Ideal.Quotient.mk (Ideal.span {1 - e (eqv i).1}))).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      obtain ⟨ψ, hψ⟩ := hmax _ hQ'
      have hin : 1 - e (eqv i).1 ∈ Q.comap (Ideal.Quotient.mk (Ideal.span {1 - e (eqv i).1})) := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))]
        exact Q.zero_mem
      rw [← hψ] at hin
      have hψM := (hmem ψ).1 hin
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, ← hψ, hψM]
    exact IsLocalRing.of_unique_max_ideal
      ⟨Q0, hQ0, fun Q hQ => (hcomap Q hQ).trans (hcomap Q0 hQ0).symm⟩

end GlobalTheory
end
