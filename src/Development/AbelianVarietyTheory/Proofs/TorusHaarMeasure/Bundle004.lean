module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory
namespace HypRot

variable {r : ℕ}

noncomputable def offN (j k : Fin r) (u : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.single j k u + Matrix.single k j (star u)

noncomputable def projP (j k : Fin r) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.single j j 1 + Matrix.single k k 1

noncomputable def rot (j k : Fin r) (u : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + (1 / 4 : ℂ) • projP j k + (3 / 4 : ℂ) • offN j k u

lemma offN_neg (j k : Fin r) (u : ℂ) : offN j k (-u) = - offN j k u := by
  simp only [offN, star_neg, Matrix.single_neg, neg_add]

lemma offN_sq {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    offN j k u * offN j k u = projP j k := by
  have hu' : star u * u = 1 := by rw [mul_comm]; exact hu
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, hu, hu',
    zero_add, add_zero]
  exact add_comm _ _

lemma projP_offN {j k : Fin r} (h : j ≠ k) (u : ℂ) :
    projP j k * offN j k u = offN j k u := by
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, one_mul,
    zero_add, add_zero]

lemma offN_projP {j k : Fin r} (h : j ≠ k) (u : ℂ) :
    offN j k u * projP j k = offN j k u := by
  simp only [offN, projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true,
    mul_one, zero_add, add_zero]
  exact add_comm _ _

lemma projP_sq {j k : Fin r} (h : j ≠ k) : projP j k * projP j k = projP j k := by
  simp only [projP, add_mul, mul_add, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h, h.symm, ne_eq, not_false_eq_true, one_mul,
    zero_add, add_zero]

lemma rot_mul_neg {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    rot j k u * rot j k (-u) = 1 := by
  have hPP := projP_sq h
  have hPN := projP_offN h u
  have hNP := offN_projP h u
  have hNN := offN_sq h hu
  simp only [rot, offN_neg, smul_neg, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, mul_neg, hPP, hPN, hNP, hNN]
  module

lemma rot_sq_sub {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    offN j k u = (4 / 15 : ℂ) • (rot j k u * rot j k u - rot j k (-u) * rot j k (-u)) := by
  have hPP := projP_sq h
  have hPN := projP_offN h u
  have hNP := offN_projP h u
  have hNN := offN_sq h hu
  simp only [rot, offN_neg, smul_neg, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, mul_neg, neg_mul, hPP, hPN, hNP, hNN]
  module

lemma rot_inv {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    (rot j k u)⁻¹ = rot j k (-u) := Matrix.inv_eq_right_inv (rot_mul_neg h hu)

lemma rot_det {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    (rot j k u).det ≠ 0 := (Matrix.isUnit_det_of_right_inverse (rot_mul_neg h hu)).ne_zero

lemma rot_herm (j k : Fin r) (u : ℂ) : (rot j k u).IsHermitian := by
  unfold Matrix.IsHermitian
  simp only [rot, offN, projP, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_single, star_star, star_one, smul_add]
  have h4 : star (1 / 4 : ℂ) = 1 / 4 := by simp
  have h34 : star (3 / 4 : ℂ) = 3 / 4 := by simp
  rw [h4, h34]
  abel

private lemma diagonal_mul_single (d : Fin r → ℂ) (i j : Fin r) (c : ℂ) :
    Matrix.diagonal d * Matrix.single i j c = Matrix.single i j (d i * c) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

private lemma single_mul_diagonal (d : Fin r → ℂ) (i j : Fin r) (c : ℂ) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.single i j (c * d j) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

lemma diag_rot {j k : Fin r} (d : Fin r → ℂ) (hd : d j = - d k) (u : ℂ) :
    Matrix.diagonal d * rot j k u = rot j k (-u) * Matrix.diagonal d := by
  simp only [rot, offN, projP, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, diagonal_mul_single, single_mul_diagonal, star_neg, hd]
  simp only [mul_one, one_mul, neg_mul, mul_neg, neg_neg, mul_comm u (d k), mul_comm (star u) (d k)]

lemma rot_unitary {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1)
    (d : Fin r → ℂ) (hd : d j = - d k) :
    (rot j k u)ᵀ * Matrix.diagonal d * (rot j k u).map (starRingEnd ℂ) = Matrix.diagonal d := by
  have hT : (rot j k u)ᵀ = rot j k (star u) := by
    simp only [rot, offN, projP, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_single, star_star, smul_add]
    abel
  have hC : (rot j k u).map (starRingEnd ℂ) = (rot j k u)ᵀ := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    exact (rot_herm j k u).apply b a
  have hu' : star u * star (star u) = 1 := by rw [star_star, mul_comm]; exact hu
  rw [hC, hT, Matrix.mul_assoc, diag_rot d hd, ← Matrix.mul_assoc, rot_mul_neg h hu',
    Matrix.one_mul]

end HypRot


open HypRot in
theorem exists_finite_symmetric_irreducible_rotations :
    (∀ (r p : ℕ), 0 < p → p < r → ∀ W : Submodule ℂ (Fin r → ℂ), (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W, (Matrix.single j k (1 : ℂ)).mulVec v ∈ W ∧ (Matrix.single k j (1 : ℂ)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by
  intro H r p hp hpr
  classical
  have hne : ∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → j ≠ k := by
    intro j k hj hk e
    have := congrArg Fin.val e
    omega
  have hUs : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ),
      u * star u = 1 ∧ -u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;>
      simp [Complex.ext_iff]
  refine ⟨((Finset.univ.filter fun jk : Fin r × Fin r => (jk.1 : ℕ) < p ∧ p ≤ (jk.2 : ℕ)) ×ˢ
      ({1, -1, Complex.I, -Complex.I} : Finset ℂ)).image (fun x => rot x.1.1 x.1.2 x.2),
      ?_, ?_, ?_, ?_⟩
  · refine ⟨rot ⟨0, by omega⟩ ⟨p, hpr⟩ 1, Finset.mem_image.mpr ⟨((⟨0, by omega⟩, ⟨p, hpr⟩), 1), ?_, rfl⟩⟩
    simp [hp]
  · intro a ha
    obtain ⟨⟨⟨j, k⟩, u⟩, hx, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨hj, hk⟩, hu⟩ := hx
    refine ⟨rot_herm j k u, rot_det (hne j k hj hk) (hUs u hu).1, ?_⟩
    rw [rot_inv (hne j k hj hk) (hUs u hu).1]
    exact Finset.mem_image.mpr ⟨((j, k), -u), by simp [hj, hk, (hUs u hu).2], rfl⟩
  · intro W hW
    apply H r p hp hpr W
    intro j k hj hk v hv
    have hjk := hne j k hj hk
    have hmem : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ), rot j k u ∈
        ((Finset.univ.filter fun jk : Fin r × Fin r => (jk.1 : ℕ) < p ∧ p ≤ (jk.2 : ℕ)) ×ˢ
        ({1, -1, Complex.I, -Complex.I} : Finset ℂ)).image (fun x => rot x.1.1 x.1.2 x.2) := by
      intro u hu
      exact Finset.mem_image.mpr ⟨((j, k), u), by simp [hj, hk, hu], rfl⟩
    have hN : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ), (offN j k u).mulVec v ∈ W := by
      intro u hu
      rw [rot_sq_sub hjk (hUs u hu).1, Matrix.smul_mulVec, Matrix.sub_mulVec]
      exact W.smul_mem _ (W.sub_mem (hW _ (hmem u hu) v hv) (hW _ (hmem _ (hUs u hu).2) v hv))
    have h1 : (1 : ℂ) ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by simp
    have hI : Complex.I ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by simp
    have hII : Complex.I * star Complex.I = 1 := by
      rw [Complex.star_def, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg]
    have hsI : Complex.I • offN j k Complex.I = -Matrix.single j k (1 : ℂ) + Matrix.single k j 1 := by
      rw [offN, smul_add, Matrix.smul_single, Matrix.smul_single, smul_eq_mul, smul_eq_mul,
        Complex.I_mul_I, hII, Matrix.single_neg]
    have h1' : offN j k (1 : ℂ) = Matrix.single j k 1 + Matrix.single k j 1 := by
      rw [offN, star_one]
    have e1 : Matrix.single j k (1 : ℂ) = (1 / 2 : ℂ) • (offN j k 1 - Complex.I • offN j k Complex.I) := by
      rw [hsI, h1']
      module
    have e2 : Matrix.single k j (1 : ℂ) = (1 / 2 : ℂ) • (offN j k 1 + Complex.I • offN j k Complex.I) := by
      rw [hsI, h1']
      module
    constructor
    · rw [e1, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
      exact W.smul_mem _ (W.sub_mem (hN 1 h1) (W.smul_mem _ (hN _ hI)))
    · rw [e2, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec]
      exact W.smul_mem _ (W.add_mem (hN 1 h1) (W.smul_mem _ (hN _ hI)))
  · intro a ha
    obtain ⟨⟨⟨j, k⟩, u⟩, hx, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨hj, hk⟩, hu⟩ := hx
    have hjk := hne j k hj hk
    have hd : (fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1) j =
        -(fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1) k := by
      simp [hj, not_lt.mpr hk]
    refine ⟨rot_unitary hjk (hUs u hu).1 _ hd, Matrix.diagonal fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1, ?_, ?_⟩
    · rw [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> simp
    · rw [rot_inv hjk (hUs u hu).1]
      exact diag_rot _ hd u

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory


open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
theorem _root_.GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) := by
  intro G _ _ _ _ _ _ _ _ Γ ⟨U, hU, hΓU⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨t, htU, ht, h1t⟩ := mem_nhds_iff.1 hU
    have hopen : IsOpen ({1} : Set Γ) := by
      rw [isOpen_induced_iff]
      refine ⟨t, ht, ?_⟩
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact Subtype.ext (hΓU x x.2 (htU hx))
      · rintro rfl
        exact h1t
    haveI : DiscreteTopology Γ := discreteTopology_of_isOpen_singleton_one hopen
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_split hU
    let C : G → Set G := fun x => {y | y * x⁻¹ ∈ V ∧ x * y⁻¹ ∈ V}
    have hCo : ∀ x, IsOpen (C x) := fun x =>
      (hVo.preimage (continuous_id.mul continuous_const)).inter
        (hVo.preimage (continuous_const.mul continuous_inv))
    have hCx : ∀ x, x ∈ C x := fun x => by simp [C, hV1]
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable C hCo
    have hTne : T.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h1 : (1 : G) ∈ ⋃ x, C x := Set.mem_iUnion.2 ⟨1, hCx 1⟩
      rw [← hT, h] at h1
      simp at h1
    obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
    let W : ℕ → Set G := fun n => C (c n)
    have hWo : ∀ n, IsOpen (W n) := fun n => hCo _
    have hcover : ∀ x, ∃ n, x ∈ W n := by
      intro x
      have hx : x ∈ ⋃ y ∈ T, C y := by rw [hT]; exact Set.mem_iUnion.2 ⟨x, hCx x⟩
      rw [hc] at hx
      simp only [Set.biUnion_range, Set.mem_iUnion] at hx
      exact hx
    have hsep : ∀ n (x : G) (γ : Γ), x ∈ W n → (γ : G) * x ∈ W n → γ = 1 := by
      intro n x γ hx hγx
      have h := hVU _ hγx.1 _ hx.2
      have he : (γ : G) * x * (c n)⁻¹ * (c n * x⁻¹) = γ := by group
      rw [he] at h
      exact Subtype.ext (hΓU γ γ.2 h)
    let S : ℕ → Set G := fun m => ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' W m
    have hSo : ∀ m, IsOpen (S m) := fun m =>
      isOpen_iUnion fun γ => (hWo m).preimage (continuous_const.mul continuous_id)
    have hmemS : ∀ m x, x ∈ S m ↔ ∃ γ : Γ, (γ : G) * x ∈ W m := fun m x => by
      simp only [S, Set.mem_iUnion, Set.mem_preimage]
    refine ⟨⋃ n : ℕ, W n \ ⋃ m : Fin n, S m, ?_, ?_⟩
    · exact MeasurableSet.iUnion fun n =>
        (hWo n).measurableSet.diff (MeasurableSet.iUnion fun m => (hSo m).measurableSet)
    · intro g
      have hmemF : ∀ y, y ∈ (⋃ n : ℕ, W n \ ⋃ m : Fin n, S m) ↔
          ∃ n, y ∈ W n ∧ ∀ m < n, y ∉ S m := by
        intro y
        simp only [Set.mem_iUnion, Set.mem_diff, not_exists]
        constructor
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m hm' => hm ⟨m, hm'⟩⟩
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m => hm m m.2⟩
      have hex : ∃ n, g ∈ S n := by
        obtain ⟨n, hn⟩ := hcover g
        exact ⟨n, (hmemS n g).2 ⟨1, by simpa using hn⟩⟩
      classical
      obtain ⟨γ, hγ⟩ := (hmemS _ g).1 (Nat.find_spec hex)
      refine ⟨γ, (hmemF _).2 ⟨Nat.find hex, hγ, fun m hm hS => ?_⟩, ?_⟩
      · obtain ⟨δ, hδ⟩ := (hmemS m _).1 hS
        exact Nat.find_min hex hm ((hmemS m g).2 ⟨δ * γ, by simpa [mul_assoc] using hδ⟩)
      · intro γ' hγ'
        obtain ⟨k, hk, hkS⟩ := (hmemF _).1 hγ'
        have hkN : k = Nat.find hex := by
          refine le_antisymm ?_ (Nat.find_min' hex ((hmemS k g).2 ⟨γ', hk⟩))
          by_contra hlt
          push_neg at hlt
          exact hkS _ hlt ((hmemS _ _).2 ⟨γ * γ'⁻¹, by simpa [mul_assoc] using hγ⟩)
        rw [hkN] at hk
        have h1 := hsep _ _ (γ' * γ⁻¹) hγ (by simpa [mul_assoc] using hk)
        exact mul_inv_eq_one.1 h1

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem finite_covolume_of_drift_function :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y) (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) → (∀ s y y', R y y' → R (t s y) (t s y')) → (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') → ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) → Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b → (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) → ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (F : Set G), MeasurableSet F → (∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ h : G, ν.map (fun g => g * h) = ν → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → ∫⁻ g in F, φ (g * h) ∂ν = ∫⁻ g in F, φ g ∂ν) ∧ ∀ K : Set G, MeasurableSet K → ν (F ∩ {g | ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k}) ≤ ν K) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) (σ : Type) [Fintype σ] [Nonempty σ] (h : σ → G) (f : G → ℝ) (c b : ℝ), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ s, ∃ k : G, k * h s = (h s)⁻¹ * k) → Measurable f → (∀ g, 0 ≤ f g) → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → 0 ≤ c → c < 1 → 0 ≤ b → (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) → (∀ M : ℝ, ∃ K : Set G, IsCompact K ∧ ∀ g, f g ≤ M → ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) → ∃ Ω : Set G, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : G, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w) := by
  intro h₁ h₂ h₃ h₄ G _ _ _ _ _ _ _ _ ν _ Γ σ _ _ h f c b hΓ hh hf hf0 hfΓ hc0 hc1 hb hd hK
  obtain ⟨hcount, F, hF, hFu⟩ := h₂ G Γ hΓ
  obtain ⟨hinv, hle⟩ := h₄ G ν Γ F hF hFu
  obtain ⟨M, hM⟩ := h₁ G σ (ν.restrict F) (fun y y' => ∃ γ ∈ Γ, y' = γ * y)
    (fun s g => g * h s) f c b (fun s => measurable_mul_const (h s))
    (by
      rintro s y y' ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, mul_assoc _ _ _⟩)
    (by
      intro φ hφ hR s
      obtain ⟨k, hk⟩ := hh s
      exact hinv (h s) (h₃ G ν (h s) k hk) φ hφ
        (fun γ hγ g => (hR g (γ * g) ⟨γ, hγ, rfl⟩).symm))
    hf hf0
    (by
      rintro y y' ⟨γ, hγ, rfl⟩
      exact (hfΓ γ hγ y).symm)
    hc0 hc1 hb hd
  obtain ⟨K, hKc, hKf⟩ := hK M
  refine ⟨F, hF, ?_, ?_⟩
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply' hF] at hM
    have h5 : ν ({y | f y ≤ M} ∩ F) ≤ ν K := by
      refine le_trans (measure_mono ?_) (hle K hKc.measurableSet)
      rintro g ⟨hg, hgF⟩
      exact ⟨hgF, hKf g hg⟩
    refine lt_of_le_of_lt hM (ENNReal.mul_lt_top (by simp) ?_)
    exact lt_of_le_of_lt h5 hKc.measure_lt_top
  · intro g
    obtain ⟨γ, hγ, -⟩ := hFu g
    exact ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, γ * g, hγ, by group⟩

end GlobalTheory
end

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem haar_map_mul_right_of_conj_inv :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) := by
  intro G _ _ _ _ _ _ _ _ ν _ h k hk
  have e : h * (k * h) = k := by rw [hk, mul_inv_cancel_left]
  have e2 := congrArg Measure.modularCharacterFun e
  rw [Measure.modularCharacterFun_map_mul, Measure.modularCharacterFun_map_mul] at e2
  have hk0 : (0 : ℝ) < Measure.modularCharacterFun k := Measure.modularCharacterFun_pos k
  have hh0 : (0 : ℝ) < Measure.modularCharacterFun h := Measure.modularCharacterFun_pos h
  have e3 : (Measure.modularCharacterFun h : ℝ) *
      ((Measure.modularCharacterFun k : ℝ) * Measure.modularCharacterFun h) =
      Measure.modularCharacterFun k := by exact_mod_cast e2
  have e4 : (Measure.modularCharacterFun h : ℝ) * Measure.modularCharacterFun h = 1 := by
    apply mul_left_cancel₀ hk0.ne'
    linarith
  have e5 : (Measure.modularCharacterFun h : ℝ) = 1 := by nlinarith
  have e6 : Measure.modularCharacterFun h = 1 := by exact_mod_cast e5
  have hm : ν.map (fun g => g * h) = Measure.modularCharacterFun h • ν := by
    rw [Measure.modularCharacterFun_eq_haarScalarFactor ν h]
    exact Measure.isMulLeftInvariant_eq_smul _ ν
  rw [hm, e6, one_smul]

end GlobalTheory
end
