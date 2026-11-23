module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.VolSemiDirect.W

open MeasureTheory

theorem exists_sfd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Λ : Subgroup G)
    [DiscreteTopology Λ] :
    ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ ∀ x : G, ∃! γ : Λ, γ • x ∈ 𝓕 := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Λ))
  have hV1 : ∀ γ : Λ, (γ : G) ∈ V ↔ γ = 1 := fun γ => Set.ext_iff.mp hV γ
  have h1V : (1 : G) ∈ V := (hV1 1).mpr rfl
  obtain ⟨W, hWo, hW1, hWV⟩ := exists_open_nhds_one_split (hVo.mem_nhds h1V)
  obtain ⟨U, hUo, hU1, hUinv, hUV⟩ : ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ (∀ g ∈ U, g⁻¹ ∈ U) ∧
      ∀ a ∈ U, ∀ b ∈ U, a * b⁻¹ ∈ V :=
    ⟨W ∩ (fun g => g⁻¹) ⁻¹' W, hWo.inter (hWo.preimage continuous_inv), ⟨hW1, by simpa using hW1⟩,
      fun g hg => ⟨hg.2, by simpa using hg.1⟩, fun a ha b hb => hWV a ha.1 _ hb.2⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq G

  have hB : ∀ x : G, ∃ n, x * (d n)⁻¹ ∈ U := by
    intro x
    obtain ⟨n, hn⟩ := hd.exists_mem_open
      (hUo.preimage (continuous_id.mul continuous_const) : IsOpen ((fun y => y * x⁻¹) ⁻¹' U))
      ⟨x, by simpa using hU1⟩
    refine ⟨n, ?_⟩
    have := hUinv _ hn
    simpa [mul_inv_rev] using this

  have hBu : ∀ (n : ℕ) (γ γ' : Λ) (x : G), (γ : G) * x * (d n)⁻¹ ∈ U →
      (γ' : G) * x * (d n)⁻¹ ∈ U → γ = γ' := by
    intro n γ γ' x h h'
    have hm := hUV _ h _ h'
    have : ((γ * γ'⁻¹ : Λ) : G) ∈ V := by
      convert hm using 1
      push_cast
      group
    rw [hV1, mul_inv_eq_one] at this
    exact this

  obtain ⟨S, hS, hSo⟩ : ∃ S : ℕ → Set G, (∀ m x, x ∈ S m ↔ ∃ γ : Λ, (γ : G) * x * (d m)⁻¹ ∈ U) ∧
      ∀ m, IsOpen (S m) :=
    ⟨fun m => ⋃ γ : Λ, (fun x => (γ : G) * x * (d m)⁻¹) ⁻¹' U, fun m x => by simp,
      fun m => isOpen_iUnion fun γ =>
        hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)⟩
  have hinv : ∀ (γ : Λ) (y : G) (m : ℕ), (γ : G) * y ∈ S m ↔ y ∈ S m := by
    intro γ y m
    rw [hS, hS]
    constructor
    · rintro ⟨δ, hδ⟩
      exact ⟨δ * γ, by push_cast; simpa [mul_assoc] using hδ⟩
    · rintro ⟨δ, hδ⟩
      exact ⟨δ * γ⁻¹, by push_cast; simpa [mul_assoc] using hδ⟩
  obtain ⟨F, hF, hFm⟩ : ∃ F : Set G, (∀ y, y ∈ F ↔ ∃ n, y * (d n)⁻¹ ∈ U ∧ ∀ m < n, y ∉ S m) ∧
      MeasurableSet F := by
    refine ⟨⋃ n, ((fun x => x * (d n)⁻¹) ⁻¹' U \ ⋃ m, ⋃ (_ : m < n), S m), fun y => ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_diff, Set.mem_preimage, not_exists]
    · exact MeasurableSet.iUnion fun n =>
        (hUo.preimage (continuous_id.mul continuous_const)).measurableSet.diff
          (isOpen_iUnion fun m => isOpen_iUnion fun _ => hSo m).measurableSet
  refine ⟨F, hFm, fun x => ?_⟩
  have hex : ∃ n, x ∈ S n := by
    obtain ⟨n, hn⟩ := hB x
    exact ⟨n, (hS n x).mpr ⟨1, by simpa using hn⟩⟩
  classical
  obtain ⟨n0, hn0x, hmin⟩ : ∃ n0, x ∈ S n0 ∧ ∀ m < n0, x ∉ S m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  obtain ⟨γ, hγ⟩ := (hS n0 x).mp hn0x
  refine ⟨γ, ?_, ?_⟩
  · change (γ : G) * x ∈ F
    rw [hF]
    exact ⟨n0, hγ, fun m hm h => hmin m hm ((hinv γ x m).mp h)⟩
  · intro γ' hγ'
    change (γ' : G) * x ∈ F at hγ'
    rw [hF] at hγ'
    obtain ⟨n, hn, hnmin⟩ := hγ'
    have hxn : x ∈ S n := (hS n x).mpr ⟨γ', hn⟩
    have hn0 : n = n0 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        exact hnmin n0 hlt ((hinv γ' x n0).mpr hn0x)
      · exact not_lt.mp fun h => hmin n h hxn
    rw [hn0] at hn
    exact hBu n0 γ' γ x hn hγ

theorem exists_fd {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Λ : Subgroup G)
    [DiscreteTopology Λ] :
    ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ ∀ μ : Measure G, IsFundamentalDomain Λ 𝓕 μ := by
  obtain ⟨F, hF, hex⟩ := exists_sfd Λ
  exact ⟨F, hF, fun μ => IsFundamentalDomain.mk' hF.nullMeasurableSet hex⟩

end PI.VolSemiDirect.W
end
end

section

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open MeasureTheory Measure
open scoped NNReal

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

def phi (X : GL (Fin k) A) : (Fin k → A) ≃ₜ+ (Fin k → A) where
  toFun v := (X : Matrix (Fin k) (Fin k) A).mulVec v
  invFun v := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).mulVec v
  left_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv v := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_add' v w := Matrix.mulVec_add _ v w
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem phi_apply (X : GL (Fin k) A) (v : Fin k → A) :
    phi X v = (X : Matrix (Fin k) (Fin k) A).mulVec v := rfl

def modM (X : GL (Fin k) A) : ℝ≥0 := addEquivAddHaarChar (phi X)

theorem phi_mul (X Y : GL (Fin k) A) : phi (X * Y) = (phi Y).trans (phi X) := by
  apply ContinuousAddEquiv.ext
  intro v
  simp only [ContinuousAddEquiv.trans_apply, phi_apply, Units.val_mul, Matrix.mulVec_mulVec]

theorem modM_mul (X Y : GL (Fin k) A) : modM (X * Y) = modM X * modM Y := by
  simp only [modM, phi_mul, addEquivAddHaarChar_trans, mul_comm]

theorem modM_one : modM (1 : GL (Fin k) A) = 1 := by
  have h : phi (1 : GL (Fin k) A) = ContinuousAddEquiv.refl _ := by
    apply ContinuousAddEquiv.ext
    intro v
    simp [phi_apply]
  simp only [modM, h, addEquivAddHaarChar_refl]

theorem modM_inv (X : GL (Fin k) A) : modM X⁻¹ = (modM X)⁻¹ := by
  have h : modM X⁻¹ * modM X = 1 := by rw [← modM_mul, inv_mul_cancel, modM_one]
  exact eq_inv_of_mul_eq_one_left h

theorem map_phi_of_modM (X : GL (Fin k) A) (hX : modM X = 1) (μ : Measure (Fin k → A))
    [μ.IsAddHaarMeasure] : μ.map (phi X) = μ := by
  have h := addEquivAddHaarChar_smul_map μ (phi X)
  rwa [show addEquivAddHaarChar (phi X) = modM X from rfl, hX, one_smul] at h

theorem modM_of_map (X : GL (Fin k) A) (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure]
    (h : μ.map (phi X) = μ) : modM X = 1 := by
  have h1 := addEquivAddHaarChar_smul_map μ (phi X)
  rw [h] at h1
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : Fin k → A)
  have hpos : μ K ≠ 0 := (measure_pos_of_mem_nhds μ hKn).ne'
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun ν : Measure (Fin k → A) => ν K) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((modM X : ℝ≥0) : ENNReal) = 1 := by
    have h4 : (modM X : ENNReal) * μ K / μ K = 1 * μ K / μ K := by rw [one_mul]; exact congrArg (· / μ K) h2
    rwa [ENNReal.mul_div_cancel_right hpos hfin, ENNReal.mul_div_cancel_right hpos hfin] at h4
  exact_mod_cast h3

end Gen

end PI.VolSemiDirect.W.Cj
end
end
