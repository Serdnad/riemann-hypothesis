module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle004
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedGainRapidDecay
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle005
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle001
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle001
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle007
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
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

@[expose] public section

section

open Matrix

theorem _root_.GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), IsUnit G.det → ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ (u : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ), uᴴ * G * u = G → δ ≤ δ₁ → (∀ i j, ‖(u - 1) i j‖ ≤ δ) → ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧ NormedSpace.exp X = u ∧ ∀ i j, ‖X i j‖ ≤ C * δ := by
  first | exact @GlobalTheory.UnitaryLog.exists_log_unitary | exact GlobalTheory.UnitaryLog.exists_log_unitary | (intros; apply GlobalTheory.UnitaryLog.exists_log_unitary <;> assumption)
end

section

open Finset

theorem _root_.GlobalTheory.T.exists_rapid_decay_of_iterated_gain : ∀ (G ι : Type) (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ)) (Dr : ι → (G → ℂ) → G → ℂ) (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ → (∀ g, 1 ≤ q g) → (∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒) → (∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ b ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G, (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ, (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i)) → ∀ A N : ℕ, ∃ (L : Finset (List ι)) (C' : ℝ), (∀ l ∈ L, ∀ i ∈ l, i ∈ B) ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ L, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) → ∀ g, ‖ψ g‖ * q g ^ N ≤ C' * ∑ l ∈ L, c l := by
  first | exact @GlobalTheory.iterated_gain_rapid_decay | exact GlobalTheory.iterated_gain_rapid_decay | (intros; apply GlobalTheory.iterated_gain_rapid_decay <;> assumption)
end

section

open MeasureTheory Classical

theorem _root_.GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul : ∀ (k : Type) [MeasurableSpace k] [Zero k] (ν : Measure k) [SigmaFinite ν] (I : Type) [Fintype I] (P Q R : I → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R], (∀ i, R i ↔ P i ∧ ¬ Q i) → (∀ i, Q i → P i) → ∀ (s : Set k), MeasurableSet s → ν s ≠ ⊤ → ∀ (G : (I → k) → ℂ), (∀ m : I → k, G m = (if ∀ i, Q i → m i ∈ s then (1 : ℂ) else 0) * G (fun i => if Q i then 0 else m i)) → ∫ e : {i // P i} → k, G (fun i => if h : P i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) = (((ν s).toReal ^ Fintype.card {i // Q i} : ℝ) : ℂ) * ∫ e : {i // R i} → k, G (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.BlockFubini.integral_block_indicator | exact GlobalTheory.BlockFubini.integral_block_indicator | (intros; apply GlobalTheory.BlockFubini.integral_block_indicator <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin

namespace GlobalTheory

theorem unipotent_upper_inv_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  intro N C
  refine ⟨(Nat.factorial N : ℝ) * (max C 1) ^ N, ?_⟩
  intro n hd hl hb
  have htri : n.BlockTriangular id := fun i j h => hl i j h
  have hdet : n.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]; simp [hd]
  have hu : IsUnit n.det := by rw [hdet]; exact isUnit_one
  refine ⟨n⁻¹, Matrix.nonsing_inv_mul n hu, Matrix.mul_nonsing_inv n hu, ?_, ?_⟩
  · intro i j h
    letI := Matrix.invertibleOfIsUnitDet n hu
    exact Matrix.blockTriangular_inv_of_blockTriangular htri h
  · intro i j
    have hinv : n⁻¹ = n.adjugate := by rw [Matrix.inv_def, hdet]; simp
    rw [hinv, Matrix.adjugate_apply]
    have key := Matrix.det_le (abv := AbsoluteValue.abs) (x := max C 1)
      (A := n.updateRow j (Pi.single i 1)) ?_
    · simpa using key
    · intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self, Pi.single_apply]
        split_ifs <;> simp
      · rw [Matrix.updateRow_ne hk]
        exact le_trans (hb k l) (le_max_left _ _)

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.FixedRoots

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental k c) :
    ∃ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) ∧ σ c = c + 1 := by
  first
  | exact @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | (apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one ..)

theorem mem_of_forall_ringEquiv_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (k : Subfield Ω) (c : Ω) (hfix : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → σ c = c) : c ∈ k := by
  by_cases hc : Transcendental k c
  · exfalso
    obtain ⟨σ, hσk, hσc⟩ := exists_ringEquiv_add_one k c hc
    have := hfix σ hσk
    rw [hσc] at this
    simp at this
  · have hcA : IsAlgebraic k c := by simpa [Transcendental] using hc
    have hzA : c ∈ algebraicClosure k Ω := (mem_algebraicClosure_iff).2 hcA
    have : IsGalois k (algebraicClosure k Ω) := inferInstance
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by
        intro σ₀
        obtain ⟨σ, hσ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀
        apply Subtype.ext
        rw [← hσ]
        exact hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))
    have : ((r : k) : Ω) = c := congrArg Subtype.val hr
    rw [← this]
    exact r.2

end GlobalTheory.FixedRoots
end

section


theorem _root_.GlobalTheory.T.exists_hermitian_two_det_ne_zero : ∀ (E κ : Type) [Field E] [CharZero E] [Field κ] (σ : E →+* E) (φ : E →+* κ) (δ : E), δ ≠ 0 → σ δ = -δ → ∀ (n : ℕ) (c d y c' d' y' : Matrix (Fin n) (Fin n) κ), (c * y + d).det ≠ 0 → (c' * y' + d').det ≠ 0 → ∃ x : Matrix (Fin n) (Fin n) E, x.map σ = x.transpose ∧ (c * x.map φ + d).det ≠ 0 ∧ (c' * x.transpose.map φ + d').det ≠ 0 := by
  first | exact @GlobalTheory.exists_hermitian_det_ne_zero_two | exact GlobalTheory.exists_hermitian_det_ne_zero_two | (intros; apply GlobalTheory.exists_hermitian_det_ne_zero_two <;> assumption)
end

section


theorem _root_.GlobalTheory.T.matrix_field_stableRange_one_det_ne_zero : ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ), c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 := by
  first | exact @GlobalTheory.matrix_stableRange_one' | exact GlobalTheory.matrix_stableRange_one' | (intros; apply GlobalTheory.matrix_stableRange_one' <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.map_restrict_isHaar_of_open_product_compact : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by
  first | exact @GlobalTheory.ChainOnto.map_restrict_isHaar | exact GlobalTheory.ChainOnto.map_restrict_isHaar | (intros; apply GlobalTheory.ChainOnto.map_restrict_isHaar <;> assumption)
end

section

open ValuativeRel GlobalTheory.SplitWeil Matrix

namespace GlobalTheory

theorem exists_finite_integer_residues (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (hn : 0 < n) :
    ∃ (ι : Type) (_ : Finite ι) (x : ι → k), (∀ i, x i ∈ 𝒪[k]) ∧
      ∀ y ∈ 𝒪[k], ∃ i, ∃ u ∈ 𝒪[k], y = x i + (n : k) * u := by
  let U : Set k := ((𝒪[k] : Subring k) : Set k)
  have hUo : IsOpen U := Valuation.isOpen_integer
  have hUc : IsCompact U := isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[k])
  have hc : (n : k) ≠ 0 := by exact_mod_cast hn.ne'
  let V : U → Set k := fun x => (fun y => (y - (x : k)) * (n : k)⁻¹) ⁻¹' U
  have hVo : ∀ x, IsOpen (V x) := fun x =>
    hUo.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  have hcov : U ⊆ ⋃ x, V x := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    show (y - y) * (n : k)⁻¹ ∈ U
    rw [sub_self, zero_mul]
    exact (𝒪[k]).zero_mem
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover V hVo hcov
  refine ⟨t, inferInstance, fun i => ((i : U) : k), fun i => (i : U).2, ?_⟩
  intro y hy
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hxt, hyx⟩ := this
  refine ⟨⟨x, hxt⟩, (y - (x : k)) * (n : k)⁻¹, hyx, ?_⟩
  field_simp
  ring

theorem matrix_integers_mod_nat_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (n : ℕ), 0 < n →
    ∃ R : Set (Matrix Y Y' k), R.Finite ∧ ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) →
      ∃ s ∈ R, ∃ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) ∧ t = s + n • u := by
  intro k _ _ _ _ _ Y Y' _ _ n hn
  obtain ⟨ι, hι, x, -, hx⟩ := exists_finite_integer_residues k n hn
  refine ⟨Set.range (fun f : Y → Y' → ι => Matrix.of fun r q => x (f r q)), Set.finite_range _, ?_⟩
  intro t ht
  have key := fun r q => hx (t r q) (ht r q)
  choose f u hu hf using key
  refine ⟨Matrix.of fun r q => x (f r q), ⟨f, rfl⟩, Matrix.of fun r q => u r q, hu, ?_⟩
  ext r q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
  exact hf r q

end GlobalTheory
end

section

open ValuativeRel NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.valued_v_map_irreducible_eq_ofAdd_neg_one : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  first | exact @GlobalTheory.adicCompletion_valuation_map_uniformiser | exact GlobalTheory.adicCompletion_valuation_map_uniformiser | (intros; apply GlobalTheory.adicCompletion_valuation_map_uniformiser <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_orthogonal_idempotents_of_sum_mul_eq_one' : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (f s : ι → NumberField.AdeleRing (NumberField.RingOfIntegers F) F), ∑ i, s i * f i = 1 → ∃ e t : ι → NumberField.AdeleRing (NumberField.RingOfIntegers F) F, ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∀ i, t i * f i = e i := by
  first | exact @GlobalTheory.AdeleIdempotents.exists_orthogonal_idempotents_of_sum_mul_eq_one | exact GlobalTheory.AdeleIdempotents.exists_orthogonal_idempotents_of_sum_mul_eq_one | (intros; apply GlobalTheory.AdeleIdempotents.exists_orthogonal_idempotents_of_sum_mul_eq_one <;> assumption)
end
