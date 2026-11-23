module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractB
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem sg_diag (σ : E ≃+* E) (u : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) u) = diagT E (Fin n) (sgT σ u) := by
  ext i j
  rw [sg, GeneralLinearGroup.map_apply, val_diagT, val_diagT]
  by_cases h : i = j
  · subst h
    simp [sgT]
  · simp [Matrix.diagonal_apply_ne _ h]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem diag_inj : Function.Injective (diagT E (Fin n)) := by
  intro a b h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h
  simpa [val_diagT] using this

private theorem near_val {r : ValueGroupWithZero E} (hr : r < 1) {s : Fin n → Eˣ} (hs : Near r s) (i : Fin n) :
    valuation E (s i : E) = 1 := by
  have h1 : valuation E ((s i : E) - 1) < valuation E (1 : E) := by
    rw [map_one]
    exact lt_of_le_of_lt (hs i) hr
  have h2 := Valuation.map_add_eq_of_lt_right (valuation E) h1
  simpa using h2

private theorem strict_near {r : ValueGroupWithZero E} (hr : r < 1) {t s : Fin n → Eˣ} (ht : Strict t)
    (hs : Near r s) : Strict (t * s) := by
  have key : ∀ k, valuation E ((t * s) k : E) = valuation E (t k : E) := by
    intro k
    rw [Pi.mul_apply, Units.val_mul, map_mul, near_val hr hs k, mul_one]
  intro i j hij
  rw [key, key]
  exact ht i j hij

private theorem ball_sg {r : ValueGroupWithZero E} {σ : E ≃+* E} (hσ : Isom σ) {a : GL (Fin n) E}
    (ha : a ∈ ball n r) : sg σ a ∈ ball n r := by
  simp only [ball, Set.mem_setOf_eq] at ha ⊢
  intro i j
  have h : ((sg σ a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j
      = σ ((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
    rw [sg, GeneralLinearGroup.map_apply, map_sub]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  rw [h, hσ]
  exact ha i j

private theorem diag_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (hs : Near r s) :
    diagT E (Fin n) s ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases h : i = j
  · subst h
    simpa using hs i
  · simp [Matrix.diagonal_apply_ne _ h, one_apply_ne h]

end

end UpperTheory.Gal.InertialTypesAlt.L

theorem UpperTheory.Gal.InertialTypesAlt.L.suppE :
    UpperTheory.Gal.InertialTypesAlt.L.SuppE := by
  intro E _ _ _ _ n σ q hc r hr0 hr1 A hA
  have hσ : Isom σ := hc.isom
  obtain ⟨K, hK, -, -⟩ := ballSub E n r hr0 hr1
  have bmul : ∀ a ∈ ball n r, ∀ b ∈ ball n r, a * b ∈ ball n r := by
    intro a ha b hb
    rw [← hK] at ha hb ⊢
    exact K.mul_mem ha hb
  have binv : ∀ a ∈ ball n r, a⁻¹ ∈ ball n r := by
    intro a ha
    rw [← hK] at ha ⊢
    exact K.inv_mem ha
  have step : ∀ δ g : GL (Fin n) E, g⁻¹ * δ * sg σ g ∈ UpperTheory.Gal.InertialTypesAlt.L.elemSet r A →
      ∃ k ∈ ball n r, ∃ t ∈ A, ∃ s, UpperTheory.Gal.InertialTypesAlt.L.Near r s ∧
        g⁻¹ * δ * sg σ g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
    intro δ g hg
    obtain ⟨a, ha, b, hb, t, ht, he⟩ := hg
    obtain ⟨k, hk, s, hs, hks⟩ := contractB E n σ hσ t (hA t ht) r hr1 a ha b hb
    exact ⟨k, hk, t, ht, s, hs, he.trans hks⟩
  refine ⟨?_, ?_⟩
  · intro δ g hg
    obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
    refine ⟨g * k⁻¹, t, ht, s, hs, UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs, ?_⟩
    calc (g * k⁻¹)⁻¹ * δ * sg σ (g * k⁻¹)
        = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
          rw [map_mul, map_inv]
          group
      _ = diagT E (Fin n) (t * s) := by
          rw [he]
          group
  · intro δ y d hd hy g
    constructor
    · intro hg
      obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
      have hts : Strict (t * s) := UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs
      have hx : (y⁻¹ * g * k⁻¹)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * g * k⁻¹)
          = diagT E (Fin n) (t * s) := by
        rw [← hy]
        calc (y⁻¹ * g * k⁻¹)⁻¹ * (y⁻¹ * δ * sg σ y) * sg σ (y⁻¹ * g * k⁻¹)
            = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
              rw [map_mul, map_mul, map_inv, map_inv]
              group
          _ = diagT E (Fin n) (t * s) := by
              rw [he]
              group
      obtain ⟨u, hu⟩ := strictNormal E n σ q hc d (t * s) hd hts _ hx
      have h2 : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * s := by
        apply UpperTheory.Gal.InertialTypesAlt.L.diag_inj
        rw [map_mul, map_mul, map_inv, ← UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← hu]
        exact hx
      refine ⟨u, ⟨t, ht, ?_⟩, k, hk, ?_⟩
      · have h3 : d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = s := by
          calc d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = (u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u) / t := by
                simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
            _ = s := by
                rw [h2]
                simp
        rw [h3]
        exact hs
      · rw [← hu]
        group
    · rintro ⟨u, ⟨t, ht, hs⟩, κ, hκ, rfl⟩
      have hid : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) := by
        rw [mul_comm t, div_mul_cancel, div_eq_mul_inv, mul_comm (d * _) u⁻¹, mul_assoc]
      have hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹ := by
        rw [← hy]
        group
      refine ⟨κ⁻¹, binv κ hκ, diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ,
        bmul _ (UpperTheory.Gal.InertialTypesAlt.L.diag_ball hs) _ (UpperTheory.Gal.InertialTypesAlt.L.ball_sg hσ hκ), t, ht, ?_⟩
      rw [hδ]
      calc (y * diagT E (Fin n) u * κ)⁻¹ * (y * diagT E (Fin n) d * (sg σ y)⁻¹)
            * sg σ (y * diagT E (Fin n) u * κ)
          = κ⁻¹ * ((diagT E (Fin n) u)⁻¹ * diagT E (Fin n) d * sg σ (diagT E (Fin n) u)) * sg σ κ := by
            rw [map_mul, map_mul]
            group
        _ = κ⁻¹ * (diagT E (Fin n) t * diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t)) * sg σ κ := by
            rw [UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← map_inv (diagT E (Fin n)) u, ← map_mul, ← map_mul, ← map_mul, hid]
        _ = κ⁻¹ * diagT E (Fin n) t * (diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ) := by
            group
end
end

section

noncomputable section

open ValuativeRel Matrix

namespace UpperTheory.Gal.InertialTypesAlt.L

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isOpen_ball (c : (ValueGroupWithZero k)ˣ) :
    IsOpen {y : k | valuation k y ≤ (c : ValueGroupWithZero k)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨c, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_setOf_eq] at hz hx ⊢
  exact le_trans (Valuation.map_add _ _ _) (max_le hx (le_of_lt hz))

private theorem isIntegral_of_cpt {n : ℕ} (g : GL (Fin n) k)
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) k)))) :
    IsIntegral 𝒪[k] (g : Matrix (Fin n) (Fin n) k) := by
  have hcont : ∀ i j : Fin n, Continuous (fun M : GL (Fin n) k => (M : Matrix (Fin n) (Fin n) k) i j) :=
    fun i j => Units.continuous_val.matrix_elem i j
  set S := ⋃ (i : Fin n) (j : Fin n), (fun M : GL (Fin n) k => (M : Matrix (Fin n) (Fin n) k) i j) ''
    closure (Subgroup.zpowers g : Set (GL (Fin n) k)) with hS
  have hSc : IsCompact S := isCompact_iUnion (fun i => isCompact_iUnion (fun j => hg.image (hcont i j)))
  obtain ⟨c, hc⟩ : ∃ c : (ValueGroupWithZero k)ˣ, S ⊆ {y | valuation k y ≤ (c : ValueGroupWithZero k)} := by
    apply hSc.elim_directed_cover (fun c : (ValueGroupWithZero k)ˣ => {y | valuation k y ≤ (c : ValueGroupWithZero k)})
    · exact fun c => isOpen_ball c
    · intro y _
      rw [Set.mem_iUnion]
      by_cases hy : valuation k y = 0
      · exact ⟨1, by simp [hy]⟩
      · exact ⟨Units.mk0 _ hy, by simp only [Set.mem_setOf_eq, Units.val_mk0, le_refl]⟩
    · intro a b
      rcases le_total (a : ValueGroupWithZero k) b with h | h
      · exact ⟨b, fun y (hy : valuation k y ≤ _) => (le_trans hy h : valuation k y ≤ _), fun y hy => hy⟩
      · exact ⟨a, fun y hy => hy, fun y (hy : valuation k y ≤ _) => (le_trans hy h : valuation k y ≤ _)⟩
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  apply GlobalTheory.isIntegral_matrix_of_pow_bounded (g : Matrix (Fin n) (Fin n) k) a ha0
  intro m i j
  have hmem : ((g ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ S := by
    rw [hS, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨j, g ^ m, subset_closure (Subgroup.npow_mem_zpowers g m), rfl⟩
  have hle : valuation k (((g : Matrix (Fin n) (Fin n) k) ^ m) i j) ≤ (c : ValueGroupWithZero k) := by
    have h1 := hc hmem
    rw [Units.val_pow_eq_pow_val] at h1
    exact h1
  refine ⟨⟨a * ((g : Matrix (Fin n) (Fin n) k) ^ m) i j, ?_⟩, rfl⟩
  show valuation k (a * ((g : Matrix (Fin n) (Fin n) k) ^ m) i j) ≤ 1
  rw [map_mul, ha]
  calc ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) * valuation k (((g : Matrix (Fin n) (Fin n) k) ^ m) i j)
      ≤ ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) * c := by gcongr
    _ = 1 := Units.inv_mul c

private theorem bounded_adjoin {n : ℕ} (N : Matrix (Fin n) (Fin n) k) (hs : N.charpoly.Separable) :
    ∃ c : ValueGroupWithZero k, ∀ g ∈ Algebra.adjoin k {N}, IsIntegral 𝒪[k] g →
      ∀ i j, valuation k (g i j) ≤ c := by
  have hI := Valuation.integer.integers (valuation k)
  exact GlobalTheory.LocBounded.bounded_of_isIntegral_general (valuation k) (fun y => y.2) (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
    (fun x hx => hI.isIntegral_iff_v_le_one.mp hx) N hs

private theorem isCompact_entries (n : ℕ) (c : ValueGroupWithZero k) :
    IsCompact {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} := by
  have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
      {x : k | valuation k x ≤ c}) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k c
  have e : {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} =
      (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ c}) := by
    ext M
    exact ⟨fun hM i _ j _ => hM i j, fun hM i j => hM i trivial j trivial⟩
  rw [e]
  exact h

end UpperTheory.Gal.InertialTypesAlt.L

private theorem isIntegral_mul_of_mem_adjoin_singleton {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (A x y : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Algebra.adjoin k {A}) (hy : y ∈ Algebra.adjoin k {A})
    (hxi : IsIntegral 𝒪[k] x) (hyi : IsIntegral 𝒪[k] y) : IsIntegral 𝒪[k] (x * y) := by
  letI : CommRing (Algebra.adjoin k {A}) := by
    open scoped IsMulCommutative in
      exact inferInstance
  let f : Algebra.adjoin k {A} →ₐ[𝒪[k]] Matrix (Fin n) (Fin n) k :=
    (Algebra.adjoin k {A}).val.restrictScalars 𝒪[k]
  have hinj : Function.Injective f := Subtype.val_injective
  have h1 : IsIntegral 𝒪[k] (⟨x, hx⟩ : Algebra.adjoin k {A}) := (isIntegral_algHom_iff f hinj).mp hxi
  have h2 : IsIntegral 𝒪[k] (⟨y, hy⟩ : Algebra.adjoin k {A}) := (isIntegral_algHom_iff f hinj).mp hyi
  exact (isIntegral_algHom_iff f hinj).mpr (h1.mul h2)

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.cptCpt :
    UpperTheory.Gal.InertialTypesAlt.L.CptCpt := by
  intro k _ _ _ _ n A T hA hT hcomm
  obtain ⟨-, -, hT2, -, hprop⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_holds k n
  haveI := hT2
  obtain ⟨c, hc⟩ := bounded_adjoin (A : Matrix (Fin n) (Fin n) k) hA
  have hΩ := isCompact_entries (k := k) n c
  have hC := hprop _ _ hΩ hΩ
  let K0 : Subgroup (GL (Fin n) k) :=
    { carrier := {g | (g : Matrix (Fin n) (Fin n) k) ∈ Algebra.adjoin k {(A : Matrix (Fin n) (Fin n) k)} ∧
        IsIntegral 𝒪[k] (g : Matrix (Fin n) (Fin n) k) ∧
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Algebra.adjoin k {(A : Matrix (Fin n) (Fin n) k)} ∧
        IsIntegral 𝒪[k] ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)}
      mul_mem' := by
        rintro g h ⟨hg1, hg2, hg3, hg4⟩ ⟨hh1, hh2, hh3, hh4⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Units.val_mul]
          exact Subalgebra.mul_mem _ hg1 hh1
        · rw [Units.val_mul]
          exact isIntegral_mul_of_mem_adjoin_singleton _ _ _ hg1 hh1 hg2 hh2
        · rw [_root_.mul_inv_rev, Units.val_mul]
          exact Subalgebra.mul_mem _ hh3 hg3
        · rw [_root_.mul_inv_rev, Units.val_mul]
          exact isIntegral_mul_of_mem_adjoin_singleton _ _ _ hh3 hg3 hh4 hg4
      one_mem' := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Units.val_one]
          exact Subalgebra.one_mem _
        · rw [Units.val_one]
          exact isIntegral_one
        · rw [inv_one, Units.val_one]
          exact Subalgebra.one_mem _
        · rw [inv_one, Units.val_one]
          exact isIntegral_one
      inv_mem' := by
        rintro g ⟨hg1, hg2, hg3, hg4⟩
        refine ⟨hg3, hg4, ?_, ?_⟩
        · rw [inv_inv]
          exact hg1
        · rw [inv_inv]
          exact hg2 }
  have hsub : (K0 : Set (GL (Fin n) k)) ⊆
      {g | (g : Matrix (Fin n) (Fin n) k) ∈ {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} ∧
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈
          {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c}} := by
    rintro g ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨hc _ hg1 hg2, hc _ hg3 hg4⟩
  have hK1 : IsCompact (K0.topologicalClosure : Set (GL (Fin n) k)) := by
    rw [Subgroup.topologicalClosure_coe]
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  have hgen : ∀ t ∈ T, IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) k))) → t ∈ K0 := by
    intro t ht hcpt
    have hcA : ∀ s ∈ T, (s : Matrix (Fin n) (Fin n) k) * A = A * s := by
      intro s hs
      rw [← Units.val_mul, ← Units.val_mul, (hcomm s hs).eq]
    have hcpt' : IsCompact (closure (Subgroup.zpowers t⁻¹ : Set (GL (Fin n) k))) := by
      rw [Subgroup.zpowers_inv]
      exact hcpt
    exact ⟨GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ _ hA (hcA t ht), isIntegral_of_cpt t hcpt,
      GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ _ hA (hcA t⁻¹ (T.inv_mem ht)), isIntegral_of_cpt t⁻¹ hcpt'⟩
  have hle : GlobalTheory.BCT.cptPart T ≤ T ⊓ K0.topologicalClosure := by
    unfold GlobalTheory.BCT.cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hcpt⟩
    exact ⟨ht, Subgroup.le_topologicalClosure K0 (hgen t ht hcpt)⟩
  have hge : T ⊓ K0.topologicalClosure ≤ GlobalTheory.BCT.cptPart T := GlobalTheory.LocFin.inf_le_cptPart T _ hK1
  rw [le_antisymm hle hge, Subgroup.coe_inf]
  exact hK1.inter_left hT
end
end
