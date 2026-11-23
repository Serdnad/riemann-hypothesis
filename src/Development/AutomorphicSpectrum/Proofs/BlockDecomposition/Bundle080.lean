module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle095
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle047
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Nakayama
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD

@[expose] public section

section

open scoped TensorProduct
open Algebra.TensorProduct (includeRight)

namespace GlobalTheory.CompanionTheory.NormLoc

section

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O']

theorem trace_fixed (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1) (u : O') :
    τ (∑ j ∈ Finset.range ℓ, (τ ^ j) u) = ∑ j ∈ Finset.range ℓ, (τ ^ j) u := by

  rw [map_sum]
  have e := (Finset.sum_range_succ' (fun j => (τ ^ j) u) ℓ).symm.trans
    (Finset.sum_range_succ (fun j => (τ ^ j) u) ℓ)
  rw [hτ, pow_zero] at e
  rw [← add_right_cancel e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

theorem exists_trace_one [IsLocalRing O] [Module.Finite O O'] (ℓ : ℕ) (τ : O' ≃ₐ[O] O')
    (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O'))
    (hdual : ∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) :
    ∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1 := by
  obtain ⟨x, y, hxy⟩ := hdual
  have hc : ∀ i, ∃ c : O, algebraMap O O' c = ∑ j ∈ Finset.range ℓ, (τ ^ j) (y i) := fun i =>
    hfix _ (GlobalTheory.CompanionTheory.NormLoc.trace_fixed ℓ τ hτ (y i))
  choose c hc using hc
  have hsum : ∑ i, x i * algebraMap O O' (c i) = 1 := by
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j hj => hxy j (Finset.mem_range.mp hj)]
    simp [hℓ]
  by_cases hunit : ∃ i, IsUnit (c i)
  · obtain ⟨i, u, hu⟩ := hunit
    refine ⟨algebraMap O O' (↑u⁻¹ : O) * y i, ?_⟩
    have h : ∀ j, (τ ^ j) (algebraMap O O' (↑u⁻¹ : O) * y i) =
        algebraMap O O' (↑u⁻¹ : O) * (τ ^ j) (y i) := by
      intro j
      rw [map_mul, AlgEquiv.commutes]
    simp_rw [h]
    rw [← Finset.mul_sum, ← hc i, ← map_mul, ← hu, Units.inv_mul, map_one]
  · push_neg at hunit
    have htop : (⊤ : Submodule O O') ≤ IsLocalRing.maximalIdeal O • ⊤ := by
      intro z _
      have hz : z = ∑ i, c i • (z * x i) := by
        simp_rw [Algebra.smul_def]
        calc z = z * 1 := (mul_one z).symm
          _ = _ := by
            rw [← hsum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
      rw [hz]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hunit i
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) ⊤
      Module.Finite.fg_top htop (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have h1 : (1 : O') = 0 := by
      have : (1 : O') ∈ (⊤ : Submodule O O') := Submodule.mem_top
      rw [hbot] at this
      exact this
    haveI : Subsingleton O' := subsingleton_of_zero_eq_one h1.symm
    exact ⟨0, Subsingleton.elim _ _⟩

variable {R : Type} [CommRing R] [Algebra O R]

theorem map_pow_succ_apply (τ : O' ≃ₐ[O] O') (j : ℕ) (t : O' ⊗[O] R) :
    Algebra.TensorProduct.map ((τ ^ (j + 1) : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t =
      Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R)
        (Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u r => simp [Algebra.TensorProduct.map_tmul, pow_succ']
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_pow_fixed (τ : O' ≃ₐ[O] O') (s : O' ⊗[O] R)
    (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s) (j : ℕ) :
    Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) s = s := by
  induction j with
  | zero =>
    clear hs
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy]
  | succ j ih => rw [GlobalTheory.CompanionTheory.NormLoc.map_pow_succ_apply, ih, hs]

theorem trace_tensor_mem (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (t : O' ⊗[O] R) :
    ∑ j ∈ Finset.range ℓ,
        Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t ∈
      Set.range (includeRight : R →ₐ[O] O' ⊗[O] R) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x r =>
    obtain ⟨c, hc⟩ := hfix _ (GlobalTheory.CompanionTheory.NormLoc.trace_fixed ℓ τ hτ x)
    refine ⟨c • r, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
    rw [← TensorProduct.sum_tmul, ← hc, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]⟩

theorem fixed_mem_range (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (a : O')
    (ha : ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) (s : O' ⊗[O] R)
    (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s) :
    s ∈ Set.range (includeRight : R →ₐ[O] O' ⊗[O] R) := by
  have key : ∑ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom)
      (AlgHom.id O R) ((a ⊗ₜ[O] (1 : R)) * s) = s := by
    simp only [map_mul, GlobalTheory.CompanionTheory.NormLoc.map_pow_fixed τ s hs]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, map_one]
    rw [← Finset.sum_mul, ← TensorProduct.sum_tmul, ha, ← Algebra.TensorProduct.one_def, one_mul]
  rw [← key]
  exact GlobalTheory.CompanionTheory.NormLoc.trace_tensor_mem ℓ τ hτ hfix _

theorem prod_one_add_tmul_sub_mem (J : Ideal R) (m : ℕ) (hm : 1 ≤ m) (r : R) (hr : r ∈ J ^ m)
    (S : Finset ℕ) (b : ℕ → O') :
    (∏ j ∈ S, (1 + b j ⊗ₜ[O] r)) - (1 + (∑ j ∈ S, b j) ⊗ₜ[O] r) ∈
      Ideal.map (includeRight : R →ₐ[O] O' ⊗[O] R) (J ^ (m + 1)) := by
  classical
  have hrr : r * r ∈ J ^ (m + 1) := by
    have h := Ideal.mul_mem_mul hr hr
    rw [← pow_add] at h
    exact Ideal.pow_le_pow_right (by omega) h
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk]
    have h : (1 + b k ⊗ₜ[O] r) * ∏ j ∈ S, (1 + b j ⊗ₜ[O] r) - (1 + (b k + ∑ j ∈ S, b j) ⊗ₜ[O] r)
        = (1 + b k ⊗ₜ[O] r) * (∏ j ∈ S, (1 + b j ⊗ₜ[O] r) - (1 + (∑ j ∈ S, b j) ⊗ₜ[O] r))
          + (b k * ∑ j ∈ S, b j) ⊗ₜ[O] (r * r) := by
      rw [TensorProduct.add_tmul, ← Algebra.TensorProduct.tmul_mul_tmul]
      ring
    rw [h]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    have h' : (b k * ∑ j ∈ S, b j) ⊗ₜ[O] (r * r) =
        ((b k * ∑ j ∈ S, b j) ⊗ₜ[O] (1 : R)) * (includeRight : R →ₐ[O] O' ⊗[O] R) (r * r) := by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul]
    rw [h']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hrr)

end

theorem fixedRing_traceOne_firstOrder : PositivityTheory.Rg.Tf.Loc.N2 := by
  unfold PositivityTheory.Rg.Tf.Loc.N2
  intro O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hdual
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.NormLoc.exists_trace_one ℓ τ hℓ hτ hfix hdual
  refine ⟨fun s hs => GlobalTheory.CompanionTheory.NormLoc.fixed_mem_range ℓ τ hτ hfix a ha s hs, a, ha, ?_⟩
  intro m hm r hr
  have key := GlobalTheory.CompanionTheory.NormLoc.prod_one_add_tmul_sub_mem (O := O) (O' := O') (Ideal.jacobson (⊥ : Ideal R)) m hm r hr
    (Finset.range ℓ) (fun j => (τ ^ j) a)
  have e1 : ∏ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom)
      (AlgHom.id O R) (1 + a ⊗ₜ[O] r) = ∏ j ∈ Finset.range ℓ, (1 + (τ ^ j) a ⊗ₜ[O] r) :=
    Finset.prod_congr rfl fun j _ => by simp
  have e2 : (includeRight : R →ₐ[O] O' ⊗[O] R) (1 + r) =
      1 + (∑ j ∈ Finset.range ℓ, (τ ^ j) a) ⊗ₜ[O] r := by
    rw [ha, Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add,
      ← Algebra.TensorProduct.one_def]
  rw [← e1, ← e2] at key
  exact key

end GlobalTheory.CompanionTheory.NormLoc
end

section

open MeasureTheory Polynomial

namespace GlobalTheory.CompanionTheory.TfLoc

open PositivityTheory.Rg.Tf.Loc

theorem commute_aeval_right {K : Type*} [Field K] {n : ℕ} {A M : Matrix (Fin n) (Fin n) K}
    (hc : Commute A M) (p : K[X]) : Commute A (aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add_right hq
  | monomial m a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right a A).mul_right (hc.pow_right m)

theorem transport_open_trace : D0a → T0 → A1 → MeasureTransportOpenSet := by
  intro hD _ hA
  unfold D0a at hD
  unfold A1 at hA
  unfold MeasureTransportOpenSet
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hur σ hgen n _ _ _ _ SE Sk hSE hSk δ γ h μδ μγ hreg hN hmap y z hz
  have hinc : Continuous (fun g : GL (Fin n) k => (incl g : GL (Fin n) E)) :=
    (hD k E hur σ hgen).2.2.2.2.2 n
  have hcf : Continuous (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hci : Continuous (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) :=
    hinc.comp continuous_subtype_val

  have hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    have h0 := hreg
    unfold IsTwRegSemisimple at h0
    rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at h0
    exact h0
  obtain ⟨p, hp⟩ := hA E n _ hsep (z : Matrix (Fin n) (Fin n) E) hz

  have hzt : ∀ t : Subgroup.centralizer {γ},
      z * incl (t : GL (Fin n) k) = incl (t : GL (Fin n) k) * z := by
    intro t
    have ht : (t : GL (Fin n) k) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.mp t.2
    have hc : Commute ((incl (t : GL (Fin n) k) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
        ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
      have := congrArg (fun g => ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) ht
      simpa [Commute, SemiconjBy, map_mul, Units.val_mul] using this
    have hc2 := commute_aeval_right hc p
    rw [← hp] at hc2
    exact Units.ext hc2.symm.eq
  set S' : Set (GL (Fin n) E) := {w | (z * incl y)⁻¹ * w * (z * incl y) ∈ SE} with hS'
  have hopen : IsOpen S' :=
    hSE.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hmeas : MeasurableSet S' := hopen.measurableSet
  have e1 : μδ {x | (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) ∈ SE} =
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ S' := by
    rw [Measure.map_apply hcf.measurable hmeas]
    congr 1
    ext x
    have : (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) =
        (z * incl y)⁻¹ * (h⁻¹ * (x : GL (Fin n) E) * h) * (z * incl y) := by group
    simp only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this]
  have e2 : Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ S' =
      μγ {t | y⁻¹ * (t : GL (Fin n) k) * y ∈ Sk} := by
    rw [Measure.map_apply hci.measurable hmeas]
    congr 1
    ext t
    have : (z * incl y)⁻¹ * incl (t : GL (Fin n) k) * (z * incl y) =
        incl (y⁻¹ * (t : GL (Fin n) k) * y) := by
      calc (z * incl y)⁻¹ * incl (t : GL (Fin n) k) * (z * incl y)
          = (incl y)⁻¹ * (z⁻¹ * (incl (t : GL (Fin n) k) * z)) * incl y := by group
        _ = (incl y)⁻¹ * (z⁻¹ * (z * incl (t : GL (Fin n) k))) * incl y := by rw [hzt t]
        _ = (incl y)⁻¹ * incl (t : GL (Fin n) k) * incl y := by group
        _ = incl (y⁻¹ * (t : GL (Fin n) k) * y) := by simp only [map_mul, map_inv]
    simp only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this, hSk]
  rw [e1, hmap, e2]

end GlobalTheory.CompanionTheory.TfLoc
end

section

open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.Tf.Loc

theorem isUnitIntegral_of_conj_mem_unitGL {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (γ g : GL (Fin n) F) (h : g⁻¹ * γ * g ∈ unitGL (n := Fin n) F) : IsUnitIntegral γ := by
  obtain ⟨u, hu⟩ := h
  have hcp : (γ : Matrix (Fin n) (Fin n) F).charpoly =
      ((u : Matrix (Fin n) (Fin n) (intO F)).charpoly).map (intO F).subtype := by
    have h1 : ((g⁻¹ * γ * g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).charpoly =
        (γ : Matrix (Fin n) (Fin n) F).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    rw [← h1, ← hu, ← Matrix.charpoly_map]
    rfl
  have hint := Valuation.integer.integers (ValuativeRel.valuation F)
  refine ⟨fun i => ?_, ?_⟩
  · rw [hcp, Polynomial.coeff_map]
    exact SetLike.coe_mem _
  · rw [hcp, Polynomial.coeff_map]
    have hdet : IsUnit (u : Matrix (Fin n) (Fin n) (intO F)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
    have hc : IsUnit ((u : Matrix (Fin n) (Fin n) (intO F)).charpoly.coeff 0) := by
      rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    exact hint.isUnit_iff_valuation_eq_one.1 hc

theorem normGL_mem_unitGL {k E : Type} [Field k] [Field E] [ValuativeRel E] [Algebra k E] {n : ℕ}
    (σ : E ≃ₐ[k] E)
    (hστ : ∀ (τ : E ≃ₐ[k] E) (g : GL (Fin n) E),
      sigmaGL τ g ∈ unitGL (n := Fin n) E ↔ g ∈ unitGL (n := Fin n) E)
    {u : GL (Fin n) E} (hu : u ∈ unitGL (n := Fin n) E) :
    normGL σ u ∈ unitGL (n := Fin n) E := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [← sigmaGL_pow]
  exact (hστ _ _).2 hu

theorem stableLattice_unitIntegral : D0a → L2 := by
  intro hD
  refine ⟨?_, ?_⟩
  · rintro F _ _ _ _ n γ ⟨g, hg⟩
    exact isUnitIntegral_of_conj_mem_unitGL γ g hg
  · intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n δ g hmem
    have hστ := (hD k E hun σ hgen).2.2.2.1
    have hℓ : σ ^ Module.finrank k E = 1 := by
      rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
    have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
      rw [← sigmaGL_pow, hℓ, sigmaGL_one]
    have h := normGL_mem_unitGL σ (hστ · n ·) hmem
    rw [normGL, twNorm_twConj_of_pow_eq_one _ hθ] at h
    exact h

end GlobalTheory.CompanionTheory.Tf.Loc
end

section

open Polynomial

namespace GlobalTheory.CompanionTheory.Centraliser

variable {K : Type} [Field K] {n : ℕ}

theorem act_mul (γ : Matrix (Fin n) (Fin n) K) (a b : K[X]) (v : Fin n → K) :
    (aeval γ (a * b)).mulVec v = (aeval γ a).mulVec ((aeval γ b).mulVec v) := by
  rw [map_mul, Matrix.mulVec_mulVec]

theorem charpoly_dvd_of_aeval_eq_zero (γ : Matrix (Fin n) (Fin n) K)
    (hs : γ.charpoly.Separable) {p : K[X]} (hp : aeval γ p = 0) : γ.charpoly ∣ p := by
  have h := GlobalTheory.CharpolyPowIrred.charpoly_dvd_pow_of_aeval γ p hp
  rcases Nat.eq_zero_or_pos (Fintype.card (Fin n)) with h0 | h0
  · rw [h0, pow_zero] at h
    exact h.trans (one_dvd p)
  · exact (hs.squarefree.dvd_pow_iff_dvd h0.ne').1 h

theorem exists_vec_ann (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) (q : K[X]) :
    q ∣ γ.charpoly → ∃ v : Fin n → K, (aeval γ q).mulVec v = 0 ∧
      ∀ h : K[X], (aeval γ h).mulVec v = 0 → q ∣ h := by
  have hf0 : γ.charpoly ≠ 0 := γ.charpoly_monic.ne_zero
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro h
    exact absurd (zero_dvd_iff.1 h) hf0
  · intro x hx _
    exact ⟨0, by simp, fun h _ => hx.dvd⟩
  · intro a p ha hp ih hd
    obtain ⟨v', hv1, hv2⟩ := ih ((dvd_mul_left a p).trans hd)
    obtain ⟨g, hg⟩ : p ∣ γ.charpoly := (dvd_mul_right p a).trans hd
    have hgne : g ≠ 0 := by
      rintro rfl
      exact hf0 (by simpa using hg)
    have hg0 : aeval γ g ≠ 0 := fun h => by
      obtain ⟨c, hc⟩ := charpoly_dvd_of_aeval_eq_zero γ hs h
      rw [hg] at hc
      have h1 : g * (p * c) = g * 1 := by
        rw [mul_one]
        calc g * (p * c) = p * g * c := by ring
          _ = g := hc.symm
      exact hp.not_unit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ hgne h1))
    obtain ⟨u, hu⟩ : ∃ u, (aeval γ g).mulVec u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hg0 (Matrix.mulVec_injective (funext fun u => by simpa using hcon u))
    set w := (aeval γ g).mulVec u with hw
    have hpw : (aeval γ p).mulVec w = 0 := by
      rw [hw, ← act_mul, ← hg, Matrix.aeval_self_charpoly, Matrix.zero_mulVec]
    have hkey : ∀ h : K[X], (aeval γ h).mulVec w = 0 → p ∣ h := by
      intro h hh
      by_contra hnd
      obtain ⟨s, t, hst⟩ := (Prime.coprime_iff_not_dvd hp).2 hnd
      apply hu
      have h1 : (aeval γ (s * p + t * h)).mulVec w = w := by
        rw [hst]; simp
      rw [map_add (f := _), Matrix.add_mulVec, act_mul, act_mul, hpw, hh] at h1
      simpa using h1.symm
    have hpa : ¬ p ∣ a := by
      rintro ⟨c, rfl⟩
      exact hp.not_unit (hs.squarefree p
        ((mul_dvd_mul_left p (dvd_mul_right p c)).trans hd))
    have hcop : IsCoprime p a := (Prime.coprime_iff_not_dvd hp).2 hpa
    refine ⟨v' + w, ?_, ?_⟩
    · rw [Matrix.mulVec_add, act_mul, hv1, mul_comm, act_mul, hpw]
      simp
    · intro h hh
      have h1 : (aeval γ (h * p)).mulVec v' = 0 := by
        have h2 : (aeval γ (h * p)).mulVec (v' + w) = 0 := by
          rw [mul_comm, act_mul, hh, Matrix.mulVec_zero]
        rw [Matrix.mulVec_add, act_mul γ h p w, hpw, Matrix.mulVec_zero, add_zero] at h2
        exact h2
      have hah : a ∣ h := hcop.symm.dvd_of_dvd_mul_right (hv2 _ h1)
      obtain ⟨c, rfl⟩ := hah
      have h3 : (aeval γ (a * c)).mulVec v' = 0 := by
        rw [mul_comm, act_mul, hv1]; simp
      rw [Matrix.mulVec_add, h3, zero_add] at hh
      exact hcop.mul_dvd (hkey _ hh) (dvd_mul_right a c)

theorem exists_cyclic_vec (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) :
    ∃ v : Fin n → K, ∀ w : Fin n → K, ∃ q : K[X], (aeval γ q).mulVec v = w := by
  obtain ⟨v, -, hv⟩ := exists_vec_ann γ hs γ.charpoly dvd_rfl
  refine ⟨v, ?_⟩
  let L : K[X] →ₗ[K] (Fin n → K) :=
    { toFun := fun p => (aeval γ p).mulVec v
      map_add' := fun a b => by rw [map_add (f := _), Matrix.add_mulVec]
      map_smul' := fun c a => by rw [map_smul, Matrix.smul_mulVec]; rfl }
  let φ : degreeLT K n →ₗ[K] (Fin n → K) := L.domRestrict (degreeLT K n)
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨p, hp⟩ h0
    have hd : γ.charpoly ∣ p := hv p h0
    have hlt : p.degree < γ.charpoly.degree := by
      rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
      exact Polynomial.mem_degreeLT.1 hp
    exact Subtype.ext (Polynomial.eq_zero_of_dvd_of_degree_lt hd hlt)
  have hfr : Module.finrank K (degreeLT K n) = Module.finrank K (Fin n → K) :=
    (degreeLTEquiv K n).finrank_eq
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  intro w
  obtain ⟨⟨q, _⟩, hq⟩ := hsurj w
  exact ⟨q, hq⟩

theorem a1 : PositivityTheory.Rg.Tf.Loc.A1 := by
  intro K _ n γ hs M hM
  obtain ⟨v, hv⟩ := exists_cyclic_vec γ hs
  obtain ⟨p, hp⟩ := hv (M.mulVec v)
  refine ⟨p, Matrix.mulVec_injective (funext fun w => ?_)⟩
  obtain ⟨q, rfl⟩ := hv w
  have hc : Commute M (aeval γ q) := by
    rw [aeval_eq_sum_range]
    exact Commute.sum_right _ _ _ fun i _ => (hM.pow_right i).smul_right _
  rw [Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, ← hp, ← act_mul, mul_comm, act_mul]

end GlobalTheory.CompanionTheory.Centraliser
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.hilbert_schmidt_norm_submultiplicative : ∀ {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ), Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  first | exact @GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | exact GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | (intros; apply GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul <;> assumption)
end
