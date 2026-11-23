module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SsDescend
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem span_map_mem {A B : Type} [Ring A] [Ring B] (F : A →+* B) (I : Set A) (x : A)
    (hx : x ∈ TwoSidedIdeal.span I) : F x ∈ TwoSidedIdeal.span (F '' I) := by
  have h : TwoSidedIdeal.span I ≤ TwoSidedIdeal.comap F (TwoSidedIdeal.span (F '' I)) := by
    rw [TwoSidedIdeal.span_le]
    intro a ha
    exact (TwoSidedIdeal.mem_comap F).2 (TwoSidedIdeal.subset_span ⟨a, ha, rfl⟩)
  exact (TwoSidedIdeal.mem_comap F).1 (h hx)

private theorem fin_quot {R κ G : Type} [CommRing R] [Field κ] [Group G] (I : Set (MonoidAlgebra R G))
    (ψ : R →+* κ)
    (hs : ∃ s : Finset G, ∀ y : MonoidAlgebra R G, ∃ c : G → R,
      y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span I) :
    Module.Finite κ (TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G ψ '' I)).ringCon.Quotient := by
  classical
  obtain ⟨s, hs⟩ := hs
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G ψ '' I) with hJ
  let π : MonoidAlgebra κ G →ₗ[κ] J.ringCon.Quotient :=
    { toFun := J.ringCon.mk'
      map_add' := fun a b => map_add _ a b
      map_smul' := fun a b => rfl }
  have hπ : Function.Surjective π := J.ringCon.mk'_surjective
  refine ⟨⟨s.image (fun g => π (MonoidAlgebra.single g 1)), ?_⟩⟩
  rw [eq_top_iff]
  intro z hz
  clear hz
  obtain ⟨y, rfl⟩ := hπ z
  have key : ∀ (g : G) (k : κ), π (MonoidAlgebra.single g k) = k • π (MonoidAlgebra.single g 1) := by
    intro g k
    rw [← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | single g k =>
    rw [key]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c, hc⟩ := hs (MonoidAlgebra.single g 1)
    have h1 := span_map_mem (MonoidAlgebra.mapRingHom G ψ) I _ hc

    rw [map_sub, map_sum] at h1
    simp only [MonoidAlgebra.mapRingHom_single, map_one] at h1
    have h2 : π (MonoidAlgebra.single g 1) = π (∑ g ∈ s, MonoidAlgebra.single g (ψ (c g))) := by
      show J.ringCon.mk' _ = J.ringCon.mk' _
      exact J.ringCon.eq.2 ((TwoSidedIdeal.rel_iff J _ _).2 h1)

    rw [h2, map_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    rw [key]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨a, ha, rfl⟩)

theorem UpperTheory.V.Pa.BC.nonSS_field :
    ∀ (R S S' G : Type) [CommRing R] [CommRing S] [CommRing S'] [Group G] (I : Set (MonoidAlgebra R G)) (φ : R →+* S) (φ' : R →+* S') (Q : Ideal S) (Q' : Ideal S'), Q'.IsPrime → Q'.comap φ' = Q.comap φ → (∃ s : Finset G, ∀ y : MonoidAlgebra R G, ∃ c : G → R, y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span I) → NonSS I φ Q → NonSS I φ' Q' := by
  intro R S S' G _ _ _ _ I φ φ' Q Q' hQ' hc hs hN
  obtain ⟨κ, _, f, hf, hns⟩ := hN
  let f' : S' →+* FractionRing (S' ⧸ Q') :=
    (algebraMap (S' ⧸ Q') (FractionRing (S' ⧸ Q'))).comp (Ideal.Quotient.mk Q')
  have hf' : RingHom.ker f' = Q' := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]
  have hk : RingHom.ker (f.comp φ) = RingHom.ker (f'.comp φ') := by
    rw [← RingHom.comap_ker, ← RingHom.comap_ker, hf, hf', hc]
  obtain ⟨K, _, j₁, j₂, hj⟩ := UpperTheory.V.Pa.BC.common_field R κ _ _ _ hk
  refine ⟨K, inferInstance, j₂.comp f', ?_, ?_⟩
  · rw [RingHom.ker_comp_of_injective _ j₂.injective, hf']
  · intro hss
    apply hns
    letI : Algebra κ K := j₁.toAlgebra
    haveI := fin_quot I (f.comp φ) hs
    obtain ⟨e⟩ := UpperTheory.V.Pa.BC.grp_quot_bc κ K G (MonoidAlgebra.mapRingHom G (f.comp φ) '' I)
    have him : MonoidAlgebra.mapRingHom G (algebraMap κ K) '' (MonoidAlgebra.mapRingHom G (f.comp φ) '' I)
        = MonoidAlgebra.mapRingHom G ((j₂.comp f').comp φ') '' I := by
      rw [RingHom.comp_assoc, ← hj, MonoidAlgebra.mapRingHom_comp j₁, RingHom.coe_comp, Set.image_comp]
      rfl
    rw [← him] at hss
    exact UpperTheory.V.Pa.BC.ss_descend κ K _ e.symm.isSemisimpleRing
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem spf_nilp {k Q : Type} [Field k] [CommRing Q] (φ : k →+* Q) (x : Q)
    (hx : ∀ y, IsUnit (x * y + 1)) (f : Polynomial k) (hf : f ≠ 0) (h : f.eval₂ φ x = 0) :
    IsNilpotent x := by
  obtain ⟨g, hg, hd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf 0
  rw [map_zero, sub_zero] at hg hd
  rw [Polynomial.X_dvd_iff] at hd
  have hu : IsUnit (g.eval₂ φ x) := by
    have e : g.eval₂ φ x = φ (g.coeff 0) * (x * (φ (g.coeff 0)⁻¹ * g.divX.eval₂ φ x) + 1) := by
      have e1 : φ (g.coeff 0) * φ (g.coeff 0)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hd, map_one]
      conv_lhs => rw [← Polynomial.X_mul_divX_add g]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
      linear_combination (-(x * g.divX.eval₂ φ x)) * e1
    rw [e]
    exact ((Ne.isUnit hd).map φ).mul (hx _)
  rw [hg, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at h
  exact ⟨_, hu.mul_left_eq_zero.1 h⟩

private theorem spf_nilp2 {k Q : Type} [Field k] [CommRing Q] (φ : k →+* Q) {n : ℕ} (x : Fin n → Q)
    (c : Fin n → k) (f : Polynomial k)
    (h : ∏ i, (Polynomial.X - Polynomial.C (φ (c i) + x i)) = f.map φ) (i : Fin n)
    (hx : ∀ y, IsUnit (x i * y + 1)) : IsNilpotent (x i) := by
  classical
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · exact ⟨1, Subsingleton.elim _ _⟩
  have hmon : (∏ j, (Polynomial.X - Polynomial.C (φ (c j) + x j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
  have hf : f ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at h
    exact hmon.ne_zero h
  have hroot : f.eval₂ φ (φ (c i) + x i) = 0 := by
    rw [← Polynomial.eval_map, ← h, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  refine spf_nilp φ (x i) hx (f.comp (Polynomial.X + Polynomial.C (c i))) ?_ ?_
  · intro h0
    apply hf
    rwa [← Polynomial.taylor_apply, Polynomial.taylor_eq_zero] at h0
  · rw [Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, add_comm]
    exact hroot

theorem UpperTheory.V.Pa.BC.sp_fin :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B), Module.Finite B (Sp P ut) ∧ IsNoetherianRing (Sp P ut) := by
  intro B _ _ _ _ q n P ut
  classical
  let k := ResidueField B
  let J := spIdeal P ut
  let Jb : Ideal (MvPowerSeries (Fin q × Fin n) k) := Ideal.map (MvPowerSeries.map (residue B)) J
  let π := Ideal.Quotient.mk Jb
  let φ : k →+* (MvPowerSeries (Fin q × Fin n) k ⧸ Jb) := π.comp MvPowerSeries.C
  let ψ : MvPowerSeries (Fin q × Fin n) B →+* (MvPowerSeries (Fin q × Fin n) k ⧸ Jb) :=
    π.comp (MvPowerSeries.map (residue B))
  have hunit : ∀ (p : Fin q × Fin n) (y : MvPowerSeries (Fin q × Fin n) k ⧸ Jb),
      IsUnit (π (MvPowerSeries.X p) * y + 1) := by
    intro p y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one π, ← map_add (f := _)]
    apply IsUnit.map
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hnil : ∀ p : Fin q × Fin n, IsNilpotent (π (MvPowerSeries.X p)) := by
    rintro ⟨j, i⟩
    refine spf_nilp2 φ (fun i => π (MvPowerSeries.X (j, i))) (fun i => residue B (ut j i))
      ((P j).map (residue B)) ?_ i (hunit _)
    have hD : (∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))) -
        (P j).map MvPowerSeries.C).map ψ = 0 := by
      ext k'
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      show π _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, k', rfl⟩)
    rw [Polynomial.map_sub, sub_eq_zero, Polynomial.map_prod, Polynomial.map_map] at hD
    have hC : ψ.comp MvPowerSeries.C = φ.comp (residue B) := by
      ext b
      simp [ψ, φ, MvPowerSeries.map_C]
    rw [hC, ← Polynomial.map_map] at hD
    rw [← hD]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [ψ, φ, MvPowerSeries.map_C, MvPowerSeries.map_X]
  have hle : Ideal.map π (Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k))) ≤ nilradical _ := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact mem_nilradical.2 (hnil p)
  have hfg : (Ideal.map π (Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)))).FG := by
    rw [Ideal.map_span]
    exact Submodule.fg_span ((Set.finite_range _).image _)
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
  have hpow : Ideal.span (Set.range
      (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)) ^ N ≤ Jb := by
    have h0 : Ideal.map π (Ideal.span (Set.range
        (MvPowerSeries.X : Fin q × Fin n → MvPowerSeries (Fin q × Fin n) k)) ^ N) = ⊥ := by
      rw [Ideal.map_pow, hN, Ideal.zero_eq_bot]
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h0
    exact h0
  have hfin : Module.Finite B (MvPowerSeries (Fin q × Fin n) B ⧸ J) :=
    GlobalTheory.FormalIsogeny.finite_quotient_of_residue J (GlobalTheory.FormalIsogeny.finite_quotient_of_pow_le hpow)
  have hfin' : Module.Finite B (Sp P ut) := hfin
  refine ⟨hfin', ?_⟩
  have hB : IsNoetherian B (Sp P ut) := inferInstance
  exact isNoetherian_of_tower B hB
end
