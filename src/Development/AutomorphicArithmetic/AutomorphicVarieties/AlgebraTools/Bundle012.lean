module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle038
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Mathlib.Topology.Algebra.OpenSubgroup
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TwoSidedIdeal.Instances
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.cotInd_extend :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      ∃ (s : ℕ) (y : Fin s → R), CotInd R (Sum.elim x y) ∧
        Ideal.span (Set.range (Sum.elim x y)) = maximalIdeal R ∧
        Fintype.card κ + s = (maximalIdeal R).spanFinrank := by
  intro R _ _ _ κ _ x hx
  obtain ⟨hm, hli⟩ := (cotInd_iff R x).mp hx
  set v : κ → CotangentSpace R := fun k => (maximalIdeal R).toCotangent ⟨x k, hm k⟩ with hv
  let bW := Module.Basis.span hli
  let bQ := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ Submodule.span (ResidueField R) (Set.range v))
  let B := Module.Basis.sumQuot bW bQ
  choose z hz using fun i => (maximalIdeal R).toCotangent_surjective (B (Sum.inr i))
  refine ⟨_, fun i => (z i : R), ?_⟩
  have hmem : ∀ j, Sum.elim x (fun i => (z i : R)) j ∈ maximalIdeal R := by
    rintro (k | i)
    · exact hm k
    · exact (z i).2
  have hB : (fun j => (maximalIdeal R).toCotangent ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩) = ⇑B := by
    funext j
    rcases j with k | i
    · simp [B, bW, Module.Basis.span_apply, hv]
    · simpa using hz i
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  refine ⟨(cotInd_iff R _).mpr ⟨hmem, ?_⟩, ?_, ?_⟩
  · rw [hB]
    exact B.linearIndependent
  · let g : κ ⊕ Fin _ → maximalIdeal R := fun j => ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩
    have hspan : Submodule.span R (Set.range g) = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp]
      have : (maximalIdeal R).toCotangent ∘ g = ⇑B := hB
      rw [this, B.span_eq]
    have := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  · rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg, Module.finrank_eq_card_basis B,
      Fintype.card_sum, Fintype.card_fin]
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.pow_mem_of_sub_one_mem :
    ∀ (l : ℕ) (E : Type) [Ring E] (J : TwoSidedIdeal E), (l : E) ∈ J → ∀ (j : ℕ) (x : E), x - 1 ∈ J →
      x ^ l ^ j - 1 ∈ (J.asIdeal : Submodule E E) ^ (j + 1) := by
  intro l E _ J hl j x hx
  have key : ∀ y : E, y - 1 ∈ J → ∀ n : ℕ, y ^ n - 1 ∈ J := by
    intro y hy n
    rw [← geom_sum_mul]
    exact J.mul_mem_left _ _ hy
  induction j with
  | zero =>
    rw [pow_zero, pow_one, zero_add, Submodule.pow_one]
    exact TwoSidedIdeal.mem_asIdeal.mpr hx
  | succ j ih =>
    have hy : x ^ l ^ j - 1 ∈ J := key x hx _
    rw [pow_succ, pow_mul, ← mul_geom_sum, Submodule.pow_succ]
    refine Submodule.mul_mem_mul ih ?_
    rw [TwoSidedIdeal.mem_asIdeal]
    have hs : ∑ i ∈ Finset.range l, (x ^ l ^ j) ^ i
        = ∑ i ∈ Finset.range l, ((x ^ l ^ j) ^ i - 1) + (l : E) := by
      simp [Finset.sum_sub_distrib]
    rw [hs]
    exact J.add_mem (sum_mem fun i _ => key _ hy i) hl
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ultra_fin :
    ∀ (ι Z : Type) (U : Ultrafilter ι) (a : ι → Z) (s : Set Z), s.Finite → (∀ᶠ i in (U : Filter ι), a i ∈ s) →
      ∃! z, z ∈ s ∧ ∀ᶠ i in (U : Filter ι), a i = z := by
  intro ι Z U a s hs h
  have hsub : {i | a i ∈ s} ⊆ ⋃ z ∈ s, {i | a i = z} := by
    intro i hi
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨a i, hi, rfl⟩
  have hmem : (⋃ z ∈ s, {i | a i = z}) ∈ U := U.1.sets_of_superset h hsub
  obtain ⟨z, hz, hzU⟩ := (Ultrafilter.finite_biUnion_mem_iff hs).1 hmem
  refine ⟨z, ⟨hz, hzU⟩, ?_⟩
  rintro w ⟨-, hw⟩
  obtain ⟨i, hi1, hi2⟩ := (hw.and hzU).exists
  exact hi1.symm.trans hi2
end

section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem exists_invariant_flag_mod_l {R : Type} [CommRing R] {n : ℕ} (P P' V : Matrix (Fin n) (Fin n) R)
    (hP : ∀ i j, j < i → P i j = 0) (hP' : ∀ i j, j < i → P' i j = 0)
    (hu : ∀ i j, j < i → IsUnit (P i i - P' j j)) (hE : P * V = V * P') :
    ∀ i j, j < i → V i j = 0 := by
  have key : ∀ j i : Fin n, j < i → V i j = 0 := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ihj =>
      intro i
      induction i using WellFoundedGT.induction with
      | ind i ihi =>
        intro hji
        have h := congrFun (congrFun hE i) j
        rw [Matrix.mul_apply, Matrix.mul_apply] at h
        have hL : ∑ k, P i k * V k j = P i i * V i j := by
          refine Finset.sum_eq_single i ?_ (by simp)
          intro k _ hk
          rcases lt_or_gt_of_ne hk with h1 | h1
          · rw [hP i k h1, zero_mul]
          · rw [ihi k h1 (hji.trans h1), mul_zero]
        have hR : ∑ k, V i k * P' k j = V i j * P' j j := by
          refine Finset.sum_eq_single j ?_ (by simp)
          intro k _ hk
          rcases lt_or_gt_of_ne hk with h1 | h1
          · rw [ihj k h1 i (h1.trans hji), zero_mul]
          · rw [hP' k j h1, mul_zero]
        rw [hL, hR] at h
        have h0 : (P i i - P' j j) * V i j = 0 := by
          linear_combination h
        exact ((hu i j hji).mul_right_eq_zero).1 h0
  intro i j h
  exact key j i h

private theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) :
    (A * B) i i = A i i * B i i :=
  _root_.UpperTheory.Reformulated.B.S8.diag_mul A B hA hB i

theorem UpperTheory.V.AlgebraTools.flag_chars_unique :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Group Γ] {n : ℕ} (r : Γ →* GL (Fin n) R) (ψ ψ' : Fin n → Γ →* Rˣ) (g g' : GL (Fin n) R), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp ((Units.coeHom R).comp (ψ i))) → (∀ i s, residue R (ψ i s) = residue R (ψ' i s)) → (∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g * r s * g⁻¹ : GL (Fin n) R) i i = (ψ i s : R)) → (∀ s, (∀ i j, j < i → (g' * r s * g'⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g' * r s * g'⁻¹ : GL (Fin n) R) i i = (ψ' i s : R)) → ψ = ψ' ∧ ∀ i j, j < i → (g * g'⁻¹ : GL (Fin n) R) i j = 0 := by
  intro R Γ _ _ _ n r ψ ψ' g g' hn hinj hres h1 h2
  obtain ⟨z, hz⟩ := UpperTheory.V.AlgebraTools.sep_chars (fun i => (Units.coeHom R).comp (ψ i)) hn hinj
  have hcomm : ∀ s, ((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      ((g' * r s * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    intro s
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have key : ∀ w : MonoidAlgebra R Γ, ∃ P P' : Matrix (Fin n) (Fin n) R,
      (∀ i j, j < i → P i j = 0) ∧ (∀ i j, j < i → P' i j = 0) ∧
      P * ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
        ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * P' ∧
      (∀ i, P i i = MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) w) ∧
      (∀ i, residue R (P' i i) = residue R (P i i)) := by
    intro w
    induction w using MonoidAlgebra.induction_on with
    | of s =>
      refine ⟨_, _, (h1 s).1, (h2 s).1, hcomm s, fun i => ?_, fun i => ?_⟩
      · rw [MonoidAlgebra.lift_of]; exact (h1 s).2 i
      · rw [(h1 s).2 i, (h2 s).2 i, hres]
    | add a b ha hb =>
      obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := ha
      obtain ⟨Q, Q', b1, b2, b3, b4, b5⟩ := hb
      refine ⟨P + Q, P' + Q', fun i j h => ?_, fun i j h => ?_, ?_, fun i => ?_, fun i => ?_⟩
      · rw [Matrix.add_apply, a1 i j h, b1 i j h, add_zero]
      · rw [Matrix.add_apply, a2 i j h, b2 i j h, add_zero]
      · rw [add_mul, mul_add, a3, b3]
      · rw [Matrix.add_apply, map_add (f := _), a4, b4]
      · rw [Matrix.add_apply, Matrix.add_apply, map_add (f := _), map_add (f := _), a5, b5]
    | smul c a ha =>
      obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := ha
      refine ⟨c • P, c • P', fun i j h => ?_, fun i j h => ?_, ?_, fun i => ?_, fun i => ?_⟩
      · rw [Matrix.smul_apply, a1 i j h, smul_zero]
      · rw [Matrix.smul_apply, a2 i j h, smul_zero]
      · rw [Matrix.smul_mul, Matrix.mul_smul, a3]
      · rw [Matrix.smul_apply, map_smul, a4]
      · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, a5]
  obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := key z
  have hV := exists_invariant_flag_mod_l P P' _ a1 a2 (fun i j h => by
    have hu := hz i j h.ne'
    rw [← a4, ← a4, ← residue_ne_zero_iff_isUnit, map_sub] at hu
    rw [← residue_ne_zero_iff_isUnit, map_sub, a5]
    exact hu) a3
  refine ⟨?_, hV⟩
  have hdet : IsUnit (((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  rw [Matrix.det_of_upperTriangular (fun i j h => hV i j h)] at hdet
  funext i
  ext s
  have hu : IsUnit (((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i) :=
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem
      (fun k => ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) k k) (Finset.mem_univ i)) hdet
  have h := congrFun (congrFun (hcomm s) i) i
  rw [diag_mul _ _ (h1 s).1 hV, diag_mul _ _ hV (h2 s).1, (h1 s).2 i, (h2 s).2 i, mul_comm] at h
  exact hu.mul_left_cancel h
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

open IsLocalRing in
private theorem complete_of_finite (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [IsLocalRing R'] : IsAdicComplete (maximalIdeal R') R' := by
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R')
        (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P
        (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have h0 : IsAdicComplete (maximalIdeal R) R' := by
    let I := maximalIdeal R
    have hb : Function.Bijective (AdicCompletion.of I R) :=
      AdicCompletion.of_bijective_iff.2 (show IsAdicComplete I R from inferInstance)
    let φ : R ≃ₗ[R] AdicCompletion I R := LinearEquiv.ofBijective (AdicCompletion.of I R) hb
    let e : R' ≃ₗ[R] AdicCompletion I R ⊗[R] R' :=
      (TensorProduct.lid R R').symm.trans (TensorProduct.congr φ (LinearEquiv.refl R R'))
    have h1 : AdicCompletion.of I R 1 = 1 := by
      ext n
      simp
    have hfac : ⇑(AdicCompletion.of I R') =
        ⇑(AdicCompletion.ofTensorProduct I R') ∘ ⇑e := by
      funext x
      have he : e x = (1 : AdicCompletion I R) ⊗ₜ[R] x := by
        simp [e, φ, h1]
      simp [he]
    apply AdicCompletion.of_bijective_iff.1
    rw [hfac]
    exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I R').comp e.bijective
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 h0.toIsPrecomplete)
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }

theorem UpperTheory.V.AlgebraTools.local_factor :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (n : Ideal A) [n.IsMaximal],
      Function.Surjective (algebraMap A (Localization.AtPrime n)) ∧ Module.Finite R (Localization.AtPrime n) ∧
      IsLocalHom (algebraMap R (Localization.AtPrime n)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime n)) (Localization.AtPrime n) ∧
      (Module.Free R A → Module.Free R (Localization.AtPrime n)) ∧
      (∃ e : A, IsIdempotentElem e ∧ (∀ n' : Ideal A, n'.IsMaximal → (e ∉ n' ↔ n' = n)) ∧
        RingHom.ker (algebraMap A (Localization.AtPrime n)) = Ideal.span {1 - e}) ∧
      ∀ (C : Type) [CommRing C] [IsLocalRing C] (f : A →+* C), (IsLocalRing.maximalIdeal C).comap f = n →
        ∃ g : Localization.AtPrime n →+* C, g.comp (algebraMap A _) = f := by
  intro R _ _ _ _ A _ _ _ n hn
  letI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  have hfin : Module.Finite R (Localization.AtPrime n) := GlobalTheory.finite_localization_of_henselian R n
  refine ⟨GlobalTheory.surjective_algebraMap_localization_of_henselian R n, hfin, ⟨fun a ha => ?_⟩,
    complete_of_finite R _, fun hF => ?_, ?_, fun C _ _ f hf => ?_⟩
  · by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal R := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal (Localization.AtPrime n)),
      Ideal.mem_comap] at h1
    exact h1 ha
  · haveI : Module.Flat A (Localization.AtPrime n) := IsLocalization.flat _ n.primeCompl
    haveI : Module.Flat R (Localization.AtPrime n) := Module.Flat.trans R A _
    exact Module.free_of_flat_of_isLocalRing
  · obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian R n
    refine ⟨e, he, H, le_antisymm (fun x hx => ?_) ?_⟩
    · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff n.primeCompl _ x).1 hx
      have heq : e ∉ n := (H n hn).2 rfl
      have hu : IsUnit (e * s + (1 - e)) := by
        by_contra h
        obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits h
        by_cases hen : e ∈ m
        · rw [Submodule.add_mem_iff_right _ (Ideal.mul_mem_right _ _ hen),
            GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he] at hmem
          exact hmem hen
        · rw [Submodule.add_mem_iff_left _
              ((GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he m).2 hen),
            (H m hm).1 hen] at hmem
          exact (hn.isPrime.mem_or_mem hmem).elim heq s.2
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      refine Ideal.mem_span_singleton'.2 ⟨v * x, ?_⟩
      linear_combination x * hv - v * e * hs
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      exact ((IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.map_units _
        (⟨e, (H n hn).2 rfl⟩ : n.primeCompl))).1 (he.map _)).symm
  · have hu : ∀ y : n.primeCompl, IsUnit (f y) := fun y => by
      by_contra h
      have h1 : (y : A) ∈ (IsLocalRing.maximalIdeal C).comap f := h
      rw [hf] at h1
      exact y.2 h1
    exact ⟨IsLocalization.lift hu, IsLocalization.lift_comp hu⟩
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.totallyDisconnected_quot :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (K : Subgroup G) [K.Normal], IsClosed (K : Set G) →
      TotallyDisconnectedSpace (G ⧸ K) ∧ (∀ g : G, (∀ O : OpenNormalSubgroup G, g ∈ K ⊔ O.toSubgroup) → g ∈ K) := by
  intro G _ _ _ _ _ N _ hN
  refine ⟨?_, fun x hx => ?_⟩
  · rw [totallyDisconnectedSpace_iff_connectedComponent_one]
    refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    by_contra hx
    have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
    have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
    let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
    have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
    have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
    obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
    exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
  · by_contra hx'
    have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
    have h := hx U
    rw [sup_comm] at h
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp h
    refine hU (U.toSubgroup.inv_mem hy) ?_
    rw [← hyz]
    simpa using hz
end
