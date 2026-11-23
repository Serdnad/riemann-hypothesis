module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

private theorem UpperTheory.exists_mul_eq_algebraMap_of_galois_fixed (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ]
    [Algebra.IsAlgebraic O ℂ] (z : ℂ) (hz : ∀ γ : ℂ ≃ₐ[O] ℂ, γ z = z) :
    ∃ a b : O, b ≠ 0 ∧ algebraMap O ℂ b * z = algebraMap O ℂ a := by
  letI : Algebra (FractionRing O) ℂ := FractionRing.liftAlgebra O ℂ
  haveI : IsScalarTower O (FractionRing O) ℂ := FractionRing.isScalarTower_liftAlgebra O ℂ
  haveI : Algebra.IsAlgebraic (FractionRing O) ℂ :=
    Algebra.IsAlgebraic.extendScalars (FaithfulSMul.algebraMap_injective O (FractionRing O))
  haveI : CharZero (FractionRing O) := RingHom.charZero (algebraMap (FractionRing O) ℂ)
  haveI : Algebra.IsSeparable (FractionRing O) ℂ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsAlgClosure (FractionRing O) ℂ := ⟨inferInstance, inferInstance⟩
  haveI : Normal (FractionRing O) ℂ := inferInstance
  haveI : IsGalois (FractionRing O) ℂ := ⟨⟩
  have hmem : z ∈ Set.range (algebraMap (FractionRing O) ℂ) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed z).2 (fun f => hz (f.restrictScalars O))
  obtain ⟨q, rfl⟩ := hmem
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) q
  refine ⟨a, b, nonZeroDivisors.ne_zero b.2, ?_⟩
  show algebraMap O ℂ b * algebraMap (FractionRing O) ℂ (IsLocalization.mk' (FractionRing O) a b) =
    algebraMap O ℂ a
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) ℂ (b : O),
    IsScalarTower.algebraMap_apply O (FractionRing O) ℂ a, ← map_mul, mul_comm,
    IsLocalization.mk'_spec]

theorem UpperTheory.le_span_integralValued_of_galoisStable :
    ∀ (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ] [Algebra.IsAlgebraic O ℂ] (X : Type) [Finite X] (I : Submodule ℂ (X → ℂ)), (∀ γ : ℂ ≃ₐ[O] ℂ, ∀ x ∈ I, (fun g => γ (x g)) ∈ I) → I ≤ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
  intro O _ _ _ _ _ X _ I hI
  classical
  haveI := Fintype.ofFinite X
  have hfix : ∀ x ∈ I, (∀ γ : ℂ ≃ₐ[O] ℂ, (fun g => γ (x g)) = x) →
      x ∈ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
    intro x hx hγ
    have hc : ∀ g, ∃ a b : O, b ≠ 0 ∧ algebraMap O ℂ b * x g = algebraMap O ℂ a :=
      fun g => UpperTheory.exists_mul_eq_algebraMap_of_galois_fixed O (x g) (fun γ => congrFun (hγ γ) g)
    choose a b hb hab using hc
    have hB : algebraMap O ℂ (∏ g, b g) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun g _ =>
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O ℂ)).2 (hb g))
    have hmem : algebraMap O ℂ (∏ g, b g) • x ∈
        Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
      apply Submodule.subset_span
      refine ⟨I.smul_mem _ hx, fun g => ⟨a g * ∏ h ∈ Finset.univ.erase g, b h, ?_⟩⟩
      show algebraMap O ℂ (a g * ∏ h ∈ Finset.univ.erase g, b h) = algebraMap O ℂ (∏ g, b g) * x g
      rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ g)]
      simp only [map_mul, ← hab g]
      ring
    have h2 := Submodule.smul_mem _ (algebraMap O ℂ (∏ g, b g))⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hB, one_smul] at h2
  have key : ∀ n : ℕ, ∀ y ∈ I, (Finset.univ.filter (fun g => y g ≠ 0)).card ≤ n →
      y ∈ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} := by
    intro n
    induction n with
    | zero =>
      intro y hy hc
      have hy0 : y = 0 := by
        funext g
        by_contra h
        have := Finset.card_pos.2
          ⟨g, (by simpa using h : g ∈ Finset.univ.filter (fun g => y g ≠ 0))⟩
        omega
      rw [hy0]
      exact Submodule.zero_mem _
    | succ n ih =>
      intro y hy hc
      by_cases h0 : y = 0
      · rw [h0]
        exact Submodule.zero_mem _
      obtain ⟨g0, hg0⟩ : ∃ g, y g ≠ 0 := by
        by_contra h
        push_neg at h
        exact h0 (funext h)
      obtain ⟨x, hx⟩ : ∃ x : X → ℂ, x = (y g0)⁻¹ • y := ⟨_, rfl⟩
      have hxI : x ∈ I := by
        rw [hx]
        exact I.smul_mem _ hy
      have hxg0 : x g0 = 1 := by
        rw [hx]
        simp [hg0]
      have hsupp : ∀ g, x g = 0 ↔ y g = 0 := by
        intro g
        rw [hx]
        simp [hg0]
      have hyx : y = y g0 • x := by
        rw [hx, smul_smul, mul_inv_cancel₀ hg0, one_smul]
      by_cases hall : ∀ γ : ℂ ≃ₐ[O] ℂ, (fun g => γ (x g)) = x
      · rw [hyx]
        exact Submodule.smul_mem _ _ (hfix x hxI hall)
      · push_neg at hall
        obtain ⟨γ, hγ⟩ := hall
        obtain ⟨d, hd⟩ : ∃ d : X → ℂ, d = (fun g => γ (x g)) - x := ⟨_, rfl⟩
        have hdI : d ∈ I := by
          rw [hd]
          exact I.sub_mem (hI γ x hxI) hxI
        have hd0 : d ≠ 0 := by
          rw [hd]
          exact sub_ne_zero.2 hγ
        obtain ⟨g1, hg1⟩ : ∃ g, d g ≠ 0 := by
          by_contra h
          push_neg at h
          exact hd0 (funext h)
        have hdsupp : ∀ g, y g = 0 → d g = 0 := by
          intro g hg
          rw [hd]
          simp [(hsupp g).2 hg]
        have hdg0 : d g0 = 0 := by
          rw [hd]
          simp [hxg0]
        have hy1 : y g1 ≠ 0 := fun e => hg1 (hdsupp g1 e)
        have hdcard : (Finset.univ.filter (fun g => d g ≠ 0)).card ≤ n := by
          have hsub : Finset.univ.filter (fun g => d g ≠ 0) ⊆
              (Finset.univ.filter (fun g => y g ≠ 0)).erase g0 := by
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun e => hg (e ▸ hdg0), fun e => hg (hdsupp g e)⟩
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem
            (show g0 ∈ Finset.univ.filter (fun g => y g ≠ 0) by simp [hg0])
          omega
        have hdW := ih d hdI hdcard
        obtain ⟨y', hy'⟩ : ∃ y' : X → ℂ, y' = y - (y g1 / d g1) • d := ⟨_, rfl⟩
        have hy'I : y' ∈ I := by
          rw [hy']
          exact I.sub_mem hy (I.smul_mem _ hdI)
        have hy'card : (Finset.univ.filter (fun g => y' g ≠ 0)).card ≤ n := by
          have hsub : Finset.univ.filter (fun g => y' g ≠ 0) ⊆
              (Finset.univ.filter (fun g => y g ≠ 0)).erase g1 := by
            intro g hg
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, ?_⟩
            · rintro rfl
              apply hg
              rw [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hg1, sub_self]
            · intro e
              apply hg
              rw [hy', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e, hdsupp g e, mul_zero, sub_zero]
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_of_mem
            (show g1 ∈ Finset.univ.filter (fun g => y g ≠ 0) by simp [hy1])
          omega
        have hy'W := ih y' hy'I hy'card
        have hyy : y = y' + (y g1 / d g1) • d := by
          rw [hy', sub_add_cancel]
        rw [hyy]
        exact Submodule.add_mem _ hy'W (Submodule.smul_mem _ _ hdW)
  intro y hy
  exact key _ y hy le_rfl
end

section

theorem UpperTheory.center_tensorProduct_le_sup_map_center :
    ∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B], Subalgebra.center ℂ (TensorProduct ℂ A B) ≤ (Subalgebra.center ℂ A).map (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) ⊔ (Subalgebra.center ℂ B).map (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) := by
  intro A B _ _ _ _ z hz
  have hz' := Subalgebra.mem_center_iff.1 hz
  have h1 : z ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B).range :
        Set (TensorProduct ℂ A B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    exact hz' g
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct] at h1
  obtain ⟨w, hw⟩ := h1
  have hw' : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B) w = z := hw
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B)) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (R := ℂ) (M := B)
      (Subalgebra.center ℂ A).val.toLinearMap Subtype.val_injective
    exact h
  have h2 : w ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeRight :
        B →ₐ[ℂ] TensorProduct ℂ (Subalgebra.center ℂ A) B).range :
        Set (TensorProduct ℂ (Subalgebra.center ℂ A) B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    apply hinj
    rw [map_mul, map_mul, hw']
    exact hz' _
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at h2
  obtain ⟨v, hv⟩ := h2
  have hv' : Algebra.TensorProduct.map (AlgHom.id ℂ (Subalgebra.center ℂ A))
      (Subalgebra.center ℂ B).val v = w := hv
  rw [← hw', ← hv']
  clear hv' hv hw' hw hz' hz
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Subalgebra.zero_mem _
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Subalgebra.add_mem _ hx hy
  | tmul a b =>
    have e : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B)
        (Algebra.TensorProduct.map (AlgHom.id ℂ (Subalgebra.center ℂ A))
          (Subalgebra.center ℂ B).val (a ⊗ₜ[ℂ] b)) =
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) (a : A) *
        (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) (b : B) := by
      simp
    rw [e]
    exact Algebra.mul_mem_sup ⟨a, a.2, rfl⟩ ⟨b, b.2, rfl⟩
end

section

open Polynomial in
theorem UpperTheory.exists_integralClosure_preimage_of_isIntegral :
    ∀ (R E k : Type) [CommRing R] [Field E] [IsAlgClosed E] [Algebra R E] [CommRing k] [IsDomain k] (ψ : integralClosure R E →+* k) (x : k), IsIntegral ℤ x → ∃ y, ψ y = x := by
  intro R E k _ _ _ _ _ _ ψ x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := hx
  set q : E[X] := p.map (algebraMap ℤ E) with hq
  have hqm : q.Monic := hpm.map _
  have hqs : q.Splits := IsAlgClosed.splits q
  let lift : E → integralClosure R E := fun a => if h : IsIntegral R a then ⟨a, h⟩ else 0
  have hlift : ∀ a ∈ q.roots, ((lift a : integralClosure R E) : E) = a := by
    intro a ha
    have hr : q.IsRoot a := (mem_roots hqm.ne_zero).1 ha
    have hi : IsIntegral ℤ a := ⟨p, hpm, by
      rw [eval₂_eq_eval_map]
      exact hr⟩
    have hiR : IsIntegral R a := hi.tower_top
    simp [lift, hiR]
  have hfac : p.map (algebraMap ℤ (integralClosure R E)) = (q.roots.map fun a => X - C (lift a)).prod := by
    apply Polynomial.map_injective (algebraMap (integralClosure R E) E) Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
    have e : (algebraMap (integralClosure R E) E).comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ E :=
      RingHom.ext_int _ _
    rw [e, ← hq]
    conv_lhs => rw [hqs.eq_prod_roots_of_monic hqm]
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
    congr 2
    exact (hlift a ha).symm
  have hk : p.map (algebraMap ℤ k) = (q.roots.map fun a => X - C (ψ (lift a))).prod := by
    have e : ψ.comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ k := RingHom.ext_int _ _
    rw [← e, ← Polynomial.map_map, hfac, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have h0 : (p.map (algebraMap ℤ k)).eval x = 0 := by
    rw [eval_map]
    exact hpx
  rw [hk, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff] at h0
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.1 h0
  refine ⟨lift a, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at ha
  exact (sub_eq_zero.1 ha).symm
end

section

theorem UpperTheory.exists_automorphic_function_with_values_on_coset_reps :
    ∀ (Γ G K A M ι : Type) [Group Γ] [Group G] [Group K] [CommRing A] [AddCommGroup M] [Module A M] (gl : Γ →* G) (j : K →* G) (ρ : Representation A K M) (x : ι → G), (∀ g, ∃ γ i k, g = gl γ * x i * j k) → (∀ i i' γ k, x i' = gl γ * x i * j k → i = i') → (∀ i γ k, gl γ * x i = x i * j k → ρ k = 1) → ∀ v : ι → M, ∃ Φ : G → M, (∀ γ g, Φ (gl γ * g) = Φ g) ∧ (∀ g k, Φ (g * j k) = ρ k⁻¹ (Φ g)) ∧ ∀ i, Φ (x i) = v i := by
  intro Γ G K A M ι _ _ _ _ _ _ gl j ρ x hcov huniq hstab v
  have key : ∀ γ i k γ' i' k', gl γ * x i * j k = gl γ' * x i' * j k' →
      i = i' ∧ ρ k⁻¹ (v i) = ρ k'⁻¹ (v i') := by
    intro γ i k γ' i' k' h
    have e : x i' = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
      calc x i' = (gl γ')⁻¹ * (gl γ' * x i' * j k') * (j k')⁻¹ := by group
        _ = (gl γ')⁻¹ * (gl γ * x i * j k) * (j k')⁻¹ := by rw [h]
        _ = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
          simp only [map_mul, map_inv]
          group
    have hii : i = i' := huniq i i' _ _ e
    subst hii
    refine ⟨rfl, ?_⟩
    have e2 : gl (γ'⁻¹ * γ) * x i = x i * j (k' * k⁻¹) := by
      calc gl (γ'⁻¹ * γ) * x i = (gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹)) * (j (k * k'⁻¹))⁻¹ := by group
        _ = x i * j (k' * k⁻¹) := by
          rw [← e]
          simp only [map_mul, map_inv]
          group
    have hρ : ρ (k' * k⁻¹) = 1 := hstab i _ _ e2
    have : ρ k⁻¹ = ρ k'⁻¹ := by
      calc ρ k⁻¹ = ρ (k'⁻¹ * (k' * k⁻¹)) := by group
        _ = ρ k'⁻¹ * ρ (k' * k⁻¹) := map_mul _ _ _
        _ = ρ k'⁻¹ := by rw [hρ, mul_one]
    rw [this]
  choose γf iF kF hg using hcov
  refine ⟨fun g => ρ (kF g)⁻¹ (v (iF g)), ?_, ?_, ?_⟩
  · intro γ g
    have h : gl (γf (gl γ * g)) * x (iF (gl γ * g)) * j (kF (gl γ * g)) =
        gl (γ * γf g) * x (iF g) * j (kF g) := by
      rw [← hg (gl γ * g)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    exact (key _ _ _ _ _ _ h).2
  · intro g k
    have h : gl (γf (g * j k)) * x (iF (g * j k)) * j (kF (g * j k)) =
        gl (γf g) * x (iF g) * j (kF g * k) := by
      rw [← hg (g * j k)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, mul_inv_rev, map_mul]
    rfl
  · intro i
    have h : gl (γf (x i)) * x (iF (x i)) * j (kF (x i)) = gl 1 * x i * j 1 := by
      rw [← hg (x i), map_one, map_one, one_mul, mul_one]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, inv_one, map_one]
    rfl
end

section

theorem UpperTheory.exists_linear_preimage_of_successive_approximation :
    ∀ (A M ι : Type) [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (I : Ideal A) [IsAdicComplete I A] (V : ℕ → Submodule A M) (σ : (ι → A) →ₗ[A] M), Antitone V → (∀ k, (I ^ k • ⊤ : Submodule A M) ≤ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ f - σ a ∈ V (j + 1)) → ∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ σ a = f := by
  intro A M ι _ _ _ _ I _ V σ hV hI hsep hstep j f hf
  classical
  let a' : ℕ → M → ι → A := fun k g => if h : g ∈ V k then (hstep k g h).choose else 0
  have ha' : ∀ k g, g ∈ V k → (∀ i, a' k g i ∈ I ^ k) ∧ g - σ (a' k g) ∈ V (k + 1) := by
    intro k g h
    simp only [a', dif_pos h]
    exact (hstep k g h).choose_spec
  let r : ℕ → M := fun n => Nat.rec f (fun n g => g - σ (a' (j + n) g)) n
  have hrs : ∀ n, r (n + 1) = r n - σ (a' (j + n) (r n)) := fun n => rfl
  have hr : ∀ n, r n ∈ V (j + n) := by
    intro n
    induction n with
    | zero => exact hf
    | succ n ih =>
      rw [hrs, ← add_assoc]
      exact (ha' _ _ ih).2
  let b : ℕ → ι → A := fun n => a' (j + n) (r n)
  have hb : ∀ n i, b n i ∈ I ^ (j + n) := fun n => (ha' _ _ (hr n)).1
  have hrsum : ∀ N, r N = f - σ (∑ n ∈ Finset.range N, b n) := by
    intro N
    induction N with
    | zero => simp [r]
    | succ N ih =>
      show r N - σ (b N) = f - σ (∑ n ∈ Finset.range (N + 1), b n)
      rw [ih, Finset.sum_range_succ, map_add (f := _)]
      abel
  have hlim : ∀ i, ∃ L : A, ∀ n,
      (∑ k ∈ Finset.range n, b k i) ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] := by
    intro i
    refine IsPrecomplete.prec (inferInstance : IsPrecomplete I A) ?_
    intro m n hmn
    rw [SModEq.sub_mem, ← neg_sub, Submodule.neg_mem_iff, ← Finset.sum_Ico_eq_sub _ hmn]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have hmk : m ≤ j + k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    simpa using Submodule.smul_mem_smul (Ideal.pow_le_pow_right hmk (hb k i))
      (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
  choose L hL using hlim
  refine ⟨L, fun i => ?_, ?_⟩
  · have h1 := SModEq.sub_mem.mp (hL i j)
    have h2 : (∑ k ∈ Finset.range j, b k i) ∈ I ^ j :=
      Submodule.sum_mem _ (fun k _ => Ideal.pow_le_pow_right (by omega) (hb k i))
    have h1' : (∑ k ∈ Finset.range j, b k i) - L i ∈ I ^ j := by
      simpa [smul_eq_mul, Ideal.mul_top] using h1
    simpa using Submodule.sub_mem _ h2 h1'
  · have h0 : f - σ L = 0 := by
      apply hsep
      intro N
      have hv : ∀ i, ((∑ n ∈ Finset.range N, b n) - L) i ∈ I ^ N := by
        intro i
        have := SModEq.sub_mem.mp (hL i N)
        simpa [Finset.sum_apply, smul_eq_mul, Ideal.mul_top] using this
      have hσ : σ ((∑ n ∈ Finset.range N, b n) - L) ∈ (I ^ N • ⊤ : Submodule A M) := by
        set v := (∑ n ∈ Finset.range N, b n) - L

        rw [pi_eq_sum_univ v, map_sum]
        refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [map_smul]
        exact Submodule.smul_mem_smul (hv i) Submodule.mem_top
      have e : f - σ L = r N + σ ((∑ n ∈ Finset.range N, b n) - L) := by
        rw [hrsum, map_sub]
        abel
      rw [e]
      exact Submodule.add_mem _ (hV (by omega : N ≤ j + N) (hr N)) (hI N hσ)
    exact (sub_eq_zero.mp h0).symm
end

section

open IsLocalRing

theorem UpperTheory.krullDim_quotient_le_card_of_radical_parameters :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (q : Ideal B) (κ : Type) [Finite κ] (x : κ → B), (∀ k, x k ∈ maximalIdeal B) → (∀ p : Ideal B, p.IsPrime → q ≤ p → (∀ k, x k ∈ p) → maximalIdeal B ≤ p) → ringKrullDim (B ⧸ q) ≤ Nat.card κ := by
  intro B _ _ _ q κ _ x hx h
  classical
  by_cases hq : q = ⊤
  · subst hq
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  haveI : Nontrivial (B ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hq
  haveI : IsLocalRing (B ⧸ q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let s : Set (B ⧸ q) := Set.range (fun k => Ideal.Quotient.mk q (x k))
  have hs : s.Finite := Set.finite_range _
  have hmin : maximalIdeal (B ⧸ q) ∈ (Ideal.span s).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact map_nonunit (Ideal.Quotient.mk q) _ (hx k)
    · rintro P ⟨hP, hsP⟩ _
      have h1 : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk q) := by
        refine h _ (Ideal.comap_isPrime _ _) ?_ ?_
        · intro a ha
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
          exact P.zero_mem
        · intro k
          exact hsP (Ideal.subset_span ⟨k, rfl⟩)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply h1
      rw [mem_maximalIdeal] at hy ⊢
      exact fun hu => hy (hu.map _)
  have h2 := Ideal.height_le_card_of_mem_minimalPrimes_span hs hmin
  have h3 : s.ncard ≤ Nat.card κ := by
    rw [← Set.ncard_univ, show s = (fun k => Ideal.Quotient.mk q (x k)) '' Set.univ from Set.image_univ.symm]
    exact Set.ncard_image_le Set.finite_univ
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have h4 : (maximalIdeal (B ⧸ q)).height ≤ (Nat.card κ : ℕ∞) := h2.trans (by exact_mod_cast h3)
  exact_mod_cast h4
end
