module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Henselian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle005
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle002
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Isomorphisms
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.sqrt_of_residue {R' : Type} [CommRing R'] [HenselianLocalRing R']
    (h2 : IsUnit (2 : R')) (u : R') (hu : IsUnit u) (hs : IsSquare (residue R' u)) :
    ∃ a : R', a * a = u := by
  obtain ⟨b, hb⟩ := hs
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective b
  have hres : residue R' (a₀ ^ 2 - u) = 0 := by rw [map_sub, map_pow, hb, pow_two, sub_self]
  have ha₀ : IsUnit a₀ := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    intro h0
    have hu0 : residue R' u = 0 := by rw [hb, h0, mul_zero]
    exact (hu.map (residue R')).ne_zero hu0
  have hev : eval a₀ (X ^ 2 - C u) ∈ maximalIdeal R' := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa using hres
  have hd : eval a₀ (derivative (X ^ 2 - C u)) = 2 * a₀ := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X]
    norm_num
  have hdu : IsUnit (eval a₀ (derivative (X ^ 2 - C u))) := by
    rw [hd]
    exact h2.mul ha₀
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C u)
    (monic_X_pow_sub_C u two_ne_zero) a₀ hev hdu
  refine ⟨a, ?_⟩
  have h0 := ha.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at h0
  rw [← pow_two]
  exact sub_eq_zero.mp h0

theorem UpperTheory.V.AlgebraTools.orthonormal_local :
    ∀ {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [HenselianLocalRing R'] (φ : R →+* R') {n : ℕ} (H : Matrix (Fin n) (Fin n) R), IsUnit (2 : R) → Hᵀ = H → IsUnit H.det → (∀ c : Rˣ, IsSquare (residue R' (φ c))) → ∃ P : GL (Fin n) R', (P : Matrix (Fin n) (Fin n) R')ᵀ * H.map φ * P = 1 := by
  intro R R' _ _ _ _ φ n H h2 hT hdet hsq
  obtain ⟨P, c, hP⟩ := UpperTheory.V.AlgebraTools.diag_local H h2 hT hdet
  have h2' : IsUnit (2 : R') := by
    have h := h2.map φ
    rwa [map_ofNat] at h
  have hroot : ∀ i, ∃ a : R', a * a = φ (c i) := fun i =>
    UpperTheory.V.AlgebraTools.sqrt_of_residue h2' _ ((c i).isUnit.map φ) (hsq (c i))
  choose a ha using hroot
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := a i) (by rw [ha i]; exact (c i).isUnit.map φ)
  let D : GL (Fin n) R' :=
    ⟨diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R'), diagonal fun i => a i,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp⟩
  have hmap : ((Matrix.GeneralLinearGroup.map φ P : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      (P : Matrix (Fin n) (Fin n) R).map φ := by
    ext i j
    exact Matrix.GeneralLinearGroup.map_apply φ i j P
  have key : ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
      (P : Matrix (Fin n) (Fin n) R).map φ = diagonal fun i => φ (c i) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hP, diagonal_map (map_zero φ)]
  refine ⟨Matrix.GeneralLinearGroup.map φ P * D, ?_⟩
  rw [Units.val_mul, hmap, Matrix.transpose_mul]
  have hD : ((D : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R') := rfl
  calc ((D : Matrix (Fin n) (Fin n) R'))ᵀ * ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        ((P : Matrix (Fin n) (Fin n) R).map φ * (D : Matrix (Fin n) (Fin n) R'))
      = ((D : Matrix (Fin n) (Fin n) R'))ᵀ * (((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        (P : Matrix (Fin n) (Fin n) R).map φ) * (D : Matrix (Fin n) (Fin n) R') := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [key, hD, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
      convert diagonal_one using 2
      funext i
      rw [← ha i]
      calc ((hau i).unit⁻¹ : R'ˣ).val * (a i * a i) * ((hau i).unit⁻¹ : R'ˣ).val
          = (((hau i).unit⁻¹ : R'ˣ).val * (hau i).unit.val) *
            ((hau i).unit.val * ((hau i).unit⁻¹ : R'ˣ).val) := by
            simp only [IsUnit.unit_spec]; ring
        _ = 1 := by simp
end

section

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.cocycle_trace_zero :
    ∀ {K G : Type} [CommRing K] [Group G] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (r : G →* (∀ s, Matrix (d s) (d s) K)) (φ : G → ∀ s, Matrix (d s) (d s) K), Submodule.span K (Set.range r) = ⊤ → (∀ g h, φ (g * h) = φ g + r g * φ h * r g⁻¹) → (∀ g, ∑ s, ((φ g * r g) s).trace = 0) → ∃ Y, ∀ g, φ g = Y - r g * Y * r g⁻¹ := by
  intro K G _ _ σ _ _ d _ _ _ r φ hspan hφ htr
  classical
  let m : G → ∀ s, Matrix (d s) (d s) K := fun g => φ g * r g
  have hinv : ∀ g, r g⁻¹ * r g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : ∀ g, r g * r g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hm : ∀ g h, m (g * h) = m g * r h + r g * m h := by
    intro g h
    simp only [m, hφ, map_mul, add_mul, mul_assoc]
    rw [← mul_assoc (r g⁻¹), hinv, one_mul]
  let T : (∀ s, Matrix (d s) (d s) K) →ₗ[K] K :=
    ∑ s, (Matrix.traceLinearMap (d s) K K) ∘ₗ LinearMap.proj s
  have hT : ∀ x, T x = ∑ s, (x s).trace := by
    intro x
    simp [T, LinearMap.sum_apply]
  have hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0 := by
    intro x hx
    funext s
    rw [Matrix.ext_iff_trace_mul_right]
    intro y
    have := hx (Pi.single s y)
    rw [hT, Finset.sum_eq_single s] at this
    · simpa using this
    · intro t _ ht
      simp [Pi.single_eq_of_ne ht]
    · simp
  have hkey : ∀ g h, T (m g * r h) = - T (r g * m h) := by
    intro g h
    have : T (m (g * h)) = 0 := by rw [hT]; exact htr _
    rw [hm, map_add (f := _)] at this
    exact eq_neg_of_add_eq_zero_left this
  let R := Finsupp.linearCombination K (fun g => r g)
  let M := Finsupp.linearCombination K m
  have hR : Function.Surjective R := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  have hkey2 : ∀ f h, T (M f * r h) = - T (R f * m h) := by
    intro f h
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add (f := _), add_mul, h₁, h₂]; ring
    | single g a =>
      simp only [R, M, Finsupp.linearCombination_single, smul_mul_assoc, map_smul, hkey, smul_neg]
  have hle : LinearMap.ker R ≤ LinearMap.ker M := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply hnd
    intro y
    have hy : y ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hkey2, hf]; simp
    | zero => simp
    | add x y _ _ h₁ h₂ => rw [mul_add, map_add (f := _), h₁, h₂, add_zero]
    | smul a x _ h₁ => rw [mul_smul_comm, map_smul, h₁, smul_zero]
  let D : (∀ s, Matrix (d s) (d s) K) →ₗ[K] (∀ s, Matrix (d s) (d s) K) :=
    (LinearMap.ker R).liftQ M hle ∘ₗ (R.quotKerEquivOfSurjective hR).symm.toLinearMap
  have hDR : ∀ f, D (R f) = M f := by
    intro f
    have : (R.quotKerEquivOfSurjective hR).symm (R f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp [D, this]
  have hDr : ∀ g, D (r g) = m g := by
    intro g
    simpa [R, M] using hDR (Finsupp.single g 1)
  have hder : ∀ x y, D (x * y) = D x * y + x * D y := by
    intro x y
    have hx : x ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    have hy : y ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      rw [← map_mul, hDr, hDr, hDr, hm]
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h₁ h₂ => simp only [add_mul, map_add (f := _), h₁, h₂]; abel
    | add_right x y z _ _ _ h₁ h₂ => simp only [mul_add, map_add (f := _), h₁, h₂]; abel
    | smul_left a x y _ _ h₁ => simp only [smul_mul_assoc, map_smul, h₁, smul_add]
    | smul_right a x y _ _ h₁ => simp only [mul_smul_comm, map_smul, h₁, smul_add]
  obtain ⟨Y, hY⟩ := UpperTheory.V.AlgebraTools.der_inner d (AlgHom.id K _) D hder
  refine ⟨Y, fun g => ?_⟩
  have h1 : φ g = m g * r g⁻¹ := by simp only [m, mul_assoc, hinv', mul_one]
  rw [h1, ← hDr, hY]
  simp only [AlgHom.id_apply, sub_mul]
  rw [mul_assoc Y, hinv', mul_one]
end

section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.lemma_B_range {A H Q : Type} [CommRing A] [AddCommGroup H] [Module A H]
    [AddCommGroup Q] [Module A Q] (N : Submodule A H) (φ : H →ₗ[A] Q) (h : N ≤ LinearMap.ker φ) :
    Module.length A (LinearMap.range φ) ≤ Module.length A (H ⧸ N) := by
  refine Module.length_le_of_surjective (N.liftQ φ.rangeRestrict (by rwa [LinearMap.ker_rangeRestrict])) ?_
  intro y
  obtain ⟨x, rfl⟩ := φ.surjective_rangeRestrict y
  exact ⟨N.mkQ x, rfl⟩

private theorem UpperTheory.V.AlgebraTools.lemma_B_sup {A Q : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    (P U V : Submodule A Q) (h : P ≤ U ⊔ V) :
    Module.length A P ≤ Module.length A U + Module.length A V := by
  have hsurj : Function.Surjective ((Submodule.inclusion (le_sup_left : U ≤ U ⊔ V)).coprod
      (Submodule.inclusion (le_sup_right : V ≤ U ⊔ V))) := by
    rintro ⟨y, hy⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  calc Module.length A P ≤ Module.length A (U ⊔ V : Submodule A Q) :=
        Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
    _ ≤ Module.length A (U × V) := Module.length_le_of_surjective _ hsurj
    _ = Module.length A U + Module.length A V := Module.length_prod _ _ _

private theorem UpperTheory.V.AlgebraTools.lemma_B_le {A M M' S : Type} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module.Finite A M'] (I : Ideal A) (f : S → M →ₗ[A] M') :
    ∃ c : ℕ, ∀ m : ℕ, (⨅ s, (I ^ (m + c) • (⊤ : Submodule A M')).comap (f s)) ≤
      (⨅ s, LinearMap.ker (f s)) ⊔ I ^ m • (⊤ : Submodule A M) := by
  classical
  obtain ⟨_, ⟨T, rfl⟩, hT⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A (M →ₗ[A] M'))
    (Set.range fun T : Finset S => Submodule.span A (f '' (T : Set S))) ⟨_, ⟨∅, rfl⟩⟩
  have hspan : ∀ s, f s ∈ Submodule.span A (f '' (T : Set S)) := by
    intro s
    by_contra hs
    refine hT _ ⟨insert s T, rfl⟩ (lt_of_le_of_ne (Submodule.span_mono ?_) ?_)
    · apply Set.image_mono
      rw [Finset.coe_insert]
      exact Set.subset_insert _ _
    · intro heq
      apply hs
      simp only at heq
      rw [heq]
      exact Submodule.subset_span ⟨s, by simp, rfl⟩
  have hker : ⨅ t : T, LinearMap.ker (f t) ≤ ⨅ s, LinearMap.ker (f s) := by
    intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    intro s
    have hle : Submodule.span A (f '' (T : Set S)) ≤
        LinearMap.ker (LinearMap.applyₗ (R := A) (M₂ := M') x) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      simpa using hx ⟨t, ht⟩
    simpa using hle (hspan s)
  let F : M →ₗ[A] (T → M') := LinearMap.pi fun t => f t
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.comap_pow_le I F
  refine ⟨c, fun m x hx => ?_⟩
  have hFx : F x ∈ I ^ (m + c) • (⊤ : Submodule A (T → M')) := by
    rw [← Finset.univ_sum_single (F x)]
    refine Submodule.sum_mem _ fun t _ => ?_
    have h1 : f t x ∈ I ^ (m + c) • (⊤ : Submodule A M') := by
      simpa using (Submodule.mem_iInf _).mp hx t
    simpa [F] using Submodule.smul_top_le_comap_smul_top (I ^ (m + c))
      (LinearMap.single A (fun _ : T => M') t) h1
  have hm := hc m hFx
  have hle : LinearMap.ker F ≤ ⨅ s, LinearMap.ker (f s) := by
    simp only [F, LinearMap.ker_pi]
    exact hker
  exact (sup_le_sup_right hle _) hm

theorem UpperTheory.V.AlgebraTools.lemma_B :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {M M' S : Type} [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (f : S → M →ₗ[A] M'), ∃ e : ℕ, ∀ j : ℕ, Module.length A ((⨅ s, (maximalIdeal A ^ j • (⊤ : Submodule A M')).comap (f s)).map (maximalIdeal A ^ j • (⊤ : Submodule A M)).mkQ) ≤ ((Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A M) * j + e : ℕ) : ℕ∞) := by
  intro A _ _ _ M M' S _ _ _ _ _ _ f
  set K : Submodule A M := ⨅ s, LinearMap.ker (f s) with hKdef
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.lemma_B_le (maximalIdeal A) f
  obtain ⟨cK, -, hK⟩ := UpperTheory.V.AlgebraTools.len_fg_quot (A := A) K
  obtain ⟨cM, -, hM⟩ := UpperTheory.V.AlgebraTools.len_fg_quot (A := A) M
  refine ⟨cK + Module.finrank A M * c + cM, fun j => ?_⟩
  set P := ⨅ s, (maximalIdeal A ^ j • (⊤ : Submodule A M')).comap (f s) with hPdef
  set N := maximalIdeal A ^ j • (⊤ : Submodule A M) with hNdef
  have hQ : Module.length A (P.map N.mkQ) ≤ Module.length A (M ⧸ N) :=
    Module.length_le_of_injective (Submodule.subtype _) (Submodule.injective_subtype _)
  by_cases hj : j < c
  · refine le_trans hQ (le_trans (hM j).2 ?_)
    have h1 := Nat.mul_le_mul_left (Module.finrank A M) hj.le
    have h2 := Nat.zero_le (Module.finrank A K * j)
    exact_mod_cast (show Module.finrank A M * j + cM ≤
      Module.finrank A K * j + (cK + Module.finrank A M * c + cM) by omega)
  · push_neg at hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + c := ⟨j - c, by omega⟩
    have hP : P ≤ K ⊔ maximalIdeal A ^ m • ⊤ := hc m
    have hU : Module.length A (K.map N.mkQ) ≤ ((Module.finrank A K * (m + c) + cK : ℕ) : ℕ∞) := by
      refine le_trans ?_ (hK (m + c)).2
      have := UpperTheory.V.AlgebraTools.lemma_B_range (maximalIdeal A ^ (m + c) • (⊤ : Submodule A K))
        (N.mkQ ∘ₗ K.subtype) ?_
      · rwa [LinearMap.range_comp, Submodule.range_subtype] at this
      · intro x hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_top_le_comap_smul_top _ K.subtype hx
    let g : (M ⧸ N) →ₗ[A] (M ⧸ (maximalIdeal A ^ m • (⊤ : Submodule A M))) :=
      N.liftQ (Submodule.mkQ _) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right m c)))
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
      exact ⟨N.mkQ x, rfl⟩
    have hV : (maximalIdeal A ^ m • (⊤ : Submodule A M)).map N.mkQ = LinearMap.ker g := by
      rw [Submodule.ker_liftQ, Submodule.ker_mkQ]
    have hlen := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
      (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)
    have hVb : Module.length A (LinearMap.ker g) ≤ ((Module.finrank A M * c + cM : ℕ) : ℕ∞) := by
      have h1 := (hM (m + c)).2
      have h2 := (hM m).1
      rw [hlen] at h1
      have h3 : Module.length A (LinearMap.ker g) + ((Module.finrank A M * m : ℕ) : ℕ∞) ≤
          ((Module.finrank A M * (m + c) + cM : ℕ) : ℕ∞) :=
        le_trans (add_le_add le_rfl h2) h1
      have hfin : Module.length A (LinearMap.ker g) ≠ ⊤ := by
        intro htop
        rw [htop, top_add, top_le_iff] at h3
        exact ENat.coe_ne_top _ h3
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← ha] at h3 ⊢
      norm_cast at h3 ⊢
      rw [Nat.mul_add] at h3
      omega
    calc Module.length A (P.map N.mkQ)
        ≤ Module.length A (K.map N.mkQ) +
          Module.length A ((maximalIdeal A ^ m • (⊤ : Submodule A M)).map N.mkQ) := by
          apply UpperTheory.V.AlgebraTools.lemma_B_sup
          rw [← Submodule.map_sup]
          exact Submodule.map_mono hP
      _ ≤ ((Module.finrank A K * (m + c) + cK : ℕ) : ℕ∞) + ((Module.finrank A M * c + cM : ℕ) : ℕ∞) := by
          rw [hV]
          exact add_le_add hU hVb
      _ = _ := by
          push_cast
          ring
end
