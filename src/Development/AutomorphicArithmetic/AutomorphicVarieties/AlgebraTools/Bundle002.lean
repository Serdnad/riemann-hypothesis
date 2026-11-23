module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem sum_matrix_single_diag_one_eq_one {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n] :
    ∑ i : n, Matrix.single i i (1 : F) = 1 := by
  ext u v
  by_cases h : u = v
  · subst h
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
    have he : (Finset.univ.filter fun w : n => w = u ∧ w = v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨rfl, rfl⟩
      exact h rfl
    rw [he]
    simp

private theorem intertwiner_of_ker {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (ht : ∀ B : Matrix (d t) (d t) F, ∃ x ∈ S, x t = B)
    (hk : ∀ x ∈ S, x t = 0 → x s = 0) :
    ∃ V : Matrix (d s) (d t) F, V ≠ 0 ∧ ∀ x ∈ S, x s * V = V * x t := by
  have key : ∀ x ∈ S, ∀ y ∈ S, x t = y t → x s = y s := by
    intro x hx y hy h
    have := hk (x - y) (S.sub_mem hx hy) (by rw [Pi.sub_apply, h, sub_self])
    rw [Pi.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨i0⟩ := (inferInstance : Nonempty (d t))
  choose xx hxS hxt using fun j => ht (Matrix.single j i0 (1 : F))
  choose z hzS hzt using fun j => ht (Matrix.single i0 j (1 : F))
  have hne : xx i0 s ≠ 0 := by
    intro h0
    have hx0 : ∀ j, xx j s = 0 := by
      intro j
      have := key (xx j * xx i0) (S.mul_mem (hxS j) (hxS i0)) (xx j) (hxS j)
        (by rw [Pi.mul_apply, hxt, hxt, Matrix.single_mul_single_same, one_mul])
      rw [← this, Pi.mul_apply, h0, mul_zero]
    have h1 := key (∑ j, xx j * z j) (Subalgebra.sum_mem _ fun j _ => S.mul_mem (hxS j) (hzS j)) 1 S.one_mem
      (by
        rw [Finset.sum_apply]
        simp only [Pi.mul_apply, hxt, hzt, Matrix.single_mul_single_same, one_mul, Pi.one_apply]
        exact sum_matrix_single_diag_one_eq_one)
    rw [Finset.sum_apply] at h1
    simp only [Pi.mul_apply, hx0, zero_mul, Finset.sum_const_zero, Pi.one_apply] at h1
    exact zero_ne_one h1
  obtain ⟨a, b, hab⟩ : ∃ a b, xx i0 s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Matrix.ext h)
  refine ⟨Matrix.of fun u j => xx j s u b, ?_, ?_⟩
  · intro hV
    apply hab
    have := congrFun (congrFun hV a) i0
    simpa using this
  · intro x hx
    ext u k
    have e := key (x * xx k) (S.mul_mem hx (hxS k)) (∑ j, x t j k • xx j)
      (Subalgebra.sum_mem _ fun j _ => S.smul_mem (hxS j) _) (by
        rw [Pi.mul_apply, hxt, Finset.sum_apply]
        simp only [Pi.smul_apply, hxt]
        ext p q
        by_cases hq : i0 = q <;> simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, hq])
    have e2 := congrFun (congrFun e u) b
    simp only [Pi.mul_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply] at e2
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [e2]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem separate {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (hs : ∀ B : Matrix (d s) (d s) F, ∃ x ∈ S, x s = B)
    (hk : ∃ x ∈ S, x t = 0 ∧ x s ≠ 0) : ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
  obtain ⟨x, hxS, hxt, hxs⟩ := hk
  obtain ⟨a, b, hab⟩ : ∃ a b, x s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxs (Matrix.ext h)
  choose p hpS hps using fun i => hs (Matrix.single i a (x s a b)⁻¹)
  choose q hqS hqs using fun i => hs (Matrix.single b i (1 : F))
  refine ⟨∑ i, p i * x * q i, ?_, ?_, ?_⟩
  · exact Subalgebra.sum_mem _ fun i _ => S.mul_mem (S.mul_mem (hpS i) hxS) (hqS i)
  · rw [Finset.sum_apply]
    simp [Pi.mul_apply, hxt]
  · rw [Finset.sum_apply]
    simp only [Pi.mul_apply, hps, hqs, Matrix.single_mul_mul_single, inv_mul_cancel₀ hab, one_mul]
    ext u v
    by_cases h : u = v
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
      have he : (Finset.univ.filter fun w : d s => w = u ∧ w = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨rfl, rfl⟩
        exact h rfl
      rw [he]
      simp

theorem UpperTheory.V.AlgebraTools.density_prod :
    ∀ {F Γ : Type} [Field F] [Monoid Γ] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (ρ : ∀ s, Γ →* Matrix (d s) (d s) F), (∀ s, Submodule.span F (Set.range (ρ s)) = ⊤) → (∀ s t, s ≠ t → ∀ V : Matrix (d s) (d t) F, (∀ g, ρ s g * V = V * ρ t g) → V = 0) → Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) = ⊤ := by
  intro F Γ _ _ σ _ _ d _ _ _ ρ hspan hint
  let φ : Γ →* ((s : σ) → Matrix (d s) (d s) F) :=
    { toFun := fun g s => ρ s g
      map_one' := funext fun s => map_one (ρ s)
      map_mul' := fun g h => funext fun s => map_mul (ρ s) g h }
  obtain ⟨S, hSdef⟩ : ∃ S : Subalgebra F ((s : σ) → Matrix (d s) (d s) F),
      S = Algebra.adjoin F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) := ⟨_, rfl⟩
  have hmem : ∀ g, (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F) ∈ S := by
    intro g
    rw [hSdef]
    exact Algebra.subset_adjoin ⟨g, rfl⟩
  have hsurj : ∀ s (B : Matrix (d s) (d s) F), ∃ x ∈ S, x s = B := by
    intro s B
    have hB : B ∈ Submodule.span F (Set.range (ρ s)) := by
      rw [hspan s]
      exact Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact ⟨_, hmem g, rfl⟩
    | zero => exact ⟨0, S.zero_mem, rfl⟩
    | add y z _ _ hy hz =>
      obtain ⟨x1, h1, e1⟩ := hy
      obtain ⟨x2, h2, e2⟩ := hz
      exact ⟨x1 + x2, S.add_mem h1 h2, by rw [Pi.add_apply, e1, e2]⟩
    | smul c y _ hy =>
      obtain ⟨x1, h1, e1⟩ := hy
      exact ⟨c • x1, S.smul_mem h1 c, by rw [Pi.smul_apply, e1]⟩
  have hsep : ∀ s t, s ≠ t → ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
    intro s t hst
    apply separate d S s t (hsurj s)
    by_contra hno
    push_neg at hno
    obtain ⟨V, hV0, hV⟩ := intertwiner_of_ker d S s t (hsurj t) hno
    exact hV0 (hint s t hst V fun g => hV _ (hmem g))
  have he : ∀ s, ∃ e ∈ S, e s = 1 ∧ ∀ t, t ≠ s → e t = 0 := by
    intro s
    have hT : ∀ T : Finset σ, s ∉ T → ∃ e ∈ S, e s = 1 ∧ ∀ t ∈ T, e t = 0 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro _
        exact ⟨1, S.one_mem, rfl, by simp⟩
      | @insert t T htT ih =>
        intro hs
        rw [Finset.mem_insert, not_or] at hs
        obtain ⟨e, heS, hes, het⟩ := ih hs.2
        obtain ⟨y, hyS, hyt, hys⟩ := hsep s t hs.1
        refine ⟨e * y, S.mul_mem heS hyS, by rw [Pi.mul_apply, hes, hys, one_mul], ?_⟩
        intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · rw [Pi.mul_apply, hyt, mul_zero]
        · rw [Pi.mul_apply, het u hu, zero_mul]
    obtain ⟨e, heS, hes, het⟩ := hT (Finset.univ.erase s) (by simp)
    exact ⟨e, heS, hes, fun t ht => het t (by simp [ht])⟩
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro Y _
    choose e heS hes het using he
    choose zz hzS hzs using fun s => hsurj s (Y s)
    have hY : Y = ∑ s, zz s * e s := by
      funext u
      rw [Finset.sum_apply, Finset.sum_eq_single u]
      · rw [Pi.mul_apply, hzs, hes, mul_one]
      · intro b _ hb
        rw [Pi.mul_apply, het b u hb.symm, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ u) h
    rw [hY]
    exact Subalgebra.sum_mem _ fun s _ => S.mul_mem (hzS s) (heS s)
  have h2 : Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) =
      Subalgebra.toSubmodule S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hmem g
    · rw [hSdef, Algebra.adjoin_eq_span, Submodule.span_le]
      intro x hx
      have hx' : x ∈ MonoidHom.mrange φ :=
        (Submonoid.closure_le.mpr (by rintro _ ⟨g, rfl⟩; exact MonoidHom.mem_mrange.mpr ⟨g, rfl⟩)) hx
      obtain ⟨g, rfl⟩ := MonoidHom.mem_mrange.mp hx'
      exact Submodule.subset_span ⟨g, rfl⟩
  rw [h2, htop]
  simp
end

section

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.length_quotient_fg_bounds {A : Type} [CommRing A] (H : Type) [AddCommGroup H] [Module A H]
    (r : ℕ) (π : H →ₗ[A] (Fin r → A)) (hπ : Function.Surjective π) (I : Ideal A) :
    Module.length A (Fin r → A ⧸ I) ≤ Module.length A (H ⧸ I • (⊤ : Submodule A H)) ∧
    Module.length A (H ⧸ I • (⊤ : Submodule A H)) ≤
      Module.length A (Fin r → A ⧸ I) + Module.length A (LinearMap.ker π) := by
  classical
  let N := I • (⊤ : Submodule A H)
  let φ : H →ₗ[A] (Fin r → A ⧸ I) := LinearMap.pi fun i => I.mkQ ∘ₗ (LinearMap.proj i ∘ₗ π)
  have hφ : ∀ h i, φ h i = Submodule.Quotient.mk (π h i) := fun h i => rfl
  have hNφ : N ≤ LinearMap.ker φ := by
    rw [Submodule.smul_le]
    intro a ha h _
    rw [LinearMap.mem_ker]
    funext i
    rw [hφ, map_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact I.mul_mem_right _ ha
  let φ' := N.liftQ φ hNφ
  have hφ' : ∀ h, φ' (N.mkQ h) = φ h := fun h => rfl
  have hsurj : Function.Surjective φ' := by
    intro y
    choose z hz using fun i => Submodule.Quotient.mk_surjective I (y i)
    obtain ⟨h, rfl⟩ := hπ z
    refine ⟨N.mkQ h, ?_⟩
    funext i
    rw [hφ', hφ, hz]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∀ v, π (s v) = v := fun v => LinearMap.congr_fun hs v
  let ρ : LinearMap.ker π →ₗ[A] LinearMap.ker φ' :=
    (N.mkQ ∘ₗ (LinearMap.ker π).subtype).codRestrict (LinearMap.ker φ') (by
      intro k
      rw [LinearMap.mem_ker, LinearMap.comp_apply, hφ']
      funext i
      rw [hφ, Submodule.subtype_apply, LinearMap.mem_ker.1 k.2]
      simp)
  have hρ : Function.Surjective ρ := by
    rintro ⟨x, hx⟩
    obtain ⟨h, rfl⟩ := N.mkQ_surjective x
    rw [LinearMap.mem_ker, hφ'] at hx
    have hI : ∀ i, π h i ∈ I := fun i => by
      have := congrFun hx i
      rw [hφ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    have hsN : s (π h) ∈ N := by

      rw [pi_eq_sum_univ (π h), map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem_smul (hI i) trivial
    have hk : h - s (π h) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, hs', sub_self]
    refine ⟨⟨_, hk⟩, ?_⟩
    apply Subtype.ext
    change N.mkQ (h - s (π h)) = N.mkQ h
    have h0 : N.mkQ (s (π h)) = 0 := (Submodule.Quotient.mk_eq_zero N).2 hsN
    rw [map_sub, h0, sub_zero]
  have hex := Module.length_eq_add_of_exact (LinearMap.ker φ').subtype φ'
    (Submodule.subtype_injective _) hsurj (LinearMap.exact_subtype_ker_map φ')
  refine ⟨Module.length_le_of_surjective φ' hsurj, ?_⟩
  rw [hex, add_comm]
  exact add_le_add le_rfl (Module.length_le_of_surjective ρ hρ)

private theorem UpperTheory.V.AlgebraTools.len_fg_quot_tors {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] (hT : Module.IsTorsion A T) :
    Module.length A T ≠ ⊤ := by
  classical
  obtain ⟨x, hxann, hx⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hT
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  have hspan : Ideal.span {x} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hspan hϖ
  have hJ : Ideal.span {x} = maximalIdeal A ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' A T
  let I : Ideal A := maximalIdeal A ^ n
  have hIf : I • (⊤ : Submodule A (Fin k → A)) ≤ LinearMap.ker f := by
    rw [Submodule.smul_le]
    intro a ha v _
    rw [LinearMap.mem_ker, map_smul]
    have ha' : a ∈ Ideal.span {x} := by rw [hJ]; exact ha
    rw [Ideal.mem_span_singleton'] at ha'
    obtain ⟨c, rfl⟩ := ha'
    rw [mul_smul, (Submodule.mem_annihilator.1 hxann) _ trivial, smul_zero]
  have hsurj : Function.Surjective ((I • (⊤ : Submodule A (Fin k → A))).liftQ f hIf) := by
    intro t
    obtain ⟨v, rfl⟩ := hf t
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  have h1 := (UpperTheory.V.AlgebraTools.length_quotient_fg_bounds (Fin k → A) k LinearMap.id
    Function.surjective_id I).2
  have hker : Module.length A (LinearMap.ker (LinearMap.id : (Fin k → A) →ₗ[A] (Fin k → A))) = 0 := by
    rw [Module.length_eq_zero_iff]
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [LinearMap.mem_ker, LinearMap.id_apply] at ha hb
    subst ha hb
    rfl
  have h2 : Module.length A (Fin k → A ⧸ I) = (k * n : ℕ) := by
    rw [Module.length_pi, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    simp
  have h3 := Module.length_le_of_surjective _ hsurj
  rw [hker, add_zero, h2] at h1
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) (h3.trans h1)

theorem UpperTheory.V.AlgebraTools.len_fg_quot :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (H : Type) [AddCommGroup H] [Module A H] [Module.Finite A H], ∃ c : ℕ, Module.length A (Submodule.torsion A H) = c ∧ ∀ j : ℕ, ((Module.finrank A H * j : ℕ) : ℕ∞) ≤ Module.length A (H ⧸ maximalIdeal A ^ j • (⊤ : Submodule A H)) ∧ Module.length A (H ⧸ maximalIdeal A ^ j • (⊤ : Submodule A H)) ≤ ((Module.finrank A H * j + c : ℕ) : ℕ∞) := by
  intro A _ _ _ H _ _ _
  classical
  let Tor := Submodule.torsion A H
  haveI : Module.Free A (H ⧸ Tor) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis A (H ⧸ Tor)
  have hm : Module.finrank A (H ⧸ Tor) = Module.finrank A H :=
    finrank_quotient_eq_of_le_torsion le_rfl
  let π : H →ₗ[A] (Fin (Module.finrank A (H ⧸ Tor)) → A) := b.equivFun.toLinearMap ∘ₗ Tor.mkQ
  have hπ : Function.Surjective π := b.equivFun.surjective.comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker π = Tor := by
    simp only [π, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  have hTf : Module.length A Tor ≠ ⊤ :=
    UpperTheory.V.AlgebraTools.len_fg_quot_tors Tor (Submodule.torsion_isTorsion)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hTf
  refine ⟨c, hc.symm, fun j => ?_⟩
  have h := UpperTheory.V.AlgebraTools.length_quotient_fg_bounds H _ π hπ (maximalIdeal A ^ j)
  have hlen : Module.length A (Fin (Module.finrank A (H ⧸ Tor)) → A ⧸ maximalIdeal A ^ j) =
      ((Module.finrank A H * j : ℕ) : ℕ∞) := by
    rw [Module.length_pi, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, hm]
    simp
  rw [hlen, hker, ← hc] at h
  refine ⟨h.1, ?_⟩
  rw [Nat.cast_add]
  exact h.2
end

section

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.sep_chars :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Monoid Γ] {n : ℕ} (ψ : Fin n → Γ →* R), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp (ψ i)) → ∃ z : MonoidAlgebra R Γ, ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift R R Γ (ψ i) z - MonoidAlgebra.lift R R Γ (ψ j) z) := by
  intro R Γ _ _ _ n ψ hcard hinj
  let χ : Fin n → Γ →* ResidueField R := fun i => (residue R : R →* ResidueField R).comp (ψ i)
  have hχ : ∀ i g, χ i g = residue R (ψ i g) := fun i g => rfl
  obtain ⟨a⟩ := (Cardinal.le_def (Fin n) (ResidueField R)).mp (by rwa [Cardinal.mk_fin])
  let L : (Γ →₀ ResidueField R) →ₗ[ResidueField R] (Fin n → ResidueField R) :=
    Finsupp.linearCombination (ResidueField R) (fun g i => χ i g)
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hli := (linearIndependent_monoidHom Γ (ResidueField R)).comp χ hinj
    rw [Fintype.linearIndependent_iff] at hli
    let c : Fin n → ResidueField R := fun i => f (fun j => if i = j then 1 else 0)
    have hf : ∀ v, f v = ∑ i, v i * c i := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]

      simp [c, map_sum, map_smul]
    have hc : ∀ i, c i = 0 := by
      apply hli c
      funext g
      have hg : (fun i => χ i g) ∈ LinearMap.range L :=
        ⟨Finsupp.single g 1, by simp [L]⟩
      have h0 := hle hg
      rw [LinearMap.mem_ker, hf] at h0
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    apply hf0
    ext v
    simp [hf, hc]
  obtain ⟨w, hw⟩ := hsurj (fun i => a i)
  let s := Function.surjInv (IsLocalRing.residue_surjective (R := R))
  let z : MonoidAlgebra R Γ := ∑ g ∈ w.support, MonoidAlgebra.single g (s (w g))
  have hz : ∀ i, residue R (MonoidAlgebra.lift R R Γ (ψ i) z) = a i := by
    intro i
    have hwi := congrFun hw i
    rw [← hwi]

    simp only [z, L, map_sum, MonoidAlgebra.lift_single, Finsupp.linearCombination_apply,
    Finsupp.sum, Finset.sum_apply, smul_eq_mul, map_mul, hχ]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Function.surjInv_eq (IsLocalRing.residue_surjective (R := R))]
    rfl
  refine ⟨z, fun i j hij => ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hz, hz, sub_ne_zero]
  exact fun h => hij (a.injective h)
end

section

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.tri_prod_zero :
    ∀ {R : Type} [CommRing R] {n : ℕ} (u : Fin n → Matrix (Fin n) (Fin n) R), (∀ k i j, j < i → u k i j = 0) → (∀ k, u k k k = 0) → (List.ofFn u).prod = 0 := by
  intro R _ n u h1 h2
  have key : ∀ m, m ≤ n → ∀ i j : Fin n, j.val < m →
      ((List.ofFn u).take m).prod i j = 0 := by
    intro m
    induction m with
    | zero => intro _ i j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm i j hj
      have hlen : m < (List.ofFn u).length := by
        rw [List.length_ofFn]; omega
      rw [List.prod_take_succ _ _ hlen, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val < m
      · rw [ih (by omega) i l hl, zero_mul]
      · have hu : (List.ofFn u)[m] = u ⟨m, by omega⟩ := by
          simp
        rw [hu]
        by_cases hjl : j < l
        · rw [h1 _ _ _ hjl, mul_zero]
        · have hjl' : l.val ≤ j.val := Fin.le_def.mp (not_lt.mp hjl)
          have e1 : l = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : j = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          rw [e1, e2, h2, mul_zero]
  ext i j
  have := key n le_rfl i j j.isLt
  rw [List.take_of_length_le (by simp)] at this
  simpa using this
end
