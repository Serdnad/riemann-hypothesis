module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory.ProjBij

theorem eq_bot_of_forall_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K : Submodule R M) (hK : K.FG) (h : ∀ m : Ideal R, m.IsMaximal → K ≤ m • K) : K = ⊥ := by
  rw [← Submodule.annihilator_eq_top_iff]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m K hK (h m hm)
  have h1 : r ∈ m := hle (Submodule.mem_annihilator.2 hr0)
  apply hm.ne_top
  rw [Ideal.eq_top_iff_one]
  have := m.sub_mem h1 hr
  simpa using this

theorem one_tmul_eq_zero_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (x : M) :
    ((1 : R ⧸ m) ⊗ₜ[R] x : (R ⧸ m) ⊗[R] M) = 0 ↔ x ∈ m • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M m).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

theorem exists_one_tmul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (y : (R ⧸ m) ⊗[R] M) : ∃ x : M, (1 : R ⧸ m) ⊗ₜ[R] x = y :=
  TensorProduct.mk_surjective R M (R ⧸ m) Ideal.Quotient.mk_surjective y

theorem bijective_of_injective_mod_maximal
    (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hinj : ∀ m : Ideal R, m.IsMaximal → ∀ x, f x ∈ m • (⊤ : Submodule R N) →
      x ∈ m • (⊤ : Submodule R M)) :
    Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    have key : (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊥ := by
      apply eq_bot_of_forall_le_smul _ Module.Finite.fg_top
      intro m hm y _
      letI := Ideal.Quotient.field m
      have hi : Function.Injective (f.baseChange (R ⧸ m)) := by
        set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
        intro z hz
        obtain ⟨x, rfl⟩ := exists_one_tmul m z
        rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hz
        exact (one_tmul_eq_zero_iff m x).2 (hinj m hm x hz)
      have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hrk m hm)).1 hi
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨z, hz⟩ := hs (1 ⊗ₜ n)
      obtain ⟨x, rfl⟩ := exists_one_tmul m z
      rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub,
        one_tmul_eq_zero_iff] at hz
      have h2 := Submodule.mem_map_of_mem (f := (LinearMap.range f).mkQ) hz
      rw [Submodule.map_smul''] at h2
      have h3 := Submodule.smul_mono (le_refl m) le_top h2
      have h4 : (LinearMap.range f).mkQ (f x) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self f x)
      rw [map_sub, h4, zero_sub] at h3
      exact (Submodule.neg_mem_iff _).1 h3
    intro n
    have : (Submodule.Quotient.mk n : N ⧸ LinearMap.range f) ∈ (⊥ : Submodule R _) := by
      rw [← key]; trivial
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at this
    exact this
  refine ⟨?_, hsurj⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hs' : ∀ n, f (s n) = n := fun n => LinearMap.congr_fun hs n
  let p : M →ₗ[R] M := LinearMap.id - s ∘ₗ f
  have hp : Submodule.map p ⊤ = LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      simp [p, hs']
    · intro x hx
      exact ⟨x, trivial, by simp [p, LinearMap.mem_ker.1 hx]⟩
  rw [← LinearMap.ker_eq_bot]
  apply eq_bot_of_forall_le_smul
  · rw [← hp]; exact Module.Finite.fg_top.map p
  · intro m hm x hx
    have hx0 : f x = 0 := hx
    have h1 := hinj m hm x (by rw [hx0]; exact Submodule.zero_mem _)
    have h2 := Submodule.mem_map_of_mem (f := p) h1
    rw [Submodule.map_smul'', hp] at h2
    simpa [p, hx0] using h2

end GlobalTheory.ProjBij
end

section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem projective_baseChange_of_presentation_split
    (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (r : Fin m → Fin n → R) (hr : Submodule.span R (Set.range r) = LinearMap.ker π)
    (v : Fin n → Fin n → B) (w : Fin n → Fin m → B)
    (hv : ∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0)
    (hvw : ∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) :
    Module.Projective B (B ⊗[R] M) := by
  classical

  let φ : (Fin n → R) →ₗ[R] (Fin n → B) := ∑ a, (LinearMap.proj a).smulRight (v a)
  have hφ : ∀ x l, φ x l = ∑ a, algebraMap R B (x a) * v a l := by
    intro x l
    simp [φ, Finset.sum_apply, Algebra.smul_def]
  have hker : LinearMap.ker π ≤ LinearMap.ker φ := by
    rw [← hr, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    funext l
    rw [hφ]
    simpa using hv b l
  let ψ : M →ₗ[R] (Fin n → B) :=
    (LinearMap.ker π).liftQ φ hker ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hψ : ∀ x, ψ (π x) = φ x := by
    intro x
    have : (π.quotKerEquivOfSurjective hπ).symm (π x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp [ψ, this]
  let i : B ⊗[R] M →ₗ[B] (Fin n → B) := ψ.liftBaseChange B
  let s : (Fin n → B) →ₗ[B] B ⊗[R] M :=
    ∑ l, (LinearMap.proj l).smulRight ((1 : B) ⊗ₜ[R] π (Pi.single l 1))
  have hs : ∀ y, s y = ∑ l, y l • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) := by
    intro y; simp [s]
  have hsr : ∀ b, ∑ l, algebraMap R B (r b l) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) = 0 := by
    intro b
    have h0 : π (r b) = 0 := by
      rw [← LinearMap.mem_ker, ← hr]; exact Submodule.subset_span ⟨b, rfl⟩
    have : ∑ l, algebraMap R B (r b l) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1))
        = (1 : B) ⊗ₜ[R] π (r b) := by
      conv_rhs => rw [show r b = ∑ l, r b l • Pi.single l (1 : R) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]

      simp [map_sum, tmul_sum, algebraMap_smul, tmul_smul]
    rw [this, h0, tmul_zero]
  have hsv : ∀ a, s (v a) = (1 : B) ⊗ₜ[R] π (Pi.single a 1) := by
    intro a
    rw [hs]
    simp_rw [hvw a, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ l, (w a b * algebraMap R B (r b l)) • ((1 : B) ⊗ₜ[R] π (Pi.single l 1)) = 0 := by
      intro b
      simp_rw [mul_smul, ← Finset.smul_sum, hsr, smul_zero]
    simp [this, ite_smul]
  have hsi : s ∘ₗ i = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    obtain ⟨z, rfl⟩ := hπ y
    simp only [LinearMap.comp_apply, LinearMap.id_apply, i, LinearMap.liftBaseChange_tmul, map_smul]
    have hz : φ z = ∑ a, z a • v a := by
      funext l; rw [hφ]; simp [Finset.sum_apply, Algebra.smul_def]

    rw [hψ, hz, map_sum]
    simp_rw [LinearMap.map_smul_of_tower, hsv]
    conv_rhs => rw [show z = ∑ a, z a • Pi.single a (1 : R) by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]

    rw [map_sum, tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_comm, TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_smul, TensorProduct.tmul_smul]
  exact Module.Projective.of_split i s hsi

end GlobalTheory
end

section

open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem projective_baseChange_presentation_matrix : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  intro R B M _ _ _ _ _ n m π hπ r hr hP
  let e := TensorProduct.piScalarRight R B B (Fin n)
  let πB : (Fin n → B) →ₗ[B] B ⊗[R] M := (π.baseChange B) ∘ₗ e.symm.toLinearMap
  have hπB : Function.Surjective πB := (LinearMap.lTensor_surjective B hπ).comp e.symm.surjective
  obtain ⟨i, hi⟩ := Module.projective_lifting_property πB LinearMap.id hπB
  let v : Fin n → Fin n → B := fun a => i ((1 : B) ⊗ₜ[R] π (Pi.single a 1))
  let f : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R r
  have hex : Function.Exact f π := by
    rw [LinearMap.exact_iff, Fintype.range_linearCombination, hr]
  have hexB := lTensor_exact B hex hπ
  let N : Submodule B (Fin n → B) := Submodule.span B (Set.range fun b l => algebraMap R B (r b l))
  have hker : ∀ y, πB y = 0 → y ∈ N := by
    intro y hy
    have h0 : (π.lTensor B) (e.symm y) = 0 := by
      have := hy
      simp only [πB, LinearMap.comp_apply, LinearEquiv.coe_coe] at this
      rwa [LinearMap.baseChange_eq_ltensor] at this
    obtain ⟨z, hz⟩ := (hexB _).1 h0
    have hy' : y = e (f.lTensor B z) := by rw [hz, LinearEquiv.apply_symm_apply]
    rw [hy']
    clear hz hy' h0 hy
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c =>
        have : e ((f.lTensor B) (x ⊗ₜ c)) = ∑ b, (x * algebraMap R B (c b)) • (fun l => algebraMap R B (r b l)) := by
          ext l
          simp [e, f, Fintype.linearCombination_apply, Finset.sum_apply, Algebra.smul_def, Finset.mul_sum,
            Finset.sum_mul, mul_comm, mul_left_comm]
        rw [this]
        exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact N.add_mem ha hb
  have hπv : ∀ a, πB (v a - Pi.single a 1) = 0 := by
    intro a
    have h1 : πB (v a) = (1 : B) ⊗ₜ[R] π (Pi.single a 1) := LinearMap.congr_fun hi _
    have h2 : e.symm (Pi.single a 1) = (1 : B) ⊗ₜ[R] (Pi.single a 1 : Fin n → R) := by
      rw [LinearEquiv.symm_apply_eq]
      ext l
      simp [e, Pi.single_apply]
    rw [map_sub, h1]
    simp [πB, h2]
  choose w hw using fun a => (Submodule.mem_span_range_iff_exists_fun B).1 (hker _ (hπv a))
  refine ⟨v, w, fun b l => ?_, fun a l => ?_⟩
  · have hrb : π (r b) = 0 := by
      have : r b ∈ LinearMap.ker π := hr ▸ Submodule.subset_span ⟨b, rfl⟩
      exact this
    have hsum : (1 : B) ⊗ₜ[R] π (r b) = ∑ a, algebraMap R B (r b a) • ((1 : B) ⊗ₜ[R] π (Pi.single a 1)) := by
      conv_lhs => rw [← Finset.univ_sum_single (r b)]

      simp only [map_sum, TensorProduct.tmul_sum, algebraMap_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← TensorProduct.tmul_smul, ← map_smul]
      congr 2
      ext j
      simp [Pi.single_apply]
    have h1 : ∑ a, algebraMap R B (r b a) • v a = 0 := by

      simp only [v, ← map_smul, ← map_sum, ← hsum, hrb, TensorProduct.tmul_zero, map_zero]
    have := congrFun h1 l
    simpa [Finset.sum_apply, Algebra.smul_def] using this
  · have := congrFun (hw a) l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply] at this
    rw [this]
    simp [eq_comm]

end GlobalTheory
end

section

namespace GlobalTheory.FinProjComplete

theorem mem_smul_top_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R) (x : ι → R) :
    x ∈ (J • ⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := fun _ : ι => R) i) h
    rw [Submodule.map_smul''] at this
    simpa using Submodule.smul_mono le_rfl le_top this
  · have hx : x = ∑ i, x i • Pi.single i (1 : R) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial

theorem isAdicComplete_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R)
    [IsAdicComplete J R] : IsAdicComplete J (ι → R) := by
  have hR : ∀ (x : R) n, x ≡ 0 [SMOD (J ^ n • ⊤ : Submodule R R)] ↔ x ∈ J ^ n := by
    intro x n; simp [SModEq.sub_mem]
  suffices h : IsHausdorff J (ι → R) ∧ IsPrecomplete J (ι → R) from
    have := h.1; have := h.2; {}
  refine ⟨⟨fun x hx => funext fun j => IsHausdorff.haus' (I := J) (x j) fun n => ?_⟩,
    ⟨fun u hu => ?_⟩⟩
  · rw [hR]
    have := SModEq.sub_mem.1 (hx n)
    simpa using (mem_smul_top_pi (J ^ n) _).1 this j
  · have h1 : ∀ i, ∃ L : R, ∀ k, u k i ≡ L [SMOD (J ^ k • ⊤ : Submodule R R)] :=
      fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (mem_smul_top_pi (J ^ a) _).1 (SModEq.sub_mem.1 (hu hab)) i
    choose L hL using h1
    refine ⟨L, fun k => SModEq.sub_mem.2 ((mem_smul_top_pi (J ^ k) _).2 fun i => ?_)⟩
    have := SModEq.sub_mem.1 (hL i k)
    rw [smul_eq_mul, Ideal.mul_top] at this
    simpa using this

theorem map_mem_pow_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) {x y : M} {n : ℕ}
    (h : x ≡ y [SMOD (J ^ n • ⊤ : Submodule R M)]) :
    f x ≡ f y [SMOD (J ^ n • ⊤ : Submodule R N)] := by
  rw [SModEq.sub_mem] at h ⊢
  have := Submodule.mem_map_of_mem (f := f) h
  rw [Submodule.map_smul'', map_sub] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem isAdicComplete_of_retract {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (π : N →ₗ[R] M) (s : M →ₗ[R] N)
    (hs : ∀ x, π (s x) = x) [IsAdicComplete J N] : IsAdicComplete J M := by
  suffices h : IsHausdorff J M ∧ IsPrecomplete J M from
    have := h.1; have := h.2; {}
  refine ⟨⟨fun x hx => ?_⟩, ⟨fun u hu => ?_⟩⟩
  · have : s x = 0 := IsHausdorff.haus' (I := J) (s x) fun n => by
      simpa using map_mem_pow_smul_top J s (hx n)
    rw [← hs x, this, map_zero]
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => s (u k))
      fun hab => map_mem_pow_smul_top J s (hu hab)
    exact ⟨π L, fun n => by simpa [hs] using map_mem_pow_smul_top J π (hL n)⟩

theorem isAdicComplete_span_natCast_of_finite_projective (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O] : IsAdicComplete (Ideal.span {(p : A)}) A := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' O A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have : IsAdicComplete (Ideal.span {(p : O)}) (Fin r → O) := isAdicComplete_pi _
  have hO : IsAdicComplete (Ideal.span {(p : O)}) A :=
    isAdicComplete_of_retract _ π s fun x => by simpa using LinearMap.congr_fun hs x
  have hmap : (Ideal.span {(p : O)}).map (algebraMap O A) = Ideal.span {(p : A)} := by
    simp [Ideal.map_span]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).2 hO

end GlobalTheory.FinProjComplete
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem flat_quot_smul_top_of_surj_flat :
    ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B]
      (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ →
      Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ →
      RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat →
      Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := by
  intro P R₁ B B₁ _ _ _ _ _ f₁ a₁ c₁ hf hc hcomp hker ha
  set K := RingHom.ker f₁ with hK
  let σ : P ⧸ K ≃+* R₁ := RingHom.quotientKerEquivOfSurjective hf
  have hσ : ((a₁.comp (σ : P ⧸ K →+* R₁))).Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective σ.bijective) ha
  letI : Algebra (P ⧸ K) B₁ := (a₁.comp (σ : P ⧸ K →+* R₁)).toAlgebra
  haveI : Module.Flat (P ⧸ K) B₁ := hσ
  letI : Algebra P B₁ := (c₁.comp (algebraMap P B)).toAlgebra
  let g : B →ₗ[P] B₁ :=
    { toFun := c₁
      map_add' := c₁.map_add
      map_smul' := fun p b => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        rfl }
  have hg : ∀ b, g b = c₁ b := fun _ => rfl
  have hkerg : LinearMap.ker g = (K • ⊤ : Submodule P B) := by
    ext b
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hker, LinearMap.mem_ker,
      RingHom.mem_ker, hg]
  have hle : (K • ⊤ : Submodule P B) ≤ LinearMap.ker g := hkerg.ge
  let e₀ := (K • ⊤ : Submodule P B).liftQ g hle
  have he₀ : Function.Bijective e₀ := by
    constructor
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ hkerg.le
    · rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
      exact hc
  let e : (B ⧸ (K • ⊤ : Submodule P B)) ≃ₗ[P ⧸ K] B₁ :=
    LinearEquiv.ofBijective
      { toFun := e₀
        map_add' := e₀.map_add
        map_smul' := fun q x => by
          obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
          have h1 : (Ideal.Quotient.mk K p) • x = p • x := by
            rw [← IsScalarTower.algebraMap_smul (P ⧸ K) p x]
            rfl
          rw [h1, e₀.map_smul, RingHom.id_apply]
          change (c₁.comp (algebraMap P B)) p * e₀ x = a₁ (σ (Ideal.Quotient.mk K p)) * e₀ x
          rw [RingHom.quotientKerEquivOfSurjective_apply_mk, hcomp]
          rfl }
      he₀
  exact Module.Flat.of_linearEquiv e

end GlobalTheory
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.NormSheaf

def normForm (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ} (x : Fin m → L) :
    MvPolynomial (Fin m) K :=
  (∑ i, (X i : MvPolynomial (Fin m) K) •
    (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* MvPolynomial (Fin m) K)).det

def normIdeal (A K L B : Type) [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L] [FiniteDimensional K L]
    [CommRing B] [Algebra B L] (J : Ideal B) : Ideal A :=
  Ideal.span {a | ∃ (m : ℕ) (g : Fin m → B), (∀ i, g i ∈ J) ∧
    ∃ s, algebraMap A K a = (normForm K L (fun i => algebraMap B L (g i))).coeff s}

end GlobalTheory.NormSheaf
end
end
