module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Noetherian.Defs
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
public import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem GlobalTheory.tensorSum_bijective_iff (A B R S : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] [CommRing S] (κ : R ⊗[A] B →+* S) {r : ℕ} (v : Fin r → B) :
    Function.Bijective (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) ↔ (Function.Surjective κ ∧ LinearIndependent R (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) = ⊤) := by
  have hsum : ∀ c : Fin r → R, ∑ k, c k • Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)
      = Ideal.Quotient.mk (RingHom.ker κ) (∑ k, c k ⊗ₜ[A] v k) := by
    intro c

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : c k • ((1 : R) ⊗ₜ[A] v k) = c k ⊗ₜ[A] v k := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [← h1]
    exact (map_smul (Ideal.Quotient.mkₐ R (RingHom.ker κ)) (c k) ((1 : R) ⊗ₜ[A] v k)).symm
  have hker : ∀ x y : R ⊗[A] B, Ideal.Quotient.mk (RingHom.ker κ) x = Ideal.Quotient.mk (RingHom.ker κ) y ↔ κ x = κ y := by
    intro x y
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
  have hsub : ∀ c c' : Fin r → R, ∑ k, (c - c') k ⊗ₜ[A] v k = ∑ k, c k ⊗ₜ[A] v k - ∑ k, c' k ⊗ₜ[A] v k := by
    intro c c'
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.sub_apply, TensorProduct.sub_tmul]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun s => ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hsurj s
      exact ⟨_, hc⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm,
        hker] at hg
      have h0 : (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) g = (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) 0 := by
        simp only [Pi.zero_apply, TensorProduct.zero_tmul, Finset.sum_const_zero, map_zero]
        simpa using hg
      intro i
      rw [hinj h0]
      rfl
    · rw [eq_top_iff]
      intro x _
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc⟩ := hsurj (κ t)
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, by rw [hsum, hker]; exact hc⟩
  · rintro ⟨hsurj, hli, hspan⟩
    refine ⟨fun c c' h => ?_, fun s => ?_⟩
    · rw [Fintype.linearIndependent_iff] at hli
      have h2 := hli (c - c') (by
        rw [hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm,
          hker, hsub, map_sub, map_zero, sub_eq_zero]
        exact h)
      funext i
      exact sub_eq_zero.mp (h2 i)
    · obtain ⟨t, rfl⟩ := hsurj s
      have hm : Ideal.Quotient.mk (RingHom.ker κ) t ∈ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) := by
        rw [hspan]; trivial
      rw [Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨c, hc⟩ := hm
      rw [hsum, hker] at hc
      exact ⟨c, hc⟩
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory

theorem quotient_basis_baseChange (A B C R : Type) [CommRing A] [CommRing B] [Algebra A B]
    [CommRing C] [Algebra A C] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B)
    (J : Ideal (C ⊗[A] B)) (ψ : C →ₐ[A] R)
    (hli : LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)))
    (hsp : Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤) :
    LinearIndependent R (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k)) ∧
    Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k))) = ⊤ := by
  set f := Algebra.TensorProduct.map ψ (AlgHom.id A B) with hf
  set J' := J.map f with hJ'
  let bas : Module.Basis (Fin r) C ((C ⊗[A] B) ⧸ J) := Module.Basis.mk hli hsp.ge
  have bas_apply : ∀ k, bas k = Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k) := fun k => Module.Basis.mk_apply _ _ _
  let Φ : (C ⊗[A] B) → (Fin r → R) := fun x k => ψ (bas.repr (Ideal.Quotient.mk J x) k)
  have mkC : ∀ (c : C) (x : C ⊗[A] B), Ideal.Quotient.mk J (c • x) = c • Ideal.Quotient.mk J x :=
    fun c x => map_smul (Ideal.Quotient.mkₐ C J) c x
  have Φ_add : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y; funext k; simp [Φ, map_add (f := _)]
  have Φ_zero : Φ 0 = 0 := by funext k; simp [Φ]
  have Φ_smul : ∀ (c : C) x, Φ (c • x) = ψ c • Φ x := by
    intro c x; funext k
    simp [Φ, mkC]
  have Φ_J : ∀ x ∈ J, Φ x = 0 := by
    intro x hx; funext k; simp [Φ, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have Φ_v : ∀ k, Φ ((1 : C) ⊗ₜ[A] v k) = Pi.single k 1 := by
    intro k; funext j
    simp only [Φ, ← bas_apply, Module.Basis.repr_self]
    by_cases h : j = k
    · subst h; simp
    · simp [Finsupp.single_apply, Pi.single_apply, Ne.symm h, h]
  let g : B →ₗ[A] (Fin r → R) :=
    { toFun := fun b => Φ ((1 : C) ⊗ₜ[A] b)
      map_add' := fun x y => by simp only [TensorProduct.tmul_add]; exact Φ_add _ _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply]
        rw [TensorProduct.tmul_smul, ← algebraMap_smul C a ((1 : C) ⊗ₜ[A] x), Φ_smul,
          AlgHom.commutes, algebraMap_smul] }
  let ℓ : R ⊗[A] B →ₗ[R] (Fin r → R) := LinearMap.liftBaseChange R g
  have ℓ_tmul : ∀ (s : R) (b : B), ℓ (s ⊗ₜ[A] b) = s • Φ ((1 : C) ⊗ₜ[A] b) := by
    intro s b; simp [ℓ, g]
  have key : ∀ x : C ⊗[A] B, ℓ (f x) = Φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [Φ_zero]
    | tmul c b =>
      rw [hf, Algebra.TensorProduct.map_tmul, ℓ_tmul]
      have : c ⊗ₜ[A] b = c • ((1 : C) ⊗ₜ[A] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, Φ_smul]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, Φ_add]
  have f_smul : ∀ (c : C) (y : C ⊗[A] B), f (c • y) = ψ c • f y := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c' b =>
      rw [TensorProduct.smul_tmul', hf, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  have f_one : ∀ b : B, f ((1 : C) ⊗ₜ[A] b) = (1 : R) ⊗ₜ[A] b := by
    intro b; rw [hf, Algebra.TensorProduct.map_tmul, map_one]; rfl
  have kill : ∀ y ∈ J', ℓ y = 0 := by
    let K : Ideal (R ⊗[A] B) :=
      { carrier := {y | ∀ a, ℓ (a * y) = 0}
        add_mem' := fun {x y} hx hy a => by rw [mul_add, map_add (f := _), hx a, hy a, add_zero]
        zero_mem' := fun a => by simp
        smul_mem' := fun c {x} hx a => by
          show ℓ (a * (c * x)) = 0
          rw [← mul_assoc]; exact hx _ }
    have hJK : J' ≤ K := by
      rw [hJ', Ideal.map_le_iff_le_comap]
      intro j hj a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul s b =>
        have : (s ⊗ₜ[A] b) * f j = s • f (((1 : C) ⊗ₜ[A] b) * j) := by
          rw [map_mul, f_one, ← smul_mul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, key, Φ_J _ (J.mul_mem_left _ hj), smul_zero]
      | add x y hx hy => rw [add_mul, map_add (f := _), hx, hy, add_zero]
    intro y hy
    have := hJK hy 1
    simpa using this
  have mkR : ∀ (s : R) (x : R ⊗[A] B), Ideal.Quotient.mk J' (s • x) = s • Ideal.Quotient.mk J' x :=
    fun s x => map_smul (Ideal.Quotient.mkₐ R J') s x
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have hmem : (∑ k, c k • ((1 : R) ⊗ₜ[A] v k)) ∈ J' := by

      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa [mkR] using hc
    have h0 := kill _ hmem

    rw [map_sum] at h0
    simp only [map_smul, ℓ_tmul, one_smul, Φ_v] at h0
    intro i
    have := congrFun h0 i
    simpa [Finset.sum_apply, Pi.single_apply] using this
  · rw [eq_top_iff]
    rintro z -
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hbase : ∀ x : C ⊗[A] B, Ideal.Quotient.mk J' (f x) ∈
        Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J' ((1 : R) ⊗ₜ[A] v k))) := by
      intro x
      have hx := bas.sum_repr (Ideal.Quotient.mk J x)
      set c := bas.repr (Ideal.Quotient.mk J x)
      have hmem : x - ∑ k, c k • ((1 : C) ⊗ₜ[A] v k) ∈ J := by

        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
        simp only [mkC, ← bas_apply]
        rw [hx, sub_self]
      have hmem' : f x - ∑ k, ψ (c k) • ((1 : R) ⊗ₜ[A] v k) ∈ J' := by
        have := Ideal.mem_map_of_mem f hmem

        rw [map_sub, map_sum] at this
        simpa only [f_smul, f_one] using this

      rw [← sub_add_cancel (f x) (∑ k, ψ (c k) • ((1 : R) ⊗ₜ[A] v k)), map_add (f := _),
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem', zero_add, map_sum]
      refine Submodule.sum_mem _ (fun k _ => ?_)
      rw [mkR]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      have : s ⊗ₜ[A] b = s • f ((1 : C) ⊗ₜ[A] b) := by
        rw [f_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, mkR]
      exact Submodule.smul_mem _ _ (hbase _)
    | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

end GlobalTheory
end

section

namespace GlobalTheory

theorem finite_alg_hom_ker_coker_killed_of_onto_mod_ideal
    (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M]
    [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N]
    (φ : M →ₐ[A] N) :
    (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) →
    (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) →
    ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧
      ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by
  intro h1 h2

  set R : Submodule A N := LinearMap.range φ.toLinearMap with hR
  have hQ : (⊤ : Submodule A (N ⧸ R)) ≤ J • ⊤ := by
    rintro q -
    obtain ⟨y, rfl⟩ := R.mkQ_surjective q
    obtain ⟨t, ht⟩ := h1 y
    have hz : y - φ t ∈ J • (⊤ : Submodule A N) := by
      rw [Ideal.smul_top_eq_map]; exact ht
    have hm : R.mkQ (y - φ t) ∈ J • (⊤ : Submodule A (N ⧸ R)) := by
      have := Submodule.mem_map_of_mem (f := R.mkQ) hz
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
      exact this
    have he : R.mkQ (y - φ t) = R.mkQ y := by
      rw [map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨t, rfl⟩
    rwa [he] at hm
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J
    (⊤ : Submodule A (N ⧸ R)) (Module.Finite.fg_top) hQ
  have hrR : ∀ y : N, r • y ∈ R := by
    intro y
    have := hr (R.mkQ y) trivial
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

  set K : Submodule A M := LinearMap.ker φ.toLinearMap with hK
  have hKfg : K.FG := IsNoetherian.noetherian K
  have hKle : K ≤ J • K := by
    intro t ht
    have hφ : φ t = 0 := ht
    have hmem : t ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule A M) := by
      rw [Submodule.mem_iInf]
      intro i
      rw [Ideal.smul_top_eq_map]
      exact h2 i t (by rw [hφ]; exact Ideal.zero_mem _)
    obtain ⟨⟨s, hs⟩, hst⟩ := (J.mem_iInf_smul_pow_eq_bot_iff t).1 hmem
    simp only at hst
    rw [← hst]
    exact Submodule.smul_mem_smul hs ht
  obtain ⟨u, hu1, hu⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J K hKfg hKle
  refine ⟨r * u, ?_, ?_, ?_⟩
  · have : r * u - 1 = r * (u - 1) + (r - 1) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left r hu1) hr1
  · intro y
    rw [← Algebra.smul_def, mul_comm, mul_smul]
    obtain ⟨t, ht⟩ := hrR y
    exact ⟨u • t, by
      change φ (u • t) = u • (r • y)
      rw [map_smul]
      congr 1⟩
  · intro t ht
    rw [← Algebra.smul_def, mul_smul, hu t ht, smul_zero]

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem fibre_going_down_tensor : ∀ (S A C : Type) [CommRing S] [CommRing A] [CommRing C] [Algebra S A] [Algebra S C]
    (u : Ideal (TensorProduct S A C)) [u.IsPrime] (Q₁ : Ideal C) [Q₁.IsPrime],
    Q₁ ≤ u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) →
    Q₁.comap (algebraMap S C) = u.comap (algebraMap S (TensorProduct S A C)) →
    ∃ Q : Ideal (TensorProduct S A C), Q.IsPrime ∧ Q ≤ u ∧
      Q.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] TensorProduct S A C) = Q₁ ∧
      Q.comap (algebraMap A (TensorProduct S A C)) = u.comap (algebraMap A (TensorProduct S A C)) := by
  intro S A C _ _ _ _ _ u _ Q₁ _ hle h2
  let p := u.comap (algebraMap A (A ⊗[S] C))
  let p₁ := u.comap (algebraMap S (A ⊗[S] C))
  have hp : p₁ = p.comap (algebraMap S A) := by
    simp only [p, p₁, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  let K₁ := p₁.ResidueField
  let K := p.ResidueField
  letI : Algebra K₁ K := (Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).toAlgebra
  haveI : IsScalarTower S K₁ K := IsScalarTower.of_algebraMap_eq
    (fun s => ((Ideal.ResidueField.mapₐ p₁ p (Algebra.ofId S A) hp).commutes s).symm)
  let F₁ := p₁.Fiber C
  let E := F₁ ⊗[K₁] K
  let e1 : p.Fiber (A ⊗[S] C) ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S A K K C
  let e2 : K ⊗[K₁] F₁ ≃ₐ[K] K ⊗[S] C := Algebra.TensorProduct.cancelBaseChange S K₁ K K C
  let e3 : K ⊗[K₁] F₁ ≃ₐ[K₁] E := Algebra.TensorProduct.comm K₁ K F₁
  haveI : Module.Flat F₁ E := inferInstance
  haveI : Algebra.HasGoingDown F₁ E := inferInstance
  let Φ : p.Fiber (A ⊗[S] C) ≃+* E :=
    (e1.toRingEquiv.trans e2.symm.toRingEquiv).trans e3.toRingEquiv
  have hΦ : ∀ c : C, Φ (Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeRight c : A ⊗[S] C))
      = algebraMap F₁ E (Algebra.TensorProduct.includeRight c) := by
    intro c
    simp only [Φ, e1, e2, e3, Algebra.TensorProduct.includeRight_apply, RingEquiv.trans_apply,
      AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    erw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    rfl

  haveI : u.LiesOver p := ⟨rfl⟩
  let isoA := PrimeSpectrum.primesOverOrderIsoFiber A (A ⊗[S] C) p
  let ub := isoA ⟨u, inferInstance, inferInstance⟩
  have hub : ub.asIdeal.comap (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) = u := by
    have := congrArg Subtype.val (isoA.symm_apply_apply ⟨u, inferInstance, inferInstance⟩)
    exact this
  have hmem : ∀ y : A ⊗[S] C, (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)) y
      ∈ ub.asIdeal ↔ y ∈ u := fun y => Iff.of_eq (congrArg (y ∈ ·) hub)

  haveI : Q₁.LiesOver p₁ := ⟨h2.symm⟩
  let iso₁ := PrimeSpectrum.primesOverOrderIsoFiber S C p₁
  let Qb := iso₁ ⟨Q₁, inferInstance, inferInstance⟩
  have hQb : Qb.asIdeal.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) = Q₁ := by
    have := congrArg Subtype.val (iso₁.symm_apply_apply ⟨Q₁, inferInstance, inferInstance⟩)
    exact this

  let ue : Ideal E := ub.asIdeal.comap (Φ.symm : E →+* p.Fiber (A ⊗[S] C))
  haveI : ue.IsPrime := Ideal.comap_isPrime _ _
  let w : Ideal F₁ := ue.comap (algebraMap F₁ E)
  haveI : w.IsPrime := Ideal.comap_isPrime _ _
  haveI : ue.LiesOver w := ⟨rfl⟩
  have hw : w.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] F₁) =
      u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C) := by
    ext c
    change Φ.symm (algebraMap F₁ E (Algebra.TensorProduct.includeRight c)) ∈ ub.asIdeal ↔ _
    rw [← hΦ, RingEquiv.symm_apply_apply]
    exact hmem _
  have hwle : Qb.asIdeal ≤ w := by
    let u₁ := u.comap (Algebra.TensorProduct.includeRight : C →ₐ[S] A ⊗[S] C)
    haveI : u₁.IsPrime := Ideal.comap_isPrime _ _
    haveI : u₁.LiesOver p₁ := ⟨by
      show p₁ = u₁.comap (algebraMap S C)
      ext s
      simp [u₁, p₁]⟩
    let wP : PrimeSpectrum F₁ := ⟨w, inferInstance⟩
    have hsym : (iso₁.symm wP).1 = u₁ := hw
    have key : iso₁.symm Qb ≤ iso₁.symm wP := by
      show (iso₁.symm Qb).1 ≤ (iso₁.symm wP).1
      rw [hsym, iso₁.symm_apply_apply]
      exact hle
    exact (iso₁.symm.le_iff_le.mp key : Qb ≤ wP)
  obtain ⟨P, hPle, hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Qb.asIdeal) (q := w) ue hwle
  refine ⟨(P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap
    (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C)), inferInstance, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hmem]
    have := hPle hx
    simpa [ue] using this
  · ext c
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
    erw [hΦ c]
    rw [← hQb, Ideal.mem_comap, ← Ideal.mem_comap, ← Ideal.under_def, ← hPover.over]
  · ext a
    let J : Ideal K := (P.comap (Φ : p.Fiber (A ⊗[S] C) →+* E)).comap (algebraMap K (p.Fiber (A ⊗[S] C)))
    haveI : J.IsPrime := Ideal.comap_isPrime _ _
    have hJ : J = ⊥ := Ideal.eq_bot_of_prime J
    have hx : (Algebra.TensorProduct.includeRight : A ⊗[S] C →ₐ[A] p.Fiber (A ⊗[S] C))
        (algebraMap A (A ⊗[S] C) a) = algebraMap K (p.Fiber (A ⊗[S] C)) (algebraMap A K a) := by
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    rw [Ideal.mem_comap, Ideal.mem_comap, hx]
    change algebraMap A K a ∈ J ↔ _
    rw [hJ, Ideal.mem_bot, Ideal.algebraMap_residueField_eq_zero]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_ideal_eq_of_span_of_linearIndependent
    (A B R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] {r : ℕ}
    (v : Fin r → B) (J₁ J₂ : Ideal (R ⊗[A] B)) (h12 : J₁ ≤ J₂)
    (hspan : Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) = ⊤)
    (hli : LinearIndependent R (fun k => Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k))) :
    J₁ = J₂ := by
  refine le_antisymm h12 (fun t ht => ?_)
  have hmem : Ideal.Quotient.mk J₁ t ∈ Submodule.span R
      (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  set s : R ⊗[A] B := ∑ k, c k • ((1 : R) ⊗ₜ[A] v k) with hs
  have hmk : ∀ (J : Ideal (R ⊗[A] B)), Ideal.Quotient.mk J s
      = ∑ k, c k • Ideal.Quotient.mk J ((1 : R) ⊗ₜ[A] v k) := by
    intro J

    rw [hs, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Ideal.Quotient.mkₐ_eq_mk R, map_smul]
  have h1 : t - s ∈ J₁ := by
    rw [← Ideal.Quotient.eq, hmk J₁, hc]
  have h2 : s ∈ J₂ := by
    have := J₂.sub_mem ht (h12 h1)
    simpa using this
  have hsum : ∑ k, c k • Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k) = 0 := by
    rw [← hmk J₂, Ideal.Quotient.eq_zero_iff_mem]; exact h2
  have hc0 : ∀ k, c k = 0 := Fintype.linearIndependent_iff.1 hli c hsum
  have hs0 : s = 0 := by simp [hs, hc0]
  rw [hs0, sub_zero] at h1
  exact h1

end GlobalTheory
end
