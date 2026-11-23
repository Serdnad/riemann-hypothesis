module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.DecompOfNormalStatement
public import Formalism.SatakeDualWeyl.Statement
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle002
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory

namespace GlobalTheory
namespace ShufflePositions

variable {A : Type} [DecidableEq A]

theorem count_cons_map (a b : A) (x : List A) (s : Multiset (List A)) :
    (s.map (List.cons b)).count (a :: x) = if a = b then s.count x else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    exact Multiset.count_map_eq_count' (List.cons a) s List.cons_injective x
  · rw [if_neg hab, Multiset.count_eq_zero]
    intro hmem
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hmem
    exact hab (List.cons.inj hy).1.symm

omit [DecidableEq A] in
theorem pos_cons {n : ℕ} (w : Fin (n + 1) → A) (p : Fin (n + 1) → Bool) :
    ((List.finRange (n + 1)).filter p).map w =
      (if p 0 then [w 0] else []) ++
        ((List.finRange n).filter fun j => p j.succ).map (fun j => w j.succ) := by
  rw [List.finRange_succ, List.filter_cons, List.filter_map]
  cases h0 : p 0
  · simp [List.map_map, Function.comp_def]
  · simp [List.map_map, Function.comp_def]

private theorem sum_filter_sub_sum_filter_and_not_eq_sum {M : Type} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → Bool) → M) :
    ∑ ε, f ε = ∑ ε : Fin n → Bool, (f (Fin.cons true ε) + f (Fin.cons false ε)) := by
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  rfl

private theorem count_cons_singleton_cons (c a : A) (x u : List A) :
    ({a :: u} : Multiset (List A)).count (c :: x) =
      if c = a then ({u} : Multiset (List A)).count x else 0 := by
  rw [← Multiset.map_singleton (List.cons a) u]
  exact count_cons_map c a x {u}

private theorem count_cons_singleton_nil (c : A) (x : List A) :
    ({[]} : Multiset (List A)).count (c :: x) = 0 := by
  simp

theorem count_single (n : ℕ) : ∀ (w : Fin n → A) (u v : List A),
    (Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool,
        ({u} : Multiset (List A)).count (((List.finRange n).filter fun j => !ε j).map w) *
        ({v} : Multiset (List A)).count (((List.finRange n).filter ε).map w) := by
  induction n with
  | zero =>
    intro w u v
    simp only [List.ofFn_zero, List.finRange_zero, List.filter_nil, List.map_nil,
      Finset.univ_unique, Finset.sum_singleton]
    rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
    · simp
    · simp
    · simp [Shuffle.shuffle_nil_right]
    · rw [Shuffle.shuffle_cons_cons]
      simp [Multiset.mem_map]
  | succ n ih =>
    intro w u v
    rw [sum_filter_sub_sum_filter_and_not_eq_sum, List.ofFn_succ]
    simp only [pos_cons, Fin.cons_zero, Fin.cons_succ, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, if_true, if_false, List.nil_append, List.singleton_append]
    set w' : Fin n → A := fun j => w j.succ with hw'
    rcases u with _ | ⟨a, u⟩ <;> rcases v with _ | ⟨b, v⟩
    · simp
    · have h := ih w' [] v
      rw [Shuffle.shuffle_nil_left] at h
      rw [Shuffle.shuffle_nil_left, count_cons_singleton_cons]
      simp only [count_cons_singleton_cons, count_cons_singleton_nil, zero_mul, add_zero]
      by_cases hc : w 0 = b
      · simp only [if_pos hc, h]
      · simp [if_neg hc]
    · have h := ih w' u []
      rw [Shuffle.shuffle_nil_right] at h
      rw [Shuffle.shuffle_nil_right, count_cons_singleton_cons]
      simp only [count_cons_singleton_cons, count_cons_singleton_nil, mul_zero, zero_add]
      by_cases hc : w 0 = a
      · simp only [if_pos hc, h]
      · simp [if_neg hc]
    · have h1 := ih w' u (b :: v)
      have h2 := ih w' (a :: u) v
      rw [Shuffle.shuffle_cons_cons, Multiset.count_add, count_cons_map, count_cons_map]
      simp only [count_cons_singleton_cons, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      · by_cases hc : w 0 = b
        · simp only [if_pos hc, h2]
        · simp [if_neg hc]
      · by_cases hc : w 0 = a
        · simp only [if_pos hc, h1]
        · simp [if_neg hc]

private theorem sum_map_count_singleton (X : List A) (s : Multiset (List A)) :
    (s.map fun v => ({v} : Multiset (List A)).count X).sum = s.count X := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons, Multiset.count_singleton,
      add_comm]

theorem count_bind_shuffle (A : Type) [DecidableEq A] (n : ℕ) (w : Fin n → A)
    (s₁ s₂ : Multiset (List A)) :
    (s₁.bind fun u => s₂.bind fun v => Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool, s₁.count (((List.finRange n).filter fun j => !ε j).map w) *
        s₂.count (((List.finRange n).filter ε).map w) := by
  simp only [Multiset.count_bind, count_single n w, Multiset.sum_map_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [Multiset.sum_map_mul_left, Multiset.sum_map_mul_right, sum_map_count_singleton]

end ShufflePositions
end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory.DenominatorExistenceTwistedOperators

theorem abs_eq_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ∉ v.asIdeal) : FinitePlace.mk v (x : K) = 1 := by
  rw [FinitePlace.mk_apply]
  have h1 := FinitePlace.norm_le_one K v x
  have h2 := (FinitePlace.norm_lt_one_iff_mem K v x).not.mpr hx
  exact le_antisymm h1 (not_lt.mp h2)

theorem exists_prime_to_part {R : Type} [CommRing R] [IsDedekindDomain R] (p : HeightOneSpectrum R) (d : R)
    (hd : d ≠ 0) : ∃ s ∉ p.asIdeal, ∀ q : HeightOneSpectrum R, q ≠ p → ∃ t ∉ q.asIdeal, ∃ u, t * s = u * d := by
  have hI : Ideal.span {d} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hd
  obtain ⟨n, J, hJ, hfac⟩ := WfDvdMonoid.max_power_factor hI p.irreducible
  rw [Ideal.dvd_iff_le] at hJ
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJ
  refine ⟨s, hsp, fun q hq => ?_⟩
  have hnle : ¬ p.asIdeal ^ n ≤ q.asIdeal := by
    intro h
    have := q.isPrime
    have h1 : p.asIdeal ≤ q.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨t, htq, ?_⟩
  have : t * s ∈ Ideal.span {d} := by
    rw [hfac]; exact Ideal.mul_mem_mul ht hsJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp this
  exact ⟨u, hu.symm⟩

theorem exists_denominator {R K M : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower R K M] (N : Submodule R M) (x : M)
    (hx : x ∈ Submodule.span K (N : Set M)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hx
    · rw [mul_smul]; exact N.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hw0 : w ≠ 0 := nonZeroDivisors.ne_zero hw
    have hwK : algebraMap R K w ≠ 0 := by simpa using hw0
    refine ⟨a * w, mul_ne_zero ha hw0, ?_⟩
    have : (a * w) • (algebraMap R K u / algebraMap R K w) • x = u • a • x := by
      rw [← algebraMap_smul K (a * w), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [this]
    exact N.smul_mem _ hx

theorem exists_smul_mem_supLattice (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type)
    [(σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [(σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [Group G]
    (Φ : FormsL LL Ks WL W G) (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK)
    (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK) (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s ∉ la.asIdeal, s • (f : WL) ∈ Φ.MK := by
  obtain ⟨d, hd, hdf⟩ := exists_denominator (K := Ks) Φ.MK (f : WL) (by rw [hspan]; exact f.2)
  obtain ⟨s, hs, hq⟩ := exists_prime_to_part la d hd
  refine ⟨s, hs, ?_⟩
  have hsm : ∀ (a : 𝓞 Ks) (g : WL), a • g = (a : Ks) • g := fun a g => (algebraMap_smul Ks a g).symm
  have hm : s • (f : WL) ∈ Φ.WK := by rw [hsm]; exact Φ.WK.smul_mem _ f.2
  refine ⟨hm, fun q y => ?_⟩
  by_cases h : q = la
  · subst h
    have h1 : (⟨s • (f : WL), hm⟩ : Φ.WK) = (s : Ks) • f := Subtype.ext (hsm s f)
    rw [h1, Φ.nrm_smul, abs_eq_one q s hs, one_mul]
    exact hf y
  · obtain ⟨t, ht, u, htu⟩ := hq q h
    have hmem : t • s • (f : WL) ∈ Φ.MK := by
      rw [smul_smul, htu, mul_smul]; exact Φ.MK.smul_mem _ hdf
    obtain ⟨hw, hb⟩ := hmem
    have h1 : (⟨t • s • (f : WL), hw⟩ : Φ.WK) = (t : Ks) • ⟨s • (f : WL), hm⟩ := Subtype.ext (hsm t _)
    have h2 := hb q y
    rwa [h1, Φ.nrm_smul, abs_eq_one q t ht, one_mul] at h2

end GlobalTheory.DenominatorExistenceTwistedOperators
end

section

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.OntoLinAlg

open Formalism.IndefR.U2

variable {I A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]

theorem op_mem_ker {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (i : I) {k : A} (hk : k ∈ LinearMap.ker θ) : op i k ∈ LinearMap.ker θ := by
  rw [LinearMap.mem_ker] at hk ⊢
  rw [hI, hk, map_zero]

theorem op_mem_orth {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (hA : AdjClosed op) (i : I) {v : A} (hv : v ∈ (LinearMap.ker θ)ᗮ) :
    op i v ∈ (LinearMap.ker θ)ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  obtain ⟨i', hi'⟩ := hA i
  rw [← LinearMap.adjoint_inner_left, ← hi']
  exact hv _ (op_mem_ker hI i' hu)

theorem eq_zero_of_mem_both {K : Submodule ℂ A} {z : A} (h1 : z ∈ K) (h2 : z ∈ Kᗮ) : z = 0 := by
  have := (Submodule.mem_orthogonal _ _).mp h2 z h1
  exact inner_self_eq_zero.mp this

theorem ontoParts_of {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    {good : Submodule ℂ A} {goodB : Submodule ℂ B} (Ix : Set (I → ℂ))
    (hI : Intw θ op opB) (hA : AdjClosed op) (hOnto : goodB ≤ LinearMap.range θ)
    (hPr : ∀ y ∈ good, ((LinearMap.ker θ).starProjection y : A) ∈ good)
    (hInj : ∀ (c : I → ℂ) (x y : A), x ∈ eigPart op c → θ x ≠ 0 → y ∈ eigPart op c ⊓ good → θ y = 0 → y = 0) :
    OntoParts (LinearMap.adjoint θ) op opB good goodB Ix := by
  intro c hc y hy
  set K := LinearMap.ker θ with hK
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.2
  obtain ⟨x0, hx0⟩ := hOnto hw.2
  set x := x0 - K.starProjection x0 with hxdef
  have hxo : x ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x0
  have hθx : θ x = w := by
    have : θ (K.starProjection x0) = 0 := LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem K x0)
    rw [hxdef, map_sub, this, sub_zero, hx0]
  have hxe : x ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hz1 : op i x - c i • x ∈ Kᗮ := Submodule.sub_mem _ (op_mem_orth hI hA i hxo) (Submodule.smul_mem _ _ hxo)
    have hz2 : op i x - c i • x ∈ K := by
      rw [hK, LinearMap.mem_ker, map_sub, map_smul, hI, hθx, (mem_eigPart.mp hw.1) i, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz2 hz1)
  set y1 := K.starProjection y with hy1
  have hy1K : y1 ∈ K := Submodule.starProjection_apply_mem K y
  have hy2 : y - y1 ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal y
  have hy1e : y1 ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hyi := (mem_eigPart.mp hy.1) i
    have e : op i y1 - c i • y1 = -(op i (y - y1) - c i • (y - y1)) := by
      rw [map_sub, smul_sub, hyi]; abel
    have hz1 : op i y1 - c i • y1 ∈ K := Submodule.sub_mem _ (op_mem_ker hI i hy1K) (Submodule.smul_mem _ _ hy1K)
    have hz2 : op i y1 - c i • y1 ∈ Kᗮ := by
      rw [e]
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (op_mem_orth hI hA i hy2) (Submodule.smul_mem _ _ hy2))
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz1 hz2)
  have hy10 : y1 = 0 := hInj c x y1 hxe (by rw [hθx]; exact hw0) ⟨hy1e, hPr y hy.2⟩ (LinearMap.mem_ker.mp hy1K)
  rw [← LinearMap.orthogonal_ker]
  have : y = y - y1 := by rw [hy10, sub_zero]
  rw [this]
  exact hy2

end GlobalTheory.OntoLinAlg
end
end

section

namespace GlobalTheory.SylvesterInertia

open Matrix Module
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

def qf (J : Matrix n n ℂ) (x : n → ℂ) : ℂ := star x ⬝ᵥ J *ᵥ x

def inlMap (a b : ℕ) : (Fin a → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim z 0
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp

def inrMap (a b : ℕ) : (Fin b → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim 0 z
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp

lemma inlMap_injective (a b : ℕ) : Function.Injective (inlMap a b) := by
  intro z z' h; funext i; exact congrFun h (Sum.inl i)

lemma inrMap_injective (a b : ℕ) : Function.Injective (inrMap a b) := by
  intro z z' h; funext i; exact congrFun h (Sum.inr i)

def chg {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) :
    (Fin a ⊕ Fin b → ℂ) →ₗ[ℂ] (n → ℂ) :=
  LinearMap.funLeft ℂ ℂ e ∘ₗ (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ).mulVecLin

lemma chg_apply {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) (y : Fin a ⊕ Fin b → ℂ) :
    chg e P y = ((P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y) ∘ e := rfl

lemma chg_injective {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) :
    Function.Injective (chg e P) := by
  intro y y' h
  have h1 : (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y = (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y' := by
    have := congrArg (fun v => v ∘ e.symm) h
    simpa [chg_apply, Function.comp_def] using this
  have h2 := congrArg (fun v => ((P⁻¹ : GL (Fin a ⊕ Fin b) ℂ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ v) h1
  simpa [mulVec_mulVec] using h2

lemma qf_chg {a b : ℕ} (J : Matrix n n ℂ) (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ)
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b) (y : Fin a ⊕ Fin b → ℂ) :
    qf J (chg e P y) = star y ⬝ᵥ Formalism.UG.Jpq a b *ᵥ y := by
  set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ := (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ)
  have hc : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by ext i j; rfl
  rw [← h, hc]
  set w := M *ᵥ y
  have h1 : J *ᵥ (w ∘ e) = (J.reindex e e *ᵥ w) ∘ e := by
    rw [reindex_apply, submatrix_mulVec_equiv]
    ext i; simp [Function.comp_def]
  have h2 : qf J (chg e P y) = star w ⬝ᵥ (J.reindex e e *ᵥ w) := by
    rw [qf, chg_apply, h1]
    simp only [dotProduct, Function.comp_apply, Pi.star_apply]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [h2]
  simp only [w, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, Matrix.mul_assoc]

lemma jpq_inl (a b : ℕ) (z : Fin a → ℂ) :
    star (inlMap a b z) ⬝ᵥ Formalism.UG.Jpq a b *ᵥ inlMap a b z = star z ⬝ᵥ z := by
  simp [inlMap, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def]

lemma jpq_inr (a b : ℕ) (z : Fin b → ℂ) :
    star (inrMap a b z) ⬝ᵥ Formalism.UG.Jpq a b *ᵥ inrMap a b z = -(star z ⬝ᵥ z) := by
  simp [inrMap, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def, neg_mulVec, Finset.sum_neg_distrib]

lemma pos_of_mem {a b : ℕ} {J : Matrix n n ℂ} {e : n ≃ Fin a ⊕ Fin b} {P : GL (Fin a ⊕ Fin b) ℂ}
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b)
    {x : n → ℂ} (hx : x ∈ LinearMap.range (chg e P ∘ₗ inlMap a b)) (hx0 : x ≠ 0) : 0 < qf J x := by
  obtain ⟨z, rfl⟩ := hx
  have hz : z ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
  rw [LinearMap.comp_apply, qf_chg J e P h, jpq_inl]
  exact dotProduct_star_self_pos_iff.mpr hz

lemma nonpos_of_mem {a b : ℕ} {J : Matrix n n ℂ} {e : n ≃ Fin a ⊕ Fin b} {P : GL (Fin a ⊕ Fin b) ℂ}
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b)
    {x : n → ℂ} (hx : x ∈ LinearMap.range (chg e P ∘ₗ inrMap a b)) : qf J x ≤ 0 := by
  obtain ⟨z, rfl⟩ := hx
  rw [LinearMap.comp_apply, qf_chg J e P h, jpq_inr]
  exact neg_nonpos.mpr (dotProduct_star_self_nonneg z)

theorem fst_le_of_hasSignature {J : Matrix n n ℂ} {a b a' b' : ℕ}
    (h : Formalism.UG.HasSignature J a b) (h' : Formalism.UG.HasSignature J a' b') : a ≤ a' := by
  obtain ⟨e, P, hP⟩ := h
  obtain ⟨e', P', hP'⟩ := h'
  by_contra hlt
  push_neg at hlt
  set U := LinearMap.range (chg e P ∘ₗ inlMap a b)
  set N := LinearMap.range (chg e' P' ∘ₗ inrMap a' b')
  have hU : finrank ℂ U = a := by
    rw [LinearMap.finrank_range_of_inj (by rw [LinearMap.coe_comp]; exact (chg_injective e P).comp (inlMap_injective a b))]
    simp
  have hN : finrank ℂ N = b' := by
    rw [LinearMap.finrank_range_of_inj (by rw [LinearMap.coe_comp]; exact (chg_injective e' P').comp (inrMap_injective a' b'))]
    simp
  have hcard : Fintype.card n = a' + b' := by simpa using Fintype.card_congr e'
  have hsup : finrank ℂ ↥(U ⊔ N) ≤ Fintype.card n := by
    have := Submodule.finrank_le (U ⊔ N)
    simpa using this
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U N
  have hinf : U ⊓ N ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hsum
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  have h1 := pos_of_mem hP (Submodule.mem_inf.1 hx).1 hx0
  have h2 := nonpos_of_mem hP' (Submodule.mem_inf.1 hx).2
  exact lt_irrefl _ (lt_of_lt_of_le h1 h2)

theorem hasSignature_fst_unique : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ},
    Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' :=
  fun h h' => le_antisymm (fst_le_of_hasSignature h h') (fst_le_of_hasSignature h' h)

end GlobalTheory.SylvesterInertia
end

section


theorem _root_.GlobalTheory.T.exists_sum_intertwined_of_mem_invariant_submodule : ∀ {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type} (a : ι → Module.End ℂ P),
    (∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) →
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, ∃ (n : ℕ) (Sm : Fin n → (P →ₗ[ℂ] (Fin m → P))) (q : Fin n → P),
      (∀ l i p, Sm l (a i p) = fun j => a i (Sm l p j)) ∧ (∀ l p, Sm l p ∈ N) ∧ y = ∑ l, Sm l (q l) := by
  first | exact @GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | exact GlobalTheory.submodule_pow_simple_eq_sum_equiv_values | (intros; apply GlobalTheory.submodule_pow_simple_eq_sum_equiv_values <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mem_iSup_irreducible_of_fixed_projector : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by
  first | exact @GlobalTheory.abstract_complete_reducibility | exact GlobalTheory.abstract_complete_reducibility | (intros; apply GlobalTheory.abstract_complete_reducibility <;> assumption)
end
