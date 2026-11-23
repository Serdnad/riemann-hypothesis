module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

section

private theorem UpperTheory.pow_preserves_submodule {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (n : ℕ) :
    ∀ f ∈ U, (T ^ n) f ∈ U := by
  induction n with
  | zero =>
    intro f hf
    simpa using hf
  | succ n ih =>
    intro f hf
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT f hf)

private theorem UpperTheory.periodic_difference_shift {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) :
    (T ^ (m + q)) f - (T ^ m) f ∈ U := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h' := UpperTheory.pow_preserves_submodule U T hT r _ h
  have e : (T ^ r) ((T ^ (a + q)) f - (T ^ a) f) = (T ^ (a + r + q)) f - (T ^ (a + r)) f := by
    rw [show a + r + q = r + (a + q) by ring, show a + r = r + a by ring,
      pow_add T r (a + q), pow_add T r a, Module.End.mul_apply, Module.End.mul_apply, map_sub]
  rw [e] at h'
  exact h'

private theorem UpperTheory.periodic_difference_mul_period {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) (c : ℕ) :
    (T ^ (m + q * c)) f - (T ^ m) f ∈ U := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h2 := UpperTheory.periodic_difference_shift U T hT f a q h (m + q * c) (by omega)
    have e : m + q * (c + 1) = m + q * c + q := by ring
    rw [e]
    have hs := U.add_mem h2 ih
    rw [sub_add_sub_cancel] at hs
    exact hs

private theorem UpperTheory.factorial_powers_cauchy {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a p : ℕ)
    (h : (T ^ (a + (p + 1))) f - (T ^ a) f ∈ U) :
    ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j → (T ^ i.factorial) f - (T ^ j.factorial) f ∈ U := by
  obtain ⟨N, hN⟩ : ∃ N, N = a * (p + 1) := ⟨_, rfl⟩
  have haN : a ≤ N := by
    rw [hN]
    exact Nat.le_mul_of_pos_right a (Nat.succ_pos p)
  have hbase : ∀ i, N + (p + 1) ≤ i → (T ^ i.factorial) f - (T ^ N) f ∈ U := by
    intro i hi
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.succ_pos p) (show p + 1 ≤ i by omega)
    have hi' : N ≤ i.factorial := le_trans (by omega) (Nat.self_le_factorial i)
    have hak : a ≤ k := by
      rw [hk, hN, mul_comm] at hi'
      exact Nat.le_of_mul_le_mul_left hi' (Nat.succ_pos p)
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hak
    have e : i.factorial = N + (p + 1) * c := by
      rw [hk, hN, Nat.succ_eq_add_one]
      ring
    rw [e]
    exact UpperTheory.periodic_difference_mul_period U T hT f a (p + 1) h N haN c
  refine ⟨N + (p + 1), fun i j hi hj => ?_⟩
  have hs := U.sub_mem (hbase i hi) (hbase j hj)
  rwa [sub_sub_sub_cancel_right] at hs

theorem UpperTheory.exists_ordinaryProjector_of_eventually_periodic :
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (V : ℕ → Submodule A M) (T : Module.End A M), Antitone V → (∀ k, ∀ f ∈ V k, T f ∈ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ a : ℕ → M, (∀ k, a (k + 1) - a k ∈ V k) → ∃ L, ∀ k, L - a k ∈ V k) → (∀ f k, ∃ a p : ℕ, (T ^ (a + (p + 1))) f - (T ^ a) f ∈ V k) → ∃ e : Module.End A M, ∀ f k, (∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - e f ∈ V k) ∧ (∃ n : ℕ, (T ^ (n + 1)) (e f) - e f ∈ V k) ∧ (f ∈ V k → e f ∈ V k) ∧ ((∃ n : ℕ, (T ^ (n + 1)) f - f ∈ V k) → e f - f ∈ V k) := by
  intro A M _ _ _ V T hV hT hsep hcomp hper
  have hJ : ∀ f k, ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j →
      (T ^ i.factorial) f - (T ^ j.factorial) f ∈ V k := by
    intro f k
    obtain ⟨a, p, h⟩ := hper f k
    exact UpperTheory.factorial_powers_cauchy (V k) T (hT k) f a p h
  choose J hJ using hJ
  let Nm : M → ℕ → ℕ := fun f k => ∑ i ∈ Finset.range (k + 1), J f i
  have hNmJ : ∀ f k, J f k ≤ Nm f k := fun f k =>
    Finset.single_le_sum (f := J f) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
  have hNmmono : ∀ f k, Nm f k ≤ Nm f (k + 1) := fun f k => by
    simp only [Nm]
    rw [Finset.sum_range_succ _ (k + 1)]
    omega
  have hseq : ∀ f k, (T ^ (Nm f (k + 1)).factorial) f - (T ^ (Nm f k).factorial) f ∈ V k :=
    fun f k => hJ f k _ _ (le_trans (hNmJ f k) (hNmmono f k)) (hNmJ f k)
  have hlim : ∀ f, ∃ L, ∀ k, L - (T ^ (Nm f k).factorial) f ∈ V k := fun f =>
    hcomp (fun k => (T ^ (Nm f k).factorial) f) (hseq f)
  choose L hL using hlim
  let P : M → M → Prop := fun f x => ∀ k, ∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - x ∈ V k
  have hPL : ∀ f, P f (L f) := by
    intro f k
    refine ⟨Nm f k, fun j hj => ?_⟩
    have h1 := hJ f k j (Nm f k) (le_trans (hNmJ f k) hj) (hNmJ f k)
    have hs := (V k).sub_mem h1 (hL f k)
    rwa [sub_sub_sub_cancel_right] at hs
  have huniq : ∀ f x y, P f x → P f y → x = y := by
    intro f x y hx hy
    have hxy : x - y = 0 := by
      apply hsep
      intro k
      obtain ⟨J1, h1⟩ := hx k
      obtain ⟨J2, h2⟩ := hy k
      have hs := (V k).sub_mem (h2 (max J1 J2) (le_max_right _ _)) (h1 (max J1 J2) (le_max_left _ _))
      rwa [sub_sub_sub_cancel_left] at hs
    exact sub_eq_zero.mp hxy
  have hPadd : ∀ f g x y, P f x → P g y → P (f + g) (x + y) := by
    intro f g x y hx hy k
    obtain ⟨J1, h1⟩ := hx k
    obtain ⟨J2, h2⟩ := hy k
    refine ⟨max J1 J2, fun j hj => ?_⟩
    have hs := (V k).add_mem (h1 j (le_trans (le_max_left _ _) hj))
      (h2 j (le_trans (le_max_right _ _) hj))
    rw [map_add (f := _)]
    convert hs using 1
    abel
  have hPsmul : ∀ (c : A) f x, P f x → P (c • f) (c • x) := by
    intro c f x hx k
    obtain ⟨J1, h1⟩ := hx k
    refine ⟨J1, fun j hj => ?_⟩
    have hs := (V k).smul_mem c (h1 j hj)
    rwa [smul_sub, ← map_smul] at hs
  let e : Module.End A M :=
    { toFun := L
      map_add' := fun f g => huniq (f + g) _ _ (hPL _) (hPadd f g _ _ (hPL f) (hPL g))
      map_smul' := fun c f => huniq (c • f) _ _ (hPL _) (hPsmul c f _ (hPL f)) }
  refine ⟨e, fun f k => ⟨hPL f k, ?_, ?_, ?_⟩⟩
  · obtain ⟨a, p, h⟩ := hper f k
    obtain ⟨J1, h1⟩ := hPL f k
    refine ⟨p, ?_⟩
    show (T ^ (p + 1)) (L f) - L f ∈ V k
    obtain ⟨j, hjdef⟩ : ∃ j, j = max J1 a := ⟨_, rfl⟩
    have hja : a ≤ j.factorial := le_trans (by omega) (Nat.self_le_factorial _)
    have hA := h1 j (by omega)
    have hB := UpperTheory.periodic_difference_shift (V k) T (hT k) f a (p + 1) h j.factorial hja
    have hC := UpperTheory.pow_preserves_submodule (V k) T (hT k) (p + 1) _ hA
    have eq : (T ^ (p + 1)) ((T ^ j.factorial) f) = (T ^ (j.factorial + (p + 1))) f := by
      rw [add_comm j.factorial (p + 1), pow_add T (p + 1) j.factorial, Module.End.mul_apply]
    have hsum := (V k).add_mem ((V k).add_mem ((V k).neg_mem hC) hB) hA
    rw [map_sub, eq] at hsum
    convert hsum using 1
    abel
  · intro hf
    obtain ⟨J1, h1⟩ := hPL f k
    have hA := h1 J1 le_rfl
    have hB := UpperTheory.pow_preserves_submodule (V k) T (hT k) J1.factorial f hf
    show L f ∈ V k
    have hs := (V k).sub_mem hB hA
    rwa [sub_sub_cancel] at hs
  · rintro ⟨n, hn⟩
    have h0 : (T ^ (0 + (n + 1))) f - (T ^ 0) f ∈ V k := by simpa using hn
    obtain ⟨J1, h1⟩ := hPL f k
    obtain ⟨N, hN⟩ : ∃ N, N = max J1 (n + 1) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.succ_pos n) (show n + 1 ≤ N by omega)
    have hB := UpperTheory.periodic_difference_mul_period (V k) T (hT k) f 0 (n + 1) h0 0 le_rfl c
    rw [zero_add, pow_zero, ← hc] at hB
    have hA := h1 N (by omega)
    show L f - f ∈ V k
    have hs := (V k).sub_mem hB hA
    rw [sub_sub_sub_cancel_left] at hs
    simpa using hs
end

section

open scoped TensorProduct

theorem UpperTheory.exists_factor_dual_embedding_of_ne_zero_tensor :
    ∀ (I : Type) [Finite I] (W : I → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)] (N : Type) [AddCommGroup N] [Module ℂ N] (Φ : Module.Dual ℂ (⨂[ℂ] i, W i) →ₗ[ℂ] N), Φ ≠ 0 → ∀ y : I, ∃ E : Module.Dual ℂ (W y) →ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] i, W i), Φ ∘ₗ E ≠ 0 ∧ ∀ T : ∀ i, W i →ₗ[ℂ] W i, (∀ i, i ≠ y → T i = LinearMap.id) → ∀ m, E m ∘ₗ PiTensorProduct.map T = E (m ∘ₗ T y) := by
  intro I _ W _ _ _ N _ _ Φ hΦ y
  classical
  have := Fintype.ofFinite I
  have hinv := PiTensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse
    (R := ℂ) (M := W) (fun i => Module.Free.chooseBasis ℂ (W i))
  have hf : ∃ f : ∀ i, Module.Dual ℂ (W i),
      Φ (PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f)) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : Φ ∘ₗ PiTensorProduct.dualDistrib = 0 := by
      apply PiTensorProduct.ext
      ext f
      simpa using h f
    apply hΦ
    rw [← LinearMap.comp_id Φ, ← hinv, ← LinearMap.comp_assoc, h0, LinearMap.zero_comp]
  obtain ⟨f, hf⟩ := hf
  refine ⟨PiTensorProduct.dualDistrib ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap f y, ?_, ?_⟩
  · intro h
    apply hf
    have := LinearMap.congr_fun h (f y)
    simpa using this
  · intro T hT m
    apply PiTensorProduct.ext
    ext w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      PiTensorProduct.map_tprod, MultilinearMap.toLinearMap_apply,
      PiTensorProduct.dualDistrib_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = y
    · subst hi
      simp
    · simp [Function.update_of_ne hi, hT i hi]
end

section

open scoped MonoidAlgebra

private theorem ss_proj {R V : Type} [Ring R] [AddCommGroup V] [Module R V]
    [IsSemisimpleModule R V] (s : Finset V) :
    ∃ (κ : Type) (_ : Fintype κ) (S : κ → Submodule R V) (P : κ → V →ₗ[R] V),
      (∀ i, IsAtom (S i)) ∧ (∀ i w, P i w ∈ S i) ∧ ∀ w ∈ s, ∑ i, P i w = w := by
  classical
  obtain ⟨t, e, -, ht⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R V
  let K : Finset t := s.biUnion fun w => (e w).support
  let Q : t → V →ₗ[R] V := fun m =>
    e.symm.toLinearMap ∘ₗ DFinsupp.lsingle (R := R) (M := fun m : t => m.1) m ∘ₗ
      DFinsupp.lapply (R := R) (M := fun m : t => m.1) m ∘ₗ e.toLinearMap
  let j : (m : t) → (m.1 →ₗ[R] V) := fun m =>
    e.symm.toLinearMap ∘ₗ DFinsupp.lsingle (R := R) (M := fun m : t => m.1) m
  have hj : ∀ m, Function.Injective (j m) := fun m =>
    e.symm.injective.comp (DFinsupp.single_injective (β := fun m : t => m.1) (i := m))
  refine ⟨K, inferInstance, fun i => LinearMap.range (j i.1), fun i => Q i.1, ?_, ?_, ?_⟩
  · intro i
    rw [← isSimpleModule_iff_isAtom]
    have := ht i.1
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hj i.1)).symm
  · intro i w
    exact ⟨e w i.1, rfl⟩
  · intro w hw
    rw [Finset.sum_coe_sort K (fun i => Q i w)]
    apply e.injective

    rw [map_sum]
    have h1 : ∀ i, e (Q i w) = DFinsupp.single i (e w i) := fun i => by simp [Q]
    simp_rw [h1]
    ext1 m
    rw [DFinsupp.finsetSum_apply]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      exact DFinsupp.single_eq_of_ne hb.symm
    · intro hm
      have : e w m = 0 := by
        by_contra h
        exact hm (Finset.mem_biUnion.mpr ⟨w, hw, DFinsupp.mem_support_iff.mpr h⟩)
      simp [this]

section
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W)

private noncomputable def toSub (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    Submodule ℂ[H] ρ.asModule where
  carrier := {x | ρ.asModuleEquiv x ∈ U}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact U.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_ofPred_eq] at *
    rw [Representation.asModuleEquiv_map_smul]
    exact ρ.asAlgebraHom_mem_of_forall_mem U hU _ hx c

private theorem mem_toSub (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (x : ρ.asModule) :
    x ∈ toSub ρ U hU ↔ ρ.asModuleEquiv x ∈ U := Iff.rfl

private noncomputable def fromSub (N : Submodule ℂ[H] ρ.asModule) : Submodule ℂ W :=
  (N.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap

private theorem mem_fromSub (N : Submodule ℂ[H] ρ.asModule) (x : W) :
    x ∈ fromSub ρ N ↔ ρ.asModuleEquiv.symm x ∈ N := Iff.rfl

private theorem fromSub_inv (N : Submodule ℂ[H] ρ.asModule) (g : H) (u : W)
    (hu : u ∈ fromSub ρ N) : ρ g u ∈ fromSub ρ N := by
  rw [mem_fromSub] at *
  rw [Representation.asModuleEquiv_symm_map_rho]
  exact N.smul_mem _ hu

private theorem from_to (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    fromSub ρ (toSub ρ U hU) = U := by
  ext x; simp [mem_fromSub, mem_toSub]

private theorem from_le_iff (A B : Submodule ℂ[H] ρ.asModule) :
    fromSub ρ A ≤ fromSub ρ B ↔ A ≤ B := by
  constructor
  · intro h x hx
    have := @h (ρ.asModuleEquiv x) (by simpa [mem_fromSub] using hx)
    simpa [mem_fromSub] using this
  · intro h x hx
    exact h hx

private theorem from_inj {A B : Submodule ℂ[H] ρ.asModule} (h : fromSub ρ A = fromSub ρ B) :
    A = B :=
  le_antisymm ((from_le_iff ρ A B).mp h.le) ((from_le_iff ρ B A).mp h.ge)

private theorem from_bot : fromSub ρ ⊥ = ⊥ := by
  ext x; simp [mem_fromSub]

private theorem atom_iff (A : Submodule ℂ[H] ρ.asModule) :
    IsAtom A ↔ fromSub ρ A ≠ ⊥ ∧
      ∀ N ≤ fromSub ρ A, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = fromSub ρ A := by
  constructor
  · intro hA
    refine ⟨fun h => hA.1 (from_inj ρ (h.trans (from_bot ρ).symm)), fun N hN hi => ?_⟩
    rw [← from_to ρ N hi] at hN ⊢
    rcases hA.le_iff.mp ((from_le_iff ρ _ _).mp hN) with h | h
    · left; rw [h, from_bot]
    · right; rw [h]
  · rintro ⟨h0, h⟩
    refine ⟨fun hA => h0 (by rw [hA, from_bot]), fun B hB => ?_⟩
    rcases h _ ((from_le_iff ρ _ _).mpr hB.le) (fromSub_inv ρ B) with h | h
    · exact from_inj ρ (h.trans (from_bot ρ).symm)
    · exact absurd (from_inj ρ h) hB.ne

end

theorem UpperTheory.exists_equivariant_projections_of_sum_irreducible :
    ∀ (H W : Type) [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W), (∀ x : W, x ∈ ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) → ∀ M : Submodule ℂ W, FiniteDimensional ℂ M → ∃ (κ : Type) (_ : Fintype κ) (U : κ → Submodule ℂ W) (P : κ → W →ₗ[ℂ] W), (∀ i, U i ≠ ⊥ ∧ (∀ g, ∀ u ∈ U i, ρ g u ∈ U i) ∧ ∀ N ≤ U i, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U i) ∧ (∀ i w, P i w ∈ U i) ∧ (∀ i g w, P i (ρ g w) = ρ g (P i w)) ∧ ∀ w ∈ M, ∑ i, P i w = w := by
  intro H W _ _ _ ρ hsum M hM
  classical
  have : IsSemisimpleModule ℂ[H] ρ.asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    rw [eq_top_iff]
    intro y _
    have hle : (⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
        ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) ≤
        fromSub ρ (sSup {m : Submodule ℂ[H] ρ.asModule | IsSimpleModule ℂ[H] m}) := by
      refine iSup_le ?_
      rintro ⟨U, h0, hi, hU⟩
      show U ≤ _
      rw [← from_to ρ U hi, from_le_iff]
      apply le_sSup
      show IsSimpleModule ℂ[H] (toSub ρ U hi)
      rw [isSimpleModule_iff_isAtom, atom_iff, from_to]
      exact ⟨h0, hU⟩
    have := hle (hsum (ρ.asModuleEquiv y))
    simpa [mem_fromSub] using this
  obtain ⟨s, hs⟩ : M.FG := (Submodule.fg_iff_finiteDimensional M).mpr hM
  obtain ⟨κ, hκ, S, P, hS, hP, hsum'⟩ :=
    ss_proj (R := ℂ[H]) (V := ρ.asModule) (s.image ρ.asModuleEquiv.symm)
  let Q : κ → W →ₗ[ℂ] W := fun i =>
    ρ.asModuleEquiv.toLinearMap ∘ₗ (P i).restrictScalars ℂ ∘ₗ ρ.asModuleEquiv.symm.toLinearMap
  have hQ : ∀ i w, Q i w = ρ.asModuleEquiv (P i (ρ.asModuleEquiv.symm w)) := fun _ _ => rfl
  refine ⟨κ, hκ, fun i => fromSub ρ (S i), Q, ?_, ?_, ?_, ?_⟩
  · intro i
    have := (atom_iff ρ (S i)).mp (hS i)
    exact ⟨this.1, fromSub_inv ρ _, this.2⟩
  · intro i w
    rw [mem_fromSub, hQ, LinearEquiv.symm_apply_apply]
    exact hP i _
  · intro i g w
    apply ρ.asModuleEquiv.symm.injective
    rw [Representation.asModuleEquiv_symm_map_rho, hQ, hQ, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Representation.asModuleEquiv_symm_map_rho, map_smul]
  · intro w hw
    rw [← hs] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      simp_rw [hQ]

      rw [← map_sum, hsum' _ (Finset.mem_image_of_mem _ hx), LinearEquiv.apply_symm_apply]
    | zero => simp
    | add x y _ _ hx hy => simp_rw [map_add (f := _)]; rw [Finset.sum_add_distrib, hx, hy]
    | smul c x _ hx => simp_rw [map_smul]; rw [← Finset.smul_sum, hx]
end

section

open MvPolynomial in
theorem UpperTheory.symmetricSubalgebra_le_adjoin_range_prod_C_add_X_complex :
    ∀ n : ℕ, MvPolynomial.symmetricSubalgebra (Fin n) ℂ ≤ Algebra.adjoin ℂ (Set.range fun u : ℂ => ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ)) := by
  intro n
  set S := Algebra.adjoin ℂ (Set.range fun u : ℂ => ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ)) with hS
  have hv : ∀ u : ℂ, ∏ k : Fin n, (C u + X k : MvPolynomial (Fin n) ℂ)
      = ∑ j ∈ Finset.range (n + 1), u ^ (n - j) • esymm (Fin n) ℂ j := by
    intro u
    have h := congrArg (Polynomial.eval (C u : MvPolynomial (Fin n) ℂ))
      (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
    simp only [Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, map_pow, mul_comm]
  have he : ∀ j, j < n + 1 → esymm (Fin n) ℂ j ∈ S := by
    intro j hj
    by_contra hc
    obtain ⟨φ, hφ, h0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := Subalgebra.toSubmodule S) hc inferInstance
    have h1 : ∀ x ∈ S, φ x = 0 := fun x hx => (Submodule.eq_bot_iff _).1 h0 _ ⟨x, hx, rfl⟩
    have hp : (∑ i ∈ Finset.range (n + 1), Polynomial.monomial (n - i) (φ (esymm (Fin n) ℂ i))) = 0 := by
      apply Polynomial.funext
      intro u
      have h2 := h1 _ (Algebra.subset_adjoin ⟨u, rfl⟩)

      simp only [hv, map_sum, map_smul, smul_eq_mul] at h2
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
      rw [← h2]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h3 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (n - j)) hp
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h3
    rw [Finset.sum_eq_single j] at h3
    · exact hφ (by simpa using h3)
    · intro b hb hbj
      rw [Finset.mem_range] at hb
      exact Finsupp.single_eq_of_ne (by omega)
    · intro h
      exact absurd (Finset.mem_range.2 hj) h
  intro p hp
  obtain ⟨q, hq⟩ := (esymmAlgHom_fin_bijective ℂ n).2 ⟨p, hp⟩
  have hq' : p = aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) q := by
    rw [← esymmAlgHom_apply, hq]
  rw [hq']
  have : Algebra.adjoin ℂ (Set.range fun i : Fin n => esymm (Fin n) ℂ (i + 1)) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact he _ (by have := i.2; omega))
  apply this
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨q, rfl⟩
end
