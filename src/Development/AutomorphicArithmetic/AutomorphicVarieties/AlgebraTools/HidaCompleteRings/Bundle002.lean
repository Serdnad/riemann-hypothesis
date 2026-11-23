module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteLength
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
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (I J : Ideal R) (n : ℕ), J ^ n ≤ I → I ≤ J → IsAdicComplete I M → IsAdicComplete J M := by
  intro R M _ _ _ I J n hn hIJ hI
  have hle : ∀ k, J ^ ((n + 1) * k) • (⊤ : Submodule R M) ≤ I ^ k • ⊤ := fun k => by
    apply Submodule.smul_mono_left
    calc J ^ ((n + 1) * k) ≤ J ^ (n * k) :=
          Ideal.pow_le_pow_right (Nat.mul_le_mul_right k (Nat.le_succ n))
      _ = (J ^ n) ^ k := pow_mul J n k
      _ ≤ I ^ k := Ideal.pow_right_mono hn k
  have hge : ∀ k, I ^ k • (⊤ : Submodule R M) ≤ J ^ k • ⊤ := fun k =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ k)
  refine
    { haus' := fun x hx => hI.toIsHausdorff.haus' x fun k => (hx ((n + 1) * k)).mono (hle k)
      prec' := fun f hf => ?_ }
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' (fun k => f ((n + 1) * k))
    (fun {a b} hab => (hf (Nat.mul_le_mul_left (n + 1) hab)).mono (hle a))
  refine ⟨L, fun m => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left m (Nat.succ_pos n))).trans ((hL m).mono (hge m))
end

section

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section Ord

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def ordPart (U : Module.End R M) : Submodule R M := ⨅ n : ℕ, LinearMap.range (U ^ n)

theorem mem_ordPart {U : Module.End R M} {x : M} : x ∈ ordPart U ↔ ∀ n : ℕ, ∃ y, (U ^ n) y = x := by
  simp [ordPart, Submodule.mem_iInf]

theorem map_mem_smul_top {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (J : Ideal R)
    {x : M} (hx : x ∈ (J • ⊤ : Submodule R M)) : f x ∈ (J • ⊤ : Submodule R N) := by
  have h1 := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

def nilPart (I : Ideal R) (U : Module.End R M) : Submodule R M where
  carrier := {x | ∀ k : ℕ, ∃ n : ℕ, (U ^ n) x ∈ (I ^ k • ⊤ : Submodule R M)}
  zero_mem' := fun k => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy k
    obtain ⟨n, hn⟩ := hx k
    obtain ⟨m, hm⟩ := hy k
    refine ⟨n + m, ?_⟩
    rw [map_add (f := _)]
    refine Submodule.add_mem _ ?_ ?_
    · rw [add_comm, pow_add, Module.End.mul_apply]; exact map_mem_smul_top _ _ hn
    · rw [pow_add, Module.End.mul_apply]; exact map_mem_smul_top _ _ hm
  smul_mem' := by
    intro c x hx k
    obtain ⟨n, hn⟩ := hx k
    exact ⟨n, by rw [map_smul]; exact Submodule.smul_mem _ _ hn⟩

structure IsOrdProj (I : Ideal R) (U e : Module.End R M) : Prop where
  idem : IsIdempotentElem e
  comm : Commute U e
  bij : Set.BijOn U (LinearMap.range e) (LinearMap.range e)
  nil : ∀ k : ℕ, ∃ n : ℕ, ∀ x, (U ^ n) (x - e x) ∈ (I ^ k • ⊤ : Submodule R M)

def IsFactLim (I : Ideal R) (U e : Module.End R M) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ x, (U ^ j.factorial) x - e x ∈ (I ^ k • ⊤ : Submodule R M)


open Classical in
noncomputable def ordProj (I : Ideal R) (U : Module.End R M) : Module.End R M :=
  by
    classical
    exact if h : ∃ e, IsOrdProj I U e then h.choose else 0

theorem isOrdProj_ordProj {I : Ideal R} {U : Module.End R M} (h : ∃ e, IsOrdProj I U e) :
    IsOrdProj I U (ordProj I U) := by
  unfold ordProj
  rw [dite_eq_left h]
  exact h.choose_spec


variable (M) in
structure OrdAdm (I : Ideal R) : Prop where
  complete : IsAdicComplete I M
  finLen : ∀ k : ℕ, IsFiniteLength R (M ⧸ (I ^ k • ⊤ : Submodule R M))

end Ord

section Map

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
  {M : Type*} [AddCommGroup M] [Module A M]
  {M' : Type*} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']

theorem pow_intertwine {U : Module.End A M} {U' : Module.End A' M'} {f : M →ₗ[A] M'}
    (h : ∀ x, f (U x) = U' (f x)) (n : ℕ) (x : M) : f ((U ^ n) x) = (U' ^ n) (f x) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, h, ih]

end Map

section Lim

variable {R : Type*} [CommRing R] {P : ℕ → Type*} [∀ b, AddCommGroup (P b)] [∀ b, Module R (P b)]
  {Q : ℕ → Type*} [∀ b, AddCommGroup (Q b)] [∀ b, Module R (Q b)]

end Lim

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
end

section

open IsLocalRing

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec (I := I) inferInstance (f := fun n => f n i) (fun {m n} hmn => ?_)
    have := (mem_smul_top_pi (I ^ m) _).1 (SModEq.sub_mem.1 (hf hmn)) i
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    simpa using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := SModEq.sub_mem.1 (hL i n)
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at this
  simpa using this

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  have hmap : ∀ n, Submodule.map π (I ^ n • ⊤) = I ^ n • (⊤ : Submodule R M) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]
  refine ⟨fun f hf => ?_⟩
  have hd : ∀ n, ∃ y ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)), π y = f (n + 1) - f n := by
    intro n
    have : f (n + 1) - f n ∈ Submodule.map π (I ^ n • ⊤) := by
      rw [hmap]
      exact SModEq.sub_mem.1 (hf (Nat.le_succ n)).symm
    exact Submodule.mem_map.1 this
  choose d hdI hdπ using hd
  obtain ⟨g0, hg0⟩ := hπ (f 0)
  have hgπ : ∀ n, π (g0 + ∑ k ∈ Finset.range n, d k) = f n := by
    intro n
    induction n with
    | zero => simp [hg0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, map_add (f := _), ih, hdπ]
      abel
  have hcau : ∀ {m n : ℕ}, m ≤ n → (g0 + ∑ k ∈ Finset.range m, d k) ≡
      (g0 + ∑ k ∈ Finset.range n, d k) [SMOD (I ^ m • ⊤ : Submodule R (Fin r → R))] := by
    intro m n hmn
    rw [SModEq.sub_mem, ← Finset.sum_range_add_sum_Ico _ hmn]
    have e : g0 + ∑ k ∈ Finset.range m, d k
        - (g0 + (∑ k ∈ Finset.range m, d k + ∑ k ∈ Finset.Ico m n, d k))
        = -∑ k ∈ Finset.Ico m n, d k := by abel
    rw [e]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1) (hdI k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance
    (f := fun n => g0 + ∑ k ∈ Finset.range n, d k) hcau
  refine ⟨π L, fun n => ?_⟩
  rw [← hgπ n, SModEq.sub_mem, ← map_sub, ← hmap n]
  exact Submodule.mem_map_of_mem (SModEq.sub_mem.1 (hL n))

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl :
    ∀ (Λ M : Type) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ) [IsAdicComplete I Λ] [AddCommGroup M] [Module Λ M] [Module.Finite Λ M], IsAdicComplete I M := by
  intro Λ M _ _ I _ _ _ _
  exact
    { toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I)
      toIsPrecomplete := isPrecomplete_finite I }
end
