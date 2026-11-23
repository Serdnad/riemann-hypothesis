module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Basic

@[expose] public section

section

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def IsStable (T : Set (End ℂ M)) (p : Submodule ℂ M) : Prop :=
  ∀ t ∈ T, ∀ x ∈ p, t x ∈ p

def IsSimpleUnder (T : Set (End ℂ M)) : Prop :=
  Nontrivial M ∧ ∀ p : Submodule ℂ M, IsStable T p → p = ⊥ ∨ p = ⊤

theorem IsStable.adjoin {T : Set (End ℂ M)} {p : Submodule ℂ M} (h : IsStable T p) :
    ∀ a ∈ Algebra.adjoin ℂ T, ∀ x ∈ p, a x ∈ p := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem t ht => exact h t ht
  | algebraMap c =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact p.smul_mem c hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.add_apply]
    exact p.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [Module.End.mul_apply]
    exact ha _ (hb x hx)

theorem commute_of_mem_adjoin {T : Set (End ℂ M)} {a : End ℂ M} (ha : ∀ t ∈ T, Commute a t) :
    ∀ b ∈ Algebra.adjoin ℂ T, Commute a b := by
  intro b hb
  induction hb using Algebra.adjoin_induction with
  | mem t ht => exact ha t ht
  | algebraMap c => exact (Algebra.commutes' c a).symm
  | add b c _ _ hb hc => exact hb.add_right hc
  | mul b c _ _ hb hc => exact hb.mul_right hc

theorem IsStable.mono {T₁ T₂ : Set (End ℂ M)} {p : Submodule ℂ M} (h : IsStable T₂ p)
    (hT : T₁ ⊆ T₂) : IsStable T₁ p :=
  fun t ht => h t (hT ht)

variable [FiniteDimensional ℂ M]

theorem adjoin_eq_top {T : Set (End ℂ M)} (h : IsSimpleUnder T) : Algebra.adjoin ℂ T = ⊤ := by
  have := h.1
  set A := Algebra.adjoin ℂ T
  have hsimple : IsSimpleModule A M := by
    have : Nontrivial (Submodule A M) := (Submodule.nontrivial_iff A).2 h.1
    refine { eq_bot_or_eq_top := fun p => ?_ }
    have hst : IsStable T (p.restrictScalars ℂ) := by
      intro t ht x hx
      have : (⟨t, Algebra.subset_adjoin ht⟩ : A) • x ∈ p := p.smul_mem _ hx
      exact this
    rcases h.2 _ hst with h0 | h0
    · left
      rw [← Submodule.restrictScalars_eq_bot_iff ℂ]
      exact h0
    · right
      rw [← Submodule.restrictScalars_eq_top_iff ℂ]
      exact h0
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ (A := A) (V := M)
  have : Module.Finite (End A M) M := Module.Finite.of_restrictScalars_finite ℂ (End A M) M
  have hsurj := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := M)
  refine eq_top_iff.2 fun φ _ => ?_
  have hφ : ∀ (f : End A M) (x : M), φ (f x) = f (φ x) := by
    intro f x
    obtain ⟨c, rfl⟩ := hb.2 f
    simp [Algebra.algebraMap_eq_smul_one]
  let ψ : End (End A M) M :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun f x => hφ f x }
  obtain ⟨a, ha⟩ := hsurj ψ
  have : (a : End ℂ M) = φ := by
    ext x
    have := congrArg (fun g : End (End A M) M => g x) ha
    exact this
  rw [← this]
  exact a.2


omit [FiniteDimensional ℂ M] in
theorem eq_zero_of_forall_mem {T₁ T₂ : Set (End ℂ M)} (h : IsSimpleUnder (T₁ ∪ T₂))
    (hc : ∀ a ∈ T₁, ∀ b ∈ T₂, Commute a b) {N : Submodule ℂ M} (hN : N ≠ ⊥) (hNs : IsStable T₁ N)
    {a : End ℂ M} (ha : ∀ b ∈ T₂, Commute a b) (h0 : ∀ x ∈ N, a x = 0) : a = 0 := by
  set B := Algebra.adjoin ℂ T₂
  set P : Submodule ℂ M := ⨆ b : B, N.map (b : End ℂ M)
  have hmap : ∀ b : B, N.map (b : End ℂ M) ≤ P := fun b => le_iSup (fun b : B => N.map (b : End ℂ M)) b
  have hst : IsStable (T₁ ∪ T₂) P := by
    intro t ht x hx
    have hle : P ≤ P.comap t := by
      refine iSup_le fun b => ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [Submodule.mem_comap]
      rcases ht with ht | ht
      · have hcomm : Commute t (b : End ℂ M) :=
          commute_of_mem_adjoin (fun s hs => hc t ht s hs) b b.2
        have : t ((b : End ℂ M) n) = (b : End ℂ M) (t n) := by
          rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
        rw [this]
        exact hmap b ⟨t n, hNs t ht n hn, rfl⟩
      · have htb : t * (b : End ℂ M) ∈ B := B.mul_mem (Algebra.subset_adjoin ht) b.2
        exact hmap ⟨_, htb⟩ ⟨n, hn, rfl⟩
    exact hle hx
  have hP : P ≠ ⊥ := by
    intro hP
    apply hN
    rw [eq_bot_iff]
    intro n hn
    have : n ∈ P := hmap 1 ⟨n, hn, by simp⟩
    rwa [hP] at this
  have hPtop : P = ⊤ := (h.2 P hst).resolve_left hP
  have hker : P ≤ LinearMap.ker a := by
    refine iSup_le fun b => ?_
    rintro _ ⟨n, hn, rfl⟩
    rw [LinearMap.mem_ker]
    have hcomm : Commute a (b : End ℂ M) := commute_of_mem_adjoin ha b b.2
    rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, h0 n hn, map_zero]
  ext x
  have : x ∈ LinearMap.ker a := hker (hPtop ▸ Submodule.mem_top)
  simpa using this

def restrictSet (T : Set (End ℂ M)) (N : Submodule ℂ M) (hN : IsStable T N) : Set (End ℂ N) :=
  Set.range fun t : T => (t : End ℂ M).restrict (hN t t.2)


omit [FiniteDimensional ℂ M] in
theorem exists_of_mem_adjoin_restrictSet {T : Set (End ℂ M)} {N : Submodule ℂ M}
    (hN : IsStable T N) {b : End ℂ N} (hb : b ∈ Algebra.adjoin ℂ (restrictSet T N hN)) :
    ∃ a ∈ Algebra.adjoin ℂ T, ∀ x : N, (b x : M) = a x := by
  let S : Subalgebra ℂ (End ℂ N) :=
    { carrier := {b | ∃ a ∈ Algebra.adjoin ℂ T, ∀ x : N, (b x : M) = a x}
      mul_mem' := by
        rintro b₁ b₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        exact ⟨a₁ * a₂, Subalgebra.mul_mem _ ha₁ ha₂, fun x => by
          rw [Module.End.mul_apply, h₁, Module.End.mul_apply, h₂]⟩
      add_mem' := by
        rintro b₁ b₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
        exact ⟨a₁ + a₂, Subalgebra.add_mem _ ha₁ ha₂, fun x => by
          rw [LinearMap.add_apply, Submodule.coe_add, h₁, h₂, LinearMap.add_apply]⟩
      algebraMap_mem' := fun c => ⟨algebraMap ℂ (End ℂ M) c, Subalgebra.algebraMap_mem _ c,
        fun x => by simp [Algebra.algebraMap_eq_smul_one]⟩ }
  have : Algebra.adjoin ℂ (restrictSet T N hN) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨t, Algebra.subset_adjoin t.2, fun x => rfl⟩
  exact this hb

theorem exists_simple_stable (T : Set (End ℂ M)) [Nontrivial M] :
    ∃ (N : Submodule ℂ M) (hN : IsStable T N), N ≠ ⊥ ∧ IsSimpleUnder (restrictSet T N hN) := by
  classical
  have hex : ∃ d, ∃ N : Submodule ℂ M, N ≠ ⊥ ∧ IsStable T N ∧ Module.finrank ℂ N = d :=
    ⟨_, ⊤, top_ne_bot, fun _ _ _ _ => trivial, rfl⟩
  obtain ⟨N, hN0, hNs, hNd⟩ := Nat.find_spec hex
  have hmin : ∀ N' : Submodule ℂ M, N' ≠ ⊥ → IsStable T N' → Module.finrank ℂ N ≤ Module.finrank ℂ N' :=
    fun N' h1 h2 => hNd ▸ Nat.find_min' hex ⟨N', h1, h2, rfl⟩
  refine ⟨N, hNs, hN0, ?_, ?_⟩
  · exact Submodule.nontrivial_iff_ne_bot.2 hN0
  · intro q hq
    by_cases hq0 : q = ⊥
    · exact Or.inl hq0
    right
    have hst : IsStable T (q.map N.subtype) := by
      rintro t ht _ ⟨x, hx, rfl⟩
      exact ⟨(t : End ℂ M).restrict (hNs t ht) x, hq _ ⟨⟨t, ht⟩, rfl⟩ x hx, rfl⟩
    have hne : q.map N.subtype ≠ ⊥ := by
      intro h0
      apply hq0
      rw [eq_bot_iff]
      intro x hx
      have : (x : M) ∈ q.map N.subtype := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    have hle := hmin _ hne hst
    rw [Submodule.finrank_map_subtype_eq] at hle
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le q) hle)

end RestrictedTensor

end GroundTheory.Automorphic
end
end

section

noncomputable section

namespace GroundTheory.Automorphic

namespace PeterssonComplement

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)

variable {ι}

theorem aeval_mem {T : Module.End ℂ V} {Z : Submodule ℂ V} (hZ : ∀ z ∈ Z, T z ∈ Z) (q : ℂ[X]) :
    ∀ z ∈ Z, aeval T q z ∈ Z := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro z hz
    rw [aeval_C, Module.algebraMap_end_apply]
    exact Z.smul_mem a hz
  | add p q hp hq =>
    intro z hz
    rw [map_add (f := _), LinearMap.add_apply]
    exact Z.add_mem (hp z hz) (hq z hz)
  | monomial k a ih =>
    intro z hz
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (hZ z hz)

theorem apply_aeval_comm (T : Module.End ℂ V) (q : ℂ[X]) (z : V) : T (aeval T q z) = aeval T q (T z) := by
  have h := (Commute.all (X : ℂ[X]) q).map (aeval T)
  rw [aeval_X] at h
  exact congrArg (fun L : Module.End ℂ V => L z) h.eq

end PeterssonComplement

end GroundTheory.Automorphic
end
end

section

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module Set TensorProduct

open scoped TensorProduct

variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
  {V₁ V₂ V₁' V₂' : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₁'] [Module ℂ V₁'] [AddCommGroup V₂'] [Module ℂ V₂']

def contractRight (l : Dual ℂ V₂) : V₁ ⊗[ℂ] V₂ →ₗ[ℂ] V₁ :=
  TensorProduct.rid ℂ V₁ ∘ₗ TensorProduct.map LinearMap.id l

def contractLeft (l : Dual ℂ V₁) : V₁ ⊗[ℂ] V₂ →ₗ[ℂ] V₂ :=
  TensorProduct.lid ℂ V₂ ∘ₗ TensorProduct.map l LinearMap.id

theorem contractRight_tmul (l : Dual ℂ V₂) (x : V₁) (y : V₂) :
    contractRight l (x ⊗ₜ y) = l y • x := by
  simp [contractRight]

theorem contractLeft_tmul (l : Dual ℂ V₁) (x : V₁) (y : V₂) :
    contractLeft (V₂ := V₂) l (x ⊗ₜ y) = l x • y := by
  simp [contractLeft]

theorem exists_contractRight_ne_zero {z : V₁ ⊗[ℂ] V₂} (hz : z ≠ 0) :
    ∃ l : Dual ℂ V₂, contractRight l z ≠ 0 := by
  classical
  let b := Basis.ofVectorSpace ℂ V₂
  set F := TensorProduct.equivFinsuppOfBasisRight (M := V₁) b
  have hfz : F z ≠ 0 := fun h => hz (F.injective (h.trans (map_zero F).symm))
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.1 hfz
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hj₀
  refine ⟨b.coord j₀, ?_⟩
  have hz' : z = (F z).sum fun j a => a ⊗ₜ[ℂ] b j := by
    conv_lhs => rw [← F.symm_apply_apply z]
    exact TensorProduct.equivFinsuppOfBasisRight_symm_apply b (F z)
  rw [hz', map_finsuppSum]
  simp only [contractRight_tmul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  rw [Finsupp.sum, Finset.sum_eq_single j₀]
  · simpa using hj₀
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finsupp.mem_support_iff.2 hj₀) h

theorem exists_contractLeft_ne_zero {z : V₁ ⊗[ℂ] V₂} (hz : z ≠ 0) :
    ∃ l : Dual ℂ V₁, contractLeft l z ≠ 0 := by
  obtain ⟨l, hl⟩ := exists_contractRight_ne_zero (V₁ := V₂) (V₂ := V₁)
    (z := TensorProduct.comm ℂ V₁ V₂ z) (fun h => hz (by
      have := congrArg (TensorProduct.comm ℂ V₁ V₂).symm h
      simpa using this))
  refine ⟨l, ?_⟩
  have key : ∀ z' : V₁ ⊗[ℂ] V₂,
      contractLeft (V₂ := V₂) l z' = contractRight l (TensorProduct.comm ℂ V₁ V₂ z') := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [contractLeft_tmul, contractRight_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rwa [key]

theorem tmul_ne_zero_of {x : V₁} {y : V₂} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨l, hl⟩ : ∃ l : Dual ℂ V₂, l y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hcon)
  intro h
  have := congrArg (contractRight l) h
  rw [contractRight_tmul, map_zero] at this
  exact (smul_ne_zero hl hx) this

variable {π₁ : Representation ℂ M₁ V₁} {π₂ : Representation ℂ M₂ V₂}
  {π₁' : Representation ℂ M₁ V₁'} {π₂' : Representation ℂ M₂ V₂'}

end RestrictedTensor

end GroundTheory.Automorphic
end
end
