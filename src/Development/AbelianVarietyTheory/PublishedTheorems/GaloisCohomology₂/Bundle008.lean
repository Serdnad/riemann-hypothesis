module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine ValuativeRel

noncomputable section
namespace GlobalTheory.LocGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exh_unipRad_one {s : ℕ} {d : Fin s → ℕ} (e : (Σ a : Fin s, Fin (d a)) ≃ Fin 1) : unipRad k e = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  have h := det_eq_one_of_mem_unipRad k hu
  have h2 : (u : Matrix (Fin 1) (Fin 1) k).det = 1 := by
    simpa using congrArg Units.val h
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simpa using h2

theorem exh_deg_one (c : IrrCl (GL (Fin 1) k)) : ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 (IrrGL.rep ⟨1, c⟩) := by
  have hc : IrrGL.IsCusp (⟨1, c⟩ : IrrGL (k := k)) := ⟨one_pos, c.rep.smooth, fun s d e he => absurd (exh_unipRad_one e) he⟩
  exact ⟨_, (single_spec hc).2.2.2⟩

theorem exh_equiv_zero {m : Fin 0 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin 0)
    {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Levi k m) W)
    (E : W ≃ₗ[ℂ] ℂ) (π : Representation ℂ (GL (Fin 0) k) V) (hirr : π.IsIrreducible) :
    Nonempty ((parInd e ρ).Equiv π) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  have hnt : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    have : (⊥ : Subrepresentation π) = ⊤ := by
      ext v; rw [h v]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := hnt
  let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by simpa [hg g] using hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  have hspan : ∀ w : V, ∃ a : ℂ, a • v = w := fun w => by
    have : w ∈ S := by rw [hS]; trivial
    exact Submodule.mem_span_singleton.1 this
  let f : (parInd e ρ).IntertwiningMap π :=
    { toFun := fun φ => E (φ.1.1 1) • v
      map_add' := fun φ ψ => by
        show E (φ.1.1 1 + ψ.1.1 1) • v = _
        rw [map_add (f := _), add_smul]
      map_smul' := fun a φ => by
        show E (a • φ.1.1 1) • v = a • (E (φ.1.1 1) • v)
        rw [map_smul, smul_eq_mul, mul_smul]
      isIntertwining' := fun g => by rw [hg g, map_one, map_one]; rfl }
  have hinj : Function.Injective f := fun φ ψ h => by
    have h1 : E (φ.1.1 1) • v = E (ψ.1.1 1) • v := h
    have h2 := E.injective (smul_left_injective ℂ hv h1)
    exact Subtype.ext (Subtype.ext (funext fun g => by rw [hg g]; exact h2))
  have hsurj : Function.Surjective f := fun w => by
    obtain ⟨a, rfl⟩ := hspan w
    refine ⟨⟨⟨fun _ => E.symm a, fun p g => ?_⟩, ?_⟩, ?_⟩
    · have : p = 1 := Subtype.ext (hg _)
      subst this; simp
    · exact mem_smoothPart_of_nhds (Filter.univ_mem' fun g => by rw [hg g]; simp)
    · show E (E.symm a) • v = a • v
      simp
  exact ⟨equivOfBijective f ⟨hinj, hsurj⟩⟩

theorem exh_deg_zero (c : IrrCl (GL (Fin 0) k)) : IsL (0 : Multiset (Segment k)) (IrrGL.rep ⟨0, c⟩) := by
  let x : Fin 0 → IrrGL (k := k) := Fin.elim0
  have hd : ∑ a, (x a).1 = 0 := by simp
  refine ⟨0, x, hd, ⟨Fin.elim0, ⟨rfl, fun i => i.elim0⟩, fun i => i.elim0⟩, ?_⟩
  obtain ⟨φ⟩ := exh_equiv_zero (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)
    (PiTensorProduct.isEmptyEquiv (Fin 0)) c.rep.ρ c.rep.irr
  exact (isCosocle_self c.rep.irr).of_equiv (.refl _) φ.symm

theorem exh_le_one (x : IrrGL (k := k)) (hx : x.1 ≤ 1) : ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep := by
  obtain ⟨n, c⟩ := x
  obtain rfl | rfl : n = 0 ∨ n = 1 := by simp at hx; omega
  · exact ⟨0, exh_deg_zero c⟩
  · exact exh_deg_one c

end GlobalTheory.LocGL
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

def IsUnitaryLSeg (δ : IrrGL (k := k)) : Prop := (∃ Δ : Segment k, IsLSeg Δ δ.rep) ∧ IsUnitarisable δ.rep

def factors (δ : List (IrrGL (k := k))) (τ : List (IrrGL (k := k) × ℝ)) : List (IrrGL (k := k)) :=
  δ ++ τ.flatMap fun p => [p.1.nu (p.2 : ℝ), p.1.nu ((-p.2 : ℝ) : ℂ)]

def IsComplementaryProduct (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (δ : List (IrrGL (k := k))) (τ : List (IrrGL (k := k) × ℝ)), (∀ x ∈ δ, IsUnitaryLSeg x) ∧
    (∀ p ∈ τ, IsUnitaryLSeg p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
    ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), List.ofFn x = factors δ τ ∧
      Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.GenericUnitary

namespace GlobalTheory.Published

def GenericUnitaryDualGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsGeneric π → GenericUnitary.IsComplementaryProduct π

end GlobalTheory.Published

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

theorem exists_of_mem_factors {δ : List (IrrGL (k := k))} {τ : List (IrrGL (k := k) × ℝ)} (hδ : ∀ x ∈ δ, IsUnitaryLSeg x)
    (hτ : ∀ p ∈ τ, IsUnitaryLSeg p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) {y : IrrGL (k := k)} (hy : y ∈ factors δ τ) :
    ∃ (x : IrrGL (k := k)) (s : ℝ), IsUnitaryLSeg x ∧ |s| < 1 / 2 ∧ y = x.nu s := by
  rcases List.mem_append.1 hy with hy | hy
  · exact ⟨y, 0, hδ y hy, by norm_num, by simp⟩
  · obtain ⟨p, hp, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨h1, h2, h3⟩ := hτ p hp
    rcases List.mem_pair.1 hy with rfl | rfl
    · exact ⟨p.1, p.2, h1, by rwa [abs_of_pos h2], rfl⟩
    · exact ⟨p.1, -p.2, h1, by rwa [abs_neg, abs_of_pos h2], rfl⟩

theorem IsComplementaryProduct.exists_prod {π : Representation ℂ (GL (Fin N) k) V} (H : IsComplementaryProduct π) :
    ∃ (h : ℕ) (δ : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, IsUnitarisable (δ j).rep) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, φ⟩ := H
  choose y s hy hs e using fun j => exists_of_mem_factors hδ hτ (y := x j) (hx ▸ List.mem_ofFn.2 ⟨j, rfl⟩)
  choose Δ hΔ using fun j => (hy j).1
  obtain rfl : x = fun j => (y j).nu (s j) := funext e
  exact ⟨h, y, Δ, s, hΔ, fun j => (hy j).2, hs, hd, φ⟩

theorem isUnitarisable_of_equiv {G : Type} [Group G] {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem isUnitaryLSeg_of_isCusp {ρ : IrrGL (k := k)} (hρ : ρ.IsCusp) (hu : IsUnitarisable ρ.rep) : IsUnitaryLSeg ρ :=
  ⟨⟨_, (single_spec hρ).2.1⟩, hu⟩

end GlobalTheory.GenericUnitary

namespace GlobalTheory.Published

theorem GenericUnitaryDualGL.exists_prod (H : GenericUnitaryDualGL) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π)
    (hg : IsGeneric π) :
    ∃ (h : ℕ) (δ : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, IsUnitarisable (δ j).rep) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) :=
  (H k N V π hs hi hu hg).exists_prod

end GlobalTheory.Published
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

def DepthZeroInduction : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))), HasSupport x.rep s →
    (∀ y ∈ s, fixed y.rep (KOne k (Fin y.1)) ≠ ⊥) → fixed x.rep (KOne k (Fin x.1)) ≠ ⊥

end GlobalTheory.Published

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.Published

def GenericUnlinkedGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsGeneric π →
    ∃ (h : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N),
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) ∧ (∀ i, IsLSeg (Δ i) (x i).rep) ∧ Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.Published

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

def LanglandsExhaustionGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (x : IrrGL (k := k)), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep

end GlobalTheory.Published

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.Published

def LanglandsMultisegments : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    (∀ (𝔪 𝔫 : Multiset (Segment k)) (x : IrrGL (k := k)), IsL 𝔪 x.rep → IsL 𝔫 x.rep → 𝔪 = 𝔫) ∧
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd)

end GlobalTheory.Published

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.Published

def StandardCosocleGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
    ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd)

end GlobalTheory.Published

end
end
