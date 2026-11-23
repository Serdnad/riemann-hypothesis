module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportProposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem not_dvd_diff (v : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2)
    (hv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  have hp := D.host.g_prime i
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.F D.host.E hp (D.nd.g_split i) v hv
  have hvq : v.asIdeal ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.F) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq D.host.F hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {((D.host.g i : ℕ) : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem diff_avoid (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ t ∈ differentIdeal ℤ (𝓞 D.host.F), algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∉ P.asIdeal := by
  have hPp := P.isPrime
  let v : HeightOneSpectrum (𝓞 D.host.F) :=
    ⟨P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.IsPrime.comap _, by
      intro hb
      apply P.ne_bot
      have hg0 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
        rw [Ideal.mem_comap, map_natCast]; exact hP
      rw [hb, Ideal.mem_bot] at hg0
      exfalso
      have : (gS D : ℕ) ≠ 0 := by
        unfold Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
      exact this (by exact_mod_cast hg0)⟩
  have hgi : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    have hg : ((gS D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
      show _ ∈ P.asIdeal.comap _
      rw [Ideal.mem_comap, map_natCast]; exact hP
    unfold Lat.gS at hg
    rw [Nat.cast_mul] at hg
    rcases v.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hgi
  have hnd := not_dvd_diff v i hi
  by_contra hc
  push Not at hc
  exact hnd (Ideal.dvd_iff_le.2 fun t ht => hc t ht)

end Formalism.L2.SG.Pf.FibD
end
end

section

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open scoped BigOperators
open Classical

section Abstract

theorem hasSum_of_fiber {P G : Type*} [Finite P] (c : P → ℂ) (cls : P → G) (F : G → ℂ)
    (hF : ∀ g, HasSum (fun x : {x : P // cls x = g} => c x.1) (F g)) {s : ℂ} (hs : HasSum F s) :
    HasSum c s := by
  haveI := Fintype.ofFinite P
  have h1 : HasSum c (∑ x, c x) := hasSum_fintype c
  have h2 := h1.tsum_fiberwise cls
  have e : F = fun g => ∑' x : ↑(cls ⁻¹' {g}), c x := funext fun g => ((hF g).tsum_eq).symm
  have h4 : HasSum F (∑ x, c x) := by
    rw [e]
    exact h2
  rw [hs.unique h4]
  exact h1

variable {ι : Type*} {X : ι → Type*}

def Rst (x0 : ∀ p, X p) : Type _ := {x : ∀ p, X p // {p | x p ≠ x0 p}.Finite}

theorem hasSum_rst (x0 : ∀ p, X p) (f : ∀ p, X p → ℂ) (a : ι → ℂ) (S : Finset ι)
    (hoff : ∀ p ∉ S, ∀ x, f p x = if x = x0 p then 1 else 0)
    (hf : ∀ p ∈ S, HasSum (f p) (a p)) (hn : ∀ p ∈ S, Summable fun x => ‖f p x‖) :
    HasSum (fun x : Rst x0 => ∏ᶠ p, f p (x.1 p)) (∏ p ∈ S, a p) := by
  have h0 := (Formalism.L2.SG.Pf.hasSum_prod_offS x0 f a S hf hn).1
  let j : Formalism.L2.SG.Pf.OffS x0 S → Rst x0 := fun θ =>
    ⟨θ.1, (S.finite_toSet).subset fun p hp => by
      by_contra h
      exact hp (θ.2 p h)⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (congrArg (fun x : Rst x0 => x.1) h)
  have hsupp : ∀ x : Rst x0, (Function.mulSupport fun p => f p (x.1 p)) ⊆ (S : Set ι) ∪ {p | x.1 p ≠ x0 p} := by
    intro x p hp
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
    exact (Function.mem_mulSupport.1 hp) (by rw [hoff p hc.1, if_pos hc.2])
  have hfin : ∀ x : Rst x0, (Function.mulSupport fun p => f p (x.1 p)).Finite := fun x =>
    ((S.finite_toSet).union x.2).subset (hsupp x)
  have hzero : ∀ x ∉ Set.range j, (∏ᶠ p, f p (x.1 p)) = 0 := by
    intro x hx
    have : ∃ p ∉ S, x.1 p ≠ x0 p := by
      by_contra h
      push_neg at h
      exact hx ⟨⟨x.1, h⟩, rfl⟩
    obtain ⟨p, hpS, hp⟩ := this
    exact finprod_eq_zero _ p (by rw [hoff p hpS, if_neg hp]) (hfin x)
  rw [← hj.hasSum_iff hzero]
  convert h0 using 1
  funext θ
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  by_contra hS
  exact (Function.mem_mulSupport.1 hp) (by rw [hoff p hS, if_pos (θ.2 p hS)])

theorem hasSum_passage {P G : Type*} [Finite P] (c : P → ℂ) (cls : P → G) (F : G → ℂ)
    (hF : ∀ g, HasSum (fun x : {x : P // cls x = g} => c x.1) (F g))
    (x0 : ∀ p, X p) (loc : G ≃ Rst x0) (f : ∀ p, X p → ℂ) (a : ι → ℂ) (S : Finset ι)
    (hFp : ∀ g, F g = ∏ᶠ p, f p ((loc g).1 p))
    (hoff : ∀ p ∉ S, ∀ x, f p x = if x = x0 p then 1 else 0)
    (hf : ∀ p ∈ S, HasSum (f p) (a p)) (hn : ∀ p ∈ S, Summable fun x => ‖f p x‖) :
    HasSum c (∏ p ∈ S, a p) := by
  have h1 := hasSum_rst x0 f a S hoff hf hn
  have h2 : HasSum F (∏ p ∈ S, a p) := by
    have e : F = (fun x : Rst x0 => ∏ᶠ p, f p (x.1 p)) ∘ loc := funext fun g => hFp g
    rw [e]
    exact (loc.hasSum_iff).2 h1
  exact hasSum_of_fiber c cls F hF h2

end Abstract

end Formalism.L2.SG.LsDatumB
end
end
