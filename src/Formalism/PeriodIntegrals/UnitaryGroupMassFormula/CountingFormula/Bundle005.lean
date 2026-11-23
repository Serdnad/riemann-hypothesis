module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFC
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fl_inj {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) : Function.Injective (algebraMap F E) := by
  haveI : Nontrivial E := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h1 := L.rank
    have h2 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    omega
  exact (algebraMap F E).injective

theorem fl_norm_ne {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hE : ∀ x : E, x ≠ 0 → IsUnit x)
    {x : E} (hx0 : x ≠ 0) (n : 𝒪[F]) (hn : algebraMap F E n = x * L.cj x) : n ≠ 0 := by
  haveI : Nontrivial E := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h1 := L.rank
    have h2 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    omega
  intro hn0
  rw [hn0] at hn
  have hcj : L.cj x ≠ 0 := fun h => hx0 ((map_eq_zero_iff L.cj L.cj.injective).mp h)
  have hu : IsUnit (x * L.cj x) := (hE x hx0).mul (hE _ hcj)
  apply hu.ne_zero
  rw [← hn]
  simp

theorem fl_fact {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hinj : Function.Injective (algebraMap F E))
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x ∈ L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u := by
  haveI := hl
  have key : ∀ n : 𝒪[F], ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x →
      ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u := by
    intro n
    refine WellFounded.induction (wellFounded_dvdNotUnit (α := 𝒪[F]))
      (C := fun n : 𝒪[F] => ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x →
        ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u) n ?_
    intro n ih x hx hx0 hn
    by_cases hdiv : ∃ z ∈ L.O, x = algebraMap F E ϖ * z
    · obtain ⟨z, hz, rfl⟩ := hdiv
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hx0
      obtain ⟨n', hn'⟩ := fl_norm L hinj hz
      have hcj : L.cj (algebraMap F E ϖ) = algebraMap F E ϖ := L.cj.commutes _
      have heq : n = n' * (ϖ * ϖ) := by
        apply Subtype.ext
        apply hinj
        calc algebraMap F E (n : F) = algebraMap F E ϖ * z * L.cj (algebraMap F E ϖ * z) := hn
          _ = (z * L.cj z) * (algebraMap F E ϖ * algebraMap F E ϖ) := by rw [map_mul, hcj]; ring
          _ = algebraMap F E n' * (algebraMap F E ϖ * algebraMap F E ϖ) := by rw [hn']
          _ = algebraMap F E ((n' * (ϖ * ϖ) : 𝒪[F]) : F) := by
            rw [show ((n' * (ϖ * ϖ) : 𝒪[F]) : F) = (n' : F) * ((ϖ : F) * (ϖ : F)) from rfl, map_mul, map_mul]
      have hdvd : DvdNotUnit n' n := by
        refine ⟨fl_norm_ne L hE hz0 n' hn', ϖ * ϖ, ?_, heq⟩
        rw [IsUnit.mul_iff]
        exact fun h => hϖ.not_isUnit h.1
      obtain ⟨k, u, hu, hw, hzu⟩ := ih n' hdvd z hz hz0 hn'
      exact ⟨k + 1, u, hu, hw, by rw [hzu, pow_succ]; ring⟩
    · obtain ⟨y, hy, hxy⟩ := fl_local L hl hE hinj ϖ hϖ x hx hdiv
      exact ⟨0, x, hx, ⟨y, hy, hxy⟩, by simp⟩
  intro x hx hx0
  obtain ⟨n, hn⟩ := fl_norm L hinj hx
  exact key n x hx hx0 hn

theorem local_density_integral : FLocO := by
  intro F E _ _ _ _ _ _ L hl _ hE ϖ hϖ
  have hinj := fl_inj L
  exact ⟨fl_local L hl hE hinj ϖ hϖ, fl_den L, fl_fact L hl hE hinj ϖ hϖ⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem span_pi_iff (hR : RedData ϖ k r n b Λ) (x : M.L.O) :
    (x : E) ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ r x = 0 := by
  rw [Submodule.mem_span_singleton, hR.ker]
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨o, o.2, by rw [← ho]; show (o : E) * _ = _; ring⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨⟨z, hz⟩, by rw [hzx]; show z * _ = _; ring⟩

theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

def Ph (r : M.L.O →+* k) (H : Loc.HermSp M V) (b : Fin n → V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O) :
    Matrix (Fin n) (Fin n) k := fun i j => r ⟨H.h (b i) (b j), hint i j⟩

theorem gram_mem (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) ∧ H.h x y ∈ M.L.O := by
  have he : H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) := by
    conv_lhs => rw [cO_sum hR hx, cO_sum hR hy]
    exact h_expand H b _ _
  refine ⟨he, ?_⟩
  rw [he]
  exact M.L.O.sum_mem fun i _ => M.L.O.sum_mem fun j _ =>
    M.L.O.mul_mem (M.L.O.mul_mem (cO_mem hR x i) (cj_mem (cO_mem hR y j))) (hint i j)

theorem gram_red (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    r ⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ =
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q := by
  have h1 : (⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ : M.L.O) =
      ∑ i, ∑ j, (⟨cO hR x i, cO_mem hR x i⟩ : M.L.O) * ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ *
        ⟨H.h (b i) (b j), hint i j⟩ := by
    apply Subtype.ext
    show H.h x y = _
    rw [(gram_mem hR H hint hx hy).1]
    push_cast
    rfl

  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, rfrob ⟨cO hR y j, cO_mem hR y j⟩ ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ rfl]
  simp only [red, Ph]
  ring

theorem gram_cond_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V)
    (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (g : E) (hg : g ∈ M.L.O) :
    H.h x y - g ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q = r ⟨g, hg⟩ := by
  have hm := (gram_mem hR H hint hx hy).2
  have := span_pi_iff hR ⟨H.h x y - g, M.L.O.sub_mem hm hg⟩
  simp only at this
  rw [this, show (⟨H.h x y - g, M.L.O.sub_mem hm hg⟩ : M.L.O) = ⟨H.h x y, hm⟩ - ⟨g, hg⟩ from
    Subtype.ext rfl, map_sub, sub_eq_zero, gram_red hR H hint q rfrob hx hy]

end FC

end PI.UnitaryGroupMassFormula.CntFormula
end
end
