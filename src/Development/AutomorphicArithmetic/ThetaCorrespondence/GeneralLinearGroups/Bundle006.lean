module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsJacQuot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocL
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsNeOfNeBot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocR
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle067
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ind₂_equiv_pair (y z : IrrGL (k := k)) {N : ℕ} (h : y.1 + z.1 = N) (hd : ∑ a, (![y, z] a).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor y.rep z.rep)).Equiv (prodIrr ![y, z] hd)) := by
  subst h
  exact nonempty_prod₂_equiv_prodIrr_pair y z hd

private theorem emb_unit (x : IrrGL (k := k)) : ∃ y : IrrGL (k := k), y.1 = 0 ∧ Emb x y x := by
  let o : IrrRep (GL (Fin 0) k) := IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one
  let y : IrrGL (k := k) := IrrGL.of o.ρ o.smooth o.irr
  have φ : o.ρ.Equiv y.rep := IrrGL.equivOf o.ρ o.smooth o.irr
  have κ : y.2.rep.V ≃ₗ[ℂ] ℂ := φ.toLinearEquiv.symm
  have h : 0 + x.1 = x.1 := Nat.zero_add _
  have hd : ∑ a, (![y, x] a).1 = x.1 := (Fin.sum_univ_two _).trans h
  obtain ⟨a⟩ := GlobalTheory.ProdReorder.ind₂_line_left h y.rep κ x.rep x.2.rep.smooth
  obtain ⟨b⟩ := ind₂_equiv_pair y x h hd
  exact ⟨y, rfl, hd, (a.symm.trans b).toIntertwiningMap, (a.symm.trans b).toLinearEquiv.injective⟩

private theorem emb_deg {x y z : IrrGL (k := k)} (h : Emb x y z) : y.1 + z.1 = x.1 := by
  obtain ⟨hd, -⟩ := h
  exact (Fin.sum_univ_two _).symm.trans hd

private theorem suppIn_occ {v y ρ : IrrGL (k := k)} {P : Set (IrrGL (k := k))} (h : Occ v y ρ) (hy : SuppIn y P)
    (hρ : ρ.IsCusp) (hP : ρ ∈ P) : SuppIn v P := by
  obtain ⟨hd, hne⟩ := h
  obtain ⟨A, hA, hAP⟩ := hy
  have hS := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![y, ρ]) (hd := hd) (t := ![A, {ρ}])
    (fun a => by
      fin_cases a
      · exact hA
      · exact hasSupport_self hρ) v.2.rep.irr (jhMult_ne_zero_iff.1 hne)
  refine ⟨_, hS, fun w hw => ?_⟩
  rw [Fin.sum_univ_two] at hw
  rcases Multiset.mem_add.1 hw with h | h
  · exact hAP w h
  · have : w = ρ := Multiset.mem_singleton.1 h
    exact this ▸ hP

end

theorem UpperTheory.Lit.Full.decompL :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))), ∃ y z, Emb x y z ∧ SuppIn y P ∧ FirstIn z Pᶜ := by
  intro hG hBZ k _ _ _ _ x P
  have key : ∀ (n : ℕ) (y z : IrrGL (k := k)), z.1 = n → Emb x y z → SuppIn y P →
      ∃ y z, Emb x y z ∧ SuppIn y P ∧ FirstIn z Pᶜ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y z hz hE hS
      by_cases hF : FirstIn z Pᶜ
      · exact ⟨y, z, hE, hS, hF⟩
      unfold FirstIn at hF
      push Not at hF
      obtain ⟨q, hq, hc, hj, hP⟩ := hF
      have hP' : q 0 ∈ P := by simpa using hP
      obtain ⟨w, hw⟩ := UpperTheory.Lit.Full.embL hG hBZ k z q hq hc hj
      obtain ⟨v, hv, hvw⟩ := UpperTheory.Lit.Full.assocL hG hBZ k x y z (q 0) w hE hw
      have h1 := emb_deg hw
      have h2 := hc.1
      exact ih w.1 (by omega) v w rfl hvw (suppIn_occ hv hS hc hP')
  obtain ⟨y, hy, hE⟩ := emb_unit x
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG y
  refine key _ y x rfl hE ⟨s, hs, ?_⟩
  rw [GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport hy hs]
  simp
end

section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

theorem UpperTheory.Lit.Full.decompR :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))), ∃ y z, Emb x y z ∧ LastIn y Pᶜ ∧ SuppIn z P := by
  intro hG hBZ k _ _ _ _ x P
  have key : ∀ (n : ℕ) (y z : IrrGL (k := k)), y.1 = n → Emb x y z → SuppIn z P →
      ∃ y z, Emb x y z ∧ LastIn y Pᶜ ∧ SuppIn z P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro y z rfl hxyz hz
      by_cases hl : LastIn y Pᶜ
      · exact ⟨y, z, hxyz, hl, hz⟩
      obtain ⟨q, hq, hc, hj, hP⟩ : ∃ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = y.1),
          (q 1).IsCusp ∧ jm q hq y.rep ≠ 0 ∧ q 1 ∈ P := by
        by_contra hn
        exact hl fun q hq hc hj hP => hn ⟨q, hq, hc, hj, hP⟩
      obtain ⟨u, hu⟩ := UpperTheory.Lit.Full.embR hG hBZ k y q hq hc hj
      obtain ⟨v, ⟨hd, hv⟩, hxuv⟩ := UpperTheory.Lit.Full.assocR hG hBZ k x y z u (q 1) hxyz hu
      obtain ⟨A, hA, hAP⟩ := hz
      have hlt : u.1 < y.1 := by
        obtain ⟨hd', -⟩ := hu
        have h1 : u.1 + (q 1).1 = y.1 := by simpa using hd'
        have := hc.1
        omega
      refine ih u.1 hlt u v rfl hxuv ⟨∑ a, (![{q 1}, A] : Fin 2 → Multiset (IrrGL (k := k))) a, ?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![q 1, z]) ?_ v.2.rep.irr
          (jhMult_ne_zero_iff.1 hv)
        exact Fin.forall_fin_two.2 ⟨hasSupport_self hc, hA⟩
      · intro w hw
        have hw' : w ∈ ({q 1} : Multiset (IrrGL (k := k))) + A := by simpa using hw
        rcases Multiset.mem_add.1 hw' with h | h
        · rw [Multiset.mem_singleton.1 h]; exact hP
        · exact hAP w h
  let o : IrrGL (k := k) := ⟨0, (IrrRep.det (Fin 0) (1 : kˣ →* ℂˣ) isSmoothChar_one).cl⟩
  have hd : ∑ a, (![x, o] a).1 = x.1 := by simp [o]
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_pair_zero k x o rfl hd
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG o
  refine key x.1 x o rfl ⟨hd, φ.toIntertwiningMap, φ.toLinearEquiv.injective⟩ ⟨s, hs, ?_⟩
  rw [GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport (N := o.1) rfl hs]
  simp
end
