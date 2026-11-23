module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle452
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
public import Mathlib.Algebra.Order.Star.Int
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Mathlib.NumberTheory.LocalField.Basic
public import GroundTheory.LocalFields.Uniqueness
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle456
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
public import Mathlib.Order.Extension.Linear
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Mathlib.Topology.Instances.Matrix
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.irreducibleResidualPoint_descends_coefficientExtension : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → (∃ r, GoodR N₀ i₀ r) → ZDecomp N₀ i₀ → Live N₁ i₁ → Live N₀ i₀ := by
  first | exact @GlobalTheory.LiveDescent.live_of_locExt | exact GlobalTheory.LiveDescent.live_of_locExt | (intros; apply GlobalTheory.LiveDescent.live_of_locExt <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isSpherical_factor_of_spherical_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsSubquotient π (prodIrr x hd) → IsSpherical π → ∀ a, IsSpherical (x a).rep := by
  first | exact @GlobalTheory.LocLanglands.SphFac.isSpherical_factor | exact GlobalTheory.LocLanglands.SphFac.isSpherical_factor | (intros; apply GlobalTheory.LocLanglands.SphFac.isSpherical_factor <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory

theorem isL_of_irreducible_prod_unitarisable_nu :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V), σ.IsIrreducible →
    ∀ (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
      IsL ↑(List.ofFn fun j => (Δ j).nu (s j)) σ := by
  intro k _ _ _ _ hprec a V _ _ σ hσ m δ Δ s hL hU hs hd ⟨e⟩
  refine ⟨m, fun j => (δ j).nu (s j), hd, ⟨fun j => (Δ j).nu (s j), ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Fin.univ_val_map _
  · intro i j _ h
    have h1 := hprec (δ i) (δ j) (Δ i) (Δ j) (hL i) (hU i) (hL j) (hU j) (s i) (s j) h
    have hi := abs_lt.1 (hs i)
    have hj := abs_lt.1 (hs j)
    linarith
  · intro j
    exact ((hL j).tw _ (isSmoothChar_absPow _)).of_equiv ((δ j).twEquiv _ _)
  · exact (isCosocle_self hσ).of_equiv (.refl _) e

end GlobalTheory
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.LocGL

theorem IsLSeg.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ : IrrGL (k := k)} {Δ : Segment k} (h : IsLSeg Δ δ.rep) (c : ℂ) : IsLSeg (Δ.nu c) (δ.nu c).rep :=
  (h.tw (absPow k c) (isSmoothChar_absPow c)).of_equiv (δ.twEquiv _ _)

theorem IsSpeh.nu_rep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {δ x : IrrGL (k := k)} {m : ℕ} (h : IsSpeh δ m x.rep) (s : ℂ) : IsSpeh (δ.nu s) m (x.nu s).rep := by
  obtain ⟨hd, h'⟩ := h.tw (absPow k s) (isSmoothChar_absPow s)
  exact ⟨hd, h'.of_equiv (x.twEquiv _ _) (.refl _)⟩

theorem isL_speh_nu (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hP : ∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) :
    ∀ (δ x : IrrGL (k := k)) (Δ : Segment k) (m : ℕ), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsSpeh δ m x.rep →
      ∀ s : ℝ, IsL ↑(List.ofFn fun i : Fin m => Δ.nu ((s + ((m : ℝ) - 1) / 2 - (i : ℕ) : ℝ) : ℂ)) (x.nu (s : ℂ)).rep := by
  intro δ x Δ m hL hU hS s
  obtain ⟨hd, hc⟩ := hS.nu_rep (s : ℂ)
  set c : Fin m → ℝ := fun i => s + ((m : ℝ) - 1) / 2 - (i : ℕ) with hcdef
  have hy : ∀ i, spehFactor (δ.nu s) m i = δ.nu (c i : ℂ) := fun i => by
    simp only [spehFactor, IrrGL.nu_nu, hcdef]
    congr 1
    push_cast
    ring
  refine ⟨m, spehFactor (δ.nu s) m, hd, ⟨fun i => Δ.nu (c i : ℂ), ⟨?_, ?_⟩, ?_⟩, hc⟩
  · rw [Fin.univ_val_map]
  · intro i j hij hp
    have h1 := hP δ δ Δ Δ hL hU hL hU (c i) (c j) hp
    have h2 : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij
    simp only [hcdef] at h1
    linarith
  · intro i
    rw [hy i]
    exact hL.nu_rep _

end GlobalTheory.LocGL
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem _root_.GlobalTheory.T.nonempty_equiv_prodChosenIrrGL_pair_degreeZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x z : IrrGL (k := k)) (hz : z.1 = 0) (hd : ∑ a, (![x, z] a).1 = x.1), Nonempty (x.rep.Equiv (prodIrr ![x, z] hd)) := by
  first | exact @GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero | exact GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero | (intros; apply GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ρ : IrrGL (k := k)} {hρ : ρ.IsCusp} {c d c' d' : ℤ} {h : c ≤ d} {h' : c' ≤ d'} {Δ Δ' : Segment k}

theorem first_mem_carrier (Δ : Segment k) : Δ.first ∈ Δ.carrier := mem_carrier.2 ⟨0, Δ.len_pos, by simp⟩

theorem nu_mem_icc {a : ℤ} : ρ.nu a ∈ (icc ρ hρ c d h).carrier ↔ c ≤ a ∧ a ≤ d := by
  simp only [mem_icc, IrrGL.nu_intCast_inj hρ.1]
  exact ⟨fun ⟨_, h1, h2, e⟩ => e ▸ ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨a, h1, h2, rfl⟩⟩

theorem eq_icc_of_first_eq (hρ : ρ.IsCusp) (e : Δ.first = ρ.nu c) :
    Δ = icc ρ hρ c (c + Δ.len - 1) (Int.le_sub_one_of_lt (lt_add_of_pos_right c (Nat.cast_pos.2 Δ.len_pos))) :=
  ext_first e (by simp only [icc, len_ofFirst]; omega)

theorem exists_eq_icc_of_mem (hρ : ρ.IsCusp) {a : ℤ} (ha : ρ.nu a ∈ Δ.carrier) :
    ∃ (c d : ℤ) (h : c ≤ d), Δ = icc ρ hρ c d h := by
  obtain ⟨b, -, hb⟩ := mem_carrier.1 ha
  refine ⟨a - b, _, _, eq_icc_of_first_eq hρ ?_⟩
  have := congrArg (fun x => IrrGL.nu x (-(b : ℂ))) hb
  simpa [sub_eq_add_neg] using this

theorem icc_subset_icc : (icc ρ hρ c d h).carrier ⊆ (icc ρ hρ c' d' h').carrier ↔ c' ≤ c ∧ d ≤ d' := by
  refine ⟨fun H => ⟨(nu_mem_icc.1 (H (nu_mem_icc.2 ⟨le_rfl, h⟩))).1, (nu_mem_icc.1 (H (nu_mem_icc.2 ⟨h, le_rfl⟩))).2⟩,
    fun ⟨h1, h2⟩ x hx => ?_⟩
  obtain ⟨a, h3, h4, rfl⟩ := mem_icc.1 hx
  exact nu_mem_icc.2 ⟨h1.trans h3, h4.trans h2⟩

theorem exists_carrier_eq_union_icc :
    (∃ Γ : Segment k, Γ.carrier = (icc ρ hρ c d h).carrier ∪ (icc ρ hρ c' d' h').carrier) ↔
      c' ≤ d + 1 ∧ c ≤ d' + 1 := by
  constructor
  · rintro ⟨Γ, hΓ⟩
    obtain ⟨e, f, hef, rfl⟩ := exists_eq_icc_of_mem (Δ := Γ) hρ (a := c)
      (by rw [hΓ]; exact Or.inl (nu_mem_icc.2 ⟨le_rfl, h⟩))
    have key : ∀ a : ℤ, (e ≤ a ∧ a ≤ f) ↔ (c ≤ a ∧ a ≤ d) ∨ (c' ≤ a ∧ a ≤ d') := fun a => by
      simpa only [Set.mem_union, nu_mem_icc] using Set.ext_iff.1 hΓ (ρ.nu a)
    have := key c; have := key d'; have := key c'; have := key d; have := key (d + 1); have := key (d' + 1)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨icc ρ hρ (min c c') (max d d') (by omega), Set.ext fun x => ?_⟩
    simp only [Set.mem_union, mem_icc]
    constructor
    · rintro ⟨a, h3, h4, rfl⟩
      by_cases ha : c ≤ a ∧ a ≤ d
      · exact Or.inl ⟨a, ha.1, ha.2, rfl⟩
      · exact Or.inr ⟨a, by omega, by omega, rfl⟩
    · rintro (⟨a, h3, h4, rfl⟩ | ⟨a, h3, h4, rfl⟩) <;> exact ⟨a, by omega, by omega, rfl⟩

theorem linked_icc : (icc ρ hρ c d h).Linked (icc ρ hρ c' d' h') ↔
    (c < c' ∧ c' ≤ d + 1 ∧ d < d') ∨ (c' < c ∧ c ≤ d' + 1 ∧ d' < d) := by
  rw [Linked, exists_carrier_eq_union_icc, icc_subset_icc, icc_subset_icc]
  omega

theorem precedes_icc : (icc ρ hρ c d h).Precedes (icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d' := by
  have key : (∃ j : ℕ, 0 < j ∧ (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j) ↔ c < c' := by
    have e : ∀ j : ℕ, (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j ↔ c' = c + j := fun j => by
      rw [← IrrGL.nu_intCast_inj hρ.1]
      simp [icc]
    simp only [e]
    exact ⟨fun ⟨j, h1, h2⟩ => by omega, fun H => ⟨(c' - c).toNat, by omega, by omega⟩⟩
  rw [Precedes, linked_icc, key]
  omega

theorem Linked.exists_eq_icc (H : Linked Δ Δ') : ∃ (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
    Δ = icc ρ hρ c d h ∧ Δ' = icc ρ hρ c' d' h' := by
  obtain ⟨⟨Γ, hΓ⟩, -⟩ := H
  have key : ∀ D : Segment k, D.carrier ⊆ Γ.carrier → ∃ (c d : ℤ) (h : c ≤ d), D = icc Γ.first Γ.isCusp_first c d h :=
    fun D hD => by
      obtain ⟨a, -, ha⟩ := mem_carrier.1 (hD D.first_mem_carrier)
      exact ⟨a, _, _, eq_icc_of_first_eq _ (by simpa using ha.symm)⟩
  obtain ⟨c, d, h, e⟩ := key Δ (hΓ ▸ Set.subset_union_left)
  obtain ⟨c', d', h', e'⟩ := key Δ' (hΓ ▸ Set.subset_union_right)
  exact ⟨_, _, c, d, c', d', h, h', e, e'⟩

theorem linked_iff_precedes : Linked Δ Δ' ↔ Precedes Δ Δ' ∨ Precedes Δ' Δ := by
  refine ⟨fun H => ?_, fun H => H.elim (·.1) (·.1.symm)⟩
  obtain ⟨ρ, hρ, c, d, c', d', h, h', rfl, rfl⟩ := H.exists_eq_icc
  simpa only [precedes_icc] using linked_icc.1 H

theorem precedes_iff : Precedes Δ Δ' ↔
    ∃ j : ℕ, 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len ∧ Δ'.first = Δ.first.nu j := by
  have key : ∀ j : ℕ, Δ'.first = Δ.first.nu j → (Precedes Δ Δ' ↔ 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len) := fun j e => by
    have e1 := eq_icc_of_first_eq (Δ := Δ) (c := 0) Δ.isCusp_first (by simp)
    have e2 := eq_icc_of_first_eq (Δ := Δ') (c := j) Δ.isCusp_first (by simpa using e)
    refine (iff_of_eq (congrArg₂ Precedes e1 e2)).trans (precedes_icc.trans ?_)
    omega
  refine ⟨fun H => ?_, fun ⟨j, h1, h2, h3, e⟩ => (key j e).2 ⟨h1, h2, h3⟩⟩
  obtain ⟨j, -, e⟩ := H.2
  obtain ⟨h1, h2, h3⟩ := (key j e).1 H
  exact ⟨j, h1, h2, h3, e⟩

theorem exists_first_eq_of_transGen (H : Relation.TransGen Precedes Δ Δ') :
    ∃ j : ℕ, 0 < j ∧ Δ'.first = Δ.first.nu j := by
  induction H with
  | single H => exact H.2
  | tail _ H ih =>
    obtain ⟨i, hi, e⟩ := ih
    obtain ⟨j, -, e'⟩ := H.2
    exact ⟨i + j, by omega, by rw [e', e, IrrGL.nu_nu, Nat.cast_add]⟩

theorem not_transGen_precedes_self (Δ : Segment k) : ¬ Relation.TransGen Precedes Δ Δ := fun H => by
  obtain ⟨j, hj, e⟩ := exists_first_eq_of_transGen H
  exact hj.ne ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by simpa using e))

theorem Precedes.asymm (H : Precedes Δ Δ') : ¬ Precedes Δ' Δ := fun H' =>
  not_transGen_precedes_self Δ ((Relation.TransGen.single H).tail H')

theorem lt_of_precedes_nu {x y : ℝ} (H : (Δ.nu x).Precedes (Δ.nu y)) : x < y := by
  obtain ⟨-, j, hj, e⟩ := H
  have e' : Δ.first.nu y = Δ.first.nu ((x + j : ℝ) : ℂ) := by
    push_cast
    exact e.trans (Δ.first.nu_nu x j)
  have : (0 : ℝ) < j := Nat.cast_pos.2 hj
  rw [(IrrGL.nu_ofReal_inj Δ.isCusp_first.1).1 e']
  linarith

theorem not_precedes_nu (Δ : Segment k) {x y : ℝ} (hxy : y < x) : ¬ (Δ.nu x).Precedes (Δ.nu y) := fun H =>
  hxy.asymm (lt_of_precedes_nu H)

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

theorem exists_list_pairwise_not_rel {α : Type*} {r : α → α → Prop} (hr : ∀ a, ¬ Relation.TransGen r a a)
    (m : Multiset α) : ∃ l : List α, (l : Multiset α) = m ∧ l.Pairwise fun a b => ¬ r a b := by
  classical
  let p : α → α → Prop := fun a b => Relation.ReflTransGen r b a
  haveI : IsPartialOrder α p :=
    { refl := fun _ => .refl
      trans := fun _ _ _ h h' => h'.trans h
      antisymm := fun a b h h' => by
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h
        · exact e
        · exact absurd (h.trans_left h') (hr _) }
  obtain ⟨s, hs, hps⟩ := extend_partialOrder p
  refine ⟨m.sort s, m.sort_eq s, (m.pairwise_sort s).imp fun {a b} hab h => ?_⟩
  obtain rfl : a = b := antisymm hab (hps _ _ (.single h))
  exact hr a (.single h)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isOrderedForm (𝔪 : Multiset (Segment k)) :
    ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪 := by
  obtain ⟨l, rfl, hl⟩ := exists_list_pairwise_not_rel Segment.not_transGen_precedes_self 𝔪
  exact ⟨l.get, (Fin.univ_val_map l.get).trans (congrArg _ (List.ofFn_get l)), List.pairwise_iff_get.1 hl⟩

theorem isOrderedForm_tw_iff {h : ℕ} {Δ : Fin h → Segment k} {𝔪 : Multiset (Segment k)} (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪 :=
  ⟨fun H => by simpa only [Multiset.map_map, Function.comp_def, Segment.tw_tw_inv, Multiset.map_id'] using H.tw χ⁻¹ hχ.inv,
    fun H => H.tw χ hχ⟩

theorem precedes_and_orderedForms (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    ((∀ Δ Δ' : Segment k, Δ.Precedes Δ' → ¬ Δ'.Precedes Δ) ∧
      (∀ Δ : Segment k, ¬ Relation.TransGen Segment.Precedes Δ Δ) ∧
      ∀ 𝔪 : Multiset (Segment k), ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪) ∧
    ((∀ (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
        (Segment.icc ρ hρ c d h).Precedes (Segment.icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d') ∧
      ∀ Δ Δ' : Segment k, Δ.Linked Δ' ↔ Δ.Precedes Δ' ∨ Δ'.Precedes Δ) ∧
    (∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Linked (Δ'.tw χ hχ) ↔ Δ.Linked Δ') ∧
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Precedes (Δ'.tw χ hχ) ↔ Δ.Precedes Δ') ∧
      ∀ (h : ℕ) (Δ : Fin h → Segment k) (𝔪 : Multiset (Segment k)),
        IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪) ∧
    ∀ (Δ : Segment k) (x y : ℝ), y < x → ¬ (Δ.nu x).Precedes (Δ.nu y) :=
  ⟨⟨fun _ _ => Segment.Precedes.asymm, Segment.not_transGen_precedes_self, exists_isOrderedForm⟩,
    ⟨fun _ _ _ _ _ _ _ _ => Segment.precedes_icc, fun _ _ => Segment.linked_iff_precedes⟩,
    fun χ hχ => ⟨fun _ _ => Segment.linked_tw_iff χ hχ, fun _ _ => Segment.precedes_tw_iff χ hχ,
      fun _ _ _ => isOrderedForm_tw_iff χ hχ⟩,
    fun Δ _ _ h => Δ.not_precedes_nu h⟩

end GlobalTheory.LocGL
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.localCountDualLifting_proof : StepLocDual := by
  first | exact @GlobalTheory.Pass.LocDual.main | exact GlobalTheory.Pass.LocDual.main | (intros; apply GlobalTheory.Pass.LocDual.main <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LBC
open scoped Topology

namespace GlobalTheory.LBC.Inh
open ValuativeRel Filter

section Cont
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']

theorem isOpen_lt_one (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsOpen {x : F | valuation F x < 1} := by
  refine isOpen_iff_mem_nhds.2 fun x hx => (IsValuativeTopology.mem_nhds_iff').2 ⟨1, fun z hz => ?_⟩
  have e : z = (z - x) + x := by ring
  show valuation F z < 1
  rw [e]
  have hz' : valuation F (z - x) < 1 := by simpa using hz
  exact (valuation F).map_add_lt hz' hx

theorem lt_one_of_lt_one (hc : Continuous (algebraMap k k')) {z : k} (h : valuation k z < 1) :
    valuation k' (algebraMap k k' z) < 1 := by
  have h1 := (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff z).2 h
  have h2 := (hc.tendsto 0).comp h1
  rw [map_zero] at h2
  apply (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).1
  refine h2.congr fun n => ?_
  simp [Function.comp_apply, map_pow]

theorem lt_one_iff (hc : Continuous (algebraMap k k')) (z : k) :
    valuation k' (algebraMap k k' z) < 1 ↔ valuation k z < 1 := by
  refine ⟨fun h => ?_, lt_one_of_lt_one hc⟩
  by_contra hz
  push_neg at hz
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz
  rcases hz.lt_or_eq with hlt | heq
  · have h2 : valuation k z⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
    have h3 := lt_one_of_lt_one (k' := k') hc h2
    have h4 : valuation k' (algebraMap k k' z) * valuation k' (algebraMap k k' z⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hz0, map_one, map_one]
    have := lt_of_le_of_lt (mul_le_of_le_one_left' h.le) h3
    rw [h4] at this
    exact lt_irrefl _ this
  · set S : Set k := {x | valuation k x ≤ 1} ∩ {x | valuation k x < 1}ᶜ with hS
    have hSc : IsCompact S :=
      (IsNonarchimedeanLocalField.isCompact_closedBall k 1).inter_right (isOpen_lt_one k).isClosed_compl
    haveI : T2Space k' := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k'
    have hI : IsClosed (algebraMap k k' '' S) := (hSc.image hc).isClosed
    have h0 : (0 : k') ∉ algebraMap k k' '' S := by
      rintro ⟨x, hx, hx0⟩
      rw [map_eq_zero_iff _ (algebraMap k k').injective] at hx0
      subst hx0
      simp [hS] at hx
    have ht := (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).2 h
    obtain ⟨n, hn⟩ := (ht.eventually (hI.isOpen_compl.mem_nhds h0)).exists
    apply hn
    refine ⟨z ^ n, ?_, by rw [map_pow]⟩
    simp [hS, map_pow, ← heq]

theorem valuativeExtension (hc : Continuous (algebraMap k k')) : ValuativeExtension k k' :=
  ⟨fun {a b} => GroundTheory.LocalField.vle_map_iff_of_valuation_lt_one_iff
    (algebraMap k k') (lt_one_iff hc) a b⟩

theorem continuous_algNorm [FiniteDimensional k k'] (hc : Continuous (algebraMap k k')) :
    Continuous (Algebra.norm k : k' → k) := by
  classical
  haveI := valuativeExtension hc
  haveI := GroundTheory.LocalField.isModuleTopology k k'
  let b := Module.finBasis k k'
  have h : (Algebra.norm k : k' → k) = fun t => (Algebra.leftMulMatrix b t).det := by
    funext t; exact Algebra.norm_eq_matrix_det b t
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun t : k' => Algebra.leftMulMatrix b t i j) =
      fun t => (b.coord i) (LinearMap.mulRight k (b j) t) := by
    funext t; simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight k (b j)))

theorem isSmoothChar_comp_norm [FiniteDimensional k k'] (hc : Continuous (algebraMap k k')) {χ : kˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) : IsSmoothChar (χ.comp (Units.map (Algebra.norm k : k' →* k))) :=
  hχ.comp _ (Continuous.units_map _ (continuous_algNorm hc))

end Cont

end GlobalTheory.LBC.Inh
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.ocTensorCoeffBasisCoords_mem_cyclotomicLevel_of_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n] (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l), (∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a) → φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ‖(c : PadicComplex l)‖ < 1 → (c : PadicComplex l) ∈ inC (Ks K m) → (∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) → ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  first | exact @GlobalTheory.Cyc.Decomp.Coord.coord | exact GlobalTheory.Cyc.Decomp.Coord.coord | (intros; apply GlobalTheory.Cyc.Decomp.Coord.coord <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL) {d e : ℕ} (b : LatB T d) (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) (y : TW (RW LL) T), letI := twTop T b; letI := aTop (K := K) bO; Continuous fun a : AA K LL => inclR LL (E.tie.io a) • y := by
  first | exact @GlobalTheory.WeakClosed.continuous_inclR_io_smul | exact GlobalTheory.WeakClosed.continuous_inclR_io_smul | (intros; apply GlobalTheory.WeakClosed.continuous_inclR_io_smul <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_dual_selmer_class_not_killed : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (β : Y →+ A →+ ZMod (X.l i ^ (nu X i + 1))), Perf A β → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (c t : A) (y₀ : Fin a → A) (j : Fin a), (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ A g m = m) → t • m = 0) → Matrix.vecMul y₀ Φ = 0 → c * t * y₀ j ≠ 0 → ∃ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y ∧ ¬ Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) := by
  first | exact @GlobalTheory.NewPrime.DualClass.exists_not_cob | exact GlobalTheory.NewPrime.DualClass.exists_not_cob | (intros; apply GlobalTheory.NewPrime.DualClass.exists_not_cob <;> assumption)
end
