module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem eq_of_regAt_eq_of_coordTie :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω),
      CoordTie o ξ x → ∀ p q : Cpt ξ, regAt ξ p = regAt ξ q → p = q := by
  intro X Ω _ ξ o _ _ κ x h p q e
  obtain ⟨c, hc⟩ := h.cover p
  have hq : InChart ξ x c q := ⟨hc.1, fun c' => e ▸ hc.2 c'⟩
  haveI hloc : IsLocalRing (regAt ξ p) :=
    (regAt_isLocalRing_isFractionRing_stalk X Ω ξ h.gen p).1
  have hmem : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c), (s : Ω) ∈ regAt ξ p :=
    fun s => (h.ring c hc.1 s).1 s.2 p hc
  let f : Algebra.adjoin o (Set.range fun j => x j / x c) →+* regAt ξ p :=
    ((Algebra.adjoin o (Set.range fun j => x j / x c)).val :
      Algebra.adjoin o (Set.range fun j => x j / x c) →+* Ω).codRestrict (regAt ξ p) hmem
  have hI : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hp' : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hq' : ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ q (s : Ω) := by
    intro s
    rw [hp' s]
    simp only [unitAt, e]
  exact (GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ o κ x h c hc.1 _ hI).unique ⟨hc, hp'⟩ ⟨hq, hq'⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_inChart_of_comp_eq :
    ∀ (W P : Scheme.{0}) (Ω : Type) [Field Ω] (ξ' : Sp Ω ⟶ W) (ξ₀ : Sp Ω ⟶ P) (g : W ⟶ P) (o : Type) [CommRing o]
      [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → ξ' ≫ g = ξ₀ → ∀ p' : Cpt ξ', ∃ c, InChart ξ' u c p' := by
  intro W P Ω _ ξ' ξ₀ g o _ _ κ u h he p'
  have hd : Dominates ξ' ξ₀ g (RingHom.id Ω) := by
    have e : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 (Spec (CommRingCat.of Ω)) := by
      exact Spec.map_id _
    show ξ' ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ₀
    rw [e, Category.id_comp]
    exact he
  obtain ⟨hs, hreg, -⟩ := RegAtDom.regAt_dominates P Ω ξ₀ W Ω ξ' g (RingHom.id Ω) hd p'
  obtain ⟨c, hc, hr⟩ := h.cover ⟨g p'.1, hs⟩
  exact ⟨c, hc, fun c' => hreg _ (hr c')⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_prime_nonunitAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hg : IsCptGen ξ) (p : Cpt ξ) {o : Type} [CommRing o] [Algebra o Ω] (A : Subalgebra o Ω)
    (hA : ∀ s ∈ A, s ∈ regAt ξ p) :
    ∃ I : Ideal A, I.IsPrime ∧ ∀ s : A, s ∉ I ↔ unitAt ξ p (s : Ω) := by
  haveI : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).1
  let φ : A →+* regAt ξ p := RingHom.codRestrict A.val.toRingHom (regAt ξ p) (fun s => hA s s.2)
  refine ⟨Ideal.comap φ (IsLocalRing.maximalIdeal _), inferInstance, fun s => ?_⟩
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h.exists_right_inv
    have e : (s : Ω) * (t : Ω) = 1 := congrArg Subtype.val ht
    refine ⟨left_ne_zero_of_mul_eq_one e, hA s s.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right e]
    exact t.2
  · rintro ⟨h0, -, h2⟩
    refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, h2⟩ : regAt ξ p) (Subtype.ext ?_)
    exact mul_inv_cancel₀ h0

theorem unitAt_of_le {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (p : Cpt ξ) (p' : Cpt ξ') (h : regAt ξ p ≤ regAt ξ' p') {a : Ω}
    (ha : unitAt ξ p a) : unitAt ξ' p' a :=
  ⟨ha.1, h ha.2.1, h ha.2.2⟩

theorem image_eq_of_regAt_eq :
    ∀ (P X₁ X₂ : Scheme.{0}) (Ω : Type) [Field Ω] (ξ₀ : Sp Ω ⟶ P) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (f₁ : X₁ ⟶ P)
      (f₂ : X₂ ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → IsCptGen ξ₁ →
      IsCptGen ξ₂ → ξ₁ ≫ f₁ = ξ₀ → ξ₂ ≫ f₂ = ξ₀ → ∀ (p₁ : Cpt ξ₁) (p₂ : Cpt ξ₂), regAt ξ₁ p₁ = regAt ξ₂ p₂ →
      f₁ p₁.1 = f₂ p₂.1 := by
  intro P X₁ X₂ Ω _ ξ₀ ξ₁ ξ₂ f₁ f₂ o _ _ κ u hu g₁ g₂ e₁ e₂ p₁ p₂ hR
  have dom : ∀ {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ P), ξ ≫ f = ξ₀ →
      Dominates ξ ξ₀ f (RingHom.id Ω) := by
    intro X ξ f e
    have : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _ := by
      rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id]
    show ξ ≫ f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ₀
    rw [this, Category.id_comp, e]
  obtain ⟨h₁, r₁, n₁⟩ := RegAtDom.regAt_dominates P Ω ξ₀ X₁ Ω ξ₁ f₁ (RingHom.id Ω) (dom ξ₁ f₁ e₁) p₁
  obtain ⟨h₂, r₂, n₂⟩ := RegAtDom.regAt_dominates P Ω ξ₀ X₂ Ω ξ₂ f₂ (RingHom.id Ω) (dom ξ₂ f₂ e₂) p₂
  set a₁ : Cpt ξ₀ := ⟨f₁ p₁.1, h₁⟩ with ha₁
  set a₂ : Cpt ξ₀ := ⟨f₂ p₂.1, h₂⟩ with ha₂
  have l₁ : regAt ξ₀ a₁ ≤ regAt ξ₁ p₁ := fun a ha => r₁ a ha
  have l₂ : regAt ξ₀ a₂ ≤ regAt ξ₁ p₁ := fun a ha => hR ▸ r₂ a ha
  have m₁ : ∀ a ∈ regAt ξ₀ a₁, unitAt ξ₁ p₁ a → unitAt ξ₀ a₁ a := n₁ g₁
  have m₂ : ∀ a ∈ regAt ξ₀ a₂, unitAt ξ₁ p₁ a → unitAt ξ₀ a₂ a := fun a ha h =>
    n₂ g₂ a ha ⟨h.1, hR ▸ h.2.1, hR ▸ h.2.2⟩
  obtain ⟨c₁, hc₁⟩ := hu.cover a₁
  obtain ⟨c, hc⟩ := hu.cover a₂

  have hq : unitAt ξ₀ a₁ (u c / u c₁) := by
    refine m₁ _ (hc₁.2 c) ⟨div_ne_zero hc.1 hc₁.1, l₁ (hc₁.2 c), ?_⟩
    rw [inv_div]
    exact l₂ (hc.2 c₁)
  have hin : InChart ξ₀ u c a₁ := by
    refine ⟨hc.1, fun j => ?_⟩
    have : u j / u c = u j / u c₁ * (u c / u c₁)⁻¹ := by
      have := hc₁.1
      have := hc.1
      field_simp
    rw [this]
    exact mul_mem (hc₁.2 j) hq.2.2
  set A := Algebra.adjoin o (Set.range fun j => u j / u c) with hA
  have A₁ : ∀ s ∈ A, s ∈ regAt ξ₀ a₁ := fun s hs => (hu.ring c hc.1 s).1 hs a₁ hin
  have A₂ : ∀ s ∈ A, s ∈ regAt ξ₀ a₂ := fun s hs => (hu.ring c hc.1 s).1 hs a₂ hc
  obtain ⟨I, hI, hI₁⟩ := exists_prime_nonunitAt ξ₀ hu.gen a₁ A A₁
  have hI₂ : ∀ s : A, s ∉ I ↔ unitAt ξ₀ a₂ (s : Ω) := fun s => by
    rw [hI₁ s]
    exact ⟨fun h => m₂ _ (A₂ s s.2) (unitAt_of_le ξ₀ ξ₁ a₁ p₁ l₁ h),
      fun h => m₁ _ (A₁ s s.2) (unitAt_of_le ξ₀ ξ₁ a₂ p₁ l₂ h)⟩
  have e := (GlobalTheory.T.prime_chart_existsUnique_point P Ω ξ₀ o κ u hu c hc.1 I hI).unique ⟨hin, hI₁⟩ ⟨hc, hI₂⟩
  exact congrArg Subtype.val e

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem length_localizedModule_quot_eq {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R}
    (h₁ : ∀ x ∈ J₁, ∃ s, s ∉ W ∧ s * x ∈ J₂) (h₂ : ∀ x ∈ J₂, ∃ s, s ∉ W ∧ s * x ∈ J₁) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₁)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₂)) := by
  have key : ∀ {A B : Ideal R}, (∀ x ∈ A, ∃ s, s ∉ W ∧ s * x ∈ B) →
      Submodule.localized W.primeCompl (M := R) A ≤ Submodule.localized W.primeCompl (M := R) B := by
    intro A B h y hy
    obtain ⟨m, hm, s, rfl⟩ := hy
    obtain ⟨t, ht, htm⟩ := h m hm
    refine ⟨t * m, htm, ⟨t, ht⟩ * s, ?_⟩
    exact IsLocalizedModule.mk'_cancel_left _ _ _ _
  have heq : Submodule.localized W.primeCompl (M := R) J₁ = Submodule.localized W.primeCompl (M := R) J₂ :=
    le_antisymm (key h₁) (key h₂)
  have e₁ := (localizedQuotientEquiv W.primeCompl (M := R) J₁).length_eq
  have e₂ := (localizedQuotientEquiv W.primeCompl (M := R) J₂).length_eq
  have e₃ := (Submodule.quotEquivOfEq _ _ heq).length_eq
  exact e₁.symm.trans (e₃.trans e₂)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem IsUnitSec.symm {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) : IsUnitSec P g f := by
  intro W hW hP hR
  obtain ⟨u, v, hu, hv, hm⟩ := h W hW hP hR
  refine ⟨v, u, hv, hu, ?_⟩
  have := P.neg_mem hm
  rwa [neg_sub] at this

theorem divSupp_subset_of_isUnitSec {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) :
    divSupp P f ⊆ divSupp P g := by
  rintro W ⟨hmin, hrel⟩
  have hWp : W.IsPrime := hmin.1.1
  have hP : P ≤ W := le_sup_left.trans hmin.1.2
  have hf : f ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨u, v, hu, hv, hm⟩ := h W hWp hP hrel
  have hvg : v * g ∈ W := by
    have e : v * g = u * f - (u * f - v * g) := by ring
    rw [e]
    exact W.sub_mem (W.mul_mem_left u hf) (hP hm)
  have hg : g ∈ W := (hWp.mem_or_mem hvg).resolve_left hv
  refine ⟨⟨⟨hWp, sup_le hP ((Ideal.span_singleton_le_iff_mem _).mpr hg)⟩, ?_⟩, hrel⟩
  rintro W' ⟨hW'p, hW'le⟩ hW'W
  have hP' : P ≤ W' := le_sup_left.trans hW'le
  have hg' : g ∈ W' := hW'le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have huf : u * f ∈ W' := by
    have e : u * f = (u * f - v * g) + v * g := by ring
    rw [e]
    exact W'.add_mem (hP' hm) (W'.mul_mem_left v hg')
  have hf' : f ∈ W' := (hW'p.mem_or_mem huf).resolve_left fun hu' => hu (hW'W hu')
  exact hmin.2 ⟨hW'p, sup_le hP' ((Ideal.span_singleton_le_iff_mem _).mpr hf')⟩ hW'W

theorem mul_mem_sup_span_of_sub_mem {R : Type*} [CommRing R] {P : Ideal R} {f g u v x : R}
    (hm : u * f - v * g ∈ P) (hx : x ∈ P ⊔ Ideal.span {f}) : u * x ∈ P ⊔ Ideal.span {g} := by
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have e : u * (p + a * f) = (u * p + a * (u * f - v * g)) + (a * v) * g := by ring
  rw [e]
  exact Ideal.add_mem _
    (Ideal.mem_sup_left (P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left a hm)))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))

theorem multAt_sup_span_eq_of_sub_mem {P W : Ideal (MRing ι)} (hW : W.IsPrime) {f g u v : MRing ι}
    (hu : u ∉ W) (hv : v ∉ W) (hm : u * f - v * g ∈ P) :
    multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  have hm' : v * g - u * f ∈ P := by
    have := P.neg_mem hm
    rwa [neg_sub] at this
  haveI := hW
  unfold multAt
  rw [dite_eq_left hW, dite_eq_left hW,
    length_localizedModule_quot_eq W
      (fun x hx => ⟨u, hu, mul_mem_sup_span_of_sub_mem hm hx⟩)
      (fun x hx => ⟨v, hv, mul_mem_sup_span_of_sub_mem hm' hx⟩)]

theorem cycles_eq_of_isUnitSec :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι),
      IsUnitSec P f g → divSupp P f = divSupp P g ∧
        (∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W) ∧
        ∀ (n : ℕ) (L : Fin n → HermLine ι), vertR P L f = vertR P L g := by
  intro K _ ι _ P f g h
  have hsupp : divSupp P f = divSupp P g :=
    Set.Subset.antisymm (divSupp_subset_of_isUnitSec h) (divSupp_subset_of_isUnitSec h.symm)
  have hmult : ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    rintro W ⟨hmin, hrel⟩
    have hWp : W.IsPrime := hmin.1.1
    obtain ⟨u, v, hu, hv, hm⟩ := h W hWp (le_sup_left.trans hmin.1.2) hrel
    exact multAt_sup_span_eq_of_sub_mem hWp hu hv hm
  refine ⟨hsupp, hmult, fun n L => ?_⟩
  unfold vertR
  rw [← hsupp]
  refine finsum_mem_congr rfl fun W hW => ?_
  rw [hmult W hW]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.unit_section_divisor_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), IsUnitSec P f g → divSupp P f = divSupp P g ∧ (∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W) ∧ ∀ (n : ℕ) (L : Fin n → HermLine ι), vertR P L f = vertR P L g := by
  intro K _ ι _ P f g h
  have length_localizedModule_quot_eq {R : Type} [CommRing R] (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R}
      (h₁ : ∀ x ∈ J₁, ∃ s, s ∉ W ∧ s * x ∈ J₂) (h₂ : ∀ x ∈ J₂, ∃ s, s ∉ W ∧ s * x ∈ J₁) :
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₁)) =
        Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₂)) := by
    have key : ∀ {A B : Ideal R}, (∀ x ∈ A, ∃ s, s ∉ W ∧ s * x ∈ B) →
        Submodule.localized W.primeCompl (M := R) A ≤ Submodule.localized W.primeCompl (M := R) B := by
      intro A B h y hy
      obtain ⟨m, hm, s, rfl⟩ := hy
      obtain ⟨t, ht, htm⟩ := h m hm
      refine ⟨t * m, htm, ⟨t, ht⟩ * s, ?_⟩
      exact IsLocalizedModule.mk'_cancel_left _ _ _ _
    have heq : Submodule.localized W.primeCompl (M := R) J₁ = Submodule.localized W.primeCompl (M := R) J₂ :=
      le_antisymm (key h₁) (key h₂)
    have e₁ := (localizedQuotientEquiv W.primeCompl (M := R) J₁).length_eq
    have e₂ := (localizedQuotientEquiv W.primeCompl (M := R) J₂).length_eq
    have e₃ := (Submodule.quotEquivOfEq _ _ heq).length_eq
    exact e₁.symm.trans (e₃.trans e₂)

  have unitSec_symm {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) : IsUnitSec P g f := by
    intro W hW hP hR
    obtain ⟨u, v, hu, hv, hm⟩ := h W hW hP hR
    refine ⟨v, u, hv, hu, ?_⟩
    have := P.neg_mem hm
    rwa [neg_sub] at this

  have divSupp_subset_of_isUnitSec {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) :
      divSupp P f ⊆ divSupp P g := by
    rintro W ⟨hmin, hrel⟩
    have hWp : W.IsPrime := hmin.1.1
    have hP : P ≤ W := le_sup_left.trans hmin.1.2
    have hf : f ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
    obtain ⟨u, v, hu, hv, hm⟩ := h W hWp hP hrel
    have hvg : v * g ∈ W := by
      have e : v * g = u * f - (u * f - v * g) := by ring
      rw [e]
      exact W.sub_mem (W.mul_mem_left u hf) (hP hm)
    have hg : g ∈ W := (hWp.mem_or_mem hvg).resolve_left hv
    refine ⟨⟨⟨hWp, sup_le hP ((Ideal.span_singleton_le_iff_mem _).mpr hg)⟩, ?_⟩, hrel⟩
    rintro W' ⟨hW'p, hW'le⟩ hW'W
    have hP' : P ≤ W' := le_sup_left.trans hW'le
    have hg' : g ∈ W' := hW'le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
    have huf : u * f ∈ W' := by
      have e : u * f = (u * f - v * g) + v * g := by ring
      rw [e]
      exact W'.add_mem (hP' hm) (W'.mul_mem_left v hg')
    have hf' : f ∈ W' := (hW'p.mem_or_mem huf).resolve_left fun hu' => hu (hW'W hu')
    exact hmin.2 ⟨hW'p, sup_le hP' ((Ideal.span_singleton_le_iff_mem _).mpr hf')⟩ hW'W

  have mul_mem_sup_span_of_sub_mem {R : Type} [CommRing R] {P : Ideal R} {f g u v x : R}
      (hm : u * f - v * g ∈ P) (hx : x ∈ P ⊔ Ideal.span {f}) : u * x ∈ P ⊔ Ideal.span {g} := by
    obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e : u * (p + a * f) = (u * p + a * (u * f - v * g)) + (a * v) * g := by ring
    rw [e]
    exact Ideal.add_mem _
      (Ideal.mem_sup_left (P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left a hm)))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))

  have multAt_sup_span_eq_of_sub_mem {P W : Ideal (MRing ι)} (hW : W.IsPrime) {f g u v : MRing ι}
      (hu : u ∉ W) (hv : v ∉ W) (hm : u * f - v * g ∈ P) :
      multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    have hm' : v * g - u * f ∈ P := by
      have := P.neg_mem hm
      rwa [neg_sub] at this
    haveI := hW
    unfold multAt
    rw [dite_eq_left hW, dite_eq_left hW,
      length_localizedModule_quot_eq W (J₁ := P ⊔ Ideal.span {f}) (J₂ := P ⊔ Ideal.span {g})
        (fun x hx => ⟨u, hu, mul_mem_sup_span_of_sub_mem hm hx⟩)
        (fun x hx => ⟨v, hv, mul_mem_sup_span_of_sub_mem hm' hx⟩)]

  have hsupp : divSupp P f = divSupp P g :=
    Set.Subset.antisymm (divSupp_subset_of_isUnitSec h) (divSupp_subset_of_isUnitSec (unitSec_symm h))
  have hmult : ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    rintro W ⟨hmin, hrel⟩
    have hWp : W.IsPrime := hmin.1.1
    obtain ⟨u, v, hu, hv, hm⟩ := h W hWp (le_sup_left.trans hmin.1.2) hrel
    exact multAt_sup_span_eq_of_sub_mem hWp hu hv hm
  refine ⟨hsupp, hmult, fun n L => ?_⟩
  unfold vertR
  rw [← hsupp]
  refine finsum_mem_congr rfl fun W hW => ?_
  rw [hmult W hW]
end

section

namespace GlobalTheory.CompanionTheory.Ar.FlagChange

open GlobalTheory.CompanionTheory.Ar

theorem exists_coeff_of_mem_step {L Li : Type} [Field L] [AddCommGroup Li] [Module L Li] {r : ℕ}
    (g : Fin r → Li) (n : ℕ) (x : Li) (hx : x ∈ flagStep L g n) :
    ∃ c : Fin r → L, (∀ k : Fin r, n ≤ (k : ℕ) → c k = 0) ∧ x = ∑ k, c k • g k := by
  unfold flagStep at hx
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination L).1 hx
  refine ⟨l, fun k hk => ?_, ?_⟩
  · by_contra h
    have : k ∈ ({k : Fin r | (k : ℕ) < n} : Set (Fin r)) :=
      hl (Finsupp.mem_support_iff.2 h)
    exact absurd this (not_lt.2 hk)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul L (g i))]

theorem adapted_triangular (L Li : Type) [Field L] [AddCommGroup Li] [Module L Li] (r : ℕ)
    (f b g : Fin r → Li) (v w : Matrix (Fin r) (Fin r) L)
    (_hf : LinearIndependent L f) (hb : LinearIndependent L b)
    (_hv1 : ∀ k, v k k = 1) (_hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0)
    (hg : ∀ k, g k = ∑ j, (v * w) j k • f j)
    (hflag : ∀ i : ℕ, flagStep L b i = flagStep L g i) :
    ∃ Tm : Matrix (Fin r) (Fin r) L, (∀ i, b i = ∑ m, Tm i m • ∑ j, v j m • f j) ∧
      (∀ i m, i < m → Tm i m = 0) ∧ ∀ i, Tm i i ≠ 0 := by
  have hC : ∀ i : Fin r, ∃ c : Fin r → L,
      (∀ k : Fin r, (i : ℕ) + 1 ≤ (k : ℕ) → c k = 0) ∧ b i = ∑ k, c k • g k := fun i =>
    exists_coeff_of_mem_step g _ _ (by
      rw [← hflag]
      exact Submodule.subset_span ⟨i, by simp, rfl⟩)
  choose C hC0 hCb using hC
  have hgW : ∀ k, g k = ∑ m, w m k • ∑ j, v j m • f j := by
    intro k
    rw [hg k]
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  refine ⟨Matrix.of fun i m => ∑ k, C i k * w m k, fun i => ?_, fun i m him => ?_, fun i => ?_⟩
  · generalize hW : (fun m => ∑ j, v j m • f j) = W at *
    have hW' : ∀ m, ∑ j, v j m • f j = W m := fun m => congrFun hW m
    simp only [hW'] at hgW ⊢
    calc b i = ∑ k, C i k • ∑ m, w m k • W m :=
          (hCb i).trans (Finset.sum_congr rfl fun k _ => by rw [hgW k])
      _ = ∑ m, (∑ k, C i k * w m k) • W m := by
          simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
          exact Finset.sum_comm
      _ = _ := rfl
  · show ∑ k, C i k * w m k = 0
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ≤ i
    · rw [hw0 m k (lt_of_le_of_lt hk him), mul_zero]
    · rw [hC0 i k (not_le.1 hk), zero_mul]
  · have hdiag : ∑ k, C i k * w i k = C i i * w i i := by
      refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hw0 i k h, mul_zero]
      · rw [hC0 i k h, zero_mul]
    show ∑ k, C i k * w i k ≠ 0
    rw [hdiag]
    refine mul_ne_zero (fun h0 => ?_) (hwd i)
    have hmem : b i ∈ flagStep L g i := by
      rw [hCb i]
      refine Submodule.sum_mem _ fun k _ => ?_
      by_cases hk : (k : ℕ) < i
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
      · have hz : C i k = 0 := by
          rcases eq_or_lt_of_le (not_lt.1 hk) with h | h
          · rw [show k = i from Fin.ext h.symm, h0]
          · exact hC0 i k h
        rw [hz, zero_smul]
        exact Submodule.zero_mem _
    rw [← hflag] at hmem
    exact hb.notMem_span_image (s := {k | (k : ℕ) < i}) (x := i) (by simp) hmem

end GlobalTheory.CompanionTheory.Ar.FlagChange
end
