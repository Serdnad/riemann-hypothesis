module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem lift_ringHom_of_scheme_lift : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → ∀ (U : (Sp B).Opens), IsAffineOpen U → ∀ (V : X.Opens), IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U), (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : Γ(Sp B, U) →+* C) (φ₀ : Γ(X, V) →+* C₀), φ₀.comp ((s.appLE U V e).hom) = π.comp β → ∃ φ : Γ(X, V) →+* C, π.comp φ = φ₀ ∧ φ.comp ((s.appLE U V e).hom) = β) := by
  intro B _ X s hlift U hU V hV e C C₀ _ _ _ _ π hπ hk β φ₀ hcomp

  haveI : Nontrivial C₀ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h1 : (1 : C) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker]; exact Subsingleton.elim _ _
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      have := Ideal.mul_mem_mul h1 h1
      simpa [pow_two] using this
    rw [hk, Ideal.mem_bot] at h2
    exact one_ne_zero h2
  have hsub : ∀ a b : PrimeSpectrum C, a = b := by
    intro a b
    ext1
    rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime a.asIdeal),
      IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime b.asIdeal)]
  have hA := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have hx₀ : (Spec.map (CommRingCat.ofHom φ₀) ≫ hV.fromSpec) ≫ s =
      spMap π ≫ (Spec.map (CommRingCat.ofHom β) ≫ hU.fromSpec) := by
    rw [Category.assoc, ← hA, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, spMap,
      ← Spec.map_comp]
    congr 2
    ext1
    exact hcomp
  obtain ⟨x, hx1, hx2⟩ := hlift C C₀ π hπ hk _ _ hx₀
  have hrange : Set.range x ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q⟩ := (inferInstance : Nonempty (PrimeSpectrum C₀))
    have hp : p = (spMap π) q := hsub _ _
    refine ⟨(Spec.map (CommRingCat.ofHom φ₀)) q, ?_⟩
    rw [hp]
    have := congrArg (fun f : Sp C₀ ⟶ X => f q) hx1
    first
      | exact this.symm
      | (rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this; exact this.symm)
      | (simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this; exact this.symm)
  have hyx : IsOpenImmersion.lift hV.fromSpec x hrange ≫ hV.fromSpec = x :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = IsOpenImmersion.lift hV.fromSpec x hrange :=
    ⟨_, Spec.map_preimage _⟩
  rw [← hφ] at hyx
  refine ⟨φ.hom, ?_, ?_⟩
  · have h3 : Spec.map (CommRingCat.ofHom (π.comp φ.hom)) ≫ hV.fromSpec =
        Spec.map (CommRingCat.ofHom φ₀) ≫ hV.fromSpec := by
      rw [← hx1, ← hyx, spMap, ← Category.assoc, ← Spec.map_comp]
      rfl
    have h4 := Spec.map_injective ((cancel_mono hV.fromSpec).1 h3)
    exact congrArg CommRingCat.Hom.hom h4
  · have h3 : Spec.map (CommRingCat.ofHom (φ.hom.comp (s.appLE U V e).hom)) ≫
        hU.fromSpec = Spec.map (CommRingCat.ofHom β) ≫ hU.fromSpec := by
      rw [← hx2, ← hyx, Category.assoc, ← hA, ← Category.assoc,
        ← Spec.map_comp]
      rfl
    have h4 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h3)
    exact congrArg CommRingCat.Hom.hom h4

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PtClosed

def killIdeal {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop) :
    Ideal A where
  carrier := {a | ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f → f a = 0}
  add_mem' {a b} ha hb R' _ f hf := by rw [map_add (f := _), ha R' f hf, hb R' f hf, add_zero]
  zero_mem' R' _ f _ := map_zero f
  smul_mem' c a ha R' _ f hf := by rw [smul_eq_mul, map_mul, ha R' f hf, mul_zero]

def Represents {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop)
    (J : Ideal A) : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f ↔ J ≤ RingHom.ker f

def ptQ {S : Scheme.{0}} (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop) (V : S.Opens)
    (hV : IsAffineOpen V) : ∀ (R' : Type) [CommRing R'], (Γ(S, V) →+* R') → Prop :=
  fun R' _ f ↦ P R' (spMap f ≫ hV.fromSpec)

theorem killIdeal_eq {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    killIdeal Q = J := by
  apply le_antisymm
  · intro a ha
    have := ha (A ⧸ J) (Ideal.Quotient.mk J) ((h _ _).2 (by simp [Ideal.mk_ker]))
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this
  · intro a ha R' _ f hf
    exact (h R' f).1 hf ha

theorem represents_killIdeal {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    Represents Q (killIdeal Q) := by
  rw [killIdeal_eq h]; exact h

theorem represents_restrict : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
  (U W : S.Opens) (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) (J : Ideal Γ(S, U)),
  Represents (ptQ P U hU) J → Represents (ptQ P W hW) (J.map (S.presheaf.map (homOfLE h).op).hom) := by
  intro S P U W hU hW h J hJ R' _ f
  have e : spMap f ≫ hW.fromSpec =
      spMap (f.comp (S.presheaf.map (homOfLE h).op).hom) ≫ hU.fromSpec := by
    rw [← hU.map_fromSpec hW (homOfLE h).op]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap f ≫ hW.fromSpec) ↔ _
  rw [e, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_prime_eq_span_of_coheight_le_one (R : Type) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R) (hq : GeneralizingMap q)
    (x : X) (hx : Order.coheight x ≤ 1) (hne : (q x).asIdeal ≠ ⊥) :
    ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  obtain ⟨π, hπP, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (q x).isPrime hne
  refine ⟨π, hπ, ?_⟩
  by_contra hQP
  have hQle : Ideal.span {π} ≤ (q x).asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hπP
  have hQprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  let Q : PrimeSpectrum R := ⟨_, hQprime⟩
  have hQsp : Q ⤳ q x := (PrimeSpectrum.le_iff_specializes Q (q x)).1 hQle
  obtain ⟨x', hx'x, hqx'⟩ := hq hQsp
  let B : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hBQ : B ⤳ Q := (PrimeSpectrum.le_iff_specializes B Q).1 bot_le
  obtain ⟨x'', hx''x', hqx''⟩ := hq (hqx' ▸ hBQ)
  have h1 : x < x' := by
    refine lt_of_le_not_ge hx'x ?_
    intro h
    have h' : q x ⤳ q x' := h.map q.continuous
    rw [hqx'] at h'
    exact hQP (le_antisymm ((PrimeSpectrum.le_iff_specializes (q x) Q).2 h') hQle)
  have h2 : x' < x'' := by
    refine lt_of_le_not_ge hx''x' ?_
    intro h
    have h' : q x' ⤳ q x'' := h.map q.continuous
    rw [hqx', hqx''] at h'
    have hle : Ideal.span {π} ≤ ⊥ := (PrimeSpectrum.le_iff_specializes Q B).2 h'
    exact hπ.ne_zero (Ideal.span_singleton_eq_bot.1 (le_bot_iff.1 hle))
  have c1 := Order.coheight_add_one_le h1
  have c2 := Order.coheight_add_one_le h2
  have : (2 : ℕ∞) ≤ Order.coheight x := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight x'' + 1 + 1 := by gcongr; exact bot_le
      _ ≤ Order.coheight x' + 1 := by gcongr
      _ ≤ Order.coheight x := c1
  have := this.trans hx
  norm_num at this

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SecGlue

theorem preimage_eq_of_comp_eq_of_sqZero : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T),
    Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens,
      u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  intro S T _ _ q hq hsq Y u w huw V
  have hsurj : Function.Surjective (spMap q).base := by
    intro p
    have hker : RingHom.ker q ≤ p.asIdeal := by
      intro x hx
      have hx2 : x * x ∈ RingHom.ker q ^ 2 := by
        rw [sq]; exact Ideal.mul_mem_mul hx hx
      rw [hsq, Ideal.mem_bot] at hx2
      exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
    haveI := p.isPrime
    haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
    refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
    intro x hx
    exact hker (by simpa [RingHom.mem_ker] using hx)
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage,
    ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, huw]

end GlobalTheory.SecGlue
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem spMap_away_mem_basicOpen {S : Type} [CommRing S] (s : S)
    (x : Sp (Localization.Away s)) :
    (spMap (algebraMap S (Localization.Away s))).base x ∈ PrimeSpectrum.basicOpen s := by
  show algebraMap S (Localization.Away s) s ∉ x.asIdeal
  intro h
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))

theorem exists_basicOpen_cover_affine (S : Type) [CommRing S] (Y : Scheme.{0}) (u : Sp S ⟶ Y) :
    ∃ (n : ℕ) (s : Fin n → S) (W : Fin n → Y.Opens), Ideal.span (Set.range s) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧ ∀ i, (spMap (algebraMap S (Localization.Away (s i))) ≫ u) ⁻¹ᵁ W i = ⊤ := by
  classical
  let T : Set S := {s | ∃ W : Y.Opens, IsAffineOpen W ∧
    ∀ x : Sp S, x ∈ PrimeSpectrum.basicOpen s → u.base x ∈ W}
  have hT : Ideal.span T = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff', eq_top_iff]
    intro x _
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (u.base x)) isOpen_univ
    obtain ⟨_, ⟨s, rfl⟩, hxs, hsW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        hxW (u ⁻¹ᵁ W).isOpen
    have hsT : s ∈ T := ⟨W, hW, fun y hy => hsW hy⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, TopologicalSpace.Opens.mem_iSup.mpr ⟨hsT, hxs⟩⟩
  obtain ⟨F, hFT, hF⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  have hW : ∀ t : F, ∃ W : Y.Opens, IsAffineOpen W ∧
      ∀ x : Sp S, x ∈ PrimeSpectrum.basicOpen (t : S) → u.base x ∈ W := fun t => hFT t.2
  choose Wf hWa hWs using hW
  refine ⟨F.card, fun i => (F.equivFin.symm i : S), fun i => Wf (F.equivFin.symm i), ?_,
    fun i => hWa _, fun i => ?_⟩
  · have : Set.range (fun i => (F.equivFin.symm i : S)) = (F : Set S) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact (F.equivFin.symm i).2
      · intro hy
        exact ⟨F.equivFin ⟨y, hy⟩, by simp⟩
    rw [this, hF]
  · rw [eq_top_iff]
    intro x _
    exact hWs _ _ (spMap_away_mem_basicOpen _ x)

end GlobalTheory.SecGlue
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Red

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]; exact Spec.map_id _

theorem away_ext {R T : Type} [CommRing R] [CommRing T] (a : R) (φ ψ : Localization.Away a →+* T)
    (h : φ.comp (algebraMap R _) = ψ.comp (algebraMap R _)) : φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h

theorem isUnit_of_away {R T : Type} [CommRing R] [CommRing T] [Algebra R T] (a : R)
    (ρ : Localization.Away a →+* T) (hρ : ρ.comp (algebraMap R _) = algebraMap R T) :
    IsUnit (algebraMap R T a) := by
  rw [← hρ]; exact (IsLocalization.Away.algebraMap_isUnit a).map ρ

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

abbrev redI (π : R →+* R₀) (S : Type) [CommRing S] [Algebra R S] : Ideal S :=
  (RingHom.ker π).map (algebraMap R S)

def redPsi (π : R →+* R₀) (hπ : Function.Surjective π) (S : Type) [CommRing S] [Algebra R S] :
    R₀ →+* S ⧸ redI π S :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨(Ideal.Quotient.mk (redI π S)).comp (algebraMap R S), fun x hx => by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hx⟩

theorem redPsi_comp (π : R →+* R₀) (hπ : Function.Surjective π) (S : Type) [CommRing S]
    [Algebra R S] : (redPsi π hπ S).comp π = (Ideal.Quotient.mk (redI π S)).comp (algebraMap R S) :=
  RingHom.liftOfRightInverse_comp _ _ _ _

theorem ker_mk_sq (π : R →+* R₀) (h : RingHom.ker π ^ 2 = ⊥) (S : Type) [CommRing S]
    [Algebra R S] : RingHom.ker (Ideal.Quotient.mk (redI π S)) ^ 2 = ⊥ := by
  rw [Ideal.mk_ker, ← Ideal.map_pow, h, Ideal.map_bot]

def IsRed (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}} (g₀ : Sp R₀ ⟶ Y)
    (S : Type) [CommRing S] [Algebra R S] (u : Sp S ⟶ Y) : Prop :=
  spMap (Ideal.Quotient.mk (redI π S)) ≫ u = spMap (redPsi π hπ S) ≫ g₀

theorem IsRed.eq {π : R →+* R₀} {hπ : Function.Surjective π} {Y : Scheme.{0}} {g₀ : Sp R₀ ⟶ Y}
    {S : Type} [CommRing S] [Algebra R S] {u v : Sp S ⟶ Y} (hu : IsRed π hπ g₀ S u)
    (hv : IsRed π hπ g₀ S v) :
    spMap (Ideal.Quotient.mk (redI π S)) ≫ u = spMap (Ideal.Quotient.mk (redI π S)) ≫ v :=
  hu.trans hv.symm

theorem isRed_of_away (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) (a : R) (u : Sp (Localization.Away a) ⟶ Y)
    (hu : spMap (Localization.awayMap π a) ≫ u =
      spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀)
    (S : Type) [CommRing S] [Algebra R S] (ρ : Localization.Away a →+* S)
    (hρ : ρ.comp (algebraMap R _) = algebraMap R S) : IsRed π hπ g₀ S (spMap ρ ≫ u) := by
  have hunit : IsUnit (redPsi π hπ S (π a)) := by
    have e : redPsi π hπ S (π a) = Ideal.Quotient.mk (redI π S) (algebraMap R S a) := by
      rw [← RingHom.comp_apply (redPsi π hπ S) π, redPsi_comp, RingHom.comp_apply]
    rw [e]; exact (isUnit_of_away a ρ hρ).map _
  let lam := IsLocalization.Away.lift (S := Localization.Away (π a)) (π a) hunit
  have key : (Ideal.Quotient.mk (redI π S)).comp ρ = lam.comp (Localization.awayMap π a) := by
    apply away_ext a
    rw [RingHom.comp_assoc, hρ, RingHom.comp_assoc]
    have e1 : (Localization.awayMap π a).comp (algebraMap R (Localization.Away a)) =
        (algebraMap R₀ (Localization.Away (π a))).comp π := IsLocalization.map_comp _
    rw [e1, ← RingHom.comp_assoc, IsLocalization.Away.lift_comp, redPsi_comp]
  unfold IsRed
  rw [← Category.assoc, ← spMap_comp, key, spMap_comp, Category.assoc, hu, ← Category.assoc,
    ← spMap_comp, IsLocalization.Away.lift_comp]

theorem isRed_self (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) (a : R) (u : Sp (Localization.Away a) ⟶ Y)
    (hu : spMap (Localization.awayMap π a) ≫ u =
      spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀) :
    IsRed π hπ g₀ (Localization.Away a) u := by
  have := isRed_of_away π hπ g₀ a u hu (Localization.Away a) (RingHom.id _) rfl
  rwa [spMap_id, Category.id_comp] at this

theorem isRed_comp (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (σ : S →+* S') (hσ : σ.comp (algebraMap R S) = algebraMap R S') {u : Sp S ⟶ Y}
    (hu : IsRed π hπ g₀ S u) : IsRed π hπ g₀ S' (spMap σ ≫ u) := by
  have hle : redI π S ≤ (redI π S').comap σ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, ← RingHom.comp_apply σ, hσ]
    exact Ideal.mem_map_of_mem _ hx
  have h1 : (Ideal.Quotient.mk (redI π S')).comp σ =
      (Ideal.quotientMap (redI π S') σ hle).comp (Ideal.Quotient.mk (redI π S)) :=
    (Ideal.quotientMap_comp_mk hle).symm
  have h2 : (Ideal.quotientMap (redI π S') σ hle).comp (redPsi π hπ S) = redPsi π hπ S' := by
    apply RingHom.ext; intro y; obtain ⟨x, rfl⟩ := hπ y
    rw [RingHom.comp_apply, ← RingHom.comp_apply (redPsi π hπ S), redPsi_comp,
      ← RingHom.comp_apply (redPsi π hπ S'), redPsi_comp, RingHom.comp_apply, RingHom.comp_apply,
      Ideal.quotientMap_mk, ← RingHom.comp_apply σ, hσ]
  unfold IsRed at *
  rw [← Category.assoc, ← spMap_comp, h1, spMap_comp, Category.assoc, hu, ← Category.assoc,
    ← spMap_comp, h2]

theorem awayMap_eq_of_red (π : R →+* R₀) {Y : Scheme.{0}} (a : R)
    (u v : Sp (Localization.Away a) ⟶ Y)
    (h : spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ u =
      spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ v) :
    spMap (Localization.awayMap π a) ≫ u = spMap (Localization.awayMap π a) ≫ v := by
  have H : ∀ x ∈ redI π (Localization.Away a), Localization.awayMap π a x = 0 := by
    intro x hx
    have hle : redI π (Localization.Away a) ≤ RingHom.ker (Localization.awayMap π a) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
        show (Localization.awayMap π a).comp (algebraMap R (Localization.Away a)) =
          (algebraMap R₀ (Localization.Away (π a))).comp π from IsLocalization.map_comp _,
        RingHom.comp_apply, RingHom.mem_ker.1 hy, map_zero]
    exact hle hx
  have e : Localization.awayMap π a =
      (Ideal.Quotient.lift _ (Localization.awayMap π a) H).comp (Ideal.Quotient.mk _) := by
    ext x; simp
  rw [e, spMap_comp, Category.assoc, Category.assoc, h]

end GlobalTheory.SecGlue.Red
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.IdealSectionsFactorization

theorem comp_eq_iff_factors {S X B W : Scheme.{0}} (p : X ⟶ B) (x y : S ⟶ X)
    (h : x ≫ p = y ≫ p) (g : W ⟶ S) :
    g ≫ x = g ≫ y ↔
      ∃ l : W ⟶ pullback (pullback.lift x y h) (pullback.diagonal p),
        l ≫ pullback.fst _ _ = g := by
  constructor
  · intro hg
    refine ⟨pullback.lift g (g ≫ x) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [pullback.diagonal_fst, pullback.lift_fst]
    · simp [pullback.diagonal_snd, pullback.lift_snd, hg]
  · rintro ⟨l, rfl⟩
    have hc := pullback.condition (f := pullback.lift x y h) (g := pullback.diagonal p)
    have h1 := congrArg (· ≫ pullback.fst p p) hc
    have h2 := congrArg (· ≫ pullback.snd p p) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd, Category.comp_id] at h1 h2
    rw [Category.assoc, Category.assoc, h1, h2]

theorem factors_iff_kills {R T : Type} [CommRing R] [CommRing T] (I : Ideal R) (ψ : R →+* T) :
    (∃ l : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (R ⧸ I)),
      l ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = Spec.map (CommRingCat.ofHom ψ)) ↔
      ∀ r ∈ I, ψ r = 0 := by
  constructor
  · rintro ⟨l, hl⟩ r hr
    obtain ⟨φ, rfl⟩ := Spec.map_surjective l
    rw [← Spec.map_comp] at hl
    have h := Spec.map_injective hl
    have h' : φ.hom (Ideal.Quotient.mk I r) = ψ r :=
      congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of T => k.hom r) h
    rw [← h', Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ h)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

theorem exists_ideal_sections_eq (R : Type) [CommRing R]
    (X : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) (hX : IsSeparated X.hom)
    (x y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R))
    (hy : y ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) :
    ∃ I : Ideal R, ∀ (T : Type) [CommRing T] (ψ : R →+* T),
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ x = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ y ↔
        ∀ r ∈ I, ψ r = 0 := by
  have h : x ≫ X.hom = y ≫ X.hom := hx.trans hy.symm
  have hc : IsClosedImmersion
      (pullback.fst (pullback.lift x y h) (pullback.diagonal X.hom)) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ _).flip hX.isClosedImmersion_diagonal
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hc
  refine ⟨I, fun T _ ψ => ?_⟩
  rw [comp_eq_iff_factors X.hom x y h, ← factors_iff_kills I ψ, he]
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.hom, by rw [Category.assoc]; exact hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.inv, by rw [Category.assoc, e.inv_hom_id_assoc]; exact hl⟩

end GlobalTheory.IdealSectionsFactorization
end
