module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem germ_isUnit_and_surj {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (y : X) (hy : y ∈ U) :
    (∀ a : Γ(X, U), IsUnit (X.presheaf.germ U y hy a) ↔ a ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
    ∀ g : X.presheaf.stalk y, ∃ b c : Γ(X, U), b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      g * X.presheaf.germ U y hy b = X.presheaf.germ U y hy c := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : U)
  have hl : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  refine ⟨fun a => ?_, fun g => ?_⟩
  · exact IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y)
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal a
  · obtain ⟨⟨c, ⟨b, hb⟩⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl g
    exact ⟨b, c, hb, h⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

theorem genMap_germ {U : X.Opens} (p : Cpt ξ) (hp : p.1 ∈ U) (hg : genPt ξ ∈ U) (a : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp a) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg a) := by
  have h : X.presheaf.germ U p.1 hp ≫ X.presheaf.stalkSpecializes p.2 = X.presheaf.germ U (genPt ξ) hg :=
    TopCat.Presheaf.germ_stalkSpecializes _ _ _
  simp only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← h]
  rfl

theorem genMap_stalkSpecializes (p q : Cpt ξ) (h : q.1 ⤳ p.1) (g : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes h).hom g) = genMap ξ p g := by
  have h2 : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes q.2 =
      X.presheaf.stalkSpecializes p.2 := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  simp only [genMap]
  rw [← h2]
  rfl

end GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_prime_generisation : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (p : Cpt ξ) (I : Ideal (regAt ξ p)), I.IsPrime → ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ∀ a : Ω, a ∈ regAt ξ q ↔ ∃ s : regAt ξ p, s ∉ I ∧ (s : Ω) * a ∈ regAt ξ p := by
  intro X Ω _ ξ hξ p I hI
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := p.1) (U := ⊤) trivial
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let ρ : X.presheaf.stalk p.1 →+* regAt ξ p := (genMap ξ p).rangeRestrict
  have hρ : ∀ r, ((ρ r : regAt ξ p) : Ω) = genMap ξ p r := fun _ => rfl
  have hρs : Function.Surjective ρ := (genMap ξ p).rangeRestrict_surjective
  let J : Ideal (X.presheaf.stalk p.1) := I.comap ρ
  have hJ : J.IsPrime := Ideal.comap_isPrime ρ I
  let gp : Γ(X, U) →+* X.presheaf.stalk p.1 := (X.presheaf.germ U p.1 hpU).hom
  let Q0 : PrimeSpectrum Γ(X, U) := ⟨J.comap gp, Ideal.comap_isPrime gp J⟩
  have hspec : ∀ P Q : PrimeSpectrum Γ(X, U), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
    intro P Q
    rw [PrimeSpectrum.le_iff_specializes]
    exact hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff
  have hqU : hU.fromSpec Q0 ∈ U := by
    have : hU.fromSpec Q0 ∈ Set.range hU.fromSpec := ⟨Q0, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hQ0 : hU.primeIdealOf ⟨_, hqU⟩ = Q0 :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  have hP := hU.fromSpec_primeIdealOf ⟨p.1, hpU⟩
  have hG := hU.fromSpec_primeIdealOf ⟨genPt ξ, hgU⟩
  obtain ⟨hPu, hPs⟩ := germ_isUnit_and_surj hU p.1 hpU
  obtain ⟨hGu, -⟩ := germ_isUnit_and_surj hU (genPt ξ) hgU
  obtain ⟨hQu, hQs⟩ := germ_isUnit_and_surj hU _ hqU
  rw [hQ0] at hQu hQs
  have hunitJ : ∀ r, IsUnit r → r ∉ J := fun r hr hrJ => hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hrJ hr)

  have hGQ : hU.primeIdealOf ⟨genPt ξ, hgU⟩ ≤ Q0 := by
    intro a ha
    let φ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
    have hφ : Function.Bijective φ := hξ.bij
    have h0 : φ (X.presheaf.germ U (genPt ξ) hgU a) = 0 := by
      by_contra hne
      obtain ⟨d, hd⟩ := hφ.2 (φ (X.presheaf.germ U (genPt ξ) hgU a))⁻¹
      have h1 : X.presheaf.germ U (genPt ξ) hgU a * d = 1 := by
        apply hφ.1
        rw [map_mul, hd, map_one, mul_inv_cancel₀ hne]
      exact (not_not.mpr ha) ((hGu a).1 (IsUnit.of_mul_eq_one _ h1))
    have h2 : gp a = 0 := by
      apply hξ.inj p
      rw [map_zero, ← h0]
      exact genMap_germ ξ p hpU hgU a
    show gp a ∈ J
    rw [h2]
    exact J.zero_mem
  have hQP : Q0 ≤ hU.primeIdealOf ⟨p.1, hpU⟩ := by
    intro a ha
    by_contra hn
    exact hunitJ _ ((hPu a).2 hn) ha
  have hqp : hU.fromSpec Q0 ⤳ p.1 := by
    have := (hspec _ _).2 hQP
    rwa [hP] at this
  have hgq : genPt ξ ⤳ hU.fromSpec Q0 := by
    have := (hspec _ _).2 hGQ
    rwa [hG] at this
  let q : Cpt ξ := ⟨hU.fromSpec Q0, hgq⟩
  let σ : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hqp).hom
  have hσ : ∀ g, genMap ξ q (σ g) = genMap ξ p g := genMap_stalkSpecializes ξ p q hqp
  have hσg : ∀ a : Γ(X, U), σ (X.presheaf.germ U p.1 hpU a) = X.presheaf.germ U q.1 hqU a :=
    fun a => X.presheaf.germ_stalkSpecializes_apply hpU hqp a
  refine ⟨q, hqp, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨b, c, hb, hbc⟩ := hQs g
    refine ⟨ρ (X.presheaf.germ U p.1 hpU b), hb, ⟨X.presheaf.germ U p.1 hpU c, ?_⟩⟩
    rw [hρ, ← hσ, ← hσ, hσg, hσg, ← hbc, map_mul, mul_comm]
  · rintro ⟨s, hs, t, ht⟩
    obtain ⟨r, rfl⟩ := hρs s
    have hrJ : r ∉ J := hs
    obtain ⟨b, c, hb, hbc⟩ := hPs r
    have hbu := (hPu b).2 hb
    have hcJ : X.presheaf.germ U p.1 hpU c ∉ J := by
      rw [← hbc]
      intro h
      exact (hJ.mem_or_mem h).elim hrJ (hunitJ _ hbu)
    have hcu := (hQu c).2 hcJ
    have hσr : IsUnit (σ r) := by
      rw [← hσg, ← hbc, map_mul] at hcu
      exact isUnit_of_mul_isUnit_left hcu
    obtain ⟨u, hu⟩ := hσr
    refine ⟨(↑u⁻¹ : X.presheaf.stalk q.1) * σ t, ?_⟩
    have hne : genMap ξ q (σ r) * genMap ξ q (↑u⁻¹ : X.presheaf.stalk q.1) = 1 := by
      rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_mul, hσ, ht, hρ, ← hσ r, ← _root_.mul_assoc, mul_comm (genMap ξ q _), hne, _root_.one_mul]

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (s : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp s) = genMap ξ q (X.presheaf.germ U q.1 hq s) := by
  have h : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr s) =
      (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr) s) := by
    intro r hr
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 s)
  rw [h p hp, h q hq]

theorem exists_open_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : Ω) (ha : a ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  exact ⟨U, hU, fun q hq => ⟨_, genMap_germ_eq_genMap_germ ξ U q p hq hU s⟩⟩

theorem regAt_unitAt_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω), (a ∈ regAt ξ p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) ∧ (unitAt ξ p a → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q a) := by
  intro X Ω _ ξ p a
  refine ⟨exists_open_mem_regAt ξ p a, ?_⟩
  rintro ⟨h0, h1, h2⟩
  obtain ⟨U, hU, HU⟩ := exists_open_mem_regAt ξ p a h1
  obtain ⟨V, hV, HV⟩ := exists_open_mem_regAt ξ p _ h2
  exact ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq => ⟨h0, HU q hq.1, HV q hq.2⟩⟩

end GlobalTheory.CompanionTheory.Ar
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_app_pullback {B : Type} [CommRing B] {X Y : Scheme.{0}}
    (x : Spec (CommRingCat.of B) ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (s : Γ(Y, U)) :
    valAt x (φ ⁻¹ᵁ U) h (φ.app U s) = valAt (x ≫ φ) U h' s := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem valAt_congr_point {B : Type} [CommRing B] {X : Scheme.{0}}
    {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x U h s = valAt y U h' s := by
  subst e
  rfl

theorem QFGroup.regularAt_translate :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T)
      (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t →
      ∀ (f : T → FractionRing R) (g : Γ.G.left),
        Γ.RegularAt f (((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g) → Γ.RegularAt (fun h => f (t * h)) g := by
  intro R _ _ T _ _ Γ σ t ht f g ⟨U, hgU, s, hs⟩
  have key : ∀ h : T, Γ.pt h ≫ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G) = Γ.pt (t * h) := by
    intro h
    rw [MonObj.comp_mul, map_mul, ← ht, Category.comp_id, ← Category.assoc, comp_toUnit]
  refine ⟨((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left ⁻¹ᵁ U, hgU, ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left.app U s, ?_⟩
  intro h hh
  have e : (Γ.pt h).left ≫ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left = (Γ.pt (t * h)).left := by
    rw [← key h]; rfl
  have h' : ⊤ ≤ ((Γ.pt h).left ≫ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left) ⁻¹ᵁ U := hh
  have h'' : ⊤ ≤ (Γ.pt (t * h)).left ⁻¹ᵁ U := e ▸ h'
  rw [valAt_app_pullback _ _ U hh h', valAt_congr_point e U h' h'' s]
  exact hs (t * h) h''

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.finite_of_qfGroup : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  intro R _ _ T _ Γ
  have hqf : LocallyQuasiFinite Γ.G.hom := Γ.quasiFinite
  have hqc : QuasiCompact Γ.G.hom := Γ.quasiCompact
  let F := pullback Γ.G.hom (genPt R).hom
  let g : F ⟶ Spec (CommRingCat.of (FractionRing R)) := pullback.snd Γ.G.hom (genPt R).hom
  have hK : ∀ u v : Spec (CommRingCat.of (FractionRing R)), u = v := fun u v =>
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) u v
  let b : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  have hgqf : LocallyQuasiFinite g := inferInstance
  have hgqc : QuasiCompact g := inferInstance
  have huniv : g ⁻¹' {b} = Set.univ := by
    ext x; simp [hK (g x) b]
  have hfin : Finite F := by
    have h := g.finite_preimage_singleton b
    rw [huniv] at h
    exact Set.finite_univ_iff.mp h
  have hw : ∀ t, (Γ.pt t).left ≫ Γ.G.hom = 𝟙 _ ≫ (genPt R).hom := fun t => by
    rw [Category.id_comp]; exact Over.w (Γ.pt t)
  let f : T → F := fun t => (pullback.lift _ _ (hw t)) b
  refine Finite.of_injective f ?_
  intro s t hst
  have h := congrArg (pullback.fst Γ.G.hom (genPt R).hom) hst
  simp only [f] at h
  simp only [← Scheme.Hom.comp_apply, pullback.lift_fst] at h
  exact Γ.pt_inj s t b b h

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.BT.LateralTheory

theorem ringHom_ext_of_isFractionRing {V K L : Type} [CommRing V] [IsDomain V] [Field K] [Field L] [Algebra V K]
    [IsFractionRing V K] (φ ψ : L →+* K) (θ : V →+* L) (h₁ : φ.comp θ = algebraMap V K)
    (h₂ : ψ.comp θ = algebraMap V K) : φ = ψ := by
  have e₁ : ∀ v, φ (θ v) = algebraMap V K v := fun v => RingHom.congr_fun h₁ v
  have e₂ : ∀ v, ψ (θ v) = algebraMap V K v := fun v => RingHom.congr_fun h₂ v
  ext c
  obtain ⟨v, w, hw0, hc⟩ := IsFractionRing.div_surjective (A := V) (φ c)
  have hw : algebraMap V K w ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hw0
  have hθ : θ w * c = θ v := φ.injective (by
    rw [map_mul, e₁, e₁, ← hc]
    field_simp)
  have h3 := congrArg ψ hθ
  rw [map_mul, e₂, e₂] at h3
  rw [← hc, div_eq_iff hw, ← h3, mul_comm]

theorem point_ext {V : Type} [CommRing V] [IsDomain V] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of V))
    (f g : Spec (CommRingCat.of (FractionRing V)) ⟶ X)
    (hf : f ≫ π = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    (hg : g ≫ π = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    (x y : Spec (CommRingCat.of (FractionRing V))) (h : f x = g y) : f = g := by
  obtain ⟨⟨z, φ⟩, hz⟩ := (Scheme.SpecToEquivOfField (FractionRing V) X).symm.surjective f
  obtain ⟨⟨w, ψ⟩, hw⟩ := (Scheme.SpecToEquivOfField (FractionRing V) X).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz hw
  have hzw : z = w := by
    have h1 : f x ∈ Set.range (X.fromSpecResidueField z) := by
      rw [← hz]; exact ⟨_, rfl⟩
    have h2 : g y ∈ Set.range (X.fromSpecResidueField w) := by
      rw [← hw]; exact ⟨_, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at h1 h2
    rw [h] at h1
    exact h1.symm.trans h2
  subst hzw
  let θ : CommRingCat.of V ⟶ X.residueField z := Spec.preimage (X.fromSpecResidueField z ≫ π)
  have hθ : Spec.map θ = X.fromSpecResidueField z ≫ π := Spec.map_preimage _
  have h₁ : θ ≫ φ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ, ← Category.assoc, hz, hf]
  have h₂ : θ ≫ ψ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hθ, ← Category.assoc, hw, hg]
  have hφψ : φ = ψ := by
    apply CommRingCat.hom_ext
    exact ringHom_ext_of_isFractionRing (V := V) φ.hom ψ.hom θ.hom
      (congrArg CommRingCat.Hom.hom h₁) (congrArg CommRingCat.Hom.hom h₂)
  rw [← hz, ← hw, hφψ]

variable {V : Type} [CommRing V] [IsDomain V] {T : Type} [CommGroup T]

theorem toUnit_genPt_left : (toUnit (genPt V)).left =
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
  simpa using Over.w (toUnit (genPt V))

theorem section_ext (Γ : QFGroup V T) (σ τ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ Γ.G)
    (h : toUnit (genPt V) ≫ σ = toUnit (genPt V) ≫ τ) : σ = τ := by
  haveI := Γ.separated
  haveI hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap V (FractionRing V)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))]
      exact bot_le)⟩
  have h' := congrArg Over.Hom.left h
  simp only [Over.comp_left, toUnit_genPt_left] at h'
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of V)) Γ.G.hom
    ((Over.w σ).trans (Over.w τ).symm)
    (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h')

theorem exists_pt_of_section (Γ : QFGroup V T) (σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ Γ.G) :
    ∃ t, toUnit (genPt V) ≫ σ = Γ.pt t := by
  let c := toUnit (genPt V) ≫ σ
  let x₀ : Spec (CommRingCat.of (FractionRing V)) := default
  have hover : ∀ c' : genPt V ⟶ Γ.G, c'.left ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := fun c' => Over.w c'
  have hgen : (Γ.G.hom (c.left x₀)).asIdeal = ⊥ := by
    have e : Γ.G.hom (c.left x₀) =
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) x₀ := by
      rw [← hover c]; rfl
    have hx₀ : x₀.asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top x₀.asIdeal).resolve_right x₀.isPrime.ne_top
    rw [e]
    change Ideal.comap (algebraMap V (FractionRing V)) x₀.asIdeal = ⊥
    rw [hx₀]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hgen
  refine ⟨t, Over.OverMorphism.ext ?_⟩
  exact point_ext Γ.G.hom _ _ (hover _) (hover _) x₀ x hx.symm

end GlobalTheory.CompanionTheory.Ar.BT.LateralTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

private theorem eq_specMap_comp_of_apply_eq {X : Scheme.{0}} {B K Ω : Type} [CommRing B] [Field K]
    [Field Ω] (h : X ⟶ Spec (CommRingCat.of B)) (β : B →+* K)
    (hβ : ∀ x : K, ∃ r u : B, β u ≠ 0 ∧ x * β u = β r)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ h = Spec.map (CommRingCat.ofHom β))
    (k : K →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ X)
    (hy : y ≫ h = Spec.map (CommRingCat.ofHom (k.comp β)))
    (a : Spec (CommRingCat.of Ω)) (b : Spec (CommRingCat.of K)) (hab : y a = s b) :
    y = Spec.map (CommRingCat.ofHom k) ≫ s := by
  have hpt : ∀ (L : Type) [Field L] (p q : Spec (CommRingCat.of L)), p = q := by
    intro L _ p q
    let p' : PrimeSpectrum L := p
    let q' : PrimeSpectrum L := q
    exact (PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p'.asIdeal).trans
      (Ideal.eq_bot_of_prime q'.asIdeal).symm) : p' = q')
  obtain ⟨W, hW, hbW, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (s b))
  haveI := hW.isOpenImmersion_fromSpec
  have hrange : ∀ {Y : Scheme.{0}} (e : Y ⟶ X) (z : Y), (∀ z', z' = z) → e z ∈ W →
      Set.range e ⊆ Set.range hW.fromSpec := by
    intro Y e z hz he
    rintro _ ⟨z', rfl⟩
    rw [hW.range_fromSpec, hz z']
    exact he
  have hyW := hrange y a (fun z' => hpt Ω z' a) (by rw [hab]; exact hbW)
  have hsW := hrange s b (fun z' => hpt K z' b) hbW
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec y hyW)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec s hsW)
  obtain ⟨α, hα⟩ := Spec.map_surjective (hW.fromSpec ≫ h)
  have hσβ : α ≫ σ = CommRingCat.ofHom β := Spec.map_injective (by
    rw [Spec.map_comp, hσ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hs])
  have hψβ : α ≫ ψ = CommRingCat.ofHom (k.comp β) := Spec.map_injective (by
    rw [Spec.map_comp, hψ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hy])
  have hpts : (Spec.map ψ) a = (Spec.map σ) b := by
    apply (Scheme.Hom.isOpenEmbedding hW.fromSpec).injective
    rw [← Scheme.Hom.comp_apply (Spec.map ψ) hW.fromSpec a,
      ← Scheme.Hom.comp_apply (Spec.map σ) hW.fromSpec b, hψ, hσ, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, hab]
  have hker : ∀ x, σ.hom x = 0 → ψ.hom x = 0 := by
    intro x hx
    let a' : PrimeSpectrum Ω := a
    let b' : PrimeSpectrum K := b
    have ha : a'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have hb : b'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have e := congrArg PrimeSpectrum.asIdeal hpts
    have hmem : x ∈ PrimeSpectrum.asIdeal ((Spec.map σ) b) := by
      rw [Spec.map_apply]
      change σ.hom x ∈ b'.asIdeal
      rw [hb, Ideal.mem_bot]
      exact hx
    rw [← e, Spec.map_apply] at hmem
    change ψ.hom x ∈ a'.asIdeal at hmem
    rwa [ha, Ideal.mem_bot] at hmem
  have hψσ : ψ = σ ≫ CommRingCat.ofHom k := by
    apply CommRingCat.hom_ext
    ext x
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    obtain ⟨r, u, hu, hxu⟩ := hβ (σ.hom x)
    have hσα : ∀ z, σ.hom (α.hom z) = β z := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hσβ, CommRingCat.hom_ofHom]
    have hψα : ∀ z, ψ.hom (α.hom z) = k (β z) := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hψβ, CommRingCat.hom_ofHom,
        RingHom.comp_apply]
    have h0 : ψ.hom (x * α.hom u - α.hom r) = 0 := hker _ (by
      rw [map_sub, map_mul, hσα, hσα, hxu, sub_self])
    rw [map_sub, map_mul, hψα, hψα, sub_eq_zero] at h0
    have hku : k (β u) ≠ 0 := (map_ne_zero k).mpr hu
    apply mul_right_cancel₀ hku
    rw [h0, ← map_mul, hxu]
  calc y = IsOpenImmersion.lift hW.fromSpec y hyW ≫ hW.fromSpec :=
        (IsOpenImmersion.lift_fac _ _ _).symm
    _ = Spec.map ψ ≫ hW.fromSpec := by rw [hψ]
    _ = Spec.map (CommRingCat.ofHom k) ≫ s := by
        rw [hψσ, Spec.map_comp, Category.assoc, hσ, IsOpenImmersion.lift_fac]

theorem QFGroup.exists_eq_comp_pt : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
    (Ω : Type) [Field Ω] (k : FractionRing R →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ Γ.G.left),
    y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) →
    ∃ t, y = Spec.map (CommRingCat.ofHom k) ≫ (Γ.pt t).left := by
  intro R _ _ T _ Γ
  cases Γ
  rename_i pt _ pt_onto _
  dsimp only
  intro Ω _ k y hy
  let a0 : Spec (CommRingCat.of Ω) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
  obtain ⟨t, x, hx⟩ := pt_onto (y a0) (by
    rw [← Scheme.Hom.comp_apply y _ a0, hy, Spec.map_apply]
    change Ideal.comap (k.comp (algebraMap R (FractionRing R))) (⊥ : Ideal Ω) = ⊥
    exact Ideal.comap_bot_of_injective _ (k.injective.comp (IsFractionRing.injective R (FractionRing R))))
  refine ⟨t, eq_specMap_comp_of_apply_eq _ (algebraMap R (FractionRing R)) ?_ (pt t).left
    (Over.w (pt t)) k y hy a0 x hx.symm⟩
  intro z
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) z
  exact ⟨n, d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hnd⟩

end GlobalTheory.CompanionTheory.Ar.BT
end
