module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Unc

noncomputable def valHom {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valHom x U h s = valAt x U h s := rfl

theorem valAt_restrict {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

theorem top_le_of_le {Y X : Scheme.{0}} (x : Y ⟶ X) {U V : X.Opens} (i : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ U := fun _ hz => i (hV hz)

theorem top_le_of_mem {K : Type} [Field K] {X : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens}
    (z : Spec (CommRingCat.of K)) (hz : x z ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := fun w _ => by
  have e : w = z := Subsingleton.elim (α := PrimeSpectrum K) w z
  subst e
  exact hz

theorem sec_inj : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 := by
  intro R _ _ T _ _ Γ U s hs
  have := Γ.flat
  have := Γ.gen_reduced
  have hdom : IsDominant (genPt R).hom :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap R (FractionRing R)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  have : IsSchemeTheoreticallyDominant (genPt R).hom := .of_isDominant _
  have : QuasiCompact (genPt R).hom :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  let j := pullback.fst Γ.G.hom (genPt R).hom
  apply j.app_injective U
  rw [map_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  intro z hz
  exfalso
  have hz' : j z ∈ Γ.G.left.basicOpen s := hz
  have hgen : (Γ.G.hom (j z)).asIdeal = ⊥ := by
    have e : Γ.G.hom (j z) = (genPt R).hom (pullback.snd Γ.G.hom (genPt R).hom z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rw [e]
    generalize pullback.snd Γ.G.hom (genPt R).hom z = w
    have hw : PrimeSpectrum.asIdeal (R := FractionRing R) w = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (PrimeSpectrum.isPrime (R := FractionRing R) w).ne_top
    change Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal (R := FractionRing R) w) = ⊥
    rw [hw]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hgen
  rw [← hx] at hz'
  have h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_mem _ x (Γ.G.left.basicOpen_le s hz')
  have h0 : (Γ.pt t).left.appLE U ⊤ h s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).1
    rw [map_zero]
    exact hs t h
  have h1 := Scheme.basicOpen_appLE (Γ.pt t).left ⊤ U h s
  rw [h0, Scheme.basicOpen_zero] at h1
  have h2 : x ∈ (⊤ : (genPt R).left.Opens) ⊓ (Γ.pt t).left ⁻¹ᵁ Γ.G.left.basicOpen s := ⟨trivial, hz'⟩
  rw [← h1] at h2
  exact h2

theorem reg_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t := by
  intro R _ _ T _ _ Γ U f
  refine ⟨fun h => ?_, fun ⟨s, hs⟩ g hg => ⟨U, hg, s, hs⟩⟩
  choose W hW s hs using fun g : U => h g.1 g.2
  let V : U → Γ.G.left.Opens := fun g => W g ⊓ U
  let sf : ∀ g : U, Γ(Γ.G.left, V g) := fun g =>
    (Γ.G.left.presheaf.map (homOfLE (inf_le_left : V g ≤ W g)).op).hom (s g)
  have hsf : ∀ (g : U) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V g), valAt (Γ.pt t).left (V g) h (sf g) = f t :=
    fun g t h => (valAt_restrict _ _ h (top_le_of_le _ inf_le_left h) _).trans (hs g t _)
  have hcomp : TopCat.Presheaf.IsCompatible Γ.G.left.sheaf.1 V sf := by
    intro a b
    have := sec_inj R T Γ (V a ⊓ V b)
      ((Γ.G.left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op).hom (sf a) -
        (Γ.G.left.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op).hom (sf b)) (fun t h => by
          rw [← valHom_apply, map_sub, valHom_apply, valHom_apply,
            valAt_restrict _ _ h (top_le_of_le _ inf_le_left h),
            valAt_restrict _ _ h (top_le_of_le _ inf_le_right h), hsf, hsf, sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨σ, hσ, -⟩ := Γ.G.left.sheaf.existsUnique_gluing' V U (fun g => homOfLE inf_le_right)
    (fun g hg => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, hg⟩, hW ⟨g, hg⟩, hg⟩) sf hcomp
  refine ⟨σ, fun t ht => ?_⟩
  let x : Spec (CommRingCat.of (FractionRing R)) := default
  let g : U := ⟨(Γ.pt t).left x, ht (Set.mem_univ x)⟩
  have hg : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V g := top_le_of_mem (Γ.pt t).left x ⟨hW g, g.2⟩
  exact (valAt_restrict _ (homOfLE (inf_le_right : V g ≤ U)) hg ht σ).symm.trans
    ((congrArg (valAt (Γ.pt t).left (V g) hg) (hσ g)).trans (hsf g t hg))

theorem finite_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  intro R _ _ X f U U' hU hU' x hx
  let x' : U.toScheme := ⟨x, hx⟩
  have hc : IsClosed ((U.ι ≫ f) '' closure {x'}) := (U.ι ≫ f).isClosedMap _ isClosed_closure
  have hs : (U.ι ≫ f) x' ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint (R := R) _
  obtain ⟨y, hy, e⟩ := hs.mem_closed hc ⟨x', subset_closure rfl, rfl⟩
  have h1 : U.ι x' ⤳ U.ι y := (specializes_iff_mem_closure.2 hy).map U.ι.continuous
  exact h1.mem_open U'.isOpen (hU' _ (by rw [← Scheme.Hom.comp_apply]; exact e))

end PositivityTheory.HtPt.Unc
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gsplit

theorem coprime_different (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) :
    IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨a, b, hab⟩ := (hpz.irreducible.coprime_iff_not_dvd).mpr hd
  rw [Ideal.isCoprime_iff_exists]
  refine ⟨(a : 𝓞 E) * p, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),
    (b : 𝓞 E) * (NumberField.discr E : 𝓞 E),
    Ideal.mul_mem_left _ _ (NumberField.discr_mem_differentIdeal E (𝓞 E)), ?_⟩
  have := congrArg (Int.cast : ℤ → 𝓞 E) hab
  push_cast at this
  exact this

theorem not_sq_dvd (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) (w : Ideal (𝓞 E)) (hw : w ≠ ⊤) :
    ¬ w ^ 2 ∣ Ideal.span {(p : 𝓞 E)} := by
  intro h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpz.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hdiff : w ^ (2 - 1) ∣ differentIdeal ℤ (𝓞 E) :=
    pow_sub_one_dvd_differentIdeal ℤ w 2 hne (by rw [hmap]; exact h)
  rw [show 2 - 1 = 1 from rfl, pow_one] at hdiff
  have hspan : w ∣ Ideal.span {(p : 𝓞 E)} := (dvd_pow_self w two_ne_zero).trans h
  exact hw (Ideal.isUnit_iff.mp
    ((PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd).isUnit_of_dvd' hspan hdiff))

theorem glue_split : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (w : Ideal (𝓞 E)) [w.IsPrime], (p : 𝓞 E) ∈ w → ∃ ε : 𝓞 E, ε - 1 ∈ w ∧ (∀ w' : Ideal (𝓞 E), w'.IsPrime → (p : 𝓞 E) ∈ w' → w' ≠ w → ε ∈ w') ∧ (∀ a : 𝓞 E, (p : 𝓞 E) ∣ ε * a ↔ a ∈ w) ∧ (p : 𝓞 E) ∣ ε * ε - ε ∧ IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  intro E hEf hEn p hp hd w hw hpw
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hwtop : w ≠ ⊤ := hw.ne_top
  have hwbot : w ≠ ⊥ := fun h => hp0 (by rw [h] at hpw; exact Ideal.mem_bot.mp hpw)
  have hmax : w.IsMaximal := hw.isMaximal hwbot
  obtain ⟨J, hJ⟩ : w ∣ Ideal.span {(p : 𝓞 E)} := Ideal.dvd_span_singleton.mpr hpw
  have hJw : ¬ J ≤ w := by
    intro hle
    apply PositivityTheory.HtPt.Gsplit.not_sq_dvd E p hp hd w hwtop
    rw [hJ, pow_two]
    exact mul_dvd_mul_left w (Ideal.dvd_iff_le.mpr hle)
  have hsup : w ⊔ J = ⊤ := by
    by_contra hne
    apply hJw
    have heq : w ⊔ J = w := by
      by_contra h'
      exact hne (hmax.out.2 _ (lt_of_le_of_ne le_sup_left (Ne.symm h')))
    exact le_sup_right.trans heq.le
  have h1 : (1 : 𝓞 E) ∈ w ⊔ J := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨x, hx, ε, hε, hxε⟩ := Submodule.mem_sup.mp h1
  have hε1 : ε - 1 ∈ w := by
    have heq : ε - 1 = -x := by
      rw [← hxε]
      ring
    rw [heq]
    exact w.neg_mem hx
  have hεw : ε ∉ w := fun h => hwtop ((Ideal.eq_top_iff_one w).mpr (by
    have h2 := w.sub_mem h hε1
    simpa using h2))
  have hmemI : ∀ b, (p : 𝓞 E) ∣ b ↔ b ∈ w * J := by
    intro b
    rw [← Ideal.mem_span_singleton, hJ]
  refine ⟨ε, hε1, ?_, ?_, ?_, PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd⟩
  · intro w' hw' hpw' hne
    have hle : w * J ≤ w' := by
      rw [← hJ, Ideal.span_singleton_le_iff_mem]
      exact hpw'
    rcases hw'.mul_le.mp hle with h | h
    · exact absurd (hmax.eq_of_le hw'.ne_top h).symm hne
    · exact h hε
  · intro a
    rw [hmemI]
    constructor
    · intro h
      have hle' : w * J ≤ w := Ideal.mul_le_left
      have hw1 : ε * a ∈ w := hle' h
      rcases hw.mem_or_mem hw1 with h' | h'
      · exact absurd h' hεw
      · exact h'
    · intro ha
      rw [mul_comm ε a]
      exact Ideal.mul_mem_mul ha hε
  · rw [hmemI]
    have heq : ε * ε - ε = (ε - 1) * ε := by ring
    rw [heq]
    exact Ideal.mul_mem_mul hε1 hε

end PositivityTheory.HtPt.Gsplit
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Teich

theorem eq_of_pow_eq_self {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] (q : ℕ)
    (hq : (q : IsLocalRing.ResidueField O) = 0) {x y : O} (hx : x ^ q = x) (hy : y ^ q = y)
    (h : IsLocalRing.residue O x = IsLocalRing.residue O y) : x = y := by
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hgeom := geom_sum₂_mul x y q
  rw [hx, hy] at hgeom
  have hS : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) = 1 := by
    have hmul : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) * (x - y) = 1 * (x - y) := by
      rw [hgeom, one_mul]
    exact mul_right_cancel₀ hsub hmul
  have hres := congrArg (IsLocalRing.residue O) hS

  rw [map_sum, map_one] at hres
  simp only [map_mul, map_pow, ← h] at hres
  rw [geom_sum₂_self, hq, zero_mul] at hres
  exact zero_ne_one hres

theorem card_eq_zero {O : Type} [CommRing O] [IsLocalRing O] {F : Type} [Field F] [Fintype F]
    (σ : F →+* IsLocalRing.ResidueField O) :
    ((Fintype.card F : ℕ) : IsLocalRing.ResidueField O) = 0 := by
  rw [← map_natCast σ, FiniteField.cast_card_eq_zero, map_zero]

theorem exists_lift {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {F : Type} [Field F]
    [Fintype F] (ζ : O) (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1))
    (σ : F →+* IsLocalRing.ResidueField O) (a : F) :
    ∃ x : O, x ^ Fintype.card F = x ∧ IsLocalRing.residue O x = σ a := by
  have hQ1 : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 := ⟨Fintype.card F - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel] at hζ
  haveI : NeZero m := ⟨by omega⟩
  have hQres := PositivityTheory.HtPt.Teich.card_eq_zero (O := O) σ
  have hfix : ∀ k : ℕ, (ζ ^ k) ^ Fintype.card F = ζ ^ k := by
    intro k
    rw [hm, pow_succ, ← pow_mul, mul_comm k m, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hprim : IsPrimitiveRoot (IsLocalRing.residue O ζ) m := by
    refine ⟨?_, ?_⟩
    · rw [← map_pow, hζ.pow_eq_one, map_one]
    · intro l hl
      apply hζ.dvd_of_pow_eq_one
      apply PositivityTheory.HtPt.Teich.eq_of_pow_eq_self _ hQres (hfix l) (one_pow _)
      rw [map_pow, hl, map_one]
  by_cases ha : a = 0
  · refine ⟨0, zero_pow (by omega), ?_⟩
    rw [ha, map_zero, map_zero]
  · have hpow := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hm, Nat.add_sub_cancel] at hpow
    have h1 : (σ a) ^ m = 1 := by rw [← map_pow, hpow, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one h1
    exact ⟨ζ ^ i, hfix i, by rw [map_pow, hi]⟩

theorem glue_teich : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ σ : F →+* IsLocalRing.ResidueField O, (∃! χ : F →*₀ O, ∀ a, IsLocalRing.residue O (χ a) = σ a) ∧ ∀ (σ' : F →+* IsLocalRing.ResidueField O) (χ χ' : F →*₀ O), (∀ a, σ' a = σ a ^ p) → (∀ a, IsLocalRing.residue O (χ a) = σ a) → (∀ a, IsLocalRing.residue O (χ' a) = σ' a) → ∀ a, χ' a = χ a ^ p := by
  intro O _ _ _ F _ _ p _ _ ζ hζ σ
  have hQ : ((Fintype.card F : ℕ) : IsLocalRing.ResidueField O) = 0 :=
    PositivityTheory.HtPt.Teich.card_eq_zero σ
  have huniq : ∀ {x y : O}, x ^ Fintype.card F = x → y ^ Fintype.card F = y →
      IsLocalRing.residue O x = IsLocalRing.residue O y → x = y :=
    fun hx hy h => PositivityTheory.HtPt.Teich.eq_of_pow_eq_self _ hQ hx hy h
  have hfixχ : ∀ (χ : F →*₀ O) (a : F), χ a ^ Fintype.card F = χ a := fun χ a => by
    rw [← map_pow, FiniteField.pow_card]
  refine ⟨?_, ?_⟩
  · choose L hL hLres using PositivityTheory.HtPt.Teich.exists_lift ζ hζ σ
    let χ : F →*₀ O :=
      { toFun := L
        map_zero' := huniq (hL 0) (zero_pow Fintype.card_ne_zero) (by rw [hLres, map_zero, map_zero])
        map_one' := huniq (hL 1) (one_pow _) (by rw [hLres, map_one, map_one])
        map_mul' := fun a b => huniq (hL (a * b)) (by rw [mul_pow, hL a, hL b])
          (by rw [hLres, map_mul, map_mul, hLres, hLres]) }
    refine ⟨χ, hLres, fun χ' hχ' => ?_⟩
    exact MonoidWithZeroHom.ext fun a => huniq (hfixχ χ' a) (hL a) ((hχ' a).trans (hLres a).symm)
  · intro σ' χ χ' hσ' hχ hχ' a
    refine huniq (hfixχ χ' a) (by rw [← pow_mul, mul_comm p, pow_mul, hfixχ χ a]) ?_
    rw [hχ', hσ', map_pow, hχ]

end PositivityTheory.HtPt.Teich
end
