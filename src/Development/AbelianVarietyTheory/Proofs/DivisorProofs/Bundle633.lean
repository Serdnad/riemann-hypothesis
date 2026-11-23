module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle010
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def ActsAs {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g : G ⟶ G) : Prop :=
  ∀ e : ℕ, (Over.pullback (thick R I e)).map g ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map b ∧
    ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X,
      TorusEndOf D.toPre.X h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map g = t ≫ (U.gt e).i

theorem pull_padd {S S' : Scheme.{0}} (f : S' ⟶ S) {T G : Over S} [GrpObj G] (a b : T ⟶ G) :
    (Over.pullback f).map (padd G a b) = padd _ ((Over.pullback f).map a) ((Over.pullback f).map b) := by
  simp [padd, Functor.Monoidal.lift_μ_assoc]

theorem comp_padd' {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (x : T ⟶ T') (a b : T' ⟶ G) :
    x ≫ padd G a b = padd G (x ≫ a) (x ≫ b) := by
  rw [padd, padd, comp_lift_assoc]

theorem padd_comp_hom {S : Scheme.{0}} {X Y T : Over S} [GrpObj X] [GrpObj Y] (f f' : T ⟶ X) (h : X ⟶ Y) [IsMonHom h] :
    padd X f f' ≫ h = padd Y (f ≫ h) (f' ≫ h) := by
  rw [padd, padd, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem torusEndOf_padd {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h h' : X → X}
    {t t' : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X h t) (ht' : TorusEndOf X h' t') :
    TorusEndOf X (h + h') (padd _ t t') := by
  rw [GlobalTheory.LinearUnifCheck.torusEndOf_iff] at ht ht' ⊢
  intro χ
  have hc : ∀ x, (charUnit S X x).val =
      (GlobalTheory.splitTorusPointsEquiv S X (splitTorus S X) (𝟙 _) (Multiplicative.ofAdd x)).val := fun x =>
    ((GlobalTheory.splitTorusPointsEquiv_val S X _ (𝟙 _) x).trans (SplitTorusHom.appTop_id _)).symm
  have hp : padd (splitTorus S X) t t' = t * t' := rfl
  rw [hp, ← GlobalTheory.splitTorusPointsEquiv_val, map_mul, MonoidHom.mul_apply, Units.val_mul,
    GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val, ht, ht', hc, hc, hc, Pi.add_apply, ofAdd_add,
    map_mul, Units.val_mul]

theorem actsAs_padd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A} {h h' : D.toPre.X → D.toPre.X} {g g' : G ⟶ G}
    (hg : ActsAs U b h g) (hg' : ActsAs U b' h' g') : ActsAs U (padd _ b b') (h + h') (padd G g g') := by
  intro e
  obtain ⟨q1, t, ht, i1⟩ := hg e
  obtain ⟨q2, t', ht', i2⟩ := hg' e
  have := (U.gt e).q_hom
  have := (U.gt e).i_hom
  refine ⟨?_, padd _ t t', torusEndOf_padd ht ht', ?_⟩
  · rw [pull_padd, pull_padd, padd_comp_hom, q1, q2, comp_padd']
  · rw [pull_padd, comp_padd', i1, i2, padd_comp_hom]

theorem actsAs_comp {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A} {h h' : D.toPre.X → D.toPre.X} {g g' : G ⟶ G}
    (hg : ActsAs U b h g) (hg' : ActsAs U b' h' g') : ActsAs U (b ≫ b') (h ∘ h') (g ≫ g') := by
  intro e
  obtain ⟨q1, t, ht, i1⟩ := hg e
  obtain ⟨q2, t', ht', i2⟩ := hg' e
  refine ⟨?_, t ≫ t', GlobalTheory.LinearUnifCheck.torusEndOf_comp ht ht', ?_⟩
  · rw [Functor.map_comp, Category.assoc, q2, ← Category.assoc, q1, Category.assoc, ← Functor.map_comp]
  · rw [Functor.map_comp, ← Category.assoc, i1, Category.assoc, i2, Category.assoc]

theorem actsAs_id {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) : ActsAs U (𝟙 _) id (𝟙 G) := by
  intro e
  refine ⟨by simp, 𝟙 _, ?_, by simp⟩
  rw [GlobalTheory.LinearUnifCheck.torusEndOf_iff]; intro χ; simp

end GlobalTheory.Mum
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.KerIdeal

theorem exists_ideal_factor_iff {X Y Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y)
    (x₀ : X) :
    ∃ J : Ideal (X.presheaf.stalk x₀), ∀ (R' : Type) [CommRing R'] (ψ : X.presheaf.stalk x₀ →+* R'),
      (∃ z : Spec (CommRingCat.of R') ⟶ Z,
        z ≫ i = (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x₀) ≫ f) ↔
        J ≤ RingHom.ker ψ := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := pullback.snd i (X.fromSpecStalk x₀ ≫ f))).1
    inferInstance
  refine ⟨I, fun R' _ ψ => ?_⟩
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ : ∃ w : Spec (CommRingCat.of R') ⟶ pullback i (X.fromSpecStalk x₀ ≫ f),
        w ≫ pullback.fst i (X.fromSpecStalk x₀ ≫ f) = z ∧
          w ≫ pullback.snd i (X.fromSpecStalk x₀ ≫ f) = Spec.map (CommRingCat.ofHom ψ) :=
      ⟨pullback.lift z (Spec.map (CommRingCat.ofHom ψ)) (hz.trans (Category.assoc _ _ _)),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [he, ← Category.assoc] at hw
    set w' := w ≫ e.hom
    have h3 : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ Spec.preimage w' = CommRingCat.ofHom ψ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact hw
    intro a ha
    rw [RingHom.mem_ker]
    have h4 := congrArg (fun u : _ ⟶ CommRingCat.of R' => u.hom a) h3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at h4
    exact h4.symm
  · intro hI
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun a ha => hI ha))) ≫ e.inv ≫
      pullback.fst i (X.fromSpecStalk x₀ ≫ f), ?_⟩
    have key : Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun a ha => hI ha))) ≫ e.inv ≫
        pullback.snd i (X.fromSpecStalk x₀ ≫ f) = Spec.map (CommRingCat.ofHom ψ) := by
      rw [he, e.inv_hom_id_assoc, ← Spec.map_comp]
      congr 1
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% key]

end GlobalTheory.KerIdeal

namespace GlobalTheory.KerIdeal

theorem kernel_ideal : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj B] (π : A ⟶ B), IsAbelianScheme B → ∀ x₀ : A.left,
    ∃ J : Ideal (A.left.presheaf.stalk x₀), ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      (∃ z : Sp R' ⟶ Sp k, z ≫ (η[B]).left = (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ≫ π.left) ↔
        J ≤ RingHom.ker ψ := by
  intro k _ A B _ π _ x₀
  haveI : IsClosedImmersion (η[B]).left := isClosedImmersion_of_comp_eq_id (Y := Sp k) B.hom _ (Over.w _)
  exact exists_ideal_factor_iff (η[B]).left π.left x₀

end GlobalTheory.KerIdeal
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbEnd

theorem isFinite_of_isFinite_geomFibres :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  intro S A _ hA φ hgeo
  haveI : IsProper A.hom := hA.proper
  haveI : IsProper (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  haveI : IsProper φ.left := IsProper.of_comp φ.left A.hom
  haveI : LocallyQuasiFinite φ.left := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton φ.left fun y => ?_
    let K := AlgebraicClosure (A.left.residueField y)
    let u : Spec (CommRingCat.of K) ⟶ A.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (A.left.residueField y) K)) ≫
        A.left.fromSpecResidueField y
    let t := u ≫ A.hom
    haveI := hgeo K t
    let φ' := ((Over.pullback t).map φ).left
    let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
    have hup : u p = y := Scheme.fromSpecResidueField_apply y _
    let v : Spec (CommRingCat.of K) ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
    refine ((φ'.finite_preimage_singleton (v p)).image (pullback.fst A.hom t)).subset fun x hx => ?_
    have hx' : φ.left x = u p := by rw [hup]; exact hx
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := u) x p hx'
    let m : pullback φ.left u ⟶ pullback A.hom t :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
        rw [← Over.w φ, ← Category.assoc, pullback.condition, Category.assoc])
    have hm1 : m ≫ pullback.fst A.hom t = pullback.fst _ _ := pullback.lift_fst _ _ _
    have hφ1 : φ' ≫ pullback.fst A.hom t = pullback.fst A.hom t ≫ φ.left :=
      (GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ).w.symm
    have hφ2 : φ' ≫ pullback.snd A.hom t = pullback.snd A.hom t := pullback.lift_snd _ _ _
    have hmv : m ≫ φ' = pullback.snd φ.left u ≫ v := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφ1, ← Category.assoc, hm1, Category.assoc, pullback.lift_fst, pullback.condition]
      · rw [Category.assoc, hφ2, pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    refine ⟨m w, ?_, ?_⟩
    · change φ' (m w) = v p
      rw [← Scheme.Hom.comp_apply, hmv, Scheme.Hom.comp_apply, hw2]
    · rw [← Scheme.Hom.comp_apply, hm1, hw1]
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ.left

end GlobalTheory.AbEnd
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Pointwise

namespace GlobalTheory.GoodMultipleLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coprime_M_N {M d : ℕ} (hM : M ≠ 0) (hd : d.Prime) (hd2 : d ≠ 2) :
    Nat.Coprime M ((2 * (M / d ^ M.factorization d)) ^ 2 + d) := by
  set c := M / d ^ M.factorization d with hc
  have hnc : ¬ d ∣ c := Nat.not_dvd_ordCompl hd hM
  have hmul : d ^ M.factorization d * c = M := Nat.ordProj_mul_ordCompl_eq_self M d
  apply Nat.coprime_of_dvd
  intro q hq hqM hqN
  have hqd : q ∣ d → q = d := fun h => (Nat.prime_dvd_prime_iff_eq hq hd).1 h
  by_cases hqc : q ∣ c
  · have h1 : q ∣ (2 * c) ^ 2 := Dvd.dvd.pow (Dvd.dvd.mul_left hqc 2) two_ne_zero
    have h2 : q ∣ d := (Nat.dvd_add_right h1).1 hqN
    exact hnc (hqd h2 ▸ hqc)
  · rw [← hmul] at hqM
    have h1 : q ∣ d ^ M.factorization d := ((Nat.Prime.dvd_mul hq).1 hqM).resolve_right hqc
    have h2 := hqd (hq.dvd_of_dvd_pow h1)
    subst h2
    have h3 : q ∣ (2 * c) ^ 2 := (Nat.dvd_add_left (dvd_refl q)).1 hqN
    have h4 := (Nat.Prime.dvd_mul hq).1 (hq.dvd_of_dvd_pow h3)
    rcases h4 with h | h
    · exact hd2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
    · exact hnc h

theorem exists_good_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H),
    ∃ l₂ : Level H, l.Dvd l₂ ∧ l₂.A = l.A ∧ ∀ q : ℕ, q.Prime → l₂.GoodAt q := by
  intro E _ _ _ H l
  have hdm := H.d_mod
  have hdp := H.d_prime
  have hM3 := l.three_le
  have hM0 : l.M ≠ 0 := by omega
  set c := l.M / H.d ^ l.M.factorization H.d with hc
  set a : ℕ := 2 * c with ha
  set N : ℕ := a ^ 2 + H.d with hN
  have hcop : Nat.Coprime l.M N := coprime_M_N hM0 hdp (by omega)
  have hdodd : Odd H.d := Nat.odd_iff.mpr (by omega)
  have hNodd : Odd N := Even.add_odd ⟨2 * c ^ 2, by rw [ha]; ring⟩ hdodd
  have hN3 : 3 ≤ N := by omega
  have hcd : Nat.Coprime a H.d := by
    rw [ha]
    refine Nat.Coprime.mul_left (Nat.coprime_two_left.mpr hdodd) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hdp).2 (Nat.not_dvd_ordCompl hdp hM0)).symm
  set α : 𝓞 E := (a : 𝓞 E) + H.rt with hα
  have hαb : H.bar α = (a : 𝓞 E) - H.rt := by
    rw [hα, map_add (f := _), map_natCast, GlobalTheory.HostModel.bar_rt, sub_eq_add_neg]
  have hnorm : α * ((a : 𝓞 E) - H.rt) = (N : 𝓞 E) := GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H a
  have hαα : IsCoprime α ((a : 𝓞 E) - H.rt) := GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hcd hNodd
  have hαmem : α ∈ Algebra.adjoin ℤ {H.w0} := add_mem (natCast_mem _ a) (GlobalTheory.HostModel.rt_mem_adjoin H)
  have hmapI : (Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.map_span, Set.image_singleton]; exact congrArg _ (congrArg _ hαb)
  have hmapM : (l.Mb * Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.map_mul, hmapI]
  have hMN : Ideal.span {(l.M : 𝓞 E)} ⊔ Ideal.span {(N : 𝓞 E)} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact Nat.Coprime.cast hcop
  have hMle : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := by rw [← l.prod]; exact Ideal.mul_le_left
  have hMle' : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [← l.prod]; exact Ideal.mul_le_right
  have hNle : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {α} := by
    rw [Ideal.span_singleton_le_span_singleton, ← hnorm]; exact dvd_mul_right _ _
  have hNle' : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.span_singleton_le_span_singleton, ← hnorm]; exact dvd_mul_left _ _
  have c1 : IsCoprime l.Mb (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.isCoprime_iff_sup_eq.2 l.coprime
  have c2 : IsCoprime l.Mb (Ideal.span {(a : 𝓞 E) - H.rt}) := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]; exact sup_le_sup hMle hNle'
  have c3 : IsCoprime (Ideal.span {α}) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]
    exact sup_le (le_sup_of_le_right hMle') (le_sup_of_le_left hNle)
  have c4 : IsCoprime (Ideal.span {α}) (Ideal.span {(a : 𝓞 E) - H.rt}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 hαα
  have hspan : l.Mb * Ideal.span {α} = Ideal.span ({x | x ∈ l.Mb ∧ x ∈ Algebra.adjoin ℤ {H.w0}} * ({α} : Set (𝓞 E))) := by
    conv_lhs => rw [l.fromK]
    exact Ideal.span_mul_span' _ _
  let l₂ : Level H :=
    { M := l.M * N
      three_le := by nlinarith
      odd := l.odd.mul hNodd
      Mb := l.Mb * Ideal.span {α}
      fromK := by
        refine le_antisymm ?_ (Ideal.span_le.2 fun x hx => hx.1)
        refine (le_of_eq hspan).trans (Ideal.span_mono ?_)
        rintro x ⟨s, hs, t, ht, rfl⟩
        rw [Set.mem_singleton_iff] at ht
        subst ht
        refine ⟨?_, mul_mem hs.2 hαmem⟩
        exact Ideal.mul_mem_mul hs.1 (Ideal.mem_span_singleton_self _)
      prod := by
        rw [hmapM]
        calc l.Mb * Ideal.span {α} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * Ideal.span {(a : 𝓞 E) - H.rt})
            = (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) * (Ideal.span {α} * Ideal.span {(a : 𝓞 E) - H.rt}) := by ring
          _ = Ideal.span {((l.M * N : ℕ) : 𝓞 E)} := by
            rw [l.prod, Ideal.span_singleton_mul_span_singleton, hnorm,
              Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]
      coprime := by
        rw [hmapM, ← Ideal.isCoprime_iff_sup_eq]
        exact (c1.mul_right c2).mul_left (c3.mul_right c4)
      A := l.A
      A_pos := l.A_pos }
  refine ⟨l₂, ⟨dvd_mul_right _ _, Ideal.mul_le_left, dvd_refl _⟩, rfl, fun q hq => ?_⟩
  exact GlobalTheory.GlobalModelGuards.goodAt_of_coprime l₂ l.M N hM3 hN3 hcop rfl q hq

end GlobalTheory.GoodMultipleLevel
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem rigUnit_exists_ratio {X Y : Scheme.{0}} (M : LB X) (hM : M.IsLB) (f : Y ⟶ X)
    (t t' : LB.Gen (M.pull f)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → M.ι), r z ∈ (M.pull f).U j →
      gm r z ((M.pull f).U j) (t.s j) = gm r z ⊤ w * gm r z ((M.pull f).U j) (t'.s j) := by
  obtain ⟨w, hw⟩ := glue_unit (X := Y) ⊤ (fun j : PUnit → M.ι => (M.pull f).U j) (fun _ => le_top)
    (fun y _ => by
      obtain ⟨i, hi⟩ := exists_chart hM (f y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩)
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      have h1 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      have h2 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht' (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 ((map_inv _ _).trans (congrArg (·⁻¹) h2)))).trans
        (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_inv _ _))).symm)
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rfl)
  refine ⟨w, fun Z r z j hj => ?_⟩
  have e := (gm_res r z (le_top : (M.pull f).U j ≤ ⊤) hj w).symm.trans (congrArg (gm r z _) (hw j))
  rw [e, map_mul, map_inv, inv_mul_cancel_right]

theorem rigUnit_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → ∀ (eA : Sp K ⟶ pullback X.hom (spMap (algebraMap R K))), eA ≫ pullback.fst X.hom (spMap (algebraMap R K)) = spMap (algebraMap R K) ≫ e → ∀ (M : LB X.left) (rig : LB.Gen (M.pull e)) (c : LB.Gen (M.pull (pullback.fst X.hom (spMap (algebraMap R K))))), M.IsLB → rig.IsGen → LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ c eA) (LB.pullGen M _ _ rig (spMap (algebraMap R K))) → ∀ (a : Kˣ) (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ pullback X.hom (spMap (algebraMap R K))) (z : Z), pullback.fst X.hom (spMap (algebraMap R K)) (r z) ∈ M.U i → (gm (r ≫ pullback.fst X.hom (spMap (algebraMap R K))) z (M.U i) (u.s i)).val = gs (r ≫ pullback.snd X.hom (spMap (algebraMap R K))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull (pullback.fst X.hom (spMap (algebraMap R K)))).U fun _ => i) (c.s fun _ => i)).val) → ∃ b : Rˣ, algebraMap R K (b : R) = (a : K) := by
  intro R K _ _ _ _ _ X e he eA heA M rig c hM hrig hcorr a u hu H
  obtain ⟨w, hw⟩ := rigUnit_exists_ratio M hM e (LB.genPull M u e) rig (LB.isGen_genPull M u hu e) hrig
  haveI : Epi (CommRingCat.ofHom (algebraMap R K)) := by
    have := IsLocalization.epi (nonZeroDivisors R) K
    exact this
  haveI : Mono (spMap (algebraMap R K)) := by
    exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op))
  have hsnd : eA ≫ pullback.snd X.hom (spMap (algebraMap R K)) = 𝟙 _ := by
    rw [← cancel_mono (spMap (algebraMap R K)), Category.assoc, ← pullback.condition, ← Category.assoc, heA,
      Category.assoc, he, Category.comp_id, Category.id_comp]
  let z : Sp K := (⊥ : PrimeSpectrum K)
  choose J hJ using fun χ : Sp K ⟶ X.left => exists_chart hM (χ z)
  have hG : Good M z J := hJ
  have hv := val_corr hG hcorr (𝟙 _)
  rw [val_pull hG, val_pull hG, Category.id_comp, Category.id_comp,
    val_of (L := M) c eA z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => by rw [heA]),
    val_of (L := M) rig _ z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => rfl)] at hv
  have hi := hJ (spMap (algebraMap R K) ≫ e)
  generalize J (spMap (algebraMap R K) ≫ e) = i at hv hi
  have h1 := H i _ eA z (by
    have : (eA ≫ pullback.fst X.hom (spMap (algebraMap R K))) z ∈ M.U i := by rw [heA]; exact hi
    exact this)
  rw [heA, hsnd] at h1
  have hm : spMap (algebraMap R K) z ∈ (M.pull e).U (fun _ => i) := mem_pull.2 hi
  have h2 := hw _ (spMap (algebraMap R K)) z (fun _ => i) hm
  have h3 : gm (spMap (algebraMap R K)) z ((M.pull e).U (fun _ => i)) ((LB.genPull M u e).s (fun _ => i)) =
      gm (spMap (algebraMap R K) ≫ e) z (M.U i) (u.s i) :=
    (gm_res _ z _ hm _).trans (gm_pull _ e z _ hi _)
  have h4 : (gm (spMap (algebraMap R K)) z ⊤ w).val =
      gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
    have h5 := (congrArg Units.val (h2.symm.trans h3)).trans (h1.trans (congrArg (_ * ·) (congrArg Units.val hv)))
    rw [Units.val_mul] at h5
    exact (Units.mul_left_inj _).1 h5
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, ?_⟩
  let φ : K →+* (Sp K).presheaf.stalk z :=
    ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  apply φ.injective
  rw [gm_val _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at h4
  refine Eq.trans ?_ h4
  change ((Sp K).presheaf.germ ⊤ z trivial).hom _ = ((Sp K).presheaf.germ ⊤ z trivial).hom _
  congr 1
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Iso.hom_inv_id_apply] at n
  exact n

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev ptR (χ : D.X) : Spec (CommRingCat.of R) ⟶ D.P.A.left :=
  (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ D.c χ).left

def unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) :
    (FractionRing R)ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
    (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).toMonoidHom

def Reads (κ : D.X → (FractionRing R)ˣ) : Prop :=
  ∃ g : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptR D χ) (fun _ => -1)),
    (∀ χ, (g χ).IsGen) ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi χ) r z J = unitAt r z (κ χ) * val (g χ) (r ≫ jK R) z J

def lead {X : Type} [AddCommGroup X] (κ : X → (FractionRing R)ˣ) (k : ℕ) (α mu : X) : (FractionRing R)ˣ :=
  κ mu ^ k * (κ (mu + α) * (κ mu)⁻¹ * (κ α)⁻¹)

end GlobalTheory.ThFam
end
end
