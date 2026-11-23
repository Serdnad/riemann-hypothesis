module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInTraceArc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle077
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle131
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalConjLabels

variable {R : Type} [CommRing R] [IsDomain R]

theorem spMap_jFK (f : Kb R →ₐ[FractionRing R] Kb R) :
    spMap f.toRingHom ≫ jFK (R := R) (Kb R) = jFK (R := R) (Kb R) := by
  rw [spMap, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) f.comp_algebraMap

def tauHom (f : Kb R →ₐ[FractionRing R] Kb R) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap f.toRingHom) (spMap_jFK f)

theorem tauHom_left (f : Kb R →ₐ[FractionRing R] Kb R) : (tauHom f).left = spMap f.toRingHom := rfl

theorem tauHom_comp_eq_id (f g : Kb R →ₐ[FractionRing R] Kb R) (h : ∀ a, f (g a) = a) :
    tauHom f ≫ tauHom g = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.id_left, tauHom_left, tauHom_left, spMap, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have e : f.toRingHom.comp g.toRingHom = RingHom.id _ := RingHom.ext h
  rw [e, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem map_unitOn' {k k' : Type} [CommRing k] [CommRing k'] (σ : k →+* k') (u : kˣ) :
    Units.map (spMap σ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map σ.toMonoidHom u) :=
  Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))).symm

end GlobalTheory.Mum.GalConjLabels

namespace GlobalTheory.Mum


open GalConjLabels in
theorem labTors_galConj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) (k : ℕ), 1 ≤ k → ∀ (x x' : QkPt D.toPre (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D.toPre A k x → (∀ p p', QkExt σ.toRingHom p p' → (x' p').left = spMap σ.toRingHom ≫ (x p).left) → LabTors D.toPre A k x' := by
  intro R _ _ _ hR D A σ k hk x x' hx hxx'
  haveI : CharZero R := hR.2
  haveI : IsNoetherianRing R := hR.1.1
  have hB := D.tau_bimult
  have hL := GlobalTheory.allSixLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hbij : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let e := AlgEquiv.ofBijective σ hbij
  let ρ : Kb R →ₐ[FractionRing R] Kb R := e.symm.toAlgHom
  have hσρ : ∀ a, σ (ρ a) = a := fun a => e.apply_symm_apply a
  have hρσ : ∀ a, ρ (σ a) = a := fun a => e.symm_apply_apply a
  have hfσ : σ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    σ.comp_algebraMap
  have hfρ : ρ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    ρ.comp_algebraMap
  haveI : CharZero (Kb R) :=
    (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  have hk0 : (k : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have rev : ∀ {p p' : QkPt D.toPre (Kb R) k}, QkExt σ.toRingHom p p' → QkExt ρ.toRingHom p' p := by
    intro p p' h
    obtain ⟨q, hq⟩ := GlobalTheory.QkClosure.exists_qkExt ρ.toRingHom hfρ p'
    have h2 := GlobalTheory.LevelField.qkExt_trans h hq
    have eid : ρ.toRingHom.comp σ.toRingHom = RingHom.id _ := RingHom.ext hρσ
    rw [eid] at h2
    have := GlobalTheory.QkClosure.qkExt_unique (RingHom.id (Kb R)) (RingHom.id_comp _) h2 (GlobalTheory.LabExt.qkExt_refl p)
    rwa [this] at hq
  have desc : ∀ p' : QkPt D.toPre (Kb R) k, ∃ p, QkExt σ.toRingHom p p' := fun p' =>
    GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom hfσ hk0 p'
  have hx'eq : ∀ p p', QkExt σ.toRingHom p p' → x' p' = tauHom σ ≫ x p := fun p p' h =>
    Over.OverMorphism.ext (hxx' p p' h)
  have cσρ : tauHom σ ≫ tauHom ρ = 𝟙 _ := tauHom_comp_eq_id σ ρ hσρ
  have cρσ : tauHom ρ ≫ tauHom σ = 𝟙 _ := tauHom_comp_eq_id ρ σ hρσ
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  refine ⟨fun y hy => ?_, fun p' => ?_, fun p' q' => ?_, fun p' q' r' hadd => ?_, fun p' q' z => ?_⟩
  · obtain ⟨p, hp⟩ := h1 (tauHom ρ ≫ y) (by rw [← comp_pow, hy, comp_one])
    obtain ⟨p', hp'⟩ := GlobalTheory.QkClosure.exists_qkExt σ.toRingHom hfσ p
    exact ⟨p', by rw [hx'eq p p' hp', hp, ← Category.assoc, cσρ, Category.id_comp]⟩
  · obtain ⟨p, hp⟩ := desc p'
    rw [hx'eq p p' hp, ← comp_pow, h2, comp_one]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    rw [hx'eq p p' hp, hx'eq q q' hq]
    constructor
    · intro h
      have h' : x p = x q := by
        have := congrArg (tauHom ρ ≫ ·) h
        simpa only [← Category.assoc, cρσ, Category.id_comp] using this
      exact GlobalTheory.TorusExt.equiv_of_qkExt hB σ.toRingHom hfσ hp hq ((h3 p q).1 h')
    · intro h
      rw [(h3 p q).2 (GlobalTheory.TorusExt.equiv_of_qkExt hB ρ.toRingHom hfρ (rev hp) (rev hq) h)]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    obtain ⟨r, hr⟩ := desc r'
    rw [hx'eq p p' hp, hx'eq q q' hq, hx'eq r r' hr,
      h4 p q r (GlobalTheory.TorusExt.qkAdd_of_qkExt hB ρ.toRingHom hfρ (rev hp) (rev hq) (rev hr) hadd), comp_mul]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    let z₀ : (Kb R)ˣ := Units.map ρ.toRingHom.toMonoidHom z
    have hz : Units.map σ.toRingHom.toMonoidHom z₀ = z := Units.ext (hσρ z)
    rw [hx'eq p p' hp, hx'eq q q' hq]
    constructor
    · intro hW
      have w₀ : WeilQkIs D.toPre (Kb R) k p q (z₀ : Kb R) := by
        have := GlobalTheory.ArcOfModel.weilQkIs_qkExt hL.1 hL.2.1 D.psi_even hB ρ.toRingHom hfρ k hk p' q' z hW
        rwa [← (GlobalTheory.TorusExt.qkExt_iff hB ρ.toRingHom hfρ _ _).1 (rev hp),
          ← (GlobalTheory.TorusExt.qkExt_iff hB ρ.toRingHom hfρ _ _).1 (rev hq)] at this
      have := GlobalTheory.CommPairing.weilIs_pull hG A.isAb A.isLB (tauHom σ) ((h5 p q z₀).1 w₀)
      rwa [tauHom_left, map_unitOn', hz] at this
    · intro hW
      have := GlobalTheory.CommPairing.weilIs_pull hG A.isAb A.isLB (tauHom ρ) hW
      rw [tauHom_left, map_unitOn', ← Category.assoc, ← Category.assoc, cρσ, Category.id_comp,
        Category.id_comp] at this
      have w₀ := GlobalTheory.ArcOfModel.weilQkIs_qkExt hL.1 hL.2.1 D.psi_even hB σ.toRingHom hfσ k hk p q _
        ((h5 p q z₀).2 this)
      rw [← (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hfσ _ _).1 hp,
        ← (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hfσ _ _).1 hq] at w₀
      have e' : σ.toRingHom (z₀ : Kb R) = (z : Kb R) := hσρ z
      rwa [e'] at w₀

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem grpPullback_pow_left {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {a : G'.left ⟶ G.left} (h : IsGrpPullback G' G f a) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ a) : ∀ n : ℕ, (x₀ ^ n).left = (x ^ n).left ≫ a := by
  intro n
  induction n with
  | zero =>
    let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ a) (by
      show ((1 : T ⟶ G').left ≫ a) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
    have hm := h.2 T 1 1 u u rfl rfl
    rw [_root_.mul_one] at hm
    have hu : u * u = u := Over.OverMorphism.ext hm
    have hu1 : u = 1 := mul_eq_left.1 hu
    rw [pow_zero, pow_zero, ← hu1]
    rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T (x ^ n) x (x₀ ^ n) x₀ ih hx

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oneTrait : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ →
    ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A →
      ∃ lab : Labels D₁.toPre A, OneTrait D₁.toPre A lab := by
  intro R _ _ _ hR D A hU
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, hW, hφ, hloc, hG', ga, hga, hpb, hLa⟩ := hU
  haveI : CharZero R := hR.2
  haveI : CharZero W := charZero_of_injective_ringHom hφ
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  letI iW : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp ga).toAlgebra
  have tf : ∀ (K M : Type) [Field K] [Field M] [Algebra K M], Module.IsTorsionFree K M := fun _ _ _ _ _ => inferInstance
  haveI := tf (FractionRing R) (Kb W)
  haveI := tf (FractionRing R) (Kb R)
  let em : Kb R →ₐ[FractionRing R] Kb W := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hF : ∀ r, algebraMap (FractionRing R) (Kb W) (algebraMap R _ r) =
      algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r)) := fun r =>
    congrArg (algebraMap (FractionRing W) (Kb W)) (hga r)
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  haveI : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero (Kb R) := charZero_of_injective_ringHom (algebraMap (FractionRing R) (Kb R)).injective
  haveI : CharZero (Kb W) := charZero_of_injective_ringHom em.toRingHom.injective
  haveI := GlobalTheory.ArcExt.epi_spMap em.toRingHom
  have hρ : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact em.commutes x
  let ρ : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ TFK (R := R) (Kb R) := Over.homMk (spMap em.toRingHom) hρ
  let Φ : (TFK (R := R) (Kb R) ⟶ A.A) →* (Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A) :=
    MonoidHom.mk' (fun y => ρ ≫ y) fun x y => by rw [MonObj.comp_mul]
  have hΦ : ∀ y, (Φ y).left = spMap em.toRingHom ≫ y.left := fun _ => rfl
  have hΦinj : Function.Injective Φ := fun x y e => Over.OverMorphism.ext
    ((cancel_epi (spMap em.toRingHom)).1 ((hΦ x).symm.trans ((congrArg (fun q => q.left) e).trans (hΦ y))))
  have desc : ∀ k : ℕ, 1 ≤ k → ∀ z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A, z ^ k = 1 →
      ∃ y : TFK (R := R) (Kb R) ⟶ A.A, Φ y = z := by
    intro k hk z hz
    let u : {y : TFK (R := R) (Kb R) ⟶ A.A // y ^ k = 1} →
        {z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A // z ^ k = 1} :=
      fun y => ⟨Φ y.1, by rw [← map_pow, y.2, map_one]⟩
    have hu : Function.Injective u := fun y y' e => Subtype.ext (hΦinj (congrArg Subtype.val e))
    have c := GlobalTheory.ArcExt.card_torsion hL A (jFK (R := R) (Kb R)) (n := k) (Nat.cast_ne_zero.2 (by omega))
    have c' := GlobalTheory.ArcExt.card_torsion hL A ((TFK (R := W) (Kb W)).hom ≫ spMap ga) (n := k)
      (Nat.cast_ne_zero.2 (by omega))
    haveI : Finite {z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A // z ^ k = 1} :=
      Nat.finite_of_card_ne_zero (by rw [c']; positivity)
    obtain ⟨y, e⟩ := (hu.bijective_of_nat_card_le (c'.trans c.symm).le).2 ⟨z, hz⟩
    exact ⟨y.1, congrArg Subtype.val e⟩
  have toA : ∀ (k : ℕ) (x' : TFK (R := W) (Kb W) ⟶ A'.A), x' ^ k = 1 →
      ∃ z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A, z.left = x'.left ≫ a ∧ z ^ k = 1 := by
    intro k x' hx
    let z : Over.mk ((TFK (R := W) (Kb W)).hom ≫ spMap ga) ⟶ A.A := Over.homMk (x'.left ≫ a) (by
      show (x'.left ≫ a) ≫ A.A.hom = (TFK (R := W) (Kb W)).hom ≫ spMap ga
      rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w])
    refine ⟨z, rfl, Over.OverMorphism.ext ?_⟩
    rw [grpPullback_pow_left hpb x' z rfl k, hx]
    exact ((grpPullback_pow_left hpb x' z rfl 0).trans (by rw [pow_zero])).symm
  have key : ∀ (k : ℕ) (p : QkPt D.toPre (Kb R) k), ∃ y : TFK (R := R) (Kb R) ⟶ A.A, 1 ≤ k →
      ∀ (p₁ : QkPt D.toPre (Kb W) k) (p' : QkPt D'.toPre (Kb W) k) (x' : TFK (R := W) (Kb W) ⟶ A'.A),
        QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD (Kb W) p₁.g p'.g →
        x'.left ≫ a = spMap em.toRingHom ≫ y.left → QkToAkU U'.toUnifPre (Kb W) k p' x' := by
    intro k p
    by_cases hk : 1 ≤ k
    swap
    · exact ⟨1, fun h => absurd h hk⟩
    by_cases hex : ∃ (p₁ : QkPt D.toPre (Kb W) k) (p' : QkPt D'.toPre (Kb W) k),
        QkExt em.toRingHom p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧ IsPullGtF φ hD (Kb W) p₁.g p'.g
    swap
    · exact ⟨1, fun _ p₁ p' _ h₁ h₂ h₃ _ => absurd ⟨p₁, p', h₁, h₂, h₃⟩ hex⟩
    obtain ⟨p₁, p', h₁, h₂, h₃⟩ := hex
    obtain ⟨f, hf, hfk⟩ := GlobalTheory.TorsionIso.torsion_clause W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
    obtain ⟨z, hz, hzk⟩ := toA k (f p') (hfk p')
    obtain ⟨y, hy⟩ := desc k hk z hzk
    refine ⟨y, fun _ q₁ q' x' e₁ e₂ e₃ e₄ => ?_⟩
    obtain rfl : q₁ = p₁ := GlobalTheory.DegActCompare.qkExt_unique e₁ h₁
    obtain rfl : q' = p' := GlobalTheory.TorusExt.qk_ext (e₂.trans h₂.symm) (GlobalTheory.ArcPull.pullGt_unique hD hF e₃ h₃)
    rw [(hf.1 q' x')]
    refine Over.OverMorphism.ext (hpb.1.hom_ext ?_ ?_)
    · rw [e₄, ← hz, ← hy]
      exact (hΦ y).symm
    · rw [Over.w x', Over.w (f q')]
  choose lab hlab using key
  exact ⟨lab, W, inferInstance, inferInstance, inferInstance, φ, G', inferInstance, inferInstance, D', A', U', hD, a, iW, em,
    hW, hφ, hloc, hG', ⟨ga, hga, hpb, hLa⟩, hF, fun k hk p p₁ p' x' h₁ h₂ h₃ h₄ => hlab k p hk p₁ p' x' h₁ h₂ h₃ h₄⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleBoth

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.RescaleLift
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_fnOn_of_le {R : Type} [CommRing R] {W : (Sp R).Opens} (r : R) (h : W ≤ (Sp R).basicOpen (fnSp R r)) :
    IsUnit (fnOn W r) := isUnit_of_basicOpen_top _ (by
  have e := Scheme.preimage_basicOpen W.ι (fnSp R r)
  refine Eq.trans e.symm (top_le_iff.1 fun x _ => h x.2))

theorem mem_basicOpen_of_ne {R F : Type} [CommRing R] [Field F] (α : R →+* F) {r : R} (h : α r ≠ 0) {Z : Scheme.{0}}
    (s : Z ⟶ Sp F) (z : Z) : (s ≫ spMap α) z ∈ (Sp R).basicOpen (fnSp R r) := by
  have hpre : (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) = ⊤ := by
    rw [Scheme.preimage_basicOpen]
    refine Scheme.basicOpen_of_isUnit _ ?_
    refine (congrArg IsUnit (appTop_comp_spMap α s r)).mpr ?_
    exact ((IsUnit.mk0 _ h).map (fnSp _)).map s.appTop.hom
  exact (show z ∈ (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) from hpre.ge trivial)

theorem val_psiOn_rescale {R F : Type} [CommRing R] [IsDomain R] [Field F] (Q : DegPre R) (g : Q.X → (FractionRing R)ˣ)
    {W W₀ : (Sp R).Opens} (ψ : PsiOn Q W) (ψ₀ : PsiOn (GlobalTheory.PolDeg.rescale Q g) W₀) (y : Q.X) (a b : R)
    (hab : (g y : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a)
    (α : R →+* F) (hb : α b ≠ 0) (v : Fˣ) (hv : (v : F) * α b = α a) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme)
    (r₀ : Z ⟶ W₀.toScheme) (s : Z ⟶ Sp F) (hr : r ≫ W.ι = s ≫ spMap α) (hr₀ : r₀ ≫ W₀.ι = s ≫ spMap α)
    (z : Z) (J) (hJ : Good Q.P.L z J) :
    val (ψ₀.psi y) r₀ z J = gm s z ⊤ (unitOn v) * val (ψ.psi y) r z J := by
  have ha : α a ≠ 0 := hv ▸ mul_ne_zero v.ne_zero hb
  have ha' : algebraMap R (FractionRing R) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => ha (by rw [h, map_zero])
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => hb (by rw [h, map_zero])
  obtain ⟨W', l, l₀, la, lb, hm⟩ : ∃ W' : (Sp R).Opens, W' ≤ W ∧ W' ≤ W₀ ∧ W' ≤ (Sp R).basicOpen (fnSp R a) ∧
      W' ≤ (Sp R).basicOpen (fnSp R b) ∧ ∀ x, (s ≫ spMap α) x ∈ W' :=
    ⟨(W ⊓ W₀) ⊓ ((Sp R).basicOpen (fnSp R a) ⊓ (Sp R).basicOpen (fnSp R b)), inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right, inf_le_right.trans inf_le_left, inf_le_right.trans inf_le_right, fun x =>
      ⟨⟨(congrArg (fun q => q x ∈ W) hr).mp (r x).2, (congrArg (fun q => q x ∈ W₀) hr₀).mp (r₀ x).2⟩,
        mem_basicOpen_of_ne α ha s x, mem_basicOpen_of_ne α hb s x⟩⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Z ⟶ W'.toScheme, ρ ≫ W'.ι = s ≫ spMap α :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hm x), IsOpenImmersion.lift_fac _ _ _⟩
  let m : W'.toScheme ⟶ W.toScheme := (Sp R).homOfLE l
  let m₀ : W'.toScheme ⟶ W₀.toScheme := (Sp R).homOfLE l₀
  have f : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have f₀ : m₀ ≫ W₀.ι = W'.ι := Scheme.homOfLE_ι _ _
  have ua := isUnit_fnOn_of_le a la
  have ub := isUnit_fnOn_of_le b lb
  have hφ : m ≫ (toUnit (TW W) ≫ Q.c y).left = m₀ ≫ (toUnit (TW W₀) ≫ Q.c y).left := by
    show m ≫ W.ι ≫ (Q.c y).left = m₀ ≫ W₀.ι ≫ (Q.c y).left
    rw [← Category.assoc, f, ← Category.assoc, f₀]
  have key := GlobalTheory.PsiEvenPull.val_eq_of_app_injective Q.P.isLB
    (u := GlobalTheory.UU.scaleGen ub.unit (LB.pullGen Q.P.L _ _ (ψ₀.psi y) m₀))
    (u' := GlobalTheory.UU.scaleGen ua.unit (LB.pullGen Q.P.L _ _ (ψ.psi y) m))
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) hφ)
    (jK R ∣_ W') (GlobalTheory.PsiEvenPull.app_injective_generic W')
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ₀.psi_gen y) m₀))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m)) (fun x I hI => by
      have e : (jK R ∣_ W') ≫ W'.ι = (jK R ⁻¹ᵁ W').ι ≫ jK R := morphismRestrict_ι _ _
      have p := GlobalTheory.ArcSpecialise.psiOn_generic ψ y ((jK R ∣_ W') ≫ m) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f, e]) hI
      have p₀ := GlobalTheory.ArcSpecialise.psiOn_generic ψ₀ y ((jK R ∣_ W') ≫ m₀) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f₀, e]) hI
      have q : val ((GlobalTheory.PolDeg.rescale Q g).psi y) (jK R ⁻¹ᵁ W').ι x I =
          gm (jK R ⁻¹ᵁ W').ι x ⊤ (unitOn (g y)) * val (Q.psi y) (jK R ⁻¹ᵁ W').ι x I :=
        GlobalTheory.UU.val_scaleGen (unitOn (g y)) (Q.psi y) _ hI
      have ga := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e a ua.unit (Units.mk0 _ ha') ua.unit_spec rfl x
      have gb := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e b ub.unit (Units.mk0 _ hb') ub.unit_spec rfl x
      have w : unitOn (Units.mk0 _ ha') = unitOn (Units.mk0 _ hb') * unitOn (g y) :=
        (congrArg unitOn (Units.ext (hab.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
      refine (GlobalTheory.UU.val_scaleGen _ _ _ hI).trans (Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hI).symm)
      refine (congrArg₂ (· * ·) gb ((val_pull hI _ _ _).trans (p₀.trans q))).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) ga ((val_pull hI _ _ _).trans p)).symm)
      rw [w, map_mul, _root_.mul_assoc]) Z ρ z J hJ
  have ga := gm_fnOn W' α _ _ hρ a ua.unit (Units.mk0 _ ha) ua.unit_spec rfl z
  have gb := gm_fnOn W' α _ _ hρ b ub.unit (Units.mk0 _ hb) ub.unit_spec rfl z
  have w : unitOn (Units.mk0 _ ha) = unitOn (Units.mk0 _ hb) * unitOn v :=
    (congrArg unitOn (Units.ext (hv.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
  have c : ρ ≫ m = r := by rw [← cancel_mono W.ι, Category.assoc, f, hρ, hr]
  have c₀ : ρ ≫ m₀ = r₀ := by rw [← cancel_mono W₀.ι, Category.assoc, f₀, hρ, hr₀]
  have k₂ := (congrArg₂ (· * ·) gb (val_pull hJ _ _ _)).symm.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm.trans
    (key.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) ga (val_pull hJ _ _ _)))))
  rw [w, map_mul, _root_.mul_assoc, c, c₀] at k₂
  exact mul_left_cancel k₂

theorem exists_isPullDeg_rescale : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {Q : DegPre R} {Q' : DegPre V} (hD : IsPullDeg θ Q Q') (g : Q.X → (FractionRing R)ˣ) (g' : Q'.X → (FractionRing V)ˣ), Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) → (∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧ (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a)) → ∃ h : IsPullDeg θ (GlobalTheory.PolDeg.rescale Q g) (GlobalTheory.PolDeg.rescale Q' g'), h.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) = hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ∧ ∀ y, h.xe y = hD.xe y := by
  intro R V _ _ _ _ θ Q Q' h g g' ⟨ψ₀⟩ H
  have hsq : jK V ≫ specOf θ = 𝟙 (TK V).left ≫ spMap ((algebraMap V (FractionRing V)).comp θ) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom θ) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm
  obtain ⟨t, ht⟩ : ∃ t : (TK V).left ⟶ (TW (⊤ : (Sp R).Opens)).left, t ≫ (⊤ : (Sp R).Opens).ι = jK V ≫ specOf θ :=
    ⟨IsOpenImmersion.lift (⊤ : (Sp R).Opens).ι (jK V ≫ specOf θ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have gp : IsGrpPullback Q'.P.A Q.P.A (spMap θ) (proj h) := pull_grp h
  have hr : PMaps (K := PUnit) h.w (fun _ => eSec Q'.P.A) (fun _ => eSec Q.P.A) (fun _ => 1) Q'.rig Q.rig (spMap θ) :=
    GlobalTheory.FieldPull.pmaps_rig h
  have hc : ∀ x : Q'.X, (Q'.c x).left ≫ proj h = spMap θ ≫ (Q.c (h.xe x)).left := h.c_pr
  have hv : ∀ (x : Q'.X) (z : (TK V).left) J J', Good Q.P.L z J → Good Q'.P.L z J' →
      val (ψ₀.psi (h.xe x)) t z J =
        (om h.w z J J' (Q'.xK x))⁻¹ * val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    obtain ⟨a, b, hb, hab, hab'⟩ := H x
    have e0 := val_psiOn_rescale Q g h.psiW ψ₀ (h.xe x) a b hab ((algebraMap V (FractionRing V)).comp θ)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hb) (g' x) hab' h.g t (𝟙 _)
      (h.g_comm.trans hsq) (ht.trans hsq) z J hJ
    have e1 := GlobalTheory.PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
    rw [Category.id_comp] at e1
    have e2 : val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' =
        gm (𝟙 (TK V).left) z ⊤ (unitOn (g' x)) * val (Q'.psi x) (𝟙 _) z J' :=
      GlobalTheory.UU.val_scaleGen (unitOn (g' x)) (Q'.psi x) (𝟙 _) hJ'
    refine e0.trans ?_
    rw [e1, e2, mul_left_comm]
    simp only [om, Category.id_comp]
  obtain ⟨hD, h₁, h₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW (GlobalTheory.PolDeg.rescale Q g)
    (GlobalTheory.PolDeg.rescale Q' g') ψ₀ t ht gp h.w ((isGen_iff h.w).1 h.w_gen) hr h.xe hc hv
  exact ⟨hD, h₁, h₂⟩

end GlobalTheory.RescaleBoth
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)),
  E8Fibration.IsProd pr → ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ f : A ⟶ A, IsMonHom f ∧ E8Fibration.ActsBy pr f m := by
  intro S A B _ _ _ pr hP m
  letI cG : ∀ Z : Over S, CommGroup (Z ⟶ B) := fun Z => Hom.commGroup
  have mc : ∀ {T : Over S} (u v : T ⟶ A) (e : A ⟶ B), IsMonHom e → (u * v) ≫ e = (u ≫ e) * (v ≫ e) := by
    intro T u v e he
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
  have pc : ∀ {T : Over S} (x : T ⟶ A) (a : Fin 8),
      x ≫ (∏ b, pr b ^ m a b : A ⟶ B) = ∏ b, (x ≫ pr b) ^ m a b := by
    intro T x a
    let φ : (A ⟶ B) →* (T ⟶ B) :=
      { toFun := fun u => x ≫ u, map_one' := MonObj.comp_one x, map_mul' := fun u v => MonObj.comp_mul x u v }
    have := map_prod φ (fun b => pr b ^ m a b) Finset.univ
    simp only [map_zpow] at this
    exact this
  obtain ⟨f, hf, -⟩ := hP.2 A (fun a => ∏ b, pr b ^ m a b)
  refine ⟨f, ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_, hf⟩
  refine (hP.2 T fun a => ((x * y) ≫ f) ≫ pr a).unique (fun a => rfl) fun a => ?_
  rw [mc _ _ _ (hP.1 a), Category.assoc, Category.assoc, Category.assoc, hf, pc, pc, pc,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [mc _ _ _ (hP.1 b), mul_zpow]
end
