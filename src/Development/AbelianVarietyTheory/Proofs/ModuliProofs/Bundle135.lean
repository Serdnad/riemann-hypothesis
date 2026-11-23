module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle131
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle014
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmOfKsCoc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle125
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodPol

theorem eq_one_of_pow_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (hn : IsUnit (n : O))
    {z : O} (hz : z ^ n = 1) (h : IsLocalRing.residue O z = 1) : z = 1 := by
  have e := mul_geom_sum z n
  rw [hz, sub_self] at e
  refine sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right fun h0 => ?_)
  have e' := congrArg (IsLocalRing.residue O) h0

  simp only [map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one,
  map_zero] at e'
  exact (hn.map (IsLocalRing.residue O)).ne_zero ((map_natCast _ n).trans e')

theorem unit_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (hn : IsUnit (n : Γ(Sp O, ⊤)))
    {z : Γ(Sp O, ⊤)ˣ} (hz : z ^ n = 1)
    (h : Units.map (spMap (IsLocalRing.residue O)).appTop.hom.toMonoidHom z = 1) : z = 1 := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
  have hn' : IsUnit (n : O) := by simpa using hn.map e
  have h₁ : e z.val = 1 := by
    refine eq_one_of_pow_eq_one hn' ?_ ?_
    · rw [← map_pow, ← Units.val_pow_eq_pow_val, hz, Units.val_one, map_one]
    · have h₂ := congrArg (fun q => q.hom z.val)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))
      have h₃ : (spMap (IsLocalRing.residue O)).appTop.hom z.val = 1 := congrArg Units.val h
      exact h₂.symm.trans ((congrArg (Scheme.ΓSpecIso _).hom.hom h₃).trans (map_one _))
  exact Units.ext (e.injective (h₁.trans (map_one e).symm))

theorem eq_one_of_triv (hL : Out.Laws) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : RigLB A} (c : CubicalStr A L) (O K : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (p : Sp O ⟶ S)
    {pk : Sp (IsLocalRing.ResidueField O) ⟶ S} (hpk : pk = spMap (IsLocalRing.residue O) ≫ p) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤)))
    (hgen : ∀ x : Over.mk (spMap (algebraMap O K) ≫ p) ⟶ A, Triv (Out.translDiff A L.L x) → x = 1)
    (x : Over.mk pk ⟶ A) (hx : x ^ n = 1) (ht : Triv (Out.translDiff A L.L x)) : x = 1 := by
  subst hpk
  have := hA.proper
  let ρK : Over.mk (spMap (algebraMap O K) ≫ p) ⟶ Over.mk p := Over.homMk (spMap (algebraMap O K)) rfl
  let ρk : Over.mk (spMap (IsLocalRing.residue O) ≫ p) ⟶ Over.mk p := Over.homMk (spMap (IsLocalRing.residue O)) rfl
  have inj : ∀ y y' : Over.mk p ⟶ A, ρK ≫ y = ρK ≫ y' → y = y' := fun y y' e =>
    over_points_ext_of_injective S A O K _ (IsFractionRing.injective O K) p y y' (congrArg (fun q => q.left) e)
  have hnO : IsUnit (n : Γ(Sp O, ⊤)) := by simpa using hn.map p.appTop.hom
  have hnK : (n : K) ≠ 0 := by
    have h₁ : IsUnit (n : O) := by
      simpa using hnO.map (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
    simpa using (h₁.map (algebraMap O K)).ne_zero

  obtain ⟨X, hX, hXx⟩ : ∃ X : Over.mk p ⟶ A, X ^ n = 1 ∧ ρk ≫ X = x := by
    obtain ⟨-, -, het⟩ := GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
    obtain ⟨z, hz, -⟩ := LatticeTorsion.existsUnique_torsion A n x hx
    obtain ⟨y, hy, hy'⟩ := (valuationRing_henselian_and_lift_of_isAlgClosed O K).2.2 _
      (pullback.snd (torsion A n).hom p) inferInstance
      (pullback.lift z.left (spMap (IsLocalRing.residue O)) (Over.w z)) (pullback.lift_snd _ _ _)
    let w : Over.mk p ⟶ torsion A n := Over.homMk (y ≫ pullback.fst _ _) (by
      show (y ≫ _) ≫ _ = p
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, Category.id_comp])
    have hw : ρk ≫ w = z := Over.OverMorphism.ext (by
      show spMap (IsLocalRing.residue O) ≫ y ≫ _ = _
      rw [← Category.assoc, hy', pullback.lift_fst])
    refine ⟨w ≫ torsion.ι A n, ?_, by rw [← Category.assoc, hw, hz]⟩
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
  have hE : ValuativeCriterion.Existence A.hom := by
    have h : UniversallyClosed A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨-, hfin, het, hsurj⟩ := abelianScheme_id_pow_finite_etale_surjective S A n hA hn
  have hXK : (ρK ≫ X) ^ n = 1 := by rw [← MonObj.comp_pow, hX, MonObj.comp_one]
  have key : ρK ≫ X = 1 := by
    refine hgen _ (CubNondeg.main hL S A hA L c K _ n hnK hfin inferInstance hsurj _ hXK fun y hy => ?_)
    obtain ⟨l, hl₁, hl₂⟩ := (hE { R := O, K := K, commSq := ⟨Over.w y⟩, .. }).exists_lift
    let Y : Over.mk p ⟶ A := Over.homMk l hl₂
    have hYy : ρK ≫ Y = y := Over.OverMorphism.ext hl₁
    have hY : Y ^ n = 1 := inj _ _ (by rw [MonObj.comp_pow, hYy, hy, MonObj.comp_one])
    obtain ⟨ex, -, pow, pull, -⟩ := cubWeil_basic S A L c n (Over.mk p)
    obtain ⟨ζ, hζ, -⟩ := ex X Y hX hY
    have hYk : (ρk ≫ Y) ^ n = 1 := by rw [← MonObj.comp_pow, hY, MonObj.comp_one]
    have h₁ := pull _ ρk X Y ζ hζ
    rw [hXx] at h₁
    have h₂ := KerPair.cubWeil_of_gen hL.globalFns S A hA L c n _ x (ρk ≫ Y) hx hYk ht
    have h₃ := ((cubWeil_basic S A L c n _).1 x (ρk ≫ Y) hx hYk).unique h₁ h₂
    have h₄ : ζ = 1 := unit_eq_one hnO (pow X Y ζ hζ).2 h₃
    have h₅ := pull _ ρK X Y ζ hζ
    rwa [h₄, map_one, hYy] at h₅
  rw [← hXx, inj X 1 (key.trans (MonObj.comp_one _).symm), MonObj.comp_one]

end GlobalTheory.GoodPol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.QuotModel

theorem injective_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Function.Injective β := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  exact IsFractionRing.injective O F

theorem mono_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) : Mono (spMap β) := by
  obtain ⟨-, -, hfr⟩ := h
  let _ := β.toAlgebra
  have : Epi (CommRingCat.ofHom β) := ⟨fun {Z} g₁ g₂ hg => by
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (j := g₁.hom) (k := g₂.hom) ?_
    have e := congrArg CommRingCat.Hom.hom hg
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    exact e⟩
  exact Functor.map_mono Scheme.Spec (CommRingCat.ofHom β).op

theorem mem_range_spMap {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : Function.Injective β) (p : Sp O) :
    p ∈ Set.range (spMap β) ↔ p.asIdeal = ⊥ := by
  have hk : RingHom.ker β = ⊥ := (RingHom.injective_iff_ker_eq_bot β).mp h
  constructor
  · rintro ⟨q, rfl⟩
    have := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    show Ideal.comap β q.asIdeal = ⊥
    rw [hq, ← RingHom.ker_eq_comap_bot, hk]
  · intro hp
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap β ⊥ = p.asIdeal
    rw [hp, ← RingHom.ker_eq_comap_bot, hk]

theorem densePart {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) {X U : Scheme.{0}}
    (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap β)) (h₁ : Flat s) (h₂ : IsProjOver s) (h₃ : IsOpenImmersion jQ)
    (h₄ : Dense (Set.range jQ)) :
    IsLocallyNoetherian X ∧ genericPoints X ⊆ Set.range (jQ ≫ pullback.fst _ _ : U ⟶ X) ∧
      ∀ u : U, IsIso ((jQ ≫ pullback.fst _ _ : U ⟶ X).stalkMap u) := by
  obtain ⟨⟨hdom, hded⟩, -, hfr⟩ := h
  let _ := β.toAlgebra
  obtain ⟨hN, -, -, hpre, hfl, hdo, hqc⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ h₁ h₂ h₃ h₄
  obtain ⟨hg, hst, -⟩ := GlobalTheory.densePart_basic X U _ hpre hfl hdo hqc
  exact ⟨hN, hg, hst⟩

private theorem isReduced_of_isNormalScheme' (X : Scheme.{0}) (h : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

end GlobalTheory.QuotModel


open GlobalTheory.QuotModel in
theorem GlobalTheory.Models.exists_quotient_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ν : SABMap t t' r) (ρ₀ : Γ →* Aut U) (τ₀ : Γ →* Aut t.G.left) (ρ : Γ →* Aut C.X) (τ : Γ →* Aut C.t.G.left) (mu : ∀ g, SABMap C.t C.t (ρ g).asIso.hom), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsProper t.G.hom → (∀ g, (mu g).φ = (τ g).asIso.hom ∧ C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j ∧ C.m.φ ≫ (τ g).asIso.hom = (τ₀ g).asIso.hom ≫ C.m.φ ∧ (τ₀ g).asIso.hom ≫ ν.φ = ν.φ) → IsQProjOver (C.t.G.hom ≫ C.s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ C.X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst C.t.G.hom x ≫ (τ g).asIso.hom = pullback.fst C.t.G.hom x) → Good C.t → PushInvertible C.t.G C.t.PP.L → ∃ C' : Cpt c' t' β', Good C'.t ∧ Nonempty (C.Above C' b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' Γ _ _ C b k r ν ρ₀ τ₀ ρ τ mu hβ hβ' hcomp hfin hrc hr hprop hmu hqp
    htame hin hgood hpush

  have sq : ∀ {S S' : Scheme.{0}} {ta : SAB H S} {tb : SAB H S'} {f : S ⟶ S'} (m : SABMap ta tb f),
      m.φ ≫ tb.G.hom = ta.G.hom ≫ f := fun m => m.cart.1.w
  have sqm : C.m.φ ≫ C.t.G.hom = t.G.hom ≫ C.j := sq C.m

  obtain ⟨X', π, s', jQ, hπ, hπfin, hπs, hnorm, hproj, hflat, hjover, hjopen, hjdense, hjc, hgen⟩ :=
    GlobalTheory.exists_quotient_model_scheme E H U F O c t β Γ C U' F' O' c' β' b k r ρ₀ ρ hβ hβ' hcomp hfin hrc hr
      (fun g => (hmu g).2.1)
  obtain ⟨hN', -, -⟩ := densePart hβ' s' jQ hflat hproj hjopen hjdense
  obtain ⟨-, hgenC, hstC⟩ := densePart hβ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hredX : IsReduced C.X := isReduced_of_isNormalScheme' _ C.normal
  have hgab : genericPoints C.X ⊆ abLocus C.t.G := by
    intro x hx
    obtain ⟨u, rfl⟩ := hgenC hx
    have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
      rw [C.ab_gen]; exact ⟨u, rfl⟩
    exact hu

  obtain ⟨t₁, ν', hν'τ, hgood'⟩ :=
    GlobalTheory.T.exists_semiAbelian_descent_tame_quotient E H Γ O C.X X' ρ π C.t C.s τ mu hπ hπfin hqp ⟨hredX, hgab⟩ (fun g => (hmu g).1) htame hin
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν' C.m
  have key : ∀ (f : U ⟶ X') (n : SABMap t t₁ f), f = r ≫ jQ ≫ pullback.fst _ _ →
      ∃ n' : SABMap t t₁ (r ≫ jQ ≫ pullback.fst _ _), n'.φ = n.φ := by
    rintro f n rfl; exact ⟨n, rfl⟩
  obtain ⟨n₂, hn₂⟩ := key _ n hjc.symm

  have hredU : IsReduced U := by
    have : ∀ u : U, _root_.IsReduced (U.presheaf.stalk u) := by
      intro u
      have hI : IsIso ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u) := hstC u
      exact isReduced_of_injective (inv ((C.jQ ≫ pullback.fst C.s (spMap β)).stalkMap u)).hom
        (ConcreteCategory.bijective_of_isIso _).1
    exact isReduced_of_isReduced_stalk U
  have hmono : Mono C.j := by
    have := mono_spMap hβ
    have := C.jQ_open
    dsimp only [Cpt.j]; infer_instance
  have hτ : ∀ g, (τ₀ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ₀ g).asIso.hom ∧ (τ₀ g).asIso.hom ≫ ν.φ = ν.φ ∧
      (τ₀ g).asIso.hom ≫ n₂.φ = n₂.φ := by
    intro g
    obtain ⟨h1, h2, h3, h4⟩ := hmu g
    refine ⟨(cancel_mono C.j).mp ?_, h4, ?_⟩
    · calc ((τ₀ g).asIso.hom ≫ t.G.hom) ≫ C.j = ((τ₀ g).asIso.hom ≫ C.m.φ) ≫ C.t.G.hom := by
            simp only [Category.assoc]; rw [← sqm]
        _ = (C.m.φ ≫ (mu g).φ) ≫ C.t.G.hom := by rw [← h3, h1]
        _ = C.m.φ ≫ C.t.G.hom ≫ (ρ g).asIso.hom := by simp only [Category.assoc]; rw [sq (mu g)]
        _ = t.G.hom ≫ C.j ≫ (ρ g).asIso.hom := by rw [← Category.assoc, sqm, Category.assoc]
        _ = (t.G.hom ≫ (ρ₀ g).asIso.hom) ≫ C.j := by rw [h2, Category.assoc]
    · rw [hn₂, hn, ← Category.assoc, ← h3, Category.assoc, hν'τ g]
  obtain ⟨m', hm'⟩ := GlobalTheory.T.exists_cmTripleMap_descend_groupQuotient E H Γ U U' X' ρ₀ r t t' t₁ τ₀ ν _ n₂ hr hredU hprop hτ

  have hπsurj : Function.Surjective π := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ C.X X' ρ π hπ).2.1.surj
  have hrsurj : Function.Surjective r := (GlobalTheory.quotient_isIntegral_surjective_orbits Γ U U' ρ₀ r hr).2.1.surj
  have habπ : ∀ x, π x ∈ abLocus t₁.G ↔ x ∈ abLocus C.t.G := fun x =>
    abLocus_pullback abLocusOne t₁.semi ν'.cart.1 x

  have hbint : ∀ p : Sp O, (spMap b p).asIdeal = ⊥ → p.asIdeal = ⊥ := by
    intro p hp
    obtain ⟨⟨hdO, -⟩, -, -⟩ := hβ
    obtain ⟨⟨hdO', -⟩, -, -⟩ := hβ'
    let _ := b.toAlgebra
    have h2 : IsFinite (Spec.map (CommRingCat.ofHom b)) := hfin
    rw [IsFinite.SpecMap_iff] at h2
    have : Module.Finite O' O := h2
    have : Algebra.IsIntegral O' O := inferInstance
    exact Ideal.eq_bot_of_comap_eq_bot (R := O') hp
  have hpre : Function.Injective (pullback.fst s' (spMap β')) := by
    obtain ⟨-, -, hfr'⟩ := hβ'
    let _ := β'.toAlgebra
    have : IsPreimmersion (spMap β') := IsPreimmersion.of_isLocalization (nonZeroDivisors O')
    exact (pullback.fst s' (spMap β')).isEmbedding.injective
  have hab : pullback.fst s' (spMap β') ⁻¹' abLocus t₁.G = Set.range jQ := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, hx⟩ := hπsurj (pullback.fst s' (spMap β') w)
      have hxab : x ∈ abLocus C.t.G := (habπ x).1 (by rw [hx]; exact hw)
      have hs' : (s' (pullback.fst s' (spMap β') w)).asIdeal = ⊥ := by
        have e : s' (pullback.fst s' (spMap β') w) = spMap β' (pullback.snd s' (spMap β') w) := by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        rw [e]
        exact (mem_range_spMap (injective_of_isDedFrac hβ') _).1 ⟨_, rfl⟩
      have hsx : (C.s x).asIdeal = ⊥ := by
        apply hbint
        have e : spMap b (C.s x) = s' (π x) := by
          rw [← Scheme.Hom.comp_apply, ← hπs, Scheme.Hom.comp_apply]
        rw [e, hx]
        exact hs'
      obtain ⟨q, hq⟩ := (mem_range_spMap (injective_of_isDedFrac hβ) (C.s x)).2 hsx
      obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.s) (g := spMap β) x q hq.symm
      have hz : z ∈ Set.range C.jQ := by
        rw [← C.ab_gen]
        show pullback.fst C.s (spMap β) z ∈ abLocus C.t.G
        rw [hz1]
        exact hxab
      obtain ⟨u, rfl⟩ := hz
      obtain ⟨u', hu'⟩ := (hgen x).2 ⟨u, hz1⟩
      exact ⟨u', hpre (hu'.trans hx)⟩
    · rintro ⟨u', rfl⟩
      obtain ⟨u, rfl⟩ := hrsurj u'
      have e : pullback.fst s' (spMap β') (jQ (r u)) = π (C.j u) := by
        have h5 := congrArg (fun f : U ⟶ X' => f u) hjc
        simpa only [Scheme.Hom.comp_apply] using h5
      show pullback.fst s' (spMap β') (jQ (r u)) ∈ abLocus t₁.G
      rw [e, habπ]
      have hu : C.jQ u ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G := by
        rw [C.ab_gen]; exact ⟨u, rfl⟩
      exact hu
  refine ⟨⟨X', s', hnorm, hproj, hflat, jQ, hjover, hjopen, hjdense, t₁, m', hab⟩, hgood' hgood hpush,
    ⟨⟨π, hπs, ?_, ν', hjc.symm, ?_⟩⟩⟩
  · refine MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) _ (pullback.fst s' (spMap b))
      inferInstance ?_
    rw [pullback.lift_fst]
    exact hπfin
  · rw [hm', hn₂, hn]

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem reduced_flat_of_charts {Z S : Scheme.{0}} (s : Z ⟶ S) (U : Z.Opens) {κ : Type} (Y : κ → Scheme.{0})
    (x : ∀ i, Y i ⟶ Z) (hx : ∀ i, IsOpenImmersion (x i)) (hr : ∀ i, IsReduced (Y i)) (hf : ∀ i, Flat (x i ≫ s))
    (hc : ∀ z ∈ U, ∃ i, z ∈ Set.range (x i)) : IsReduced U.toScheme ∧ Flat (U.ι ≫ s) := by
  let 𝒰 : U.toScheme.OpenCover := Scheme.Cover.mkOfCovers κ (fun i => pullback U.ι (x i)) (fun i => pullback.fst U.ι (x i))
    (fun z => by
      obtain ⟨i, y, hy⟩ := hc z.1 z.2
      have : z ∈ Set.range (pullback.fst U.ι (x i)) := by
        rw [Scheme.Pullback.range_fst]
        exact ⟨y, hy⟩
      exact ⟨i, this⟩) (fun i => inferInstance)
  constructor
  · haveI : ∀ i, IsReduced (𝒰.X i) := fun i =>
      by
      change IsReduced (pullback U.ι (x i) :)
      haveI := hr i
      exact isReduced_of_isOpenImmersion (pullback.snd U.ι (x i))
    exact IsReduced.of_openCover _ 𝒰
  · haveI : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
    refine IsZariskiLocalAtSource.of_openCover (P := @Flat) 𝒰 (fun i => ?_)
    change Flat (pullback.fst U.ι (x i) ≫ U.ι ≫ s)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    haveI := hf i
    haveI := hx i
    exact MorphismProperty.comp_mem @Flat _ _ inferInstance (hf i)

theorem flat_spMap_of_torsionFree {o σ : Type} [CommRing o] [IsDedekindDomain o] (J : Ideal (MvPolynomial σ o))
    (h : ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ J → F ∈ J) :
    Flat (spMap ((Ideal.Quotient.mk J).comp MvPolynomial.C)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  have : Module.IsTorsionFree o (MvPolynomial σ o ⧸ J) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro c y hy
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [Ideal.Quotient.eq_zero_iff_mem]
      apply h c F hc
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← MvPolynomial.smul_eq_C_mul]
      exact hy
  have hfl : Module.Flat o (MvPolynomial σ o ⧸ J) := inferInstance
  exact (RingHom.flat_algebraMap_iff.2 hfl :)

theorem nonempty_MMPre : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)), 0 < N' → I.IsRadical → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → Nonempty (MMPre n N' I) := by
  intro o _ _ g n N' I hN hrad hhom htf
  haveI : NeZero (N' ^ 2) := ⟨by positivity⟩
  obtain ⟨Z, s, M, th, hproj, hrep, hfp, -⟩ := GlobalTheory.T.exists_projCoordRepresentation_homogeneousIdeal_flat o (Ix g (N' ^ 2)) I 0 hhom
  obtain ⟨N, j, hj, hjs⟩ := hproj ⟨0⟩
  haveI := hfp (IsNoetherian.noetherian I)
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  let U : Z.Opens := ⟨⋂ a, ⋃ c, (Out.nonzeroLocus (th (a + (N' / n) • c)) : Set Z),
    isOpen_iInter_of_finite fun a => isOpen_iUnion fun c => (Out.nonzeroLocus _).2⟩
  have hU : ∀ z : Z, z ∈ U ↔ ∀ a, ∃ c, z ∈ Out.nonzeroLocus (th (a + (N' / n) • c)) := fun z => by
    change z ∈ ⋂ a, ⋃ c, (Out.nonzeroLocus (th (a + (N' / n) • c)) : Set Z) ↔ _
    simp only [Set.mem_iInter, Set.mem_iUnion, SetLike.mem_coe]
  choose x hxo hxr hxs _ using fun i => GlobalTheory.T.exists_nonzeroCoordinate_affineChart o _ I Z s M th i hrep
  obtain ⟨hred, hflat⟩ := reduced_flat_of_charts s U _ x hxo
    (fun i => by
      haveI : _root_.IsReduced (MvPolynomial (Ix g (N' ^ 2)) o ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) :=
        (Ideal.isRadical_iff_quotient_reduced _).1 ((GlobalTheory.T.sup_span_X_sub_one_isRadical_and_torsionFree o _ I i hhom).1 hrad)
      infer_instance)
    (fun i => by
      rw [hxs i]
      exact flat_spMap_of_torsionFree _ ((GlobalTheory.T.sup_span_X_sub_one_isRadical_and_torsionFree o _ I i hhom).2 htf))
    (fun z hz => by
      obtain ⟨c, hc⟩ := (hU z).1 hz 0
      exact ⟨_, by rw [hxr]; exact hc⟩)
  obtain ⟨hpull, -, hnz⟩ := GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus Z M _ th hrep.1
  obtain ⟨th', hth'⟩ := hpull U.toScheme U.ι
  refine ⟨{ MM := U.toScheme, s := U.ι ≫ s, qproj := ⟨N, U.ι ≫ j, inferInstance, inferInstance, by rw [Category.assoc, hjs]⟩
            flat := hflat, reduced := hred, de := M.pull U.ι, isLB := pull_isLB hrep.1 _, th := th', loc := ?_, pts := ?_ }⟩
  · intro R _ β y v hy hv
    rw [hth'] at hv
    refine ⟨(hrep.2.1 R β (y ≫ U.ι) v (by rw [Category.assoc, hy]) hv).2, fun q hq a => ?_⟩
    let p : Sp R := (⟨q, hq⟩ : PrimeSpectrum R)
    obtain ⟨c, hc⟩ := (hU ((y ≫ U.ι) p)).1 (by rw [Scheme.Hom.comp_apply]; exact (y p).2) a
    exact ⟨c, (hnz R _ v _ p hv).1 hc⟩
  · intro R _ β v hv
    have hspan : Ideal.span (Set.range v) = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨c, hc⟩ := hv.2 m hm.isPrime 0
      exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))
    obtain ⟨y, ⟨hys, hyv⟩, huniq⟩ := hrep.2.2 R β v hspan hv.1
    have hrange : Set.range y ⊆ Set.range U.ι := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine (hU _).2 fun a => ?_
      obtain ⟨c, hc⟩ := hv.2 p.asIdeal p.isPrime a
      exact ⟨c, (hnz R y v _ p hyv).2 hc⟩
    have hl := IsOpenImmersion.lift_fac U.ι y hrange
    refine ⟨IsOpenImmersion.lift U.ι y hrange, ⟨by rw [← Category.assoc, hl, hys], by rw [hth', hl]; exact hyv⟩, ?_⟩
    rintro y' ⟨h1, h2⟩
    rw [hth'] at h2
    rw [← cancel_mono U.ι, hl]
    exact huniq _ ⟨by rw [Category.assoc, h1], h2⟩

end GlobalTheory.ZM
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.KSField.exists_ksMatrix : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ :=
  GlobalTheory.KSField.exists_ksMatrix_of GlobalTheory.FinAffineCharts.exists_finite_affine_charts GlobalTheory.KS.InvField.main GlobalTheory.KS.DlogPol.dlog_independent GlobalTheory.KS.Cocycle.exists_ksCoc GlobalTheory.KS.LinDir.ksCoc_linear GlobalTheory.KS.Sym.exists_symm_of_ksCoc GlobalTheory.KS.matrix_intertwines_adjoint GlobalTheory.KS.exists_global_locDer_of_isCob GlobalTheory.KS.exists_isConstK_of_locDerK
end
