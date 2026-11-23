module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle011
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

theorem appLE_top_eq_zero_iff {X T : Scheme.{0}} (t : T ⟶ X) {U : X.Opens} (h : ⊤ ≤ t ⁻¹ᵁ U)
    (a : Γ(X, U)) : (t.appLE U ⊤ h).hom a = 0 ↔ (t.app U).hom a = 0 := by
  have e : (t.appLE U ⊤ h).hom a = resG _ h ((t.app U).hom a) := rfl
  rw [e]
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have := congrArg (resG _ (le_top : t ⁻¹ᵁ U ≤ ⊤)) h0
  rwa [Cartier.resG_resG, Cartier.resG_self, map_zero] at this

theorem appLE_originSec_eq_zero_iff {R : Type} [CommRing R] (W : WeierstrassCurve R) {T : Scheme.{0}}
    (t : T ⟶ scheme W) (i : (originLB W).ι) (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i) :
    (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔ t = t ≫ toSpec W ≫ zero W := by
  rw [appLE_top_eq_zero_iff]
  constructor
  · intro h0
    rcases i with _ | _
    · have h1 : (1 : Γ(T, t ⁻¹ᵁ coordOpen W 2)) = 0 := (map_one _).symm.trans h0
      have hT : IsEmpty T := ⟨fun p => by
        have := congrArg (T.presheaf.germ (t ⁻¹ᵁ coordOpen W 2) p (h (Set.mem_univ p))).hom h1
        rw [map_one, map_zero] at this
        exact absurd this one_ne_zero⟩
      refine (eq_comp_zero_iff W t).2 ⟨fun p _ => (hT.false p).elim, Cartier.ext_germ fun p _ => (hT.false p).elim⟩
    · exact (eq_comp_zero_iff W t).2 ⟨h, h0⟩
  · intro e
    have h0 := (secPull_originSec_eq_zero_iff W t).2 e (fun _ => i)
    have := congrArg (resG T (Cartier.pull_U (originLB W) t (fun _ => i)).ge) h0
    rw [map_zero] at this
    exact ((Cartier.resG_resG _ _ _).trans (Cartier.resG_self _ _)).symm.trans this

theorem appLE_sec_pull_originLB_eq_zero {R : Type} [CommRing R] (W : WeierstrassCurve R)
    {R' : Type} [CommRing R'] {f : Sp R' ⟶ Sp R} {Y : Scheme.{0}} {φ : Y ⟶ scheme W} {q : Y ⟶ Sp R'}
    (H : IsPullback φ q (toSpec W) f) (s : ((originLB W).pull φ).Sec) {T : Scheme.{0}} (t : T ⟶ Y)
    (j : ((originLB W).pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ ((originLB W).pull φ).U j)
    (e : t ≫ φ = t ≫ φ ≫ toSpec W ≫ zero W) :
    (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom (s.f j) = 0 := by
  obtain ⟨c, hc, -⟩ := existsUnique_eq_appLE_mul_secPull W H s
  have h' : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ (originLB W).U (j ⟨⟩) :=
    fun p hp => (Cartier.pull_U (originLB W) φ j).le (h hp)
  have h0 := (appLE_originSec_eq_zero_iff W (t ≫ φ) (j ⟨⟩) h').2 (e.trans (Category.assoc _ _ _).symm)
  have h1 : (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom
      ((Cartier.secPull (originSec W) φ).f j) = 0 := by
    refine Eq.trans ?_ h0
    have := Scheme.Hom.appLE_comp_appLE t φ ((originLB W).U (j ⟨⟩)) _ ⊤
      (Cartier.pull_U (originLB W) φ j).le h
    exact congrArg (fun g => g.hom ((originSec W).f (j ⟨⟩))) this
  rw [hc j, map_mul, h1, mul_zero]

theorem originLB_polarisation (R : Type) [CommRing R] (W : WeierstrassCurve R) [GrpObj (schemeOver W)]
    (_hc : IsCommMonObj (schemeOver W)) (he : η[schemeOver W].left = zero W) :
    Out.Rigidified (schemeOver W) (originLB W) ∧ Out.Sym (schemeOver W) (originLB W) ∧
      Out.RelAmple (schemeOver W) (originLB W) ∧ Out.KTriv (schemeOver W) (originLB W) := by
  have he' : eSec (schemeOver W) = zero W := he
  have hz : ∀ (T : Scheme.{0}) (t : T ⟶ (schemeOver W).left) (i : (originLB W).ι)
      (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i),
      (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
        t = t ≫ (schemeOver W).hom ≫ eSec (schemeOver W) := fun T t i h => by
    rw [he']
    exact appLE_originSec_eq_zero_iff W t i h
  refine ⟨?_, ?_, relAmple_originLB W, ?_⟩
  · unfold Out.Rigidified
    rw [he']
    exact ⟨_, isGen_one_pull_zero W⟩
  · exact GlobalTheory.T.symmetric_lineBundle_of_regular_section _ (schemeOver W) (originLB W) (originSec W) (originLB_isLB W)
      (fun i V h => ((isRegularSec_originSec W i).resG h).mem) hz
  · refine GlobalTheory.T.kernelPolarisation_trivial_of_sections_vanish_zero _ (schemeOver W) (originLB W) (originSec W) (originLB_isLB W) hz ?_
    intro R' _ f Y φ q H s T t j h e
    rw [he'] at e
    exact appLE_sec_pull_originLB_eq_zero W H s t j h e

end GlobalTheory.WeierstrassCurve
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isFibreOf_iff_isPolFibre : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Nontrivial R'] (f : R →+* R') (A : Out.PolAV (Sp R)) (x : KeyIn R') (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (spMap f) φ ↔ IsPolFibre f A x.P φ := by
  intro R R' _ _ _ f A x φ
  refine ⟨fun h => ⟨?_, h.1, LBIso.symm h.2⟩, fun h => ⟨h.2.1, LBIso.symm h.2.2⟩⟩
  exact H1.dim_unique _ x.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1.1 A.smoothDim)
    (eSec x.P.A (Classical.arbitrary (PrimeSpectrum R')))

end GlobalTheory.LamF
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleProd

open GlobalTheory.CechPic

section Local

variable {Y Y' B B' : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ pull (π ⁻¹ᵁ V).ι c = 0

theorem pull_eq_zero_of_range {W : Y.Opens} {c : Pic Y} (H : pull W.ι c = 0) (h : Y' ⟶ Y) (hW : ∀ y, h y ∈ W) :
    pull h c = 0 := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hW y
  rw [← IsOpenImmersion.lift_fac W.ι h hr, pull_comp, H, map_zero]

theorem LocZero.sub {π : Y ⟶ B} {c d : Pic Y} (H : LocZero π c) (H' : LocZero π d) : LocZero π (c - d) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  obtain ⟨V', hV', t'⟩ := H' p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ?_⟩
  rw [map_sub, pull_eq_zero_of_range t (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.1,
    pull_eq_zero_of_range t' (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.2, sub_zero]

theorem LocZero.pull_over {π : Y ⟶ B} {c : Pic Y} (H : LocZero π c) {π' : Y' ⟶ B} (h : Y' ⟶ Y) (sq : h ≫ π = π') :
    LocZero π' (pull h c) := by
  subst sq
  intro p
  obtain ⟨V, hV, t⟩ := H p
  refine ⟨V, hV, ?_⟩
  rw [← pull_comp]
  exact pull_eq_zero_of_range t _ fun y => y.2

theorem locZero_base (π : Y ⟶ B) (c : Pic B) : LocZero π (pull π c) := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  intro p
  obtain ⟨i, hi⟩ := exists_chart hL p
  refine ⟨L.U i, hi, ?_⟩
  rw [← pull_comp]
  exact (cls_eq_zero_iff (pull_isLB hL _)).2
    (BoxKernel.gen_of_chart (pull_isLB hL _) (fun _ => i) fun y => mem_pull.2 y.2)

theorem locZero_iff (π : Y ⟶ B) {N : LB Y} (hN : N.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (N.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls N hN) :=
  forall_congr' fun _ => exists_congr fun _ => and_congr_right fun _ =>
    (cls_eq_zero_iff (pull_isLB hN _)).symm

end Local

section Kernel

variable {S : Scheme.{0}} {A G H : Over S} [GrpObj A] [GrpObj G] [GrpObj H]

theorem cls_translDiff {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A) :
    cls (Out.translDiff A L x) (LB.isLB_linComb hL _ _) =
      pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
  refine (cls_linComb hL _ _ _).trans ?_
  rw [Fin.sum_univ_two]
  show (1 : ℤ) • pull ((fst T A ≫ x) * snd T A).left (cls L hL) + (-1 : ℤ) • pull (snd T A).left (cls L hL) = _
  rw [one_zsmul, neg_one_zsmul, sub_eq_add_neg]

theorem locZero_translDiff_comp {N : LB A.left} {L : LB G.left} (hN : N.IsLB) (hL : L.IsLB) (b : Pic H.left)
    (p : A ⟶ G) (q : A ⟶ H) [IsMonHom p] [IsMonHom q] (u : G ⟶ A) (hp : u ≫ p = 𝟙 G) (hq : u ≫ q = 1)
    (e : cls N hN = pull p.left (cls L hL) + pull q.left b) {T : Over S} (x : T ⟶ A)
    (hx : LocZero (fst T A).left (cls (Out.translDiff A N x) (LB.isLB_linComb hN _ _))) :
    LocZero (fst T G).left (cls (Out.translDiff G L (x ≫ p)) (LB.isLB_linComb hL _ _)) := by
  have H₁ := hx.pull_over (π' := (fst T G).left) (T ◁ u).left (congrArg (fun q => q.left) (whiskerLeft_fst T u))
  have H₂ := (H₁.sub (locZero_base (fst T G).left (pull (x ≫ q).left b))).sub
    (locZero_base (fst T G).left (-pull (1 : T ⟶ H).left b))
  have e₁ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ p = (fst T G ≫ x ≫ p) * snd T G := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hp,
      Category.comp_id]
  have e₂ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ q = fst T G ≫ x ≫ q := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hq,
      MonObj.comp_one, _root_.mul_one]
  have e₃ : T ◁ u ≫ snd T A ≫ p = snd T G := by rw [whiskerLeft_snd_assoc, hp, Category.comp_id]
  have e₄ : T ◁ u ≫ snd T A ≫ q = fst T G ≫ (1 : T ⟶ H) := by
    rw [whiskerLeft_snd_assoc, hq, MonObj.comp_one, MonObj.comp_one]
  convert H₂ using 1
  rw [cls_translDiff hL, cls_translDiff hN, e]
  simp only [map_sub, map_add (f := _), map_neg, ← pull_comp, ← Over.comp_left, e₁, e₂, e₃, e₄]
  abel

theorem kTriv_prod {N : LB (G ⊗ H).left} {L : LB G.left} {L' : LB H.left} (hN : N.IsLB) (hL : L.IsLB)
    (hL' : L'.IsLB) (e : cls N hN = pull (fst G H).left (cls L hL) + pull (snd G H).left (cls L' hL'))
    (hK : Out.KTriv G L) (hK' : Out.KTriv H L') : Out.KTriv (G ⊗ H) N := by
  intro R _ t x hx
  have hx' := (locZero_iff _ (LB.isLB_linComb hN _ _)).1 hx
  have h₁ : x ≫ fst G H = 1 := hK R t _ ((locZero_iff _ (LB.isLB_linComb hL _ _)).2
    (locZero_translDiff_comp hN hL _ (fst G H) (snd G H) (lift (𝟙 G) 1) (lift_fst _ _) (lift_snd _ _) e x hx'))
  have h₂ : x ≫ snd G H = 1 := hK' R t _ ((locZero_iff _ (LB.isLB_linComb hL' _ _)).2
    (locZero_translDiff_comp hN hL' _ (snd G H) (fst G H) (lift 1 (𝟙 H)) (lift_snd _ _) (lift_fst _ _)
      (e.trans (add_comm _ _)) x hx'))
  show x = 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [h₁, MonObj.one_comp]
  · rw [h₂, MonObj.one_comp]

end Kernel

section Cube

variable {S : Scheme.{0}} {A G : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] {n : ℕ}

def cubeCls {T : Over S} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls (cubeLB G x L) (LB.isLB_linComb hL _ _) = cubeCls x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls {T T' : Over S} (ρ : T' ⟶ T) (x : Fin n → (T ⟶ G)) (c : Pic G.left)
    (y : Fin n → (T' ⟶ G)) (h : ∀ i, y i = ρ ≫ x i) : cubeCls y c = pull ρ.left (cubeCls x c) := by

  rw [cubeCls, cubeCls, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, PrimNorm.psum_pre ρ x y h]

end Cube

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S) {T : Over S}

end Triple

end GlobalTheory.TripleProd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.EllipticHom

theorem exists_coord {g : ℕ} (hg : g = 1) {w : Fin g → ℂ} (hw : w ≠ 0) :
    ∃ c : (Fin g → ℂ) →ₗ[ℂ] ℂ, (∀ x, c x • w = x) ∧ c w = 1 := by
  subst hg
  have hw0 : w 0 ≠ 0 := fun h => hw (funext fun i => by rw [Subsingleton.elim i 0, h]; rfl)
  refine ⟨(w 0)⁻¹ • LinearMap.proj 0, fun x => ?_, by simp [hw0]⟩
  funext i
  rw [Subsingleton.elim i 0]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem exists_index {L L' : PeriodPair} {α : ℂ} (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) :
    ∃ n : ℕ, Complex.normSq α * |(L.ω₁ * starRingEnd ℂ L.ω₂).im| = n * |(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| := by
  obtain ⟨p, q, h1⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₁_mem_lattice)
  obtain ⟨r, s, h2⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₂_mem_lattice)
  refine ⟨(p * s - q * r).natAbs, ?_⟩
  have e : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im =
      ((p * s - q * r : ℤ) : ℝ) * (L'.ω₁ * starRingEnd ℂ L'.ω₂).im := by
    have e1 : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im = ((α * L.ω₁) * starRingEnd ℂ (α * L.ω₂)).im := by
      simp [Complex.normSq_apply]
      ring
    rw [e1, ← h1, ← h2]
    simp
    ring
  rw [Nat.cast_natAbs, Int.cast_abs, ← abs_mul, ← e, abs_mul, abs_of_nonneg (Complex.normSq_nonneg α)]

theorem covolume_ne_zero (L : PeriodPair) : (L.ω₁ * starRingEnd ℂ L.ω₂).im ≠ 0 := by
  intro h
  have hi := LinearIndependent.pair_iff.1 L.indep
  simp at h
  have h1 := hi L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := hi L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := hi 0 1 (by
    apply Complex.ext <;> simp [h1.1, h2.1])
  exact one_ne_zero h3.2

theorem multiplier_iff_exists_hom : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (s : R →+* ℂ) (L L' : PeriodPair) (α : ℂ), P.g = 1 → Q.g = 1 → IsTangent v → IsTangent t → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s Q P' φ' → IsVecOver s φ' t v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L'.lattice ↔ z • w' ∈ u'.Λ) → ((∀ z ∈ L.lattice, α * z ∈ L'.lattice) ↔ (∀ (P₁ Q₁ : Out.PolAV (Sp ℂ)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR ℂ ⟶ P₁.A) (t₁ : epsR ℂ ⟶ Q₁.A), IsPolFibre s P P₁ φ₁ → IsPolFibre s Q Q₁ ψ₁ → IsVecOver s φ₁ v v₁ → IsVecOver s ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![α] ![t₁] (v₁ ≫ f₁))) := by
  intro hU hB R _ P Q v t s L L' α hP hQ hv ht hL hL'
  constructor
  · intro hα P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, Hm, χ, Ef, hA, -, hd, -, -, hθ, hE, hEb, -⟩ := hU P₁ rig hrig
    obtain ⟨u', Hm', χ', Ef', hA', -, hd', he', -, hθ', hE', hEb', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨w0, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨w0', hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    have g1 : P₁.g = 1 := hφ.1.trans hP
    have g2 : Q₁.g = 1 := hψ.1.trans hQ
    have hH := hermForm_principal_dim_one _ u.Λ w L Hm Ef g1 w0 hΛ hA.1 (hA.2.1 w w0) hE hEb
    have hH' := hermForm_principal_dim_one _ u'.Λ w' L' Hm' Ef' g2 w0' hΛ' hA'.1 (hA'.2.1 w' w0') hE' hEb'
    obtain ⟨c, hc, hc1⟩ := exists_coord g1 w0
    obtain ⟨n, hn⟩ := exists_index hα
    let F : (Fin P₁.g → ℂ) →ₗ[ℂ] (Fin Q₁.g → ℂ) := (α • c).smulRight w'
    have hF : ∀ x, F x = (α * c x) • w' := fun x => rfl
    obtain ⟨f, hf, hFf⟩ := exists_hom_of_linear_scaling_hermForm P₁ Q₁ u u' Hm χ Hm' χ' hA hA'
      (fun k => (hθ k).2) (fun k => (hθ' k).1) F n
      (fun l hl => by
        rw [hF, ← hΛ']
        exact hα _ ((hΛ _).2 (by rwa [hc])))
      (fun x y => by
        have e := hH (c x) (c y)
        rw [hc, hc] at e
        have a1 : ((|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L)
        have a2 : ((|(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L')
        have hn' := congrArg (fun r : ℝ => (r : ℂ)) hn
        simp only [Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.mul_conj] at hn'
        rw [hF, hF, hH', e, map_mul, ← mul_div_assoc, div_eq_div_iff a2 a1]
        linear_combination (c x * starRingEnd ℂ (c y)) * hn')
    refine ⟨f, hf, ?_⟩
    have h1 := HomLinear.isDiff_comp u u' f F hFf tv hw
    rw [hF, hc1, _root_.mul_one] at h1
    have hx := (LieMultiple.isLieComb_one_iff_comp α t₁ _).2 rfl
    have hxt : IsTangent (Chart.spMap (Chart.scaleD α) ≫ t₁) :=
      (Chart.isTan_iff _).1 (Chart.isTan_scale α ((Chart.isTan_iff _).2 tt))
    have := (he' (α • w')).unique ⟨HomLinear.isTangent_comp f tv, h1⟩
      ⟨hxt, CMNormIdentity.isDiff_of_isLieComb u' hw' α hx⟩
    rw [this]
    exact hx
  · intro h z hz
    obtain ⟨P₁, φ₁, hφ⟩ := exists_isPolFibre hB s P
    obtain ⟨Q₁, ψ₁, hψ⟩ := exists_isPolFibre hB s Q
    obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨t₁, ht₁, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
    obtain ⟨f, hf, hl⟩ := h P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, -, -, -, -, -, hd, -⟩ := hU P₁ rig hrig
    obtain ⟨u', -, -, -, -, -, hd', he', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨-, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨-, hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    obtain ⟨F, -, hF, hT, -⟩ := HomLinear.exists_linear_of_isMonHom P₁.A Q₁.A P₁.isAb Q₁.isAb P₁.L Q₁.L _ _ u u'
      hd' he' f hf
    obtain ⟨tf, df⟩ := hT w v₁ tv hw
    have e : F w = α • w' := (hd' _ tf).unique df (CMNormIdentity.isDiff_of_isLieComb u' hw' α hl)
    have := hF _ ((hΛ z).1 hz)
    rw [map_smul, e, smul_smul, _root_.mul_comm] at this
    exact (hΛ' _).2 this

end GlobalTheory.EllipticHom
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.HomDerivative

theorem isLieComb_inv {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {v x : epsR R ⟶ G} {a : R}
    (hv : IsTangent v) (hx : IsLieComb ![a] ![v] x) : IsLieComb ![-a] ![v] x⁻¹ := by
  obtain ⟨y, hy⟩ : ∃ y, IsLieComb ![-a] ![v] y :=
    ⟨_, (GlobalTheory.LieMultiple.isLieComb_one_iff_comp (-a) v _).2 rfl⟩
  have hsum := (GlobalTheory.LieMultiple.lieMultiple_calculus R G G v x y a (-a)).2.1 hv hx hy
  have hone := (GlobalTheory.LieMultiple.lieMultiple_calculus R G G v x y a (-a)).2.2.2.2.2 hv
  rw [add_neg_cancel] at hsum
  have hxy : x * y = 1 :=
    ((GlobalTheory.LieMultiple.isLieComb_one_iff_comp 0 v _).1 hsum).trans
      ((GlobalTheory.LieMultiple.isLieComb_one_iff_comp 0 v _).1 hone).symm
  rw [← eq_inv_of_mul_eq_one_right hxy]
  exact hy

theorem hom_derivative_closure : Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (S : Set R₁), IsTangent t → (∀ a ∈ S, (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre ρ P P₁ φ₁ → IsPolFibre ρ Q Q₁ ψ₁ → IsVecOver ρ φ₁ v v₁ → IsVecOver ρ ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁))) → ∀ a ∈ AddSubgroup.closure S, (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre ρ P P₁ φ₁ → IsPolFibre ρ Q Q₁ ψ₁ → IsVecOver ρ φ₁ v v₁ → IsVecOver ρ ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) := by
  intro _ R _ P Q v t R₁ _ ρ S ht hS a ha
  induction ha using AddSubgroup.closure_induction with
  | mem a h => exact hS a h
  | zero =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    refine ⟨toUnit _ ≫ η, inferInstance, ?_⟩
    have h1 : v₁ ≫ toUnit P₁.A ≫ η[Q₁.A] = 1 := by
      rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (v₁ ≫ toUnit _) (toUnit _)]
      rfl
    rw [h1]
    exact (GlobalTheory.LieMultiple.lieMultiple_calculus R₁ Q₁.A Q₁.A t₁ t₁ t₁ 0 0).2.2.2.2.2 hT
  | add a b _ _ iha ihb =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    obtain ⟨f, hf, hfa⟩ := iha P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    obtain ⟨g, hg, hgb⟩ := ihb P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    refine ⟨lift f g ≫ μ, inferInstance, ?_⟩
    change IsLieComb _ _ (v₁ ≫ (f * g))
    rw [MonObj.comp_mul]
    exact (GlobalTheory.LieMultiple.lieMultiple_calculus R₁ Q₁.A Q₁.A t₁ (v₁ ≫ f) (v₁ ≫ g) a b).2.1 hT hfa hgb
  | neg a _ iha =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    obtain ⟨f, hf, hfa⟩ := iha P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    refine ⟨f⁻¹, inferInstance, ?_⟩
    rw [GrpObj.comp_inv]
    exact isLieComb_inv hT hfa

end GlobalTheory.HomDerivative
end
end
