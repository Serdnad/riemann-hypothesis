module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericExt

universe u

theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

theorem exists_hom_specStalk {W Y T X : Scheme.{u}} (j : W ⟶ Y) [IsSchemeTheoreticallyDominant j]
    [QuasiCompact j] [X.IsSeparated] (F : W ⟶ X) (g' : T ⟶ Y) [Flat g'] (g : T ⟶ X)
    (H : ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) (p : T) :
    ∃ φ : Spec (Y.presheaf.stalk (g' p)) ⟶ X, ∀ (Z : Scheme.{u})
      (ρ : Z ⟶ Spec (Y.presheaf.stalk (g' p))) (r : Z ⟶ W),
      r ≫ j = ρ ≫ Y.fromSpecStalk (g' p) → r ≫ F = ρ ≫ φ := by
  let h := Spec.map (g'.stalkMap p)
  obtain ⟨h₁, h₂⟩ : Flat h ∧ Surjective h :=
    (flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_stalkMap_of_flat g' p)
  have hh : h ≫ Y.fromSpecStalk (g' p) = T.fromSpecStalk p ≫ g' :=
    Scheme.SpecMap_stalkMap_fromSpecStalk g'
  have := flat_fromSpecStalk Y (g' p)
  have key : pullback.fst h h ≫ T.fromSpecStalk p ≫ g = pullback.snd h h ≫ T.fromSpecStalk p ≫ g := by
    let q := pullback.fst h h ≫ h ≫ Y.fromSpecStalk (g' p)
    have hq : Flat q := inferInstance
    refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst q j) (terminal.from X) ?_
      (terminal.hom_ext _ _)
    have e₁ := H _ (pullback.fst q j ≫ pullback.fst h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]; simp only [q, Category.assoc, hh])
    have e₂ := H _ (pullback.fst q j ≫ pullback.snd h h ≫ T.fromSpecStalk p) (pullback.snd q j) (by
      rw [← pullback.condition]
      simp only [q, Category.assoc, ← hh, pullback.condition_assoc])
    simpa only [Category.assoc] using e₁.symm.trans e₂
  let φ := EffectiveEpi.desc h (T.fromSpecStalk p ≫ g) (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hφ : h ≫ φ = T.fromSpecStalk p ≫ g := EffectiveEpi.fac _ _ _
  refine ⟨φ, fun Z ρ r hr => ?_⟩
  rw [← cancel_epi (pullback.fst ρ h), pullback.condition_assoc, hφ]
  have := H _ (pullback.snd ρ h ≫ T.fromSpecStalk p) (pullback.fst ρ h ≫ r) (by
    rw [Category.assoc, hr, pullback.condition_assoc, hh, Category.assoc])
  simpa only [Category.assoc] using this

theorem exists_extension {W Y X S : Scheme.{u}} (j : W ⟶ Y) [IsOpenImmersion j] [IsDominant j]
    [QuasiCompact j] [IsIntegral Y] [S.IsSeparated] (sY : Y ⟶ S) (sX : X ⟶ S) [IsSeparated sX]
    [LocallyOfFiniteType sX] (F : W ⟶ X) (hF : F ≫ sX = j ≫ sY)
    (H : ∀ y : Y, y ∉ Set.range j → ∃ (T : Scheme.{u}) (g' : T ⟶ Y) (g : T ⟶ X), Flat g' ∧ y ∈ Set.range g' ∧
      ∀ (Z : Scheme.{u}) (ρ : Z ⟶ T) (r : Z ⟶ W), r ≫ j = ρ ≫ g' → r ≫ F = ρ ≫ g) :
    ∃ ψ : Y ⟶ X, j ≫ ψ = F ∧ ψ ≫ sX = sY := by
  have hX : X.IsSeparated := ⟨by rw [← terminal.comp_from sX]; infer_instance⟩
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  let e₀ := Y.fromSpecStalk (genericPoint Y)
  have : IsDominant e₀ := isDominant_fromSpecStalk_genericPoint Y
  have hr : Set.range e₀ ⊆ Set.range j := by
    rw [Scheme.range_fromSpecStalk]
    intro z hz
    have hg : genericPoint Y ∈ Set.range j :=
      (genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range |>.2
        (by simpa [Set.range_nonempty_iff_nonempty] using j.denseRange.nonempty)
    exact Specializes.mem_open hz j.isOpenEmbedding.isOpen_range hg
  let e := IsOpenImmersion.lift j e₀ hr
  have he : e ≫ j = e₀ := IsOpenImmersion.lift_fac _ _ _
  have loc : ∀ y : Y, ∃ (U : Scheme.{u}) (k : U ⟶ Y) (_ : IsOpenImmersion k) (ψ : U ⟶ X)
      (l : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ U),
      y ∈ Set.range k ∧ l ≫ k = e₀ ∧ l ≫ ψ = e ≫ F := by
    intro y
    by_cases hy : y ∈ Set.range j
    · exact ⟨W, j, inferInstance, F, e, hy, he, rfl⟩
    obtain ⟨T, g', g, hg', ⟨p, rfl⟩, hT⟩ := H y hy
    obtain ⟨φ, hφ⟩ := exists_hom_specStalk j F g' g hT p
    have := flat_fromSpecStalk Y (g' p)
    have hover : φ ≫ sX = Y.fromSpecStalk (g' p) ≫ sY := by
      refine hom_ext_of_isSchemeTheoreticallyDominant (pullback.fst (Y.fromSpecStalk (g' p)) j)
        (terminal.from S) ?_ (terminal.hom_ext _ _)
      rw [← reassoc_of% (hφ _ _ _ pullback.condition.symm), hF, pullback.condition_assoc]
    obtain ⟨U, hU, ψ, h₁, -⟩ := spread_out_of_isGermInjective' sY sX φ hover
    let m := Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes (g' p)))
    have hm : m ≫ Y.fromSpecStalk (g' p) = e₀ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    refine ⟨U, U.ι, inferInstance, ψ, m ≫ U.fromSpecStalkOfMem _ hU, ⟨⟨_, hU⟩, rfl⟩, ?_, ?_⟩
    · rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hm]
    · rw [Category.assoc, ← h₁]
      exact (hφ _ m e (he.trans hm.symm)).symm
  choose U k hk ψ l hy hl hψ using loc
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y U k (fun y => ⟨y, hy y⟩) hk
  have hc : ∀ a b : Y, pullback.fst (k a) (k b) ≫ ψ a = pullback.snd (k a) (k b) ≫ ψ b := by
    intro a b
    let m := pullback.lift (l a) (l b) ((hl a).trans (hl b).symm)
    have : IsReduced (pullback (k a) (k b)) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ k a)
    have : IsDominant (m ≫ pullback.fst _ _ ≫ k a) := by
      rw [pullback.lift_fst_assoc, hl]
      infer_instance
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ k a)
    refine ext_of_isDominant m ?_
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hψ, hψ]
  have hι : ∀ a : Y, k a ≫ 𝒰.glueMorphisms ψ hc = ψ a := fun a => 𝒰.ι_glueMorphisms ψ hc a
  have h1 : j ≫ 𝒰.glueMorphisms ψ hc = F := by
    have : IsReduced W := isReduced_of_isOpenImmersion j
    have : IsDominant (e ≫ j) := by rw [he]; infer_instance
    have : IsDominant e := .of_comp_of_isOpenImmersion e j
    refine ext_of_isDominant e ?_
    rw [reassoc_of% he, ← hl (genericPoint Y), Category.assoc, hι, hψ]
  refine ⟨_, h1, ext_of_isDominant j ?_⟩
  rw [reassoc_of% h1, hF]

theorem isOpenImmersion_jK (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsOpenImmersion (jK R) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ

theorem eq_closedPoint_of_not_mem_range (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (s : Spec (CommRingCat.of R)) (hs : s ∉ Set.range (jK R)) : s = IsLocalRing.closedPoint R := by
  by_cases h : s.asIdeal = ⊥
  · refine (hs ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩).elim
    rw [h]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  · exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (s.isPrime.isMaximal h))

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X' X : Over (Spec (CommRingCat.of R))) [Flat X'.hom] [IsIntegral X'.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom] (f : (Over.pullback (jK R)).obj X' ⟶ (Over.pullback (jK R)).obj X), (∀ x : X'.left, X'.hom x = IsLocalRing.closedPoint R → ∃ (T : Scheme.{0}) (g' : T ⟶ X'.left) (g : T ⟶ X.left), Flat g' ∧ x ∈ Set.range g' ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ T) (r : Z ⟶ ((Over.pullback (jK R)).obj X').left), r ≫ pullback.fst X'.hom (jK R) = ρ ≫ g' → r ≫ f.left ≫ pullback.fst X.hom (jK R) = ρ ≫ g) → ∃ ψ : X' ⟶ X, (Over.pullback (jK R)).map ψ = f := by
  intro R _ _ _ X' X _ _ _ _ f H
  have := isOpenImmersion_jK R
  have : IsDominant (jK R) := DVR.isDominant_jK
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsDominant (pullback.fst X'.hom (jK R)) := inferInstance
  have hf : f.left ≫ pullback.snd X.hom (jK R) = pullback.snd X'.hom (jK R) := Over.w f
  obtain ⟨ψ, h₁, h₂⟩ := exists_extension (pullback.fst X'.hom (jK R)) X'.hom X.hom
    (f.left ≫ pullback.fst X.hom (jK R))
    (by rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]; congr 1)
    (fun y hy => H y (eq_closedPoint_of_not_mem_range R _ fun h => hy (by
      rw [Scheme.Pullback.range_fst]; exact h)))
  refine ⟨Over.homMk ψ h₂, Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩
  · exact (pullback.lift_fst _ _ _).trans h₁
  · exact (Over.w _).trans hf.symm

end GlobalTheory.GenericExt
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowBasis

theorem gs_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {m : ℕ} (a : Fin m → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by simp only [gs_eq f y U h, map_sum]

theorem comb_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {m : ℕ} (s : LB.Sec (LB.LinComb L φ ε)) (b : Fin m → LB.Sec (LB.LinComb L φ ε)) (r : Fin m → Γ(Y, ⊤)) :
    (∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (r i) * (b i).f j) ↔
      ∀ y J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (r i) * sval (b i) (𝟙 Y) y J := by
  have key : ∀ (j : K → L.ι) (y : Y) (hy : y ∈ LB.wchart L φ j),
      gs (𝟙 Y) y (LB.wchart L φ j)
        (∑ i, (Y.presheaf.map (homOfLE (le_top : (LB.LinComb L φ ε).U j ≤ ⊤)).op).hom (r i) * (b i).f j :
          Γ(Y, (LB.LinComb L φ ε).U j)) =
      ∑ i, gs (𝟙 Y) y ⊤ (r i) * gs (𝟙 Y) y (LB.wchart L φ j) ((b i).f j) := fun j y hy =>
    (gs_sum (𝟙 Y) y _ hy _).trans (Finset.sum_congr rfl fun i _ =>
      (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg (· * _) (gs_res (𝟙 Y) y le_top hy _)))
  constructor
  · intro h y J hJ
    exact (congrArg (gs (𝟙 Y) y _) (h _)).trans (key _ y (hJ.mem φ (𝟙 Y)))
  · intro h j
    refine fn_ext fun y hy => ?_
    choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    refine ((sec_trans s (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans ?_)).trans
      (key j y hy).symm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_trans (b i) (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y)), mul_left_comm]
    rfl

theorem exists_basis_of_formEq {S : Scheme.{0}} {A T : Over S} {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((T ⊗ A).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((T ⊗ A).left ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') {m : ℕ}
    {b : Fin m → LB.Sec (LB.LinComb L φ ε)} (hb : IsSecBasis _ b) :
    ∃ b' : Fin m → LB.Sec (LB.LinComb L φ' ε'), IsSecBasis _ b' := by
  choose b' hb' using fun i => exists_sec hL h (b i)
  refine ⟨b', fun t => ?_⟩
  obtain ⟨s, hs⟩ := exists_sec hL (φ := φ') (ε := ε') (φ' := φ) (ε' := ε) (fun U _ g => (h U g).symm) t
  refine (existsUnique_congr fun r => ?_).1 (hb s)
  refine (comb_iff hL s b fun i => (fst T A).left.appTop.hom (r i)).trans
    (Iff.trans ?_ (comb_iff hL t b' fun i => (fst T A).left.appTop.hom (r i)).symm)
  refine forall_congr' fun y => forall_congr' fun J => forall_congr' fun hJ => ?_
  rw [hs _ _ y J hJ]
  simp only [hb' _ _ _ y J hJ]

theorem translPt_one {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) :
    translPt A (1 : T ⟶ A) = snd T A := by
  have e : translPt A (1 : T ⟶ A) = (fst T A ≫ (1 : T ⟶ A)) * snd T A := rfl
  rw [e, MonObj.comp_one, _root_.one_mul]

theorem exists_basis_pow (hT : SecTwistSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : 1 ≤ k) (R : Type) [CommRing R]
    [IsLocalRing R] (t : Spec (CommRingCat.of R) ⟶ S) :
    ∃ b : Fin (k ^ P.g) → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk t)), IsSecBasis _ b := by
  obtain ⟨⟨b, hb⟩, -⟩ := hT S P k hk R t 1
  refine exists_basis_of_formEq P.isLB (fun U _ g => ?_) hb
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, translPt_one, Fintype.prod_unique]
  rw [← zpow_add, sub_add_cancel]

theorem exists_basis_pow_field : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∀ t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∃! c : Fin (k ^ A.g) → F, ∀ j, t.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j := by
  intro hT R _ _ A F _ _ k hk
  obtain ⟨b, hb⟩ := exists_basis_pow hT A k hk F (jFK (R := R) F)
  refine ⟨b, fun t => ?_⟩
  obtain ⟨r, hr, hu⟩ := hb t
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i), fun j => ?_, fun c hc => ?_⟩
  · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (fun x => liftFun A.A _ x * (b i).f j)
      ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply (r i)).symm
  · have e := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) hc
    funext i
    rw [← congrFun e i]
    exact ((Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply (c i)).symm

end GlobalTheory.PowBasis
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gm_mul_eq_of_res_mul_eq {Y Z : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂}
    {h₃ : V ≤ U₃} {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : res h₁ a * res h₂ b = res h₃ c * res h₄ d) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ V) :
    gm r z U₁ a * gm r z U₂ b = gm r z U₃ c * gm r z U₄ d := by
  have e := congrArg (gm r z V) H
  rwa [map_mul, map_mul, gm_res r z h₁ hz, gm_res r z h₂ hz, gm_res r z h₃ hz, gm_res r z h₄ hz] at e

theorem res_mul_eq_of_gm_mul_eq {Y : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂}
    {h₃ : V ≤ U₃} {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : ∀ y ∈ V, gm (𝟙 Y) y U₁ a * gm (𝟙 Y) y U₂ b = gm (𝟙 Y) y U₃ c * gm (𝟙 Y) y U₄ d) :
    res h₁ a * res h₂ b = res h₃ c * res h₄ d := by
  apply unit_ext
  intro y hy
  rw [map_mul, map_mul, gm_res (𝟙 Y) y h₁ hy, gm_res (𝟙 Y) y h₂ hy, gm_res (𝟙 Y) y h₃ hy,
    gm_res (𝟙 Y) y h₄ hy]
  exact H y hy

theorem square_res_iff_gw {X X' G G' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {L : LB G} {L' : LB G'}
    {F : X' ⟶ X} {B : G' ⟶ G} {p : Y ⟶ X} {p' : Y' ⟶ X'} {f : Y ⟶ G} {f' : Y' ⟶ G'} {h : Y' ⟶ Y}
    (hf : h ≫ f = f' ≫ B) (hp : p' ≫ F = h ≫ p)
    (wM : LB.Iso M' (M.pull F)) (wL : LB.Iso L' (L.pull B))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) :
    (∀ (jM : PUnit → M.ι) (jM' : M'.ι) (jL' : L'.ι) (jL : PUnit → L.ι),
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_left) :
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM') ⊓
            (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') ⊓
            h ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (jM, jL) ⊓
            f' ⁻¹ᵁ (LB.div (L.pull B) L').U (jL, jL') ≤
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM'))
        (pullU p' _ (wM.s (jM, jM'))) *
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (w'.s (fun _ => jM', fun _ => jL')) =
      res (X := Y') (inf_le_left.trans inf_le_right) (pullU h _ (w.s (jM, jL))) *
      res (X := Y') inf_le_right (pullU f' _ (wL.s (jL, jL')))) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      F (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → B (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL' := by
  have ef : ∀ y : Y', f (h y) = B (f' y) := fun y => congrArg (fun g => g y) hf
  have ep : ∀ y : Y', p (h y) = F (p' y) := fun y => congrArg (fun g => g y) hp.symm
  constructor
  · intro H Z r z jM jM' jL jL' h₁ h₂ h₃ h₄
    have m₁ : p' (r z) ∈ (LB.div (M.pull F) M').U (fun _ => jM, jM') := ⟨mem_pull.2 h₁, h₂⟩
    have m₂ : r z ∈ (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') :=
      ⟨mem_pull.2 h₂, mem_pull.2 h₄⟩
    have m₃ : h (r z) ∈ (LB.div (M.pull p) (L.pull f)).U (fun _ => jM, fun _ => jL) :=
      ⟨mem_pull.2 (by rw [ep]; exact h₁), mem_pull.2 (by rw [ef]; exact h₃)⟩
    have m₄ : f' (r z) ∈ (LB.div (L.pull B) L').U (fun _ => jL, jL') := ⟨mem_pull.2 h₃, h₄⟩
    have e := gm_mul_eq_of_res_mul_eq (H (fun _ => jM) jM' jL' (fun _ => jL)) r z ⟨⟨⟨m₁, m₂⟩, m₃⟩, m₄⟩
    rw [gm_pull r p' z _ m₁, gm_pull r h z _ m₃, gm_pull r f' z _ m₄] at e
    exact e
  · intro H jM jM' jL' jL
    refine res_mul_eq_of_gm_mul_eq fun y hy => ?_
    have e := H Y' (𝟙 Y') y (jM PUnit.unit) jM' (jL PUnit.unit) jL' (mem_pull.1 hy.1.1.1.1) hy.1.1.1.2
      (mem_pull.1 hy.2.1) hy.2.2
    rw [gm_pull (𝟙 Y') p' y _ hy.1.1.1, gm_pull (𝟙 Y') h y _ hy.1.2, gm_pull (𝟙 Y') f' y _ hy.2]
    exact e

theorem isPullUnif_iff_stalks : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' ↔ ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wL.IsGen ∧ ∃ he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G, LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) ∧ ∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL') := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc U U'
  constructor
  · rintro ⟨wL, hg, he, hr, H⟩
    refine ⟨wL, hg, he, hr, fun e => ?_⟩
    obtain ⟨h, hf, hp, ht, hw⟩ := H e
    refine ⟨h, hf, ⟨hp, fun x => ?_⟩, (square_res_iff_gw hf hp hD.w wL (U.w e) (U'.w e)).1 hw⟩
    obtain ⟨hψ, hm⟩ := ht x
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ h _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩
  · rintro ⟨wL, hg, he, hr, H⟩
    refine ⟨wL, hg, he, hr, fun e => ?_⟩
    obtain ⟨h, hf, ⟨hp, ht⟩, hw⟩ := H e
    refine ⟨h, hf, hp, fun x => ?_, (square_res_iff_gw hf hp hD.w wL (U.w e) (U'.w e)).2 hw⟩
    obtain ⟨hψ, hm⟩ := ht x
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ h _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2 hm⟩

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_id_eq_zero_iff {Y : Scheme.{0}} [IsIntegral Y] (y : Y) (U : Y.Opens) (hy : y ∈ U) (a : Γ(Y, U)) :
    gs (𝟙 Y) y U a = 0 ↔ a = 0 := by
  have e : gs (𝟙 Y) y U a = (Y.presheaf.germ U y hy).hom a := gs_eq (𝟙 Y) y U hy a
  rw [e]
  exact map_eq_zero_iff _ (germ_injective_of_isIntegral Y y hy)

theorem exists_ne_zero_iff_sval_ne_zero {Y X : Scheme.{0}} [IsIntegral Y] {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    (∃ j, s.f j ≠ 0) ↔ sval s (𝟙 Y) y J ≠ 0 := by
  have hm : y ∈ LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k)) := hJ.mem φ (𝟙 Y)
  constructor
  · rintro ⟨j, hj⟩ h0
    apply hj
    have h1 : s.f (fun k => J (𝟙 Y ≫ φ k)) = 0 := (gs_id_eq_zero_iff y _ hm _).1 h0
    refine fn_ext (V := LB.wchart L φ j) fun x hx => ?_
    have hne : (LB.wchart L φ j : Set Y).Nonempty := ⟨x, hx⟩
    obtain ⟨w, hw, hw'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen
      (LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k))).isOpen hne ⟨y, hm⟩
    have h2 := sec_trans s (𝟙 Y) w hw hw'
    have h3 : gs (𝟙 Y) w (LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k))) (s.f (fun k => J (𝟙 Y ≫ φ k))) = 0 :=
      (gs_id_eq_zero_iff w _ hw' _).2 h1
    rw [h3, mul_zero] at h2
    exact congrArg (gs (𝟙 Y) x (LB.wchart L φ j)) ((gs_id_eq_zero_iff w _ hw _).1 h2)
  · intro h
    exact ⟨fun k => J (𝟙 Y ≫ φ k), fun h0 => h ((gs_id_eq_zero_iff y _ hm _).2 h0)⟩

theorem exists_ne_zero_of_sval_eq_mul_unit : ∀ (Y X : Scheme.{0}) [IsIntegral Y] (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (φ'' : K'' → (Y ⟶ X)) (ε'' : K'' → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (d : LB.Sec (LB.LinComb L φ'' ε'')), (∀ (y : Y) (J), Good L y J → ∃ v : (Y.presheaf.stalk y)ˣ, sval d (𝟙 Y) y J = sval s (𝟙 Y) y J * sval s' (𝟙 Y) y J * v.val) → (∃ j, s.f j ≠ 0) → (∃ j, s'.f j ≠ 0) → ∃ j, d.f j ≠ 0 := by
  intro Y X _ L hL K K' K'' _ _ _ φ ε φ' ε' φ'' ε'' s s' d h hs hs'
  choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ (genericPoint Y))
  have hG : Good L (genericPoint Y) J := hJ
  obtain ⟨v, hv⟩ := h _ J hG
  rw [exists_ne_zero_iff_sval_ne_zero _ hG] at hs hs' ⊢
  rw [hv]
  exact mul_ne_zero (mul_ne_zero hs hs') v.ne_zero

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem levelff_stalkMap_injective {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have h := Flat.stalkMap f x
  have hl : IsLocalHom (f.stalkMap x).hom := inferInstance
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem levelff_gs_comp {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (p z) ∈ U)
    (a : Γ(X, U)) : gs (p ≫ r) z U a = (p.stalkMap z).hom (gs r (p z) U a) := by
  rw [← gs_pull p r z U h, gs_eq p z (r ⁻¹ᵁ U) h, gs_eq r (p z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply p (r ⁻¹ᵁ U) z h _).symm

theorem sval_eq_zero_of_faithfullyFlat_base : ∀ (R W : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W] (I : Ideal R) (e : ℕ) (Y : Over (Spec (CommRingCat.of R))) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left) (ω : Z ⟶ Spec (CommRingCat.of W)), ω ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = r ≫ Y.hom → (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R W _ _ _ _ I e Y X L hL K _ φ ε d H Z r hρ z J hJ
  let g : Spec (CommRingCat.of W) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R W))
  have hg : Flat g ∧ Surjective g := by
    refine (flat_and_surjective_SpecMap_iff _).2 ?_
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  obtain ⟨_, _⟩ := hg
  let p : pullback (r ≫ Y.hom) g ⟶ Z := pullback.fst _ _
  have : Flat p := inferInstance
  have : Surjective p := inferInstance
  obtain ⟨z', rfl⟩ := p.surjective z
  obtain ⟨ρ, hρ⟩ := hρ
  choose J' hJ' using fun χ : pullback (r ≫ Y.hom) g ⟶ X => exists_chart hL (χ z')
  have h0 := H _ (p ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition.symm)
    ⟨p ≫ ρ, by rw [Category.assoc, hρ, Category.assoc]⟩ z' J' hJ'
  have hm : r (p z') ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have h1 := sec_trans d (p ≫ r) z' (j := fun k => J (r ≫ φ k)) hm (Good.mem hJ' φ (p ≫ r))
  have h2 : gs (p ≫ r) z' (LB.wchart L φ (fun k => J (r ≫ φ k))) (d.f (fun k => J (r ≫ φ k))) = 0 :=
    h1.trans ((congrArg _ h0).trans (mul_zero _))
  apply levelff_stalkMap_injective p z'
  rw [map_zero]
  exact (levelff_gs_comp p r z' _ hm _).symm.trans h2

end GlobalTheory
end
