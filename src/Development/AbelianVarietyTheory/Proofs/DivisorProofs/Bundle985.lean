module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle970
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
import Development.DiscreteGroups.GlobalIrreducibility.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

section Step

variable {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I J : Ideal R} {I₁ : Ideal R₁}
  {κ : DividedPowers I} {π : R →+* R₀} {hJ : J ^ 2 = 0} {ρ : R →+* R₁} {κ₁ : DividedPowers I₁}
  {π₁ : R₁ →+* R₀}

theorem IsStep.spMap_eq (st : IsStep κ π hJ ρ κ₁ π₁) : spMap π = spMap π₁ ≫ spMap ρ := by
  rw [← st.comp, Cris.spMap_comp]

theorem IsStep.idMor (st : IsStep κ π hJ ρ κ₁ π₁) (A₀ : Over (Sp R₀)) [GrpObj A₀] :
    GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) :=
  ⟨st.dp, by simpa using st.spMap_eq, by simp, by
    intro T x y x₀ y₀ hx hy
    have ex : x₀ = x := Over.OverMorphism.ext (by simpa using hx)
    have ey : y₀ = y := Over.OverMorphism.ext (by simpa using hy)
    subst x₀; subst y₀
    exact Category.comp_id _ |>.symm⟩

def redSub (hρ : Function.Surjective ρ) {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A]
    {i₂ : A₁.left ⟶ A.left} (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (F : Submodule R (HdR A)) :
    Submodule R₁ (HdR A₁) where
  carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
  add_mem' := by
    rintro y y' ⟨x, hx, e⟩ ⟨x', hx', e'⟩
    exact ⟨x + x', F.add_mem hx hx', fun c ↦ by
      rw [LinearMap.add_apply, LinearMap.add_apply, e, e', map_add (f := _)]⟩
  zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
  smul_mem' := by
    rintro r₁ y ⟨x, hx, e⟩
    obtain ⟨r, rfl⟩ := hρ r₁
    exact ⟨r • x, F.smul_mem r hx, fun c ↦ by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, e, map_mul]⟩

theorem mem_liftFil_iff (P : AbelianDeRham) (st : IsStep κ π hJ ρ κ₁ π₁) {g : ℕ} {A₀ : Over (Sp R₀)}
    [GrpObj A₀] {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A] {i₁ : A₀.left ⟶ A₁.left}
    {i₂ : A₁.left ⟶ A.left} {i : A₀.left ⟶ A.left} (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁)
    (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i) (ei : i₁ ≫ i₂ = i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    d₁ ∈ liftFil κ₁ h₁ ↔ ∃ d ∈ liftFil κ h, (st.idMor A₀).Corr d d₁ := by
  have T := GlobalTheory.T.hodgeFiltration_middle_eq_reduction_of_top P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
    (st.idMor A₀) (Fil A) (redSub st.surj h₂ (Fil A)) (fun _ ↦ Iff.rfl)
  have e : Fil A₁ = redSub st.surj h₂ (Fil A) := Submodule.ext T.2
  rw [liftFil, Submodule.mem_comap, e, T.1 d₁]
  exact Iff.rfl

theorem dualMap_push {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀] {A₁ B₁ : Over (Sp R₁)} [GrpObj A₁]
    [GrpObj B₁] {i₁ : A₀.left ⟶ A₁.left} {j₁ : B₀.left ⟶ B₁.left}
    (NA : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁)
    (NB : GrpMor (divided₂ hJ) (spMap ρ) B₁ κ (spMap π) B₀ (RingHom.id R) (spMap π₁) j₁)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) [IsMonHom f₀] [IsMonHom f₁] (e : i₁ ≫ f₁.left = f₀.left ≫ j₁)
    (d : Crys κ (spMap π) A₀) :
    (NB.pull : prim (divided₂ hJ) (spMap ρ) B₁ →ₗ[R] prim κ (spMap π) B₀).dualMap (push κ (spMap π) f₀ d) =
      push (divided₂ hJ) (spMap ρ) f₁
        ((NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  refine LinearMap.ext fun c ↦ ?_
  let m : GrpMor (divided₂ hJ) (spMap ρ) B₁ κ (spMap π) A₀
      (RingHom.id R) (spMap π₁ ≫ 𝟙 _) (i₁ ≫ f₁.left) := by
    refine ⟨NA.dp, ?_, ?_, ?_⟩
    · simpa using NA.base
    · simpa only [Category.comp_id, Category.assoc, Over.w f₁] using NA.w
    · intro T x y x₀ y₀ hx hy
      let x₁ : Over.mk (T.hom ≫ spMap π₁) ⟶ A₁ :=
        Over.homMk (x.left ≫ i₁) (by simp only [Over.mk_hom, Category.assoc, NA.w, reassoc_of% (Over.w x)])
      let y₁ : Over.mk (T.hom ≫ spMap π₁) ⟶ A₁ :=
        Over.homMk (y.left ≫ i₁) (by simp only [Over.mk_hom, Category.assoc, NA.w, reassoc_of% (Over.w y)])
      let x₂ : Over.mk ((Over.mk (T.hom ≫ spMap π₁)).hom ≫ 𝟙 _) ⟶ B₁ :=
        Over.homMk x₀.left (by simpa using Over.w x₀)
      let y₂ : Over.mk ((Over.mk (T.hom ≫ spMap π₁)).hom ≫ 𝟙 _) ⟶ B₁ :=
        Over.homMk y₀.left (by simpa using Over.w y₀)
      have h₁ := NA.mul T x y x₁ y₁ rfl rfl
      have h₂ := (homMor (divided₂ hJ) (spMap ρ) f₁).mul _ x₁ y₁ x₂ y₂
        (by simpa [x₂, x₁, Category.assoc] using hx)
        (by simpa [y₂, y₁, Category.assoc] using hy)
      have h₃ : (x₀ * y₀).left = (x₂ * y₂).left := by
        simp [Hom.mul_def, Over.comp_left, Over.lift_left, x₂, y₂]
      rw [h₃, h₂, h₁, Category.assoc]
  have e1 : (homMor κ (spMap π) f₀).pull (NB.pull c) = m.pull c :=
    GrpMor.pull_pull NB (homMor κ (spMap π) f₀) m (fun _ ↦ rfl) e.symm c
  have e2 : NA.pull ((homMor (divided₂ hJ) (spMap ρ) f₁).pull c) = m.pull c :=
    GrpMor.pull_pull (homMor (divided₂ hJ) (spMap ρ) f₁) NA m (fun _ ↦ rfl) rfl c
  exact congrArg d (e1.trans e2.symm)

end Step

theorem liftHom_of_isStep : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftHom (divided₂ hJ) ρ → LiftHom κ₁ π₁ → LiftHom κ π := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ st H₂ H₁
  intro g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have hc : spMap (π₁.comp ρ) = spMap π := by rw [st.comp]
  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, ei, hA₁, hgA⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g A₀ A i (by rw [hc]; exact h) hA hg
  obtain ⟨B₁, _, j₁, j₂, k₁, k₂, ej, hB₁, hgB⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g' B₀ B j (by rw [hc]; exact k) hB hg'

  have hf₁ : ∀ d₁ ∈ liftFil κ₁ h₁, push κ₁ (spMap π₁) f₀ d₁ ∈ liftFil κ₁ k₁ := by
    intro d₁ hd₁
    obtain ⟨d, hd, e⟩ := (mem_liftFil_iff P st h₁ h₂ h ei hA hg d₁).1 hd₁
    exact (mem_liftFil_iff P st k₁ k₂ k ej hB hg' _).2
      ⟨_, hf d hd, GrpMor.Corr.push (st.idMor B₀) f₀ f₀ (by simp) e⟩
  obtain ⟨f₁, ⟨_, ef₁⟩, uf₁⟩ := H₁ g A₀ A₁ i₁ h₁ hA₁ hgA g' B₀ B₁ j₁ k₁ hB₁ hgB f₀ hf₁

  obtain ⟨NA, bA, cA⟩ := GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
  obtain ⟨NB, -, cB⟩ := GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g' B₀ B₁ B j₁ j₂ j k₁ k₂ k ej hB hg'
  have sA : Function.Surjective
      (NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap :=
    (LinearEquiv.ofBijective _ bA).dualMap.surjective
  have hf₂ : ∀ e ∈ liftFil (divided₂ hJ) h₂, push (divided₂ hJ) (spMap ρ) f₁ e ∈ liftFil (divided₂ hJ) k₂ := by
    intro e he
    obtain ⟨d, rfl⟩ := sA e
    have hd : d ∈ liftFil κ h := by
      rw [liftFil, Submodule.mem_comap, cA]; exact he
    have hk := hf d hd
    rw [liftFil, Submodule.mem_comap, cB] at hk
    rw [liftFil, Submodule.mem_comap, ← dualMap_push NA NB f₀ f₁ ef₁ d]
    exact hk
  obtain ⟨f, ⟨_, ef⟩, uf⟩ := H₂ g A₁ A i₂ h₂ hA hg g' B₁ B j₂ k₂ hB hg' f₁ hf₂
  refine ⟨f, ⟨inferInstance, ?_⟩, ?_⟩
  · rw [← ei, ← ej, Category.assoc, ef, ← Category.assoc, ef₁, Category.assoc]
  · rintro f' ⟨_, ef'⟩
    let f₁' : A₁ ⟶ B₁ := Over.homMk (k₂.1.lift (i₂ ≫ f'.left) A₁.hom
      (by rw [Category.assoc, Over.w f', h₂.1.w])) (k₂.1.lift_snd _ _ _)
    have e₁ : f₁'.left ≫ j₂ = i₂ ≫ f'.left := k₂.1.lift_fst _ _ _
    haveI := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback h₂ k₂ f' f₁' e₁
    have e₂ : i₁ ≫ f₁'.left = f₀.left ≫ j₁ := by
      refine k₂.1.hom_ext ?_ ?_
      · rw [Category.assoc, e₁, ← Category.assoc, ei, ef', Category.assoc, ej]
      · rw [Category.assoc, Category.assoc, Over.w f₁', h₁.1.w, k₁.1.w, ← Category.assoc, Over.w f₀]
    have e₃ : f₁' = f₁ := uf₁ f₁' ⟨inferInstance, e₂⟩
    exact uf f' ⟨inferInstance, by rw [← e₁, e₃]⟩

end GlobalTheory.SqLift
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem corr_crysToDR_step_iff {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I : Ideal R}
    {I₁ : Ideal R₁} {κ : DividedPowers I} {κ₁ : DividedPowers I₁} {π : R →+* R₀} {ρ : R →+* R₁}
    {π₁ : R₁ →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {X₁ : Over (Sp R₁)} [GrpObj X₁] {X : Over (Sp R)}
    [GrpObj X] {i₁ : A₀.left ⟶ X₁.left} {i₂ : X₁.left ⟶ X.left} {i : A₀.left ⟶ X.left}
    (h₁ : IsGrpPullback A₀ X₁ (spMap π₁) i₁) (h₂ : IsGrpPullback X₁ X (spMap ρ) i₂)
    (h : IsGrpPullback A₀ X (spMap π) i) (e : i₁ ≫ i₂ = i)
    (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _))
    (hs : Function.Surjective (liftMor κ h).pull) (d : Crys κ (spMap π) A₀) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
  have k : GrpMor (dp0 R) (𝟙 _) X κ₁ (spMap π₁) A₀
      (ρ.comp (RingHom.id R)) ((𝟙 _) ≫ spMap π) ((𝟙 _) ≫ i) := by
    apply GrpMor.of_isGrpPullback
    · exact IsDPMorphism.comp _ M.dp (liftMor κ h).dp
    · simpa using M.base
    · simpa using h
  have e1 : ∀ c, (liftMor κ₁ h₁).pull ((redMor h₂).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) (by rw [Category.id_comp, e]) c
  have e2 : ∀ c, M.pull ((liftMor κ h).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c
  constructor
  · intro H c
    obtain ⟨c, rfl⟩ := hs c
    have := H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2] at this
    exact this
  · intro H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2]
    exact H _

theorem liftObj_step : AbelianDeRham → AbelianUnobstructed → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁]
    [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftObj (divided₂ hJ) ρ → LiftObj κ₁ π₁ → LiftObj κ π := by
  intro P U R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ S L₂ L₁
  intro g A₀ _ A' _ i' h' hA' hg F hF
  have hπ : Function.Surjective π := S.comp ▸ S.surj₁.comp S.surj
  have hrig := P.2.2.2.1
  have hsp : spMap π = spMap π₁ ≫ spMap ρ := by rw [← S.comp, Cris.spMap_comp]
  have M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) := by
    refine ⟨S.dp, ?_, ?_, ?_⟩
    · simpa using hsp
    · simp
    · intro T x y x₀ y₀ hx hy
      have mul_left {U : Over (Sp R₀)} (a b : U ⟶ A₀) :
          (a * b).left = CategoryTheory.Limits.pullback.lift a.left b.left ((Over.w a).trans (Over.w b).symm) ≫ μ[A₀].left := by
        rw [Hom.mul_def, Over.comp_left, Over.lift_left]
      rw [mul_left, mul_left]
      congr 1
      apply CategoryTheory.Limits.pullback.hom_ext
      · simpa using hx
      · simpa using hy

  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, e₁₂, hA₁, hg₁⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g A₀ A' i' (by rw [S.comp]; exact h') hA' hg
  obtain ⟨F₁, hF₁, hF₁F⟩ :=
    GlobalTheory.T.group_scheme_divided_power_lift_tower P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ A₁ A' i₁ i₂ i' h₁ h₂ h' e₁₂ hA' hg F hF

  obtain ⟨B₁, _, j₁, k₁, hB₁, hgB₁, hfB₁⟩ := L₁ g A₀ A₁ i₁ h₁ hA₁ hg₁ F₁ hF₁
  obtain ⟨C, _, j₂, k₂, hC⟩ := U R J hJ R₁ ρ S.surj S.kerJ B₁ hB₁
  have hgC : SmoothOfRelativeDimension g C.hom :=
    GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction R R₁ ρ S.surj (by rw [S.kerJ]; exact ⟨2, hJ⟩) g C B₁ j₂ k₂.1 hC.smooth hgB₁
  have kC : IsGrpPullback A₀ C (spMap π) (j₁ ≫ j₂) := (k₁.comp k₂).congr hsp.symm rfl
  have b' : Function.Bijective (crysToDR κ h') :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hA' hg S.nil hπ S.ker h'
  have bC : Function.Bijective (crysToDR κ kC) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hC hgC S.nil hπ S.ker kC
  have bB₁ : Function.Bijective (crysToDR κ₁ k₁) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hB₁ hgB₁ S.nil₁ S.surj₁ S.ker₁ k₁
  have s' := (hrig R A' g hA' hg I κ S.nil R₀ π hπ S.ker A₀ i' h').2
  have sC := (hrig R C g hC hgC I κ S.nil R₀ π hπ S.ker A₀ _ kC).2

  set E := F.comap (crysToDR κ h') with hE
  set FC := E.map (crysToDR κ kC) with hFC
  have hFCa : IsAdmissible k₂ FC := by
    obtain ⟨N, hN⟩ := hF.1
    refine ⟨⟨(N.comap (crysToDR κ h')).map (crysToDR κ kC), ?_⟩, fun y ↦ ?_⟩
    · exact (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ bC)).isCompl
        ((Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ b')).symm.isCompl hN)
    obtain ⟨d₁, rfl⟩ := bB₁.2 y
    have l1 : crysToDR κ₁ k₁ d₁ ∈ Fil B₁ ↔ ∃ d ∈ E, M.Corr d d₁ := by
      change d₁ ∈ liftFil κ₁ k₁ ↔ _
      rw [hfB₁, Submodule.mem_comap, hF₁F]
      constructor
      · rintro ⟨x, hx, ex⟩
        obtain ⟨d, rfl⟩ := b'.2 x
        exact ⟨d, hx, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).1 ex⟩
      · rintro ⟨d, hd, ed⟩
        exact ⟨_, hd, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).2 ed⟩
    rw [l1]
    constructor
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).2 ed⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, ex⟩
      exact ⟨d, hd, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).1 ex⟩

  obtain ⟨A, _, j₃, k₃, hA, hgA, hfA⟩ := L₂ g B₁ C j₂ k₂ hC hgC FC hFCa
  have kA : IsGrpPullback A₀ A (spMap π) (j₁ ≫ j₃) := (k₁.comp k₃).congr hsp.symm rfl
  refine ⟨A, inferInstance, j₁ ≫ j₃, kA, hA, hgA, ?_⟩
  obtain ⟨N, -, hNC⟩ :=
    GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ C j₁ j₂ (j₁ ≫ j₂) k₁ k₂ kC rfl hC hgC
  obtain ⟨N', -, hNA⟩ :=
    GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ A j₁ j₃ (j₁ ≫ j₃) k₁ k₃ kA rfl hA hgA
  obtain rfl : N' = N := rfl
  ext d
  change crysToDR κ kA d ∈ Fil A ↔ d ∈ E
  rw [hNA d]
  change _ ∈ liftFil (divided₂ hJ) k₃ ↔ _
  rw [hfA, Submodule.mem_comap, ← hNC d]
  exact ⟨fun ⟨d', hd', e⟩ ↦ bC.1 e ▸ hd', fun hd ↦ ⟨d, hd, rfl⟩⟩

end GlobalTheory.SqLift
end
end

section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.NearOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_valuation_sub_lt_one (a : k) : ∀ᶠ x in nhds a, valuation k (x - a) < 1 := by
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨1, one_ne_zero, subset_rfl⟩
  have hc : Filter.Tendsto (fun x : k => x - a) (nhds a) (nhds 0) := by
    have : Continuous (fun x : k => x - a) := by fun_prop
    simpa using this.tendsto a
  exact hc h0

theorem exists_box_subset_of_mem_nhds_zero {p q : ℕ} {S : Set (Matrix (Fin p) (Fin q) k)} (hS : S ∈ nhds 0) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ box p q d ⊆ S := by
  have hk : ∀ s ∈ nhds (0 : k), ∀ᶠ d in nhds (0 : k), {x : k | valuation k x ≤ valuation k d} ⊆ s := by
    intro s hs
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
    have h0 : {x : k | valuation k x < r} ∈ nhds (0 : k) :=
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨r, hr, subset_rfl⟩
    filter_upwards [h0] with d hd x hx
    exact hrs (lt_of_le_of_lt hx hd)
  have hS' : {x : Fin p → Fin q → k | Matrix.of x ∈ S} ∈ nhds (0 : Fin p → Fin q → k) := hS
  rw [nhds_pi, Filter.mem_pi'] at hS'
  obtain ⟨I, t, ht, hI⟩ := hS'
  have ht' : ∀ i, ∃ u : Fin q → Set k, (∀ j, u j ∈ nhds (0 : k)) ∧ Set.univ.pi u ⊆ t i := by
    intro i
    have h := ht i
    rw [nhds_pi, Filter.mem_pi'] at h
    obtain ⟨J, u, hu, hJ⟩ := h
    exact ⟨u, hu, fun x hx => hJ fun j _ => hx j trivial⟩
  choose u hu hut using ht'
  have hev : ∀ᶠ d in nhds (0 : k), valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j :=
    (eventually_valuation_sub_lt_one 0).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hk _ (hu i j))
  have hne : ∃ d : k, d ≠ 0 ∧ valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j := by
    have hd : (nhdsWithin (0 : k) {0}ᶜ).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
      intro s hs
      obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
      obtain ⟨r', hr', hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
      obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective r
      have hy : y ≠ 0 := by simpa using hr
      refine ⟨r' * y, hrs ?_, mul_ne_zero (by simpa using hr') hy⟩
      show valuation k (r' * y) < valuation k y
      rw [map_mul]
      exact mul_lt_of_lt_one_left (zero_lt_iff.mpr hr) hr1
    exact (eventually_mem_nhdsWithin.and (hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ)))).exists
  obtain ⟨d, hd0, hd1, hdu⟩ := hne
  refine ⟨Units.mk0 d hd0, by simpa using hd1.le, fun X hX => hI fun i _ => hut i fun j _ => hdu i j (hX i j)⟩

theorem one_add_small_near_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ nhds (1 : GL (Fin n) k)) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ ∀ N ∈ box n n d, ∃ A : GL (Fin n) k, A.val = 1 + N ∧ A ∈ U ∧
      valuation k (GeneralLinearGroup.det A : k) = 1 ∧ A⁻¹.val ∈ box n n 1 := by
  have hadd : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => 1 + N) (nhds 0) (nhds 1) := by
    have : Continuous (fun N : Matrix (Fin n) (Fin n) k => 1 + N) := by fun_prop
    simpa using this.tendsto 0
  have hdet : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N).det) (nhds 0) (nhds 1) := by
    have : Continuous (fun M : Matrix (Fin n) (Fin n) k => M.det) := continuous_id.matrix_det
    have h2 := (this.tendsto 1).comp hadd
    rw [det_one] at h2
    exact h2
  have hinv : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N)⁻¹) (nhds 0) (nhds 1) := by
    have : ContinuousAt Inv.inv (1 : Matrix (Fin n) (Fin n) k) := by
      apply continuousAt_matrix_inv
      rw [det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h2 := this.tendsto.comp hadd
    rw [inv_one] at h2
    exact h2
  have hv : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, valuation k (1 + N).det = 1 := by
    filter_upwards [hdet (eventually_valuation_sub_lt_one 1)] with N hN
    have hN' : valuation k ((1 + N).det - 1) < 1 := hN
    have := Valuation.map_one_add_of_lt (valuation k) hN'
    simpa using this
  have hb : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, ∀ i j, valuation k ((1 + N)⁻¹ i j) ≤ 1 := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    have hc : Continuous (fun M : Matrix (Fin n) (Fin n) k => M i j) := continuous_id.matrix_elem i j
    filter_upwards [((hc.tendsto 1).comp hinv) (eventually_valuation_sub_lt_one _)] with N hN
    have hN' : valuation k ((1 + N)⁻¹ i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := hN
    have h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have := Valuation.map_add_le (valuation k) hN'.le h1
    simpa using this
  have hval : ∀ N : Matrix (Fin n) (Fin n) k, valuation k (1 + N).det = 1 → (toGL (1 + N)).val = 1 + N := by
    intro N hN
    have hu : IsUnit (1 + N) := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h
      rw [h] at hN
      simp at hN
    unfold toGL
    rw [dite_eq_left hu]
    rfl
  have hGL : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => toGL (1 + N)) (nhds 0) (nhds 1) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    have h3 := hadd.prodMk_nhds ((MulOpposite.continuous_op.tendsto 1).comp hinv)
    have e : (Units.embedProduct _ (1 : GL (Fin n) k)) = (1, MulOpposite.op 1) := by simp
    rw [e]
    refine Filter.Tendsto.congr' ?_ h3
    filter_upwards [hv] with N hN
    simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, hval N hN]
  obtain ⟨d, hd, hS⟩ := exists_box_subset_of_mem_nhds_zero (p := n) (q := n) (hv.and (hb.and (hGL hU)))
  refine ⟨d, hd, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS hN
  refine ⟨toGL (1 + N), hval N h1, h3, ?_, fun i j => ?_⟩
  · rw [GeneralLinearGroup.val_det_apply, hval N h1, h1]
  · rw [Matrix.coe_units_inv, hval N h1]
    simpa using h2 i j

end GlobalTheory.GamMul.NearOne
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.a6ring_holds : GlobalTheory.EtC.DivisorRingCompatibility := by
  intro q _ E
  exact ⟨fun hE _ _ a => (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE a,
    fun a b c => GlobalTheory.T.tateTwistCupProduct_assoc q E a b c,
    fun a b => GlobalTheory.T.tateTwistCupProduct_graded_comm q E a b⟩

end GlobalTheory
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_quasiLogarithm_of_dualCharacter : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ χ : G.dual.Tate, ∃ (f : MvPowerSeries (Fin d) F.Q) (w : Fin d → F.B), QL μ' ⊤ f ∧ In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) ∧ In (⊤ : Ideal F.B) (frob p F.s f - (p : F.Q) • f) ∧ (∀ i, lin f i = algebraMap F.B F.Q (w i)) ∧ dlog G χ = ∑ i, F.θ (w i) • c.form i ∧ ∀ t, c.HasPeriod F.θ t f (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  first | exact @GlobalTheory.CharLog.exists_log_char_period | exact GlobalTheory.CharLog.exists_log_char_period | (intros; apply GlobalTheory.CharLog.exists_log_char_period <;> assumption)
end
