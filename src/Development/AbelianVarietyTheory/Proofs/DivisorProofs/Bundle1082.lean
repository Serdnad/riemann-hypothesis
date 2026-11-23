module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle004
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescIsoExists

theorem lbIso_pull_fst_snd : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → P.IsLB → IsAdditive P → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → LBIso (P.pull (pullback.fst (q ▷ B).left (q ▷ B).left)) (P.pull (pullback.snd (q ▷ B).left (q ▷ B).left)) := by
  intro K _ _ A A' B _ _ _ q P _ _ _ hq hP hadd hker
  let f := (q ▷ B).left
  have hw : f ≫ (A' ⊗ B).hom = (A ⊗ B).hom := Over.w (q ▷ B)
  let Z : Over (Sp K) := Over.mk (pullback.fst f f ≫ (A ⊗ B).hom)
  have hsnd : pullback.snd f f ≫ (A ⊗ B).hom = pullback.fst f f ≫ (A ⊗ B).hom := by
    rw [← hw, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hB : (q ▷ B) ≫ snd A' B = snd A B := whiskerRight_snd q B
  have hA : (q ▷ B) ≫ fst A' B = fst A B ≫ q := whiskerRight_fst q B
  have hBl : f ≫ (snd A' B).left = (snd A B).left := by rw [← Over.comp_left, hB]
  have hAl : f ≫ (fst A' B).left = (fst A B).left ≫ q.left := by
    rw [← Over.comp_left, hA, Over.comp_left]
  let a : Z ⟶ A := Over.homMk (pullback.fst f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let a' : Z ⟶ A := Over.homMk (pullback.snd f f ≫ (fst A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w]; exact hsnd)
  let b : Z ⟶ B := Over.homMk (pullback.fst f f ≫ (snd A B).left) (by
    simp only [Z, Over.mk_hom, Category.assoc, Over.w])
  let u : Z ⟶ A ⊗ B := Over.homMk (pullback.fst f f) rfl
  let u' : Z ⟶ A ⊗ B := Over.homMk (pullback.snd f f) hsnd
  have hu : lift a b = u := by
    ext1
    · ext; simp [a, u]
    · ext; simp [b, u]
  have hu' : lift a' b = u' := by
    ext1
    · ext; simp [a', u']
    · ext
      simp only [b, u', lift_snd, Over.homMk_left, Over.comp_left]
      rw [← hBl, ← Category.assoc, pullback.condition, Category.assoc]
  have hq' : a ≫ q = a' ≫ q := by
    ext
    simp only [a, a', Over.comp_left, Over.homMk_left, Category.assoc]
    rw [← hAl, ← Category.assoc, pullback.condition, Category.assoc]

  have e1 : (pullback.fst f f : pullback f f ⟶ _) = (lift a b).left := by rw [hu]; rfl
  have e2 : (pullback.snd f f : pullback f f ⟶ _) = (lift a' b).left := by rw [hu']; rfl
  refine (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).1 ?_
  have c1 : cls _ (pull_isLB hP (pullback.fst f f)) = evc hP a b := by
    rw [cls_pull hP]; simp only [evc]; rw [e1]
  have c2 : cls _ (pull_isLB hP (pullback.snd f f)) = evc hP a' b := by
    rw [cls_pull hP]; simp only [evc]; rw [e2]
  rw [c1, c2]
  let k : Z ⟶ A := a' * a⁻¹
  have hinv : a⁻¹ ≫ q = (a ≫ q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hk : k ≫ q = 1 := by
    simp only [k]
    rw [MonObj.mul_comp, hinv, ← hq', mul_inv_cancel]
  have h0 : evc hP k b = 0 := by
    have e := congrArg (CechPic.pull (lift (𝟙 Z) b).left) ((triv_ev_iff hP _ _).1 (hker Z k hk))
    rwa [pull_evc, map_zero, lift_fst_assoc, Category.id_comp, lift_snd] at e
  have ha : a' = k * a := by simp only [k, inv_mul_cancel_right]
  rw [ha, (isAdditive_iff hP).1 hadd, h0, zero_add]

end GlobalTheory.DescIsoExists
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearLift

variable {S : Scheme.{0}}

theorem isMonHom_mul {H G : Over S} [GrpObj H] [GrpObj G] [IsCommMonObj G] (f g : H ⟶ G) [IsMonHom f]
    [IsMonHom g] : IsMonHom (f * g) :=
  inferInstanceAs (IsMonHom (lift f g ≫ μ[G]))

theorem isCommMonObj_of_isGrpPullback {S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    [IsCommMonObj G] {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G b φ) : IsCommMonObj G' := by
  have key : ∀ {T : Over S'} (x y : T ⟶ G'), x * y = y * x := by
    intro T x y
    let x₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    let y₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (y.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    have e₁ := h.2 T x y x₀ y₀ rfl rfl
    have e₂ := h.2 T y x y₀ x₀ rfl rfl
    have c : x₀ * y₀ = y₀ * x₀ := mul_comm _ _
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← e₁, ← e₂, c]
    · rw [Over.w, Over.w]
  refine ⟨?_⟩
  rw [mul_eq_mul, comp_mul, key]
  simp

theorem isGrpPullback_tensor {S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨GlobalTheory.AbDual.isPullback_prod m.1 n.1 h₁ h₂, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e₁ : ((x₀ * y₀) ≫ fst A B).left = ((x * y) ≫ fst A' B').left ≫ f := by
    rw [mul_comp, mul_comp]
    refine m.2 T _ _ _ _ ?_ ?_
    · simp only [Over.comp_left, hx, Category.assoc, h₁]
    · simp only [Over.comp_left, hy, Category.assoc, h₁]
  have e₂ : ((x₀ * y₀) ≫ snd A B).left = ((x * y) ≫ snd A' B').left ≫ g := by
    rw [mul_comp, mul_comp]
    refine n.2 T _ _ _ _ ?_ ?_
    · simp only [Over.comp_left, hx, Category.assoc, h₂]
    · simp only [Over.comp_left, hy, Category.assoc, h₂]
  have p : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [← Over.comp_left, e₁]
    simp only [Over.comp_left, Category.assoc, h₁]
  · rw [← Over.comp_left, e₂]
    simp only [Over.comp_left, Category.assoc, h₂]

theorem exists_lift_shear : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π →
    ∀ (g g' : ℕ) (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (i' : A₀.left ⟶ A'.left) (j' : B₀.left ⟶ B'.left),
    IsGrpPullback A₀ A' (spMap π) i' → IsGrpPullback B₀ B' (spMap π) j' → IsAbelianScheme A' → IsAbelianScheme B' →
    SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g' B'.hom →
    ∀ (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left) (h : IsPullback i A₀.hom X.hom (spMap π))
      (k : IsPullback j B₀.hom Y.hom (spMap π)), Smooth X.hom → Smooth Y.hom →
    ∀ (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
    (∀ d ∈ schemeFil (divided₂ hI) A₀ X i h.w, push (divided₂ hI) (spMap π) f₀ d ∈ schemeFil (divided₂ hI) B₀ Y j k.w) →
    ∃ φ : X ⊗ Y ⟶ Y, l ≫ φ.left = ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀).left ≫ j := by
  intro R R₀ _ _ I hI π hπ hker hL g g' A₀ B₀ _ _ A' B' _ _ i' j' hA hB hAab hBab hAg hBg X Y i j h k hX hY
    e e' he he' hie hje l hl₁ hl₂ f₀ _ hf
  haveI : IsCommMonObj B' := hBab.comm
  haveI : IsCommMonObj B₀ := isCommMonObj_of_isGrpPullback hB
  haveI hm : IsMonHom ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀) := isMonHom_mul _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, σ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀) * snd A₀ B₀) := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : A₀ ⊗ B₀ ⟶ A₀ ⊗ B₀, τ = lift (fst A₀ B₀) ((fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀) := ⟨_, rfl⟩
  haveI : IsMonHom σ := by rw [hσ]; infer_instance
  have σ₁ : σ ≫ fst A₀ B₀ = fst A₀ B₀ := by rw [hσ, lift_fst]
  have σ₂ : σ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀) * snd A₀ B₀ := by rw [hσ, lift_snd]
  have τ₁ : τ ≫ fst A₀ B₀ = fst A₀ B₀ := by rw [hτ, lift_fst]
  have τ₂ : τ ≫ snd A₀ B₀ = (fst A₀ B₀ ≫ f₀)⁻¹ * snd A₀ B₀ := by rw [hτ, lift_snd]
  have hστ : σ ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, τ₁, σ₁, Category.id_comp]
    · rw [Category.assoc, τ₂, comp_mul, GrpObj.comp_inv, ← Category.assoc, σ₁, σ₂, inv_mul_cancel_left,
        Category.id_comp]
  have hτσ : τ ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, σ₁, τ₁, Category.id_comp]
    · rw [Category.assoc, σ₂, comp_mul, ← Category.assoc, τ₁, τ₂, mul_inv_cancel_left, Category.id_comp]
  haveI : IsIso σ := ⟨τ, hστ, hτσ⟩
  haveI : IsIso σ.left :=
    ⟨τ.left, by rw [← Over.comp_left, hστ, Over.id_left], by rw [← Over.comp_left, hτσ, Over.id_left]⟩
  obtain ⟨h₀, h₀₁, h₀₂⟩ := GlobalTheory.AbDual.exists_prod_pullback hA hB
  have hAB : IsGrpPullback (A₀ ⊗ B₀) (A' ⊗ B') (spMap π) h₀ := isGrpPullback_tensor hA hB h₀₁ h₀₂
  have hABab := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A' B' hAab hBab
  have hABg := GlobalTheory.AbDual.smooth_prod hAg hBg
  have hl : IsPullback l (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π) := GlobalTheory.AbDual.isPullback_prod h k hl₁ hl₂
  have hσl : IsPullback (σ.left ≫ l) (A₀ ⊗ B₀).hom (X ⊗ Y).hom (spMap π) := by
    have q := (IsPullback.of_horiz_isIso (fst := σ.left) (snd := (A₀ ⊗ B₀).hom) (f := (A₀ ⊗ B₀).hom)
      (g := 𝟙 _) ⟨by rw [Over.w, Category.comp_id]⟩).paste_horiz hl
    rwa [Category.id_comp] at q
  have hsm : Smooth (X ⊗ Y).hom := by
    haveI := hX
    haveI := hY
    rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  have hfil : schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) l hl.w =
      schemeFil (divided₂ hI) (A₀ ⊗ B₀) (X ⊗ Y) (σ.left ≫ l) hσl.w := by
    ext d
    rw [GlobalTheory.T.hodgeFiltration_comp_iso_lift_iff R R₀ I (divided₂ hI) π (A₀ ⊗ B₀) (A₀ ⊗ B₀) σ (X ⊗ Y) l hl.w hσl.w d]
    have P := fun d' ↦ GlobalTheory.T.hodgeFiltration_tensor_lifts_iff_projections R R₀ I (divided₂ hI) π A₀ B₀ X Y i j h.w k.w e e' he he' hie hje l hl₁ hl₂ hl.w d'
    rw [P d, P (push (divided₂ hI) (spMap π) σ d)]
    have c₁ : push (divided₂ hI) (spMap π) (fst A₀ B₀) (push (divided₂ hI) (spMap π) σ d) =
        push (divided₂ hI) (spMap π) (fst A₀ B₀) d := by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₁]
    have c₂ : push (divided₂ hI) (spMap π) (snd A₀ B₀) (push (divided₂ hI) (spMap π) σ d) =
        push (divided₂ hI) (spMap π) f₀ (push (divided₂ hI) (spMap π) (fst A₀ B₀) d) +
          push (divided₂ hI) (spMap π) (snd A₀ B₀) d := by
      rw [← LinearMap.comp_apply, ← push_comp, push_congr _ _ σ₂, push_mul, LinearMap.add_apply, push_comp,
        LinearMap.comp_apply]
    rw [c₁, c₂]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, add_mem (hf _ ha) hb⟩
    · rintro ⟨ha, hb⟩
      refine ⟨ha, ?_⟩
      have := sub_mem hb (hf _ ha)
      rwa [add_sub_cancel_left] at this
  obtain ⟨E, hE⟩ := hL.exists_iso hAB hABab hABg hl hσl hsm hsm hfil
  refine ⟨E.hom ≫ snd X Y, ?_⟩
  rw [Over.comp_left, ← Category.assoc, hE, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left, σ₂]

end GlobalTheory.ShearLift
end
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CochainInv

theorem continuous_multilinear {ι : Type} [Fintype ι] {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G] (f : (ι → V) →ₘₗ[ℝ] G) :
    Continuous f := by
  classical
  let b := Module.finBasis ℝ V
  have h : ∀ x : ι → V, f x = ∑ r : ι → Fin (Module.finrank ℝ V), (∏ i, b.coord (r i) (x i)) • f (fun i => b (r i)) := by
    intro x
    conv_lhs => rw [show x = fun i => ∑ j, b.coord j (x i) • b j from funext fun i => (b.sum_repr (x i)).symm]

    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simpa only [RingHom.id_apply] using f.map_smul_univ (fun i => b.coord (r i) (x i)) (fun i => b (r i))
  rw [show (f : (ι → V) → G) = fun x => ∑ r : ι → Fin (Module.finrank ℝ V), (∏ i, b.coord (r i) (x i)) • f (fun i => b (r i))
    from funext h]
  refine continuous_finsetSum _ fun r _ => (continuous_finsetProd _ fun i _ => ?_).smul continuous_const
  exact ((b.coord (r i)).continuous_of_finiteDimensional).comp (continuous_apply i)

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def hermPart : Lie E a →ₗ[ℝ] Herm E a where
  toFun X := (2⁻¹ : ℝ) • ⟨Matrix.of X + star (Matrix.of X), IsSelfAdjoint.add_star_self _⟩
  map_add' X Y := by
    rw [← smul_add]; congr 1; ext1
    simp only [Submodule.coe_add, ← Matrix.of_add_of, star_add]; abel
  map_smul' c X := by
    rw [RingHom.id_apply, smul_comm]; congr 1; ext1
    simp only [SetLike.val_smul, ← Matrix.smul_of, star_smul, star_trivial, smul_add]

theorem hermPart_toL (X : Herm E a) : hermPart (toL X.1) = X := by
  ext1
  have h : star X.1 = X.1 := X.2.star_eq
  change (2⁻¹ : ℝ) • (Matrix.of (toL X.1) + star (Matrix.of (toL X.1))) = X.1
  rw [show Matrix.of (toL X.1) = X.1 from Matrix.of.apply_symm_apply _, h, ← two_smul ℝ, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

end GlobalTheory.CochainInv

namespace GlobalTheory.CochainInv


open GlobalTheory.GKCoh in
theorem lie_apply_eq_sum : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (S : Set (Module.Dual ℂ M)) (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z → c 0 = 1 → HasDerivAt (fun t => toL (c t).1) (toL Z) 0 → (∀ m, (∀ l ∈ S, l m = 0) → m = 0) → (∀ l ∈ S, ∀ m, HasDerivAt (fun t => l (κ (c t) m)) (l (L (toL Z) m)) 0) → ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → ∀ Y W : Fin q → Herm E a, (∀ i, (W i).1 = Z * (Y i).1 - (Y i).1 * Z) → L (toL Z) (ω Y) = ∑ i, ω (Function.update Y i (W i)) := by
  intro E _ _ a M _ _ _ _ κ L S c Z hZ hc0 hc hS hκ q ω hω Y W hW
  classical
  have hE : ∀ r m, HasDerivAt (fun t => (c t).1 r m) (Z r m) 0 := fun r m => hasDerivAt_pi.1 (hasDerivAt_pi.1 hc r) m
  let u : ℝ → Fin q → Lie E a := fun t i => toL ((c t).1 * (Y i).1 * star (c t).1)
  have hu : HasDerivAt u (fun i => toL (W i).1) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun r => hasDerivAt_pi.2 fun s => ?_
    have key : HasDerivAt (fun t => ((c t).1 * (Y i).1 * star (c t).1) r s)
        ((Z * (Y i).1 * star (c 0).1 + (c 0).1 * (Y i).1 * star Z) r s) 0 := by
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
      refine HasDerivAt.fun_sum fun k _ => ?_
      have h1 : HasDerivAt (fun t => ∑ m, (c t).1 r m * (Y i).1 m k) (∑ m, Z r m * (Y i).1 m k) 0 :=
        HasDerivAt.fun_sum fun m _ => (hE r m).mul_const _
      exact h1.mul (hE s k).star
    have e : Z * (Y i).1 * star (c 0).1 + (c 0).1 * (Y i).1 * star Z = (W i).1 := by
      rw [hW, hc0, hZ]; simp [sub_eq_add_neg]
    rw [e] at key
    exact key
  refine sub_eq_zero.1 (hS _ fun l hl => ?_)
  rw [map_sub, sub_eq_zero]
  let f : (Fin q → Lie E a) →ₘₗ[ℝ] ℂ :=
    (l.restrictScalars ℝ).compMultilinearMap (ω.toMultilinearMap.compLinearMap fun _ => hermPart)
  let F : ContinuousMultilinearMap ℝ (fun _ : Fin q => Lie E a) ℂ := ⟨f, continuous_multilinear f⟩
  have hF : ∀ x, F x = l (ω (fun i => hermPart (x i))) := fun x => rfl
  have h1 := (F.hasFDerivAt (u 0)).comp_hasDerivAt (0 : ℝ) hu
  have h2 : (F ∘ u) = fun t => l (κ (c t) (ω Y)) := by
    funext t
    rw [Function.comp_apply, hF, ← hω (c t) Y]
    congr 2
    funext i
    exact hermPart_toL (adHerm (c t) (Y i))
  rw [h2, ContinuousMultilinearMap.linearDeriv_apply] at h1

  rw [(hκ l hl (ω Y)).unique h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF]
  congr 2
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp [hermPart_toL]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    change hermPart (toL ((c 0).1 * (Y j).1 * star (c 0).1)) = Y j
    simp [hc0, hermPart_toL]

end GlobalTheory.CochainInv

end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.UCls

theorem torusBound : TorusBound := by
  intro E _ _ _ r M G Λ hr hM hE hΛ
  classical
  set c := IsCMField.complexConj E
  obtain ⟨S, hS, hS'⟩ := GlobalTheory.UCls.normOne_classes_le_classNumber E hE
  obtain ⟨S', hS₂, hS₂'⟩ := GlobalTheory.UCls.NormOneMod.normOne_mod E M hM
  let T : Finset (RA (maximalRealSubfield E) E) := (S ×ˢ S').image fun p => p.1 * p.2
  have hT : T.card ≤ classNumber E * M ^ (2 * fdeg E) :=
    Finset.card_image_le.trans ((Finset.card_product S S').le.trans (Nat.mul_le_mul hS hS₂))
  have hTA : ∀ a b : RA (maximalRealSubfield E) E, IsTA c a → IsTA c b → IsTA c (a * b) := by
    intro a b ha hb
    unfold IsTA at *
    rw [map_mul, mul_mul_mul_comm, ha, hb, one_mul]
  have hone : IsTA c (1 : RA (maximalRealSubfield E) E) := by simp [IsTA]
  let Q := Quot fun a b : {t // IsTA c t} => TEquiv c G (Λ : Set (Fin r → E)) M a.1 b.1
  let φ : T → Q := fun x => if h : IsTA c x.1 then Quot.mk _ ⟨x.1, h⟩ else Quot.mk _ ⟨1, hone⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, u, hu, k, hk, hkint, hsTA, rfl⟩ := hS' t ht
    obtain ⟨s', hs', hs'TA, k', hk'TA, hk'1, rfl⟩ := hS₂' k hk hkint
    obtain ⟨g, hg, hdet⟩ := GlobalTheory.UCls.Det.exists_isKM_det_eq E hE r M G Λ hr hM hΛ k' hk'TA hk'1
    have hmem : s * s' ∈ T := Finset.mem_image.2 ⟨(s, s'), Finset.mem_product.2 ⟨hs, hs'⟩, rfl⟩
    refine ⟨⟨s * s', hmem⟩, ?_⟩
    simp only [φ, dif_pos (hTA s s' hsTA hs'TA)]
    refine Quot.sound ⟨u, hu, g, hg, ?_⟩
    rw [hdet]
    ring
  calc torusNo c G (Λ : Set (Fin r → E)) M = ENat.card Q := rfl
    _ ≤ ENat.card T := ENat.card_le_card_of_injective (Function.injective_surjInv hφ)
    _ = T.card := by rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]
    _ ≤ _ := by exact_mod_cast hT

end GlobalTheory.UCls
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContragredientPar

open Finset GlobalTheory.SignedHC

theorem v_strictAnti {R : Ranks} (P : HCParam R) : StrictAnti P.v := by
  have hs : ∀ (a : ℕ) (h : a + 1 < R.k - 1), P.v ⟨a + 1, h⟩ < P.v ⟨a, by omega⟩ :=
    fun a h => (P.u_gt_v ⟨a + 1, h⟩).trans (P.v_gt_u ⟨a, by omega⟩)
  have hA : ∀ (d a : ℕ) (h : a + d + 1 < R.k - 1), P.v ⟨a + d + 1, h⟩ < P.v ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => exact hs
    | succ d ih => intro a h; exact (hs (a + d + 1) h).trans (ih a (by omega))
  rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < c from hac)
  exact hA d a hc

theorem b_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.b := by
  have hs : ∀ (a : ℕ) (h : a + 1 < R.m), P.b ⟨a, by omega⟩ < P.b ⟨a + 1, h⟩ := fun a h => by
    have h1 := P.gap_be ⟨a, by omega⟩
    have h2 := P.gap_eb ⟨a, by omega⟩ h
    have h3 : (0 : ℚ) ≤ R.t := by positivity
    linarith
  have hA : ∀ (d a : ℕ) (h : a + d + 1 < R.m), P.b ⟨a, by omega⟩ < P.b ⟨a + d + 1, h⟩ := by
    intro d
    induction d with
    | zero => exact hs
    | succ d ih => intro a h; exact (ih a (by omega)).trans (hs (a + d + 1) h)
  rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < c from hac)
  exact hA d a hc

theorem neg_v_lt_b {R : Ranks} (P : HCParam R) (i : Fin (R.k - 1)) (j : Fin R.m) : -P.v i < P.b j := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 := P.u_last_gt (by omega) (by omega)
  have h2 := P.v_gt_u ⟨R.k - 2, by omega⟩
  have h3 : P.v ⟨R.k - 2, by omega⟩ ≤ P.v i :=
    (v_strictAnti P).antitone (show i.1 ≤ R.k - 2 by have := i.2; omega)
  have h4 : P.b ⟨0, by omega⟩ ≤ P.b j := (b_strictMono P).monotone (show 0 ≤ j.1 from Nat.zero_le _)
  have h5 : (⟨R.k - 2 + 1, by omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
  simp only [h5] at h2
  linarith

end GlobalTheory.ContragredientPar
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.kernelConstant_exponents_finite : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀), k.YFinite := by
  first | exact @GlobalTheory.ExponentsFinite.yFinite | exact GlobalTheory.ExponentsFinite.yFinite | (intros; apply GlobalTheory.ExponentsFinite.yFinite <;> assumption)
end
