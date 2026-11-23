module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle691
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupGradedCommOfIsFlip
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

open GlobalTheory.Obs.BaseChg in
theorem GlobalTheory.Obs.extCoef_two_equiv : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H2 (OAff s₁) ≃+ GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegTwo R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullbackH2Structure h₁ c c' := by
  intro R₀ R₁ _ _ _ q hq
  have hres : ∀ {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
      (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))),
      Function.Bijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2 := fun {X₀ X₁ s₀ s₁ pr} hp ↦
    GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective R₁ X₁ s₁ _ (preF hp) (preF_cover hp (GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp))
      (preF_dir hp (GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq X₀ X₁ s₀ s₁ pr hp))
  have hfwd : ∀ {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
      (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))), Function.Bijective (fwd hp).pull2 :=
    fun {X₀ X₁ s₀ s₁ pr} hp ↦ ofNat_pull2_bijective _ _ _ (fun U ↦ GlobalTheory.T.baseChangeSectionsComparisonHom_bijective R₀ R₁ X₀ X₁ s₀ s₁ pr hp U.unop)
  refine ⟨fun X₀ X₁ s₀ s₁ pr hp ↦
    (AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2.toAddMonoidHom (hres hp)).trans
      (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).symm, ?_⟩
  intro X₀ X₁ s₀ s₁ pr hp Y₀ Y₁ t₀ t₁ pr' hp' f₀ f₁ h₀ h₁ hf c c' hE
  set d := ((AddEquiv.ofBijective (CoefMap.restrict (OAff s₁) (preF hp)).pull2.toAddMonoidHom (hres hp)).trans
      (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).symm) c with hd0
  set d' := ((AddEquiv.ofBijective (CoefMap.restrict (OAff t₁) (preF hp')).pull2.toAddMonoidHom (hres hp')).trans
      (AddEquiv.ofBijective (fwd hp').pull2.toAddMonoidHom (hfwd hp')).symm) c' with hd0'
  have hd : (fwd hp).pull2 d = (CoefMap.restrict (OAff s₁) (preF hp)).pull2 c :=
    (AddEquiv.ofBijective (fwd hp).pull2.toAddMonoidHom (hfwd hp)).apply_symm_apply _
  have hd' : (fwd hp').pull2 d' = (CoefMap.restrict (OAff t₁) (preF hp')).pull2 c' :=
    (AddEquiv.ofBijective (fwd hp').pull2.toAddMonoidHom (hfwd hp')).apply_symm_apply _
  clear_value d d'
  have A : (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairPull h₁).pull2 c) =
      (kMap hp hp' hf).pull2 ((extMap R₁ (pairPull h₀)).pull2 d) := by
    rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    rw [CoefMap.pullCohomologyTwo_eq_of_natTrans ((pairPull h₁).comp (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)))
      ((CoefMap.restrict (OAff s₁) (preF hp)).comp (zMap hp hp' hf h₁)) { app := fun p ↦ 𝟙 _ }
      (fun p b ↦ by erw [mp_id]; rfl) c]
    rw [CoefMap.pullCohomologyTwo_comp, ← hd, ← CoefMap.pullCohomologyTwo_comp]
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((fwd hp).comp (zMap hp hp' hf h₁))
      ((extMap R₁ (pairPull h₀)).comp (kMap hp hp' hf)) { app := fun p ↦ 𝟙 _ } (fun p b ↦ ?_) d
    erw [mp_id]
    change beta hp' p.unop.1.1 (extHom R₁ (coefHom (pairPull h₀) p) b) =
      GlobalTheory.CechDR.secPull s₁ t₁ (preP hp hp' hf p.unop) (beta hp p.unop.1.2 b)
    revert b
    change ∀ b : R₁ ⊗[R₀] Sec s₀ p.unop.1.2.1, _
    intro b
    induction b using TensorProduct.induction_on with
    | zero =>
      exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
    | tmul r a =>
      change beta hp' p.unop.1.1 (r ⊗ₜ[R₀] (coefHom (pairPull h₀) p a)) = _
      rw [beta_tmul hp p.unop.1.2 r a]
      erw [beta_tmul hp' p.unop.1.1 r]
      rw [map_mul]
      have hr : GlobalTheory.CechDR.secPull s₁ t₁ (preP hp hp' hf p.unop) (algebraMap R₁ _ r) = algebraMap R₁ _ r := by
        have := semiHom_secPull h₁ (preP hp hp' hf p.unop) r 1
        rw [map_one, RingHom.id_apply, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at this
        exact this
      have e1 := congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_comp_appLE pr' f₀ p.unop.1.2.1 p.unop.1.1.1
        (pr' ⁻¹ᵁ p.unop.1.1.1) p.unop.2 le_rfl)
      have e2 := congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_comp_appLE f₁ pr p.unop.1.2.1
        (pr ⁻¹ᵁ p.unop.1.2.1) (pr' ⁻¹ᵁ p.unop.1.1.1) le_rfl (preP hp hp' hf p.unop).2)
      have key : ∀ (g g' : Y₁ ⟶ X₀) (_ : g = g') (e e'),
          (g.appLE p.unop.1.2.1 (pr' ⁻¹ᵁ p.unop.1.1.1) e).hom a = (g'.appLE p.unop.1.2.1 (pr' ⁻¹ᵁ p.unop.1.1.1) e').hom a := by
        rintro g _ rfl _ _; rfl
      rw [hr]
      congr 1
      exact e1.trans ((key _ _ hf.symm _ _).trans e2.symm)
    | add x y hx hy =>
      exact ((congrArg _ (map_add _ x y)).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) hx hy))).trans
        ((congrArg _ (map_add _ x y)).trans (map_add _ _ _)).symm
  have B : (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairRes f₁ t₁).pull2 c') =
      (kMap hp hp' hf).pull2 ((extMap R₁ (pairRes f₀ t₀)).pull2 d') := by
    rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp]
    rw [CoefMap.pullCohomologyTwo_eq_of_natTrans ((pairRes f₁ t₁).comp (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)))
      ((CoefMap.restrict (OAff t₁) (preF hp')).comp (zRes hp hp' hf)) { app := fun p ↦ 𝟙 _ }
      (fun p b ↦ by erw [mp_id]; rfl) c']
    rw [CoefMap.pullCohomologyTwo_comp, ← hd', ← CoefMap.pullCohomologyTwo_comp]
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((fwd hp').comp (zRes hp hp' hf))
      ((extMap R₁ (pairRes f₀ t₀)).comp (kMap hp hp' hf)) { app := fun p ↦ 𝟙 _ } (fun p b ↦ ?_) d'
    erw [mp_id]
    change beta hp' p.unop.1.1 (extHom R₁ (coefHom (pairRes f₀ t₀) p) b) = beta hp' p.unop.1.1 b
    congr 1
    revert b
    change ∀ b : R₁ ⊗[R₀] Sec t₀ p.unop.1.1.1, _
    intro b
    induction b using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul r a => rfl
    | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy)
  have hinj : Function.Injective (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 := by
    intro x y hxy
    obtain ⟨x0, rfl⟩ := (GlobalTheory.AbCoh.pairRes_pull2_bijective f₁ t₁).2 x
    obtain ⟨y0, rfl⟩ := (GlobalTheory.AbCoh.pairRes_pull2_bijective f₁ t₁).2 y
    have key : ∀ z, (CoefMap.restrict (OPair f₁ t₁) (preFP hp hp' hf)).pull2 ((pairRes f₁ t₁).pull2 z) =
        (CoefMap.restrict (OAff t₁) (preFP hp hp' hf ⋙ pairFst f₁)).pull2 z := fun z ↦ by
      rw [← CoefMap.pullCohomologyTwo_comp]
      exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun p ↦ 𝟙 _ } (fun p b ↦ mp_id _ _ b) z
    rw [key, key] at hxy
    have hW' := GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation R₀ R₁ q hq Y₀ Y₁ t₀ t₁ pr' hp'
    rw [(GlobalTheory.T.restrict_structureSheaf_affineBasis_pull2_bijective R₁ Y₁ t₁ _ (preFP hp hp' hf ⋙ pairFst f₁) (preFP_cover hp hp' hf hW')
      (preFP_directed hp hp' hf hW')).1 hxy]
  apply hinj
  rw [A, B]
  exact congrArg _ hE
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.PairExt

variable {X X' Y : Scheme.{0}}

theorem pair_point (φ : X' ⟶ X) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Pair φ)ᵒᵖ, x ∈ ((pairFst φ).obj t).unop.1 ∧ ((pairFst φ).obj t).unop.1 ≤ U := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := (⊤ : X.Opens)) trivial
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).2⟩, hxW, fun y hy ↦ (hWU hy).1⟩

theorem pair_point_two (φ : X' ⟶ X) (t₁ t₂ : (Pair φ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((pairFst φ).obj t₁).unop.1) (h₂ : x ∈ ((pairFst φ).obj t₂).unop.1) :
    ∃ t₃ : (Pair φ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((pairFst φ).obj t₃).unop.1 ∧
      ((pairFst φ).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨t₁.unop.2 h₁', t₂.unop.2 h₂'⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Pair φ := ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).1.2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).2⟩

theorem triple_point (φ : X' ⟶ X) (ψ : X ⟶ Y) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Triple φ ψ)ᵒᵖ, x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ≤ U := by
  obtain ⟨Z, hZ, hxZ, -⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x)) (U := (⊤ : Y.Opens)) trivial
  obtain ⟨V, hV, hxV, hVZ⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := ψ ⁻¹ᵁ Z) hxZ
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).2, fun y hy ↦ hVZ hy⟩, hxW,
    fun y hy ↦ (hWU hy).1⟩

theorem triple_point_two (φ : X' ⟶ X) (ψ : X ⟶ Y) (t₁ t₂ : (Triple φ ψ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₁).unop.1)
    (h₂ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₂).unop.1) :
    ∃ t₃ : (Triple φ ψ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
      x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  have hy₁ : φ.base x ∈ t₁.unop.1.2.1.1 := t₁.unop.2.1 h₁'
  have hy₂ : φ.base x ∈ t₂.unop.1.2.1.1 := t₂.unop.2.1 h₂'
  obtain ⟨Z, hZ, hxZ, hZZ⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x))
    (U := t₁.unop.1.2.2.1 ⊓ t₂.unop.1.2.2.1) ⟨t₁.unop.2.2 hy₁, t₂.unop.2.2 hy₂⟩
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1.1 ⊓ t₂.unop.1.2.1.1 ⊓ ψ ⁻¹ᵁ Z) ⟨⟨hy₁, hy₂⟩, hxZ⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Triple φ ψ := ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).1.2, fun y hy ↦ (hVV hy).2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1.1, fun y hy ↦ (hZZ hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).1.2, fun y hy ↦ (hZZ hy).2⟩

theorem extHom_of_id {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] {B : Type} [CommRing B]
    [Algebra R₀ B] (f : B →ₐ[R₀] B) (hf : ∀ b, f b = b) (y : R₁ ⊗[R₀] B) : extHom R₁ f y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cechTripleRestrict_comp_pairRestrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (s' : X' ⟶ Sp R₀)
    (φ : X' ⟶ X) (ψ : X ⟶ Y) (c : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 ((extMap R₁ (pairRes φ s')).pull1 c) =
      (extMap R₁ (CoefMap.restrict (OAff s') (cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)))).pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' a
  exact extHom_of_id R₁ (coefHom (cechTripleRestrictFirst φ ψ s') T') (fun _ ↦ rfl) _

theorem pairRes_ext_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R₀) (φ : X' ⟶ X), (Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2) ∧ ∀ (Y : Scheme.{0}) (ψ : X ⟶ Y), Function.Injective (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 := by
  intro R₀ R₁ _ _ _ X X' s' φ
  have hp : Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2 :=
    GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X' s' _ (pairFst φ) (pair_point φ) (pair_point_two φ)
  refine ⟨hp, fun Y ψ x y e ↦ ?_⟩
  obtain ⟨x0, rfl⟩ := hp.1.2 x
  obtain ⟨y0, rfl⟩ := hp.1.2 y
  rw [cechTripleRestrict_comp_pairRestrict, cechTripleRestrict_comp_pairRestrict] at e
  rw [(GlobalTheory.T.cohomology_restrict_basis_extended_bijective R₀ R₁ X' s' _ _ (triple_point φ ψ) (triple_point_two φ ψ)).1.1 e]

end GlobalTheory.Obs.PairExt
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SuppRes

open ClsSpec

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
private theorem shv_hom_ext_of_sec_map_eq {S : Type} [CommRing S] {F G : _root_.GlobalTheory.EtC.Shv S}
    (φ ψ : F ⟶ G)
    (h : ∀ U (a : _root_.GlobalTheory.EtC.Sec F U),
      _root_.GlobalTheory.EtC.Sec.map φ a = _root_.GlobalTheory.EtC.Sec.map ψ a) : φ = ψ := by
  ext U a
  exact h U.unop a

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
private theorem sec_map_zero_apply {S : Type} [CommRing S] {F G : _root_.GlobalTheory.EtC.Shv S}
    {U : Scheme} (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.map (0 : F ⟶ G) a = 0 := by
  simp [_root_.GlobalTheory.EtC.Sec.map]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
private theorem etLoc_of_forall {U : Scheme} {P : (V : Scheme) → (V ⟶ U) → Prop}
    (h : ∀ V g, P V g) : _root_.GlobalTheory.EtC.Loc U P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => h V g⟩


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.SuppRes.supp_res : ∀ (q : ℕ) [NeZero q] (i : ℤ)
    (D : _root_.GlobalTheory.EtC.Cx (ZMod q))
    (ι : D ⟶ _root_.GlobalTheory.EtC.res _ (_root_.GlobalTheory.EtC.tw q i)),
    (∀ n U, Function.Injective (_root_.GlobalTheory.EtC.Sec.map (ι.f n) (U := U))) →
    (∀ n U (a : _root_.GlobalTheory.EtC.Sec ((_root_.GlobalTheory.EtC.res _ (_root_.GlobalTheory.EtC.tw q i)).X n) U),
      (∃ b, _root_.GlobalTheory.EtC.Sec.map (ι.f n) b = a) ↔
      _root_.GlobalTheory.EtC.Loc U fun V g =>
        IsUnit (q : Γ(V, ⊤)) ∨ _root_.GlobalTheory.EtC.Sec.res g a = 0) →
    ∃ e : ∀ U : Scheme.{0}, _root_.GlobalTheory.EtC.Prim q Γ(U, ⊤) → _root_.GlobalTheory.EtC.Sec (D.X 0) U,
      _root_.GlobalTheory.EtC.IsTwRes q i D e ∧
      ∀ U ζ, _root_.GlobalTheory.EtC.Sec.map (ι.f 0) (e U ζ) = _root_.GlobalTheory.EtC.resGen i ζ := by
  intro q _ i D ι hinj himg
  haveI hmono : ∀ n, Mono (ι.f n) := fun n =>
    (_root_.GlobalTheory.EtC.mono_epi_sections (ZMod q) (ι.f n)).1.2 (fun U => hinj n U)
  obtain ⟨-, -, hIge, -, hterm, hAmono, hAd, -⟩ :=
    _root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (_root_.GlobalTheory.EtC.tw q i)
  haveI := hIge
  haveI := hAmono
  have hA : _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) ≫
      cokernel.π (ι.f 0) = 0 := by
    apply shv_hom_ext_of_sec_map_eq
    intro U y
    rw [sec_map_zero_apply, ← _root_.GlobalTheory.EtC.ClsSpec.map_comp]
    obtain ⟨b, hb⟩ := (himg 0 U (_root_.GlobalTheory.EtC.Sec.map
      (_root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)) y)).2 (by
        refine _root_.GlobalTheory.EtC.ClsSpec.loc_mono
          ((_root_.GlobalTheory.EtC.twist_sections q i).1 U y) ?_
        rintro V g (h | ⟨ζ, c, -⟩)
        · right
          rw [_root_.GlobalTheory.EtC.ClsSpec.res_map, h,
            _root_.GlobalTheory.EtC.ClsSpec.smap_zero]
        · exact Or.inl ζ.2.1)
    rw [← hb, _root_.GlobalTheory.EtC.ClsSpec.map_comp, cokernel.condition, sec_map_zero_apply]
  have hA' : Abelian.monoLift (ι.f 0) _ hA ≫ ι.f 0 =
      _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) :=
    Abelian.monoLift_comp _ _ _
  have hd : Abelian.monoLift (ι.f 0) _ hA ≫ D.d 0 1 = 0 := by
    rw [← cancel_mono (ι.f 1), zero_comp, Category.assoc, ← ι.comm, ← Category.assoc, hA', hAd]
  let ε : _root_.GlobalTheory.EtC.sgl (_root_.GlobalTheory.EtC.tw q i) ⟶ D :=
    HomologicalComplex.mkHomFromSingle (Abelian.monoLift (ι.f 0) _ hA) (by
        intro k hk
        have hk1 : k = 1 := by simpa using hk.symm
        subst hk1
        exact hd)
  have hε0 : ε.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (_root_.GlobalTheory.EtC.tw q i)).hom ≫ Abelian.monoLift (ι.f 0) _ hA :=
    HomologicalComplex.mkHomFromSingle_f _ _
  have haug : (_root_.GlobalTheory.EtC.resAug (_root_.GlobalTheory.EtC.tw q i)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)).hom ≫
        _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) := by
    rw [← hterm]
    unfold _root_.GlobalTheory.EtC.sglι
    erw [Iso.hom_inv_id_assoc]
  have hει : ε.f 0 ≫ ι.f 0 = (_root_.GlobalTheory.EtC.resAug (_root_.GlobalTheory.EtC.tw q i)).f 0 := by
    rw [haug]
    erw [hε0, Category.assoc, hA']
    all_goals rfl
  have hterm' : _root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i) ≫ ε.f 0 ≫ ι.f 0 =
      _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i) := by
    rw [hει, hterm]
  refine ⟨fun U ζ => _root_.GlobalTheory.EtC.Sec.map (ε.f 0) (_root_.GlobalTheory.EtC.Sec.map
    (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) (_root_.GlobalTheory.EtC.twGen i ζ)), ?_, ?_⟩
  · unfold _root_.GlobalTheory.EtC.IsTwRes
    refine ⟨?_, ε, ?_, fun U ζ => rfl⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      exact @IsZero.of_mono _ _ _ _ _ (ι.f n) (hmono n) (CochainComplex.isZero_of_isStrictlyGE _ 0 n hn)
    · refine ⟨fun n => ?_⟩
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · rw [quasiIsoAt_iff_exactAt ε n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn.ne)]
        exact ShortComplex.exact_of_isZero_X₂ _
          (@IsZero.of_mono _ _ _ _ _ (ι.f n) (hmono n) (CochainComplex.isZero_of_isStrictlyGE _ 0 n hn))
      · rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp),
          ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_]
        · constructor
          · rw [_root_.GlobalTheory.EtC.exactIff]
            intro U b hb
            have hcyc : _root_.GlobalTheory.EtC.Sec.map
                ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d 0 1)
                (_root_.GlobalTheory.EtC.Sec.map (ι.f 0) b) = 0 := by
              erw [_root_.GlobalTheory.EtC.ClsSpec.map_comp, ι.comm,
                ← _root_.GlobalTheory.EtC.ClsSpec.map_comp, hb]
              exact _root_.GlobalTheory.EtC.ClsSpec.smap_zero _
            obtain ⟨y, hy⟩ := ((_root_.GlobalTheory.EtC.resSec (ZMod q)
              (_root_.GlobalTheory.EtC.tw q i) U).1 _).1 hcyc
            have hb' : _root_.GlobalTheory.EtC.Sec.map (ε.f 0) (_root_.GlobalTheory.EtC.Sec.map
                (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) y) = b := by
              apply hinj 0 U
              simp only [_root_.GlobalTheory.EtC.ClsSpec.map_comp, Category.assoc, hterm', hy]
            exact etLoc_of_forall fun V g =>
              ⟨_root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.map
                (_root_.GlobalTheory.EtC.sglι (_root_.GlobalTheory.EtC.tw q i)) y),
                (_root_.GlobalTheory.EtC.ClsSpec.res_map (ε.f 0) g _).symm.trans
                  (congrArg (_root_.GlobalTheory.EtC.Sec.res g) hb')⟩
          · have hcomp : Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (_root_.GlobalTheory.EtC.tw q i)).hom ≫
                _root_.GlobalTheory.EtC.resι (ZMod q) (_root_.GlobalTheory.EtC.tw q i)) :=
              @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _ hAmono
            rw [← haug, ← hει] at hcomp
            exact @mono_of_mono _ _ _ _ _ (ε.f 0) (ι.f 0) hcomp
        · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)
            (-1) (by norm_num)).eq_of_src _ _
        · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (_root_.GlobalTheory.EtC.tw q i)
            1 (by norm_num)).eq_of_tgt _ _
        · exact (@IsZero.of_mono _ _ _ _ _ (ι.f (-1)) (hmono (-1))
            (CochainComplex.isZero_of_isStrictlyGE _ 0 (-1) (by simp))).eq_of_src _ _
      · rw [quasiIsoAt_iff_exactAt ε n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn.ne'),
          D.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp),
          _root_.GlobalTheory.EtC.exactIff]
        intro U b hb
        have hcyc : _root_.GlobalTheory.EtC.Sec.map
            ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d n (n + 1))
            (_root_.GlobalTheory.EtC.Sec.map (ι.f n) b) = 0 := by
          erw [_root_.GlobalTheory.EtC.ClsSpec.map_comp, ι.comm,
            ← _root_.GlobalTheory.EtC.ClsSpec.map_comp, hb]
          exact _root_.GlobalTheory.EtC.ClsSpec.smap_zero _
        have hex := (_root_.GlobalTheory.EtC.resSec (ZMod q)
          (_root_.GlobalTheory.EtC.tw q i) U).2.2.1 (n - 1) n (n + 1) hn (by ring) _ rfl hcyc
        have hsupp := (himg n U (_root_.GlobalTheory.EtC.Sec.map (ι.f n) b)).1 ⟨b, rfl⟩
        refine _root_.GlobalTheory.EtC.ClsSpec.loc_mono (_root_.GlobalTheory.EtC.ClsSpec.loc_and hex hsupp) ?_
        rintro V g ⟨⟨y, hy⟩, hq | hz⟩
        · obtain ⟨y', rfl⟩ := (himg (n - 1) V y).2
            (etLoc_of_forall fun W h => Or.inl (_root_.GlobalTheory.EtC.ClsSpec.unit_res h hq))
          refine ⟨y', hinj n V ?_⟩
          exact (_root_.GlobalTheory.EtC.ClsSpec.map_comp (D.d (n - 1) n) (ι.f n) y').trans
            ((congrArg (fun φ => _root_.GlobalTheory.EtC.Sec.map φ y') (ι.comm (n - 1) n).symm).trans
              ((_root_.GlobalTheory.EtC.ClsSpec.map_comp (ι.f (n - 1))
                ((_root_.GlobalTheory.EtC.res (ZMod q) (_root_.GlobalTheory.EtC.tw q i)).d (n - 1) n)
                  y').symm.trans
                (hy.trans (_root_.GlobalTheory.EtC.ClsSpec.res_map (ι.f n) g b))))
        · refine ⟨0, ?_⟩
          erw [_root_.GlobalTheory.EtC.ClsSpec.smap_zero]
          apply hinj n V
          exact (_root_.GlobalTheory.EtC.ClsSpec.smap_zero _).trans
            (hz.symm.trans (_root_.GlobalTheory.EtC.ClsSpec.res_map _ g b))
  · intro U ζ
    simp only [_root_.GlobalTheory.EtC.ClsSpec.map_comp, Category.assoc, hterm']
    rfl

end GlobalTheory.EtC.SuppRes

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy : ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧ (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧ ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u') := by
  first | (exact @GlobalTheory.EtC.TwResExt.twRes_ext) | (exact GlobalTheory.EtC.TwResExt.twRes_ext) | (intros; apply GlobalTheory.EtC.TwResExt.twRes_ext  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), (∀ s, Injective (I.X s)) → (∀ s, Injective (J.X s)) → ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ {n m k : ℤ} (hk : n + m = k) a b, cpull ((chains R).map f) I n a = 0 → cpull ((chains R).map g) J m b = 0 → μ.cup E hk a b = 0 := by
  first | (exact @GlobalTheory.EtC.cup_supp) | (exact GlobalTheory.EtC.cup_supp) | (intros; apply GlobalTheory.EtC.cup_supp  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective : ∀ (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q), (∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, φ.app (op V) x = Q.map g.op y) → QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from (Arrow.mk φ).augmentedCechNerve.hom)) := by
  first | (exact @GlobalTheory.EtC.quasiIso_chains_cech_of_locSurj) | (exact GlobalTheory.EtC.quasiIso_chains_cech_of_locSurj) | (intros; apply GlobalTheory.EtC.quasiIso_chains_cech_of_locSurj  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tateTwist_mul_degreeZero_locally_injective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → (∀ (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ), c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c) → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  first | (exact @GlobalTheory.EtC.TwMulInj.tw_mul_loc_injective) | (exact GlobalTheory.EtC.TwMulInj.tw_mul_loc_injective) | (intros; apply GlobalTheory.EtC.TwMulInj.tw_mul_loc_injective  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tateTwist_mul_degreeZero_locally_surjective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (y : Sec (K.X 0) U), Loc U fun V g => ∃ z : Sec (tw q k) V, Sec.map φ z = Sec.res g y := by
  first | (exact @GlobalTheory.EtC.tw_mul_locSurj) | (exact GlobalTheory.EtC.tw_mul_locSurj) | (intros; apply GlobalTheory.EtC.tw_mul_locSurj  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cup_graded_comm_of_isFlip : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ} (h : n + m = k) (h' : m + n = k) a b, μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a := by
  first | exact @GlobalTheory.EtC.Pair.cup_flip | exact GlobalTheory.EtC.Pair.cup_flip | (intros; apply GlobalTheory.EtC.Pair.cup_flip <;> assumption)
end
