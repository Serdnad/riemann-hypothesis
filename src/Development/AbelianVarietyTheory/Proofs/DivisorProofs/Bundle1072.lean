module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationOperatorFormulaGroupAndProjectors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem germ_app_congr {Y X : Scheme.{0}} {f g : Y ⟶ X} (e : f = g) (W : X.Opens) (y : Y) (hf : f y ∈ W)
    (hg : g y ∈ W) (s : Γ(X, W)) :
    Y.presheaf.germ (f ⁻¹ᵁ W) y hf ((f.app W).hom s) = Y.presheaf.germ (g ⁻¹ᵁ W) y hg ((g.app W).hom s) := by
  subst e; rfl

theorem affine_descent_units : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    ∀ W : X.Opens, IsAffineOpen W → ∀ (u' : Γ(X', p ⁻¹ᵁ W)ˣ) (v : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) u' = gm p' z (i ⁻¹ᵁ W) v) →
      ∃ u : Γ(X, W)ˣ, pullU p W u = u' := by
  intro X X' Z Z' p i i' p' h hp hi hc W hW u' v huv
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  have claim : ∀ (s' : Γ(X', p ⁻¹ᵁ W)) (t : Γ(Z, i ⁻¹ᵁ W)),
      (∀ z : Z', ∀ hz : p (i' z) ∈ W,
        Z'.presheaf.germ (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) z hz ((i'.app (p ⁻¹ᵁ W)).hom s') =
          Z'.presheaf.germ (p' ⁻¹ᵁ (i ⁻¹ᵁ W)) z (show i (p' z) ∈ W from hw z ▸ hz) ((p'.app (i ⁻¹ᵁ W)).hom t)) →
      ∃ s : Γ(X, W), (p.app W).hom s = s' := by
    intro s' t hst
    obtain ⟨s₀, rfl⟩ := Scheme.Hom.app_surjective i W hW t
    have hd : (i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀) = 0 := by
      apply TopCat.Presheaf.section_ext Z'.sheaf
      intro z hz
      show (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom ((i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀)) =
        (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom 0
      rw [map_sub, map_sub, map_zero, sub_eq_zero, hst z hz]
      have e1 := germ_app_congr h.w W z hz (show i (p' z) ∈ W from hw z ▸ hz) s₀
      exact e1.symm
    have hmem := GlobalTheory.T.closedImmersion_baseChange_ker_mem_map_affine X X' Z Z' p i i' p' h hp hi W hW _ hd
    have key : ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = s' - (p.app W).hom s₀ := by
      refine Submodule.span_induction (p := fun x _ => ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = x)
        ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · exact ⟨0, map_zero _, map_zero _⟩
      · rintro _ _ _ _ ⟨y₁, h₁, e₁⟩ ⟨y₂, h₂, e₂⟩
        exact ⟨y₁ + y₂, by rw [map_add (f := _), h₁, h₂, add_zero], by rw [map_add (f := _), e₁, e₂]⟩
      · rintro r _ _ ⟨y, hy, rfl⟩
        obtain ⟨y', hy', e'⟩ := (hc W hW).2 y hy r
        exact ⟨y', hy', by rw [smul_eq_mul, mul_comm]; exact e'⟩
    obtain ⟨y, -, hy⟩ := key
    exact ⟨s₀ + y, by rw [map_add (f := _), hy, add_sub_cancel]⟩
  have germs : ∀ (a : Γ(X', p ⁻¹ᵁ W)ˣ) (b : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) a = gm p' z (i ⁻¹ᵁ W) b) →
      ∃ s : Γ(X, W), (p.app W).hom s = a.val := by
    intro a b hab
    refine claim a.val b.val fun z hz => ?_
    have := congrArg Units.val (hab z hz)
    rwa [gm_val i' z _ hz, gm_val p' z _ (show i (p' z) ∈ W from hw z ▸ hz)] at this
  obtain ⟨x, hx⟩ := germs u' v huv
  obtain ⟨y, hy⟩ := germs u'⁻¹ v⁻¹ fun z hz => by rw [map_inv, map_inv, huv z hz]
  have hxy : x * y = 1 := (hc W hW).1 (by
    show (p.app W).hom (x * y) = (p.app W).hom 1
    rw [map_mul, map_one, hx, hy, Units.mul_inv])
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, Units.ext hx⟩

theorem pullU_injective {X X' : Scheme.{0}} (p : X' ⟶ X)
    (hp : ∀ W : X.Opens, IsAffineOpen W → Function.Injective (p.app W)) (W : X.Opens) :
    Function.Injective (pullU p W) := by
  intro a b hab
  apply unit_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  have hle : V ≤ W := hVW
  have e : res hle a = res hle b := by
    apply Units.ext
    apply hp V hV
    have := congrArg Units.val (show pullU p V (res hle a) = pullU p V (res hle b) by
      rw [pullU_res₂, pullU_res₂, hab])
    exact this
  rw [← gm_res (𝟙 X) x hle hxV a, ← gm_res (𝟙 X) x hle hxV b, e]

theorem unitsPatch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    GlobalTheory.Pinch.UnitsPatch p i i' p' := by
  intro X X' Z Z' p i i' p' h hp hi hc W
  have hinj : ∀ V : X.Opens, Function.Injective (pullU p V) :=
    pullU_injective p (fun V hV => (hc V hV).1)
  refine ⟨hinj W, fun u' v huv => ?_⟩
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  have hsub : ∀ j : J, p ⁻¹ᵁ j.1 ≤ p ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have hsubZ : ∀ j : J, i ⁻¹ᵁ j.1 ≤ i ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have loc : ∀ j : J, ∃ a : Γ(X, j.1)ˣ, pullU p j.1 a = res (hsub j) u' := by
    intro j
    refine affine_descent_units X X' Z Z' p i i' p' h hp hi hc j.1 j.2.1 _ (res (hsubZ j) v) ?_
    intro z hz
    rw [gm_res i' z (hsub j) hz, gm_res p' z (hsubZ j) (show i (p' z) ∈ j.1 from hw z ▸ hz)]
    exact huv z (j.2.2 hz)
  choose a ha using loc

  have hD : ∀ j : J, ∀ y : X', ∀ hy : p y ∈ j.1, gm p y j.1 (a j) = gm (𝟙 X') y (p ⁻¹ᵁ W) u' := by
    intro j y hy
    rw [← gm_id_pull p y j.1 hy, ha j, gm_res (𝟙 X') y (hsub j) hy]
  obtain ⟨s, hs⟩ := glue_unit W (fun j : J => j.1) (fun j => j.2.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVW⟩, hxV⟩) a (by
      intro j k x hx
      have hle1 : j.1 ⊓ k.1 ≤ j.1 := inf_le_left
      have hle2 : j.1 ⊓ k.1 ≤ k.1 := inf_le_right
      have e : res hle1 (a j) = res hle2 (a k) := by
        apply hinj
        apply unit_ext
        intro y hy
        rw [gm_id_pull p y _ hy, gm_id_pull p y _ hy, gm_res p y hle1 hy, gm_res p y hle2 hy,
          hD j y (hle1 hy), hD k y (hle2 hy)]
      rw [← gm_res (𝟙 X) x hle1 hx, ← gm_res (𝟙 X) x hle2 hx, e])
  refine ⟨s, unit_ext fun y hy => ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show p y ∈ W from hy) W.2
  let j : J := ⟨V, hV, hVW⟩
  rw [gm_id_pull p y W hy, ← gm_res p y j.2.2 hxV, hs j]
  exact hD j y hxV

end GlobalTheory.Pinch
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem pullTop_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    pullTop (f ≫ g) u = pullTop f (pullTop g u) := by
  ext
  simp only [pullTop, Units.coe_map, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rfl

section Tri

variable {S : Scheme.{0}} (A N T : Over S) [GrpObj A] [GrpObj N] (i : N ⟶ A)

def triM₁₂ : A ⊗ (N ⊗ (N ⊗ T)) ⟶ A ⊗ (N ⊗ T) :=
  lift (fst A _) (lift (snd A _ ≫ fst N _) (snd A _ ≫ snd N _ ≫ snd N T))

def triM₂₃ : A ⊗ (N ⊗ (N ⊗ T)) ⟶ A ⊗ (N ⊗ T) :=
  lift (fst A _ * (snd A _ ≫ fst N _ ≫ i)) (snd A _ ≫ snd N (N ⊗ T))

def triM₁₃ : A ⊗ (N ⊗ (N ⊗ T)) ⟶ A ⊗ (N ⊗ T) :=
  lift (fst A _) (lift (snd A _ ≫ fst N _ * (snd A _ ≫ snd N _ ≫ fst N T)) (snd A _ ≫ snd N _ ≫ snd N T))

theorem triM₁₂_actMap_eq : triM₁₂ A N T ≫ actMap i T = triM₂₃ A N T i ≫ prMap A N T := by
  apply hom_ext <;> simp [triM₁₂, triM₂₃, actMap, prMap, comp_mul]

theorem tri_isPullback_over : IsPullback (triM₁₂ A N T) (triM₂₃ A N T i) (actMap i T) (prMap A N T) := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (triM₁₂_actMap_eq A N T i))
    (PullbackCone.IsLimit.mk (triM₁₂_actMap_eq A N T i)
      (fun s => lift (s.fst ≫ fst A _) (lift (s.fst ≫ snd A _ ≫ fst N T)
        (lift (s.snd ≫ snd A _ ≫ fst N T) (s.fst ≫ snd A _ ≫ snd N T)))) ?_ ?_ ?_)
  · intro s
    apply hom_ext
    · simp [triM₁₂]
    · apply hom_ext <;> simp [triM₁₂]
  · intro s
    have h := s.condition
    have h₁ := congrArg (· ≫ fst A T) h
    have h₂ := congrArg (· ≫ snd A T) h
    simp only [Category.assoc, actMap, prMap, lift_fst, lift_snd, comp_mul] at h₁ h₂
    apply hom_ext
    · simp [triM₂₃, comp_mul, ← h₁]
    · apply hom_ext
      · simp [triM₂₃]
      · simp [triM₂₃, h₂]
  · intro s m h₁ h₂
    have e₁ := congrArg (· ≫ fst A _) h₁
    have e₂ := congrArg (· ≫ snd A _ ≫ fst N T) h₁
    have e₃ := congrArg (· ≫ snd A _ ≫ snd N T) h₁
    have e₄ := congrArg (· ≫ snd A _ ≫ fst N T) h₂
    simp only [triM₁₂, triM₂₃, Category.assoc, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] at e₁ e₂ e₃ e₄
    apply hom_ext
    · simpa using e₁
    · apply hom_ext
      · simpa using e₂
      · apply hom_ext
        · simpa using e₄
        · simpa using e₃

theorem triM₁₃_prMap : triM₁₃ A N T ≫ prMap A N T = triM₁₂ A N T ≫ prMap A N T := by
  apply hom_ext <;> simp [triM₁₃, triM₁₂, prMap]

theorem triM₁₃_actMap [IsMonHom i] : triM₁₃ A N T ≫ actMap i T = triM₂₃ A N T i ≫ actMap i T := by
  apply hom_ext
  · simp only [triM₁₃, triM₂₃, actMap, comp_lift, lift_fst, lift_fst_assoc, lift_snd_assoc, comp_mul, mul_comp,
      Category.assoc]
    exact (mul_assoc _ _ _).symm
  · simp [triM₁₃, triM₂₃, actMap]

theorem triM₁₃_snd : triM₁₃ A N T ≫ snd A (N ⊗ T) =
    snd A (N ⊗ (N ⊗ T)) ≫ lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T) := by
  apply hom_ext <;> simp [triM₁₃, comp_mul]

theorem triM₁₂_snd : triM₁₂ A N T ≫ snd A (N ⊗ T) =
    snd A (N ⊗ (N ⊗ T)) ≫ lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T) := by
  apply hom_ext <;> simp [triM₁₂]

theorem triM₂₃_snd : triM₂₃ A N T i ≫ snd A (N ⊗ T) = snd A (N ⊗ (N ⊗ T)) ≫ snd N (N ⊗ T) := by
  simp [triM₂₃]

end Tri

theorem triOverlap : ∀ (S : Scheme.{0}) (A N T : Over S) [GrpObj A] [GrpObj N] (i : N ⟶ A) (χ : Γ((N ⊗ T).left, ⊤)ˣ),
    IsMonHom i → IsCharacter χ → ∃ (W : Scheme.{0}) (m₁₂ m₂₃ m₁₃ : W ⟶ (A ⊗ (N ⊗ T)).left),
      IsPullback m₁₂ m₂₃ (actMap i T).left (prMap A N T).left ∧
      m₁₃ ≫ (prMap A N T).left = m₁₂ ≫ (prMap A N T).left ∧
      m₁₃ ≫ (actMap i T).left = m₂₃ ≫ (actMap i T).left ∧
      pullTop m₁₃ (pullTop (snd A (N ⊗ T)).left χ) =
        pullTop m₁₂ (pullTop (snd A (N ⊗ T)).left χ) * pullTop m₂₃ (pullTop (snd A (N ⊗ T)).left χ) := by
  intro S A N T _ _ i χ hi hχ
  haveI := hi
  refine ⟨(A ⊗ (N ⊗ (N ⊗ T))).left, (triM₁₂ A N T).left, (triM₂₃ A N T i).left, (triM₁₃ A N T).left,
    (tri_isPullback_over A N T i).map (Over.forget S), ?_, ?_, ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, triM₁₃_prMap]
  · rw [← Over.comp_left, ← Over.comp_left, triM₁₃_actMap]
  · rw [← pullTop_comp_apply, ← pullTop_comp_apply, ← pullTop_comp_apply, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
      triM₁₃_snd, triM₁₂_snd, triM₂₃_snd, Over.comp_left, Over.comp_left, Over.comp_left, pullTop_comp_apply, pullTop_comp_apply,
      pullTop_comp_apply]
    unfold IsCharacter at hχ
    rw [hχ, map_mul]

end GlobalTheory.CharKer
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem factor_ker_iff {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V]
    (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T) (Y : Over (Sp V)) (x : Y ⟶ bc A φ) :
    (∃ y : Y ⟶ ker A φ h, y ≫ kerι A φ h = x) ↔
      ∃ z : up φ Y ⟶ H, z ≫ h = lift (upa φ x) (upt φ Y) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y.left ≫ pullback.snd (h ≫ snd A T).left φ = Y.hom := Over.w y
    have hT : (h ≫ snd A T).left ≫ T.hom = H.hom := Over.w _
    have hc : (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ (h ≫ snd A T).left = Y.hom ≫ φ := by
      rw [← hy]
      exact (Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    refine ⟨Over.homMk (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ?_, ?_⟩
    · show (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ H.hom = Y.hom ≫ φ ≫ T.hom
      rw [← hT, ← Category.assoc, hc, Category.assoc]
    · apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc]
        apply Over.OverMorphism.ext
        have e : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
            = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
        exact (Category.assoc _ _ _).trans
          ((congrArg (y.left ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
      · rw [lift_snd, Category.assoc]
        apply Over.OverMorphism.ext
        exact hc
  · rintro ⟨z, hz⟩
    have h1 : z ≫ h ≫ fst A T = upa φ x := by rw [← Category.assoc, hz, lift_fst]
    have h2 : z ≫ h ≫ snd A T = upt φ Y := by rw [← Category.assoc, hz, lift_snd]
    have h1' : z.left ≫ (h ≫ fst A T).left = x.left ≫ pullback.fst A.hom (φ ≫ T.hom) :=
      congrArg (·.left) h1
    have h2' : z.left ≫ (h ≫ snd A T).left = Y.hom ≫ φ := congrArg (·.left) h2
    let l : Y.left ⟶ pullback (h ≫ snd A T).left φ := pullback.lift z.left Y.hom h2'
    have l1 : l ≫ pullback.fst _ _ = z.left := pullback.lift_fst _ _ _
    have l2 : l ≫ pullback.snd _ _ = Y.hom := pullback.lift_snd _ _ _
    refine ⟨Over.homMk l l2, ?_⟩
    apply Over.OverMorphism.ext
    have e1 : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
        = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
    have e2 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)
        = pullback.snd (h ≫ snd A T).left φ := pullback.lift_snd _ _ _
    have hx : x.left ≫ pullback.snd A.hom (φ ≫ T.hom) = Y.hom := Over.w x
    apply pullback.hom_ext (f := A.hom) (g := φ ≫ T.hom)
    · refine (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e1).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (h ≫ fst A T).left) l1).trans h1')
    · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e2).trans (l2.trans hx.symm))

end GlobalTheory.TwistFlat
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem isClosedImmersion_kerι : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  intro R _ A T V _ φ H h hh
  have hP : IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom T.hom
  have w : pullback.fst A.hom (φ ≫ T.hom) ≫ A.hom = (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) ≫ T.hom := by
    rw [Category.assoc]; exact pullback.condition
  let g : pullback A.hom (φ ≫ T.hom) ⟶ (A ⊗ T).left :=
    hP.lift (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) w
  have hg1 : g ≫ (fst A T).left = pullback.fst A.hom (φ ≫ T.hom) := hP.lift_fst _ _ _
  have hg2 : g ≫ (snd A T).left = pullback.snd A.hom (φ ≫ T.hom) ≫ φ := hP.lift_snd _ _ _
  have ht : IsPullback g (pullback.snd A.hom (φ ≫ T.hom)) (snd A T).left φ := by
    refine IsPullback.of_right (h₁₂ := (fst A T).left) (h₂₂ := T.hom) ?_ hg2 hP
    rw [hg1]
    exact IsPullback.of_hasPullback A.hom (φ ≫ T.hom)
  have hs : IsPullback (pullback.fst (h ≫ snd A T).left φ)
      ((kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)) (h.left ≫ (snd A T).left) φ := by
    have e1 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom) = pullback.snd (h ≫ snd A T).left φ :=
      pullback.lift_snd _ _ _
    rw [e1, ← Over.comp_left]
    exact IsPullback.of_hasPullback _ _
  have hsq : pullback.fst (h ≫ snd A T).left φ ≫ h.left = (kerι A φ h).left ≫ g := by
    apply hP.hom_ext
    · rw [Category.assoc, Category.assoc, hg1]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, hg2, ← Over.comp_left, pullback.condition]
      exact congrArg (· ≫ φ) (pullback.lift_snd _ _ _).symm
  have hpb : IsPullback (pullback.fst (h ≫ snd A T).left φ) (kerι A φ h).left h.left g :=
    IsPullback.of_bot hs hsq ht
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb hh

end GlobalTheory.TwistFlat
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

lemma res_res_pull {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem triv_pull_of_isPullGen : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → Triv (M.pull p) := by
  intro X Y p M e he
  refine ⟨⟨fun j => res (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit) (e (j PUnit.unit))⟩, fun i j => ?_⟩
  have gg : (M.pull p).g i j = res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit)))
      (pullU p _ (M.g (i PUnit.unit) (j PUnit.unit))) :=
    (Fintype.prod_unique (fun k : PUnit => (res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i k))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j k)))
      (pullU p _ (M.g (i k) (j k)))) ^ (1 : ℤ))).trans (zpow_one _)
  rw [gg]
  have h := he (i PUnit.unit) (j PUnit.unit) (LB.wchart M (fun _ : PUnit => p) i ⊓ LB.wchart M (fun _ : PUnit => p) j)
    (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
    (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit))
    (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit)))
  refine (res_res_pull _ _ _).trans (h.trans ?_)
  exact congrArg _ (res_res_pull _ _ _).symm

end GlobalTheory.CharKer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBDescent

theorem descCompat_of_lbIso : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB →
    LBIso (L.pull (pullback.fst f f)) (L.pull (pullback.snd f f)) →
    ∃ φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ, DescCompat f L φ := by
  intro X Y f L hL hI
  obtain ⟨w, hw⟩ := hI
  have hP := (isGen_iff w).1 hw
  have hle : ∀ i j, chart f L i j ≤ (L.pull (pullback.snd f f)).U (fun _ => j) ⊓ (L.pull (pullback.fst f f)).U (fun _ => i) :=
    fun i j z hz => ⟨mem_pull.2 hz.2, mem_pull.2 hz.1⟩
  refine ⟨fun i j => res (hle i j) (w.s (fun _ => j, fun _ => i)), ?_⟩
  intro z i i' j j' hi hi' hj hj'
  have hc : ∀ a b, pullback.fst f f z ∈ L.U a → pullback.snd f f z ∈ L.U b →
      gm (𝟙 _) z (chart f L a b) (res (hle a b) (w.s (fun _ => b, fun _ => a))) =
        gw w (𝟙 _) z b (fun _ => a) := fun a b ha hb =>
    gm_res (𝟙 _) z (hle a b) ⟨ha, hb⟩ _
  have key := hP _ (𝟙 _) z j' j (fun _ => i') (fun _ => i) hj' hj (mem_pull.2 hi') (mem_pull.2 hi)
  have e1 : gm (𝟙 _) z _ ((L.pull (pullback.fst f f)).g (fun _ => i') (fun _ => i)) =
      gm (pullback.fst f f) z _ (L.g i' i) := by
    have := gm_pull_g L (pullback.fst f f) (𝟙 _) z (fun _ => i') (fun _ => i) (mem_pull.2 hi') (mem_pull.2 hi)
    rw [Category.id_comp] at this
    exact this
  have e2 : (gm (pullback.fst f f) z _ (L.g i' i))⁻¹ = gm (pullback.fst f f) z _ (L.g i i') := by
    rw [inv_eq_iff_mul_eq_one, gm_cocycle hL _ z hi' hi hi', gm_self hL _ z hi']
  rw [Category.id_comp, e1, e2] at key
  rw [hc i' j' hi' hj', hc i j hi hj, key]
  ac_rfl

end GlobalTheory.LBDescent
end

section

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

theorem _root_.GlobalTheory.T.polarisationOperator_formula_groupAndProjectors : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι) (M : ℕ) (a b : Fin N), ∃ F : FreeAlgebra O (Letter O N ι), ∀ (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)), (∀ σ, Antitone (res N (lam σ))) → (∀ σ w, IsProj O N lam σ w (P σ w)) → ∑ c : Fin N, lam τ c ≤ M → ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O a b 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧ evalE O N lam P F (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y) := by
  first | exact @GlobalTheory.PolarFormula.polar_formula | exact GlobalTheory.PolarFormula.polar_formula | (intros; apply GlobalTheory.PolarFormula.polar_formula <;> assumption)
end
