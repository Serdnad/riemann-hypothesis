module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AbTorsionFiniteF

theorem finite_torsion_TF : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} := by
  intro R _ _ D F _ _ _ k hk
  let g := jFK (R := R) F ≫ jK R
  let B' := (Over.pullback g).obj D.P.A
  have hB : IsAbelianScheme B' := GlobalTheory.isAbelianScheme_pullback_obj g D.P.A D.P.isAb
  have hfin := GlobalTheory.AbTorsionFinite.finite_torsion F B' hB k hk
  let φ : (TF (R := R) F ⟶ D.P.A) → (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ B') := fun x =>
    Over.homMk (pullback.lift x.left (𝟙_ (Over (Spec (CommRingCat.of F)))).hom
      ((Over.w x).trans (by simp [g]))) (pullback.lift_snd _ _ _)
  have hφ : ∀ x, (φ x).left ≫ pullback.fst D.P.A.hom g = x.left := fun x => pullback.lift_fst _ _ _
  have hpow : ∀ x : TF (R := R) F ⟶ D.P.A, (φ x) ^ k = 1 ↔ x ^ k = 1 := fun x =>
    GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull (by simp [g]) (isGrpPullback_pullback D.P.A g) (hφ x)
  refine Finite.of_injective (fun x : {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} =>
    (⟨φ x.1, (hpow x.1).2 x.2⟩ : {y : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ B' // y ^ k = 1})) ?_
  intro a b hab
  have e := congrArg (fun y => y.1.left ≫ pullback.fst D.P.A.hom g) hab
  simp only [hφ] at e
  exact Subtype.ext (Over.OverMorphism.ext e)

end GlobalTheory.AbTorsionFiniteF
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem extLI_preimage_le {X X' Y : Scheme.{0}} (a : Y ⟶ X') (f : X' ⟶ X) (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X.Opens) : a ⁻¹ᵁ (f ⁻¹ᵁ W) ≤ α ⁻¹ᵁ W := by
  intro y hy
  show α y ∈ W
  rw [← e, Scheme.Hom.comp_apply]
  exact hy

theorem extLI_le_chart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X'.Opens) (j : L.ι) (hW : W ≤ f ⁻¹ᵁ L.U j) :
    a ⁻¹ᵁ W ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => extLI_preimage_le a f α e (L.U j) (hW hy)

theorem extLI_le_wchart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (j : Fin 1 → L.ι) :
    a ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j ≤ LB.wchart L (K := Fin 1) (fun _ => α) j :=
  fun _ hy => Set.mem_iInter.2 fun k => extLI_preimage_le a f α e (L.U (j k)) (Set.mem_iInter.1 hy k)

theorem extLI_preimage_mono {X Y : Scheme.{0}} (a : Y ⟶ X) {V V' : X.Opens} (hV : V ≤ V') : a ⁻¹ᵁ V ≤ a ⁻¹ᵁ V' :=
  fun _ hz => hV hz

theorem extLI_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE h3).op).hom x := by
  change (Y.presheaf.map (homOfLE h1).op ≫ Y.presheaf.map (homOfLE h2).op).hom x = _
  rw [← Functor.map_comp]
  rfl

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SquareSpread

theorem germ_res_hom {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) {x : X} (hx : x ∈ V) (s : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (X.presheaf.germ U x (h hx)).hom s :=
  TopCat.Presheaf.germ_res_apply _ (homOfLE h) x hx s

theorem res_res_hom {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_res_eq {X : Scheme.{0}} {U : X.Opens} {x : X} (hx : x ∈ U) (s t : Γ(X, U))
    (h : (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom t) :
    ∃ W : X.Opens, ∃ hW : W ≤ U, x ∈ W ∧
      (X.presheaf.map (homOfLE hW).op).hom s = (X.presheaf.map (homOfLE hW).op).hom t := by
  obtain ⟨W, hxW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hx hx s t h
  refine ⟨W, iU.le, hxW, ?_⟩
  have h1 : iU = homOfLE iU.le := rfl
  have h2 : iV = homOfLE iU.le := Subsingleton.elim _ _
  rw [h1] at e
  rw [h2] at e
  exact e

end GlobalTheory.Mum.SquareSpread


open GlobalTheory.Mum.SquareSpread in
theorem GlobalTheory.Mum.unit_mul_sq_spread : ∀ (X : Scheme.{0}) (L2 : LB X) (h : L2.Sec) (x : X) (j₀ : L2.ι) (hx : x ∈ L2.U j₀) (u : (X.presheaf.stalk x)ˣ) (a : X.presheaf.stalk x), a ≠ 0 → (X.presheaf.germ (L2.U j₀) x hx).hom (h.f j₀) = u * a ^ 2 → ∃ V : X.Opens, x ∈ V ∧ ∃ a : Γ(X, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(X, V ⊓ L2.U j)ˣ, (X.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(X, V ⊓ L2.U j)) * (X.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  intro X L2 h x j₀ hx u a ha hh

  obtain ⟨W₁, hW₁, hx₁, a', ha'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf a hx
  obtain ⟨W₂, hW₂, hx₂, u', hu'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf (u : X.presheaf.stalk x) hx₁
  obtain ⟨W₃, hW₃, hx₃, v', hv'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) hx₂
  have l31 : W₃ ≤ W₁ := hW₃.trans hW₂
  have l30 : W₃ ≤ L2.U j₀ := l31.trans hW₁
  set A : Γ(X, W₃) := (X.presheaf.map (homOfLE l31).op).hom a' with hA
  set U' : Γ(X, W₃) := (X.presheaf.map (homOfLE hW₃).op).hom u' with hU'
  set H : Γ(X, W₃) := (X.presheaf.map (homOfLE l30).op).hom (h.f j₀) with hH
  have gA : (X.presheaf.germ W₃ x hx₃).hom A = a := by rw [hA, germ_res_hom]; exact ha'
  have gU : (X.presheaf.germ W₃ x hx₃).hom U' = u := by rw [hU', germ_res_hom]; exact hu'
  have gV : (X.presheaf.germ W₃ x hx₃).hom v' = ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) := hv'
  have gH : (X.presheaf.germ W₃ x hx₃).hom H = u * a ^ 2 := by rw [hH, germ_res_hom]; exact hh
  obtain ⟨W₄, hW₄, hx₄, e₄⟩ := exists_res_eq hx₃ (U' * v') 1 (by
    rw [map_mul, map_one, gU, gV, Units.mul_inv])
  obtain ⟨W₅, hW₅, hx₅, e₅⟩ := exists_res_eq hx₃ H (U' * A ^ 2) (by
    rw [map_mul, map_pow, gU, gA, gH])

  have lV3 : W₄ ⊓ W₅ ≤ W₃ := inf_le_left.trans hW₄
  have hxV : x ∈ W₄ ⊓ W₅ := ⟨hx₄, hx₅⟩
  have e₄' : (X.presheaf.map (homOfLE lV3).op).hom U' * (X.presheaf.map (homOfLE lV3).op).hom v' = 1 := by
    rw [← map_mul, ← map_one (X.presheaf.map (homOfLE lV3).op).hom, ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄),
      ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄) 1, e₄]
  have e₅' : (X.presheaf.map (homOfLE lV3).op).hom H = (X.presheaf.map (homOfLE lV3).op).hom U' *
      ((X.presheaf.map (homOfLE lV3).op).hom A) ^ 2 := by
    rw [← map_pow, ← map_mul, ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅),
      ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅) (U' * A ^ 2), e₅]
  let uV : Γ(X, W₄ ⊓ W₅)ˣ := ⟨_, _, e₄', by rw [mul_comm]; exact e₄'⟩
  refine ⟨W₄ ⊓ W₅, hxV, (X.presheaf.map (homOfLE lV3).op).hom A, ?_, ?_⟩
  · intro h0
    apply ha
    rw [← gA, ← germ_res_hom lV3 hxV, h0, map_zero]
  · intro j
    have k : W₄ ⊓ W₅ ⊓ L2.U j ≤ L2.U j ⊓ L2.U j₀ := le_inf inf_le_right (inf_le_left.trans (lV3.trans l30))
    refine ⟨res k (L2.g j j₀) * Units.map (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom uV, ?_⟩
    have c := congrArg (X.presheaf.map (homOfLE k).op).hom (h.compat j j₀)
    rw [map_mul, res_res_hom, res_res_hom] at c
    have e6 := congrArg (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom e₅'
    rw [map_mul, map_pow, hH, res_res_hom, res_res_hom, res_res_hom] at e6
    rw [Units.val_mul, Units.coe_map, res, Units.coe_map]
    simp only [MonoidHom.coe_coe, hA, res_res_hom] at e6 ⊢
    rw [c, e6, _root_.mul_assoc]
    congr 2
    exact (res_res_hom lV3 _ U').symm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CechPic

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (x : Γ(X, U)ˣ) :
    res h1 (res h2 x) = res (h1.trans h2) x :=
  unit_ext fun y hy => by rw [gm_res _ y _ hy, gm_res _ y _ (h1 hy), gm_res _ y _ hy]

theorem app_restrict {X X₀ : Scheme.{0}} (i : X₀ ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (i.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (X₀.presheaf.map (homOfLE (fun y (hy : y ∈ i ⁻¹ᵁ V) => (h hy : i y ∈ U))).op).hom ((i.app U).hom x) := by
  have e := congrArg (fun q => q.hom x) (i.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

end GlobalTheory.CechPic
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.finite_kTorsion_abelianPart_algClosed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} := by
  first | exact @GlobalTheory.AbTorsionFiniteF.finite_torsion_TF | exact GlobalTheory.AbTorsionFiniteF.finite_torsion_TF | (intros; apply GlobalTheory.AbTorsionFiniteF.finite_torsion_TF <;> assumption)

end
end
