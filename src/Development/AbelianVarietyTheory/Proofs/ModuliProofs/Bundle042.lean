module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeEighthPowerOfMatrixAction
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ActDescent

variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
theorem _root_.GlobalTheory.ActDescent.over_hom_ext {X Y : Over S} {X' : Scheme.{0}} {φ : X' ⟶ X.left} {p : X' ⟶ U}
    (h : IsPullback φ p X.hom j) {f g : X ⟶ Y} (hfg : φ ≫ f.left = φ ≫ g.left) : f = g := by
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip ‹Flat j›
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹Surjective j›
  have := Flat.epi_of_flat_of_surjective φ
  exact Over.OverMorphism.ext ((cancel_epi φ).mp hfg)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
omit [Flat j] [Surjective j] in
theorem _root_.GlobalTheory.ActDescent.pullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left := by
  exact pullback.lift_fst _ _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
variable (j) in
theorem _root_.GlobalTheory.ActDescent.pullback_map_injective (X Y : Over S) :
    Function.Injective ((Over.pullback j).map : (X ⟶ Y) → _) := by
  intro a b hab
  apply _root_.GlobalTheory.ActDescent.over_hom_ext (IsPullback.of_hasPullback X.hom j)
  rw [← _root_.GlobalTheory.ActDescent.pullback_map_left_fst, ← _root_.GlobalTheory.ActDescent.pullback_map_left_fst, hab]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
private theorem mul_comp_of_descends_monHom {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ) (hH : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback H' H j ψ) (f' : G' ⟶ H') [IsMonHom f'] (f : G ⟶ H)
    (hf : f'.left ≫ ψ = φ ≫ f.left) (T : Over S) (x y : T ⟶ G) :
    (x * y) ≫ f = x ≫ f * y ≫ f := by
  have hT : IsPullback (pullback.fst T.hom j) (pullback.snd T.hom j) T.hom j :=
    IsPullback.of_hasPullback _ _
  apply _root_.GlobalTheory.ActDescent.over_hom_ext hT
  let T' : Over U := (Over.pullback j).obj T
  let ρ : Over.mk (T'.hom ≫ j) ⟶ T :=
    Over.homMk (pullback.fst T.hom j) (by simp [T', pullback.condition])
  let up : (T ⟶ G) → (T' ⟶ G') := fun z => Over.homMk
    (hG.1.lift (pullback.fst T.hom j ≫ z.left) T'.hom (by simp [T', pullback.condition]))
    (hG.1.lift_snd _ _ _)
  have hup : ∀ z : T ⟶ G, (up z).left ≫ φ = pullback.fst T.hom j ≫ z.left :=
    fun z => hG.1.lift_fst _ _ _
  have hpush : ∀ z : T ⟶ G, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG T' (up z) = ρ ≫ z :=
    fun z => Over.OverMorphism.ext (by exact hup z)
  have hpushH : ∀ z : T ⟶ G, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hH T' (up z ≫ f') = ρ ≫ z ≫ f := by
    intro z
    ext1
    change ((up z).left ≫ f'.left) ≫ ψ = pullback.fst T.hom j ≫ z.left ≫ f.left
    rw [Category.assoc, hf, ← Category.assoc, hup, Category.assoc]
  change (ρ ≫ (x * y) ≫ f).left = (ρ ≫ (x ≫ f * y ≫ f)).left
  rw [MonObj.comp_mul ρ (x ≫ f), ← hpushH x, ← hpushH y, ← map_mul, ← MonObj.mul_comp,
    ← Category.assoc, MonObj.comp_mul ρ x y, ← hpush x, ← hpush y, ← map_mul]
  change ((up x * up y).left ≫ φ) ≫ f.left = ((up x * up y) ≫ f').left ≫ ψ
  rw [Over.comp_left, Category.assoc, Category.assoc, hf]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
theorem _root_.GlobalTheory.ActDescent.isMonHom_descend {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ) (hH : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback H' H j ψ) (f' : G' ⟶ H') [IsMonHom f'] (f : G ⟶ H)
    (hf : f'.left ≫ ψ = φ ≫ f.left) : IsMonHom f := by
  have key := mul_comp_of_descends_monHom hG hH f' f hf
  refine ⟨?_, ?_⟩
  · have h1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ f = 1 := by
      have h := key (𝟙_ (Over S)) 1 1
      rw [_root_.one_mul] at h
      exact mul_eq_left.mp h.symm
    simpa [Hom.one_def] using h1
  · have h := key _ (fst G G) (snd G G)
    simpa [Hom.mul_def] using h



open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
theorem _root_.GlobalTheory.ActDescent.exists_oAct {O : Type} [CommRing O] {G : Over S} [GrpObj G]
    {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ)
    (i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G') (hi : ∀ x, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) :
    ∃ a : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  choose g hg using hi
  have hpb := hG.1
  have hmon : ∀ x, IsMonHom (g x) := fun x =>
    haveI := i.hom x
    _root_.GlobalTheory.ActDescent.isMonHom_descend hG hG (i.act x) (g x) (hg x)
  refine ⟨⟨g, hmon, ?_, ?_, ?_⟩, hg⟩
  · apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    rw [← hg, i.one]
    simp
  · intro a b
    apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    rw [← hg, i.mul, Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, hg,
      Category.assoc]
  · intro a b
    apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    let ρ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hpb.w
    have hpush : ∀ c, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG G' (i.act c) = ρ ≫ g c :=
      fun c => Over.OverMorphism.ext (by exact hg c)
    change (ρ ≫ g (a + b)).left = (ρ ≫ (g a * g b)).left
    rw [MonObj.comp_mul, ← hpush, ← hpush, ← hpush, ← map_mul, i.add]

end GlobalTheory.ActDescent

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
theorem _root_.GlobalTheory.oAct_descend_of_generators : ∀ (O : Type) [CommRing O] (J : Type) (a : J → O) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K₀)) (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A₀] [GrpObj A] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A) (act₀ : J → (A₀ ⟶ A₀)), Subring.closure (Set.range a) = ⊤ → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A A₀ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → ∃ r : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A₀, (∀ j, r.act (a j) = act₀ j) ∧ ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left := by
  intro O _ J a K₀ K _ _ i A₀ A _ _ _ φ act act₀ hgen hG hact
  haveI : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap; infer_instance
  haveI : Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap; infer_instance
  let ρ : Over.mk (A.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) ⟶ A₀ := Over.homMk φ hG.1.w
  have hiff : ∀ (z : A ⟶ A) (g : A₀ ⟶ A₀), z.left ≫ φ = φ ≫ g.left →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG A z = ρ ≫ g := fun z g h => Over.OverMorphism.ext (by exact h)
  have hback : ∀ (z : A ⟶ A) (g : A₀ ⟶ A₀), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG A z = ρ ≫ g →
      z.left ≫ φ = φ ≫ g.left := fun z g h => by
    have h' := congrArg (fun m => m.left) h
    exact h'
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hD : ∀ c, ∃ g : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ g.left := by
    intro c
    have hc : c ∈ Subring.closure (Set.range a) := hgen ▸ Subring.mem_top c
    induction hc using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨act₀ k, hact k⟩
    | zero =>
      refine ⟨1, hback _ _ ?_⟩
      rw [h0, map_one, MonObj.comp_one]
    | one =>
      exact ⟨𝟙 _, by simp [act.one]⟩
    | add x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      refine ⟨g * g', hback _ _ ?_⟩
      rw [act.add, map_mul, hiff _ _ hg, hiff _ _ hg', MonObj.comp_mul]
    | neg x _ hx =>
      obtain ⟨g, hg⟩ := hx
      have hneg : act.act (-x) = (act.act x)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← act.add, add_neg_cancel, h0]
      refine ⟨g⁻¹, hback _ _ ?_⟩
      rw [hneg, map_inv, hiff _ _ hg, GrpObj.comp_inv]
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      refine ⟨g ≫ g', ?_⟩
      rw [act.mul, Over.comp_left, Over.comp_left, Category.assoc, hg', ← Category.assoc, hg,
        Category.assoc]
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.ActDescent.exists_oAct hG act hD
  refine ⟨r, fun k => ?_, hr⟩
  apply _root_.GlobalTheory.ActDescent.over_hom_ext hG.1
  rw [← hr, hact]

end GlobalTheory
end
end

section

open Complex Matrix
open scoped ContDiff BigOperators Real Topology

namespace GlobalTheory.PeriodicCousin

variable {g : ℕ}

noncomputable def dbar (a : Fin g) (f : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) : ℂ :=
  fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))

theorem dbar_congr {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : f =ᶠ[𝓝 z] f') :
    dbar a f z = dbar a f' z := by
  unfold dbar; rw [h.fderiv_eq]

theorem dbar_sub {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z) :
    dbar a (fun x => f x - f' x) z = dbar a f z - dbar a f' z := by
  unfold dbar
  rw [fderiv_fun_sub h h']
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem contDiffAt_fderiv {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fderiv ℝ f) z :=
  h.fderiv_right (m := ∞) (by norm_cast)

theorem contDiffAt_dbar {a : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (dbar a f) z := by
  have h1 := contDiffAt_fderiv h
  exact (h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))

theorem fderiv_dbar {a : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) (v : Fin g → ℂ) :
    fderiv ℝ (dbar a f) z v = fderiv ℝ (fderiv ℝ f) z v (Pi.single a 1 : Fin g → ℂ) +
      I * fderiv ℝ (fderiv ℝ f) z v (I • (Pi.single a 1 : Fin g → ℂ)) := by
  have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((contDiffAt_fderiv h).differentiableAt (by simp)).hasFDerivAt
  have h2 := fun u : Fin g → ℂ =>
    (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp z h1
  have h3 := (h2 (Pi.single a 1)).add ((h2 (I • (Pi.single a 1 : Fin g → ℂ))).const_mul I)
  have h4 : fderiv ℝ (dbar a f) z = _ := h3.fderiv
  rw [h4]
  simp

theorem dbar_comm {a b : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) : dbar a (dbar b f) z = dbar b (dbar a f) z := by
  have hs : IsSymmSndFDerivAt ℝ f z := h.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have e : ∀ u v, fderiv ℝ (fderiv ℝ f) z u v = fderiv ℝ (fderiv ℝ f) z v u := hs
  show fderiv ℝ (dbar b f) z _ + I * fderiv ℝ (dbar b f) z _ =
    fderiv ℝ (dbar a f) z _ + I * fderiv ℝ (dbar a f) z _
  rw [fderiv_dbar h, fderiv_dbar h, fderiv_dbar h, fderiv_dbar h,
    e (Pi.single b 1) (Pi.single a 1), e (Pi.single b 1) (I • (Pi.single a 1 : Fin g → ℂ)),
    e (I • (Pi.single b 1 : Fin g → ℂ)) (Pi.single a 1),
    e (I • (Pi.single b 1 : Fin g → ℂ)) (I • (Pi.single a 1 : Fin g → ℂ))]
  ring

noncomputable def antilin (t : Fin g → ℂ) : (Fin g → ℂ) →L[ℝ] ℂ :=
  ∑ a, t a • ((conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj a))

theorem antilin_apply (t z : Fin g → ℂ) : antilin t z = t ⬝ᵥ star z := by
  simp [antilin, dotProduct]

theorem dbar_antilin (t z : Fin g → ℂ) (a : Fin g) : dbar a (antilin t) z = 2 * t a := by
  unfold dbar
  rw [ContinuousLinearMap.fderiv, antilin_apply, antilin_apply]
  have h1 : star (Pi.single a 1 : Fin g → ℂ) = Pi.single a 1 := by
    ext j; by_cases h : j = a
    · subst h; simp
    · simp [h]
  rw [star_smul, h1]
  simp only [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, star_def, conj_I]
  linear_combination (-t a) * I_mul_I

end GlobalTheory.PeriodicCousin

namespace GlobalTheory
open PeriodicCousin

theorem holomorphic_periodic_cocycle_coboundary : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i j, DifferentiableOn ℂ (c i j) (U i ∩ U j)) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, c i j (z + l) = c i j z) → (∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z = c i k z) → ∃ (t : (Fin g → ℂ)) (h : ι → (Fin g → ℂ) → ℂ), (∀ i, DifferentiableOn ℂ (h i) (U i) ∧ ∀ (l : Λ), ∀ z ∈ U i, h i (z + l) = h i z + t ⬝ᵥ star (l : (Fin g → ℂ))) ∧ ∀ i j, ∀ z ∈ U i ∩ U j, c i j z = h j z - h i z := by
  intro g Λ hd hs ι U c hU hUΛ hcov hc hcΛ hcoc
  have hcs : ∀ i j, ContDiffOn ℝ ∞ (c i j) (U i ∩ U j) := fun i j =>
    ((GlobalTheory.T.cauchyRiemann_iff_differentiableOn g _ (c i j) ((hU i).inter (hU j))).2 (hc i j)).1
  obtain ⟨b, hb, hcb⟩ := GlobalTheory.T.exists_periodic_smooth_coboundary_of_cech_cocycle g Λ hd hs ι U c hU hUΛ hcov hcs hcΛ hcoc
  choose k hk using hcov
  have hbAt : ∀ i, ∀ z ∈ U i, ContDiffAt ℝ ∞ (b i) z := fun i z hz =>
    (hb i).1.contDiffAt ((hU i).mem_nhds hz)
  have hind : ∀ a i j, ∀ z ∈ U i, z ∈ U j → dbar a (b j) z = dbar a (b i) z := by
    intro a i j z hi hj
    have ho := (hU i).inter (hU j)
    have h0 : dbar a (c i j) z = 0 :=
      ((GlobalTheory.T.cauchyRiemann_iff_differentiableOn g _ (c i j) ho).1 ((hcs i j).differentiableOn (by simp))).2 (hc i j) a z ⟨hi, hj⟩
    have h1 : c i j =ᶠ[𝓝 z] fun x => b j x - b i x := by
      filter_upwards [ho.mem_nhds ⟨hi, hj⟩] with x hx using hcb i j x hx
    rw [dbar_congr h1, dbar_sub ((hbAt j z hj).differentiableAt (by simp))
      ((hbAt i z hi).differentiableAt (by simp))] at h0
    exact sub_eq_zero.1 h0
  let w : Fin g → (Fin g → ℂ) → ℂ := fun a z => dbar a (b (k z)) z
  have hw : ∀ a i, ∀ z ∈ U i, w a z = dbar a (b i) z := fun a i z hz => hind a i (k z) z hz (hk z)
  have hw' : ∀ a i, ∀ z ∈ U i, w a =ᶠ[𝓝 z] dbar a (b i) := by
    intro a i z hz
    filter_upwards [(hU i).mem_nhds hz] with x hx using hw a i x hx
  obtain ⟨t, f, hf, hfΛ, hft⟩ := GlobalTheory.T.exists_periodic_dbar_solution g Λ hd hs w (by
    intro a
    refine ⟨contDiff_iff_contDiffAt.2 fun z =>
      (contDiffAt_dbar (hbAt _ z (hk z))).congr_of_eventuallyEq (hw' a _ z (hk z)), fun l z => ?_⟩
    rw [hw a (k z) _ (hUΛ _ l z (hk z)), hw a (k z) z (hk z)]
    have h1 : (fun x => b (k z) (x + l)) =ᶠ[𝓝 z] b (k z) := by
      filter_upwards [(hU _).mem_nhds (hk z)] with x hx using (hb _).2 l x hx
    rw [← dbar_congr h1]
    unfold dbar
    rw [fderiv_comp_add_right]) (by
    intro a a' z
    show dbar a (w a') z = dbar a' (w a) z
    rw [dbar_congr (hw' a' _ z (hk z)), dbar_congr (hw' a _ z (hk z))]
    exact dbar_comm (hbAt _ z (hk z)))
  have hfd : ∀ z, DifferentiableAt ℝ f z := fun z => (hf.differentiable (by simp)) z
  refine ⟨-((1 / 2 : ℂ) • t), fun i z => b i z - f z - antilin ((1 / 2 : ℂ) • t) z,
    fun i => ⟨?_, ?_⟩, ?_⟩
  · have hbd : ∀ z ∈ U i, DifferentiableAt ℝ (b i) z := fun z hz =>
      (hbAt i z hz).differentiableAt (by simp)
    refine ((GlobalTheory.T.cauchyRiemann_iff_differentiableOn g _ _ (hU i)).1 ?_).1 ?_
    · intro z hz
      exact (((hbd z hz).sub (hfd z)).sub (antilin _).differentiableAt).differentiableWithinAt
    · intro a z hz
      show dbar a (fun z => (b i z - f z) - antilin ((1 / 2 : ℂ) • t) z) z = 0
      have h3 : dbar a f z = w a z - t a := hft a z
      rw [dbar_sub ((hbd z hz).fun_sub (hfd z)) (antilin _).differentiableAt,
        dbar_sub (hbd z hz) (hfd z), dbar_antilin, h3, hw a i z hz]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · intro l z hz
    simp only [(hb i).2 l z hz, hfΛ l z, map_add (f := _), antilin_apply _ (l : Fin g → ℂ), neg_dotProduct]
    ring
  · intro i j z hz
    rw [hcb i j z hz]
    ring

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsAbelianScheme G → (∀ m, IsMonHom (ρ m)) → (∀ m m', ρ (m * m') = ρ m' ≫ ρ m) → (∀ m m', ρ (m + m') = ρ m * ρ m') → ρ 1 = 𝟙 G → ∃ (A : Over S) (_ : GrpObj A) (pr : Fin 8 → (G ⟶ A)), IsAbelianScheme A ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧ ∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := by
  first | exact @GlobalTheory.MatrixPower.abelianScheme_matrix_power | exact GlobalTheory.MatrixPower.abelianScheme_matrix_power | (intros; apply GlobalTheory.MatrixPower.abelianScheme_matrix_power <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.finrank_symm_commutant_kronecker_le : ∀ (K : Type) [Field K] (h : ℕ) (Em Ei : Matrix (Fin 8) (Fin 8) ℤ) (V : Submodule K (Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)), Em.IsSymm → Ei * Em = 1 → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose) → Module.finrank K V ≤ h * (h + 1) / 2 := by
  first | exact @GlobalTheory.ZM.finrank_symm_commutant_le | exact GlobalTheory.ZM.finrank_symm_commutant_le | (intros; apply GlobalTheory.ZM.finrank_symm_commutant_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
theorem _root_.GlobalTheory.KS.exists_derivation_extend_of_formallySmooth :
    ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra.FormallySmooth R B] (φ : B →+* C) (D : R → C), (∀ a b, D (a + b) = D a + D b) → (∀ a b, D (a * b) = φ (algebraMap R B a) * D b + φ (algebraMap R B b) * D a) → ∃ d : B → C, (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = φ a * d b + φ b * d a) ∧ ∀ r, d (algebraMap R B r) = D r := by
  intro R B C _ _ _ _ _ φ D hadd hmul
  have h0 : D 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have h1 : D 1 = 0 := by
    have h11 := hmul 1 1
    have e : (1 : R) * 1 = 1 := mul_one 1
    rw [e, map_one, map_one, _root_.one_mul] at h11
    linear_combination -h11
  let ψ : R →+* TrivSqZeroExt C C :=
    { toFun := fun r => TrivSqZeroExt.inl (φ (algebraMap R B r)) + TrivSqZeroExt.inr (D r)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun a b => by ext <;> simp [hmul] <;> ring
      map_zero' := by ext <;> simp [h0]
      map_add' := fun a b => by ext <;> simp [hadd] }
  letI : Algebra R (TrivSqZeroExt C C) := ψ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  let g : TrivSqZeroExt C C →ₐ[R] C :=
    { (TrivSqZeroExt.fstHom C C C).toRingHom with
      commutes' := fun r => by
        show (ψ r).fst = φ (algebraMap R B r)
        simp [ψ] }
  let f : B →ₐ[R] C :=
    { φ with
      commutes' := fun r => rfl }
  have hg : Function.Surjective g := fun c => ⟨TrivSqZeroExt.inl c, by simp [g]⟩
  have hker : IsNilpotent (RingHom.ker g) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.mpr fun x hx y hy => ?_
    rw [RingHom.mem_ker] at hx hy
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx, hy]
  let L := Algebra.FormallySmooth.liftOfSurjective f g hg hker
  refine ⟨fun b => (L b).snd, fun a b => ?_, fun a b => ?_, fun r => ?_⟩
  · simp
  · have hfa : (L a).fst = φ a := Algebra.FormallySmooth.liftOfSurjective_apply f g hg hker a
    have hfb : (L b).fst = φ b := Algebra.FormallySmooth.liftOfSurjective_apply f g hg hker b
    simp [hfa, hfb]
    ring
  · show (L (algebraMap R B r)).snd = D r
    rw [L.commutes r]
    show (ψ r).snd = D r
    simp [ψ]

end GlobalTheory.KS
end
