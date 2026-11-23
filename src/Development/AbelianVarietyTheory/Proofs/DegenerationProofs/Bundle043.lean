module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLimitPointTateIsoSequence
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle004

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.TupleGlue

private theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

variable {X : Scheme.{0}} {N : X.Opens} {J : Type}

private theorem isUnit_res (s : Γ(X, N)) {W : X.Opens} (h : W ≤ X.basicOpen s) :
    IsUnit (resG X (h.trans (X.basicOpen_le s)) s) := by
  have hu : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
  have := hu.map (resG X h)
  rwa [rr] at this

theorem eq_of_mul_eq (v : J → Γ(X, N)) (hv : N ≤ ⨆ i, X.basicOpen (v i)) {a b : Γ(X, N)}
    (h : ∀ i, a * v i = b * v i) : a = b := by
  refine X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv a b fun i => ?_
  change resG X (X.basicOpen_le (v i)) a = resG X (X.basicOpen_le (v i)) b
  apply (isUnit_res (v i) le_rfl).mul_right_cancel
  have := congrArg (resG X (X.basicOpen_le (v i))) (h i)
  rwa [map_mul, map_mul] at this

theorem exists_mul (u v : J → Γ(X, N)) (hv : N ≤ ⨆ i, X.basicOpen (v i))
    (h : ∀ i j, u i * v j = u j * v i) : ∃ r : Γ(X, N), ∀ j, u j = r * v j := by
  have hq : ∀ i, ∃ q : Γ(X, X.basicOpen (v i)), resG X (X.basicOpen_le (v i)) (u i) =
      q * resG X (X.basicOpen_le (v i)) (v i) := fun i =>
    ⟨resG X (X.basicOpen_le (v i)) (u i) * ↑(isUnit_res (v i) le_rfl).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun i => X.basicOpen (v i)) q := by
    intro i j
    change resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q i) =
      resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q j)
    have e1 := congrArg (resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq j)
    rw [map_mul, rr, rr] at e1 e2
    have e3 := congrArg (resG X ((inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _).trans
      (X.basicOpen_le (v i)))) (h i j)
    rw [map_mul, map_mul, e1, e2] at e3
    have ui := isUnit_res (v i) (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)
    have uj := isUnit_res (v j) (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)
    apply (ui.mul uj).mul_right_cancel
    linear_combination e3
  obtain ⟨r₀, hr, -⟩ := X.sheaf.existsUnique_gluing' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv q hcomp
  let r : Γ(X, N) := r₀
  refine ⟨r, fun j => ?_⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv (u j) (r * v j) fun i => ?_
  change resG X (X.basicOpen_le (v i)) (u j) = resG X (X.basicOpen_le (v i)) (r * v j)
  have hri : resG X (X.basicOpen_le (v i)) r = q i := hr i
  rw [map_mul, hri]
  apply (isUnit_res (v i) le_rfl).mul_right_cancel
  have e3 := congrArg (resG X (X.basicOpen_le (v i))) (h i j)
  rw [map_mul, map_mul, hq i] at e3
  linear_combination -e3

theorem exists_unit_mul (u v : J → Γ(X, N)) (hu : N ≤ ⨆ i, X.basicOpen (u i))
    (hv : N ≤ ⨆ i, X.basicOpen (v i))
    (h : ∀ i j, u i * v j = u j * v i) : ∃ r : Γ(X, N)ˣ, ∀ j, u j = r * v j := by
  obtain ⟨r, hr⟩ := exists_mul u v hv h
  obtain ⟨r', hr'⟩ := exists_mul v u hu fun i j => by linear_combination h j i
  have h1 : r * r' = 1 := eq_of_mul_eq u hu fun i => by
    rw [_root_.mul_assoc, ← hr', ← hr, _root_.one_mul]
  exact ⟨⟨r, r', h1, by rw [_root_.mul_comm, h1]⟩, hr⟩

private theorem cover_res {U : X.Opens} (e : N ≤ U) (v : J → Γ(X, U))
    (hv : U ≤ ⨆ i, X.basicOpen (v i)) : N ≤ ⨆ i, X.basicOpen (resG X e (v i)) := by
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hv (e hx))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  erw [Scheme.basicOpen_res]
  exact ⟨hx, hi⟩

theorem exists_sections : ∀ (X : Scheme.{0}) (A J : Type) (V : A → X.Opens) (t : ∀ a, J → Γ(X, V a)), (∀ a, V a ≤ ⨆ i, X.basicOpen (t a i)) → (∀ a a' i j, resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' j) = resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a j) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i)) → ∃ (g : ∀ a a', Γ(X, V a ⊓ V a')ˣ) (T : J → LB.Sec (⟨A, V, g⟩ : LB X)), ∀ i a, (T i).f a = t a i := by
  intro X A J V t hV h
  choose g hg using fun a a' => exists_unit_mul
    (fun i => resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i))
    (fun i => resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i))
    (cover_res _ _ (hV a)) (cover_res _ _ (hV a')) (h a a')
  exact ⟨g, fun i => ⟨fun a => t a i, fun a a' => hg a a' i⟩, fun _ _ => rfl⟩

end GlobalTheory.TupleGlue
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

def refinePull {X Y : Scheme.{0}} (A : LB Y) (π : X ⟶ Y) {I : Type} (V : I → X.Opens) (idx : I → A.ι)
    (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) : LB X where
  «ι» := I
  U := V
  g l l' := res (show V l ⊓ V l' ≤ π ⁻¹ᵁ (A.U (idx l) ⊓ A.U (idx l')) from fun _ hy => ⟨le l hy.1, le l' hy.2⟩)
    (pullU π _ (A.g (idx l) (idx l')))

theorem gm_refinePull {X Y : Scheme.{0}} (A : LB Y) (π : X ⟶ Y) {I : Type} (V : I → X.Opens) (idx : I → A.ι)
    (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) (y : X) (l l' : I) (h : y ∈ V l) (h' : y ∈ V l') :
    gm (𝟙 X) y (V l ⊓ V l') ((refinePull A π V idx le).g l l') =
      gm π y (A.U (idx l) ⊓ A.U (idx l')) (A.g (idx l) (idx l')) := by
  have hm : (𝟙 X : X ⟶ X) y ∈ V l ⊓ V l' := ⟨h, h'⟩
  refine (gm_res (𝟙 X) y _ hm _).trans ((gm_pull (𝟙 X) π y (A.U (idx l) ⊓ A.U (idx l'))
    ⟨le l h, le l' h'⟩ _).trans ?_)
  rw [Category.id_comp]

theorem refinePull_isLB {X Y : Scheme.{0}} (A : LB Y) (hA : A.IsLB) (π : X ⟶ Y) {I : Type} (V : I → X.Opens)
    (idx : I → A.ι) (le : ∀ l, V l ≤ π ⁻¹ᵁ A.U (idx l)) (hV : ⨆ l, V l = ⊤) : (refinePull A π V idx le).IsLB := by
  refine ⟨hV, fun (l : I) => unit_ext (V := V l) fun y hy => ?_,
    fun (i j k : I) => unit_ext (V := V i ⊓ V j ⊓ V k) fun y hy => ?_⟩
  · refine (gm_res (𝟙 X) y _ hy _).trans ((gm_refinePull A π V idx le y l l hy hy).trans ?_)
    exact (mul_eq_left.1 (gm_cocycle hA π y (le l hy) (le l hy) (le l hy))).trans (map_one _).symm
  · refine (map_mul _ _ _).trans ((congrArg₂ (· * ·)
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y i j hy.1.1 hy.1.2))
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y j k hy.1.2 hy.2))).trans
      ((gm_cocycle hA π y (le i hy.1.1) (le j hy.1.2) (le k hy.2)).trans
      ((gm_res (𝟙 X) y _ hy _).trans (gm_refinePull A π V idx le y i k hy.1.1 hy.2)).symm))

theorem exists_mem_splitChart {S : Scheme.{0}} (E : SplitExt S) (y : E.B.left) : ∃ j, y ∈ E.chart j := by
  classical
  choose j hj using fun k : Module.Free.ChooseBasisIndex ℤ E.X => exists_chart (E.O (E.basis k)).isLB y
  refine ⟨j, ?_⟩
  show y ∈ ((⨅ k, (E.O (E.basis k)).L.U (j k) : E.B.left.Opens) : Set E.B.left)
  rw [TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter.2 hj

theorem exists_affine_refinement : ∀ (S : Scheme.{0}) (E : SplitExt S) (Y : Scheme.{0}) (A : LB Y), A.IsLB → ∀ π : E.B.left ⟶ Y, ∃ N₀ : LB E.B.left, N₀.IsLB ∧ (∀ l, IsAffineOpen (N₀.U l)) ∧ (∀ l, ∃ j, N₀.U l ≤ E.chart j) ∧ Nonempty (ChartPull N₀ A π) := by
  intro S E Y A hA π
  have key : ∀ y : E.B.left, ∃ (V : E.B.left.Opens) (i : A.ι), y ∈ V ∧ IsAffineOpen V ∧ V ≤ π ⁻¹ᵁ A.U i ∧
      ∃ j, V ≤ E.chart j := fun y => by
    obtain ⟨i, hi⟩ := exists_chart hA (π y)
    obtain ⟨j, hj⟩ := exists_mem_splitChart E y
    obtain ⟨V, hV, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := π ⁻¹ᵁ A.U i ⊓ E.chart j) ⟨hi, hj⟩
    exact ⟨V, i, hy, hV, fun z hz => (hle hz).1, j, fun z hz => (hle hz).2⟩
  choose V idx hy haff le hch using key
  refine ⟨refinePull A π V idx le, refinePull_isLB A hA π V idx le ?_, haff, hch,
    ⟨⟨idx, le, fun y l l' h h' => gm_refinePull A π V idx le y l l' h h'⟩⟩⟩
  exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩

end GlobalTheory.ZH.UFib
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_sec_compat {Y Z : Scheme.{0}} {M : LB Y} (φ : M.Sec) (r : Z ⟶ Y) (z : Z) {l l' : M.ι}
    (hl : r z ∈ M.U l) (hl' : r z ∈ M.U l') :
    gs r z (M.U l) (φ.f l) = (gm r z (M.U l ⊓ M.U l') (M.g l l')).val * gs r z (M.U l') (φ.f l') := by
  have hm : r z ∈ M.U l ⊓ M.U l' := ⟨hl, hl'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (φ.compat l l')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem exists_sec_of_refine : ∀ (Y : Scheme.{0}) (M A : LB Y), M.IsLB → A.IsLB →
    ∀ (c : ChartPull M A (𝟙 Y)) (φ : M.Sec), ∃ s : A.Sec, ∀ (l : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ M.U l → gs r z (M.U l) (φ.f l) = gs r z (A.U (c.idx l)) (s.f (c.idx l)) := by
  intro Y M A hM hA c φ
  have cle : ∀ l (y : Y), y ∈ M.U l → y ∈ A.U (c.idx l) := fun l y hy => c.le l hy
  have glue : ∀ i : A.ι, ∃ a : Γ(Y, A.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : M.ι),
      r z ∈ A.U i → r z ∈ M.U l →
      gs r z _ a = (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) := by
    intro i
    let W : M.ι → Y.Opens := fun l => A.U i ⊓ M.U l
    have hW : ∀ l, W l ≤ A.U i ⊓ A.U (c.idx l) := fun l y hy => ⟨hy.1, cle l y hy.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) l, r z ∈ W l →
        gs r z (W l) (u l) =
          (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) :=
      ⟨fun l => (Y.presheaf.map (homOfLE (hW l)).op).hom (A.g i (c.idx l)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W l ≤ M.U l)).op).hom (φ.f l), fun Z r z l hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (hW l hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (A.U i)
      (fun l => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨l, hl⟩ := exists_chart hM y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hy, hl⟩) u
      (fun l l' => fn_ext (V := W l ⊓ W l') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y l hy.1, hu _ _ y l' hy.2, gs_sec_compat φ (𝟙 Y) y hy.1.2 hy.2.2, c.g y l l' hy.1.2 hy.2.2,
          ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hA (𝟙 Y) y hy.1.1 (cle l y hy.1.2) (cle l' y hy.2.2)])
    refine ⟨a, fun Z r z l h₁ h₂ => ?_⟩
    have hz : r z ∈ W l := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W l)) (ha l)).trans (hu Z r z l hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun l Z r z hl => ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 Y) y _ hy _) (gs_res (𝟙 Y) y _ hy _))).symm)
    rw [ha j _ (𝟙 Y) y l hy.1 hl, ha j' _ (𝟙 Y) y l hy.2 hl,
      ← gm_cocycle hA (𝟙 Y) y hy.1 hy.2 (cle l y hl), Units.val_mul, _root_.mul_assoc]
  · have m := cle l _ hl
    refine Eq.symm ((ha _ Z r z l m hl).trans ?_)
    rw [gm_self hA r z m, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorsLift

theorem exists_pow_eq_hom {X M : Type} [AddCommGroup X] [Module.Free ℤ X] [CommGroup M] (n : ℕ)
    (h : ∀ m : M, ∃ r : M, r ^ n = m) (f : Multiplicative X →* M) :
    ∃ g : Multiplicative X →* M, g ^ n = f := by
  choose r hr using h
  let b := Module.Free.chooseBasis ℤ X
  let g : X →ₗ[ℤ] Additive M :=
    b.constr ℤ fun i => Additive.ofMul (r (f (Multiplicative.ofAdd (b i))))
  have hg : n • g = (MonoidHom.toAdditiveRight f).toIntLinearMap := by
    refine b.ext fun i => ?_
    simp only [g, LinearMap.smul_apply, Module.Basis.constr_basis]
    rw [← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft g.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hg x.toAdd)

theorem exists_pow_eq_unit (k : Type) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 1 ≤ n)
    (m : Γ(Sp k, ⊤)ˣ) : ∃ r : Γ(Sp k, ⊤)ˣ, r ^ n = m := by
  let e : Γ(Sp k, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e m.val) (n := n) hn
  have h1 : (e.symm z) ^ n = m.val := by
    rw [← map_pow, hz, RingEquiv.symm_apply_apply]
  have hu : IsUnit (e.symm z) := (isUnit_pow_iff (by omega : n ≠ 0)).1 (h1 ▸ m.isUnit)
  exact ⟨hu.unit, Units.ext (by simpa using h1)⟩

theorem exists_pow_eq_torus (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] (n : ℕ) (hn : 1 ≤ n) (t : Out.baseOver (Sp k) ⟶ splitTorus (Sp k) X) :
    ∃ s : Out.baseOver (Sp k) ⟶ splitTorus (Sp k) X, s ^ n = t := by
  let e := splitTorusPointsEquiv (Sp k) X (Out.baseOver (Sp k))
  obtain ⟨g, hg⟩ := exists_pow_eq_hom n (exists_pow_eq_unit k n hn) (e t)
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_pow, e.apply_symm_apply]
  exact hg

theorem points_lift :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (D : E.GtDatum G) (n : ℕ), 1 ≤ n → (∀ b : Out.baseOver (Sp k) ⟶ E.B, ∃ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = b) ∧ (∀ b : Out.baseOver (Sp k) ⟶ E.B, b ^ n = 1 → ∃ x : Out.baseOver (Sp k) ⟶ G, x ^ n = 1 ∧ x ≫ D.q = b) ∧ ∀ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = 1 → ∃ x' : Out.baseOver (Sp k) ⟶ G, x' ≫ D.q = 1 ∧ x' ^ n = x := by
  intro k _ _ E G _ _ D n hn
  have := D.q_hom
  have := D.i_hom
  have h1 : ∀ b : Out.baseOver (Sp k) ⟶ E.B, ∃ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = b :=
    RatLift.exists_point_over k E G D
  have h3 : ∀ x : Out.baseOver (Sp k) ⟶ G, x ≫ D.q = 1 →
      ∃ x' : Out.baseOver (Sp k) ⟶ G, x' ≫ D.q = 1 ∧ x' ^ n = x := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_pow_eq_torus k E.X n hn (D.isKernel.lift x (toUnit _) hx)
    refine ⟨s ≫ D.i, ?_, ?_⟩
    · rw [Category.assoc, D.isKernel.w, ← Category.assoc, comp_toUnit]
      rfl
    · rw [← MonObj.pow_comp, hs, D.isKernel.lift_fst]
  refine ⟨h1, fun b hb => ?_, h3⟩
  obtain ⟨x, hx⟩ := h1 b
  obtain ⟨y, hy, hyx⟩ := h3 (x ^ n) (by rw [MonObj.pow_comp, hx, hb])
  refine ⟨x * y⁻¹, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hyx, mul_inv_cancel]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, hx, hy, inv_one, _root_.mul_one]

end GlobalTheory.TorsLift
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.exists_limitPoint_tateIso_sequence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : ℕ → TateIso D k Q act e), ∃ I' : TateIso D k Q act e, ∀ M, 0 < M → ∀ j₀, ∃ j, j₀ ≤ j ∧ I'.ev M = (I j).ev M ∧ I'.ζ M = (I j).ζ M := by
  first | exact @GlobalTheory.Ex.TateLimit.exists_limit | exact GlobalTheory.Ex.TateLimit.exists_limit | (intros; apply GlobalTheory.Ex.TateLimit.exists_limit <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FibreLinInd

theorem geometric_of_field (G Z : Scheme.{0}) (f : G ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] (L : LB G) (r : ℕ) (s : Fin r → LB.Sec L) (z : Z)
    (K : Type) [Field K] (x : Sp K ⟶ Z) (hx : Set.range x = {z})
    (hz : ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0)
    (K' : Type) [Field K'] [IsAlgClosed K'] (x' : Sp K' ⟶ Z) (hx' : Set.range x' = {z})
    (c : Fin r → K') (hc : ∀ (g : Sp K' ⟶ G) (j : L.ι), g ≫ f = x' →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) : c = 0 := by
  classical
  obtain ⟨P, p, π, h1, h2, h3, h4⟩ := exists_fibrePower f r
  have hxt : ∀ t, x t = z := fun t => by
    rw [← Set.mem_singleton_iff, ← hx]
    exact ⟨t, rfl⟩
  let t₀ : Sp K := IsLocalRing.closedPoint K
  obtain ⟨a, ha⟩ := exists_det_ne_zero
    (fun (a : {g : Sp K ⟶ G // g ≫ f = x} × L.ι) i => valF a.1.1 (L.U a.2) ((s i).f a.2))
    fun c hc => hz c fun g j hg => hc (⟨g, hg⟩, j)
  let j : Fin r → L.ι := fun k => (a k).2
  let U : P.Opens := LB.wchart L π j
  have hU : ∀ k, U ≤ π k ⁻¹ᵁ L.U (j k) := LB.wchart_le L π j
  let M : Matrix (Fin r) (Fin r) Γ(P, U) :=
    Matrix.of fun k i => (π k).appLE (L.U (j k)) U (hU k) ((s i).f (j k))
  have hM : ∀ {K : Type} [Field K] (h : Sp K ⟶ P) (hh : ⊤ ≤ h ⁻¹ᵁ U), evalHom h U hh M.det =
      (Matrix.of fun k i => valF (h ≫ π k) (L.U (j k)) ((s i).f (j k))).det := by
    intro K _ h hh
    rw [RingHom.map_det]
    congr 1
    ext k i
    exact evalHom_appLE h U hh (π k) _ (hU k) _
  let O : P.Opens := P.basicOpen M.det
  have hmem : z ∈ p '' (O : Set P) := by
    obtain ⟨h, hp, hπ⟩ := h4 (Sp K) x (fun k => (a k).1.1) fun k => (a k).1.2
    have hle : ⊤ ≤ h ⁻¹ᵁ U := by
      intro t ht
      refine Set.mem_iInter.2 fun k => ?_
      have hk : ⊤ ≤ (a k).1.1 ⁻¹ᵁ L.U (j k) := by
        by_contra hn
        exact ha (Matrix.det_eq_zero_of_row_eq_zero k fun i => dif_neg hn)
      have := hk ht
      rw [← hπ k] at this
      exact this
    refine ⟨h t₀, (mem_basicOpen_iff h U hle M.det t₀).2 ?_, ?_⟩
    · rw [hM]
      simp only [hπ]
      exact ha
    · rw [← Scheme.Hom.comp_apply, hp, hxt]
  obtain ⟨w, hw, rfl⟩ := hmem
  let t : Sp K' := IsLocalRing.closedPoint K'
  have ht : x' t = p w := by
    rw [← Set.mem_singleton_iff, ← hx']
    exact ⟨t, rfl⟩
  obtain ⟨h, hh⟩ := exists_lift (O.ι ≫ p) x' ⟨w, hw⟩ t ht.symm
  have hO : (h ≫ O.ι) t ∈ O := (h t).2
  have hle : ⊤ ≤ (h ≫ O.ι) ⁻¹ᵁ U := (top_le_iff _ U t).2 (P.basicOpen_le _ hO)
  have hd := (mem_basicOpen_iff _ U hle M.det t).1 hO
  rw [hM] at hd
  refine Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun k => ?_)
  have := hc ((h ≫ O.ι) ≫ π k) (j k) (by rw [Category.assoc, h3, Category.assoc, hh])
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

theorem linearIndependent_on_fibres_of_closedPoints :
    ∀ (G Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G), L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), let P : Z → Prop := fun z => ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0; (∀ z, IsClosed ({z} : Set Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Z), Set.range x = {z} ∧ ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0) → ∀ z, P z := by
  intro G Z π _ f _ _ L hL r s P h z
  let U : Z.Opens := ⟨{z | P z}, isOpen_setOf_linearIndependent_on_fibres G Z f L hL r s⟩
  have hU : U = ⊤ := (GlobalTheory.jacobson_closedPoints_tools_int Z π).2.2.1 U ⊤ fun y hy => by
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨K, _, x, hx, hz⟩ := h y hy
    intro K' _ _ x' hx' c hc
    exact geometric_of_field G Z f L r s y K x hx hz K' x' hx' c hc
  have : z ∈ U := by rw [hU]; trivial
  exact this

end GlobalTheory.FibreLinInd
end
end
