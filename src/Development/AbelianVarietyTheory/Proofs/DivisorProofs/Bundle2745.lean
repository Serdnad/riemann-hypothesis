module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section
namespace GlobalTheory.VertCoeffRing

theorem isLieBasis_tvE : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  intro R _ G _ _ n v
  have hE : (overAt (𝟙 (Sp R)) (DualNumber R)).hom = (epsR R).hom := by
    simp [epsR, overAt]
  let e : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (𝟙 _) (by simp [hE])
  let f : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ epsR R := Over.homMk (𝟙 _) (by simp [hE])
  have hfe : f ≫ e = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])
  have hef : e ≫ f = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])

  have htv : ∀ x : TanM (𝟙 (Sp R)) G, tvE x = e ≫ tv x := by
    intro x
    apply Over.OverMorphism.ext
    first
    | (simp only [e, Over.comp_left, Over.homMk_left, Category.id_comp]; exact tvE_left x)
    | simp [e, tvE_left x]
  have hadd : ∀ x y : TanM (𝟙 (Sp R)) G, tvE (x + y) = tvE x * tvE y := by
    intro x y; rw [htv, htv, htv, PullbackSections.tv_add, MonObj.comp_mul]
  have hzero : tvE (0 : TanM (𝟙 (Sp R)) G) = 1 := by
    rw [htv, PullbackSections.tv_zero, MonObj.comp_one]

  have hsmul : ∀ (a : R) (x : TanM (𝟙 (Sp R)) G),
      (tvE (a • x)).left = spMap (epsScaleR a) ≫ (tvE x).left := by
    intro a x; rw [tvE_left, tvE_left, PullbackSections.tv_smul]
    first
    | rfl
    | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
  have hinj : ∀ x y : TanM (𝟙 (Sp R)) G, tvE x = tvE y → x = y := by
    intro x y h
    apply PullbackSections.tanM_ext
    have h' := congrArg (fun t => f ≫ t) h
    simpa [htv, ← Category.assoc, hfe] using h'
  have hsum : ∀ (c : Fin n → R) (s : Finset (Fin n)),
      tvE (∑ i ∈ s, c i • v i) = ∏ i ∈ s, tvE (c i • v i) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]

  have hcomb : ∀ (c : Fin n → R) (w : epsR R ⟶ G),
      IsLieComb c (fun a => tvE (v a)) w ↔ w = tvE (∑ i, c i • v i) := by
    intro c w
    rw [IsLieComb.eq_1, hsum]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [List.prod_ofFn]
      refine Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext ?_
      rw [hu i, hsmul]
    · rintro rfl
      exact ⟨fun i => tvE (c i • v i), fun i => hsmul _ _, by rw [List.prod_ofFn]⟩

  have hfa : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp
  have hdual : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    simp only [spMap.eq_1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id]
    all_goals rfl
  have hz : spMap (epsScaleR (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have h0 : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
      refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
      all_goals first
        | (simp [epsScaleR]; done)
        | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done)
        | (simp [epsScaleR.eq_1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fstHom_apply,
            TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]; done)
        | rfl
        | (simp [epsScaleR]; rfl)
    rw [h0]
    simp only [spMap.eq_1, CommRingCat.ofHom_comp, Spec.map_comp]
  have hu : (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left = spMap (algebraMap R (DualNumber R)) := by
    first
    | simp [overAt]
    | (have h := Over.w (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))); simpa [overAt] using h)
  have hone : (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left =
      spMap (algebraMap R (DualNumber R)) ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := by
    calc (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left
        = (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := rfl
      _ = _ := by rw [hu]

  have key : ∀ g : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, smT (𝟙 (Sp R)) 0 g = 1 ↔ IsTangent (e ≫ g) := by
    intro g
    rw [IsTangent.eq_1]
    have hl : (smT (𝟙 (Sp R)) 0 g).left = spMap (algebraMap R (DualNumber R)) ≫
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g.left := by
      rw [← Category.assoc, ← hz]
      first
      | rfl
      | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
    have he : ∀ t : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (e ≫ t).left =
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t.left := by
      intro t; simp [e]
    rw [he]
    constructor
    · intro h
      have h2 := congrArg Over.Hom.left h
      rw [hl, hone] at h2
      have h3 := congrArg (fun t => spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t) h2
      simpa only [← Category.assoc, hdual, Category.id_comp] using h3
    · intro h
      apply Over.OverMorphism.ext
      rw [hl, hone, h]
  have htan : ∀ x, IsTangent (tvE x) := fun x => by
    rw [htv]; exact (key (tv x)).1 (PullbackSections.tv_mem x)
  have hsurj : ∀ w : epsR R ⟶ G, IsTangent w → ∃ x, tvE x = w := by
    intro w hw
    have hw' : IsTangent (e ≫ (f ≫ w)) := by rwa [← Category.assoc, hef, Category.id_comp]
    refine ⟨PullbackSections.mkT (f ≫ w) ((key _).2 hw'), ?_⟩
    rw [htv, PullbackSections.tv_mkT, ← Category.assoc, hef, Category.id_comp]
  rw [IsLieBasis.eq_1]
  refine ⟨fun i => htan (v i), fun w hw => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj w hw
  refine ⟨⇑(v.repr x), (hcomb _ _).2 ?_, fun c hc => ?_⟩
  · rw [v.sum_repr]
  · have h := hinj _ _ ((hcomb c _).1 hc)
    rw [h, v.repr_sum_self]

end GlobalTheory.VertCoeffRing
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThBdl

theorem resG_resG_glue {X : Scheme.{0}} {A B C : X.Opens} (h : B ≤ A) (h' : C ≤ B) (f : Γ(X, A)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem locSec_glue : ∀ (S : Scheme.{0}) (G : Over S) (L : LB G.left) (V : S.Opens) (κ : Type) (N : κ → S.Opens)
    (s : ∀ k, LocSec G L (N k)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V → (∀ k, IsLocSec (s k)) →
    (∀ k k' i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k) (s k i) =
      resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k') (s k' i)) →
    ∃ s' : LocSec G L V, IsLocSec s' ∧ ∀ k i,
      resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i := by
  intro S G L V κ N s hN hV hs hc
  have hmem : ∀ x : G.left, G.hom.base x ∈ V → ∃ k, G.hom.base x ∈ N k := by
    intro x hx
    have : G.hom.base x ∈ (⨆ k, N k) := by rw [hV]; exact hx
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hcov : ∀ i, L.U i ⊓ G.hom ⁻¹ᵁ V ≤ ⨆ k, (L.U i ⊓ G.hom ⁻¹ᵁ N k) := by
    intro i x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  have hWV : ∀ i k, L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V := fun i k _ hx => ⟨hx.1, hN k hx.2⟩
  have hglue : ∀ i, ∃! t : Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ V), ∀ k, resG _ (hWV i k) t = s k i := by
    intro i
    refine G.left.sheaf.existsUnique_gluing' (fun k => L.U i ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ G.hom ⁻¹ᵁ V)
      (fun k => homOfLE (hWV i k)) (hcov i) (fun k => s k i) ?_
    intro k k'
    have hle : (L.U i ⊓ G.hom ⁻¹ᵁ N k) ⊓ (L.U i ⊓ G.hom ⁻¹ᵁ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') :=
      fun _ hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩
    have e := congrArg (resG _ hle) (hc k k' i)
    exact (resG_resG_glue _ _ _).symm.trans (e.trans (resG_resG_glue _ _ _))
  choose s' hs' _ using hglue
  refine ⟨s', ?_, fun k i => hs' i k⟩
  intro i j
  have hTV : ∀ k, L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V := fun k _ hx => ⟨hx.1, hN k hx.2⟩
  refine G.left.sheaf.eq_of_locally_eq' (fun k => L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V)
    (fun k => homOfLE (hTV k)) ?_ _ _ ?_
  · intro x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  · intro k
    have hi1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.1, hx.2⟩
    have hj1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U j ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.2, hx.2⟩
    have e1 : resG _ (hi1.trans (hWV i k)) (s' i) = resG _ hi1 (s k i) := by
      rw [← hs' i k, resG_resG_glue]
    have e2 : resG _ (hj1.trans (hWV j k)) (s' j) = resG _ hj1 (s k j) := by
      rw [← hs' j k, resG_resG_glue]
    change resG _ (hTV k) (resG _ _ (s' i)) =
      resG _ (hTV k) (resG _ _ (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) * resG _ _ (s' j))
    rw [map_mul]
    refine ((resG_resG_glue _ _ _).trans e1).trans ((hs k i j).trans ?_)
    congr 1
    · exact (resG_resG_glue _ _ _).symm
    · exact ((resG_resG_glue _ _ _).trans e2).symm

end GlobalTheory.UMin.ThBdl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl.Glued

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U W : X.Opens} (h : W ≤ U) (f : Γ(X, U))
    (hy : ⊤ ≤ y ⁻¹ᵁ W) : valF y W (resG X h f) = valF y U f := by
  have hU : ⊤ ≤ y ⁻¹ᵁ U := fun a ha => h (hy ha)
  unfold valF
  rw [dite_eq_left hy, dite_eq_left hU]
  congr 1
  show (X.presheaf.map (homOfLE h).op ≫ y.appLE W ⊤ hy).hom f = _
  rw [Scheme.Hom.map_appLE]

theorem glued : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S)
    (V : S.Opens) (κ : Type) (N : κ → S.Opens) (s : ∀ k, LocSec G L (N k)) (s' : LocSec G L V)
    (v : SecM G L 1 (Over.mk ξ)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V →
    (∀ k i, resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i) →
    (∀ k, GenIs ξ (s k) v) → (∀ k, FibNz (s k) (N k)) → (Nonempty κ → GenIs ξ s' v) ∧ FibNz s' V := by
  intro S G _ L K _ ξ V κ N s s' v hN hsup hres hgen hnz
  refine ⟨fun ⟨k⟩ => ?_, ?_⟩
  · obtain ⟨hξk, hk⟩ := hgen k
    refine ⟨hξk.trans (hN k), ?_⟩
    rw [← hk]
    funext j
    unfold genPull
    rw [← hres k (j 0)]
    show _ = (G.left.presheaf.map _ ≫ (snd (Over.mk ξ) G).left.appLE _ _ _).hom (s' (j 0))
    rw [Scheme.Hom.map_appLE]
  · intro K' _ _ x hx
    obtain ⟨p⟩ : Nonempty (Sp K') := inferInstance
    have hp : x p ∈ (⨆ k, N k : S.Opens) := hsup ▸ hx ⟨p, rfl⟩
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    have hxk : Set.range x ⊆ N k := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q p]
      exact hk
    obtain ⟨y, i, hyx, hyr, hval⟩ := hnz k K' x hxk
    refine ⟨y, i, hyx, fun z hz => ⟨(hyr hz).1, hN k (hyr hz).2⟩, ?_⟩
    rw [← hres k i] at hval
    convert hval using 1
    exact (valF_resG y _ (s' i) ((GlobalTheory.ZH.top_le_preimage_iff _ _).2 hyr)).symm

end GlobalTheory.UMin.ThBdl.Glued
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

theorem genPt_dom {S : Scheme.{0}} [IsIntegral S] {K : Type} [Field K] (ξ : Sp K ⟶ S)
    (hξ : Set.range ξ = {genericPoint S}) : QuasiCompact ξ ∧ IsSchemeTheoreticallyDominant ξ := by
  have hd : IsDominant ξ := ⟨by
    show Dense (Set.range ξ)
    rw [hξ]
    exact dense_iff_closure_eq.2 (genericPoint_spec S)⟩
  refine ⟨⟨fun U _ _ => (Set.subsingleton_of_subsingleton).isCompact⟩, ?_⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant ξ

theorem app_snd_injective {S : Scheme.{0}} [IsIntegral S] (G : Over S) [Flat G.hom] {K : Type} [Field K]
    (ξ : Sp K ⟶ S) (hξ : Set.range ξ = {genericPoint S}) (O : G.left.Opens) :
    Function.Injective ((snd (Over.mk ξ) G).left.app O).hom := by
  obtain ⟨_, _⟩ := genPt_dom ξ hξ
  have hP : IsPullback (fst (Over.mk ξ) G).left (snd (Over.mk ξ) G).left ξ G.hom := .of_hasPullback _ _
  have : IsSchemeTheoreticallyDominant (snd (Over.mk ξ) G).left := IsSchemeTheoreticallyDominant.of_isPullback hP
  have : QuasiCompact (snd (Over.mk ξ) G).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hP inferInstance
  exact (snd (Over.mk ξ) G).left.app_injective O

theorem locSec_eq_of_genIs : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S), Set.range ξ = {genericPoint S} →
    ∀ (N N' : S.Opens) (s : LocSec G L N) (s' : LocSec G L N') (v : SecM G L 1 (Over.mk ξ)),
      GenIs ξ s v → GenIs ξ s' v → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i) := by
  intro S _ G _ _ hG L K _ ξ hξ N N' s s' v ⟨h₁, e₁⟩ ⟨h₂, e₂⟩ i
  have := hG.smooth
  have hfl : Flat G.hom := inferInstance
  have e := congrFun (e₁.trans e₂.symm) (fun _ => i)
  have h₃ : Set.range ξ ⊆ ((N ⊓ N' : S.Opens) : Set S) := fun x hx => ⟨h₁ hx, h₂ hx⟩
  set O : G.left.Opens := L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') with hO
  set W : (Over.mk ξ ⊗ G).left.Opens := (LPow G L 1 (Over.mk ξ)).U (fun _ => i) with hW
  have hle : W ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ O := lpow_U_le h₃ (fun _ => i)
  have hge : (snd (Over.mk ξ) G).left ⁻¹ᵁ O ≤ W := fun y hy => Set.mem_iInter.2 fun _ => hy.1
  have hinj : Function.Injective ((snd (Over.mk ξ) G).left.appLE O W hle).hom := by
    have hEq : W = (snd (Over.mk ξ) G).left ⁻¹ᵁ O := le_antisymm hle hge
    clear_value W
    subst hEq
    rw [← Scheme.Hom.app_eq_appLE]
    exact app_snd_injective G ξ hξ O
  apply hinj
  have k₁ : ((snd (Over.mk ξ) G).left.appLE O W hle).hom
      (resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : O ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i)) = genPull h₁ s (fun _ => i) := by
    dsimp only [resG]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have k₂ : ((snd (Over.mk ξ) G).left.appLE O W hle).hom
      (resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : O ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) = genPull h₂ s' (fun _ => i) := by
    dsimp only [resG]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  exact k₁.trans (e.trans k₂.symm)

end GlobalTheory.UMin.ThBdl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinKer

open Matrix GlobalTheory.ZarhinFam

def kerN (d : ℕ) : ord d :=
  ⟨form d * single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [Matrix.mul_apply, single]⟩

def kerM (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inr 0) 1 * formInv d, fun i j => by simp [Matrix.mul_apply, single]⟩

theorem idem_mul_kerN (d : ℕ) : idem d * kerN d = polUnit d := by
  ext1
  simp only [Subring.coe_mul, idem, kerN, polUnit_coe]
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single]
  simp [form]

theorem kerM_mul_bar_kerN {d : ℕ} (hd : 0 < d) : kerM d * bar d (kerN d) = idem d := by
  ext1
  simp only [Subring.coe_mul, bar_coe, kerM, kerN, idem, Matrix.transpose_mul, transpose_single, form_transpose]
  calc single (Sum.inl 0) (Sum.inr 0) (1 : ℤ) * formInv d *
        (form d * (single (Sum.inr 0) (Sum.inl 0) 1 * form d) * formInv d)
      = single (Sum.inl 0) (Sum.inr 0) (1 : ℤ) * (formInv d * form d) * single (Sum.inr 0) (Sum.inl 0) 1 *
          (form d * formInv d) := by simp only [Matrix.mul_assoc]
    _ = single (Sum.inl 0) (Sum.inl 0) 1 := by
      rw [formInv_mul_form hd, form_mul_formInv hd, Matrix.mul_one, Matrix.mul_one, single_mul_single_same, _root_.one_mul]

end GlobalTheory.ZarhinKer

namespace GlobalTheory.ZarhinKer

open GlobalTheory.ZarhinFam

theorem polUnit_ker_le : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 → ∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen := by
  intro h M d hd S t c z act inc pr _hdu _hker _hprin hact hadj _hinc _hpr hip hpi hP T x hx
  have hinc_idem : inc ≫ act (idem d) = inc := by
    rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hN : inc ≫ act (kerN d) = inc ≫ act (polUnit d) := by
    calc inc ≫ act (kerN d) = (inc ≫ act (idem d)) ≫ act (kerN d) := by rw [hinc_idem]
      _ = inc ≫ act (polUnit d) := by rw [Category.assoc, ← hact.2.2.1, idem_mul_kerN]
  have hM : inc ≫ act (kerM d) ≫ act (bar d (kerN d)) = inc := by
    rw [← hact.2.2.1, kerM_mul_bar_kerN hd, hinc_idem]
  have hv : (snd c.A T ≫ x ≫ inc) ≫ act (kerN d) = 1 := by
    rw [Category.assoc, Category.assoc, hN, hx, comp_one]
  have e1 : ((fst c.A T ≫ inc ≫ act (kerM d)) ≫ lift (1 : z.A ⟶ z.A) (𝟙 z.A)).left =
      (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc ≫ act (kerM d))).left ≫
        (lift (fst z.A z.A ≫ act (kerN d)) (snd z.A z.A)).left := by
    rw [← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, comp_one]
      rw [← hv]; simp only [Category.assoc]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, Category.comp_id]
  have e2 : (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc)).left =
      (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc ≫ act (kerM d))).left ≫
        (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar d (kerN d)))).left := by
    rw [← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, lift_fst, lift_fst_assoc]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, hM]
  have e3 : (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc)).left =
      (lift (snd c.A T ≫ x) (fst c.A T)).left ≫ (inc ⊗ₘ inc).left := by
    rw [← Over.comp_left]
    congr 1
    rw [lift_map, Category.assoc]
  have i1 := GlobalTheory.GenSpread.lbIso_pull_comp _ e1 e2 (hadj (kerN d))
  have i2 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP (lift (snd c.A T ≫ x) (fst c.A T)).left e3
  obtain ⟨t0, ht0⟩ := z.rig₁
  have g1 : ∃ u : LB.Gen (z.P.pull ((fst c.A T ≫ inc ≫ act (kerM d)) ≫ lift (1 : z.A ⟶ z.A) (𝟙 z.A)).left),
      u.IsGen :=
    ⟨LB.pullGen z.P _ _ t0 (fst c.A T ≫ inc ≫ act (kerM d)).left,
      LB.isGen_pullGen z.P _ _ t0 ht0 (fst c.A T ≫ inc ≫ act (kerM d)).left⟩
  have g2 := GlobalTheory.RigidBundleGlue.exists_gen_of_lbIso (pull_isLB z.isLB _) (pull_isLB z.isLB _) i1 g1
  exact GlobalTheory.RigidBundleGlue.exists_gen_of_lbIso (pull_isLB z.isLB _) (pull_isLB c.isLB _) i2.symm g2

end GlobalTheory.ZarhinKer
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum


theorem _root_.GlobalTheory.T.exists_twistedThetaValue_subsingleton_base : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A), Subsingleton T.left → Odd m → N = m ^ 2 → τ.IsGen → x ^ N = 1 → h ^ m = β ≫ z₀ → ∃ v, IsTwVal P N m θ τ β x h v := by
  first | exact @GlobalTheory.UPoinc.USum.exists_isTwVal_of_subsingleton | exact GlobalTheory.UPoinc.USum.exists_isTwVal_of_subsingleton | (intros; apply GlobalTheory.UPoinc.USum.exists_isTwVal_of_subsingleton <;> assumption)
end
