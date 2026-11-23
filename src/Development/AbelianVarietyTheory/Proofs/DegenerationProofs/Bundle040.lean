module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Mathlib.RingTheory.Nullstellensatz
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.WtLin

theorem coeff_symm_sum {A B X : Type} [CommRing A] [CommRing B] [AddCommGroup X] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) {J : Type} [Fintype J]
    (c : J → A) (s : J → B) (χ : X) :
    ((Equiv.ofBijective _ hb).symm (∑ i, f (c i) * s i)).coeff χ =
      ∑ i, c i * ((Equiv.ofBijective _ hb).symm (s i)).coeff χ := by
  let e := RingEquiv.ofBijective _ hb
  have h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    change _ = AddMonoidAlgebra.liftNCRingHom f g hc _
    simp [AddMonoidAlgebra.liftNCRingHom]
  change (e.symm _).coeff χ = ∑ i, c i * (e.symm (s i)).coeff χ

  simp [map_sum, map_mul, h1]

theorem app_constFn {R : Type} [CommRing R] {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X)
    (hf : f ≫ q = q') (U : X.Opens) (a : R) :
    (f.app U).hom (constFn q U a) = constFn q' (f ⁻¹ᵁ U) a := by
  subst hf
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U _ (fun _ _ => trivial) le_rfl)

theorem weight_sum {k : Type} [Field k] (Φ : FibPre k) {d : ℕ} {J : Type} [Fintype J]
    (F : J → (Φ.H d).Sec) (a : J → k) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α
        (∑ i, constFn Φ.G.hom ((Φ.H d).U l) (a i) * (F i).f l : Γ(Φ.G.left, (Φ.H d).U l)) =
      ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l := by
  refine Eq.trans ?_ (coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l))
    (fun i => constFn Φ.E.B.hom _ (a i)) (fun i => (F i).f l) α)
  simp only [app_constFn _ _ _ (Over.w Φ.D.q)]
  rfl

theorem weight_zero {k : Type} [Field k] (Φ : FibPre k) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α 0 = 0 := by
  have := coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) (J := Empty)
    Empty.elim Empty.elim α
  simpa [SplitExt.GtDatum.weight] using this

theorem linIndep : (∀ (k : Type) [Field k] (Φ : FibPre k) (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec), Φ.Good N q cls F → ∀ a : J → k, (∀ l, ∑ i, constFn Φ.G.hom ((Φ.H 1).U l) (a i) * (F i).f l = 0) → a = 0) := by
  intro k _ Φ N q J _ cls F hG a ha
  classical
  funext i₀
  have key := hG.inj (cls i₀) (hG.short i₀)
    (fun i => if ∃ m, cls i₀ = cls i + N • m then a i else 0)
    (fun i hi => by
      by_contra h
      exact hi (if_neg h))
    (fun l => by
      have h := weight_sum Φ F a (cls i₀) l
      rw [ha l] at h
      refine Eq.trans ?_ (h.symm.trans (weight_zero Φ _ l))
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rfl
      · have h0 : Φ.wt (F i) (cls i₀) l = 0 := by
          by_contra hne
          exact hi (hG.supp i _ ⟨l, hne⟩).2
        rw [h0, mul_zero, mul_zero])
  have := congrFun key i₀
  rwa [if_pos ⟨0, by simp⟩] at this

end GlobalTheory.ZH.WtLin
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem weight_app {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G]
    (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V)
    (h : V ≤ E.chart j) (χ : E.X) (a : Γ(E.B.left, V)) :
    D.weight j V hV h χ ((D.q.left.app V).hom a) = (Finsupp.single (0 : E.X) a) χ := by
  have e : (Equiv.ofBijective _ (D.coord j V hV h)).symm ((D.q.left.app V).hom a) =
      AddMonoidAlgebra.single 0 a := by
    rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply]
    simp [AddMonoidAlgebra.liftNCRingHom]
  unfold SplitExt.GtDatum.weight
  rw [e, AddMonoidAlgebra.coeff_single]

theorem eq_of_weight_eq {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G]
    (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V)
    (h : V ≤ E.chart j) {s s' : Γ(G.left, D.q.left ⁻¹ᵁ V)}
    (e : ∀ χ, D.weight j V hV h χ s = D.weight j V hV h χ s') : s = s' := by
  apply (Equiv.ofBijective _ (D.coord j V hV h)).symm.injective
  apply AddMonoidAlgebra.ext
  ext χ
  exact e χ

theorem app_res {X Y : Scheme.{0}} (q : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : q ⁻¹ᵁ V ≤ q ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    (q.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (Y.presheaf.map (homOfLE h').op).hom ((q.app U).hom a) := by
  have := q.naturality (homOfLE h).op
  exact congrArg (fun f => f.hom a) this

theorem FibPre.compat_iff {k : Type} [Field k] (Φ : FibPre k) (t : ∀ l, Γ(Φ.E.B.left, Φ.N₀.U l))
    (i j : Φ.N₀.ι) :
    ((Φ.G.left.presheaf.map (homOfLE (inf_le_left : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U i)).op).hom
        ((Φ.D.q.left.app (Φ.N₀.U i)).hom (t i)) =
      ((Φ.H 1).g i j : Γ(Φ.G.left, (Φ.H 1).U i ⊓ (Φ.H 1).U j)) *
        (Φ.G.left.presheaf.map (homOfLE (inf_le_right : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U j)).op).hom
          ((Φ.D.q.left.app (Φ.N₀.U j)).hom (t j))) ↔
    (Φ.E.B.left.presheaf.map (homOfLE (inf_le_left : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U i)).op).hom (t i) =
      (Φ.N₀.g i j : Γ(Φ.E.B.left, Φ.N₀.U i ⊓ Φ.N₀.U j)) *
        (Φ.E.B.left.presheaf.map (homOfLE (inf_le_right : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U j)).op).hom (t j) := by
  have := Φ.D.q_flat
  have := Φ.D.q_surjective
  rw [← (GlobalTheory.FunDescent.app_injective Φ.D.q.left (Φ.N₀.U i ⊓ Φ.N₀.U j)).eq_iff, map_mul,
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_left), app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right)]
  have hg : ((Φ.H 1).g i j : Γ(Φ.G.left, (Φ.H 1).U i ⊓ (Φ.H 1).U j)) =
      (Φ.D.q.left.app (Φ.N₀.U i ⊓ Φ.N₀.U j)).hom (Φ.N₀.g i j) :=
    congrArg Units.val (pow_one (pullU Φ.D.q.left (Φ.N₀.U i ⊓ Φ.N₀.U j) (Φ.N₀.g i j)))
  rw [hg]
  exact Iff.rfl

theorem FibPre.pure_zero : (∀ (k : Type) [Field k] (Φ : FibPre k), (∀ t : Φ.N₀.Sec, ∃ φ : (Φ.H 1).Sec, Φ.Pure 0 φ ∧ ∀ l, Φ.wt φ 0 l = t.f l) ∧ ∀ φ : (Φ.H 1).Sec, Φ.Pure 0 φ → ∃ t : Φ.N₀.Sec, (∀ l, Φ.wt φ 0 l = t.f l) ∧ (∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l)) ∧ Out.nonzeroLocus φ = Φ.D.q.left ⁻¹ᵁ Out.nonzeroLocus t) := by
  intro k _ Φ
  refine ⟨fun t => ?_, fun φ hφ => ?_⟩
  · refine ⟨⟨fun l => (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l),
      fun i j => (Φ.compat_iff t.f i j).2 (t.compat i j)⟩, ?_, fun l => ?_⟩
    · rintro α ⟨l, hl⟩
      by_contra hα
      exact hl ((weight_app Φ.D _ _ _ _ α (t.f l)).trans (Finsupp.single_eq_of_ne hα))
    · exact (weight_app Φ.D _ _ _ _ 0 (t.f l)).trans Finsupp.single_eq_same
  · have hf : ∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (Φ.wt φ 0 l) := fun l => by
      refine eq_of_weight_eq Φ.D (Φ.ch l) _ (Φ.aff l) (Φ.le l) fun χ => ?_
      rw [weight_app]
      by_cases hχ : χ = 0
      · subst hχ
        exact Finsupp.single_eq_same.symm
      · rw [Finsupp.single_eq_of_ne hχ]
        by_contra hne
        exact hχ (hφ ⟨l, hne⟩)
    refine ⟨⟨fun l => Φ.wt φ 0 l, fun i j => (Φ.compat_iff _ i j).1 ?_⟩, fun _ => rfl, hf, ?_⟩
    · have c := φ.compat i j
      rw [hf i, hf j] at c
      exact c
    · unfold Out.nonzeroLocus
      rw [Scheme.Hom.preimage_iSup]
      refine iSup_congr fun l => ?_
      rw [Scheme.preimage_basicOpen, hf]
      rfl

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorusTranslate

theorem appLE_res_pullU {X Y Z : Scheme.{0}} (m : Z ⟶ Y) (f : Y ⟶ X) (g : Z ⟶ X) (e : m ≫ f = g)
    (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (hm : ⊤ ≤ m ⁻¹ᵁ W) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) :
    (m.appLE W ⊤ hm).hom (res h (pullU f U u)).val = (g.appLE U ⊤ hg).hom u.val := by
  subst e
  have : f.app U ≫ Y.presheaf.map (homOfLE h).op ≫ m.appLE W ⊤ hm = (m ≫ f).appLE U ⊤ hg := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appLE]
  exact congrArg (fun φ => φ.hom u.val) this

theorem appLE_app {X Y Z : Scheme.{0}} (m : Z ⟶ Y) (f : Y ⟶ X) (g : Z ⟶ X) (e : m ≫ f = g)
    (U : X.Opens) (hm : ⊤ ≤ m ⁻¹ᵁ (f ⁻¹ᵁ U)) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (u : Γ(X, U)) :
    (m.appLE (f ⁻¹ᵁ U) ⊤ hm).hom ((f.app U).hom u) = (g.appLE U ⊤ hg).hom u := by
  subst e
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem appLE_res {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U W : Y.Opens) (h : W ≤ U)
    (hm : ⊤ ≤ m ⁻¹ᵁ W) (hg : ⊤ ≤ m ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    (m.appLE W ⊤ hm).hom (res h u).val = (m.appLE U ⊤ hg).hom u.val :=
  congrArg (fun φ => φ.hom u.val) (Scheme.Hom.map_appLE m hm (homOfLE h).op)

variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G) {Z : Over S}

theorem torus_comp_q (τ : Z ⟶ splitTorus S E.X) : (τ ≫ D.i) ≫ D.q = 1 := by
  rw [Category.assoc, D.isKernel.w, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem translate_comp_q (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) :
    ((τ ≫ D.i) * x).left ≫ D.q.left = x.left ≫ D.q.left := by
  have := D.q_hom
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, torus_comp_q, _root_.one_mul]

theorem translate_le (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (V : E.B.left.Opens)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V)) : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage] at h ⊢
  rwa [translate_comp_q]

theorem translate_coord (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (j : E.ChartIdx)
    (k : Module.Free.ChooseBasisIndex ℤ E.X)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j))
    (h' : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j)) :
    (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (D.u j k).val =
      τ.left.appTop.hom (charUnit S E.X (E.basis k)).val * (x.left.appLE _ ⊤ h).hom (D.u j k).val := by
  let m : Z ⟶ splitTorus S E.X ⊗ G := lift τ x
  have e1 : m.left ≫ (fst (splitTorus S E.X) G).left = τ.left := by
    rw [← Over.comp_left, lift_fst]
  have e2 : m.left ≫ (snd (splitTorus S E.X) G).left = x.left := by
    rw [← Over.comp_left, lift_snd]
  have e3 : m.left ≫ (lift (fst (splitTorus S E.X) G ≫ D.i) (snd (splitTorus S E.X) G) ≫ μ[G]).left
      = ((τ ≫ D.i) * x).left := by
    rw [← Over.comp_left, Hom.mul_def, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have hm : ⊤ ≤ m.left ⁻¹ᵁ ((snd (splitTorus S E.X) G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j)) := by
    rw [← Scheme.Hom.comp_preimage, e2]; exact h
  have key := congrArg (m.left.appLE _ ⊤ hm).hom (congrArg Units.val (D.equiv j k))
  simp only [Units.val_mul, map_mul] at key
  rw [appLE_res_pullU _ _ _ e3 _ _ _ hm h'] at key
  rw [key]
  congr 1
  · refine (appLE_res_pullU _ _ _ e1 ⊤ _ _ hm le_top _).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  · exact appLE_app _ _ _ e2 _ hm h _

theorem translate_pure (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (j : E.ChartIdx)
    (V : E.B.left.Opens) (hV : IsAffineOpen V) (hle : V ≤ E.chart j) (α : E.X)
    (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) (hs : ∀ β, β ≠ α → D.weight j V hV hle β s = 0)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V))
    (h' : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V)) :
    (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom s =
      τ.left.appTop.hom (charUnit S E.X α).val * (x.left.appLE _ ⊤ h).hom s := by
  have hsingle : (Equiv.ofBijective _ (D.coord j V hV hle)).symm s =
      AddMonoidAlgebra.single α (D.weight j V hV hle α s) := by
    apply AddMonoidAlgebra.ext
    ext β
    by_cases hβ : β = α
    · subst hβ
      simp [SplitExt.GtDatum.weight]
    · have := hs β hβ
      rw [SplitExt.GtDatum.weight] at this
      rw [this]
      simp [Ne.symm hβ]
  generalize D.weight j V hV hle α s = w at hsingle
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, AddMonoidAlgebra.liftNCRingHom_single] at hsingle
  let c : E.X →ₗ[ℤ] Additive Γ(G.left, D.q.left ⁻¹ᵁ V)ˣ := E.basis.constr ℤ (fun k => Additive.ofMul
            (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k)))
  have hs' : s = (D.q.left.app V).hom w * (Additive.toMul (c α)).val := hsingle
  let f₁ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    (Units.map (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom
  let f₂ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    (Units.map (x.left.appLE _ ⊤ h).hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom
  let f₀ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    MonoidHom.toAdditiveRight (splitTorusPointsEquiv S E.X Z τ)
  have hf : f₁.toIntLinearMap = (f₀ + f₂).toIntLinearMap := by
    refine E.basis.ext fun k => ?_
    apply Additive.toMul.injective
    apply Units.ext
    have hc : c (E.basis k) = Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k)) := E.basis.constr_basis _ _ _
    change (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c (E.basis k))).val =
      (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd (E.basis k))).val *
        (x.left.appLE _ ⊤ h).hom (Additive.toMul (c (E.basis k))).val
    have g : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j) :=
      h.trans (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hle))
    rw [hc, toMul_ofMul, splitTorusPointsEquiv_val,
      appLE_res _ _ _ _ h' (translate_le D τ x _ g), appLE_res _ _ _ _ h g]
    exact translate_coord D τ x j k g _
  have hα : (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c α)).val =
      (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd α)).val *
        (x.left.appLE _ ⊤ h).hom (Additive.toMul (c α)).val :=
    congrArg (fun z => (Additive.toMul z).val) (LinearMap.congr_fun hf α)
  have g : ⊤ ≤ (x.left ≫ D.q.left) ⁻¹ᵁ V := h
  rw [hs', map_mul, map_mul, hα, splitTorusPointsEquiv_val,
    appLE_app _ _ _ (translate_comp_q D τ x) V h' g, appLE_app _ _ _ rfl V h g]
  ring

end GlobalTheory.TorusTranslate

namespace GlobalTheory.TorusTranslate

theorem exists_point_translate_pure : (∀ (k : Type) [Field k] (Φ : FibPre k) (t : Multiplicative Φ.E.X →* kˣ), ∃ a : Φ.Pt, a ≫ Φ.D.q = 1 ∧ (∀ n : ℕ, t ^ n = 1 → a ^ n = 1) ∧ ∀ (d : ℕ) (α : Φ.E.X) (φ : (Φ.H d).Sec), Φ.Pure α φ → ∀ (x : Φ.Pt) (l : Φ.N₀.ι), ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l → ⊤ ≤ (a * x).left ⁻¹ᵁ (Φ.H d).U l ∧ valF (a * x).left ((Φ.H d).U l) (φ.f l) = (t (Multiplicative.ofAdd α) : k) * valF x.left ((Φ.H d).U l) (φ.f l)) := by
  intro k _ Φ t
  have := Φ.D.i_hom
  let κ : kˣ →* Γ((Out.baseOver (Sp k)).left, ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom
  let e := splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k))
  let τ := e.symm (κ.comp t)
  have hτ : e τ = κ.comp t := e.apply_symm_apply _
  refine ⟨τ ≫ Φ.D.i, torus_comp_q Φ.D τ, fun n hn => ?_, fun d α φ hφ x l hx => ?_⟩
  · have : τ ^ n = 1 := by
      apply e.injective
      rw [map_pow, map_one, hτ]
      refine MonoidHom.ext fun χ => ?_
      have := DFunLike.congr_fun hn χ
      rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, this, map_one, MonoidHom.one_apply]
    rw [← MonObj.pow_comp, this, MonObj.one_comp]
  · have hx' := translate_le Φ.D τ x (Φ.N₀.U l) hx
    refine ⟨hx', ?_⟩
    have key := translate_pure Φ.D τ x (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α (φ.f l)
      (fun β hβ => by
        by_contra hne
        exact hβ (hφ ⟨l, hne⟩)) hx hx'
    rw [← splitTorusPointsEquiv_val] at key
    have hv : (splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k)) τ
        (Multiplicative.ofAdd α)).val =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (t (Multiplicative.ofAdd α) : k) := by
      change (e τ _).val = _
      rw [hτ]; rfl
    rw [hv] at key
    have key2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom key
    refine Eq.trans ?_ (Eq.trans key2 (Eq.trans ((map_mul _ _ _)) ?_))
    · exact dif_pos hx'
    · congr 1
      · exact Iso.inv_hom_id_apply _ _
      · symm
        exact dif_pos hx

end GlobalTheory.TorusTranslate
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem hilb_eq_finrank_quotPiece {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (quotPiece (MvPolynomial.vanishingIdeal k C) (d : ℤ)) := by
  rw [quotPiece_natCast]
  let ev : MvPolynomial J k →ₐ[k] (C → k) :=
    AlgHom.pi fun v : C => MvPolynomial.aeval v.1
  have hker : ∀ a ∈ MvPolynomial.vanishingIdeal k C, ev a = 0 := fun a ha =>
    funext fun v => ha v.1 v.2
  let φ := Ideal.Quotient.liftₐ (MvPolynomial.vanishingIdeal k C) ev hker
  have hφ : Function.Injective φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 fun v hv => congrFun (show ev x = 0 from hx) ⟨v, hv⟩
  rw [(Submodule.equivMapOfInjective _ hφ _).finrank_eq, ← Submodule.map_comp]
  rfl

theorem eval_eq_zero_of_hilb_le : (∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J] (C : Set (J → k)) (g N : ℕ), (MvPolynomial.vanishingIdeal k C).IsPrime → (MvPolynomial.vanishingIdeal k C).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) → (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k C) → ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k C) = (g + 1 : ℕ) → (∀ d, 1 ≤ d → hilb C d ≤ (N * d) ^ g) → ∀ v : J → k, (∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → Pf ∈ MvPolynomial.vanishingIdeal k C → MvPolynomial.eval v Pf = 0) → ∀ Pf ∈ MvPolynomial.vanishingIdeal k C, MvPolynomial.eval v Pf = 0) := by
  intro k _ _ J _ C g N hP hPh hne hdim hb v hv Pf hPf
  by_contra h0
  obtain ⟨d, hd, f, hf, hfd, hfv⟩ :=
    exists_form_degree_le_hilbertDegree_eval_ne_zero hPh hne v ⟨Pf, hPf, h0⟩
  refine hfv (hv d f (hd.trans ?_) hfd hf)
  have hH := isHilbertPoly_idealHilbertPoly hPh
  have hg : (idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).natDegree = g := by
    rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hPh hne] at hdim
    have := Nat.cast_injective hdim
    omega
  have h1 : 0 ≤ (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g -
      idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).coeff g := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le (Polynomial.degree_C_mul_X_pow_le _ _) ?_)
      exact Polynomial.degree_le_of_natDegree_le hg.le
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        Filter.eventually_ge_atTop 1] with n hn h1n
      have := hb n h1n
      rw [hilb_eq_finrank_quotPiece, mul_pow] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
        ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, _root_.mul_one,
    sub_nonneg] at h1
  have h2 := cast_hilbertDegree hPh
  rw [Polynomial.leadingCoeff, hg] at h2
  have h3 : (hilbertDegree (MvPolynomial.vanishingIdeal k C) : ℚ) ≤ (N : ℚ) ^ g * g.factorial := by
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  exact_mod_cast h3

end GlobalTheory.ZH
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

theorem toStk_valR_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valR x U a) = gs x z U a := by
  rw [valR, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem toStk_surjective {F : Type} [Field F] (y : Sp F) : Function.Surjective (toStk y) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp F).presheaf.exists_germ_eq s
  obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_mem (𝟙 (Sp F)) U y).2 hU)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom a, by simp [toStk]⟩

theorem crd_of_germs_unit : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (H : LB X) (H' : LB Y), H'.IsLB → ∀ (J : Type) (F : J → H.Sec) (σ : J → H'.Sec) (x : Sp k ⟶ X) (y : Sp k ⟶ Y), (∀ (z : Sp k) (l : H.ι) (l' : H'.ι), x z ∈ H.U l → y z ∈ H'.U l' → ∃ u : ((Sp k).presheaf.stalk z)ˣ, ∀ i, gs x z (H.U l) ((F i).f l) = u.val * gs y z (H'.U l') ((σ i).f l')) → ∀ v : J → k, GlobalTheory.ZH.Crd H F x v → GlobalTheory.ZH.Crd H' σ y v := by
  intro k _ X Y H H' hH' J F σ x y h v ⟨l, c, hl, hv⟩
  let z : Sp k := (⊥ : PrimeSpectrum k)
  obtain ⟨l', hl'⟩ := exists_chart hH' (y z)
  have hx := (top_le_iff_mem x _ z).1 hl
  obtain ⟨u, hu⟩ := h z l l' hx hl'
  obtain ⟨f, hf⟩ := toStk_surjective z u.val
  have f0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact u.ne_zero hf.symm
  refine ⟨l', c * Units.mk0 f f0, (top_le_iff_mem y _ z).2 hl', fun j => ?_⟩
  rw [hv j, Units.val_mul, Units.val_mk0, _root_.mul_assoc]
  congr 1
  apply (toStk z).injective
  rw [map_mul, toStk_valR_gs x _ z hx, toStk_valR_gs y _ z hl', hf, hu j]

end GlobalTheory.ZH.UFib
end
end
