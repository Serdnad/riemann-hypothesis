module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle313
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemiAbelianHomExtensionUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle072
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc.Sep
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx

section Chart

variable {Y Y' : Scheme.{0}}

theorem chartPull_le {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (p : B'.ι × A'.ι) : B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) :=
  fun _ hy => ⟨b.le _ hy.1, a.le _ hy.2⟩

def isoPull {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (w : LB.Iso A B) : LB.Iso A' B' :=
  ⟨fun p => res (chartPull_le a b p) (pullU h _ (w.s (b.idx p.1, a.idx p.2)))⟩

theorem gm_isoPull {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (w : LB.Iso A B) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (p : B'.ι × A'.ι) (hz : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((isoPull a b w).s p) =
      gm (r ≫ h) z (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) :=
  (gm_res r z (chartPull_le a b p) hz _).trans (gm_pull r h z _ (chartPull_le a b p hz) _)

theorem isoPull_isGen {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    (w : LB.Iso A B) (hw : w.IsGen) : (isoPull a b w).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ ((isoPull a b w).s p) =
        gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2)) (w.s (b.idx p.1, a.idx p.2)) := fun p hp =>
    (gm_isoPull a b w (𝟙 Y') y p hp).trans (by rw [Category.id_comp])
  have hm : h y ∈ B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2)) :=
    ⟨chartPull_le a b p hy.1, chartPull_le a b q hy.2⟩
  have e := congrArg (gm h y (B.U (b.idx p.1) ⊓ A.U (a.idx p.2) ⊓ (B.U (b.idx q.1) ⊓ A.U (a.idx q.2))))
    (hw (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B h y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2) hm) (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val p hy.1)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div A' B' (𝟙 Y') y p q hy).trans ?_)
    ((gm_res (𝟙 Y') y _ hy _).trans (val q hy.2)))
  rw [a.g y _ _ hy.1.2 hy.2.2, b.g y _ _ hy.1.1 hy.2.1]

end Chart

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Base

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Base

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Iso

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Iso

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Val

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Val

end GlobalTheory.PolDeg.TautFrom

namespace GlobalTheory.PolDeg.TautFrom

open GlobalTheory.PolDeg.TautEx GlobalTheory.PrimCocycle

section Main

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Main

end GlobalTheory.PolDeg.TautFrom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

namespace GlobalTheory.IsoFinExt

theorem isPullback_compare {X S L S' T : Scheme.{0}} (a : X ⟶ S) (b : L ⟶ S) (i : S' ⟶ S) (j : T ⟶ L)
    (l : T ⟶ S') (hc : l ≫ i = j ≫ b) :
    ∃ q : pullback (pullback.snd a b) j ⟶ pullback a i,
      q ≫ pullback.fst a i = pullback.fst _ _ ≫ pullback.fst a b ∧
      IsPullback q (pullback.snd _ _) (pullback.snd a i) l := by
  have hw : (pullback.fst (pullback.snd a b) j ≫ pullback.fst a b) ≫ a = (pullback.snd _ _ ≫ l) ≫ i := by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc, Category.assoc, hc]
  refine ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback a i)
  rw [pullback.lift_fst, hc]
  exact (IsPullback.of_hasPullback (pullback.snd a b) j).paste_horiz (IsPullback.of_hasPullback a b)

theorem isIso_of_compare {X₁ X₂ S L S' T : Scheme.{0}} (a₁ : X₁ ⟶ S) (a₂ : X₂ ⟶ S) (b : L ⟶ S) (i : S' ⟶ S)
    (j : T ⟶ L) (l : T ⟶ S') [Surjective l] [Flat l] [QuasiCompact l] (hc : l ≫ i = j ≫ b)
    (f : pullback a₁ b ⟶ pullback a₂ b) [IsIso f] (hf : f ≫ pullback.snd _ _ = pullback.snd _ _)
    (f' : pullback a₁ i ⟶ pullback a₂ i) (hf' : f' ≫ pullback.snd _ _ = pullback.snd _ _)
    (h : ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback a₁ b) (p' : Z ⟶ pullback a₁ i) (t : Z ⟶ T),
      p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ j →
      p' ≫ pullback.snd _ _ = t ≫ l → p ≫ f ≫ pullback.fst _ _ = p' ≫ f' ≫ pullback.fst _ _) :
    IsIso f' := by
  obtain ⟨q₁, e₁, H₁⟩ := isPullback_compare a₁ b i j l hc
  obtain ⟨q₂, e₂, H₂⟩ := isPullback_compare a₂ b i j l hc
  let F : pullback (pullback.snd a₁ b) j ⟶ pullback (pullback.snd a₂ b) j :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hf]) (by simp)
  have hF₁ : F ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f := pullback.lift_fst _ _ _
  have hF₂ : F ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hw : q₁ ≫ f' = F ≫ q₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, e₂, ← Category.assoc F, hF₁, Category.assoc]
      exact (h _ _ q₁ _ e₁.symm pullback.condition H₁.w).symm
    · rw [Category.assoc, Category.assoc, hf', H₂.w, ← Category.assoc, hF₂, H₁.w]
  have H : IsPullback q₁ F f' q₂ := by
    refine IsPullback.of_bot ?_ hw H₂
    rw [hF₂, hf']
    exact H₁
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q₂ :=
    ⟨⟨MorphismProperty.of_isPullback H₂.flip ‹Surjective l›,
      MorphismProperty.of_isPullback H₂.flip ‹Flat l›⟩,
      MorphismProperty.of_isPullback H₂.flip ‹QuasiCompact l›⟩
  have hF : IsIso F := inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
    H.flip hq hF

theorem exists_finite_iso : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (A₁ A₂ : Over (Sp K)) [GrpObj A₁] [GrpObj A₂], IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ (f : (Over.pullback (spMap β)).obj A₁ ≅ (Over.pullback (spMap β)).obj A₂), IsMonHom f.hom → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω : Type) (_ : Field Ω) (j : L →+* Ω) (l : K' →+* Ω) (φ : (Over.pullback (spMap io)).obj A₁ ≅ (Over.pullback (spMap io)).obj A₂), io.Finite ∧ l.comp io = j.comp β ∧ IsMonHom φ.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A₁.hom (spMap β)) (p' : Z ⟶ pullback A₁.hom (spMap io)) (t : Z ⟶ Sp Ω), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.hom.left ≫ pullback.fst _ _ = p' ≫ φ.hom.left ≫ pullback.fst _ _ := by
  intro K L _ _ _ β A₁ A₂ _ _ h₁ h₂ f hf
  obtain ⟨K', _, io, Ω, _, j, l, f', hfin, hc, hm, h⟩ := GlobalTheory.T.exists_finiteExt_abelianVarietyHom_descent K L β A₁ A₂ h₁ h₂ f.hom hf
  have hc' : spMap l ≫ spMap io = spMap j ≫ spMap β := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc]
  have : Flat (spMap l) := by
    rw [Flat.SpecMap_iff]
    letI := l.toAlgebra
    exact (inferInstance : Module.Flat K' Ω)
  have : Surjective (spMap l) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hl : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  have : IsIso f'.left :=
    @isIso_of_compare _ _ _ _ _ _ A₁.hom A₂.hom (spMap β) (spMap io) (spMap j) (spMap l) _ _ _ hc'
      f.hom.left hl (Over.w f.hom) f'.left (Over.w f') h
  have : IsIso ((Over.forget _).map f') := this
  have : IsIso f' := isIso_of_reflects_iso f' (Over.forget _)
  exact ⟨K', inferInstance, io, Ω, inferInstance, j, l, asIso f', hfin, hc, hm, h⟩

end GlobalTheory.IsoFinExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LBIsoEnd

def SelfPt {X : Scheme.{0}} (L : LB X) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : L.ι), f y ∈ L.U i → gm f y (L.U i ⊓ L.U i) (L.g i i) = 1

theorem selfPt_of_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : SelfPt L :=
  fun _ f y _ hi => gm_self hL f y hi

theorem selfPt_of_lbIso {X : Scheme.{0}} {B P : LB X} (hB : B.IsLB) (H : LBIso B P) : SelfPt P := by
  intro Y f y k hk
  obtain ⟨w, hw⟩ := H
  obtain ⟨i, hi⟩ := exists_chart hB (f y)
  have hm : f y ∈ P.U k ⊓ B.U i ⊓ (P.U k ⊓ B.U i) := ⟨⟨hk, hi⟩, hk, hi⟩
  have e := congrArg (gm f y (P.U k ⊓ B.U i ⊓ (P.U k ⊓ B.U i))) (hw (k, i) (k, i))
  have e' := (gm_res f y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div B P f y (k, i) (k, i) hm) (gm_res f y _ hm _))))
  rw [gm_self hB f y hi, inv_one, _root_.mul_one] at e'
  exact _root_.mul_eq_right.1 e'.symm

section Tri

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem indep_comp' (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w')
    (hL : SelfPt L) (hL'' : SelfPt L'') {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have a := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have b := hw' Y f y i i' k k hi hi' hk hk
  rw [hL Y ((f ≫ F') ≫ F) y j hj] at a
  rw [hL'' Y f y k hk] at b
  rw [a, b]
  generalize gm (f ≫ F') y _ (L'.g i i') = B
  generalize gw w (f ≫ F') y j i' = C
  generalize gw w' f y i' k = D
  rw [_root_.one_mul, inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, _root_.inv_mul_cancel, _root_.one_mul]

theorem exists_comp' (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL : SelfPt L) (hL'' : SelfPt L'') :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have glue : ∀ (j : L.ι) (k : L''.ι), ∃ s : Γ(X'', (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i → f y ∈ L''.U k →
        gm f y _ s = gw w (f ≫ F') y j i * gw w' f y i k := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : L'.ι → X''.Opens, ∀ i x, x ∈ W i ↔ F (F' x) ∈ L.U j ∧ F' x ∈ L'.U i ∧ x ∈ L''.U k :=
      ⟨fun i => F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull₂.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.2⟩
    have l₁ : ∀ i, W i ≤ F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) := fun i x hx =>
      ⟨mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
    have l₂ : ∀ i, W i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull.2 ((hW i x).1 hx).2.1, ((hW i x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X'', W i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), f y ∈ W i →
        gm f y (W i) (u i) = gw w (f ≫ F') y j i * gw w' f y i k :=
      ⟨fun i => res (l₁ i) (pullU F' _ (w.s (fun _ => j, i))) * res (l₂ i) (w'.s (fun _ => i, k)), fun Y f y i hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ i) hy _).trans (gm_pull f F' y _ (l₁ i hy) _)) (gm_res f y (l₂ i) hy _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hW i x).2 ⟨mem_pull₂.1 hx.1, hi, hx.2⟩⟩) u (fun i i' x hx => by
        have h₁ := (hW i x).1 hx.1
        have h₂ := (hW i' x).1 hx.2
        exact (hu _ (𝟙 X'') x i hx.1).trans ((indep_comp' w w' hw hw' hL hL'' (𝟙 X'') x j i i' k h₁.1 h₁.2.1 h₂.2.1
          h₁.2.2).trans (hu _ (𝟙 X'') x i' hx.2).symm))
    refine ⟨s, fun Y f y i hj hi hk => ?_⟩
    have hy := (hW i (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ i) hy s).symm.trans ((congrArg (gm f y (W i)) (hs i)).trans (hu Y f y i hy))
  choose s hs using glue
  exact ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, fun Y f y j i k hj hi hk => hs j k Y f y i hj hi hk⟩

end Tri

theorem lbIso_trans_of_selfPt {X : Scheme.{0}} {A B C : LB X} (hA : SelfPt A) (hB : B.IsLB) (hC : SelfPt C)
    (H : LBIso A B) (H' : LBIso B C) : LBIso A C := by
  obtain ⟨w', h'⟩ := H.chartPull (chartPullId A) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w, h⟩ := H'.chartPull (chartPullId B) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull C (𝟙 X) (𝟙 X) rfl)
  obtain ⟨w'', T⟩ := exists_comp' hB w w' ((isGen_iff w).1 h) ((isGen_iff w').1 h') hC hA
  exact LBIso.chartPull (chartPullId A) (chartPullUnpull C _ (Category.id_comp _))
    ⟨w'', (isGen_iff w'').2 (T.pgen_comp hB ((isGen_iff w).1 h) ((isGen_iff w').1 h'))⟩

theorem lbIso_trans_end : ∀ (X : Scheme.{0}) (A B P : LB X), A.IsLB → B.IsLB → LBIso A B → LBIso P B → LBIso A P :=
  fun _ _ _ _ hA hB H H' =>
    lbIso_trans_of_selfPt (selfPt_of_isLB hA) hB (selfPt_of_lbIso hB H'.symm) H H'.symm

end GlobalTheory.LBIsoEnd
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unimodLattice_bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) :
    H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem unimodLattice_bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.bar H.rt = -H.rt := by
  apply RingOfIntegers.ext
  rw [H.bar_eq]
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using this
  have hd : (7 : ℝ) ≤ H.d := by
    have := H.d_mod
    have : 7 ≤ H.d := by omega
    exact_mod_cast this
  set z := φ (H.rt : E) with hz
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have hx : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 hm with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg z.re]
  have key : starRingEnd ℂ z = -z := by apply Complex.ext <;> simp [hx]
  rw [hz] at key
  simpa using key

theorem unimodLattice_w0_add {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have h1 := H.two_weight_eq_one_add_root
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar h1
    rw [map_mul, map_add (f := _), map_one, unimodLattice_bar_rt, map_ofNat] at this
    rw [this]; ring
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h1, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

theorem unimodLattice :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit (W + W.transpose).det ∧ (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) ∧ W = (W + W.transpose) * ρ H.w0 := by
  intro E _ _ _ H
  obtain ⟨m, B0, ρ0, hm, hsym, hpd, hadj⟩ := GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef E H
  obtain ⟨r, b, ρ, hr, hbs, hbpd, hbu, hbadj⟩ :=
    GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) (unimodLattice_bar_bar H) m B0 ρ0 hm hsym hpd hadj
  have hW : b * ρ H.w0 + (b * ρ H.w0).transpose = b := by
    rw [Matrix.transpose_mul, hbs, hbadj, ← Matrix.mul_add, ← map_add (f := _)]
    erw [unimodLattice_w0_add H]
    rw [map_one, Matrix.mul_one]
  refine ⟨r, b * ρ H.w0, ρ, hr, ?_, ?_, ?_, ?_⟩
  · rw [hW]; exact hbpd
  · rw [hW]; exact hbu
  · intro a; rw [hW]; exact hbadj a
  · rw [hW]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilDomain

theorem appTop_spMap_inv {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (a : A) :
    (spMap g).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (g a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm

theorem weilIs_of_fractionField : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (e : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ Over.mk (spMap f)), e.left = spMap (algebraMap W L) → ∀ (n : ℕ) (x y : Over.mk (spMap f) ⟶ P.A), x ^ n = 1 → y ^ n = 1 → ∀ (w : Wˣ), Out.WeilIs P.A P.L n (e ≫ x) (e ≫ y) (unitOn (Units.map (algebraMap W L).toMonoidHom w)) → Out.WeilIs P.A P.L n x y (unitOn w) := by
  intro R _ _ P W L _ _ _ _ _ f e he n x y hx hy w H
  have hL := (GlobalTheory.firstFiveLaws).1
  obtain ⟨c, hc, -⟩ := (hL.weil _ P n (Over.mk (spMap f))).1 x y hx hy
  have H' := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB e hc
  have hu := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H' H
  have hinj : Function.Injective e.left.appTop.hom := by
    rw [he]
    intro a b hab
    have ia := CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of W)) a
    have ib := CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of W)) b
    rw [← ia, ← ib, appTop_spMap_inv, appTop_spMap_inv] at hab
    have h1 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).1 hab
    have h2 := IsFractionRing.injective W L h1
    rw [← ia, ← ib, h2]
  have hc' : c = unitOn w := by
    apply Units.ext
    apply hinj
    have := congrArg Units.val hu
    refine this.trans ?_
    show (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom (algebraMap W L w) = _
    rw [he]
    exact (appTop_spMap_inv (algebraMap W L) (w : W)).symm
  exact hc' ▸ hc

end GlobalTheory.WeilDomain
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.semiAbelian_hom_extends_at_stalk_agreeing_on_open : ∀ {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f → ∀ (s : S) [IsDomain (S.presheaf.stalk s)] [IsNoetherianRing (S.presheaf.stalk s)] [IsIntegrallyClosed (S.presheaf.stalk s)] (k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U), k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s → ∃ g : pullback G.hom (S.fromSpecStalk s) ⟶ H.left, g ≫ H.hom = pullback.fst G.hom (S.fromSpecStalk s) ≫ G.hom ∧ GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom (S.fromSpecStalk s)) g := by
  first | exact @GlobalTheory.StalkExt.exists_agree_at_stalk | exact GlobalTheory.StalkExt.exists_agree_at_stalk | (intros; apply GlobalTheory.StalkExt.exists_agree_at_stalk <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.isIso_of_proper_isIso_on_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (T X : Scheme.{0}) (φ : T ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)), IsProper φ → IsProper f → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (c : ∀ e, (Y e).left ⟶ T), (∀ e, IsPullback (c e) (Y e).hom (φ ≫ f) (thick R I e)) → (∀ e, IsPullback (c e ≫ φ) (Y e).hom f (thick R I e)) → IsIso φ := by
  first | exact @GlobalTheory.FormalAlg.isIso_of_isIso_reductions | exact GlobalTheory.FormalAlg.isIso_of_isIso_reductions | (intros; apply GlobalTheory.FormalAlg.isIso_of_isIso_reductions <;> assumption)
end
