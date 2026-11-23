module

public import Development.EtaleCohomology.EtaleSheaves.Bundle058
public import Development.EtaleCohomology.EtaleSheaves.Bundle034
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Development.EtaleCohomology.EtaleSheaves.Bundle059
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafConsPfB
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafConsPfA

theorem rpl_congr (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') {u u2 : U' ⟶ U} {e e2 : E' ⟶ E}
    (hu : u = u2) (he : e = e2) (c : f' ≫ e = u ≫ f) (c2 : f' ≫ e2 = u2 ≫ f) (n : ℤ) (y) :
    rpl q i f f' u e c n y = rpl q i f f' u2 e2 c2 n y := by
  subst hu he; rfl

instance (B : Scheme.{0}) : IsIso (top B).hom := by show IsIso (Iso.refl B).hom; infer_instance

abbrev uT {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) :
    pullback (pullback.snd p (top B).hom ≫ (top B).hom) ι ⟶ pullback p ι :=
  pullback.map _ ι p ι (pullback.fst p (top B).hom) (𝟙 W) (𝟙 B) (by rw [Category.comp_id, pullback.condition]) (by simp)

theorem uT_comm {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) :
    prU p ι (top B) ≫ pullback.fst p (top B).hom = uT p ι ≫ pullback.fst p ι := (pullback.lift_fst _ _ _).symm

instance {Y B : Scheme.{0}} (p : Y ⟶ B) : IsIso (pullback.fst p (top B).hom) := by infer_instance
instance {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) : IsIso (uT p ι) := by infer_instance

theorem rpl_comp' (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (n : ℤ) (y) :
    rpl q i f' f'' u' e' c' n (rpl q i f f' u e c n y) =
      rpl q i f f'' (u' ≫ u) (e' ≫ e) (by rw [← Category.assoc, c', Category.assoc, c, Category.assoc]) n y :=
  (rpl_comp q i f f' f'' u e u' e' c c' _ n y).symm

abbrev TT (q : ℕ) (i : ℤ) {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (n : ℤ) :=
  rpl q i (pullback.fst p ι) (prU p ι (top B)) (uT p ι) (pullback.fst p (top B).hom) (uT_comm p ι) n

abbrev TL (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) (n : ℤ) :=
  rpl q i ι (prB ι (top B)) (pullback.snd (top B).hom ι) (top B).hom pullback.condition n


theorem L1 {B Y0 Y1 Y2 : Scheme.{0}} (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) :
    pullback.fst (g2 ≫ g1 ≫ p) (top B).hom ≫ g2 ≫ g1 =
      mY (g1 ≫ p) g2 (top B) ≫ mY p g1 (top B) ≫ pullback.fst p (top B).hom := by
  simp only [mY, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]


theorem L3 {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) :
    uT p ι ≫ pullback.snd p ι = toBW p ι (top B) ≫ pullback.snd (top B).hom ι := by
  simp only [uT, toBW, pullback.map]
  erw [pullback.lift_snd, pullback.lift_snd]


theorem L2 {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) :
    uT (g2 ≫ g1 ≫ p) ι ≫ pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp) =
      mW (g1 ≫ p) g2 ι (top B) ≫ mW p g1 ι (top B) ≫ uT p ι := by
  apply pullback.hom_ext
  · have := L1 p g1 g2
    simp only [mY] at this
    simp only [uT, mW, mY, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.map]
  · simp only [uT, mW, mY, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map]
    simp

theorem LeafGlob_pf : LateralTheory.E.LeafConsPf.LeafGlob := by
  intro q _ i B W Y0 Y1 Y2 ι _ p g1 g2 K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  refine ⟨fun n y => l0 (top B) n (TT q i p ι n y), fun n y => l2 (top B) n (TT q i (g2 ≫ g1 ≫ p) ι n y),
    fun n c => lL (top B) n (TL q i ι n c), ?_, ?_, ?_, ?_⟩
  · intro n
    exact (r2.1 _ n).1.comp (rpl_bij _ _ _ _ _ _ _ _).1
  · intro n
    exact (rL.1 _ n).2.comp (rpl_bij _ _ _ _ _ _ _ _).2
  · intro n y
    have h1 := mf (top B) n (TT q i p ι n y)
    have h2 := mg (top B) n (rpl q i (prU p ι (top B)) (prU (g1 ≫ p) ι (top B)) (mW p g1 ι (top B)) (mY p g1 (top B))
      (pullback.lift_fst _ _ _).symm n (TT q i p ι n y))
    show l2 (top B) n _ = l0 (top B) n (TT q i p ι n y) ≫ (shiftFunctor _ n).map (f ≫ g)
    rw [Functor.map_comp]
    refine Eq.trans ?_ (Category.assoc _ _ _)
    rw [← h1, ← h2]
    refine congrArg (l2 (top B) n) ?_
    rw [rpl_comp', rpl_comp', rpl_comp']
    apply rpl_congr
    · simpa only [Category.assoc] using L2 ι p g1 g2
    · simpa only [Category.assoc] using L1 p g1 g2
  · intro n c
    have h := mℓ (top B) n (TL q i ι n c)
    refine Eq.trans ?_ h
    refine congrArg (l2 (top B) n) ?_
    rw [rpl_comp', rpl_comp']
    apply rpl_congr
    · simpa only [Category.assoc] using L3 (g2 ≫ g1 ≫ p) ι
    · simp only [toBY]; exact pullback.condition

end LateralTheory.E.LeafConsPfB
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.HasLimPf

theorem hasLimit_of_affine {K : Type} [SmallCategory K] (F : K ⥤ Scheme.{0}) (hF : ∀ k, IsAffine (F.obj k)) :
    HasLimit F := by
  have : HasLimit (F ⋙ Scheme.Γ.rightOp) := inferInstance
  have : PreservesLimitsOfSize.{0, 0} Scheme.Spec.{0} := ΓSpec.adjunction.rightAdjoint_preservesLimits
  have : HasLimit (F ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec) :=
    HasLimit.mk ⟨_, isLimitOfPreserves Scheme.Spec (limit.isLimit (F ⋙ Scheme.Γ.rightOp))⟩
  have : ∀ k, IsIso ((Functor.whiskerLeft F ΓSpec.adjunction.unit).app k) := fun k => by
    have := hF k
    dsimp; infer_instance
  have : IsIso (Functor.whiskerLeft F ΓSpec.adjunction.unit) := NatIso.isIso_of_isIso_app _
  exact hasLimit_of_iso (asIso (Functor.whiskerLeft F ΓSpec.adjunction.unit)).symm

def Loc : Prop := ∀ {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (j₀ : J),
  (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) →
  (∀ U : (D.obj j₀).Opens, IsAffineOpen U → HasLimit (opensDiagram D j₀ U)) → HasLimit (Over.forget j₀ ⋙ D)

theorem HasLim_of (hL : Loc) : LateralTheory.E.SysPf.HasLim := by
  intro J _ _ D hD
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  have : HasLimit (Over.forget j₀ ⋙ D) := hL D j₀ hD (fun U hU => by
    refine hasLimit_of_affine _ (fun j => ?_)
    have := hD j.hom
    exact hU.preimage (D.map j.hom))
  have : HasLimit D := Functor.Initial.hasLimit_of_comp (Over.forget j₀)
  exact ⟨limit.cone D, ⟨limit.isLimit D⟩⟩

end LateralTheory.E.HasLimPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafVanBPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev bpl (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) (m : ℤ) :=
  rpl q i (prB ι U) (pullback.fst (t ≫ U.hom) ι)
    (pullback.map (t ≫ U.hom) ι U.hom ι t (𝟙 W) (𝟙 B) (by simp) (by simp)) t (pullback.lift_fst _ _ _).symm m

def LeafVanBStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ U.left), SH A → IsUnit (q : A) → bpl q i ι U t m c = 0) →
  Cov U (fun _ a => rB q i ι a m c = 0)

def LeafRelVanOfH : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  Subsingleton (H R E F n) → Function.Surjective (pull R f F (n - 1)) → Subsingleton (Hrel R f F n)

theorem relVanOfH : LeafRelVanOfH := by
  intro R _ F U E f n hE hs
  suffices h : ∀ y : Hrel R f F n, y = 0 from ⟨fun y₁ y₂ => by rw [h y₁, h y₂]⟩
  intro y
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  set φ := (chains R).map f with hφ
  let a : Cocycle ((chains R).obj E) (res R F) n := zcomp (Cocycle.ofHom (mappingCone.inr φ)) z (zero_add n)
  have ha : CohomologyClass.mk a = 0 := hE.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at ha
  obtain ⟨α, hα⟩ := ha
  let b : Cochain ((chains R).obj U) (res R F) (n - 1) := (mappingCone.inl φ).comp z.1 (by omega)
  have hz : z.1 = mappingCone.descCochain φ b a.1 (by omega) := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    simp [b, a, zcomp, mappingCone.inl_descCochain, mappingCone.inr_descCochain]
  have h0 : δ n (n + 1) z.1 = 0 := Cocycle.δ_eq_zero z (n + 1)
  rw [hz, mappingCone.δ_descCochain _ _ _ _ (n + 1) rfl] at h0
  have h1 := congrArg (fun x => (mappingCone.inl φ).comp x (show -1 + (n + 1) = n by omega)) h0
  simp only [Cochain.comp_add, Cochain.comp_zero, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, add_zero] at h1
  have hδα : δ (n - 1) n α = a.1 := hα
  let b' : Cochain ((chains R).obj U) (res R F) (n - 1) :=
    b - n.negOnePow • (Cochain.ofHom φ).comp α (zero_add _)
  have hb' : δ (n - 1) n b' = 0 := by
    have e1 : δ (n - 1) n b = -((n + 1).negOnePow • (Cochain.ofHom φ).comp a.1 (zero_add n)) := eq_neg_of_add_eq_zero_left h1
    simp only [b', δ_sub, δ_units_smul, e1, Int.negOnePow_succ]
    simp
    rw [hδα, sub_self]
  obtain ⟨g, hg⟩ := hs (CohomologyClass.mk (Cocycle.mk b' n (by omega) hb'))
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective g
  have hg' : CohomologyClass.mk (Cocycle.mk b' n (by omega) hb' - zcomp (Cocycle.ofHom φ) γ (zero_add _)) = 0 := by
    rw [CohomologyClass.mk_sub, ← hg]; exact sub_eq_zero.mpr rfl
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 2) (by omega)] at hg'
  obtain ⟨ε, hε⟩ := hg'
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨mappingCone.descCochain φ ε (α + n.negOnePow • γ.1) (by omega), ?_⟩
  have hε' : δ (n - 2) (n - 1) ε = b' - (Cochain.ofHom φ).comp γ.1 (zero_add _) := hε
  have hX : δ (n - 2) (n - 1) ε + n.negOnePow • (Cochain.ofHom φ).comp (α + n.negOnePow • γ.1) (zero_add _) = b := by
    rw [hε']
    simp only [b', Cochain.comp_add, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul]
    abel
  have hY : δ (n - 1) n (α + n.negOnePow • γ.1) = a.1 := by
    rw [δ_add, δ_units_smul, hδα, Cocycle.δ_eq_zero γ n, smul_zero, add_zero]
  rw [mappingCone.δ_descCochain _ _ _ _ n (by omega), hX, hY, hz]
  rfl

def LeafClosedSH : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  (∀ n : ℤ, 0 < n → Subsingleton (H (ZMod q) (sch.obj W') (tw q i) n)) ∧
  Function.Surjective (pull (ZMod q) (sch.map ι') (tw q i) 0)

def LeafClosedSHPos : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A →
  IsUnit (q : A) → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  ∀ n : ℤ, 0 < n → Subsingleton (H (ZMod q) (sch.obj W') (tw q i) n)

def LeafClosedSH0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A →
  IsUnit (q : A) → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  Function.Surjective (pull (ZMod q) (sch.map ι') (tw q i) 0)

theorem closedSH_of (h1 : LeafClosedSHPos) (h2 : LeafClosedSH0) : LeafClosedSH :=
  fun hy q _ i A _ _ hA hq _ ι' _ => ⟨h1 hy q i A hA hq ι', h2 hy q i A hA hq ι'⟩

theorem heightFunctionalStatement_of_pairingProperties (hy : Hyps) : B2 := hy.2.2.2.2.2.2.2.2.2.2.2.1

theorem vanBPt (hC : LeafClosedSH) (hy : Hyps) (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A]
    [IsLocalRing A] (hA : SH A) (hq : IsUnit (q : A)) {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'] (m : ℤ)
    (hm : 0 < m) : Subsingleton (Hrel (ZMod q) (sch.map ι') (tw q i) m) := by
  obtain ⟨hW, hs⟩ := hC hy q i A hA hq ι'
  refine relVanOfH (ZMod q) (tw q i) (sch.map ι') m (heightFunctionalStatement_of_pairingProperties hy (ZMod q) A hA (tw q i) m hm) ?_
  rcases eq_or_lt_of_le (show (1 : ℤ) ≤ m by omega) with h | h
  · subst h; simpa using hs
  · have := hW (m - 1) (by omega)
    intro y; exact ⟨0, Subsingleton.elim _ _⟩

theorem LeafVanB_of (hS : LeafVanBStalk) (hP : LeafClosedSHPos) (h0 : LeafClosedSH0) : LeafVanB := by
  have hC := closedSH_of hP h0
  intro hy q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV p g1 g2 h1 h2 h3 hsh U m hm c
  exact hS hy q k hq i s ι U m c (fun A _ _ t hA hqA =>
    (vanBPt hC hy q i A hA hqA (pullback.fst (t ≫ U.hom) ι) m hm).elim _ _)

end LateralTheory.E.LeafVanBPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafInj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_pts {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop}
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧
      Cov U' (fun U'' b => P U'' (b ≫ a))) : Cov U P := by
  choose U' a y hy hC using h
  choose T hT hP using hC
  let R : Sieve U :=
    { arrows := fun {Z} g => ∃ x, ∃ b : Z ⟶ U' x, T x b ∧ g = b ≫ a x
      downward_closed := by
        rintro Z W g ⟨x, b, hb, rfl⟩ h
        exact ⟨x, h ≫ b, (T x).downward_closed hb h, by simp⟩ }
  refine ⟨R, ?_, ?_⟩
  · have h0 : Sieve.ofArrows U' a ∈ (EtTop B) U := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      ext z
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨z, y z, hy z⟩
    refine (EtTop B).transitive h0 R ?_
    intro Z f hf
    obtain ⟨W, g, f', hf', rfl⟩ := hf
    cases hf' with
    | mk x =>
      refine (EtTop B).superset_covering ?_ ((EtTop B).pullback_stable g (hT x))
      intro V c hc
      exact ⟨x, c ≫ g, hc, by simp⟩
  · rintro Z g ⟨x, b, hb, rfl⟩
    exact hP x Z b hb

def LeafInj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

def LeafInj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  ∀ x : U.left, U.hom x ∉ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

theorem LeafInj0_of (hW : LeafInj0W) (hV : LeafInj0V) : LateralTheory.E.LeafDegCut.LeafInj0 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp1 hp2 hp3 hS U c hc
  apply cov_of_pts
  intro x
  by_cases hx : U.hom x ∈ Set.range ι
  · exact hW hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c x hx
  · exact hV hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c hc x hx
end LateralTheory.E.LeafInj0Pf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSurj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_points {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop)
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
      ∀ (U'' : B.Etale) (b : U'' ⟶ U'), P U'' (b ≫ a)) : Cov U P := by
  choose Z f hx hP using h
  refine ⟨Sieve.ofArrows Z f, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hx x⟩
  · rintro U' a ⟨Y, b, g, ⟨j⟩, rfl⟩
    exact hP j U' b

def LeafSurj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y = 0

def LeafSurj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ V → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), ∃ c : Hrel (ZMod q) (sch.map (prB ι U'')) (tw q i) 0,
      bY q i (g2 ≫ g1 ≫ p) ι U'' 0 c = rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y

theorem LeafSurj0_of (hW : LeafSurj0W) (hV : LeafSurj0V) : LateralTheory.E.LeafDegCut.LeafSurj0 := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hVW p g1 g2 h0 h1 h2 hS U y
  refine cov_of_points U _ fun x => ?_
  by_cases hx : U.hom x ∈ V
  · exact hV hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hx
  · have hxW : U.hom x ∈ Set.range ι := by
      have : U.hom x ∉ (V : Set B) := hx
      rw [hVW] at this
      simpa using this
    obtain ⟨U', a, hxa, hz⟩ := hW hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hxW
    exact ⟨U', a, hxa, fun U'' b' => ⟨0, by rw [map_zero, hz U'' b']⟩⟩

end LateralTheory.E.LeafSurj0Pf
end
end

section

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafNegPf

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  change IsZero ((((chainsN R).obj E).extend ComplexShape.embeddingDownNat).X n)
  apply HomologicalComplex.isZero_extend_X
  intro i
  change -(i : ℤ) ≠ n
  omega

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) :
    IsZero ((res R F).X n) := by
  unfold res
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)

theorem cone_isZero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (p : ℤ) (hp : 0 < p) :
    IsZero ((mappingCone ((chains R).map f)).X p) := by
  rw [IsZero.iff_id_eq_zero]
  apply mappingCone.ext_from _ (p + 1) p rfl
  · exact (chains_isZero R U (p + 1) (by omega)).eq_of_src _ _
  · exact (chains_isZero R E p hp).eq_of_src _ _

theorem cochain_eq_zero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ) (hm : m < 0)
    (z : Cochain (mappingCone ((chains R).map f)) (res R F) m) : z = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hq : q < 0
  · exact (res_isZero R F q hq).eq_of_tgt _ _
  · exact (cone_isZero R f p (by omega)).eq_of_src _ _

theorem LeafNeg_of : LateralTheory.E.LeafDegCut.LeafNeg := by
  intro R _ U E f F m hm
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective b
  have hx : x = y := by
    ext1
    rw [cochain_eq_zero R f F m hm (x : Cochain _ _ m), cochain_eq_zero R f F m hm (y : Cochain _ _ m)]
  rw [hx]

end LateralTheory.E.LeafNegPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafVan0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev prS {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (s : S ⟶ B) : pullback (pullback.snd p s ≫ s) ι ⟶ pullback p s :=
  pullback.fst _ _

def LeafVanStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A →
    Subsingleton (Hrel (ZMod q) (sch.map (prS p ι (t ≫ U.hom))) (tw q i) m)) →
  ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m, Cov U (fun U' a => rY q i p ι a m y = 0)

def LeafVanW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (A : Type) [CommRing A] (s : Sp A ⟶ B), SH A → (∃ x : Sp A, (∀ z : Sp A, z ⤳ x) ∧ s x ∈ Set.range ι) →
  ∀ m : ℤ, Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

def LeafVanV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y S : Scheme.{0}} (ι : W ⟶ B) (p : Y ⟶ B) (s : S ⟶ B),
  (∀ x : S, s x ∉ Set.range ι) → ∀ m : ℤ, Subsingleton (Ht q (sch.obj (pullback p s)) m i) →
  Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

theorem LeafVan0_of (hS : LeafVanStalk) (hW : LeafVanW) (hV : LeafVanV) : LeafVan0 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV' p g1 g2 hp _ _ hSHV U m hm y
  refine hS hH q k hq i b ι p hp U m ?_ y
  intro A _ t hA
  obtain ⟨hHen, _⟩ := hA
  by_cases hx : (t ≫ U.hom) (IsLocalRing.closedPoint A) ∈ Set.range ι
  · exact hW hH q k hq i b ι p hp A (t ≫ U.hom) ⟨hHen, ‹_›⟩
      ⟨IsLocalRing.closedPoint A, fun z => IsLocalRing.specializes_closedPoint z, hx⟩ m
  · have hall : ∀ z : Sp A, (t ≫ U.hom) z ∈ (V : Set B) := by
      intro z
      have hz : (t ≫ U.hom) z ⤳ (t ≫ U.hom) (IsLocalRing.closedPoint A) :=
        (IsLocalRing.specializes_closedPoint z).map (t ≫ U.hom).continuous
      have hxV : (t ≫ U.hom) (IsLocalRing.closedPoint A) ∈ (V : Set B) := by rw [hV']; exact hx
      exact hz.mem_open V.isOpen hxV
    have hrange : Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B) := by rintro _ ⟨z, rfl⟩; exact hall z
    have hmiss : ∀ z : Sp A, (t ≫ U.hom) z ∉ Set.range ι := by
      intro z hz; have := hall z; rw [hV'] at this; exact this hz
    exact hV hH q i ι p (t ≫ U.hom) hmiss m ((hSHV A (t ≫ U.hom) ⟨hHen, ‹_›⟩ hrange).1 m (by omega))

end LateralTheory.E.LeafVan0Pf
end
end
