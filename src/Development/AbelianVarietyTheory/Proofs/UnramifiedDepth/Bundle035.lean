module

public import ReciprocityTheory.DualLattices.Bundle019
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma map_sub' {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (a' : Fin m → Fin d → PS S n e) (h : ∀ i j, MvPowerSeries.map β (a i j) = a' i j) :
    MvPowerSeries.map β (sub a f) = sub a' (MvPowerSeries.map β f) := by
  unfold sub
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2) (fun q => ha q.1 q.2))]
  simp only [h]

private lemma cc_sub {R : Type} [CommRing R] {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub a f) = 0 := by
  unfold sub
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
      (fun q => ha q.1 q.2)) (fun q => ha q.1 q.2) hf

private lemma ev_eq {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Fin d → PS R n d) (f : PS R m d) :
    ev a f = sub a f := rfl

private lemma map_pt {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.map β (pt R d j i) = pt S d j i := by simp [pt]

private lemma cc_pt {R : Type} [CommRing R] {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (pt R d j i) = 0 := by simp [pt]

private lemma map_subst_single {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d) :
    MvPowerSeries.map β (sub ![x] f) =
      sub ![fun j => MvPowerSeries.map β (x j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by fin_cases i; exact hx j) f _ (fun i j => by fin_cases i; rfl)

private lemma map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d) :
    MvPowerSeries.map β (sub ![x, y] f) =
      sub ![fun j => MvPowerSeries.map β (x j), fun j => MvPowerSeries.map β (y j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f _ (fun i j => by fin_cases i <;> rfl)

private lemma constCoeff_subst_single {R : Type} [CommRing R] {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x] f) = 0 :=
  cc_sub _ (fun i j => by fin_cases i; exact hx j) f hf

private lemma constantCoeff_sub2_eq_zero {R : Type} [CommRing R] {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x, y] f) = 0 :=
  cc_sub _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f hf

private lemma isHomF_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ}
    (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (φ : Fin e → PS R 1 d)
    (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0) (h : IsHomF F F' φ) :
    IsHomF (fun j => MvPowerSeries.map β (F j)) (fun j => MvPowerSeries.map β (F' j))
      (fun j => MvPowerSeries.map β (φ j)) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun j => by simp [MvPowerSeries.constantCoeff_map, h0], fun j => ?_⟩
  have := congrArg (MvPowerSeries.map β) (h1 j)
  simp only [ev_eq] at this ⊢
  rw [map_subst_single β _ hF, map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))
    (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))] at this
  simp only [map_subst_single β _ (cc_pt _), map_pt] at this
  exact this

private lemma lin_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ} (φ : Fin e → PS R 1 d) :
    lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β := by
  ext i j
  simp [lin, MvPowerSeries.coeff_map]

private noncomputable def mapLaw {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d : ℕ} (F : FGLaw R d) :
    FGLaw S d where
  F := F.mapF β
  const i := by simp [FGLaw.mapF, MvPowerSeries.constantCoeff_map, F.const]
  unit i := by
    have := congrArg (MvPowerSeries.map β) (F.unit i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun _ => by simp) (cc_pt _)] at this
    simp only [map_pt, Pi.zero_apply, map_zero, MvPowerSeries.map_X] at this
    exact this
  comm i := by
    have := congrArg (MvPowerSeries.map β) (F.comm i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _)] at this
    simp only [map_pt] at this
    exact this
  assoc i := by
    have := congrArg (MvPowerSeries.map β) (F.assoc i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l)) (cc_pt _),
      map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l))] at this
    simp only [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _), map_pt] at this
    exact this

theorem changeCoeff_law_lin_extSer : ∀ (R S : Type) [CommRing R] [CommRing S] (β : R →+* S), (∀ (d : ℕ) (F : FGLaw R d), ∃ F' : FGLaw S d, F'.F = F.mapF β) ∧ (∀ (d e : ℕ) (φ : Fin e → PS R 1 d), lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β) ∧ ∀ (d g r : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q → ExtSer (F.mapF β) (FB.mapF β) (fun j => MvPowerSeries.map β (J j)) (fun j => MvPowerSeries.map β (Q j)) := by
  intro R S _ _ β
  refine ⟨fun d F => ⟨mapLaw β F, rfl⟩, fun d e φ => lin_map β φ, fun d g r F FB J Q h => ⟨?_, ?_, ?_⟩⟩
  · have hg : (fun j => MvPowerSeries.map β (gmF R r j)) = gmF S r := by
      funext j; simp [gmF]
    rw [← hg]
    exact isHomF_map β _ _ _ (fun j => by simp [gmF]) h.homI
  · exact isHomF_map β _ _ _ F.const h.homQ
  · rw [lin_map, lin_map]
    obtain ⟨h0, A', B', h1, h2, h3⟩ := h.exact
    refine ⟨?_, A'.map β, B'.map β, ?_, ?_, ?_⟩
    · rw [← Matrix.map_mul, h0]; simp
    · rw [← Matrix.map_mul, h1]; simp
    · rw [← Matrix.map_mul, h2]; simp
    · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add β), h3]; simp

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem appTop_charUnit_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : Out.TorusEndOf X h t) (χ : X) :
    t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, ht χ]

theorem qRel_iRel_equivariant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G), ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (k : ℕ) (a : OE) (S : Type) [CommRing S] [Algebra R S], (∀ z y, QRel (U.gt k) S z y → QRel (U.gt k) S (z ≫ io.act a) (y ≫ oD.onB.act a)) ∧ ∀ χ χ' z, (∀ x, χ' (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd (star a • x))) → IRel (U.gt k) S χ z → IRel (U.gt k) S χ' (z ≫ io.act a) := by
  intro R _ _ I D A G _ _ U OE _ _ _ io oD oA hl k a S _ _
  have hG : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (Out.fstG I k G).left =
      (Out.fstG I k G).left ≫ (io.act a).left :=
    GlobalTheory.SplitTorusPoints.map_left_fst (Out.thick R I k) (io.act a)
  refine ⟨?_, ?_⟩
  · rintro z y ⟨w, h1, h2⟩
    refine ⟨w ≫ ((Over.pullback (Out.thick R I k)).map (io.act a)).left, ?_, ?_⟩
    · rw [Over.comp_left, ← h1]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hG).trans (Category.assoc _ _ _).symm)
    · have hB : ((Over.pullback (Out.thick R I k)).map (oD.onB.act a)).left ≫
          (D.toPre.prBe I k).left = (D.toPre.prBe I k).left ≫ (oD.onB.act a).left :=
        GlobalTheory.SplitTorusPoints.map_left_fst (Out.thick R I k) (oD.onB.act a)
      have hq : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (U.gt k).q.left =
          (U.gt k).q.left ≫ ((Over.pullback (Out.thick R I k)).map (oD.onB.act a)).left :=
        congrArg (·.left) (hl.q_lin k a)
      have hp : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (U.gt k).pG.left =
          (U.gt k).pG.left ≫ (oD.onB.act a).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.toPre.prBe I k).left) hq).trans
          ((Category.assoc _ _ _).trans ((congrArg ((U.gt k).q.left ≫ ·) hB).trans
            (Category.assoc _ _ _).symm)))
      rw [Over.comp_left (g := oD.onB.act a), ← h2]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hp).trans (Category.assoc _ _ _).symm)
  · rintro χ χ' z hχ ⟨w, h1, h2⟩
    obtain ⟨t, ht, hi⟩ := hl.i_lin k a
    refine ⟨w ≫ t.left, fun x => ?_, ?_⟩
    · rw [hχ, ← h1, ← appTop_charUnit_of_torusEndOf ht x, Scheme.Hom.comp_appTop]
      rfl
    · have hi' : (U.gt k).i.left ≫ ((Over.pullback (Out.thick R I k)).map (io.act a)).left =
          t.left ≫ (U.gt k).i.left := congrArg (·.left) hi
      have hp : t.left ≫ (U.gt k).i.left ≫ (Out.fstG I k G).left =
          ((U.gt k).i.left ≫ (Out.fstG I k G).left) ≫ (io.act a).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Out.fstG I k G).left) hi'.symm).trans
          ((Category.assoc _ _ _).trans ((congrArg ((U.gt k).i.left ≫ ·) hG).trans
            (Category.assoc _ _ _).symm)))
      rw [Over.comp_left, ← h2]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hp).trans (Category.assoc _ _ _).symm)

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
open scoped CategoryTheory.Obj

private theorem mul_left_fst {S' S : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {Y : Over S} {Z : Over S'}
    (e : Y.left ⟶ Z.left) (a b : Z ⟶ (Over.pullback f).obj G) (za zb : Y ⟶ G)
    (ha : e ≫ a.left ≫ pullback.fst G.hom f = za.left) (hb : e ≫ b.left ≫ pullback.fst G.hom f = zb.left) :
    e ≫ (a * b).left ≫ pullback.fst G.hom f = (za * zb).left := by
  let F := Over.pullback f
  let m : Z ⟶ F.obj (G ⊗ G) := lift a b ≫ Functor.LaxMonoidal.μ F G G
  have key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom f) ≫ g.left =
      (m ≫ F.map g).left ≫ pullback.fst G.hom f := by
    intro g
    rw [Category.assoc, ← SplitTorusPoints.map_left_fst, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  have h1 : m ≫ F.map (fst G G) = a := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))
  have h2 : m ≫ F.map (snd G G) = b := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))
  have h3 : m ≫ F.map μ[G] = a * b := Category.assoc _ _ _
  have hq : e ≫ m.left ≫ pullback.fst (G ⊗ G).hom f = (lift za zb).left := by
    apply pullback.hom_ext
    · have := key (fst G G)
      rw [h1] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (ha.trans
        (congrArg (fun t => t.left) (lift_fst za zb)).symm))
    · have := key (snd G G)
      rw [h2] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (hb.trans
        (congrArg (fun t => t.left) (lift_snd za zb)).symm))
  have := key μ[G]
  rw [h3] at this
  rw [← this, ← Category.assoc, hq]
  rfl

end

private theorem mono_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) : Mono (Out.thick R I e) := by
  have : IsClosedImmersion (Out.thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

private theorem exists_struct {R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (S : Type) [CommRing S] [Algebra R S]
    (h : Kills I k S) : ∃ s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))),
      s ≫ Out.thick R I k = (sp (R₀ := R) S).hom := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap R S) h)), ?_⟩
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))) = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem exists_equiv {B : Scheme.{0}} (X : Type) [AddCommGroup X] (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ B) :
    ∃ e : (Over.mk s ⟶ splitTorus B X) ≃* (Multiplicative X →* Sˣ), ∀ t χ, e t = χ ↔
      ∀ x : X, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) = (χ (Multiplicative.ofAdd x) : S) := by
  let u : Γ(Spec (CommRingCat.of S), ⊤)ˣ ≃* Sˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.toMulEquiv
  refine ⟨(splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight), fun t χ => ?_⟩
  have hv : ∀ x : X, ((((splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight)) t
      (Multiplicative.ofAdd x) : Sˣ) : S) = (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) := fun x =>
    congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (splitTorusPointsEquiv_val B X (Over.mk s) t x)
  constructor
  · rintro rfl x
    exact (hv x).symm
  · intro h
    ext x
    exact (hv x).trans (h x)

private theorem irel_iff {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegPre R} {k : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G)
    (S : Type) [CommRing S] [Algebra R S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))))
    (hs : s ≫ Out.thick R I k = (sp (R₀ := R) S).hom) :
    ∃ e : (Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X) ≃* (Multiplicative D.X →* Sˣ),
      ∀ χ z, IRel c S χ z ↔ (e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k) = z.left := by
  obtain ⟨e, he⟩ := exists_equiv D.X S s
  refine ⟨e, fun χ z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨w, hw, hz⟩
    have := mono_thick I k
    have hws : w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).hom = s := by
      rw [← cancel_mono (Out.thick R I k), hs, ← Over.w z, ← hz, ← Over.w c.i]
      simp only [Category.assoc]
      exact congrArg (fun g => w ≫ c.i.left ≫ g) (Over.w (Out.fstG I k G)).symm
    let t : Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X := Over.homMk w hws
    have ht : e t = χ := (he t χ).2 hw
    rw [← ht, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).trans hz
  · exact ⟨(e.symm χ).left, (he _ χ).1 (e.apply_symm_apply χ), (Category.assoc _ _ _).symm.trans h⟩


open scoped CategoryTheory.Obj in
theorem irel_points : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G), (∀ (S : Type) [CommRing S] [Algebra R S], Kills I k S → (∀ χ, ∃! z, IRel c S χ z) ∧ (∀ χ χ' z z', IRel c S χ z → IRel c S χ' z' → IRel c S (χ * χ') (z * z')) ∧ ∀ χ χ' z, IRel c S χ z → IRel c S χ' z → χ = χ') ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') χ z, IRel c S χ z → IRel c S' ((Units.map (φ : S →* S')).comp χ) (spMap φ ≫ z) := by
  intro R _ _ I D k G _ _ c
  refine ⟨fun S _ _ hS => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_struct I k S hS
    obtain ⟨e, he⟩ := irel_iff c S s hs
    refine ⟨fun χ => ?_, fun χ χ' z z' h h' => ?_, fun χ χ' z h h' => ?_⟩
    · refine ⟨Over.homMk ((e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k)) ?_,
        (he _ _).2 rfl, fun z hz => Over.OverMorphism.ext ((he _ _).1 hz).symm⟩
      rw [← hs]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Out.thick R I k) (Over.w (e.symm χ ≫ c.i)))))
    · rw [he] at h h' ⊢
      have := c.i_hom
      rw [map_mul, MonObj.mul_comp]
      exact (Category.id_comp _).symm.trans (mul_left_fst (Out.thick R I k) G (Y := sp S) (Z := Over.mk s) (𝟙 _)
        _ _ z z' ((Category.id_comp _).trans h) ((Category.id_comp _).trans h'))
    · rw [he] at h h'
      have := mono_thick I k
      have h1 : e.symm χ ≫ c.i = e.symm χ' ≫ c.i :=
        Over.OverMorphism.ext ((cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (h.trans h'.symm))
      exact e.symm.injective (c.isKernel.hom_ext h1 (toUnit_unique _ _))
  · rintro S _ _ S' _ _ φ χ z ⟨w, hw, hz⟩
    refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ w, fun x => ?_, ?_⟩
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← RingHom.comp_apply,
        ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, RingHom.comp_apply, hw]
      rfl
    · rw [Category.assoc, hz]
      rfl

end GlobalTheory
end

section

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

private theorem one_left_fst {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) {t : Z ⟶ S'} {r : Z ⟶ S}
    (h : t ≫ f = r) :
    (1 : Over.mk t ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f = (1 : Over.mk r ⟶ G).left := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk t ⟶ (Over.pullback f).obj (𝟙_ (Over S)) :=
    toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f)
  have h1 : (1 : Over.mk t ⟶ (Over.pullback f).obj G) = z ≫ (Over.pullback f).map η[G] := by
    rw [Hom.one_def, Functor.obj.η_def, ← Category.assoc]
  have h2 : z.left ≫ pullback.fst (𝟙_ (Over S)).hom f = (toUnit (Over.mk r)).left := by
    have a1 : pullback.fst (𝟙_ (Over S)).hom f ≫ (𝟙_ (Over S)).hom = pullback.snd _ f ≫ f := pullback.condition
    have a2 : z.left ≫ pullback.snd (𝟙_ (Over S)).hom f = t := Over.w z
    have a3 : (toUnit (Over.mk r)).left ≫ (𝟙_ (Over S)).hom = r := Over.w _
    have : Mono (𝟙_ (Over S)).hom := inferInstanceAs (Mono (𝟙 S))
    rw [← cancel_mono (𝟙_ (Over S)).hom, a3, Category.assoc, a1, ← Category.assoc, a2, h]
  rw [h1, Over.comp_left, Category.assoc, A, ← Category.assoc, h2, Hom.one_def, Over.comp_left]

private theorem mono_thick (R : Type) [CommRing R] (I : Ideal R) (k : ℕ) : Mono (Out.thick R I k) := by
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem qRel_one_iff_exists_iRel : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ z, QRel c S z 1 ↔ ∃ χ, IRel c S χ z := by
  intro R _ _ I D k G _ _ c S _ _ hS z
  have hm := mono_thick R I k
  have hf : Mono (pullback.fst D.P.A.hom (Out.thick R I k)) := inferInstance
  let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
  have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hw : ∀ (w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left),
      w ≫ (Out.fstG I k G).left = z.left → w ≫ (Out.thickObj R I k G).hom = t := by
    intro w h
    rw [← cancel_mono (Out.thick R I k), ht]
    have h1 : (Out.thickObj R I k G).hom ≫ Out.thick R I k = (Out.fstG I k G).left ≫ G.hom :=
      (pullback.condition (f := G.hom) (g := Out.thick R I k)).symm
    rw [Category.assoc, h1, ← Category.assoc, h]
    exact Over.w z
  have h1 : (1 : Over.mk t ⟶ Out.thickObj R I k D.P.A).left ≫ pullback.fst D.P.A.hom (Out.thick R I k) =
      (1 : sp (R₀ := R) S ⟶ D.P.A).left := one_left_fst D.P.A (Out.thick R I k) ht
  constructor
  · rintro ⟨w, a, b⟩
    let x : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w (hw w a)
    have hx : x ≫ c.q = toUnit _ ≫ η[Out.thickObj R I k D.P.A] := by
      apply Over.OverMorphism.ext
      refine (cancel_mono (pullback.fst D.P.A.hom (Out.thick R I k))).1 ?_
      exact ((Category.assoc _ _ _).trans b).trans h1.symm
    let u := c.isKernel.lift x (toUnit _) hx
    have hu : u ≫ c.i = x := c.isKernel.lift_fst _ _ _
    refine ⟨(Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom).comp
      (splitTorusPointsEquiv _ D.X (Over.mk t) u), u.left, fun χ => ?_, ?_⟩
    · exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (splitTorusPointsEquiv_val _ D.X (Over.mk t) u χ)).symm
    · have e : u.left ≫ c.i.left = w := congrArg (·.left) hu
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e)).trans a
  · rintro ⟨χ, w, -, a⟩
    have a' : (w ≫ c.i.left) ≫ (Out.fstG I k G).left = z.left := (Category.assoc _ _ _).trans a
    refine ⟨w ≫ c.i.left, a', ?_⟩
    let u : Over.mk t ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X := Over.homMk w (by
      have := hw _ a'
      rw [Category.assoc, Over.w c.i] at this
      exact this)
    have hu : u ≫ c.i ≫ c.q = 1 := by
      rw [c.isKernel.w, Hom.one_def, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    have e : (w ≫ c.i.left) ≫ c.q.left = (1 : Over.mk t ⟶ Out.thickObj R I k D.P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (·.left) hu)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e)).trans h1

end GlobalTheory.ChF
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem hodgeTateSetting_ainfTower_of_isPrimitiveRoot : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE], HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) (show O from (Ainf.ainfTowerL p O hv ε hε).c) := by
  intro p hp C _ _ _ v O _ _ hu _ hv ε hε _ OE _ _
  refine ⟨hv, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne (hv.map_le_one _) (fun e => hu.out (hv.isUnit_of_one' e))
  · rw [map_natCast]
    exact fun h => Nat.cast_ne_zero.2 hp.out.ne_zero ((Valuation.zero_iff v).1 h)
  · rw [map_natCast]
    exact Ainf.c_val p O hv ε hε
  · intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have h : ∀ (x : ℤ_[p]) (y : OE), sigE p OE (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℤ] star y := fun _ _ => rfl
      rw [h, h, star_star]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.ChF
end
