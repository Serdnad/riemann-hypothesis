module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle085
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle055
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkCover

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

theorem exists_geomPt (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ X), ∀ q, x q = g :=
  ⟨AlgebraicClosure (X.residueField g), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) _)) ≫ X.fromSpecResidueField g,
    fun _ => Scheme.fromSpecResidueField_apply g _⟩

theorem exists_power {C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (n : ℕ) :
    ∃ (P : Scheme.{0}) (π : P ⟶ S) (σ : Fin n → (P ⟶ C)), IsFinite π ∧ Etale π ∧ (∀ j, σ j ≫ c = π) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ S) (u : Fin n → (T ⟶ C)), (∀ j, u j ≫ c = x) →
        ∃ y : T ⟶ P, y ≫ π = x ∧ ∀ j, y ≫ σ j = u j := by
  induction n with
  | zero => exact ⟨S, 𝟙 S, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0,
      fun T x u _ => ⟨x, by simp, fun j => j.elim0⟩⟩
  | succ n ih =>
    obtain ⟨P, π, σ, h₁, h₂, h₃, h₄⟩ := ih
    refine ⟨pullback π c, pullback.fst π c ≫ π,
      Fin.cons (pullback.snd π c) (fun j => pullback.fst π c ≫ σ j), inferInstance, inferInstance, fun j => ?_,
      fun T x u hu => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [pullback.condition]
      · simp [h₃]
    · obtain ⟨y, hy, hy'⟩ := h₄ T x (fun j => u j.succ) (fun j => hu _)
      refine ⟨pullback.lift y (u 0) (hy.trans (hu 0).symm), by simp [hy], fun j => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp [hy']

theorem exists_eqLocus {P C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (a b : P ⟶ C) (h : a ≫ c = b ≫ c) :
    ∃ U : Set P, IsClopen U ∧ ∀ (T : Scheme.{0}) (y : T ⟶ P), y ≫ a = y ≫ b ↔ Set.range y ⊆ U := by
  first
  | (rename_i h_4 h_5; revert P C S c h_4 h_5 a b h; exact @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer)
  | exact @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer
  | exact _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer
  | (apply _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer ..)

theorem exists_distinct {C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (n : ℕ) :
    ∃ (P : Scheme.{0}) (π : P ⟶ S) (σ : Fin n → (P ⟶ C)), IsFinite π ∧ Etale π ∧ (∀ j, σ j ≫ c = π) ∧
      (∀ (k : Type) [Field k] (y : Sp k ⟶ P), Function.Injective fun j => y ≫ σ j) ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (u : Fin n → (Sp k ⟶ C)), (∀ j, u j ≫ c = x) → Function.Injective u →
        ∃ y : Sp k ⟶ P, y ≫ π = x := by
  obtain ⟨P, π, σ, h₁, h₂, h₃, h₄⟩ := exists_power c n
  choose U hU hU' using fun a b : Fin n => exists_eqLocus c (σ a) (σ b) ((h₃ a).trans (h₃ b).symm)
  have hV : IsClopen (⋂ a, ⋂ b, ⋂ _ : a ≠ b, (U a b)ᶜ) :=
    isClopen_iInter_of_finite fun a => isClopen_iInter_of_finite fun b =>
      isClopen_iInter_of_finite fun _ => (hU a b).compl
  let V : P.Opens := ⟨_, hV.isOpen⟩
  have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV.isClosed)
  refine ⟨V, V.ι ≫ π, fun j => V.ι ≫ σ j, inferInstance, inferInstance, fun j => by simp [h₃],
    fun k _ y a b e => ?_, fun k _ x u hu hi => ?_⟩
  · by_contra ne
    have q : Sp k := IsLocalRing.closedPoint k
    have m₁ : (y ≫ V.ι) q ∈ U a b := (hU' a b _ (y ≫ V.ι)).1 (by simpa using e) ⟨q, rfl⟩
    have m₂ : (y ≫ V.ι) q ∈ (V : Set P) := by
      rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
    exact (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 m₂ a) b) ne) m₁
  · obtain ⟨y, hy, hy'⟩ := h₄ _ x u hu
    have hr : Set.range y ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      refine Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => Set.mem_iInter.2 fun ne m => ne (hi ?_)
      rw [← hy', ← hy', hU']
      rintro _ ⟨q', rfl⟩
      rwa [Subsingleton.elim q' q]
    exact ⟨IsOpenImmersion.lift V.ι y hr, by rw [← Category.assoc, IsOpenImmersion.lift_fac, hy]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem comp_act_natCast (t : SAB H S) {T : Over S} (z : T ⟶ t.G) (n : ℕ) : z ≫ t.act.act (n : 𝓞 E) = z ^ n := by
  induction n with
  | zero =>
    have := t.act.add 0 0
    rw [add_zero] at this
    rw [Nat.cast_zero, pow_zero, show t.act.act 0 = 1 from left_eq_mul.1 this, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem pow_sq_eq_one (t : SAB H S) {T : Over S} {D : Datum H} {P : Ideal (𝓞 E)} {p i : ℕ} (hp : (p : 𝓞 E) ∈ P)
    {C : Subgroup (T ⟶ t.G)} (h : t.HeckeKer T D P p i C) {z : T ⟶ t.G} (hz : z ∈ C) : z ^ (p ^ 2) = 1 := by
  rw [← comp_act_natCast]
  refine h.2.2.1 hz _ ?_
  rw [Nat.cast_pow, sq]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp

end GlobalTheory.HkCover


open GlobalTheory.HkCover in
theorem GlobalTheory.exists_cover_lists_heckeSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → EtSet o.t.G K → HeckeSet D o.t 𝔓 p i K → ∃ (S' : Scheme.{0}) (π : S' ⟶ S) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over S') ⟶ o'.t.G)), IsFinite π ∧ Etale π ∧ Surjective π ∧ Lists (p ^ 2) τ (m.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l P p i S _ s o K hA hE hK
  obtain ⟨C, j, h₁, h₂, h₃, rfl⟩ := hE
  have hn : p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) ≠ 0 := pow_ne_zero _ hA.2.2.1.ne_zero
  have hcard : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ Q : Subgroup (Over.mk x ⟶ o.t.G),
      (∀ z, z ∈ Q ↔ Set.range z.left ⊆ Set.range j.left) ∧ (∀ z ∈ Q, z ^ (p ^ 2) = 1) ∧
      Nat.card Q = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) := fun k _ _ x => by
    obtain ⟨Q, hQ, hq⟩ := hK k x
    exact ⟨Q, hQ, fun z hz => pow_sq_eq_one o.t hA.2.2.2.1 hq hz, hq.2.2.2.2.1⟩
  generalize p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) = n at hn hcard ⊢
  have wj : j.left ≫ o.t.G.hom = C.hom := Over.w j
  have rg : ∀ {T : Scheme.{0}} (u : T ⟶ C.left), Set.range (u ≫ j.left) ⊆ Set.range j.left := by
    rintro T u _ ⟨q, rfl⟩
    exact ⟨u q, (Scheme.Hom.comp_apply _ _ _).symm⟩

  have hj : j ^ (p ^ 2) = 1 := by
    have : IsReduced C.left := GlobalTheory.isReduced_of_smooth_of_isReduced C.hom
    have := o.proper
    refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_geometricPoints_dense o.t.G.hom _ _
      ((Over.w _).trans (Over.w _).symm) Set.univ dense_univ fun k _ _ x _ => ?_)
    obtain ⟨Q, hQ, hq, -⟩ := hcard k (x ≫ C.hom)
    let x' : Over.mk (x ≫ C.hom) ⟶ C := Over.homMk x rfl
    have e := hq (x' ≫ j) ((hQ _).2 (rg x))
    rw [← MonObj.comp_pow, ← MonObj.comp_one x'] at e
    exact congrArg (fun z => z.left) e
  obtain ⟨S', π, σ, f₁, f₂, f₃, f₄, f₅⟩ := exists_distinct C.hom n
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (π ≫ s) π rfl rfl
    (by simp [spMap]) o
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over S'))
  let σ' : Fin n → (Over.mk ((𝟙_ (Over S')).hom ≫ π) ⟶ C) := fun a => Over.homMk (σ a) (by simpa using f₃ a)
  have e : ∀ a, (ρ.symm (σ' a ≫ j)).left ≫ m.toSABMap.φ = σ a ≫ j.left := fun a => by
    rw [← e₀, ρ.apply_symm_apply]; rfl
  have wτ : ∀ a, (ρ.symm (σ' a ≫ j)).left ≫ o'.t.G.hom = 𝟙 S' := fun a => Over.w _
  refine ⟨S', π, o', m, fun a => ρ.symm (σ' a ≫ j), f₁, f₂, ⟨fun g => ?_⟩, fun a => ?_, ?_, fun k _ _ y a b hab => ?_⟩
  · obtain ⟨k, _, _, x, hx⟩ := exists_geomPt S g
    obtain ⟨Q, hQ, -, hc⟩ := hcard k x
    have en : Q ≃ Fin n := Nat.equivFinOfCardPos (hc ▸ hn) |>.trans (finCongr hc)
    have : ∀ a : Fin n, ∃ u : Sp k ⟶ C.left, u ≫ j.left = (en.symm a).1.left := fun a =>
      GlobalTheory.exists_lift_closedImmersion_of_dense j.left _ Set.univ dense_univ
        fun q _ => (hQ _).1 (en.symm a).2 ⟨q, rfl⟩
    choose u hu using this
    obtain ⟨y, hy⟩ := f₅ k x u (fun a => by rw [← wj, ← Category.assoc, hu]; exact Over.w (en.symm a).1)
      fun a b hab => en.symm.injective (Subtype.ext (Over.OverMorphism.ext (by rw [← hu, ← hu, hab])))
    have q : Sp k := IsLocalRing.closedPoint k
    exact ⟨y q, by rw [← Scheme.Hom.comp_apply, hy, hx]⟩
  · rw [← map_pow, ← MonObj.comp_pow, hj, MonObj.comp_one, map_one]
  · refine Set.Subset.antisymm (fun g hg => ?_) (Set.iUnion_subset fun a => ?_)
    · obtain ⟨k, _, _, w, hw⟩ := exists_geomPt _ g
      obtain ⟨Q, hQ, -, hc⟩ := hcard k ((w ≫ o'.t.G.hom) ≫ π)
      let z : Fin n → Q := fun a => ⟨Over.homMk (((w ≫ o'.t.G.hom) ≫ σ a) ≫ j.left)
        (by simp [wj, f₃]), (hQ _).2 (rg _)⟩
      have zi : Function.Injective z := fun a b hab => f₄ k (w ≫ o'.t.G.hom)
        ((cancel_mono j.left).1 (congrArg (fun z : Q => z.1.left) hab))
      have : Finite Q := Nat.finite_of_card_ne_zero (hc ▸ hn)
      have zb := (Nat.bijective_iff_injective_and_card z).2 ⟨zi, by simp [hc]⟩
      obtain ⟨a, ha⟩ := zb.2 ⟨Over.homMk (w ≫ m.toSABMap.φ) (by simpa using congrArg (w ≫ ·) m.cart.1.w), (hQ _).2 (by
        rintro _ ⟨q, rfl⟩
        have : (w ≫ m.toSABMap.φ) q ∈ Set.range j.left := by rw [Scheme.Hom.comp_apply, hw]; exact hg
        exact this)⟩
      have ha' : ((w ≫ o'.t.G.hom) ≫ σ a) ≫ j.left = w ≫ m.toSABMap.φ := congrArg (fun z : Q => z.1.left) ha
      have hw' : (w ≫ o'.t.G.hom) ≫ (ρ.symm (σ' a ≫ j)).left = w := m.cart.1.hom_ext
        (by rw [Category.assoc, ← ha', Category.assoc _ (σ a)]; exact congrArg (_ ≫ ·) (e a))
        (by rw [Category.assoc, wτ]; exact Category.comp_id _)
      have q : Sp k := IsLocalRing.closedPoint k
      refine Set.mem_iUnion.2 ⟨a, (w ≫ o'.t.G.hom) q, ?_⟩
      rw [← hw q]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun v : Sp k ⟶ _ => v q) hw')
    · rintro _ ⟨q, rfl⟩
      have := rg (σ a) ⟨q, rfl⟩
      rw [← e, Scheme.Hom.comp_apply] at this
      exact this
  · refine f₄ k y ((cancel_mono j.left).1 ?_)
    have := congrArg (· ≫ m.toSABMap.φ) hab
    simpa only [Category.assoc, e] using this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.CoordMove
open GlobalTheory.ZM.RepBC

theorem isUnit_cst_id {R : Type} [CommRing R] (p : Sp R) (a : R) : IsUnit (cst (𝟙 (Sp R)) p a) ↔ a ∉ p.asIdeal := by
  rw [cst, gs_eq _ _ ⊤ trivial]
  refine ((Sp R).mem_basicOpen (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) p trivial).symm.trans ?_
  have := basicOpen_eq_of_affine (R := CommRingCat.of R) a
  exact (congrArg (fun U : (Sp R).Opens => p ∈ U) this).to_iff

theorem secCoord_iff {X : Scheme.{0}} (M : LB X) {I : Type} (th : I → M.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (v : I → R) : SecCoord M th x v ↔ ∃ τ : (M.pull x).Gen, τ.IsGen ∧ ∀ (i : I) (j : PUnit → M.ι) (p : Sp R),
      p ∈ (M.pull x).U j → gs x p _ ((th i).f (j PUnit.unit)) =
        cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := by
  refine exists_congr fun τ => and_congr_right fun _ => forall₂_congr fun i j => ?_
  have l : ∀ (h : (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit)) (p : Sp R), p ∈ (M.pull x).U j →
      gs (𝟙 (Sp R)) p ((M.pull x).U j) ((x.appLE _ _ h).hom ((th i).f (j PUnit.unit))) =
        gs x p _ ((th i).f (j PUnit.unit)) := fun h p hp =>
    (gs_appLE x _ _ h (𝟙 _) p hp _).trans (by rw [Category.id_comp])
  have r : ∀ (p : Sp R), p ∈ (M.pull x).U j → gs (𝟙 (Sp R)) p ((M.pull x).U j)
      (resG (Sp R) le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) *
        (show Γ(Sp R, (M.pull x).U j) from (τ.s j).val)) =
      cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := fun p hp =>
    (gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_res _ p le_top hp _) (gs_unit _ p _ hp _))
  exact ⟨fun h p hp => (l (pull_le M x j) p hp).symm.trans ((congrArg _ (h _)).trans (r p hp)),
    fun h e => fn_ext fun p hp => (l e p hp).trans ((h p hp).trans (r p hp).symm)⟩

theorem secCoord_down {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (H : LBIso L' (L.pull F)) {I : Type} (th : I → L.Sec) :
    ∃ th' : I → L'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R),
      SecCoord L' th' x v ↔ SecCoord L th (x ≫ F) v := by
  obtain ⟨w, hw⟩ := H
  have hw' := (isGen_iff w).1 hw
  choose th' h' using fun i => sec_pull_down hw' hL hL' (th i)
  refine ⟨th', fun R _ x v => ?_⟩
  have e : ∀ (p : Sp R) (j : PUnit → L.ι) (k : PUnit → L'.ι),
      pw w (fun _ : PUnit => x) (fun _ => 1) (𝟙 _) p j k = gw w x p (j PUnit.unit) (k PUnit.unit) := fun p j k => by
    rw [pw, Fintype.prod_unique, zpow_one, Category.id_comp]
  rw [secCoord_iff, secCoord_iff]
  constructor
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := exists_up hw' hL hL' τ hτ
    refine ⟨t, ht, fun i j p hp => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hL' (x p)
    have hk' : p ∈ (L'.pull x).U (fun _ => k) := mem_pull.2 hk
    have h₁ := h' i _ x p (j PUnit.unit) k (mem_pull₂.1 hp) hk
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p j (fun _ => k) hp hk')
    rw [e, Units.val_mul] at h₂
    refine h₁.trans ((congrArg (_ * ·) (h i (fun _ => k) p hk')).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₂.symm)
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := CubTransport.exists_down_units hw' hL hL' (φ' := fun _ : PUnit => x) τ hτ
    refine ⟨t, ht, fun i k p hp => ?_⟩
    obtain ⟨j, hj⟩ := exists_chart hL (F (x p))
    have hj' : p ∈ (L.pull (x ≫ F)).U (fun _ => j) := mem_pull₂.2 hj
    have h₁ := h' i _ x p j (k PUnit.unit) hj (mem_pull.1 hp)
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p (fun _ => j) k hj' hp)
    rw [e, Units.val_mul] at h₂
    refine (Units.mul_right_inj (gw w x p j (k PUnit.unit))).1 (h₁.symm.trans ((h i (fun _ => j) p hj').trans ?_))
    exact (congrArg (_ * ·) h₂).trans (mul_left_comm _ _ _)

theorem mem_nonzeroLocus_iff {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {R : Type} [CommRing R]
    {x : Sp R ⟶ X} {v : I → R} (i : I) (p : Sp R) (h : SecCoord M th x v) :
    x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal := by
  obtain ⟨τ, -, h⟩ := (secCoord_iff M th x v).1 h
  have key : ∀ k, x p ∈ M.U k → (IsUnit (gs (𝟙 X) (x p) _ ((th i).f k)) ↔ v i ∉ p.asIdeal) := fun k hk => by
    have e := h i (fun _ => k) p (mem_pull.2 hk)
    rw [gs_stalkMap x p _ hk] at e
    rw [← isUnit_cst_id, ← isUnit_map_iff (x.stalkMap p).hom]
    exact (congrArg IsUnit e).to_iff.trans (Units.isUnit_mul_units _ _)
  rw [mem_nonzeroLocus]
  refine ⟨fun ⟨k, hk, u⟩ => (key k hk).1 u, fun u => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hM (x p)
  exact ⟨k, hk, (key k hk).2 u⟩

theorem secCoord_pull_iso_locus : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (X' : Scheme.{0}) (π : X' ⟶ X), ∃ th' : I → (M.pull π).Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v) ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → ∃ th' : I → M'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), SecCoord M' th' x v ↔ SecCoord M th x v) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R) (i : I) (p : Sp R), SecCoord M th x v → (x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal) := by
  intro X M I th hM
  refine ⟨fun X' π => ⟨fun i => RepBC.secPull M π (th i), fun R _ x v => secCoord_pull M th π x v⟩, fun M' hM' H => ?_,
    fun R _ x v i p h => mem_nonzeroLocus_iff hM i p h⟩
  obtain ⟨th', h⟩ := secCoord_down hM hM'
    (LBIso.chartPull (chartPullId M') (Geo.Tor.chartPullPull M (𝟙 X) (𝟙 X) rfl) (LBIso.symm H)) th
  refine ⟨th', fun R _ x v => ?_⟩
  have := h R x v
  rwa [Category.comp_id] at this

end GlobalTheory.ZM.CoordMove
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

theorem isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (s : X ⟶ Sp R) :
    IsQProjOver s ↔ LocallyOfFiniteType s ∧ ∃ L : LB X, IsAmpleLB L := by
  constructor
  · rintro ⟨N, i, hi, hq, rfl⟩
    haveI := hi
    haveI := hq
    haveI : IsProper (PSpace.str R N) :=
      ((isProjOver_iff_isProper_and_exists_isAmpleLB (PSpace.str R N)).1
        ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩).1
    exact ⟨inferInstance, _, IsAmpleLB.pull_of_isImmersion (isAmpleLB_basic.2.2.2.2.2.2.1 R N) i⟩
  · rintro ⟨hs, L, hL⟩
    haveI := hs
    exact hL.isQProjOver s

theorem isQProjOver_comp_of_isAffineHom (f : Y ⟶ X) [IsAffineHom f] [LocallyOfFiniteType f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  haveI := hs
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (f ≫ s)).2 ⟨inferInstance, L.pull f, ?_⟩
  exact isAmpleLB_basic.2.2.1 f inferInstance hL

theorem isQProjOver_comp_of_isFinite (f : Y ⟶ X) [IsFinite f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := isQProjOver_comp_of_isAffineHom f h

theorem isQProjOver_of_isPullback {R' : Type} [CommRing R'] {b : R →+* R'} {s : X ⟶ Sp R} {π : Y ⟶ X}
    {s' : Y ⟶ Sp R'} (H : IsPullback π s' s (spMap b)) (h : IsQProjOver s) : IsQProjOver s' := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s').2 ⟨?_, L.pull π, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H hs
  · exact hL.pull_of_isPullback H

theorem isQProjOver_finite_and_baseChange :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      (∀ (Y : Scheme.{0}) (f : Y ⟶ X), IsFinite f → IsQProjOver (f ≫ s)) ∧
        ∀ (R' : Type) [CommRing R'] (b : R →+* R'), IsQProjOver (pullback.snd s (spMap b)) := by
  intro R _ _ X s h
  refine ⟨fun Y f hf => ?_, fun R' _ b => ?_⟩
  · haveI := hf
    exact isQProjOver_comp_of_isFinite f h
  · exact isQProjOver_of_isPullback (IsPullback.of_hasPullback s (spMap b)) h

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.AmpleDominates

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {X : Scheme.{0}} {M N : LB X}

theorem eventually_isGenerated {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsGenerated (LB.div (lbPow M t) N) := by
  obtain ⟨d, hd, m, s, hs⟩ := hM.exists_veryAmpleBy f
  have hH := isLB_lbPow hM.isLB d
  have hD : ∀ i, (LB.div (lbPow M i) N).IsLB := fun i => LB.isLB_div (isLB_lbPow hM.isLB i) hN
  choose t₀ ht₀ using fun i => TwistGen.twist_generated R X f _ m s hH hs _ (hD i)
  refine Filter.eventually_atTop.2 ⟨d * (Finset.range d).sup fun i => (t₀ i).toNat, fun t ht => ?_⟩
  have h₁ : (t₀ (t % d)).toNat ≤ t / d :=
    (Finset.le_sup (f := fun i => (t₀ i).toNat) (Finset.mem_range.2 (Nat.mod_lt t hd))).trans
      ((Nat.le_div_iff_mul_le hd).2 (by rwa [Nat.mul_comm]))
  obtain ⟨n, u, hu⟩ := ht₀ (t % d) (t / d : ℕ) (Int.toNat_le.1 h₁)
  have hG : IsGenerated (tw (LB.div (lbPow M (t % d)) N) (lbPow M d) (t / d : ℕ)) := ⟨_, u, hu⟩
  refine hG.of_lbIso (hD t) ((cls_eq_iff (hD t) hG.isLB).1 ?_)
  have e : cls _ hG.isLB = cls _ (hD (t % d)) - cls _ (isLB_pw hH (-((t / d : ℕ) : ℤ))) :=
    cls_div (hD _) (isLB_pw hH _) _
  rw [e, AmpleStabFinite.cls_pw hH, cls_div (isLB_lbPow hM.isLB t) hN, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_lbPow hM.isLB, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  generalize cls M hM.isLB = a
  generalize cls N hN = b
  conv_lhs => rw [← Nat.mod_add_div t d]
  simp only [add_nsmul, mul_nsmul, neg_zsmul, natCast_zsmul]
  abel

theorem eventually_isAmpleLB {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsAmpleLB (LB.div (lbPow M t) N) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (eventually_isGenerated f hM hN)
  refine Filter.eventually_atTop.2 ⟨a + 1, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hG := ha k (by omega)
  have h₀ := LB.isLB_div (isLB_lbPow hM.isLB (k + 1)) hN
  have h₁ := LB.isLB_div h₀ hM.isLB
  refine hM.tensor_isGenerated hG h₀ ((cls_eq_zero_iff (LB.isLB_div h₁ hG.isLB)).1 ?_)
  rw [cls_div h₁ hG.isLB, cls_div h₀ hM.isLB, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_div (isLB_lbPow hM.isLB _) hN, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  simp only [add_nsmul, one_nsmul]
  abel

theorem exists_sec_ne_zero [Nonempty X] {L : LB X} (h : IsGenerated L) : ∃ s : L.Sec, ∃ j, s.f j ≠ 0 := by
  obtain ⟨s, hs⟩ := h.exists_mem (Classical.arbitrary X)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  refine ⟨s, j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem eventually_sec_and_relAmple : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M N : LB P.A.left), M.IsLB → N.IsLB → Out.RelAmple P.A M → ∀ᶠ t : ℕ in Filter.atTop, (∃ s : (LB.div (lbPow M t) N).Sec, ∃ j, s.f j ≠ 0) ∧ Out.RelAmple P.A (LB.div (lbPow M t) N) := by
  intro K _ _ P M N hM hN h
  have := P.isAb.proper
  have := polAV_isIntegral_of_isAlgClosed K P
  have hA := isAmpleLB_of_relAmple_of_isAffine P.A hM h
  filter_upwards [eventually_isGenerated P.A.hom hA hN, eventually_isAmpleLB P.A.hom hA hN] with t h₁ h₂
  exact ⟨exists_sec_ne_zero h₁, (relAmple_iff_isAmpleLB_of_isAffine P.A h₂.isLB).2 h₂⟩

end GlobalTheory.AmpleDominates
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

open GlobalTheory.ThetaObjPull

theorem pow_left_comp_of_grpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (x' : Out.baseOver S' ⟶ A')
    (x : Out.baseOver S ⟶ A) (e : x'.left ≫ φ = f ≫ x.left) (n : ℕ) :
    (x' ^ n).left ≫ φ = f ≫ (x ^ n).left := by
  have e₁ : pushHom h _ x' = toBase f ≫ x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ n) = toBase f ≫ (x ^ n) := by
    rw [map_pow, e₁]
    exact (map_pow (preHom (toBase f)) _ _).symm
  exact congrArg (fun z => z.left) e₂

theorem gLies_pull : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ s₁ = s₂ → ∃ (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), TMap u t₁ y ∧ GLies A act Q (y ≫ c) u ψ ∧ LBIso u.L (L.pull ψ) ∧ ∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ hL ⟨h₁, h₂, h₃⟩ hI hs
  obtain ⟨u, φ, k₁, k₂, k₃, k₄⟩ := GlobalTheory.tObj_pull o g (N' ^ 2) J b S₁ S₂ s₁ s₂ y t₁ hs
  refine ⟨u, φ ≫ ψ₁, ⟨φ, k₁, k₂, k₃, k₄⟩, ⟨k₁.comp h₁, fun i => ?_, fun i => ?_⟩, ?_, fun i => ?_⟩
  · rw [← Category.assoc, k₄, Category.assoc, h₂, Category.assoc]
  · rw [← Category.assoc, pow_left_comp_of_grpPullback k₁ _ _ (k₃ i), Category.assoc, h₃, Category.assoc]
  · exact LBIso.trans u.isLB (pull_isLB t₁.isLB _) (pull_isLB hL _) k₂ (lbIso_pull_comp hI φ)
  · rw [← Category.assoc, k₃, Category.assoc]

end GlobalTheory.ZM.NearBuild
end
end
