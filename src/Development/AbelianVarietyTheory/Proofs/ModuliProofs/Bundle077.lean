module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle073
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle002

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (g : Sp A ⟶ Sp B) : ∃ β : B →+* A, g = spMap β :=
  ⟨(Spec.preimage g).hom, (Spec.map_preimage g).symm⟩

theorem spMap_inj' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

def fnOn {L : Type} [CommRing L] {T : Scheme.{0}} (g : T ⟶ Sp L) : L →+* Γ(T, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom

theorem map_fnOn {L k : Type} [CommRing L] [CommRing k] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp k ⟶ T)
    (β : L →+* k) (e : h ≫ g = spMap β) (c : Lˣ) :
    Units.map h.appTop.hom.toMonoidHom (Units.map (fnOn g).toMonoidHom c) = unitOn (Units.map β.toMonoidHom c) := by
  apply Units.ext
  show h.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) =
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β c)
  have h1 : (h ≫ g).appTop = g.appTop ≫ h.appTop := Scheme.Hom.comp_appTop _ _
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  have h3 := congrArg (fun φ => φ.hom (c : L)) h2
  rw [e] at h1
  have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) h1
  exact h4.symm.trans h3.symm

abbrev TateAt (D : Datum H) (t : SAB H S) {k : Type} [Field k] (x : Sp k ⟶ S) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
    (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

theorem datum_free (D : Datum H) : Module.Free ℤ D.La ∧ Module.Finite ℤ D.La := by
  have := D.fin
  have := D.proj
  have h : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  exact ⟨inferInstance, h⟩

theorem act_nsmul (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) (c : 𝓞 E) :
    x ≫ t.act.act (n • c) = (x ^ n) ≫ t.act.act c := by
  have := t.act.hom c
  rw [add_map_nsmul t.act.add, MonObj.comp_pow, MonObj.pow_comp]

theorem exists_full (t : SAB H S) {B L : Type} [Field B] [CharZero B] [Field L] [Algebra B L] [FiniteDimensional B L]
    (s : S ⟶ Sp B) {N : ℕ} (hN : 0 < N) {ξ : Lˣ} (hξ : ξ ^ N = 1)
    {Z : Over S} {et : D.La → (Z ⟶ t.G)} (R : RepTors t.G N D.La Z et)
    (hW : ∀ (T : Over S) (x y : T ⟶ t.G) (c : Γ(T.left, ⊤)ˣ), IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
      c ^ N = 1 → ClopenCond T fun _ h =>
        Out.WeilIs t.G t.PP.L N (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c)) :
    ∃ (W : Over S) (α : D.La → (W ⟶ t.G)), IsFinite W.hom ∧ Etale W.hom ∧ (∀ a c, α (a + c) = α a * α c) ∧
      (∀ a, α a ^ N = 1) ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
        ∀ α' : D.La → (Over.mk x ⟶ t.G), (∀ a c, α' (a + c) = α' a * α' c) → (∀ a, α' a ^ N = 1) →
          ((∃ w : Over.mk x ⟶ W, ∀ a, w ≫ α a = α' a) ↔ ∃ β' : L →+* k, β'.comp (algebraMap B L) = β ∧
            (∀ (c : 𝓞 E) a, α' (c • a) = α' a ≫ t.act.act c) ∧
            ∀ a b, Out.WeilIs t.G t.PP.L N (α' a) (α' b) (unitOn (Units.map β'.toMonoidHom ξ ^ D.EF a b))) := by
  obtain ⟨hfree, hfin⟩ := datum_free D
  have hLf : IsFinite (spMap (algebraMap B L)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hLe : Etale (spMap (algebraMap B L)) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isSeparable B L
    have : Algebra.FinitePresentation B L := Algebra.FinitePresentation.of_finiteType.1 inferInstance
    exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  let C : Over S := Over.mk (pullback.fst s (spMap (algebraMap B L)))
  have hC1 : IsFinite C.hom := inferInstanceAs (IsFinite (pullback.fst s (spMap (algebraMap B L))))
  have hC2 : Etale C.hom := inferInstanceAs (Etale (pullback.fst s (spMap (algebraMap B L))))
  have := R.1
  have := R.2.1
  obtain ⟨hY1, hY2⟩ := finiteEtale_tensor Z C
  let g : (Z ⊗ C).left ⟶ Sp L := (snd Z C).left ≫ pullback.snd s (spMap (algebraMap B L))
  have hg : g ≫ spMap (algebraMap B L) = (Z ⊗ C).hom ≫ s := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ s) (Over.w (snd Z C))
  let y : D.La → (Z ⊗ C ⟶ t.G) := fun a => fst Z C ≫ et a
  have yadd : ∀ a c, y (a + c) = y a * y c := fun a c => by simp only [y, R.2.2.1, MonObj.comp_mul]
  have ypow : ∀ a, y a ^ N = 1 := fun a => by simp only [y]; rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one]
  have ymod : ∀ a c, y (a + N • c) = y a := fun a c => by rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap B L).injective
  have hu : IsUnit (N : Γ((Z ⊗ C).left, ⊤)) := by
    have := (IsUnit.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')).map (fnOn g)
    rwa [map_natCast] at this
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod D.La hN
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod (𝓞 E) hN
  have c1 : ClopenCond (Z ⊗ C) fun _ h => ∀ (c : 𝓞 E) a, h ≫ y (c • a) = h ≫ y a ≫ t.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := t.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ t.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := t.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, t.act.add, MonObj.comp_mul, act_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond (Z ⊗ C) fun _ h => ∀ p : D.La × D.La, Out.WeilIs t.G t.PP.L N (h ≫ y p.1) (h ≫ y p.2)
      (Units.map (h.left.appTop).hom.toMonoidHom (Units.map (fnOn g).toMonoidHom (ξ ^ D.EF p.1 p.2))) := by
    refine ClopenCond.forall_of_finite (Prod.map q q) (fun p => hW _ _ _ _ hu (ypow _) (ypow _) ?_)
      fun p p' e T' h Hc => ?_
    · rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow, map_one]
    · obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := p'
      obtain ⟨c, rfl⟩ := hq a a' (congrArg Prod.fst e)
      obtain ⟨d, rfl⟩ := hq b b' (congrArg Prod.snd e)
      have : ξ ^ D.EF (a + N • c) (b + N • d) = ξ ^ D.EF a b := by
        have : D.EF (a + N • c) (b + N • d) = D.EF a b + N * (D.EF a d + D.EF c (b + N • d)) := by
          simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
          ring
        rw [this, zpow_add, zpow_mul, zpow_natCast, hξ, one_zpow, _root_.mul_one]
      dsimp only at Hc ⊢
      rwa [ymod, ymod, this]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, -, Hi⟩ := exists_sub U hU
  refine ⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, ypow, MonObj.comp_one], fun k _ x β hx α' hadd hpow => ⟨?_, ?_⟩⟩
  · rintro ⟨w, hw⟩
    obtain ⟨h1, h2⟩ := (HU _ (w ≫ i)).2 ((Hi _ _).2 ⟨w, rfl⟩)
    obtain ⟨β', hβ'⟩ := exists_spMap (A := k) ((w ≫ i).left ≫ g)
    refine ⟨β', spMap_inj' ?_, fun c a => ?_, fun a b => ?_⟩
    · rw [← spMap_comp'', ← hβ', ← hx, Category.assoc, hg, ← Category.assoc]
      exact congrArg (· ≫ s) (Over.w (w ≫ i))
    · rw [← hw, ← hw, ← Category.assoc, h1]
      simp only [Category.assoc]
    · have := h2 (a, b)
      rw [map_fnOn g _ β' hβ', map_zpow, Category.assoc, Category.assoc, hw, hw] at this
      exact this
  · rintro ⟨β', hβ', h1, h2⟩
    obtain ⟨z, hz, -⟩ := R.2.2.2.2 _ α' hadd hpow
    let c : Over.mk x ⟶ C := Over.homMk (pullback.lift x (spMap β') (by rw [hx, spMap_comp'', hβ']))
      (pullback.lift_fst _ _ _)
    have hy : ∀ a, lift z c ≫ y a = α' a := fun a => by simp only [y]; rw [lift_fst_assoc, hz]
    have hg' : (lift z c).left ≫ g = spMap β' := by
      simp only [g]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact pullback.lift_snd _ _ _
    obtain ⟨w, hw⟩ := (Hi _ (lift z c)).1 ((HU _ _).1 ⟨fun c a => by rw [hy, ← Category.assoc, hy, h1], fun p => by
      rw [map_fnOn g _ β' hg', map_zpow, hy, hy]
      exact h2 _ _⟩)
    exact ⟨w, fun a => by rw [← Category.assoc, hw, hy]⟩

end GlobalTheory.LevCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.FamOf

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

section Unit
variable {S : Scheme.{0}} (A : Over S)

def unitInv : A ⟶ Over.mk (𝟙 S) ⊗ A := lift (Over.homMk A.hom (by simp)) (𝟙 A)

theorem unitInv_snd : (unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left = 𝟙 _ := by
  rw [← Over.comp_left, unitInv, lift_snd]; rfl

theorem to_base_ext {T : Over S} (f f' : T ⟶ Over.mk (𝟙 S)) : f = f' :=
  Over.mkIdTerminal.hom_ext f f'

theorem snd_unitInv : (snd (Over.mk (𝟙 S)) A).left ≫ (unitInv A).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : snd (Over.mk (𝟙 S)) A ≫ unitInv A = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])
  rw [this]; rfl

theorem unitInv_fst : (unitInv A).left ≫ (fst (Over.mk (𝟙 S)) A).left = A.hom := by
  rw [← Over.comp_left, unitInv, lift_fst]; rfl

theorem pt_unitInv (z : Over.mk (𝟙 S) ⟶ A) : z.left ≫ (unitInv A).left = (lift (𝟙 (Over.mk (𝟙 S))) z).left := by
  rw [← Over.comp_left]
  congr 1
  exact CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])

theorem isPullback_unitInv : IsPullback (unitInv A).left A.hom (fst (Over.mk (𝟙 S)) A).left (𝟙 S) := by
  haveI : IsIso (unitInv A).left := ⟨_, unitInv_snd A, snd_unitInv A⟩
  exact IsPullback.of_horiz_isIso ⟨by rw [unitInv_fst, Category.comp_id]⟩

def chartPullUnit (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k) :
    ChartPull (lbPow L k) (Out.LPow A L a (Over.mk (𝟙 S))) (unitInv A).left :=
  have le : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => 𝟙 A.left) j ≤ (unitInv A).left ⁻¹ᵁ
      LB.wchart L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun _ => by
      have h1 : y ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy PUnit.unit
      show ((unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left) y ∈ L.U (j PUnit.unit)
      rw [unitInv_snd]; exact h1
  { idx := fun j _ => j PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (k : ℤ)) (𝟙 _) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => a) (unitInv A).left y _ _
          (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_unique, Fintype.prod_unique, unitInv_snd, Category.comp_id, ha] }

end Unit

theorem pt_unique {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Scheme.{0}} {s : Z ⟶ Sp R}
    {M : LB Z} {th : σ → M.Sec} (hP : ProjRep I s M th) {T : Type} [CommRing T] {β : R →+* T} {y y' : Sp T ⟶ Z}
    {w : σ → T} (hy : y ≫ s = spMap β) (hy' : y' ≫ s = spMap β) (hc : SecCoord M th y w) (hc' : SecCoord M th y' w) :
    y = y' := by
  obtain ⟨h1, h2⟩ := hP.2.1 T β y w hy hc
  exact (hP.2.2 T β w h1 h2).unique ⟨hy, hc⟩ ⟨hy', hc'⟩

theorem fibre_of_unit {R K σ : Type} [CommRing R] [CommRing K] {x : R →+* K} {Z : Scheme.{0}} {s : Z ⟶ Sp R} {M : LB Z}
    {th : σ → M.Sec} (A : Over (Sp K)) (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k)
    (th' : σ → (Out.LPow A L a (Over.mk (𝟙 (Sp K)))).Sec) (φ₀ : (Over.mk (𝟙 (Sp K)) ⊗ A).left ⟶ Z)
    (h1 : IsPullback φ₀ (fst (Over.mk (𝟙 (Sp K))) A).left s (spMap x))
    (h2 : LBIso (Out.LPow A L a (Over.mk (𝟙 (Sp K)))) (M.pull φ₀))
    (h3 : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
      SecCoord _ th' y w ↔ SecCoord M th (y ≫ φ₀) w) :
    ∃ φ : A.left ⟶ Z, IsPullback φ A.hom s (spMap x) ∧
      (∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
        SecCoord _ th' y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) A).left ≫ φ) w) ∧
      LBIso (lbPow L k) (M.pull φ) ∧
      ∀ (z : Over.mk (𝟙 (Sp K)) ⟶ A) (w : σ → K), SecCoord _ th' (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left w →
        SecCoord M th (z.left ≫ φ) w := by
  refine ⟨(unitInv A).left ≫ φ₀, ?_, fun T _ y w => ?_, ?_, fun z w hz => ?_⟩
  · have := (isPullback_unitInv A).paste_horiz h1
    rwa [Category.id_comp] at this
  · have e : (snd (Over.mk (𝟙 (Sp K))) A).left ≫ (unitInv A).left ≫ φ₀ = φ₀ := by
      rw [← Category.assoc, snd_unitInv, Category.id_comp]
    rw [e]
    exact h3 T y w
  · exact LBIso.chartPull (chartPullUnit A L k a ha) (chartPullSame M _ _ _ (unitInv A).left fun _ => rfl) h2
  · have e : z.left ≫ (unitInv A).left ≫ φ₀ = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left ≫ φ₀ := by
      rw [← Category.assoc, pt_unitInv]
    rw [e]
    exact (h3 K _ w).1 hz

theorem exists_section {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Over (Sp R)}
    {M : LB Z.left} {th : σ → M.Sec} (hP : ProjRep I Z.hom M th) (p : σ → R) {P : Set (Ideal R)} (hd : DenseP P)
    (hu : Ideal.span (Set.range p) = ⊤)
    (h : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (y : Sp K ⟶ Z.left), RingHom.ker x = q ∧
      y ≫ Z.hom = spMap x ∧ SecCoord M th y (fun a => x (p a))) :
    ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left p := by
  have hF : ∀ F ∈ I, MvPolynomial.eval₂ (RingHom.id R) p F = 0 := by
    intro F hF
    refine hd _ fun q hq _ => ?_
    obtain ⟨K, _, x, y, hx, hy, hc⟩ := h q hq
    have h1 := (hP.2.1 K x y _ hy hc).2 F hF
    rw [← hx, RingHom.mem_ker, MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    exact h1
  obtain ⟨y, ⟨hy, hc⟩, -⟩ := hP.2.2 R (RingHom.id R) p hu hF
  exact ⟨Over.homMk y (hy.trans (spMap_id R)), hc⟩

theorem exists_sections_fam : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R) (Hh : Type) (hh : Hh → Ix g (N' ^ 2)) (Q : Polynomial ℚ) (d : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec), DenseP (objPrimes b Mat κ β v) → FibData b Mat κ β v m p hh Q d → (∀ h, Ideal.span (Set.range (p h)) = ⊤) → ProjRep (vanIdeal d (fun h i => p (hh h) i)) Z.hom M th → Flat Z.hom → (∀ (K : Type) [Field K] (x : R →+* K) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : Ix g (N' ^ 2) → M'.Sec), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → CutBy I Q d (fun h i => x (p (hh h) i)) → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : Ix g (N' ^ 2) → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w) → ∃ sc, Fam b Mat κ β v m M th sc := by
  intro o _ g N' J b Mat κ R _ _ β v m p Hh hh Q d Z M th hd hfib hu hZ hflat hφ
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t' → ∃ φ : t'.A.left ⟶ Z.left, IsPullback φ t'.A.hom Z.hom (spMap x) ∧
      (∃ σ, t'.Emb m (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T]
        (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g (N' ^ 2) → T),
        SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
      LBIso (lbPow t'.L (m ^ 2)) (M.pull φ) ∧
      ∀ h, ((t'.lab h ^ N').left ≫ φ) ≫ Z.hom = spMap x ∧
        SecCoord M th ((t'.lab h ^ N').left ≫ φ) (fun a => x (p h a)) := by
    intro K _ _ x s t' ht
    obtain ⟨σ, I, hE, hP, hI, hc, hs⟩ := hfib K x s t' ht
    obtain ⟨φ₀, a1, a2, a3⟩ := hφ K x I _ _ _ σ hI hc hP
    obtain ⟨φ, b1, b2, b3, b4⟩ := fibre_of_unit t'.A t'.L (m ^ 2) _ (Nat.cast_pow m 2).symm σ φ₀ a1 a2 a3
    refine ⟨φ, b1, ⟨σ, hE, b2⟩, b3, fun h => ⟨?_, b4 _ _ (hs h)⟩⟩
    rw [Category.assoc, b1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _
  have hsc : ∀ h, ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left (p h) := fun h =>
    exists_section hZ (p h) hd (hu h) (by
      intro q hq
      obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨φ, -, -, -, h4⟩ := key K x s t' ht
      exact ⟨K, inferInstance, x, _, hx, h4 h⟩)
  choose sc hsc using hsc
  refine ⟨sc, ⟨_, p, hZ, hsc⟩, hflat, fun K _ _ x s t' ht => ?_⟩
  obtain ⟨φ, h1, h2, h3, h4⟩ := key K x s t' ht
  refine ⟨φ, h1, h2, h3, fun h => pt_unique hZ (h4 h).1 ?_ (h4 h).2
    ((Coord.secCoord_bc_scale_unique _ M _ th R _ _ hZ.1 (hsc h)).1 K x)⟩
  rw [Category.assoc, Over.w]
  exact Category.comp_id _

end GlobalTheory.ZM.FamOf
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem hom_descends_to_fg_intermediateField : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (A B : Over (Sp K)) (f : (Over.pullback (spMap (algebraMap K C))).obj A ⟶ (Over.pullback (spMap (algebraMap K C))).obj B), LocallyOfFiniteType A.hom → QuasiCompact A.hom → IsSeparated A.hom → LocallyOfFiniteType B.hom → ∃ (L : IntermediateField K C) (f₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ B.left), L.FG ∧ f₀ ≫ B.hom = pullback.fst _ _ ≫ A.hom ∧ ∀ i : pullback A.hom (spMap (algebraMap K C)) ⟶ pullback A.hom (spMap (algebraMap K L)), i ≫ pullback.fst _ _ = pullback.fst _ _ → i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (algebraMap L C) → i ≫ f₀ = f.left ≫ pullback.fst _ _ := by
  intro K C _ _ _ A B f _ _ _ _
  have hw : f.left ≫ pullback.snd B.hom (spMap (algebraMap K C)) =
      pullback.snd A.hom (spMap (algebraMap K C)) := by
    simpa using Over.w f
  have hφ : (f.left ≫ pullback.fst _ _) ≫ B.hom = pullback.fst _ _ ≫ A.hom := by
    rw [Category.assoc, pullback.condition, reassoc_of% hw, pullback.condition]
  obtain ⟨R, ψ, hR, hψ, hRψ⟩ := Spread.exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) hφ
  obtain ⟨t, rfl⟩ := hR
  let L : IntermediateField K C := IntermediateField.adjoin K (t : Set C)
  have hle : Algebra.adjoin K (t : Set C) ≤ L.toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin K _
  refine ⟨L, Spread.bcMap A.hom (Subalgebra.inclusion hle) ≫ ψ, ⟨t, rfl⟩, ?_, ?_⟩
  · rw [Category.assoc, hψ, Spread.bcMap_fst_assoc]
  · intro i h₁ h₂
    rw [Spread.eq_bcMap A.hom L.val h₁ h₂, ← Category.assoc,
      Spread.bcMap_comp_of_eq A.hom _ _ (Algebra.adjoin K (t : Set C)).val fun _ ↦ rfl, hRψ]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_partialBundle_iso_normalised : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V V' : S.Opens) (M M' : LB X) (r : (M.pull e).Gen) (r' : (M'.pull e).Gen), e ≫ p = 𝟙 S → ⨆ a, M.U a = p ⁻¹ᵁ V → ⨆ a, M'.U a = p ⁻¹ᵁ V' → r.IsGen → r'.IsGen → LBIso M' M → ∃ w : LB.Iso M' M, w.IsGen ∧ ∀ (x : S) (a : M.ι) (b : M'.ι), e x ∈ M.U a → e x ∈ M'.U b → gm (𝟙 S) x ((M.pull e).U fun _ => a) (r.s fun _ => a) = gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x ((M'.pull e).U fun _ => b) (r'.s fun _ => b) := by
  first | exact @GlobalTheory.BundleNormalise.exists_iso_normalised | exact GlobalTheory.BundleNormalise.exists_iso_normalised | (intros; apply GlobalTheory.BundleNormalise.exists_iso_normalised <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DegActCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

variable {R : Type} [CommRing R] [IsDomain R]

section Act

variable {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X]
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Act

section Ext

variable {D : DegPre R} {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] {k : ℕ}

theorem qkExt_unique {f : F →+* F'} {p : QkPt D F k} {q q' : QkPt D F' k} (h : QkExt f p q)
    (h' : QkExt f p q') : q = q' := by
  have hg : q.g = q'.g :=
    TorusExt.gt_ext_val (Over.OverMorphism.ext (h.2.1.trans h'.2.1.symm)) fun χ y J hJ =>
      (val_corr hJ (h.2.2 χ) _).trans (val_corr hJ (h'.2.2 χ) _).symm
  have hy : q.y = q'.y := h.1.trans h'.1.symm
  obtain ⟨y, g, e⟩ := q
  obtain ⟨y', g', e'⟩ := q'
  obtain rfl : y = y' := hy
  obtain rfl : g = g' := hg
  rfl

end Ext

section Through

variable {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X]

end Through

section Unit

variable (D : DegPre R) (χ : D.X)

end Unit

end GlobalTheory.DegActCompare
end
end
