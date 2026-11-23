module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  ReciprocityTheory.ChartRestriction.G.Out in
noncomputable local instance (priority := high) grpObjUniformizationThick075 {R : Type} [CommRing R]
    (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] :
    GrpObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.grpObjObj (F := Over.pullback (thick R I e)) (G := G)

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.FormalTorusPts

theorem scal_comp {W : Type} [CommRing W] {Z Z' : Scheme.{0}} (h : Z' ⟶ Z)
    (r : Z ⟶ Spec (CommRingCat.of W)) (w : W) : scal (h ≫ r) w = h.appTop.hom (scal r w) := by
  rw [scal, scal, Scheme.Hom.comp_appTop]; rfl

theorem scal_specMap {W W' : Type} [CommRing W] [CommRing W'] {Z : Scheme.{0}} (φ : W →+* W')
    (r : Z ⟶ Spec (CommRingCat.of W')) (w : W) :
    scal (r ≫ Spec.map (CommRingCat.ofHom φ)) w = scal r (φ w) :=
  congr($(SplitTorusPoints.ΓSpecIso_inv_comp_specMap r (CommRingCat.ofHom φ)).hom w)

theorem exists_lift_quot {W : Type} [CommRing W] (J : Ideal W) {Z : Scheme.{0}}
    (r : Z ⟶ Spec (CommRingCat.of W)) (h : ∀ w ∈ J, scal r w = 0) :
    ∃ r' : Z ⟶ Spec (CommRingCat.of (W ⧸ J)),
      r' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = r := by
  let φ : CommRingCat.of W ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J φ.hom h)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp]
  change Z.toSpecΓ ≫ Spec.map φ = r
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of W)).inv,
    SplitTorusPoints.ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
    Category.comp_id]

variable {R : Type} [CommRing R] (I : Ideal R) (W : Type) [CommRing W] [Algebra R W]

theorem pow_le_comap (n : ℕ) : I ^ n ≤ ((I.map (algebraMap R W)) ^ n).comap (algebraMap R W) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]

def lev (e : ℕ) : Spec (CommRingCat.of (W ⧸ (I.map (algebraMap R W)) ^ (e + 1))) ⟶
    Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap R W) (pow_le_comap I W (e + 1))))

theorem lev_thick (e : ℕ) : lev I W e ≫ thick R I e =
    adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) := by
  rw [lev, ← Spec.map_comp, ← Spec.map_comp]; rfl

instance mono_thick (e : ℕ) : Mono (thick R I e) := by
  have := isClosedImmersion_red (I ^ (e + 1))
  infer_instance

variable {X : Type} [AddCommGroup X] {W}

def pt (e : ℕ) (a : Multiplicative X →* Wˣ) :
    Over.mk (lev I W e) ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X :=
  (splitTorusPointsEquiv _ X (Over.mk (lev I W e))).symm
    ((Units.map ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
      (adicLevelι (I.map (algebraMap R W)) (e + 1)).appTop).hom.toMonoidHom).comp a)

theorem pt_mul (e : ℕ) (a b : Multiplicative X →* Wˣ) : pt I e (a * b) = pt I e a * pt I e b := by
  rw [pt, pt, pt, ← map_mul]
  congr 1
  ext χ
  simp

theorem pt_char (e : ℕ) (a : Multiplicative X →* Wˣ) (χ : X) :
    (pt I e a).left.appTop.hom (charUnit _ X χ).val =
      scal (adicLevelι (I.map (algebraMap R W)) (e + 1)) (a (Multiplicative.ofAdd χ)).val := by
  rw [← splitTorusPointsEquiv_val, pt, MulEquiv.apply_symm_apply]
  rfl

theorem pt_hom (e : ℕ) (a : Multiplicative X →* Wˣ) :
    (pt I e a).left ≫ (splitTorus _ X).hom = lev I W e := Over.w (pt I e a)

theorem exists_factor (e : ℕ) (a : Multiplicative X →* Wˣ) {Z : Scheme.{0}}
    (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ X).left)
    (h : τ ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).hom ≫ thick R I e =
      r ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)))
    (hχ : ∀ χ, τ.appTop.hom (charUnit _ X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) :
    ∃ r', r' ≫ adicLevelι (I.map (algebraMap R W)) (e + 1) = r ∧ r' ≫ (pt I e a).left = τ := by
  have hk : ∀ w ∈ (I.map (algebraMap R W)) ^ (e + 1), scal r w = 0 := by
    have : (I.map (algebraMap R W)) ^ (e + 1) ≤ RingHom.ker
        ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop).hom := by
      rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
      intro v hv
      change scal r (algebraMap R W v) = 0
      rw [← scal_specMap, ← h, ← Category.assoc, scal_specMap, Ideal.Quotient.eq_zero_iff_mem.2 hv]
      simp [scal]
    exact fun w hw => this hw
  obtain ⟨r', hr⟩ := exists_lift_quot _ r hk
  refine ⟨r', hr, splitTorus_left_hom_ext _ _ ?_ fun χ => ?_⟩
  · rw [← cancel_mono (thick R I e), Category.assoc, Category.assoc, Category.assoc, h,
      ← Category.assoc (pt I e a).left, pt_hom, lev_thick, ← hr]
    exact (Category.assoc _ _ _).symm
  · rw [hχ, ← hr, scal_comp, ← pt_char, Scheme.Hom.comp_appTop]
    rfl

variable {G : Over (Spec (CommRingCat.of R))}
  (i : ∀ e, splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X ⟶ thickObj R I e G)

def gpt (a : Multiplicative X →* Wˣ) (e : ℕ) :
    Spec (CommRingCat.of (W ⧸ (I.map (algebraMap R W)) ^ (e + 1))) ⟶ G.left :=
  (pt I e a).left ≫ (i e).left ≫ pullback.fst G.hom (thick R I e)

theorem gpt_hom (a : Multiplicative X →* Wˣ) (e : ℕ) : gpt I i a e ≫ G.hom =
    adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) := by
  rw [← lev_thick, ← pt_hom I e a, ← Over.w (i e), gpt]
  simp only [Category.assoc]
  congr 2
  exact pullback.condition

theorem isAdicFamily_aux
    (hi : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (i e) (i (e + 1)))
    (a : Multiplicative X →* Wˣ) : IsAdicFamily (I.map (algebraMap R W)) (gpt I i a) := by
  intro e
  obtain ⟨τ, h1, h2, h3⟩ := hi e
  have h4 : adicLevelMap (I.map (algebraMap R W)) (Nat.le_succ (e + 1)) ≫ (pt I (e + 1) a).left =
      (pt I e a).left ≫ τ := by
    refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [← cancel_mono (thick R I (e + 1))]
      simp only [Category.assoc]
      rw [← Category.assoc (pt I (e + 1) a).left, pt_hom, lev_thick, adicLevelMap_ι_assoc,
        ← Category.assoc τ, h1, Category.assoc, thickTrans_comp, ← Category.assoc, pt_hom, lev_thick]
    · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, CommRingCat.hom_comp,
        RingHom.comp_apply, RingHom.comp_apply, h2, pt_char, pt_char, ← scal_comp, adicLevelMap_ι]
  have h5 : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) =
      pullback.fst G.hom (thick R I e) := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [gpt, gpt, ← Category.assoc, h4, Category.assoc, ← Category.assoc τ, h3, Category.assoc, h5]

theorem exists_hom [GrpObj G] [IsLocalRing W] [IsAdicComplete (I.map (algebraMap R W)) W]
    (hi : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (i e) (i (e + 1)))
    (hm : ∀ e, IsMonHom (i e)) (hmono : ∀ e, Mono (i e)) :
    ∃ ι' : (Multiplicative X →* Wˣ) →* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶ G),
      Function.Injective ι' ∧ ∀ (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶ G)
        (a : Multiplicative X →* Wˣ), x = ι' a ↔
        ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ X).left),
          τ ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X).hom ≫ thick R I e =
            r ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) →
          (∀ χ, τ.appTop.hom (charUnit _ X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) →
          τ ≫ (i e).left ≫ pullback.fst G.hom (thick R I e) = r ≫ x.left := by
  have ex := fun a : Multiplicative X →* Wˣ =>
    (existsUnique_over_of_isAdicFamily _ G.hom (isAdicFamily_aux I i hi a) (gpt_hom I i a)).exists
  choose g hg hg' using ex
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R W)))
  let f : (Multiplicative X →* Wˣ) → (T ⟶ G) := fun a => Over.homMk (g a) (hg a)
  have hf : ∀ a e, adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ (f a).left = gpt I i a e := hg'
  have hext : ∀ (x : T ⟶ G) a,
      (∀ e, adicLevelι (I.map (algebraMap R W)) (e + 1) ≫ x.left = gpt I i a e) → x = f a :=
    fun x a h => Over.OverMorphism.ext
      (hom_ext_of_isHausdorff (I.map (algebraMap R W)) fun e => (h e).trans (hf a e).symm)
  have hmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    refine (hext _ _ fun e => ?_).symm
    have := hm e
    let k : Over.mk ((Over.mk (lev I W e)).hom ≫ thick R I e) ⟶ T :=
      Over.homMk (adicLevelι (I.map (algebraMap R W)) (e + 1)) (lev_thick I W e).symm
    have hk : ∀ c, (k ≫ f c).left = (pt I e c ≫ i e).left ≫ pullback.fst G.hom (thick R I e) :=
      fun c => (hf c e).trans (Category.assoc _ _ _).symm
    have h := SplitTorus.mul_left_comp_fst G (thick R I e) (pt I e a ≫ i e) (pt I e b ≫ i e)
      (k ≫ f a) (k ≫ f b) (hk a) (hk b)
    rw [← MonObj.comp_mul, ← MonObj.mul_comp, ← pt_mul] at h
    exact h.trans (Category.assoc _ _ _)
  refine ⟨MonoidHom.mk' f hmul, fun a b hab => ?_, fun x a => ⟨?_, fun h => hext x a fun e => ?_⟩⟩
  · refine MonoidHom.ext fun χ => Units.ext ?_
    refine IsHausdorff.StrictMono.funext' (I.map (algebraMap R W)) (a := fun n => n + 1)
      (strictMono_id.add_const 1) (f := fun _ : Unit => (a χ).val) (g := fun _ => (b χ).val)
      (fun e _ => ?_) |> (congrFun · ())
    have := hmono e
    have : Mono (i e).left := inferInstanceAs (Mono ((Over.forget _).map (i e)))
    have h1 : gpt I i a e = gpt I i b e := by
      rw [← hf, ← hf]; exact congrArg (fun y : T ⟶ G => _ ≫ y.left) hab
    rw [gpt, gpt, cancel_mono] at h1
    have h2 := pt_char I e a χ.toAdd
    rw [h1, pt_char, ← Category.id_comp (adicLevelι _ _), scal_specMap, scal_specMap] at h2
    simp only [scal, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at h2
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1 h2).symm
  · rintro rfl e Z r τ h hχ
    obtain ⟨r', rfl, rfl⟩ := exists_factor I e a r τ h hχ
    rw [Category.assoc, Category.assoc]
    exact congrArg (r' ≫ ·) (hf a e).symm
  · refine (h e _ _ (pt I e a).left ?_ (pt_char I e a)).symm
    rw [← Category.assoc, pt_hom, lev_thick]

end GlobalTheory.UU.FormalTorusPts

namespace GlobalTheory.UU

theorem exists_formalTorus_points :
    AllSet fun {V} _ _ _ {_} {G} _ _ s => ∀ (t : Tower s) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∃ ι' : (Multiplicative s.X →* Wˣ) →* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G), Function.Injective ι' ∧ ∀ (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (a : Multiplicative s.X →* Wˣ), x = ι' a ↔ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ x.left := by
  intro V _ _ _ A G _ _ s t W _ _ _ hW _
  refine FormalTorusPts.exists_hom (IsLocalRing.maximalIdeal V) (fun e => (t.l e).Q.i) t.tor
    (fun e => (t.l e).Q.i_hom) fun e => ?_
  exact ⟨fun a b h => (t.l e).Q.isKernel.hom_ext h (toUnit_unique _ _)⟩

end GlobalTheory.UU
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.AddLevel

theorem expand_alg {S X : Type} [CommRing S] {n : ℕ} (s s₀ : Finset X) (F F' : Fin n → X → S) (σ σ' : Fin n → S)
    (p m : X → S) (θp θm r : S) (tx ty tp tm : X → Sˣ) (Wx Wy Wp Wm kL kM : Sˣ) (k u v : X → X → Sˣ)
    (hx : ∀ i, Wx.val ^ 2 * σ i = ∑ α ∈ s, F i α * (tx α).val)
    (hy : ∀ i, Wy.val ^ 2 * σ' i = ∑ α ∈ s, F' i α * (ty α).val)
    (hp : Wp.val ^ 1 * θp = ∑ a ∈ s₀, p a * (tp a).val) (hm : Wm.val ^ 1 * θm = ∑ a ∈ s₀, m a * (tm a).val)
    (hadd : ∑ i, σ i * σ' i = r * kL.val * (θp * θm))
    (hk : Wx ^ 2 * Wy ^ 2 * kL = kM * (Wp * Wm))
    (ht : ∀ a b, kM * (tp a * tm b) = k a b * (u a b * v a b)) :
    ∑ α ∈ s, ∑ β ∈ s, (∑ i, F i α * F' i β) * ((tx α).val * (ty β).val) =
      ∑ a ∈ s₀, ∑ b ∈ s₀, r * (k a b).val * (p a * m b) * ((u a b).val * (v a b).val) := by
  have hk' := congrArg Units.val hk
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hk'
  have e₁ : ∑ α ∈ s, ∑ β ∈ s, (∑ i, F i α * F' i β) * ((tx α).val * (ty β).val) =
      ∑ i, (∑ α ∈ s, F i α * (tx α).val) * (∑ β ∈ s, F' i β * (ty β).val) := by
    simp only [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm (s := Finset.univ)]
    exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun i _ => by ring
  have e₂ : ∑ a ∈ s₀, ∑ b ∈ s₀, r * (k a b).val * (p a * m b) * ((u a b).val * (v a b).val) =
      r * kM.val * ((∑ a ∈ s₀, p a * (tp a).val) * (∑ b ∈ s₀, m b * (tm b).val)) := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h := congrArg Units.val (ht a b)
    simp only [Units.val_mul] at h
    linear_combination (-(r * p a * m b)) * h
  have e₃ : ∑ i, Wx.val ^ 2 * σ i * (Wy.val ^ 2 * σ' i) = Wx.val ^ 2 * Wy.val ^ 2 * ∑ i, σ i * σ' i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e₁, e₂, ← hp, ← hm]
  simp only [← hx, ← hy]
  rw [e₃, hadd]
  linear_combination (r * θp * θm) * hk'

theorem unit_alg {U : Type} [CommGroup U] {k p m c₁ c₂ c₃ d₁ d₂ u v : U}
    (h : p * m * (c₁ * c₂ * c₃) = u * v * (d₁ * d₂)) :
    k * (p * m) = k * d₁ * d₂ * (c₁ * c₂ * c₃)⁻¹ * (u * v) := by
  rw [eq_mul_inv_of_mul_eq h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {e : ℕ}

noncomputable def toG (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
    map_mul (pushHom (isGrpPullback_pullback G (thick R I e)) T) x y

noncomputable def toB (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ g.pG) (GlobalTheory.TorusCoord.im_mul g)

theorem lift_snd_left {S : Scheme.{0}} {T B : Over S} (x : T ⟶ B) :
    (lift (toUnit T) x).left ≫ (snd (𝟙_ _) B).left = x.left := by
  rw [← Over.comp_left, lift_snd]

theorem lift_fst_left {S : Scheme.{0}} {T B : Over S} (x : T ⟶ B) :
    (lift (toUnit T) x).left ≫ (fst (𝟙_ _) B).left = (toUnit T).left := by
  rw [← Over.comp_left, lift_fst]

theorem exp_at (U : PreU I D A G) {k : ℕ} {σ : U.SecGT (𝟙_ _) k} {f : ∀ α, SecBT D (𝟙_ _) k α}
    (h : U.ExpT (𝟙_ _) k σ f) (e : ℕ) : ∃ s : Finset D.X,
      ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : T ⟶ thickObj R I e G) (z : T.left) (JG) (J),
      Good U.P.L.L z JG → Good D.P.L z J →
      (∀ α ∉ s, sval (Z := T.left) (f α) (lift (toUnit _) (toB (U.gt e) T x)).left z J = 0) ∧ ∀ s', s ⊆ s' →
      (gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => JG (x.left ≫ (fstG I e G).left))).val ^ k *
          sval (Z := T.left) σ (lift (toUnit _) (toG G T x)).left z JG =
        ∑ α ∈ s', sval (Z := T.left) (f α) (lift (toUnit _) (toB (U.gt e) T x)).left z J *
          (val ((U.gt e).t α) x.left z J).val := by
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, fun T x z JG J hG hJ => ?_⟩
  obtain ⟨h₁, h₂⟩ := hs T.left x.left (lift (toUnit _) (toG G T x)).left (lift (toUnit _) (toB (U.gt e) T x)).left
    (lift_snd_left _) (lift_snd_left _) ((lift_fst_left _).trans (lift_fst_left _).symm) z JG J hG hJ
  refine ⟨h₁, fun s' hs' => h₂.trans (Finset.sum_subset hs' fun α _ hα => ?_)⟩
  rw [h₁ α hα, zero_mul]

theorem val_t_add (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {J}
    (hJ : Good D.P.L z J) (a b : D.X) (x : T ⟶ thickObj R I e G) :
    val (g.t (a + b)) x.left z J * @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
      (cT D _ a) (cT D _ b) (toB g T x)) = val (g.t a) x.left z J * val (g.t b) x.left z J := by
  refine Eq.trans ?_ ((val_corr hJ (g.t_mul a b) x.left).trans (val_mul hJ _ _ _))
  refine Eq.trans ?_ (val_mul hJ _ _ _).symm
  refine congrArg (_ * ·) (Eq.trans ?_ (val_cub D.cub ((Over.map (thick R I e)).map x) hJ _ _ _).symm)
  have e₁ : ∀ c : D.X, (Over.map (thick R I e)).map x ≫ toUnit _ ≫ D.c c = cT D _ c := fun c => by
    rw [← Category.assoc, comp_toUnit]
  rw [e₁, e₁]
  rfl
end

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {e : ℕ}

theorem additionFormulaFactor_comparisonIso_value (U : PreU I D A G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {z : T.left} {JG} {J}
    (hG : Good U.P.L.L z JG) (hJ : Good D.P.L z J) (W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ)
    (hW : ∀ x, W x = gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => JG (x.left ≫ (fstG I e G).left)))
    (x y : T ⟶ thickObj R I e G) :
    W x ^ 2 * W y ^ 2 * @id (T.left.presheaf.stalk z)ˣ
        (kap0 U.P.c U.P.sym (T := (Over.map (thick R I e)).obj T) z JG (toG G T x) (toG G T y)) =
      @id (T.left.presheaf.stalk z)ˣ
        (kap0 D.cub D.sym (T := (Over.map (thick R I e)).obj T) z J (toB (U.gt e) T x) (toB (U.gt e) T y)) *
        (W (x * y) * W (x * y⁻¹)) := by
  obtain ⟨h₁, h₂, h₃⟩ := U.w_vals e T z JG J hG hJ W hW
  have h := GlobalTheory.addition_factor_through_cubical_even_iso _ _ W _ _
    (fun a b c => cubV U.P.c (T := (Over.map (thick R I e)).obj T) z JG (toG G T a) (toG G T b) (toG G T c))
    (fun a b c => cubV D.cub (T := (Over.map (thick R I e)).obj T) z J (toB (U.gt e) T a) (toB (U.gt e) T b)
      (toB (U.gt e) T c)) _ _ h₁ h₂ h₃ x y
  simp only [map_inv] at h
  exact h

theorem torusCoordinate_sum_difference_additionFactor (hGF : GlobalFnsSt) (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {z : T.left} {J} (hJ : Good D.P.L z J) (x y : T ⟶ thickObj R I e G) (a b : D.X) :
    @id (T.left.presheaf.stalk z)ˣ
        (kap0 D.cub D.sym (T := (Over.map (thick R I e)).obj T) z J (toB g T x) (toB g T y)) *
        (val (g.t a) (x * y).left z J * val (g.t b) (x * y⁻¹).left z J) =
      @id (T.left.presheaf.stalk z)ˣ (kapV D a b (T := (Over.map (thick R I e)).obj T) z J (toB g T x) (toB g T y)) *
        (val (g.t (a + b)) x.left z J * val (g.t (a - b)) y.left z J) :=
  unit_alg (GlobalTheory.cub_coord_mul_mul_inv _ (T.left.presheaf.stalk z)ˣ D.X
    (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J)
    (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ) _ (toB g T) (cT D _)
    (fun a b => (congrArg (toUnit _ ≫ ·) (D.c_add a b)).trans (MonObj.comp_mul _ _ _))
    (fun a x => val (g.t a) x.left z J) (val_t_add g hJ)
    (fun a x y => torus_coord_add hGF R I D e G g T x y a z J hJ) a b x y)

theorem at_points (hGF : GlobalFnsSt) (U : PreU I D A G) (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : R)
    (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α) (hA : U.AddG θ r σ σ')
    (hθ : U.ExpT (𝟙_ _) 1 θ f₀) (hσ : ∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) (e : ℕ) :
    ∃ s₀ : Finset D.X, ∀ (T' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x' y' : T' ⟶ thickObj R I e G)
      (x y : (Over.map (thick R I e)).obj T' ⟶ D.P.A), x = toB (U.gt e) T' x' → y = toB (U.gt e) T' y' →
      ∀ (z : ((Over.map (thick R I e)).obj T').left) (J), Good D.P.L z J →
      (∀ a ∉ s₀, sval (f₀ a) (lift (toUnit _) (x * y)).left z J = 0 ∧
        sval (f₀ a) (lift (toUnit _) (x * y⁻¹)).left z J = 0) ∧ ∀ s : Finset D.X, s₀ ⊆ s →
      ∑ α ∈ s, ∑ β ∈ s, (∑ i, sval (f i α) (lift (toUnit _) x).left z J * sval (f' i β) (lift (toUnit _) y).left z J) *
        ((val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t α) x'.left z J).val *
          (val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t β) y'.left z J).val) =
      ∑ a ∈ s₀, ∑ b ∈ s₀, gs (𝟙 _) z ⊤ (scal ((Over.map (thick R I e)).obj T').hom r) * (kapV D a b z J x y).val *
        (sval (f₀ a) (lift (toUnit _) (x * y)).left z J * sval (f₀ b) (lift (toUnit _) (x * y⁻¹)).left z J) *
        ((val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t (a + b)) x'.left z J).val *
          (val (Z := ((Over.map (thick R I e)).obj T').left) ((U.gt e).t (a - b)) y'.left z J).val) := by
  classical
  obtain ⟨s₁, h₁⟩ := exp_at U hθ e
  choose s₂ h₂ using fun i => exp_at U (hσ i).1 e
  choose s₃ h₃ using fun i => exp_at U (hσ i).2 e
  obtain ⟨s₀, a₁, a₂, a₃⟩ : ∃ s₀ : Finset D.X, s₁ ⊆ s₀ ∧ (∀ i, s₂ i ⊆ s₀) ∧ ∀ i, s₃ i ⊆ s₀ :=
    ⟨s₁ ∪ (Finset.univ.biUnion s₂ ∪ Finset.univ.biUnion s₃), Finset.subset_union_left,
      fun i => ((Finset.subset_biUnion_of_mem s₂ (Finset.mem_univ i)).trans Finset.subset_union_left).trans
        Finset.subset_union_right,
      fun i => ((Finset.subset_biUnion_of_mem s₃ (Finset.mem_univ i)).trans Finset.subset_union_right).trans
        Finset.subset_union_right⟩
  refine ⟨s₀, fun T x y _ _ hx hy z J hJ => ?_⟩
  subst hx hy
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have p := h₁ T (x * y) z JG J hG hJ
  have m := h₁ T (x * y⁻¹) z JG J hG hJ
  simp only [map_mul, map_inv] at p m
  refine ⟨fun a ha => ⟨p.1 a fun h => ha (a₁ h), m.1 a fun h => ha (a₁ h)⟩, fun s hs => ?_⟩
  exact expand_alg s s₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun i => (h₂ i T x z JG J hG hJ).2 s ((a₂ i).trans hs)) (fun i => (h₃ i T y z JG J hG hJ).2 s ((a₃ i).trans hs))
    (p.2 s₀ a₁) (m.2 s₀ a₁) (hA _ (toG G T x) (toG G T y) z JG hG) (additionFormulaFactor_comparisonIso_value U hG hJ _ (fun _ => rfl) x y)
    (torusCoordinate_sum_difference_additionFactor hGF (U.gt e) hJ x y)

end

end GlobalTheory.AddLevel

theorem GlobalTheory.addition_formula_expanded_at_level : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → ∀ e : ℕ, ∃ s₀ : Finset D.X, ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (U.gt e).pG.left = x.left → ye ≫ (U.gt e).pG.left = y.left → xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom = ye ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom → ∀ (z : T.left) (J), Good D.P.L z J → (∀ a ∉ s₀, sval (f₀ a) (lift (toUnit T) (x * y)).left z J = 0 ∧ sval (f₀ a) (lift (toUnit T) (x * y⁻¹)).left z J = 0) ∧ ∀ s : Finset D.X, s₀ ⊆ s → ∑ α ∈ s, ∑ β ∈ s, (∑ i, sval (f i α) (lift (toUnit T) x).left z J * sval (f' i β) (lift (toUnit T) y).left z J) * ((val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val) = ∑ a ∈ s₀, ∑ b ∈ s₀, gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val * (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J) * ((val ((U.gt e).t (a + b)) xe z J).val * (val ((U.gt e).t (a - b)) ye z J).val)) := by
  intro hGF V _ _ _ _ D A G _ _ U θ f₀ r n σ σ' f f' hA hθ hσ e
  obtain ⟨s₀, H⟩ := GlobalTheory.AddLevel.at_points hGF U θ f₀ r n σ σ' f f' hA hθ hσ e
  refine ⟨s₀, fun T x y xe ye hx hy hxy => ?_⟩
  have hT : T.hom = (xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom) ≫ thick V (IsLocalRing.maximalIdeal V) e := by
    rw [← Over.w x, ← hx, Category.assoc, Over.w, Category.assoc]
    rfl
  obtain ⟨Z, ⟨⟨⟩⟩, h⟩ := T
  change Z ⟶ _ at xe ye
  change h = (CategoryStruct.comp (X := Z) xe (thickObj V (IsLocalRing.maximalIdeal V) e G).hom ≫
    thick V (IsLocalRing.maximalIdeal V) e : Z ⟶ _) at hT
  subst hT
  exact H (Over.mk (xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom)) (Over.homMk xe rfl)
    (Over.homMk ye hxy.symm) x y (Over.OverMorphism.ext hx.symm) (Over.OverMorphism.ext hy.symm)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem HidaSetting.smoothDim_model : AllSet fun {_} _ _ _ {A} {G} _ _ _ => SmoothOfRelativeDimension A.g G.hom := by
  intro V _ _ _ A G _ _ s
  letI : (Over.pullback (jK V)).Monoidal :=
    (Over.instBraidedPullback (f := jK V)).toMonoidal
  letI : GrpObj ((Over.pullback (jK V)).obj G) :=
    Functor.grpObjObj (F := Over.pullback (jK V)) (G := G)
  have hs : Smooth G.hom := s.semi.smooth
  have : GeometricallyConnected G.hom := s.semi.geomConnected
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have a := A.smoothDim
  have b : SmoothOfRelativeDimension (0 + A.g) ((Over.pullback (jK V)).obj G).hom := by
    have : IsIso s.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map s.gen.hom))
    rw [← Over.w s.gen.hom]; infer_instance
  have c : SmoothOfRelativeDimension n ((Over.pullback (jK V)).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hn
  have h₁ : n = A.g :=
    (H1.dim_unique _ c b (eSec _ (Classical.arbitrary (Spec (CommRingCat.of (FractionRing V)))))).trans (zero_add _)
  exact h₁ ▸ hn

theorem Tower.dim_eq_add_finrank : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (g' : ℕ), (SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X) ∧ ∀ a : t.Alg, SmoothOfRelativeDimension g' a.B.hom → A.g = g' + Module.finrank ℤ s.X := by
  intro V _ _ _ A G _ _ s t g'
  have hG : SmoothOfRelativeDimension A.g G.hom := HidaSetting.smoothDim_model V A G s
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by simpa using (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
  have h₀ : SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X := fun h =>
    TQ.dim_eq_add_finrank _ s.X _ (t.l 0).Q A.g g'
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG) h
  refine ⟨h₀, fun a ha => h₀ ?_⟩
  obtain ⟨h, -⟩ := a.b_pb 0
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 ha

end GlobalTheory.UU
end
