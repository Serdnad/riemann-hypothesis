module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle013
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_id isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.LieComb

open GlobalTheory.SqZero

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR R ⟶ G)}

theorem isLieComb_iff_tanExp (c : Fin n → R) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = tanExp v c := isLieComb_iff_lieExp c w

theorem isTangent_tanExp (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) : IsTangent (tanExp v c) :=
  (isTan_iff _).1 (isTanOver_tanExp hv c)

def combHom (hv : ∀ i, IsTangent (v i)) :
    (Fin n → R) →+ Additive (sp (R₀ := R) (DualNumber R) ⟶ G) :=
  AddMonoidHom.mk' (fun c => Additive.ofMul (tanExp v c)) (fun c c' => by
    rw [← ofMul_mul]
    refine congrArg Additive.ofMul ?_
    rw [← lieExp_add hv _ _ _ _ (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
      (fun _ => by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
    exact lieExp_congr _ (fun i => TrivSqZeroExt.inr_add _ _ _) _ _)

theorem tanExp_tanExp (hv : ∀ i, IsTangent (v i)) {m : ℕ} (M : Fin m → Fin n → R)
    (c : Fin m → R) : tanExp (fun i => tanExp v (M i)) c = tanExp v (∑ i, c i • M i) := by
  change _ = (combHom hv (∑ i, c i • M i)).toMul

  rw [map_sum, toMul_sum, tanExp, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine (comp_lieExp v _ _ _).trans ?_
  exact lieExp_congr _ (fun j => by
    simp [epsTo, dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr,
      mul_comm, smul_smul]) _ _

theorem tanExp_single (hv : ∀ i, IsTangent (v i)) (i : Fin n) :
    tanExp v (Pi.single i (1 : R)) = v i := by
  rw [tanExp, lieExp, Finset.prod_eq_single i]
  · have : ∀ h, epsTo R (inr ((Pi.single i (1 : R) : Fin n → R) i) : DualNumber R) h =
        AlgHom.id R _ := fun h => DualNumber.algHom_ext (by
      rw [epsTo_eps, Pi.single_eq_same]; rfl)
    rw [this, spMap_id]
    exact Category.id_comp _
  · intro j _ hj
    exact epsTo_zero_comp ((isTan_iff _).2 (hv j)) _ (by simp [Pi.single_eq_of_ne hj]) _
  · simp

theorem isLieBasis_iff_isUnit_det (hv : IsLieBasis v) (M : Matrix (Fin n) (Fin n) R) :
    IsLieBasis (fun i => tanExp v (M i)) ↔ IsUnit M.det := by
  have key : ∀ c : Fin n → R,
      tanExp (fun i => tanExp v (M i)) c = tanExp v (Matrix.vecMul c M) := fun c => by
    rw [Matrix.vecMul_eq_sum]
    exact tanExp_tanExp hv.1 (fun i => M i) c
  have hinj : Function.Injective (fun c : Fin n → R => tanExp v c) := by
    intro a b hab
    obtain ⟨c, hc, hu⟩ := hv.2 (tanExp v b) (isTangent_tanExp hv.1 b)
    have ha : IsLieComb a v (tanExp v b) :=
      (isLieComb_iff_tanExp _ _).2 hab.symm
    have hb : IsLieComb b v (tanExp v b) :=
      (isLieComb_iff_tanExp _ _).2 rfl
    exact (hu a ha).trans (hu b hb).symm
  rw [← Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h
    refine Matrix.vecMul_surjective_iff_isUnit.1 fun d => ?_
    obtain ⟨c, hc, -⟩ := h.2 _ (isTangent_tanExp hv.1 d)
    rw [isLieComb_iff_tanExp, key] at hc
    exact ⟨c, (hinj hc).symm⟩
  · intro h
    refine ⟨fun i => isTangent_tanExp hv.1 _, fun w hw => ?_⟩
    obtain ⟨d, hd, -⟩ := hv.2 w hw
    obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.2 h d
    have hc' : Matrix.vecMul c M = d := hc
    rw [isLieComb_iff_tanExp] at hd
    refine ⟨c, ?_, fun c' h' => ?_⟩
    · change IsLieComb _ _ _
      rw [isLieComb_iff_tanExp, key, hc', hd]
    · change IsLieComb _ _ _ at h'
      rw [isLieComb_iff_tanExp, key, hd, ← hc'] at h'
      exact Matrix.vecMul_injective_of_isUnit h (hinj h').symm

theorem lieComb_algebra (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (hv : ∀ i, IsTangent (v i)) :
    (∀ c, ∃! w, IsLieComb c v w) ∧ (∀ c w, IsLieComb c v w → IsTangent w) ∧
    (∀ (m : ℕ) (M : Fin m → Fin n → R) (v' : Fin m → (epsR R ⟶ G)) (c : Fin m → R) (w),
      (∀ i, IsLieComb (M i) v (v' i)) → IsLieComb c v' w → IsLieComb (∑ i, c i • M i) v w) ∧
    (∀ i, IsLieComb (Pi.single i 1) v (v i)) ∧
    ∀ (M : Matrix (Fin n) (Fin n) R) (v' : Fin n → (epsR R ⟶ G)), IsLieBasis v →
      (∀ i, IsLieComb (M i) v (v' i)) → (IsLieBasis v' ↔ IsUnit M.det) := by
  refine ⟨fun c => ⟨tanExp v c, (isLieComb_iff_tanExp _ _).2 rfl,
    fun w hw => (isLieComb_iff_tanExp _ _).1 hw⟩, fun c w hw => ?_, fun m M v' c w hM hw => ?_,
    fun i => (isLieComb_iff_tanExp _ _).2 (tanExp_single hv i).symm, fun M v' hb hM => ?_⟩
  · rw [(isLieComb_iff_tanExp _ _).1 hw]
    exact isTangent_tanExp hv c
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    rw [isLieComb_iff_tanExp] at hw ⊢
    rw [hw, tanExp_tanExp hv]
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    exact isLieBasis_iff_isUnit_det hb M

end GlobalTheory.LieComb
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T Y' T' : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

theorem affine_gs_appLE {Z : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ W) (f : Γ(X, U)) : gs r z W ((q.appLE U W e).hom f) = gs (r ≫ q) z U f :=
  (gs_res r z e hz _).trans (gs_pull r q z U (e hz) f)

theorem affine_comb (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (j : Y' ⟶ Y) (p₁' : Y' ⟶ T') (g : T' ⟶ T) (w : j ≫ p₁ = p₁' ≫ g) (e : ⊤ ≤ g ⁻¹ᵁ W)
    (c : Fin N → Γ(T, W)) (z : Y') (i : L.ι) (h₂ : p₂ (j z) ∈ L.U i) :
    comb b p₁' (j ≫ p₂) ⊤ (fun k => (g.appLE W ⊤ e).hom (c k)) z i =
      (j.stalkMap z).hom (comb b p₁ p₂ W c (j z) i) := by
  have h₁ : p₁ (j z) ∈ W := by
    have : (j ≫ p₁) z ∈ W := by rw [w]; exact e (show p₁' z ∈ (⊤ : T'.Opens) from trivial)
    exact this
  rw [← comb_comp b j p₁ p₂ W c z i h₁ h₂, comb, comb]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [affine_gs_appLE g W ⊤ e p₁' z trivial, w]

theorem affine_transfer (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (j : Y' ⟶ Y) (p₁' : Y' ⟶ T') (g : T' ⟶ T) [IsOpenImmersion g] (sq : IsPullback j p₁' p₁ g)
    (hr : Set.range g = W) (e : ⊤ ≤ g ⁻¹ᵁ W) (hb : Function.Bijective (g.appLE W ⊤ e).hom)
    (h₁ : IndepOn b p₁' (j ≫ p₂) ⊤) (h₂ : SpanOn b p₁' (j ≫ p₂) ⊤) :
    IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W := by
  have hj : IsOpenImmersion j := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  have hW : ∀ z : Y', p₁ (j z) ∈ W := fun z => by
    have : (j ≫ p₁) z ∈ W := by rw [sq.w]; exact e (show p₁' z ∈ (⊤ : T'.Opens) from trivial)
    exact this
  refine ⟨fun c hc => ?_, fun σ hσ => ?_⟩
  · have := h₁ (fun k => (g.appLE W ⊤ e).hom (c k)) (fun z i _ hz => by
      rw [affine_comb b p₁ p₂ W j p₁' g sq.w e c z i hz, hc (j z) i (hW z) hz, map_zero])
    funext k
    apply hb.1
    rw [Pi.zero_apply, map_zero]
    exact congrFun this k
  · have le : ∀ i, p₁' ⁻¹ᵁ ⊤ ⊓ (j ≫ p₂) ⁻¹ᵁ L.U i ≤ j ⁻¹ᵁ (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i) :=
      fun i z hz => ⟨hW z, hz.2⟩
    have key : ∀ (z : Y') (i : L.ι), p₂ (j z) ∈ L.U i →
        gs (𝟙 Y') z _ ((j.appLE _ _ (le i)).hom (σ i)) = (j.stalkMap z).hom (gs (𝟙 Y) (j z) _ (σ i)) := by
      intro z i hz
      rw [affine_gs_appLE j _ _ (le i) (𝟙 Y') z ⟨trivial, hz⟩, Category.id_comp,
        ← gs_comp j (𝟙 Y) z (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i) ⟨hW z, hz⟩, Category.comp_id]
    obtain ⟨c', hc'⟩ := h₂ (fun i => (j.appLE _ _ (le i)).hom (σ i)) (fun z i i' _ hi hi' => by
      rw [key z i hi, key z i' hi', hσ (j z) i i' (hW z) hi hi', map_mul]
      congr 1
      have : gm (j ≫ p₂) z (L.U i ⊓ L.U i') (L.g i i') =
          Units.map (j.stalkMap z).hom.toMonoidHom (gm p₂ (j z) (L.U i ⊓ L.U i') (L.g i i')) := by
        apply Units.ext
        rw [← gs_unit (j ≫ p₂) z (L.U i ⊓ L.U i') ⟨hi, hi'⟩, gs_comp j p₂ z (L.U i ⊓ L.U i') ⟨hi, hi'⟩,
          gs_unit p₂ (j z) (L.U i ⊓ L.U i') ⟨hi, hi'⟩]
        rfl
      rw [this, ← map_zpow (Units.map (j.stalkMap z).hom.toMonoidHom)]
      rfl)
    choose c hc using fun k => hb.2 (c' k)
    refine ⟨c, fun y i hy hi => ?_⟩
    obtain ⟨s, hs⟩ : p₁ y ∈ Set.range g := by rw [hr]; exact hy
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback sq y s hs.symm
    apply (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1
    have := hc' z i trivial hi
    rw [key z i hi, ← funext hc, affine_comb b p₁ p₂ W j p₁' g sq.w e c z i hi] at this
    exact this

theorem indepOn_spanOn_of_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), (∀ (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (Y : Scheme.{0}) (p₁ : Y ⟶ Sp R') (p₂ : Y ⟶ X), IsPullback p₂ p₁ p (spMap f) ∧ GlobalTheory.RelBasis.IndepOn b p₁ p₂ ⊤ ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ ⊤) → ∀ (T Y : Scheme.{0}) (q : T ⟶ Sp R) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), IsPullback p₂ p₁ p q → ∀ W : T.Opens, IsAffineOpen W → GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W := by
  intro R _ X p L t N b H T Y q p₁ p₂ sq W hW
  obtain ⟨Y', p₁', p₂', sq', h₁, h₂⟩ := H Γ(T, W) (Spec.preimage (hW.fromSpec ≫ q)).hom
  have hf : spMap (Spec.preimage (hW.fromSpec ≫ q)).hom = hW.fromSpec ≫ q := Spec.map_preimage _
  rw [hf] at sq'
  let j : Y' ⟶ Y := sq.lift p₂' (p₁' ≫ hW.fromSpec) (by rw [sq'.w, Category.assoc])
  have e₂ : j ≫ p₂ = p₂' := sq.lift_fst _ _ _
  have e₁ : j ≫ p₁ = p₁' ≫ hW.fromSpec := sq.lift_snd _ _ _
  rw [← e₂] at sq' h₁ h₂
  have sq'' : IsPullback j p₁' p₁ hW.fromSpec := IsPullback.of_right (by simpa using sq') e₁ sq
  have e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
  refine affine_transfer b p₁ p₂ W j p₁' hW.fromSpec sq'' hW.range_fromSpec e ?_ h₁ h₂
  have : hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(T, W)).inv := by
    rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ ((congrArg _ (Subsingleton.elim _ _)).trans (CategoryTheory.Functor.map_id _ _))).trans
      (Category.comp_id _)
  rw [this]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(T, W)).inv

end GlobalTheory.RelBasis
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

theorem comb_res (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) {V W : T.Opens} (hle : V ≤ W)
    (c : Fin N → Γ(T, W)) (y : Y) (i : L.ι) (h : p₁ y ∈ V) :
    comb b p₁ p₂ V (fun k => (T.presheaf.map (homOfLE hle).op).hom (c k)) y i = comb b p₁ p₂ W c y i := by
  unfold comb
  exact Finset.sum_congr rfl fun k _ => by rw [gs_res p₁ y hle h]

theorem comb_sub (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) {W : T.Opens}
    (c c' : Fin N → Γ(T, W)) (y : Y) (i : L.ι) (h : p₁ y ∈ W) :
    comb b p₁ p₂ W (c - c') y i = comb b p₁ p₂ W c y i - comb b p₁ p₂ W c' y i := by
  unfold comb
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gs_eq_gsHom p₁ y W h, Pi.sub_apply, map_sub, sub_mul]

theorem exists_affine_le (W : T.Opens) (x : T) (hx : x ∈ W) :
    ∃ V : T.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ W := by
  obtain ⟨V, hV, hxV, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens) hx
  exact ⟨V, hV, hxV, hle⟩

theorem indepOn_of_affine (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X)
    (H : ∀ W : T.Opens, IsAffineOpen W → IndepOn b p₁ p₂ W) (W : T.Opens) : IndepOn b p₁ p₂ W := by
  intro c hc
  funext k
  refine fn_ext fun x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le W x hx
  have h0 := H V hV (fun k => (T.presheaf.map (homOfLE hle).op).hom (c k)) fun y i h₁ h₂ =>
    (comb_res b p₁ p₂ hle c y i h₁).trans (hc y i (hle h₁) h₂)
  have hk : (T.presheaf.map (homOfLE hle).op).hom (c k) = 0 := congrFun h0 k
  have hxV' : (𝟙 T : T ⟶ T) x ∈ V := hxV
  rw [← gs_res (𝟙 T) x hle hxV', ← gs_res (𝟙 T) x hle hxV', hk, Pi.zero_apply, map_zero]

theorem basis_of_affine (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t))
    (p₁ : Y ⟶ T) (p₂ : Y ⟶ X)
    (H : ∀ W : T.Opens, IsAffineOpen W → IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W) (W : T.Opens) :
    IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W := by
  have hI := indepOn_of_affine b p₁ p₂ fun W hW => (H W hW).1
  refine ⟨hI W, fun σ hσ => ?_⟩
  let Ix := {V : T.Opens // IsAffineOpen V ∧ V ≤ W}
  have hloc : ∀ V : Ix, ∃ c : Fin N → Γ(T, V.1), ∀ (y : Y) (i : L.ι), p₁ y ∈ V.1 → p₂ y ∈ L.U i →
      gs (𝟙 Y) y _ (σ i) = comb b p₁ p₂ V.1 c y i := by
    intro V
    have hle : ∀ i, p₁ ⁻¹ᵁ V.1 ⊓ p₂ ⁻¹ᵁ L.U i ≤ p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i := fun i y hy => ⟨V.2.2 hy.1, hy.2⟩
    have hr : ∀ (y : Y) i, p₁ y ∈ V.1 → p₂ y ∈ L.U i →
        gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (hle i)).op).hom (σ i)) = gs (𝟙 Y) y _ (σ i) :=
      fun y i h₁ h₂ => gs_res (𝟙 Y) y (hle i) ⟨h₁, h₂⟩ _
    obtain ⟨c, hc⟩ := (H V.1 V.2.1).2 (fun i => (Y.presheaf.map (homOfLE (hle i)).op).hom (σ i))
      (fun y i i' h₁ h₂ h₃ => (hr y i h₁ h₂).trans ((hσ y i i' (V.2.2 h₁) h₂ h₃).trans
        (congrArg _ (hr y i' h₁ h₃).symm)))
    exact ⟨c, fun y i h₁ h₂ => (hr y i h₁ h₂).symm.trans (hc y i h₁ h₂)⟩
  choose c hc using hloc
  have hcomp : ∀ V V' : Ix, (fun k => (T.presheaf.map (homOfLE (inf_le_left : V.1 ⊓ V'.1 ≤ V.1)).op).hom (c V k)) =
      (fun k => (T.presheaf.map (homOfLE (inf_le_right : V.1 ⊓ V'.1 ≤ V'.1)).op).hom (c V' k)) := by
    intro V V'
    refine sub_eq_zero.1 (hI (V.1 ⊓ V'.1) _ fun y i h₁ h₂ => ?_)
    rw [comb_sub b p₁ p₂ _ _ y i h₁, comb_res b p₁ p₂ _ _ y i h₁, comb_res b p₁ p₂ _ _ y i h₁,
      ← hc V y i h₁.1 h₂, ← hc V' y i h₁.2 h₂, sub_self]
  have glue : ∀ k, ∃ a : Γ(T, W), ∀ V : Ix, (T.presheaf.map (homOfLE V.2.2).op).hom a = c V k := by
    intro k
    obtain ⟨a, ha, -⟩ := T.sheaf.existsUnique_gluing' (fun V : Ix => V.1) W (fun V => homOfLE V.2.2)
      (fun x hx => by
        obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le W x hx
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hle⟩, hxV⟩) (fun V => c V k)
      (fun V V' => congrFun (hcomp V V') k)
    exact ⟨a, ha⟩
  choose a ha using glue
  refine ⟨a, fun y i h₁ h₂ => ?_⟩
  obtain ⟨V, hV, hyV, hle⟩ := exists_affine_le W (p₁ y) h₁
  rw [hc ⟨V, hV, hle⟩ y i hyV h₂, ← comb_res b p₁ p₂ hle a y i hyV]
  exact congrArg (fun c => comb b p₁ p₂ V c y i) (funext fun k => (ha k ⟨V, hV, hle⟩).symm)

end GlobalTheory.RelBasis
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

theorem boxSpan_of_indep_span (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t))
    (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (hL : L.IsLB) (H : ∀ W : T.Opens, IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W) :
    BoxSpan b p₁ p₂ := by
  intro K _ φ ε s
  have mem : ∀ (j : K → L.ι) (i : L.ι) (y : Y), p₁ y ∈ LB.wchart L φ j → p₂ y ∈ L.U i →
      y ∈ LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)) := by
    intro j i y h₁ h₂
    refine Set.mem_iInter.2 ?_
    rintro (k | k)
    exacts [Set.mem_iInter.1 h₁ k, h₂]
  have tr : ∀ (j j' : K → L.ι) (i i' : L.ι) (y : Y), p₁ y ∈ LB.wchart L φ j → p₂ y ∈ L.U i →
      p₁ y ∈ LB.wchart L φ j' → p₂ y ∈ L.U i' →
      gs (𝟙 Y) y (LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)))
          (s.f (Sum.elim j (fun _ => i))) =
        (trF φ ε p₁ y j j').val * (gm p₂ y (L.U i ⊓ L.U i') (L.g i i') ^ t).val *
        gs (𝟙 Y) y (LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j' (fun _ => i')))
          (s.f (Sum.elim j' (fun _ => i'))) := by
    intro j j' i i' y h₁ h₂ h₁' h₂'
    rw [sec_trans s (𝟙 Y) y (mem j i y h₁ h₂) (mem j' i' y h₁' h₂'), trF, Fintype.prod_sum_type, Units.val_mul,
      @Fintype.prod_unique _ PUnit]
    simp only [trF, Category.id_comp, Sum.elim_inl, Sum.elim_inr]
    rfl
  have hc : ∀ j : K → L.ι, ∃ c : Fin N → Γ(T, LB.wchart L φ j), ∀ (y : Y) (i : L.ι), p₁ y ∈ LB.wchart L φ j →
      p₂ y ∈ L.U i →
      gs (𝟙 Y) y (LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)))
          (s.f (Sum.elim j (fun _ => i))) = comb b p₁ p₂ _ c y i := by
    intro j
    have le : ∀ i, p₁ ⁻¹ᵁ LB.wchart L φ j ⊓ p₂ ⁻¹ᵁ L.U i ≤
        LB.wchart L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim j (fun _ => i)) :=
      fun i y hy => mem j i y hy.1 hy.2
    obtain ⟨c, hc⟩ := (H (LB.wchart L φ j)).2
      (fun i => (Y.presheaf.map (homOfLE (le i)).op).hom (s.f (Sum.elim j (fun _ => i)))) (by
        intro y i i' h₁ h₂ h₂'
        have e := tr j j i i' y h₁ h₂ h₁ h₂'
        rw [mul_eq_left.1 (trF_trans hL φ ε p₁ y h₁ h₁ h₁), Units.val_one, _root_.one_mul] at e
        exact (gs_res (𝟙 Y) y (le i) ⟨h₁, h₂⟩ _).trans
          (e.trans (congrArg _ (gs_res (𝟙 Y) y (le i') ⟨h₁, h₂'⟩ _).symm)))
    exact ⟨c, fun y i h₁ h₂ => (gs_res (𝟙 Y) y (le i) ⟨h₁, h₂⟩ _).symm.trans (hc y i h₁ h₂)⟩
  choose c hc using hc
  have compat : ∀ j j' : K → L.ι, ∀ k,
      (T.presheaf.map (homOfLE (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j k) =
        (show Γ(T, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (T.presheaf.map (homOfLE (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j' k) := by
    intro j j' k
    refine sub_eq_zero.1 (congrFun ((H (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 (fun k =>
      (T.presheaf.map (homOfLE (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j k) -
        (show Γ(T, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (T.presheaf.map (homOfLE (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)).op).hom (c j' k)) ?_) k)
    intro y i h₁ h₂
    have e := tr j j' i i y h₁.1 h₂ h₁.2 h₂
    rw [hc j y i h₁.1 h₂, hc j' y i h₁.2 h₂, gm_self hL p₂ y h₂, one_zpow, Units.val_one, _root_.mul_one, comb, comb,
      Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    refine (Finset.sum_congr rfl fun k _ => ?_).trans e
    have u : gs p₁ y (LB.wchart L φ j ⊓ LB.wchart L φ j')
        (show Γ(T, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val =
        (trF φ ε p₁ y j j').val :=
      (gs_unit p₁ y _ h₁ _).trans (congrArg Units.val (gm_linComb L φ ε p₁ y j j' h₁.1 h₁.2))
    rw [gs_eq_gsHom p₁ y _ h₁, map_sub, ← gs_eq_gsHom, ← gs_eq_gsHom, gs_mul p₁ y _ h₁, u,
      gs_res p₁ y _ h₁, gs_res p₁ y _ h₁, sub_mul, _root_.mul_assoc]
  refine ⟨fun k => ⟨fun j => c j k, fun j j' => compat j j' k⟩, fun Z r z J hJ => ?_⟩
  have h₁ : p₁ (r z) ∈ LB.wchart L φ (fun k => J (r ≫ p₁ ≫ φ k)) :=
    Set.mem_iInter.2 fun k => hJ (r ≫ p₁ ≫ φ k)
  have h₂ : p₂ (r z) ∈ L.U (J (r ≫ p₂)) := hJ (r ≫ p₂)
  have e := (gs_comp r (𝟙 Y) z _ (mem _ _ _ h₁ h₂) _).trans ((congrArg (r.stalkMap z).hom (hc _ (r z) _ h₁ h₂)).trans
    (comb_comp b r p₁ p₂ _ _ z _ h₁ h₂).symm)
  rw [Category.comp_id] at e
  rw [sval_of s r z J (Sum.elim (fun k => J (r ≫ p₁ ≫ φ k)) (fun _ => J (r ≫ p₂))) (by rintro (k | k) <;> rfl)]
  refine e.trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [sval_of _ (r ≫ p₁) z J (fun k => J (r ≫ p₁ ≫ φ k)) (fun k => by rw [Category.assoc])]

end GlobalTheory.RelBasis
end
end
