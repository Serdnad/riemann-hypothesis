module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.DiagMat

def act (M : Matrix (Fin 8) (Fin 8) ℤ) (X : Type) [AddCommGroup X] : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun c := fun v => ∑ u, M v u • c u
  map_zero' := by ext v; simp
  map_add' c d := by ext v; simp [smul_add, Finset.sum_add_distrib]

theorem act_apply (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) (v : Fin 8) :
    act M X c v = ∑ u, M v u • c u := rfl

theorem act_act (M N : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) :
    act M X (act N X c) = act (M * N) X c := by
  ext v
  simp only [act_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem act_one {X : Type} [AddCommGroup X] (c : Fin 8 → X) : act 1 X c = c := by
  ext v
  simp [act_apply, Matrix.one_apply]

theorem act_comp {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁] (M : Matrix (Fin 8) (Fin 8) ℤ)
    (π : X₀ →+ X₁) (c : Fin 8 → X₀) : act M X₁ (fun u => π (c u)) = fun u => π (act M X₀ c u) := by
  ext v

  simp [act_apply, map_sum, map_zsmul]

theorem matRel_iff (W : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (a b : Fin 8) (y y' : Fin 8 → X) :
    MatRel W a b y y' ↔ act (W + W.transpose) X y' = Pi.single b (act (W + W.transpose) X y a) := by
  constructor
  · intro h; ext v; rw [act_apply, h v, Pi.single_apply]; rfl
  · intro h v; have := congrFun h v; rw [act_apply] at this; rw [this, Pi.single_apply]; rfl

end GlobalTheory.Poinc.Eq8.DiagMat


open GlobalTheory.Poinc.Eq8.DiagMat in
theorem GlobalTheory.Poinc.Eq8.exists_diag_of_matRel : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (Y X₀ X₁ : Type) [AddCommGroup Y] [AddCommGroup X₀] [AddCommGroup X₁] (m : Fin 8 → Fin 8 → (Y →+ Y)) (e₀ : Y ≃+ (Fin 8 → X₀)) (ρ : Y →+ (Fin 8 → X₁)), Function.Surjective ρ → (∀ a b y, MatRel W a b (e₀ y) (e₀ (m a b y))) → (∀ a b y, MatRel W a b (ρ y) (ρ (m a b y))) → ∃ π : X₀ →+ X₁, Function.Surjective π ∧ ∀ y u, ρ y u = π (e₀ y u) := by
  intro W hW Y X₀ X₁ _ _ _ m e₀ ρ hρ h₀ h₁
  set Q := W + W.transpose with hQ
  have hdet : IsUnit Q.det := by rw [hW.2]; exact isUnit_one
  have hQP : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
  have hPQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdet

  let Ψ : (Fin 8 → X₀) →+ (Fin 8 → X₁) :=
    (act Q X₁).comp (ρ.comp ((e₀.symm : (Fin 8 → X₀) →+ Y).comp (act Q⁻¹ X₀)))
  have hΨ : ∀ z, Ψ (act Q X₀ (e₀ z)) = act Q X₁ (ρ z) := by
    intro z
    simp only [Ψ, AddMonoidHom.comp_apply, act_act, hPQ, act_one]
    simp
  have hE : ∀ a b c, Ψ (Pi.single b (c a)) = Pi.single b (Ψ c a) := by
    intro a b c
    set z := e₀.symm (act Q⁻¹ X₀ c) with hz
    have hc : act Q X₀ (e₀ z) = c := by simp [hz, act_act, hQP, act_one]
    have r0 := (matRel_iff W a b _ _).1 (h₀ a b z)
    have r1 := (matRel_iff W a b _ _).1 (h₁ a b z)
    rw [← hQ, hc] at r0
    rw [← hQ] at r1
    rw [← r0, hΨ, r1, ← hΨ, hc]
  let π : X₀ →+ X₁ := (Pi.evalAddMonoidHom (fun _ => X₁) 0).comp (Ψ.comp (AddMonoidHom.single (fun _ => X₀) 0))
  have hπ : ∀ b x, Ψ (Pi.single b x) = Pi.single b (π x) := by
    intro b x
    have := hE 0 b (Pi.single 0 x)
    simpa [π] using this
  have hdiag : ∀ c, Ψ c = fun u => π (c u) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]

    rw [map_sum]
    simp only [hπ]
    rw [← Finset.univ_sum_single (fun u => π (c u))]
  have key : ∀ y u, ρ y u = π (e₀ y u) := by
    intro y u
    have h1 : act Q X₁ (ρ y) = fun u => π (act Q X₀ (e₀ y) u) := by rw [← hΨ, hdiag]
    have h2 := congrArg (act Q⁻¹ X₁) h1
    rw [act_act, hPQ, act_one, act_comp, act_act, hPQ, act_one] at h2
    exact congrFun h2 u
  refine ⟨π, ?_, key⟩
  intro x
  obtain ⟨y, hy⟩ := hρ (fun _ => x)
  exact ⟨e₀ y 0, by rw [← key, hy]⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_openAt_of_levAt : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (β : cycAway n →+* o) (S : ThetaSys o Ω) (u : Sp S.R ⟶ F.X) (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X)
    (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → X.IsHom M (AlgHom.id o Ω) f →
    IsIso (f ∣_ Xab) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → Set.range d ⊆ Xab →
    ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ f ⁻¹' Xab := by
  intro g n F o Ω _ _ _ β S u Y X M q f Xab d hL hf hiso hd hdo hrange
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id]
  have hf' : M.pt ≫ f = X.pt := by simpa [RatModel.IsHom, hid] using hf
  have hd' : Y.pt ≫ d = X.pt := by simpa [RatModel.IsHom, hid] using hd
  set U : M.Z.Opens := f ⁻¹ᵁ d.opensRange with hUdef
  have hUle : U ≤ f ⁻¹ᵁ Xab := fun m hm => hrange hm
  have hopen : IsOpenImmersion (U.ι ≫ f) := by
    have e : U.ι ≫ f = M.Z.homOfLE hUle ≫ (f ∣_ Xab) ≫ Xab.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    rw [e]
    infer_instance
  have hrng : Set.range (U.ι ≫ f) = Set.range d := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact m.2
    · rintro ⟨y, rfl⟩
      have hy : d y ∈ Xab := hrange ⟨y, rfl⟩
      obtain ⟨m', hm'⟩ := (f ∣_ Xab).surjective ⟨d y, hy⟩
      have h1 : f ((f ⁻¹ᵁ Xab).ι m') = d y := by
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hm']
        rfl
      have h2 : (f ⁻¹ᵁ Xab).ι m' ∈ U := ⟨y, h1.symm⟩
      exact ⟨⟨_, h2⟩, h1⟩
  let e := IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) d hrng
  have he : e.hom ≫ d = U.ι ≫ f := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨-, hfin, hsurj, hs, hpt⟩ := hL
  refine ⟨U, e.hom ≫ q, ⟨?_, inferInstance, inferInstance, ?_, ?_⟩, fun m hm => hUle hm⟩
  · obtain ⟨w⟩ : Nonempty (Sp Ω) := inferInstance
    refine ⟨M.pt w, Y.pt w, ?_⟩
    have h1 : d (Y.pt w) = X.pt w := by rw [← hd']; rfl
    have h2 : f (M.pt w) = X.pt w := by rw [← hf']; rfl
    exact h1.trans h2.symm
  · rw [Category.assoc, hs, ← hd.inducedModelMorphism_comp_structureMap, ← hf.inducedModelMorphism_comp_structureMap]
    simp only [← Category.assoc, he]
  · intro x hx
    have h : x ≫ e.hom = Y.pt := by
      rw [← cancel_mono d, Category.assoc, he, ← Category.assoc, hx, hf', hd']
    rw [← Category.assoc, h, hpt]

end GlobalTheory.SiegTh

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def LabTors {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (k : ℕ)
    (x : QkPt D (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)) : Prop :=
  (∀ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ k = 1 → ∃ p, x p = y) ∧ (∀ p, x p ^ k = 1) ∧
    (∀ p p', x p = x p' ↔ QkPt.Equiv D (Kb R) p p') ∧
    (∀ p p' p'', QkAdd p p' p'' → x p'' = x p * x p') ∧
    ∀ p p' (z : (Kb R)ˣ), WeilQkIs D (Kb R) k p p' z ↔ WeilIs A.A A.L k (x p) (x p') (unitOn z)

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def GeomIso {K₀ K' Ω : Type} [CommRing K₀] [CommRing K'] [CommRing Ω] (A₀ : PolAV (Sp K₀)) (A' : PolAV (Sp K'))
    (e₀ : K₀ →+* Ω) (e' : K' →+* Ω) : Prop :=
  ∃ (B : PolAV (Sp Ω)) (b₀ : B.A.left ⟶ A₀.A.left) (b' : B.A.left ⟶ A'.A.left),
    IsGrpPullback B.A A₀.A (spMap e₀) b₀ ∧ LBIso B.L (A₀.L.pull b₀) ∧
    IsGrpPullback B.A A'.A (spMap e') b' ∧ LBIso B.L (A'.L.pull b')

def UniTrait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (_ : Unif (maximalIdeal W) D' A' G') (_ : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left),
    GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsSemiAbelian G' ∧ IsFib φ A A' a

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.Eq8

theorem eq_torusMap_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X →+ X)
    (t : splitTorus S X ⟶ splitTorus S X) (ht : TorusEndOf X h t) : t = GlobalTheory.SplitTorus.torusMap S h := by
  refine (GlobalTheory.SplitTorus.eq_torusMap_iff t h).2 fun b => ?_
  have e := congrArg Units.val (ht b)
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X b)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X b).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val] at e
  exact e

theorem endChar_endU : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (E : EndU U.toUnifPre), EndChar U E.aG E.h := by
  intro V₁ _ _ _ _ D P G _ _ _ U E κ _ a ha G₀ _ φ h f₀ hf
  obtain ⟨t, ht, hi⟩ := E.i_lin 0
  have htm := eq_torusMap_of_torusEndOf E.h t ht
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift ha h
  have e : f₀.left ≫ GlobalTheory.TorusPart.thickLift ha h =
      GlobalTheory.TorusPart.thickLift ha h ≫ ((Over.pullback (thick V₁ (maximalIdeal V₁) 0)).map E.aG).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, hf, Category.assoc]
      simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, Over.w]
  have hc := GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e (U.gt 0).i
  unfold GlobalTheory.TorusPart.gtTorus
  rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

end GlobalTheory.Poinc.Eq8
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

theorem exists_prime_eq_zero_of_finiteType (κ : Type) [Field κ] [Algebra.FiniteType ℤ κ] :
    ∃ p : ℕ, p.Prime ∧ (p : κ) = 0 := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ κ := finite_of_finite_type_of_isJacobsonRing ℤ κ
  obtain ⟨q, hq⟩ := CharP.exists κ
  rcases CharP.char_is_prime_or_zero κ q with hqp | hq0
  · exact ⟨q, hqp, CharP.cast_eq_zero κ q⟩
  · subst hq0
    haveI : CharZero κ := CharP.charP_to_charZero κ
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := κ) (algebraMap ℤ κ).injective_int (Field.toIsField κ))
      Int.not_isField

theorem isLocalHom_of_isCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] {j : O →+* R} (h : IsCpl j) :
    IsLocalHom j := by
  obtain ⟨e, he⟩ := h
  refine ⟨fun a ha => ?_⟩
  rw [← he] at ha
  have h1 : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) a) := by
    simpa using ha.map e.symm
  have h2 := h1.map (AdicCompletion.evalₐ (maximalIdeal O) 1)
  rw [AlgHom.commutes] at h2
  by_contra hn
  have hm : a ∈ maximalIdeal O ^ 1 := by rw [pow_one]; exact hn
  have h0 : algebraMap O (O ⧸ maximalIdeal O ^ 1) a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ 1) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [pow_one]; exact (maximalIdeal.isMaximal O).ne_top)
  rw [h0] at h2
  exact not_isUnit_zero h2

theorem finiteType_residueField {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) (hx : IsClosed ({x} : Set M.Z)) :
    Algebra.FiniteType ℤ (M.Z.residueField x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  haveI : IsClosedImmersion (M.Z.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.1 hx
  have h : LocallyOfFiniteType (M.Z.fromSpecResidueField x ≫ M.s) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of o') (M.Z.fromSpecResidueField x ≫ M.s)
  rw [← hφ] at h
  have h₁ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  rw [← RingHom.finiteType_algebraMap]
  convert h₁.comp h₀
  exact RingHom.ext_int _ _

theorem closedPoint_cpl_residueChar : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsLocalHom j ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ maximalIdeal R := by
  intro o' Ω _ _ _ _ M x hx
  refine ⟨RatModel.essFiniteType_int_stalk_of_arithBase M x, fun R _ _ j hj => ?_⟩
  haveI hl := isLocalHom_of_isCpl hj
  refine ⟨hl, ?_⟩
  haveI := finiteType_residueField M x hx
  obtain ⟨p, hp, h0⟩ := exists_prime_eq_zero_of_finiteType (M.Z.residueField x)
  refine ⟨p, hp, ?_⟩
  have hm : (p : M.Z.presheaf.stalk x) ∈ maximalIdeal (M.Z.presheaf.stalk x) := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact h0
  rw [← map_natCast j p]
  exact map_nonunit j _ hm

end GlobalTheory.UPoinc.ClosedPt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Emb.range_closed (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (E : Emb π G') :
    (∀ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R → ∃ y : E.Y.left, E.f g = E.j y) ∧
    (Surjective π → ∀ y : E.Y.left, ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g = E.j y) := by
  constructor
  · intro g hg
    obtain ⟨p, hp⟩ : ∃ p, p = E.H.ι g := ⟨_, rfl⟩
    rw [← hp] at hg
    let Ω := G'.left.residueField p
    let x0 : Sp Ω ⟶ G'.left := G'.left.fromSpecResidueField p
    let x : Sp Ω ⟶ S := x0 ≫ G'.hom
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, x0, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hg
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    let w : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ x) :=
      pullback.lift (spMap io ≫ x0) (𝟙 _) (by simp [x])
    let w0 : Sp Ω' := closedPoint Ω'
    have hw : pullback.fst G'.hom (spMap io ≫ x) (w w0) = p := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    have hlw : l (w w0) = g := by
      apply E.H.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hl1, ← hp]
      exact hw
    refine ⟨pullback.fst E.Y.hom (spMap (io.comp κ)) (e.hom.left (w w0)), ?_⟩
    rw [← hlw, ← Scheme.Hom.comp_apply, hl2]
    simp only [Scheme.Hom.comp_apply]
  · intro hπ y
    obtain ⟨s, hs⟩ := hπ.surj (closedPoint R)
    let Ω := S.residueField s
    let x : Sp Ω ⟶ S := S.fromSpecResidueField s
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    obtain ⟨w', hw'⟩ := (pullback.fst E.Y.hom (spMap (io.comp κ))).surjective y
    let w := e.inv.left w'
    have hew : e.hom.left w = w' := by
      simp only [w]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id]
      rfl
    refine ⟨l w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply l E.H.ι, hl1,
        ← Scheme.Hom.comp_apply (pullback.fst G'.hom (spMap io ≫ x)) G'.hom, pullback.condition]
      simp only [Scheme.Hom.comp_apply, x]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    · rw [← Scheme.Hom.comp_apply, hl2]
      simp only [Scheme.Hom.comp_apply]
      rw [hew, hw']

end GlobalTheory.Mum
end
