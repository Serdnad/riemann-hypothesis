module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle045
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Transl

theorem exp_alg {A X : Type} [CommRing A] {N : ℕ} {Wy Wxy Wx W1 cG cB vf vw : Aˣ} {σ : A} (s : Finset X) {f : X → A}
    {ty txy g θ : X → Aˣ} (h₁ : cB * Wxy ^ N * W1 ^ N = Wy ^ N * Wx ^ N * cG) (h₂ : vw * Wx ^ N = W1 ^ N * vf)
    (h₃ : ∀ α, txy α * θ α = g α * ty α) (h₄ : Wxy.val ^ N * σ = ∑ α ∈ s, f α * (txy α).val) :
    Wy.val ^ N * (σ * (cG * vf).val) = ∑ α ∈ s, (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val := by
  have key : cB * vw * Wxy ^ N = Wy ^ N * (cG * vf) := by
    apply mul_right_cancel (b := W1 ^ N)
    calc cB * vw * Wxy ^ N * W1 ^ N = vw * (cB * Wxy ^ N * W1 ^ N) := by ac_rfl
      _ = vw * (Wy ^ N * Wx ^ N * cG) := by rw [h₁]
      _ = Wy ^ N * cG * (vw * Wx ^ N) := by ac_rfl
      _ = Wy ^ N * cG * (W1 ^ N * vf) := by rw [h₂]
      _ = Wy ^ N * (cG * vf) * W1 ^ N := by ac_rfl
  have hα : ∀ α, (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val =
      (cB * vw).val * (f α * (txy α).val) := by
    intro α
    have ht : txy α = g α * ty α * (θ α)⁻¹ := eq_mul_inv_of_mul_eq (h₃ α)
    have hu : cB * vw * g α * (θ α)⁻¹ * ty α = cB * vw * txy α := by rw [ht]; ac_rfl
    calc (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val
        = f α * (cB * vw * g α * (θ α)⁻¹ * ty α).val := by rw [Units.val_mul _ (ty α), _root_.mul_assoc]
      _ = f α * (cB * vw * txy α).val := by rw [hu]
      _ = (cB * vw).val * (f α * (txy α).val) := by rw [Units.val_mul _ (txy α)]; ring
  rw [Finset.sum_congr rfl (fun α _ => hα α), ← Finset.mul_sum, ← h₄]
  have hv := congrArg Units.val key
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hv
  simp only [Units.val_mul]
  linear_combination (-σ) * hv

section Level

noncomputable local instance (priority := high) monObjTranslThick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [MonObj G] : MonObj (thickObj R I e G) :=
  letI : (Over.pullback (thick R I e)).Monoidal :=
    (Over.instBraidedPullback (f := thick R I e)).toMonoidal
  Functor.monObjObj (F := Over.pullback (thick R I e)) G

noncomputable local instance (priority := high) oneTranslThick {R : Type} [CommRing R]
    (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [MonObj G]
    (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    One (Z ⟶ thickObj R I e G) :=
  ⟨(CategoryTheory.Hom.monoid (M := thickObj R I e G) (X := Z)).one⟩

noncomputable local instance (priority := high) ofNatTranslThick {R : Type} [CommRing R]
    (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [MonObj G]
    (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    OfNat (Z ⟶ thickObj R I e G) 1 :=
  ⟨(oneTranslThick I e G Z).one⟩

noncomputable local instance (priority := high) commGroupTranslThick {R : Type} [CommRing R]
    (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    CommGroup (Z ⟶ thickObj R I e G) :=
  let braided := Over.instBraidedPullback (f := thick R I e)
  letI : (Over.pullback (thick R I e)).Monoidal := braided.toMonoidal
  letI : (Over.pullback (thick R I e)).LaxBraided := braided.toLaxBraided
  let grp : GrpObj (thickObj R I e G) := Functor.grpObjObj (F := Over.pullback (thick R I e)) (G := G)
  have comm : @IsCommMonObj _ _ _ _ (thickObj R I e G) grp.toMonObj :=
    Functor.isCommMonObj_obj (F := Over.pullback (thick R I e)) (M := G)
  @CategoryTheory.Hom.commGroup _ _ _ (thickObj R I e G) Z grp inferInstance comm

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))}
open ReciprocityTheory.ChartRestriction.G.DVR

def wv (e : ℕ) {Z : Scheme.{0}} (z : Z) (JG : (Z ⟶ G.left) → U.P.L.L.ι) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (a : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  gw (U.w e) a z (J (a ≫ (U.gt e).pG.left)) (fun _ => JG (a ≫ (fstG I e G).left))

def upHom (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (Z ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj Z ⟶ G) :=
  MonoidHom.mk' (fun a => (Over.map (thick R I e)).map a ≫ fstG I e G) fun a b =>
    FormalPoint.map_mul_fstG (I := I) (e := e) (G := G) (Z := Z) a b

def imHom (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (Z ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj Z ⟶ D.P.A) :=
  MonoidHom.mk' (TorusCoord.im (U.gt e) (T := Z)) fun a b =>
    TorusCoord.im_mul (U.gt e) (T := Z) a b

def FrameRel (x : T ⟶ G) (b : T ⟶ D.P.A) (N : ℕ)
    (f : LB.Gen (LB.LinComb U.P.L.L (K := Fin 2) ![(1 : T ⟶ G).left, x.left] ![(N : ℤ), -(N : ℤ)]))
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, b.left] ![(N : ℤ), -(N : ℤ)])) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left) (o a : Z ⟶ (thickObj R I e G).left),
    o ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left → a ≫ (fstG I e G).left = r ≫ x.left →
    ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J →
      val w r z J * wv U e z JG J a ^ N = wv U e z JG J o ^ N * val f r z JG

variable {U}

theorem exists_level_point {x : T ⟶ G} {g : GtPt D T} (hr : U.Red x g) {N : ℕ} (hx : x ^ N = 1) {e : ℕ}
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : (Over.map (thick R I e)).obj Z ⟶ T) :
    ∃ a : Z ⟶ thickObj R I e G, upHom I e G Z a = τ ≫ x ∧ imHom U e Z a = τ ≫ g.b ∧ a ^ N = 1 := by
  obtain ⟨a, ha⟩ := GlobalTheory.FormalPoint.exists_lift_fstG (τ ≫ x)
  have hup : upHom I e G Z a = τ ≫ x := ha
  have hleft : a.left ≫ (fstG I e G).left = τ.left ≫ x.left := by
    have := congrArg CommaMorphism.left ha
    simpa using this
  refine ⟨a, hup, ?_, ?_⟩
  · show (Over.map (thick R I e)).map a ≫ (U.gt e).pG = τ ≫ g.b
    ext1
    simpa using (hr e _ τ.left a.left hleft).1
  · apply GlobalTheory.FormalPoint.eq_of_map_fstG
    change upHom I e G Z (a ^ N) = upHom I e G Z 1
    rw [map_pow, map_one, hup, ← CategoryTheory.MonObj.comp_pow, hx, CategoryTheory.MonObj.comp_one]

theorem exists_over_point {e : ℕ} {Z : Scheme.{0}} (y₀ : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (T ⊗ G).left)
    (rB : Z ⟶ (T ⊗ D.P.A).left) (e₁ : rG ≫ (snd T G).left = y₀ ≫ (fstG I e G).left)
    (e₂ : rB ≫ (snd T D.P.A).left = y₀ ≫ (U.gt e).pG.left) (e₃ : rB ≫ (fst T D.P.A).left = rG ≫ (fst T G).left) :
    ∃ τ : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T,
      rG = (lift τ (upHom I e G _ (Over.homMk y₀ rfl))).left ∧ rB = (lift τ (imHom U e _ (Over.homMk y₀ rfl))).left := by
  have h1 : (fst T G).left ≫ T.hom = (snd T G).left ≫ G.hom := by
    rw [Over.w (fst T G), Over.w (snd T G)]
  have h2 : (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
  have hw : (rG ≫ (fst T G).left) ≫ T.hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    simp only [Category.assoc]
    rw [h1, reassoc_of% e₁, h2]
  have hG : rG ≫ (T ⊗ G).hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w (fst T G), ← Category.assoc]; exact hw
  have hB : rB ≫ (T ⊗ D.P.A).hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w (fst T D.P.A), ← Category.assoc, e₃]; exact hw
  refine ⟨Over.homMk (rG ≫ (fst T G).left) hw, ?_, ?_⟩
  · have key : (Over.homMk rG hG : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T ⊗ G) =
        lift (Over.homMk (rG ≫ (fst T G).left) hw) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]; ext1; simp
      · rw [lift_snd]
        show Over.homMk rG hG ≫ snd T G = (Over.map (thick R I e)).map (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) ≫ fstG I e G
        ext1; simpa using e₁
    exact congrArg CommaMorphism.left key
  · have key : (Over.homMk rB hB : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T ⊗ D.P.A) =
        lift (Over.homMk (rG ≫ (fst T G).left) hw) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]; ext1; simpa using e₃
      · rw [lift_snd]
        show Over.homMk rB hB ≫ snd T D.P.A = (Over.map (thick R I e)).map (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) ≫ (U.gt e).pG
        ext1; simpa using e₂
    exact congrArg CommaMorphism.left key

theorem expT_transl (hG : GlobalFnsSt) {x : T ⟶ G} {g : GtPt D T} (hr : U.Red x g) {N : ℕ} (hx : x ^ N = 1)
    {f₀ w} (hf : FrameRel U x g.b N f₀ w) {σ : U.SecGT (𝟙_ _) N} {σ' : U.SecGT T N}
    {f : ∀ α, SecBT D (𝟙_ _) N α} {f' : ∀ α, SecBT D T N α}
    (hσ : ∀ (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good U.P.L.L z J →
      sval σ' (lift τ y).left z J = sval σ (lift (toUnit T') ((τ ≫ x) * y)).left z J *
        (cubN (cubV U.P.c z J) N 1 (τ ≫ x) y * val f₀ τ.left z J).val)
    (hf' : ∀ α (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J),
      Good D.P.L z J → sval (f' α) (lift τ y).left z J =
        sval (f α) (lift (toUnit T') ((τ ≫ g.b) * y)).left z J * (fac g N w α τ y z J).val)
    (h : U.ExpT (𝟙_ _) N σ f) : U.ExpT T N σ' f' := by
  intro e
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, ?_⟩
  intro Z y₀ rG rB e₁ e₂ e₃ z JG J hJG hJ
  obtain ⟨τ, hτG, hτB⟩ := exists_over_point (U := U) y₀ rG rB e₁ e₂ e₃
  subst hτG hτB
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_level_point hr hx τ
  have hal : a.left ≫ (fstG I e G).left = τ.left ≫ x.left := congrArg CommaMorphism.left ha₁
  have hu : (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ fstG I e G =
      (τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) := by
    rw [show (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ fstG I e G =
      upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) from rfl, map_mul, ha₁]
  have hi : (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ (U.gt e).pG =
      (τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) := by
    rw [show (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ (U.gt e).pG =
      imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) from rfl, map_mul, ha₂]
  have c₁ := (congrArg CommaMorphism.left (lift_snd (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left hu).symm
  have c₂ := (congrArg CommaMorphism.left (lift_snd (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left hi).symm
  have c₃ := (congrArg CommaMorphism.left (lift_fst (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left (lift_fst (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).symm
  obtain ⟨hz, hsum⟩ := hs Z (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)).left
    (lift (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))).left
    (lift (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))).left c₁ c₂ c₃ z JG J hJG hJ
  refine ⟨fun α hα => ?_, ?_⟩
  · rw [hf' α _ τ _ z J hJ, hz α hα, zero_mul]
  have hcube : ∀ p q u : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G,
      @id (Z.presheaf.stalk z)ˣ (cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) D.cub z J (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) p) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) q)
        (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) u)) *
          wv U e z JG J (p * q).left * wv U e z JG J (p * u).left * wv U e z JG J (q * u).left *
          wv U e z JG J (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left =
        wv U e z JG J (p * q * u).left * wv U e z JG J p.left * wv U e z JG J q.left * wv U e z JG J u.left *
          @id (Z.presheaf.stalk z)ˣ (cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) U.P.c z JG (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) p) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) q)
            (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) u)) :=
    fun p q u => (U.w_vals e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) z JG J hJG hJ (fun q => wv U e z JG J q.left) (fun _ => rfl)).2.2 p q u
  have H1 := cubN_twist (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom))) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom))) (fun q => wv U e z JG J q.left)
    (θ := cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) D.cub z J) (θ' := cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) U.P.c z JG) hcube ha₃ (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)
  rw [ha₁, ha₂] at H1
  have h1o : (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left ≫ (fstG I e G).left = τ.left ≫ (1 : T ⟶ G).left := by
    have h1 : upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) 1 = τ ≫ (1 : T ⟶ G) := by rw [map_one, MonObj.comp_one]
    exact congrArg CommaMorphism.left h1
  have H2 := hf e Z τ.left (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left a.left h1o hal z JG J hJG hJ
  have ha₂' : (Over.map (thick R I e)).map a ≫ (U.gt e).pG = τ ≫ g.b := ha₂
  have H3 : ∀ α, @id (Z.presheaf.stalk z)ˣ (val ((U.gt e).t α) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)).left z J) *
      @id (Z.presheaf.stalk z)ˣ (th D z J (cP D ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom))) α) (τ ≫ g.b) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))) =
      @id (Z.presheaf.stalk z)ˣ (val (g.s α) τ.left z J) * @id (Z.presheaf.stalk z)ˣ (val ((U.gt e).t α) y₀ z J) := by
    intro α
    have ht := torus_coord_add hG R I D e G (U.gt e) (Over.mk (y₀ ≫ (thickObj R I e G).hom)) a (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) α z J hJ
    rw [ha₂'] at ht
    rw [← (hr e _ τ.left a.left hal).2 α z J hJ]
    exact ht
  rw [hσ _ τ _ z JG hJG]
  simp only [hf' _ _ τ _ z J hJ]
  exact exp_alg s H1 H2 H3 hsum

end Level

end GlobalTheory.UU.Transl
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gm_eq_of_flat_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    {U V : Y.Opens} (a : Γ(Y, U)ˣ) (b : Γ(Y, V)ˣ)
    (h : ∀ x : X, π x ∈ U → π x ∈ V → gm π x U a = gm π x V b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hU : r z ∈ U) (hV : r z ∈ V) :
    gm r z U a = gm r z V b := by
  have e : pullU π (U ⊓ V) (res inf_le_left a) = pullU π (U ⊓ V) (res inf_le_right b) := by
    apply unit_ext
    intro x hx
    have hx' : π x ∈ U ⊓ V := hx
    have h₁ := gm_pull (𝟙 X) π x (U ⊓ V) hx' (res inf_le_left a)
    have h₂ := gm_pull (𝟙 X) π x (U ⊓ V) hx' (res inf_le_right b)
    rw [Category.id_comp] at h₁ h₂
    exact h₁.trans ((gm_res π x _ hx' a).trans ((h x hx'.1 hx'.2).trans
      ((gm_res π x _ hx' b).symm.trans h₂.symm)))
  have e' : (res inf_le_left a : Γ(Y, U ⊓ V)ˣ) = res inf_le_right b :=
    Units.ext (FunDescent.app_injective π (U ⊓ V) (congrArg Units.val e))
  have hz : r z ∈ U ⊓ V := ⟨hU, hV⟩
  exact (gm_res r z _ hz a).symm.trans ((congrArg (gm r z _) e').trans (gm_res r z _ hz b))

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}


omit [IsDomain R] in
theorem trans_comp_proj (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem trans_comp_q (e : ℕ) :
    thickMap R I e G ≫ (U.gt (e + 1)).q.left = (U.gt e).q.left ≫ thickMap R I e D.toPre.P.A := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((U.gt_q e).trans
      ((congrArg ((U.gt e).q.left ≫ ·) (trans_comp_proj e D.toPre.P.A).symm).trans
        (Category.assoc _ _ _).symm))
  · have h₁ : (U.gt (e + 1)).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt (e + 1)).q
    have h₀ : (U.gt e).q.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (U.gt e).q
    have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg (thickMap R I e G ≫ ·) h₁).trans ((k G).trans
      ((congrArg (· ≫ thickTrans R I e) h₀.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg ((U.gt e).q.left ≫ ·) (k _).symm).trans (Category.assoc _ _ _).symm)))))

theorem gw_trans (e : ℕ) (y : (thickObj R I e G).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (U.gt e).pG.left y ∈ D.toPre.P.L.U jM) (hL : (fstG I e G).left y ∈ U.LG.L.U jL) :
    gw (U.w (e + 1)) (thickMap R I e G) y jM (fun _ => jL) = gw (U.w e) (𝟙 _) y jM (fun _ => jL) := by
  have hM' : (U.gt (e + 1)).pG.left (thickMap R I e G y) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g y ∈ D.toPre.P.L.U jM) (U.gt_q e)).mpr hM
  have hL' : (fstG I (e + 1) G).left (thickMap R I e G y) ∈ U.LG.L.U jL :=
    (congrArg (fun g => g y ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL
  have hm : y ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt (e + 1)).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I (e + 1) G).left).U (fun _ => jL)) ⊓
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)) :=
    ⟨⟨mem_pull.2 hM', mem_pull.2 hL'⟩, mem_pull.2 hM, mem_pull.2 hL⟩
  have H := congrArg (gm (𝟙 _) y _)
    (U.w_compat e (fun _ => jM, fun _ => jL) _ inf_le_left inf_le_right)
  have h₁ := gm_pull (𝟙 _) (thickMap R I e G) y _ hm.1 ((U.w (e + 1)).s (fun _ => jM, fun _ => jL))
  rw [Category.id_comp] at h₁
  exact h₁.symm.trans ((gm_res (𝟙 _) y inf_le_left hm _).symm.trans
    (H.trans (gm_res (𝟙 _) y inf_le_right hm _)))

end GlobalTheory.UnifCompare

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor UnifCompare

theorem unifPre_polarised_iso :
    GlobalFnsSt → SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) := by
  intro hGF hS hA R _ _ _ I hR D D' A A' G _ _ hG U U' wL he hgen hrig
  choose β hβm hβ using unifPre_abelianPart_iso R I hR D D' A A' G hG U U'
  choose v hvg hv using fun e =>
    T.uniformisation_polarisations_agree_at_level hGF R I hR D D' A A' G hG U U' wL he hgen hrig e (β e) (hβm e) (hβ e)
  have hβl : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left = (U.gt e).q.left := fun e =>
    congrArg (·.left) (hβ e)
  have hp : ∀ e, (U'.gt e).q.left ≫ (β e).hom.left ≫ (fstG I e D.toPre.P.A).left =
      (U.gt e).pG.left := fun e =>
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (fstG I e D.toPre.P.A).left) (hβl e))
  have hc : ∀ e, thickMap R I e D'.toPre.P.A ≫ (β (e + 1)).hom.left =
      (β e).hom.left ≫ thickMap R I e D.toPre.P.A := by
    intro e
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have : Epi (U'.gt e).q.left := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (U'.gt e).q.left, ← Category.assoc, ← trans_comp_q, Category.assoc, hβl,
      trans_comp_q, ← Category.assoc, hβl]
  obtain ⟨hN, -, -, hC⟩ := hR
  obtain ⟨Φ, w, hw, H⟩ := T.exists_iso_of_compatible_abelianThickenings hS hA R I D.toPre.P D'.toPre.P β v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R I e D'.toPre.P.A).left,
        y ∈ (D.toPre.P.L.pull ((β e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') →
        thickMap R I e D'.toPre.P.A y ∈
          (D.toPre.P.L.pull ((β (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I (e + 1) D'.toPre.P.A).left).U (fun _ => j') := by
      intro y hy
      have k : thickMap R I e D'.toPre.P.A ≫ (β (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left =
          (β e).hom.left ≫ (fstG I e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((β e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U j) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ D'.toPre.P.L.U j') (trans_comp_proj e _)).mpr
          (mem_pull.1 hy.2))⟩
    have hz : r z ∈ (D.toPre.P.L.pull ((β e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG I e G).left x)
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG I e G).left x)
    have hM : (U.gt e).pG.left x ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hp e)).mp (mem_pull.1 hx.1)
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_pull.1 hx.2
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R I e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U' e x j' jL' hM' hL', gw_trans U e x j jL hM hL, trans_comp_q, trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  refine ⟨Φ, w, hw, fun e => ⟨?_, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩⟩
  · exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) (H e).1).trans (hp e))
  · have h := (H e).2 Z (r ≫ (U'.gt e).q.left) z jM jM'
      ((congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (hp e)).mpr hM) hM'
    rw [Category.assoc] at h
    exact (congrArg (· * _) h).trans (hv e Z r z jM jM' jL jL' hM hM' hL hL')

end GlobalTheory
end
