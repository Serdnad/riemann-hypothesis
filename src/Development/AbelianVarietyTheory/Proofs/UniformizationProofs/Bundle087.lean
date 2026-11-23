module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle078
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable local instance (priority := high) grpObjUniformizationPullback087
    {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  letI : (Over.pullback f).Monoidal := (Over.instBraidedPullback (f := f)).toMonoidal
  Functor.grpObjObj (F := Over.pullback f)

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace SecondPosition
open FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]

theorem cT_zero (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h := cT_add D T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem cT_neg (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (a : D.X) : cT D T (-a) = (cT D T a)⁻¹ := by
  have h := cT_add D T a (-a)
  rw [add_neg_cancel, cT_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem val_sym_one (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val D.sym (1 : T ⟶ D.P.A).left z J = 1 := by
  have a := val_corr hJ D.sym_rig T.hom
  rw [val_one] at a
  refine Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans a)
  congr 1

theorem one_kapV (D : DegPre R) (a b : D.X) {T : Over (Spec (CommRingCat.of R))} {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (y : T ⟶ D.P.A) :
    kapV D a b z J 1 y = (val D.sym y.left z J)⁻¹ * rigV D z J ^ 2 * cubV D.cub z J (cT D T b) y y⁻¹ *
      (cubV D.cub z J (cT D T (a - b)) (cT D T b) y)⁻¹ := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  rw [kapV, kap0]
  simp only [h.face₃, h.face₂, h.face, _root_.mul_one, _root_.one_mul]
  rfl

theorem compare (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (s₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (s s' : Fin n → ∀ α, SecBT D T₀ 2 α) (hA : AddB D T₀ s₀ r s s') (hP : PsiRel D T₀ s₀) (mu : D.X)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (y : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) [IsDomain (T.left.presheaf.stalk z)] (hr : gs (𝟙 _) z ⊤ (scal T.hom r) ≠ 0)
    (h0 : sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J ≠ 0)
    (h0' : sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J ≠ 0) (C U : T.left.presheaf.stalk z)
    (hs : ∀ i, sval (s' i (0 + 2 • mu)) (lift ρ y).left z J =
      C * (sval (s' i 0) (lift ρ (y * cT D T mu)).left z J * U)) :
    (cubV D.cub z J (cT D T (-mu)) y y⁻¹).val *
        ((val (D.psi mu) κ.left z J).val * (val (D.psi (-mu)) κ.left z J).val *
          (val D.sym (y * cT D T mu).left z J).val) =
      C * (U * (val (D.psi 0) κ.left z J).val * (val (D.psi 0) κ.left z J).val) *
        ((cubV D.cub z J (cT D T (mu - -mu)) (cT D T (-mu)) y).val * (val D.sym y.left z J).val) := by
  have h := isCub_cubV D.cub (T := T) (z := z) (J := J) hJ
  have e₁ := (hA T ρ 1 y z J hJ).1 mu (-mu) 0 (0 + 2 • mu) (by abel) (by rw [two_smul]; abel)
  have e₂ := (hA T ρ 1 (y * cT D T mu) z J hJ).1 0 0 0 0 (by abel) (by abel)
  rw [one_kapV D _ _ hJ, _root_.one_mul y, _root_.one_mul y⁻¹, hP _ T ρ κ _ z J hJ,
    hP (-mu) T ρ κ _ z J hJ] at e₁
  rw [one_kapV D _ _ hJ, _root_.one_mul (y * cT D T mu), _root_.one_mul (y * cT D T mu)⁻¹, mul_inv y, ← cT_neg,
    hP 0 T ρ κ (y * cT D T mu) z J hJ, hP 0 T ρ κ (y⁻¹ * cT D T (-mu)) z J hJ, cT_zero, h.face, h.face₂,
    _root_.mul_one (y * cT D T mu), _root_.mul_one (y⁻¹ * cT D T (-mu))] at e₂
  have e₃ : ∑ i, sval (s i 0) (lift ρ 1).left z J * sval (s' i (0 + 2 • mu)) (lift ρ y).left z J =
      C * U * ∑ i, sval (s i 0) (lift ρ 1).left z J * sval (s' i 0) (lift ρ (y * cT D T mu)).left z J := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]; ring
  rw [e₁, e₂] at e₃
  generalize val D.sym y.left z J = A at e₃ ⊢
  generalize val D.sym (y * cT D T mu).left z J = B at e₃ ⊢
  generalize cubV D.cub z J (cT D T (mu - -mu)) (cT D T (-mu)) y = E at e₃ ⊢
  have hne : gs (𝟙 _) z ⊤ (scal T.hom r) * (A⁻¹ * B⁻¹ * E⁻¹ * rigV D z J ^ 4).val *
      sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J *
      sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hr (Units.ne_zero _)) h0) h0'
  refine mul_left_cancel₀ hne ?_
  have a := A.mul_inv
  have b := B.mul_inv
  have e := E.mul_inv
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, inv_one, Units.val_one] at e₃ ⊢
  generalize gs (𝟙 _) z ⊤ (scal T.hom r) = g at e₃ ⊢
  generalize sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J = p at e₃ ⊢
  generalize sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J = q at e₃ ⊢
  generalize (rigV D z J).val = w at e₃ ⊢
  generalize (val (D.psi mu) κ.left z J).val = m at e₃ ⊢
  generalize (val (D.psi (-mu)) κ.left z J).val = m' at e₃ ⊢
  generalize (val (D.psi 0) κ.left z J).val = o at e₃ ⊢
  generalize (cubV D.cub z J (cT D T (-mu)) y y⁻¹).val = k at e₃ ⊢
  linear_combination e₃ + g * A⁻¹.val * E⁻¹.val * w ^ 4 * p * q * k * m * m' * b -
    g * B⁻¹.val * w ^ 4 * p * q * C * U * o * o * (E.val * E⁻¹.val * a + e)

theorem isIso_refl (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (χ : D.X) :
    IsIso (lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ)) := by
  have e : lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ) ≫
      lift (fst T D.P.A) ((snd T D.P.A)⁻¹ * cT D (T ⊗ D.P.A) χ) = 𝟙 _ := by
    ext
    · simp
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv, lift_snd, comp_cT, mul_inv, inv_inv,
        inv_mul_cancel_right, Category.id_comp]
  exact ⟨_, e, e⟩

end SecondPosition


open FirstSlot SecondPosition in
theorem psi_mul_psi_of_addition_second_variable : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (mu α : D.X), α = 0 → ∀ (c : F) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 2 α mu) (DegPre.deltaε 2))), (∀ i z J, Good D.P.L z J → sval (s' i (α + 2 • mu)) (𝟙 _) z J = gs (𝟙 _) z ⊤ (DegPre.constBF D F c ⊤) * (sval (s' i α) (DegPre.trF D F mu).left z J * (val u (𝟙 _) z J).val)) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → (val (Z := (TF (R := R) F).left) (D.psi (mu)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (-mu)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) mu).left z J).val = gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) * (val u (DegPre.zF D F).left z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J).val := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA hP h0 mu α hα c u hs z J hJ
  subst hα
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hint : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let κF : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have zf : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have zs : DegPre.zF D F ≫ snd _ _ = 1 := lift_snd _ _
  have zκ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A ≫ κF).left = jFK (R := R) F := by
    rw [← Over.comp_left, ← Category.assoc, zf, Category.id_comp]; rfl
  have hJ' : Good D.P.L ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) := fun ψ => hJ _
  have hhom : (DegPre.BF D F).hom = (fst (TF (R := R) F) D.P.A ≫ κF).left ≫ jK R :=
    (Over.w (fst (TF (R := R) F) D.P.A ≫ κF)).symm
  have key := SecondPosition.compare D (TF (R := R) F) s₀ r s s' hA hP mu (DegPre.BF D F) (fst _ _) (fst _ _ ≫ κF)
    (snd _ _) ((DegPre.zF D F).left z) _ hJ' (by rw [hhom]; exact gs_scal_ne_zero _ _ hr)
    (by
      have := isIso_transl D (TF (R := R) F) mu
      have : IsIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (DegPre.BF D F) mu)).left :=
        (Over.forget _).map_isIso (lift (fst (TF (R := R) F) D.P.A) (snd _ _ * cT D (TF (R := R) F ⊗ D.P.A) mu))
      exact sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) h0 _ _ _ _ hJ')
    (by
      have := isIso_refl D (TF (R := R) F) (-mu)
      have : IsIso (lift (fst (TF (R := R) F) D.P.A) ((snd _ _)⁻¹ * cT D (DegPre.BF D F) (-mu))).left :=
        (Over.forget _).map_isIso
          (lift (fst (TF (R := R) F) D.P.A) ((snd _ _)⁻¹ * cT D (TF (R := R) F ⊗ D.P.A) (-mu)))
      exact sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) h0 _ _ _ _ hJ')
    _ _ (fun i => by
      rw [lift_fst_snd]
      exact hs i _ _ hJ')
  have ψn : ∀ χ, ((DegPre.zF D F).left.stalkMap z).hom (val (D.psi χ) (fst (TF (R := R) F) D.P.A ≫ κF).left
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val (Z := (TF (R := R) F).left) (D.psi χ) (jFK (R := R) F) z J).val := fun χ => by
    rw [← zκ]
    exact ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 (D.psi χ)).symm
  have cn : ∀ x x' y : DegPre.BF D F ⟶ D.P.A, ((DegPre.zF D F).left.stalkMap z).hom (cubV D.cub
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ)) x x' y).val =
      (cubV D.cub z J (DegPre.zF D F ≫ x) (DegPre.zF D F ≫ x') (DegPre.zF D F ≫ y)).val := fun x x' y => by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 D.cub.t).symm.trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl
  have sn : ∀ y : DegPre.BF D F ⟶ D.P.A, ((DegPre.zF D F).left.stalkMap z).hom (val D.sym y.left
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val D.sym (DegPre.zF D F ≫ y).left z J).val := fun y =>
    ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 D.sym).symm
  have un : ((DegPre.zF D F).left.stalkMap z).hom (val u (𝟙 _)
      ((DegPre.zF D F).left z) (fun ψ => J ((DegPre.zF D F).left ≫ ψ))).val =
      (val u (DegPre.zF D F).left z J).val := by
    refine ((values_natural _ _ _ _ D.P.L _ _ _ _ _ z J hJ).2.2.1 u).symm.trans ?_
    rw [Category.comp_id]
  have kn : ((DegPre.zF D F).left.stalkMap z).hom (gs (𝟙 _) ((DegPre.zF D F).left z) ⊤ (DegPre.constBF D F c ⊤)) =
      gs (𝟙 (TF (R := R) F).left) z ⊤ (scal (Y := (TF (R := R) F).left) (𝟙 (Spec (CommRingCat.of F))) c) := by
    refine (gs_comp_stalkMap (𝟙 _) (DegPre.zF D F).left z ⊤ trivial _).symm.trans ?_
    refine (gs_res ((DegPre.zF D F).left ≫ 𝟙 _) z (U := ⊤) (V := ⊤) le_top trivial _).trans ?_
    refine (gs_pull ((DegPre.zF D F).left ≫ 𝟙 _) (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_
    rw [Category.comp_id, ← Over.comp_left, zf]
    rfl
  have h := isCub_cubV D.cub (T := TF (R := R) F) (z := z) (J := J) hJ
  have k2 := congrArg ((DegPre.zF D F).left.stalkMap z).hom key
  simp only [map_mul] at k2
  rw [ψn, ψn, ψn, cn, cn, sn, sn, un, kn, MonObj.comp_mul, zs, h.face₂, h.face₃, comp_cT, _root_.one_mul (cT D _ mu),
    val_sym_one D hJ, Units.val_one, _root_.one_mul, _root_.one_mul, _root_.mul_one] at k2
  simp only [Units.val_mul]
  exact k2

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiRel_of_pullB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (f : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1), PullB D F (toUnit _) 1 f s₀ → PsiRel D (𝟙_ _) f → PsiRel D (TF (R := R) F) s₀ := by
  intro R _ _ D F _ _ f s₀ h hψ χ T ρ κ y z J hJ
  have a := pullB_values R D F _ _ 1 f s₀ h χ T ρ y z J hJ
  have b := pullB_values R D F _ _ 1 f s₀ h 0 T ρ (y * cT D T χ) z J hJ
  have c := hψ χ T (ρ ≫ toUnit _) κ y z J hJ
  exact a.trans (c.trans (congrArg _ b.symm))

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.IntWit

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs
  split_ifs
  · simp only [map_zero]
  · rfl

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans (gs_zero r z _)

theorem eq_zero_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j : K → L.ι) :
    s.f j = 0 := by
  refine fn_ext (V := LB.wchart L φ j) fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans (gs_zero _ _ _).symm

theorem integral_witness : AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X), U.FE F k → U.Supp F k β → ∃ (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), U.ExpT (𝟙_ _) k σ f ∧ PullB D F (toUnit _) k f s ∧ DegPre.FamFE D F k s ∧ (∃ j, (s β).f j ≠ 0) ∧ ∃ j, (f β).f j ≠ 0 := by
  intro V _ _ _ hV D A G _ _ U F _ _ k β hFE hS
  obtain ⟨t, s, ⟨n, c, σ, f, hE, -, hB⟩, j₀, hj₀⟩ := hS
  obtain ⟨hG, hP⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U F (𝟙_ _) (toUnit _) k
  choose s' hs' using fun i => (hP (f i)).exists
  have hex : ∃ i, ∃ j, (s' i β).f j ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hj₀ (eq_zero_of_sval D.P.isLB (s β) (fun y J hJ => ?_) j₀)
    have w : (toUnit (TF (R := V) F) ▷ D.P.A).left ≫ (snd (𝟙_ _) D.P.A).left = (snd _ D.P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := V) F)) D.P.A)
    refine (hB β _ (𝟙 _) (toUnit (TF (R := V) F) ▷ D.P.A).left (w.trans (Category.id_comp _).symm) y J hJ).trans ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (congrArg (_ * ·) ((hs' i β y J hJ).symm.trans (sval_eq_zero _ (hn i) _ _ _))).trans (mul_zero _)
  obtain ⟨i, j, hj⟩ := hex
  obtain ⟨t', ht'⟩ := (hG (σ i)).exists
  refine ⟨σ i, f i, s' i, hE i, hs' i,
    hFE t' (s' i) (IntExp.expF_of_expT V _ D A G U F k (σ i) (f i) t' (s' i) (hE i) ht' (hs' i)), ⟨j, hj⟩, ?_⟩
  by_contra hn
  push Not at hn
  exact hj (eq_zero_of_sval D.P.isLB (s' i β)
    (fun y J hJ => (hs' i β y J hJ).trans (sval_eq_zero _ hn _ _ _)) j)

end GlobalTheory.UU.IntWit
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.psiScalars_relations_up_to_baseUnits : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) := by
  first | exact @GlobalTheory.PsiScalUnit.main | exact GlobalTheory.PsiScalUnit.main | (intros; apply GlobalTheory.PsiScalUnit.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))))

theorem scal_specMap {A C : Type} [CommRing A] [CommRing C] (φ : A →+* C) {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (a : A) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) a = scal p (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact congrArg p.appTop.hom e.symm

theorem gs_scal_inv_mul {R : Type} [CommRing R] [IsDomain R] {Y₁ Y₂ Z : Scheme.{0}}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of (FractionRing R))) (p₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂) (h : r₂ ≫ p₂ = ((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) (z : Z)
    {a : R} (ha : a ≠ 0) :
    gs r₁ z ⊤ (scal p₁ (algebraMap R (FractionRing R) a)⁻¹) * gs r₂ z ⊤ (scal p₂ a) = 1 := by
  have k : ∀ {S : Type} [CommRing S] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of S)) (r : Z ⟶ Y) (c : S),
      gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
    intro S _ Y p r c
    calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
      _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
      _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl
  have e : scal (((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) a =
      scal (r₁ ≫ p₁) (algebraMap R (FractionRing R) a) :=
    (scal_specMap _ _ a).trans (scal_specMap _ _ _)
  have ha' : algebraMap R (FractionRing R) a ≠ 0 := fun h0 =>
    ha (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
  rw [k p₁, k p₂, h, e, ← gs_mul _ z ⊤ trivial, scal, scal, ← map_mul, ← map_mul, inv_mul_cancel₀ ha', map_one, map_one,
    gs_eq _ z ⊤ trivial, map_one, map_one]

theorem expF_of_expands : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ t s hσ hK hE
  obtain ⟨r, hr, τ, f, hτ, hf, hE⟩ := hE
  have hL := hM.LG
  have hX := fun τ₀ τ' f' h₁ h₂ h₃ => expT_of_expandsAt R I D A G U U' hM k τ τ₀ τ' f f' h₁ h₂ h₃ hE
  clear hE hM
  cases U'
  dsimp only at hL
  subst hL
  cases hσ
  obtain ⟨e₁, -, e₃, -⟩ := GlobalTheory.UnitSec.same_exists R D.toPre G U.P.L.L U.P.L.isLB k
  obtain ⟨τ', hτ'⟩ := e₁ τ
  obtain ⟨f', hf'⟩ := e₃ f
  refine ⟨1, fun _ => (algebraMap R (FractionRing R) r)⁻¹, fun _ => τ', fun _ => f',
    fun _ => hX τ τ' f' HEq.rfl hτ' hf', ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    refine (hK Z rA y h₁ z JA JG hJA hJG).trans ?_
    rw [Fin.sum_univ_one, hτ' Z rG z JG hJG, h₂]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal hτ y z hJG)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rA y ?_ z hr).symm)
    have w₁ := Over.w (fst (TFK (R := R) (FractionRing R)) A.A)
    have w₂ := Over.w (snd (TFK (R := R) (FractionRing R)) A.A)
    have w₃ := Over.w U.gen.hom
    have w₄ : (rA ≫ (fst (TFK (R := R) (FractionRing R)) A.A).left) ≫ jFK (R := R) (FractionRing R) =
        y ≫ pullback.snd G.hom (jK R) :=
      (Category.assoc _ _ _).trans ((congrArg (rA ≫ ·) (w₁.trans w₂.symm)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ A.A.hom) h₁).trans ((Category.assoc _ _ _).trans (congrArg (y ≫ ·) w₃)))))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) w₄.symm)
  · intro α Z rF rB h₁ z J hJ
    rw [Fin.sum_univ_one, hf' α Z rB z J hJ, h₁]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal (hf α) rF z hJ)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rF rF ?_ z hr).symm)
    have w₁ := Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)
    exact (congrArg (rF ≫ ·) w₁.symm).trans ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm)

end GlobalTheory.UU
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → (∀ L : RigLB B, (∃ t : LB.Gen (Theta B L.L), t.IsGen) → (∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]), t.IsGen) → ∃ M : CP B, M.L = L) ∧ ∀ (S' : Scheme.{0}) (f : S' ⟶ S) (B' : Over S') [GrpObj B'] [IsCommMonObj B'], IsAbelianScheme B' → ∀ (M : CP B) (M' : CP B') (β : B'.left ⟶ B.left), IsGrpPullback B' B f β → (∃ r : LB.Gen (M'.L.L.pull (eSec B')), r.IsGen) → LBIso M'.L.L (M.L.L.pull β) → IsCPPullback M' M f β) := by
  first | exact @GlobalTheory.AbPackage.abelian_cp | exact GlobalTheory.AbPackage.abelian_cp | (intros; apply GlobalTheory.AbPackage.abelian_cp <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.mumfordTower_repWt_unique : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ (χ : s.X) (c c' : 𝟙_ _ ⟶ a.B), (∀ e, a.RepWt c χ e) → (∀ e, a.RepWt c' χ e) → c = c' := by
  first | exact @GlobalTheory.UU.repWt_unique | exact GlobalTheory.UU.repWt_unique | (intros; apply GlobalTheory.UU.repWt_unique <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.dim_eq_abelianPart_dim_add_torus_rank : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (g' : ℕ), (SmoothOfRelativeDimension g' (t.l 0).Q.B.hom → A.g = g' + Module.finrank ℤ s.X) ∧ ∀ a : t.Alg, SmoothOfRelativeDimension g' a.B.hom → A.g = g' + Module.finrank ℤ s.X := by
  first | exact @GlobalTheory.UU.Tower.dim_eq_add_finrank | exact GlobalTheory.UU.Tower.dim_eq_add_finrank | (intros; apply GlobalTheory.UU.Tower.dim_eq_add_finrank <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_formalTorus_points_semiAbelian_model : AllSet fun {V} _ _ _ {_} {G} _ _ s => ∀ (t : Tower s) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∃ ι' : (Multiplicative s.X →* Wˣ) →* (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G), Function.Injective ι' ∧ ∀ (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (a : Multiplicative s.X →* Wˣ), x = ι' a ↔ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (a (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ x.left := by
  first | exact @GlobalTheory.UU.exists_formalTorus_points | exact GlobalTheory.UU.exists_formalTorus_points | (intros; apply GlobalTheory.UU.exists_formalTorus_points <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.additionFormula_tensor_ne_zero : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∑ i, TensorProduct.tmul F (t i) (t' i) ≠ 0 := by
  first | exact @GlobalTheory.addition_tensor_ne_zero | exact GlobalTheory.addition_tensor_ne_zero | (intros; apply GlobalTheory.addition_tensor_ne_zero <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  first | exact @GlobalTheory.addB_tensor_ne_zero_iff | exact GlobalTheory.addB_tensor_ne_zero_iff | (intros; apply GlobalTheory.addB_tensor_ne_zero_iff <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.tau_bimult_psi_even_over_extension_field : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F], ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ a b m : D.X, val (Z := (TF (R := R) F).left) (D.psi (a + b + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J * rigV D z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ m) = val (Z := (TF (R := R) F).left) (D.psi (a + b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + m)) (jFK (R := R) F) z J) ↔ D.TauBimult) ∧ ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ m : D.X, val (Z := (TF (R := R) F).left) (D.psi (-m)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) m).left z J = val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J) ↔ D.PsiEven) := by
  first | exact @GlobalTheory.TauValues.main | exact GlobalTheory.TauValues.main | (intros; apply GlobalTheory.TauValues.main <;> assumption)
end
