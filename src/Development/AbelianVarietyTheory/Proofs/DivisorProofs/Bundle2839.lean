module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLaws
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PsiSignRel

open GlobalTheory.UT.SymFrame

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem act_zero' (o : D.OAct O) : o.onB.act (0 : O) = 1 := by
  have h := o.onB.map_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem act_add' (o : D.OAct O) (a c : O) : o.onB.act a * o.onB.act c = o.onB.act (a + c) :=
  (o.onB.map_add a c).symm

theorem act_comp' (o : D.OAct O) (a c : O) : o.onB.act a ≫ o.onB.act c = o.onB.act (c * a) :=
  (o.onB.map_mul c a).symm

theorem act_natCast' (o : D.OAct O) (n : ℕ) : o.onB.act (n : O) = 𝟙 D.P.A ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero', pow_zero]
  | succ n ih => rw [Nat.cast_succ, ← act_add', ih, o.onB.map_one, pow_succ]

theorem act_pow' (o : D.OAct O) (a : O) (n : ℕ) : o.onB.act a ^ n = o.onB.act ((n : O) * a) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, act_zero']
  | succ n ih => rw [pow_succ, ih, act_add', Nat.cast_succ, add_one_mul]

theorem prod_gam {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x : T ⟶ A) {U : Type} [CommGroup U]
    (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(𝟙 A ^ 5).left, (𝟙 A ^ 4).left, 𝟙 _, (1 : A ⟶ A).left] : Fin 4 → _) i) ^
      (![2, -3, -2, 3] : Fin 4 → ℤ) i =
      k (x ^ 5).left ^ 2 * (k (x ^ 4).left ^ 3)⁻¹ * (k x.left ^ 2)⁻¹ * k (1 : T ⟶ A).left ^ 3 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ 𝟙 A ^ 5).left ^ (2 : ℤ) * k (x ≫ 𝟙 A ^ 4).left ^ (-3 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) *
    k (x ≫ 1).left ^ (3 : ℤ) = _
  rw [MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_one, Category.comp_id, zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat,
    zpow_ofNat, zpow_ofNat]



theorem core_id (hG : GlobalFnsSt) (o : D.OAct O) (w : O) (u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w)) (hu : Normd u)
    (gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]))
    (hgam : Normd gam)
    (ra : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star (1 + w))) (o.onB.act (1 + w))) rosatiε))
    (hra : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star (1 + w))) (o.onB.act (1 + w)) ra)
    (rw' : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star w)) (o.onB.act w)) rosatiε))
    (hrw : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star w)) (o.onB.act w) rw')
    (hw : w + star w = 1) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (z : T.left) {J} (hJ : Good D.P.L z J) :
    val u (b ^ 4).left z J * val₂ ra z J ((b ^ 4) ≫ o.onB.act (1 + w)) b ^ 2 * val gam (b ≫ o.onB.act (1 + w)).left z J =
      th D z J (b ^ 4 * b ^ 4) ((b ^ 4) ≫ o.onB.act (star w * w)) b ^ 2 * th D z J (b ^ 4) (b ^ 4) b ^ 2 *
        val gam b.left z J ^ 2 * val₂ rw' z J ((b ^ 4) ≫ o.onB.act w) b ^ 2 * val gam (b ≫ o.onB.act w).left z J := by
  have hm : ∀ t : O, IsMonHom (o.onB.act t) := o.onB.hom
  have Gu := (grep_gen (Y := D.P.A) u hu.1 (o.onB.act 4).left).congr (P' := fun _ _ h =>
      h (o.onB.act 4 * (o.onB.act 4 ≫ o.onB.act w)).left * (h (o.onB.act 4).left ^ 2)⁻¹ *
        (h (o.onB.act 4 ≫ o.onB.act w).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ 2)
    (fun _ _ h => GlobalTheory.PsiWZeroPull.prod_four _ _ h) (fun _ _ _ _ _ => rfl)
  have Gra := (grep_gen (Y := D.P.A) ra hra.1 (lift (o.onB.act 4 ≫ o.onB.act (1 + w)) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Grw := (grep_gen (Y := D.P.A) rw' hrw.1 (lift (o.onB.act 4 ≫ o.onB.act w) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Gga := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act (1 + w)).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggw := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act w).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggb := (grep_gen (Y := D.P.A) gam hgam.1 (Over.Hom.left (𝟙 D.P.A))).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Gt2 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4 * o.onB.act 4) (o.onB.act 4 ≫ o.onB.act (star w * w)) (𝟙 D.P.A)
  have Gt1 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4) (o.onB.act 4) (𝟙 D.P.A)
  have key := (((Gu.mul (Gra.pow 2)).mul Gga).mul (((((Gt2.pow 2).mul (Gt1.pow 2)).mul (Ggb.pow 2)).mul
    (Grw.pow 2)).mul Ggw).inv).triv hG (fun U _ h => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have e1 : 𝟙 D.P.A = o.onB.act 1 := o.onB.map_one.symm
      have e0 : (1 : D.P.A ⟶ D.P.A) = o.onB.act 0 := (act_zero' o).symm
      have hsw : star w = 1 - w := eq_sub_of_add_eq' hw
      simp only [e1, e0, act_add', act_comp', act_pow', star_add, star_one, hsw]
      ring_nf
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
      abel) (fun y I hI => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      have o1 : ∀ t : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫ (o.onB.act t).left =
          (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left := fun t => by
        rw [← Over.comp_left, MonObj.one_comp]
      have l1 : ∀ t t' : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫
          (lift (o.onB.act t ≫ o.onB.act t') (𝟙 D.P.A)).left =
          (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1).left := fun t t' => by
        rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, MonObj.one_comp, MonObj.one_comp]
      beta_reduce
      rw [o1, l1, l1, o1, o1, Over.id_left, Category.comp_id, normd_one hu hI, normd_one hgam hI]
      have r1 := hra.val_origin hI
      have r2 := hrw.val_origin hI
      unfold val₂ at r1 r2
      rw [r1, r2]
      simp only [MonObj.comp_mul, MonObj.one_comp, Category.comp_id, _root_.mul_one, C.face, one_pow, inv_one, normd_one hgam hI]) T b z J hJ
  have c4 : b ≫ o.onB.act 4 = b ^ 4 := by
    have := act_natCast' o 4
    rw [Nat.cast_ofNat] at this
    rw [this, comp_id_pow]
  beta_reduce at key
  simp only [← Over.comp_left, comp_lift, ← Category.assoc, c4, MonObj.comp_mul, Category.comp_id] at key
  exact mul_inv_eq_one.1 key



theorem sign_rel : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (O : Type) [CommRing O] [StarRing O] [Module O D.X] (o : D.OAct O) (w : O), w + star w = 1 → ∀ u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w), Normd u → ∀ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam → ∀ p q r : QkPt D F 4, q.y = w • p.y → r.y = (1 + w) • p.y → GtAct o w p.g q.g → GtAct o (1 + w) p.g r.g → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ s s' s'' : ((TF (R := R) F).left.presheaf.stalk z)ˣ, s * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J → s' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (q.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (q.g.s q.y) (𝟙 _) z J ^ 2 * val gam q.g.b.left z J → s'' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (r.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (r.g.s r.y) (𝟙 _) z J ^ 2 * val gam r.g.b.left z J → s'' = s ^ 2 * s' → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) * val u (cP D (TF (R := R) F) p.y).left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J := by
  intro R _ _ D F _ _ O _ _ _ o w hw u hu gam hgam p q r hq hr hgq hgr z J hJ s s' s'' hs hs' hs'' hss
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hb4 : cP D (TF (R := R) F) p.y = p.g.b ^ 4 := cPoint_y p
  obtain ⟨qb, qv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o w p.g q.g).1 hgq
  obtain ⟨rb, rv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o (1 + w) p.g r.g).1 hgr
  have eq1 := qv (w • p.y) z J hJ
  have eq2 := rv ((1 + w) • p.y) z J hJ
  have sm1 : star w • w • p.y = (star w * w) • p.y := smul_smul _ _ _
  have sm2 : star (1 + w) • (1 + w) • p.y = (p.y + p.y) + (star w * w) • p.y := by
    rw [smul_smul, show star (1 + w) * (1 + w) = 1 + 1 + star w * w by
      rw [star_add, star_one]; linear_combination hw, add_smul, add_smul, one_smul]
  have e3 : (1 + w) • p.y = p.y + w • p.y := by rw [add_smul, one_smul]
  rw [sm1, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq1
  rw [sm2, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq2
  have g1 := GlobalTheory.TorusExt.charVal_add p.g hJ p.y p.y
  have g2 := GlobalTheory.TorusExt.charVal_add p.g hJ (p.y + p.y) ((star w * w) • p.y)
  rw [cPoint_add, GlobalTheory.TorusExt.cPoint_smul o, hb4] at g2
  rw [hb4] at g1
  have cid := core_id hG o w u hu gam hgam (GlobalTheory.TorusExt.rosGen hG o (1 + w)) (GlobalTheory.TorusExt.rosGen_isRos hG o (1 + w))
    (GlobalTheory.TorusExt.rosGen hG o w) (GlobalTheory.TorusExt.rosGen_isRos hG o w) hw p.g.b z hJ
  have vτ : @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) =
      @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi ((1 + w) • p.y)) (jFK (R := R) F) z J) *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi p.y) (jFK (R := R) F) z J))⁻¹ *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (w • p.y)) (jFK (R := R) F) z J))⁻¹ *
        (rigV D (TF (R := R) F).hom z J)⁻¹ := by
    rw [e3]
    exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans
        (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans rfl))))
  have gq : val gam q.g.b.left z J = val gam (p.g.b ≫ o.onB.act w).left z J := by rw [qb]
  have gr : val gam r.g.b.left z J = val gam (p.g.b ≫ o.onB.act (1 + w)).left z J := by rw [rb]
  rw [hq, gq] at hs'
  rw [hr, gr] at hs''
  rw [vτ, hb4]
  simp only [id_eq] at hs hs' hs'' ⊢
  apply Additive.ofMul.injective
  have E := fun {a c : ((TF (R := R) F).left.presheaf.stalk z)ˣ} (e : a = c) => congrArg Additive.ofMul e
  have hs := E hs; have hs' := E hs'; have hs'' := E hs''; have hss := E hss
  have eq1 := E eq1; have eq2 := E eq2; have g1 := E g1; have g2 := E g2; have cid := E cid
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at hs hs' hs'' hss eq1 eq2 g1 g2 cid ⊢
  linear_combination (norm := module) hs'' - 2 • hs - hs' - hss + 2 • eq2 - 2 • eq1 + 2 • g2 + 2 • g1 + cid

end GlobalTheory.PsiSignRel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

section Reg

variable {X X' Y W : Scheme.{0}} (L : LB X) (L' : LB X')

def tr {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (I : (Y ⟶ X) → L.ι) (ψ : Y ⟶ X) :
    (Z.presheaf.stalk z)ˣ :=
  gm (r ≫ ψ) z (L.U (J (r ≫ ψ)) ⊓ L.U (I ψ)) (L.g (J (r ≫ ψ)) (I ψ))

def Reg (F : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ)
    (c : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U) : Prop :=
  ∀ (y : Y) I I', Good L y I → Good L' y I' → ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' →
      F Z r z J J' = c _ (tr L r z J I) (tr L' r z J' I') * gm r z V u

variable {L L'}
variable {F G : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ}
  {c d : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U}

theorem Reg.mul (hF : Reg L L' F c) (hG : Reg L L' G d) :
    Reg L L' (fun Z r z J J' => F Z r z J J' * G Z r z J J') (fun U _ h h' => c U h h' * d U h h') := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  obtain ⟨V', hV', u', hu'⟩ := hG y I I' hI hI'
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, res inf_le_left u * res inf_le_right u', fun Z r z J J' hz hJ hJ' => ?_⟩
  rw [map_mul, gm_res r z _ hz, gm_res r z _ hz]
  show F Z r z J J' * G Z r z J J' = _
  rw [hu Z r z J J' hz.1 hJ hJ', hu' Z r z J J' hz.2 hJ hJ', _root_.mul_mul_mul_comm]

theorem Reg.inv (hF : Reg L L' F c) :
    Reg L L' (fun Z r z J J' => (F Z r z J J')⁻¹) (fun U _ h h' => (c U h h')⁻¹) := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  refine ⟨V, hV, u⁻¹, fun Z r z J J' hz hJ hJ' => ?_⟩
  show (F Z r z J J')⁻¹ = _
  rw [map_inv, hu Z r z J J' hz hJ hJ', mul_inv]

theorem good_exists {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem Reg.glue (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      F Z r z J J' = gm r z ⊤ a := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' → F Z r z J J' = gm r z V u := by
    intro y
    obtain ⟨I, hI⟩ := good_exists hL y
    obtain ⟨I', hI'⟩ := good_exists hL' y
    obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
    exact ⟨V, hV, u, fun Z r z J J' hz hJ hJ' => by rw [hu Z r z J J' hz hJ hJ', hc, _root_.one_mul]⟩
  choose V hV u hu using H
  obtain ⟨a, ha⟩ := glue_unit ⊤ V (fun _ => le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩) u
    (fun i j x hx => by
      obtain ⟨I, hI⟩ := good_exists hL x
      obtain ⟨I', hI'⟩ := good_exists hL' x
      exact (hu i _ (𝟙 Y) x I I' hx.1 hI hI').symm.trans (hu j _ (𝟙 Y) x I I' hx.2 hI hI'))
  refine ⟨a, fun Z r z J J' hJ hJ' => ?_⟩
  rw [hu (r z) Z r z J J' (hV _) hJ hJ', ← ha, gm_res r z _ (hV _)]

theorem Reg.rigid (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) {S : Scheme.{0}} (p : Y ⟶ S)
    (hp : Function.Surjective p.appTop.hom) {Z : Scheme.{0}} (r r' : Z ⟶ Y) (hr : r ≫ p = r' ≫ p) (z : Z) {J J'}
    (hJ : Good L z J) (hJ' : Good L' z J') : F Z r z J J' = F Z r' z J J' := by
  obtain ⟨a, ha⟩ := hF.glue hL hL' hc
  obtain ⟨a₀, e⟩ := hp a.val
  rw [ha Z r z J J' hJ hJ', ha Z r' z J J' hJ hJ']
  apply Units.ext
  have k : ∀ q : Z ⟶ Y, (gm q z ⊤ a).val = gs (q ≫ p) z ⊤ a₀ := fun q => by
    rw [← gs_unit q z ⊤ trivial, ← e]
    exact gs_pull q p z ⊤ trivial a₀
  rw [k, k, hr]

variable {K : Type} [Fintype K]

theorem reg_val {φ : K → (W ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z J _ => val t (r ≫ p) z J) (fun _ _ h _ => ∏ k, h (p ≫ φ k) ^ ε k) := by
  intro y I I' hI _
  refine ⟨p ⁻¹ᵁ LB.wchart L φ (fun k => I (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz hJ _ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

theorem reg_val' {φ : K → (W ⟶ X')} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L' φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z _ J' => val t (r ≫ p) z J') (fun _ _ _ h' => ∏ k, h' (p ≫ φ k) ^ ε k) := by
  intro y I I' _ hI
  refine ⟨p ⁻¹ᵁ LB.wchart L' φ (fun k => I' (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz _ hJ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

def wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} (w : LB.Iso L' (LB.LinComb L pr ε)) {Z : Scheme.{0}} (q : Z ⟶ X') (z : Z)
    (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) : (Z.presheaf.stalk z)ˣ :=
  gv w q z (fun k => J (q ≫ pr k)) (J' q)

theorem reg_wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) (p : Y ⟶ X') :
    Reg L L' (fun _ r z J J' => wv w (r ≫ p) z J J') (fun _ _ h h' => (∏ k, h (p ≫ pr k) ^ ε k) * (h' p)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (LB.wchart L pr (fun k => I (p ≫ pr k)) ⊓ L'.U (I' p)), ⟨hI.mem pr p, hI' p⟩,
    pullU p _ (w.s (fun k => I (p ≫ pr k), I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gm_isGen hw (r ≫ p) z _ (fun k => I (p ≫ pr k)) _ (I' p) (hJ.mem pr (r ≫ p)) hz.1 (hJ' _) hz.2).trans
    (congrArg (· * _) (congrArg₂ (· * ·) ?_ rfl))
  refine (gm_linComb L pr ε (r ≫ p) z _ _ (hJ.mem pr (r ≫ p)) hz.1).trans ?_
  rfl

end Reg

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg in
theorem reg_lam {S S' Y : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)} (hw : w.IsGen) (p : Y ⟶ (G2 B').left) :
    Reg M M' (fun _ r z J J' => lamVal w (r ≫ p) z J J')
      (fun _ _ h h' => (∏ k, h ((p ≫ β₂) ≫ lamφ B k) ^ lamε k) * (∏ k, h' (p ≫ lamφ B' k) ^ lamε k)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (((abelian₂ B M).pull β₂).U (fun _ => ind B I (p ≫ β₂)) ⊓ (abelian₂ B' M').U (ind B' I' p)),
    ⟨mem_pull.2 (good_ind hI (p ≫ β₂)), good_ind hI' p⟩,
    pullU p _ (w.s (fun _ => ind B I (p ≫ β₂), ind B' I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (lamVal_eq w (r ≫ p) z J J').trans ?_
  refine ((isGen_iff w).1 hw Z (r ≫ p) z _ (ind B I (p ≫ β₂)) _ (ind B' I' p) (good_ind hJ ((r ≫ p) ≫ β₂))
    (mem_pull.1 hz.1) (good_ind hJ' _) hz.2).trans (congrArg (· * _) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_)))
  · refine (gm_linComb M (lamφ B) lamε ((r ≫ p) ≫ β₂) z _ _ (good_ind hJ ((r ≫ p) ≫ β₂)) (mem_pull.1 hz.1)).trans ?_
    rfl
  · refine (gm_linComb M' (lamφ B') lamε (r ≫ p) z _ _ (good_ind hJ' _) hz.2).trans ?_
    rfl

section Scale

variable {Y : Scheme.{0}} {M : LB Y}

def scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun i => res le_top a * t.s i⟩

theorem gm_scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (i : M.ι) (h : r z ∈ M.U i) :
    gm r z (M.U i) ((scale a t).s i) = gm r z ⊤ a * gm r z (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ h a))

theorem scale_isGen (a : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (scale a t).IsGen := fun i j =>
  unit_ext fun y hy => by
    have e := congrArg (gm (𝟙 Y) y _) (ht i j)
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_scale a t _ y i hy.1, gm_scale a t _ y j hy.2, e, mul_left_comm]

end Scale

theorem mapsAtExp_of_val {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {K : Type}
    [Fintype K] {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) {p : Y ⟶ X'} {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))} (ha : a.IsGen)
    {b : LB.Gen (LB.LinComb L (K := K) (fun i => p ≫ pr i) (fun i => n * ε i))} (hb : b.IsGen)
    (H : ∀ (y : Y) J J', Good L y J → Good L' y J' → val b (𝟙 Y) y J = wv w p y J J' ^ n * val a (𝟙 Y) y J') :
    MapsAtExp L L' pr ε w p n a b := by
  intro jN jL
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := good_exists hL y
  obtain ⟨J', hJ'⟩ := good_exists hL' y
  have e := H y J J' hJ hJ'
  rw [val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]),
    val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])] at e
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun i => p ≫ pr i) (fun i => J (p ≫ pr i)) := Set.mem_iInter.2 fun i => hJ _
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' (fun _ : PUnit => p) (fun _ => J' p) := Set.mem_iInter.2 fun i => hJ' _
  have eb := gen_trans hb (𝟙 Y) y (mapsAtExp_le_b L L' pr ε p jN jL hy) m₁
  have ea := gen_trans ha (𝟙 Y) y (mapsAtExp_le_a L L' pr ε p jN jL hy) m₂
  have ew := gm_isGen hw p y jN (fun i => J (p ≫ pr i)) jL (J' p) hy.1 (hJ.mem pr p) hy.2 (hJ' p)
  have el := gm_linComb L pr ε p y jN (fun i => J (p ≫ pr i)) hy.1 (hJ.mem pr p)
  refine (gm_res _ y _ hy _).trans (eb.trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans
      ((congrArg (fun q : Y ⟶ X' => gv w q y jN jL) (Category.id_comp p)).trans
        (ew.trans (congrArg (fun x => x * _ * _) el)))))) ((gm_res _ y _ hy _).trans ea))).symm))
  rw [e]
  simp only [trF, wv, Category.id_comp, Fintype.prod_unique, mul_zpow, ← Finset.prod_zpow, inv_zpow, ← zpow_mul,
    mul_comm n]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumCmp.Point
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem formEq_twist_cube : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := by
  intro R _ _ D₂ D T Y₀ q y p₂ β _ hp b χ₂ χ U _ h
  have hu : ∀ x : T ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit T := fun x => toUnit_unique _ _
  have ht : ∀ x : T ⟶ D₂.P.A, ∏ i, h (x.left ≫ GlobalTheory.MumCmp.twφ D₂ D β b i) ^ GlobalTheory.MumCmp.twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.Oφ p₂ χ₂ k = ((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ p : Fin 4 × Fin 3, h (D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) ^ (Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) =
      ∏ k : Fin 4, (h (((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k ≫ β) * (toUnit T ≫ b)).left *
        (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left) ^ Oinvε k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (Oinvε k) (GlobalTheory.MumCmp.twε i), zpow_mul, hx]
  have h0 : (p₂ * (toUnit T ≫ D₂.c χ₂)) ≫ β = (q ≫ y) * (toUnit T ≫ D₂.c χ₂ ≫ β) := by
    rw [MonObj.mul_comp, hp, Category.assoc]
  have h3 : (1 : T ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  have hC : ∏ k, h (D.Oφ (q ≫ y) χ k) ^ (-Oinvε k) = h ((q ≫ y) * (toUnit T ≫ D.c χ)).left *
      (h (toUnit T ≫ D.c χ).left)⁻¹ * (h (q ≫ y).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    rw [Fin.prod_univ_four]
    show h ((q ≫ y) * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
      h (q ≫ y).left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ) = _
    simp only [zpow_neg, zpow_one, inv_inv]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hA, prod_cub, hC, GlobalTheory.CoordCompare.prod_diff, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    h0, h3, hp, _root_.one_mul, Category.assoc]
  simp only [Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumCmp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secRatio_app_restrict {Y Z : Scheme.{0}} (h : Z ⟶ Y) {U W : Y.Opens} (hle : W ≤ U)
    (hle' : h ⁻¹ᵁ W ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (Z.presheaf.map (homOfLE hle').op).hom ((h.app U).hom x) =
      (h.app W).hom ((Y.presheaf.map (homOfLE hle).op).hom x) := by
  have := congrArg (fun φ => φ.hom x) (h.naturality (homOfLE hle).op)
  simpa using this.symm

theorem secRatioEq_comp : ∀ {X Y Z : Scheme.{0}} (L : LB X) {k k' : ℕ} (u v : Y ⟶ X) (h : Z ⟶ Y) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k'), SecRatioEq L u v s₁ s₂ t₁ t₂ → SecRatioEq L (h ≫ u) (h ≫ v) s₁ s₂ t₁ t₂ := by
  intro X Y Z L k k' u v h s₁ s₂ t₁ t₂ hR i i'
  have e := congrArg (h.app (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')).hom (hR i i')
  simp only [map_mul] at e
  simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i'),
    secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')]
  exact e

end GlobalTheory.Mum
end
