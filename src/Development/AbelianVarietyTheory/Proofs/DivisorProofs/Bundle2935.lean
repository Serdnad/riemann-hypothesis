module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle018
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle121
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PowPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.SiegelPower

def siegLam (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] (P : PolAV (Sp R)) [IsCommMonObj P.A] :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := P.A
  ab := P.isAb
  P := abelian₂ P.A P.L
  isLB := LB.isLB_linComb P.isLB _ _
  rig₁ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull P.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG P.isAb (pull_isLB (LB.isLB_linComb P.isLB _ _) _) _

theorem det_eq_one {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (hpd : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef)
    (hdet : IsUnit (W + W.transpose).det) : (W + W.transpose).det = 1 := by
  have h₁ := hpd.det_pos
  have h₂ : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).det = (((W + W.transpose).det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [h₂] at h₁
  rcases Int.isUnit_iff.1 hdet with h | h
  · exact h
  · rw [h] at h₁; norm_num at h₁

theorem exists_pow_polAV : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ P.A)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ P'.g = r * P.g ∧ LBIso P'.L (LB.LinComb P.L (tensφ pr) (tensε W)) := by
  intro R _ _ _ _ P r W hpd hdet
  have := P.isAb.comm
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := siegLam hG P
  have hP : c.P.IsLB := c.isLB
  have hD : c.diag.IsLB := pull_isLB hP _
  have hfin : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := inferInstanceAs (IsFinite (𝟙 P.A.left))
  have hamp : RelAmple c.A c.diag := by
    have e := lbIso_diag L₁ P
    have h := relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb P.isLB hfin
    exact (relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) (lbPow P.L 2) 1 one_pos P.isAb P.isAb
      (LB.isLB_linComb P.isLB _ _) hfin).2.2.2 _ hD e (h.2.1.2 P.ample)
  let G := Out.powObj P.A r
  let pr : Fin r → (G ⟶ P.A) := Out.powPr P.A
  have hpr : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have hu : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ P.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit P.A r).lift (Fan.mk T y), fun u => (Out.powIsLimit P.A r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit P.A r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hB : ∀ (T : Over (Sp R)) (x x' y : T ⟶ c.A), bi hP (x * x') y = bi hP x y + bi hP x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2
      (GlobalTheory.T.biadditive_of_trivial_on_axes hG (Sp R) c.A c.diag c.ab hD hamp c.P hP c.rig₁ c.rig₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [bi]
    abel
  have hs : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), bi hP x y = bi hP y x := fun T x y => by
    have e : cls c.P hP = bi hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    rw [bi, e, pull_bi, lift_fst, lift_snd]
  have hLB : (sharp c.P pr W).IsLB := LB.isLB_linComb hP _ _
  refine ⟨{ A := G
            isAb := isAbelianScheme_powObj_of_isAbelianScheme P.A P.isAb r
            g := r * P.g
            smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ r P.smoothDim
            L := sharp c.P pr W
            isLB := hLB
            rigid := rigidified_sharp hP pr W hpr hB
            sym := sym_sharp hP pr W hpr hB hs
            ample := GlobalTheory.T.relAmple_formBundle_power_of_posDef hG 0 1 r R 1 (Sp R) (𝟙 _) c G pr W hpr hu hamp hpd
            ktriv := kTriv_sharp hP pr W hpr hB hs hu (det_eq_one W hpd hdet)
              (fun T x hx => eq_one_of_lam P.isLB P.ktriv x hx) }, pr, hpr, ⟨Out.powIsLimit P.A r⟩, rfl, ?_⟩
  refine lbIso_nested P.isLB _ _ (fun uv : Fin r × Fin r => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ _ ?_
  simp only [prod_lam (pr _) (pr _) (PrimNorm.cls P.L)]
  rw [Fintype.prod_prod_type (f := fun k : (Fin r × Fin r) × Fin 4 => PrimNorm.cls P.L (tensφ pr k) ^ tensε W k)]
  refine Finset.prod_congr rfl fun uv _ => ?_
  simp only [Fin.prod_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, diff₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, zpow_mul]
  simp only [zpow_one, zpow_neg, mul_zpow, inv_zpow]

end GlobalTheory.Mum.PowPol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensPer

theorem prod_psum_two {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {U : Type} [CommGroup U]
    (H : ((G ⊗ G).left ⟶ G.left) → U) :
    ∏ K : ULift.{0} (Finset (Fin 2)), H (psum G (x2 G) K.down).left ^ ((-1 : ℤ) ^ (2 - K.down.card)) =
      H (psum G (x2 G) {0, 1}).left * (H (psum G (x2 G) {0}).left)⁻¹ * (H (psum G (x2 G) {1}).left)⁻¹ *
        H (psum G (x2 G) ∅).left := by
  refine (Fintype.prod_equiv Equiv.ulift _
    (fun I => H (psum G (x2 G) I).left ^ ((-1 : ℤ) ^ (2 - I.card))) fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q₂ : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₂, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem periods_alg {U : Type} [CommGroup U] {X : Type} [AddCommGroup X] {P : Type} [Mul P] (c : X → P)
    (c_add : ∀ x y, c (x + y) = c x * c y) (t : X → X → U) (θ : P → P → P → U) (symm : ∀ x y, t x y = t y x)
    (add : ∀ x x' y, t (x + x') y * θ (c x) (c x') (c y) = t x y * t x' y) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (a b : Fin r → X) :
    (∏ i, ∏ j, t (a i + b i) (a j + b j) ^ W i j) * (∏ i, ∏ j, t (a i) (a j) ^ W i j)⁻¹ *
        (∏ i, ∏ j, t (b i) (b j) ^ W i j)⁻¹ =
      (∏ i, ∏ j, (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j)) * ∏ i, ∏ j, t (a i) (b j) ^ ((W + W.transpose) i j) := by
  have base : ∀ x x' y y' : X, t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ =
      (θ (c x) (c x') (c y * c y') * θ (c y) (c y') (c x) * θ (c y) (c y') (c x'))⁻¹ * (t x y' * t y x') := by
    intro x x' y y'
    have e₁ := add x x' (y + y')
    have e₂ := add y y' x
    have e₃ := add y y' x'
    rw [c_add] at e₁
    have s₁ := symm x (y + y')
    have s₂ := symm x' (y + y')
    have s₃ := symm y x
    have s₄ := symm y' x
    have s₅ := symm y' x'
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃
    have b₁ := E s₁; have b₂ := E s₂; have b₃ := E s₃; have b₄ := E s₄; have b₅ := E s₅
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ b₃ b₄ b₅ ⊢
    linear_combination (norm := abel) a₁ + a₂ + a₃ + b₁ + b₂ + b₃ + b₄ + b₅
  have hij : ∀ i j, t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ * (t (b i) (b j) ^ W i j)⁻¹ =
      (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j) * (t (a i) (b j) ^ W i j * t (a j) (b i) ^ W i j) := by
    intro i j
    rw [← inv_zpow, ← inv_zpow, ← mul_zpow, ← mul_zpow, base, zpow_neg, ← inv_zpow, ← mul_zpow, mul_zpow]
  have hc : ∏ i, ∏ j, t (a j) (b i) ^ W i j = ∏ i, ∏ j, t (a i) (b j) ^ W j i := Finset.prod_comm
  calc _ = ∏ i, ∏ j, (t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ *
        (t (b i) (b j) ^ W i j)⁻¹) := by simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    _ = _ := Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hij i j
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Matrix.add_apply, Matrix.transpose_apply, zpow_add]
      rw [hc]

end GlobalTheory.Mum.TensPer

namespace GlobalTheory.Mum.TensPer
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem groupSchemePartialSum_twoPoints_empty : psum G (x2 G) ∅ = 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_first : psum G (x2 G) {0} = fst G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_second : psum G (x2 G) {1} = snd G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_both : psum G (x2 G) {0, 1} = fst G G * (snd G G * 1) := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] by decide]
  rfl

end GlobalTheory.Mum.TensPer


open GlobalTheory.Mum.TensPer in
theorem GlobalTheory.Mum.Tens.tau_periods : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (T.w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ T.pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j)) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I D D' r W T a b z J J' hJ hJ'
  have twist_vector_at_zero : ∀ (E : DegData R I) (K : ((TK R).left ⟶ E.toPre.P.A.left) → E.toPre.P.L.ι),
      Good E.toPre.P.L z K → val (E.toPre.tau 0 0) (𝟙 _) z K = 1 := by
    intro E K hK
    have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hK E.tau_bimult 0 0 0
    have f : th E.toPre z K (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) = 1 := by
      rw [cPoint_zero]; exact (isCub_cubV E.toPre.cub hK).face 1 1
    rw [f, _root_.mul_one] at e
    have h0 : val (E.toPre.tau (0 + 0) 0) (𝟙 _) z K = val (E.toPre.tau 0 0) (𝟙 _) z K :=
      congrArg (fun x => val (E.toPre.tau x 0) (𝟙 _) z K) (add_zero 0)
    exact mul_eq_left.1 (e.symm.trans h0)
  have hadd : ∀ x x' y : D.toPre.X, val (D.toPre.tau (x + x') y) (𝟙 _) z J *
      cubV D.toPre.cub z J (cP D.toPre (TK R) x) (cP D.toPre (TK R) x') (cP D.toPre (TK R) y) =
      val (D.toPre.tau x y) (𝟙 _) z J * val (D.toPre.tau x' y) (𝟙 _) z J :=
    fun x x' y => GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ D.tau_bimult x x' y
  have hsym : ∀ x y : D.toPre.X, val (D.toPre.tau x y) (𝟙 _) z J = val (D.toPre.tau y x) (𝟙 _) z J :=
    fun x y => GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ x y
  set ρ : TK R ⟶ D'.toPre.P.A ⊗ D'.toPre.P.A :=
    lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) with hρ
  have wv : ∀ (q : (D'.toPre.P.A ⊗ D'.toPre.P.A).left ⟶ D'.toPre.P.A.left) (y : D'.toPre.X),
      ρ.left ≫ q = D'.toPre.xK y →
      gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))) =
      gm (D'.toPre.xK y) z _ (T.w.s (fun k => J (D'.toPre.xK y ≫ tensφ T.pr k), J' (D'.toPre.xK y))) := by
    intro q y h
    have gen : ∀ m m' j j', m = m' → j = j' → gm m z _ (T.w.s j) = gm m' z _ (T.w.s j') := by
      rintro _ _ _ _ rfl rfl; rfl
    refine gen _ _ _ _ h ?_
    refine Prod.ext ?_ ?_
    · dsimp only
      funext k
      rw [← Category.assoc, h]
    · dsimp only
      rw [h]
  have hE : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) ∅).left = D'.toPre.xK 0 := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) 0).left
    rw [groupSchemePartialSum_twoPoints_empty, cPoint_zero, MonObj.comp_one]
  have h₀ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0}).left = D'.toPre.xK a := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) a).left
    rw [groupSchemePartialSum_twoPoints_first, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst]; rfl
  have h₁ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {1}).left = D'.toPre.xK b := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) b).left
    rw [groupSchemePartialSum_twoPoints_second, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_snd]; rfl
  have h₂ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0, 1}).left = D'.toPre.xK (a + b) := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) (a + b)).left
    rw [groupSchemePartialSum_twoPoints_both, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst, lift_snd, cPoint_add]; rfl
  have hA : ∀ i, ρ ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe a i) := fun i => by
    rw [hρ, lift_fst_assoc, Category.assoc, T.c_pr]; rfl
  have hB : ∀ i, ρ ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe b i) := fun i => by
    rw [hρ, lift_snd_assoc, Category.assoc, T.c_pr]; rfl
  have P := prod_psum_two (G := D'.toPre.P.A)
    (fun q => gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))))
  beta_reduce at P
  rw [P]
  rw [wv _ _ h₂, wv _ _ h₀, wv _ _ h₁, wv _ _ hE]
  simp only [hA, hB]
  rw [GlobalTheory.TauBalBox.tau_val D'.toPre hJ' a b (𝟙 _)]
  have hrig : (val D'.toPre.rigK (𝟙 _) z J')⁻¹ = val (D'.toPre.psi 0) (𝟙 _) z J' := by
    have e := GlobalTheory.TauBalBox.tau_val D'.toPre hJ' 0 0 (𝟙 _)
    rw [twist_vector_at_zero D' J' hJ'] at e
    have h0 : val (D'.toPre.psi (0 + 0)) (𝟙 _) z J' = val (D'.toPre.psi 0) (𝟙 _) z J' :=
      congrArg (fun x => val (D'.toPre.psi x) (𝟙 _) z J') (add_zero 0)
    rw [h0, mul_inv_cancel, _root_.one_mul] at e
    exact (inv_mul_eq_one.1 e.symm).symm
  rw [hrig, T.psi (a + b) z J J' hJ hJ', T.psi a z J J' hJ hJ', T.psi b z J J' hJ hJ', T.psi 0 z J J' hJ hJ']
  have hQ0 : ∏ i, ∏ j, val (D.toPre.tau (T.xe 0 i) (T.xe 0 j)) (𝟙 _) z J ^ W i j = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [show T.xe 0 = 0 from map_zero _]
      exact (congrArg (· ^ W i j) (twist_vector_at_zero D J hJ)).trans (one_zpow _)
  have hQab : ∏ i, ∏ j, val (D.toPre.tau (T.xe (a + b) i) (T.xe (a + b) j)) (𝟙 _) z J ^ W i j =
      ∏ i, ∏ j, val (D.toPre.tau (T.xe a i + T.xe b i) (T.xe a j + T.xe b j)) (𝟙 _) z J ^ W i j := by
    rw [map_add (f := _)]; rfl
  rw [hQ0, hQab]
  have key := periods_alg (cP D.toPre (TK R)) (cPoint_add D.toPre (TK R))
    (fun x y => val (D.toPre.tau x y) (𝟙 _) z J) (cubV D.toPre.cub z J) hsym hadd W (T.xe a) (T.xe b)
  beta_reduce at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k ⊢
  linear_combination (norm := abel) k
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalSquares

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_div {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    {k : ℕ} (l N : ℕ) (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) :
    ∃ q : QkPt D.toPre (Kb R) N, q.y = p.y ∧ l • q.g = p.g := by
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_nsmul_eq (F := Kb R) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1.1)
    (n := l) (by omega) p.g
  refine ⟨GlobalTheory.TorusExt.qkMk D.tau_bimult p.y g ?_, rfl, hg⟩
  rw [hN, mul_nsmul', hg]
  exact GlobalTheory.TorusExt.qk_nsmul D.tau_bimult p

theorem qkExt_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) {F F' : Type} [Field F]
    [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') {k N : ℕ}
    (l : ℕ) {p : QkPt D F k} {p' : QkPt D F' k} {q : QkPt D F N} (hp : QkExt σ.toRingHom p p') (hy : q.y = p.y)
    (hg : l • q.g = p.g) : ∃ q' : QkPt D F' N, QkExt σ.toRingHom q q' ∧ q'.y = p'.y ∧ l • q'.g = p'.g := by
  have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext σ.commutes
  refine ⟨GlobalTheory.TorusExt.qkExt hB σ.toRingHom hσ q, (GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).2 rfl, ?_, ?_⟩
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    exact hy
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    show l • GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ q.g = GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ p.g
    rw [← map_nsmul, hg]

theorem pow_left_of_comp {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (x y : TFK (R := R) (Kb R) ⟶ A.A) (h : y.left = spMap σ.toRingHom ≫ x.left)
    (l : ℕ) : (y ^ l).left = spMap σ.toRingHom ≫ (x ^ l).left := by
  let s : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) := Over.homMk (spMap σ.toRingHom) (by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext σ.commutes))
  have hy : y = s ≫ x := Over.OverMorphism.ext h
  have hp : ∀ m : ℕ, s ≫ x ^ m = (s ≫ x) ^ m := fun m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
    | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  rw [hy, ← hp]
  rfl

theorem compPow {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (m : ℕ) :
    (ρ ≫ x) ^ m = ρ ≫ x ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem lab_level {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (hO : OneTrait D.toPre A lab) (k l N : ℕ) (hk : 1 ≤ k)
    (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) N) (hy : q.y = p.y)
    (hg : GtPtF.IsNsmul l q.g p.g) : (lab k p).left = ((lab N q) ^ l).left := by
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, -, -, hG', ⟨ga, hga, hcart, -⟩, hc, hind⟩ := hO
  have := hW.1
  haveI : CharZero W := hW.2.2
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hG := GlobalTheory.globalFns_holds
  have hL := GlobalTheory.firstFiveLaws
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hl
  have hem : em.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb W) :=
    RingHom.ext em.commutes
  have hsq : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hem]
    refine congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    simp only [RingHom.comp_apply]
    rw [hga r]
    exact hc r
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hcart (TFK (R := W) (Kb W)) _ hsq
  let s : Over.mk (spMap em.toRingHom ≫ jFK (R := R) (Kb R)) ⟶ TFK (R := R) (Kb R) :=
    Over.homMk (spMap em.toRingHom) rfl
  have hcomp : ∀ {m : ℕ} (r : QkPt D.toPre (Kb R) m), 1 ≤ m →
      QkToAkU U'.toUnifPre (Kb W) m (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem r))
        (e.symm (s ≫ lab m r)) := by
    intro m r hm
    refine hind m hm r _ _ _ ((GlobalTheory.TorusExt.qkExt_iff hB _ hem _ _).2 rfl) rfl
      ((GlobalTheory.ArcPull.eq_pullQk_iff hD hG hc hB hB' _ _).1 rfl).2 ?_
    rw [← he, e.apply_symm_apply]
    rfl
  have h₁ := hcomp p hk
  have h₂ := (GlobalTheory.LevelCompat.qkToAkU_level hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k l N hk hl hN
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem p))
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem q)) (e.symm (s ≫ lab N q))).2
    (by show hD.xe.symm p.y = hD.xe.symm q.y; rw [hy])
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by
      show GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem p.g) =
        l • GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem q.g)
      rw [(GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hg, map_nsmul, map_nsmul])) (hcomp q hN1)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
  have hx := ((hf _ _).1 h₁).trans ((hf _ _).1 h₂).symm
  have hs : s ≫ lab k p = s ≫ lab N q ^ l := by
    have := congrArg e hx
    rw [e.apply_symm_apply, map_pow, e.apply_symm_apply] at this
    rw [this, compPow]
  have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (spMap em.toRingHom)).1 (congrArg (fun z => z.left) hs)

end GlobalTheory.Mum.GalSquares


open GlobalTheory.Mum.GalSquares in
theorem GlobalTheory.Mum.galEqN_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime →
    Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' →
        (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  intro R _ _ _ hR n hn _ _ D A lab hO ⟨i₀, H⟩ σ j p p' hpp'
  letI := GlobalTheory.TorusExt.gtGroup D.toPre (Kb R)
  have hi : i₀ ≤ max i₀ j := le_max_left _ _
  have hj : j ≤ max i₀ j := le_max_right _ _
  have hN : (n ^ max i₀ j) ^ 2 = n ^ j * n ^ (2 * max i₀ j - j) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hl : 1 ≤ n ^ (2 * max i₀ j - j) := Nat.one_le_pow _ _ hn.pos
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  obtain ⟨q, hqy, hqg⟩ := exists_div hR D _ _ hl hN p
  obtain ⟨q', hq', hq'y, hq'g⟩ := qkExt_nsmul D.toPre D.tau_bimult σ _ hpp' hqy hqg
  have e₁ := lab_level D A lab hO _ _ _ hk hl hN p q hqy ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hqg.symm)
  have e₂ := lab_level D A lab hO _ _ _ hk hl hN p' q' hq'y ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hq'g.symm)
  rw [e₂, pow_left_of_comp σ _ _ (H _ hi σ q q' hq'), ← e₁]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F), (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult).IsMonomialTau ![T.ϖ] ![T.β] ∧ (∀ a, 0 ≤ T.β a a) ∧ (∀ a, a ≠ 0 → 0 < T.β a a) ∧ (2 ≤ n → IsUnit ζ → Module.finrank ℤ T.D.toPre.X ≤ g) := by
  first | exact @GlobalTheory.Poinc.TraitTau.main | exact GlobalTheory.Poinc.TraitTau.main | (intros; apply GlobalTheory.Poinc.TraitTau.main <;> assumption)
end
