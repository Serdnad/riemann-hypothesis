module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

theorem prod_support_eq {U : Type} [CommGroup U] {r : ℕ} (g : Vec r → ℤ → U) (d : Vec r →₀ ℤ) :
    ∏ v : d.support, g v.1 (d v.1) = d.prod g :=
  Finset.prod_coe_sort d.support (fun v => g v (d v))

theorem triv_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c c' : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T c' →
    GlobalTheory.TensBal.Triv T (c + c') := by
  intro R _ _ D D' r W T c c' ⟨Ξ, hΞ, h1, h2⟩ ⟨Ξ', hΞ', h1', h2'⟩
  have hform : FormEq (Sum.elim (fun v : c.support => (vecHom T v.1).left) (fun v : c'.support => (vecHom T v.1).left))
      (Sum.elim (fun v : c.support => c v.1) (fun v : c'.support => c' v.1))
      (fun v : (c + c').support => (vecHom T v.1).left) (fun v => (c + c') v.1) := by
    intro U _ h
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [prod_support_eq (fun v n => h (vecHom T v).left ^ n) c,
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) c',
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) (c + c'),
      Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  obtain ⟨Ξ'', hΞ'', hv⟩ := exists_gen D.P.isLB hform _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ hΞ hΞ')
  refine ⟨Ξ'', hΞ'', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_mul hJ, h1 z J hJ, h1' z J hJ, _root_.mul_one]
  · rw [hv _ _ z J hJ, val_mul hJ, h2 z J hJ y y', h2' z J hJ y y']
    exact (Finsupp.prod_add_index' (f := c) (g := c')
      (h := fun v n => val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-n))
      (fun _ => by simp only [neg_zero, zpow_zero]) (fun _ _ _ => by simp only [neg_add, zpow_add])).symm

end GlobalTheory.TensBal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBalLat

open GlobalTheory.TensBal

section Calc

variable {M : Type} [CommGroup M] {α : Type}

def logHom (f : α → M) : (α →₀ ℤ) →+ Additive M :=
  Finsupp.liftAddHom fun v => zmultiplesHom (Additive M) (Additive.ofMul (f v)⁻¹)

theorem logHom_single (f : α → M) (v : α) : logHom f (Finsupp.single v 1) = Additive.ofMul (f v)⁻¹ := by
  simp [logHom]

theorem prod_eq_logHom (f : α → M) (c : α →₀ ℤ) :
    ∏ v ∈ c.support, f v ^ (-(c v)) = Additive.toMul (logHom f c) := by
  simp [logHom, Finsupp.liftAddHom_apply, Finsupp.sum, toMul_sum, toMul_zsmul, inv_zpow']

end Calc

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecLat_add (T : Tens D D' W) (u v : Vec r) (y y' : D'.X) :
    vecLat T (u + v) y y' = vecLat T u y y' + vecLat T v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel

theorem vecLat_zero (T : Tens D D' W) (y y' : D'.X) : vecLat T 0 y y' = 0 := by
  simp [vecLat]

theorem vecLat_rosVec (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (y y' : D'.X) (a : Fin 6) (i : Fin r) :
    vecLat T (rosVec A A' a i) y y' = T.xe (rosLat T A A' y y' a) i := by
  fin_cases a <;>
    simp [vecLat, rosVec, rosLat, axv, azv, xv, zv, GlobalTheory.TensAct.xe_latAct, map_add (f := _), Pi.single_apply,
      Finset.sum_add_distrib, add_smul, ite_smul]

theorem logHom_lam (T : Tens D D' W) (hB : D.TauBimult) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (y y' : D'.X) (u v : Vec r) :
    logHom (fun w => val (D.psi (vecLat T w y y')) (𝟙 _) z J) (lam u v) =
      Additive.ofMul (val (D.tau (vecLat T u y y') (vecLat T v y y')) (𝟙 _) z J)⁻¹ := by
  have hk : val (D.psi 0) (𝟙 _) z J = (val D.rigK (𝟙 _) z J)⁻¹ := by
    have e := (GlobalTheory.TauBalBox.tau_val D hJ 0 0 (𝟙 _)).symm.trans (GlobalTheory.TauBalElem.tau_zero_left hB hJ 0)
    rw [add_zero, mul_inv_cancel, _root_.one_mul] at e
    exact inv_mul_eq_one.mp e
  have h0 : vecLat T (0 : Vec r) y y' = 0 := vecLat_zero T y y'
  simp only [lam, map_add (f := _), map_sub, logHom_single, vecLat_add]
  rw [h0, vecLat_add]
  rw [GlobalTheory.TauBalBox.tau_val D hJ, hk]
  simp only [ofMul_mul, ofMul_inv, inv_inv]
  abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), D.TauBimult → ∀ (A A' : Matrix (Fin r) (Fin r) ℤ) (z : (TK R).left)
    (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ y y' : D'.X,
    ∏ v ∈ (GlobalTheory.TensBal.sig W A A').support,
        val (D.psi (GlobalTheory.TensBal.vecLat T v y y')) (𝟙 _) z J ^ (-(GlobalTheory.TensBal.sig W A A' v)) =
      ∏ a, GlobalTheory.TensBal.qv T z J (GlobalTheory.TensBal.rosLat T A A' y y' a) ^ (-(rosatiε a)) := by
  intro R _ _ D D' r W T hB A A' z J hJ y y'
  rw [prod_eq_logHom (fun w => val (D.psi (vecLat T w y y')) (𝟙 _) z J)]
  apply Additive.ofMul.injective
  rw [ofMul_toMul]

  simp only [sig, map_sum, map_zsmul, logHom_lam T hB hJ, vecLat_rosVec, qv, ofMul_prod, ofMul_zpow,
  Finset.smul_sum, ofMul_inv, smul_neg, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul, neg_mul, vecLat_rosVec, vecLat_rosVec]

end GlobalTheory.TensBalLat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBal

section Alg

variable {r : ℕ} {U : Type} [CommGroup U]

theorem prod_theta (a b c : Vec r) (F : Vec r → U) :
    ∏ v ∈ (theta a b c).support, F v ^ theta a b c v =
      F (a + b + c) * (F (a + b))⁻¹ * (F (a + c))⁻¹ * (F (b + c))⁻¹ * F a * F b * F c * (F 0)⁻¹ := by
  have h0 : ∀ v, F v ^ (0 : ℤ) = 1 := fun v => zpow_zero _
  have hadd : ∀ v (m n : ℤ), F v ^ (m + n) = F v ^ m * F v ^ n := fun v m n => zpow_add _ _ _
  change (theta a b c).prod (fun v n => F v ^ n) = _
  simp only [theta, sub_eq_add_neg, ← Finsupp.single_neg, Finsupp.prod_add_index' h0 hadd]
  simp only [Finsupp.prod_single_index (h := fun v (n : ℤ) => F v ^ n) (h0 _), zpow_one, zpow_neg]

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecHom_add (T : Tens D D' W) (u v : Vec r) : vecHom T (u + v) = vecHom T u * vecHom T v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (T : Tens D D' W) : vecHom T 0 = 1 := by
  simp only [vecHom, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]

theorem vecLat_add (T : Tens D D' W) (u v : Vec r) (y y' : D'.X) :
    vecLat T (u + v) y y' = vecLat T u y y' + vecLat T v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem vecLat_zero (T : Tens D D' W) (y y' : D'.X) : vecLat T 0 y y' = 0 := by
  simp only [vecLat, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

theorem comp_vecHom (T : Tens D D' W) {Z : Over (Spec (CommRingCat.of R))} (p q : Z ⟶ D'.P.A) (v : Vec r) :
    lift p q ≫ vecHom T v = (∏ k, (p ≫ T.pr k) ^ v (Sum.inl k)) * ∏ k, (q ≫ T.pr k) ^ v (Sum.inr k) := by
  have e := (preHom (G := D.P.A) (lift p q)).map_mul (∏ k, (fst D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inl k))
    (∏ k, (snd D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inr k))
  simp only [map_prod, map_zpow] at e
  rw [vecHom]
  simpa only [preHom, MonoidHom.mk'_apply, lift_fst_assoc, lift_snd_assoc] using e

theorem zero_vecHom (T : Tens D D' W) (v : Vec r) : lift η[D'.P.A] η[D'.P.A] ≫ vecHom T v = 1 := by
  have h : ∀ k, η[D'.P.A] ≫ T.pr k = 1 := fun k => by
    haveI := T.pr_hom k
    rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  simp only [comp_vecHom, h, one_zpow, Finset.prod_const_one, _root_.mul_one]

def cPHom (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) : Multiplicative D.X →* (T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => DVR.cP D T x.toAdd) fun a b => DVR.cPoint_add D T a.toAdd b.toAdd

theorem pt_vecHom (T : Tens D D' W) (y y' : D'.X) (v : Vec r) :
    lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y') ≫ vecHom T v = DVR.cP D (TK R) (vecLat T v y y') := by
  have hp : ∀ x k, DVR.cP D' (TK R) x ≫ T.pr k = cPHom D (TK R) (Multiplicative.ofAdd (T.xe x k)) := fun x k => by
    simp only [DVR.cP, Category.assoc, T.c_pr]; rfl
  rw [comp_vecHom, show DVR.cP D (TK R) (vecLat T v y y') = cPHom D (TK R) (Multiplicative.ofAdd (vecLat T v y y')) from rfl]
  simp only [hp, vecLat, ofAdd_add, ofAdd_sum, ofAdd_zsmul, map_mul, map_prod, map_zpow]

theorem cubV_psi (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (p q s : D.X) :
    cubV D.cub (T := TK R) z J (DVR.cP D _ p) (DVR.cP D _ q) (DVR.cP D _ s) =
      (val (D.psi (p + q + s)) (𝟙 _) z J)⁻¹ * val (D.psi (p + q)) (𝟙 _) z J * val (D.psi (p + s)) (𝟙 _) z J *
        val (D.psi (q + s)) (𝟙 _) z J * (val (D.psi p) (𝟙 _) z J)⁻¹ * (val (D.psi q) (𝟙 _) z J)⁻¹ *
        (val (D.psi s) (𝟙 _) z J)⁻¹ * val (D.psi 0) (𝟙 _) z J := by
  have t := DVR.tauK_mul hJ hB p q s
  have t0 := GlobalTheory.TauBalElem.tau_zero_left hB hJ 0
  rw [GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ] at t
  rw [GlobalTheory.TauBalBox.tau_val D hJ, add_zero] at t0
  apply Additive.ofMul.injective
  have t' := congrArg Additive.ofMul t
  have t0' := congrArg Additive.ofMul t0
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at t' t0' ⊢
  linear_combination (norm := abel) t' + t0'

theorem triv_theta : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), D.TauBimult → ∀ a b c : GlobalTheory.TensBal.Vec r, GlobalTheory.TensBal.Triv T (GlobalTheory.TensBal.theta a b c) := by
  intro R _ _ D D' r W T hB a b c
  have hF : FormEq (fun I => (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left ≫ thφ D.P.A (x3 D.P.A) I) thε
      (fun v : (theta a b c).support => (vecHom T v.1).left) (fun v => theta a b c v.1) := fun U _ h => by
    refine (prod_cub (vecHom T a) (vecHom T b) (vecHom T c) h).trans ?_
    rw [Finset.prod_coe_sort (theta a b c).support (fun v => h (vecHom T v).left ^ theta a b c v), prod_theta,
      vecHom_add, vecHom_add, vecHom_add, vecHom_add, vecHom_zero]
  obtain ⟨Ξ, hΞ, hv⟩ := exists_gen D.P.isLB hF
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left)
    (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)
  refine ⟨Ξ, hΞ, fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift η[D'.P.A] η[D'.P.A]) hJ _ _ _).trans ?_)
    rw [zero_vecHom, zero_vecHom, zero_vecHom]
    exact (isCub_cubV D.cub hJ).face _ _
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y')) hJ _ _ _).trans ?_)
    rw [pt_vecHom, pt_vecHom, pt_vecHom, cubV_psi hB hJ]
    simp only [zpow_neg, ← inv_zpow]
    rw [prod_theta (F := fun v => (val (D.psi (vecLat T v y y')) (𝟙 _) z J)⁻¹)]
    rw [vecLat_add T (a + b) c, vecLat_add T a b, vecLat_add T a c, vecLat_add T b c, vecLat_zero]
    simp only [inv_inv]

end GlobalTheory.TensBal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

variable {R : Type} [CommRing R] [IsDomain R]

theorem famMapTw_trPt (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {b b' : TF (R := R) (Kb R) ⟶ D.P.A}
    (hb : twF ρ ≫ b = b') : famMapTw D ρ ≫ DegPre.trPt D (Kb R) b = DegPre.trPt D (Kb R) b' ≫ famMapTw D ρ := by
  subst hb
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trPt]
  · simp [DegPre.trPt, padd, comp_lift_assoc]

theorem zF_famMapTw (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) :
    DegPre.zF D (Kb R) ≫ famMapTw D ρ = twF ρ ≫ DegPre.zF D (Kb R) := by
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem famMapTw_famφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) (β : D.X) (i : Fin 4) :
    (famMapTw D ρ).left ≫ DegPre.famφ D (Kb R) β i = DegPre.famφ D (Kb R) β i :=
  (famφ_famMap D (Kb R) (TwF ρ) β i).symm

theorem famMapTw_phiφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {y y₀ : D.X} (α : D.X)
    {b b₀ : TF (R := R) (Kb R) ⟶ D.P.A} (hy : y₀ = y) (hb : twF ρ ≫ b₀ = b) :
    (fun k => (famMapTw D ρ).left ≫ DegPre.phiφ D (Kb R) y₀ α b₀ k) = DegPre.phiφ D (Kb R) y α b := by
  subst hy
  funext k
  rcases k with i | i
  · exact famMapTw_famφ D ρ _ i
  · show (famMapTw D ρ).left ≫ (DegPre.trPt D (Kb R) b₀).left ≫ DegPre.famφ D (Kb R) α i =
      (DegPre.trPt D (Kb R) b).left ≫ DegPre.famφ D (Kb R) α i
    rw [← Category.assoc, ← Over.comp_left, famMapTw_trPt D ρ hb, Over.comp_left, Category.assoc,
      famMapTw_famφ]

theorem twF_left (ρ : Kb R →ₐ[FractionRing R] Kb R) : (twF ρ).left = spMap ρ.toRingHom := rfl

end GlobalTheory.Mum.Conj.PhiTw

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

theorem phiRel_famTw : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) (s s' : Fam D (Kb R) N),
    PhiRel D (Kb R) N p w s s' → PhiRel D (Kb R) N p₀ (frTw D τ h w) (famTw D N τ s) (famTw D N τ s') := by
  intro R _ _ D N τ p p₀ h w s s' H α u hu hu0
  have hL := D.P.isLB
  let e : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
  let σ : Kb R →ₐ[FractionRing R] Kb R := (e.symm : Kb R →ₐ[FractionRing R] Kb R)
  have hστ : ∀ x, σ (τ x) = x := fun x => e.symm_apply_apply x
  have hτσ : ∀ x, τ (σ x) = x := fun x => e.apply_symm_apply x
  have hb₀ : twF τ ≫ p.g.b = p₀.g.b := Over.OverMorphism.ext (by
    rw [Over.comp_left, twF_left]; exact h.2.1.symm)
  have hb : twF σ ≫ p₀.g.b = p.g.b := by
    rw [← hb₀, ← Category.assoc, twF_comp_eq_id hστ, Category.id_comp]
  have hφ := famMapTw_phiφ D σ α h.1 hb
  let u' := genCast hφ (LB.pullGen D.P.L _ _ u (famMapTw D σ).left)
  have hu' : u'.IsGen := genCast_isGen _ (DVR.pullGen_isGen _ _ _ u hu _)
  have hid : (twF σ).left ≫ spMap τ.toRingHom = 𝟙 _ := by
    rw [← twF_left, ← Over.comp_left, twF_comp_eq_id hστ]; rfl
  have hz : (DegPre.zF D (Kb R)).left ≫ (famMapTw D σ).left = (twF σ).left ≫ (DegPre.zF D (Kb R)).left := by
    rw [← Over.comp_left, zF_famMapTw, Over.comp_left]
  have hu'0 : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u' (DegPre.zF D (Kb R)).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) := corr_of_val hL fun y J hJ => by
    rw [val_pull hJ, val_genCast, val_pull hJ, Category.id_comp, hz, ← val_pull hJ, val_corr hJ hu0,
      val_mul hJ, val_mul hJ, val_corr hJ (h.2.2 α), val_pull hJ, frTw, val_genCast, val_pull hJ, hid]
  have H1 := (secRel_iff hL _ _ _ _ _ _ _ _ _ u').1 (H α u' hu' hu'0)
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e1 := H1 _ (famMapTw D τ).left y J hJ
  have hTT : (famMapTw D τ).left ≫ (famMapTw D σ).left = 𝟙 _ := by
    rw [← Over.comp_left, famMapTw_comp_eq_id D hτσ]; rfl
  rw [val_genCast, val_pull hJ, hTT] at e1
  rw [← h.1] at e1
  have hc : (famMapTw D τ).left ≫ (DegPre.trPt D (Kb R) p.g.b).left =
      (DegPre.trPt D (Kb R) p₀.g.b).left ≫ (famMapTw D τ).left := by
    rw [← Over.comp_left, famMapTw_trPt D τ hb₀, Over.comp_left]
  rw [sval_famTw _ _ _ _ _ _ hJ, sval_famTw _ _ _ _ _ _ hJ]
  simp only [Category.id_comp]
  rw [e1, hc]

end GlobalTheory.Mum.Conj.PhiTw
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SndAdj

open GlobalTheory.CechPic

theorem psum_comp_hom {S : Scheme.{0}} {T H H' : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    (f : H ⟶ H') [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ H)) (I : Finset (Fin n)) :
    psum H x I ≫ f = psum H' (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem sum_cube_zero {S : Scheme.{0}} {T H : Over S} [GrpObj H] [IsCommMonObj H] {M : Type*} [AddCommGroup M]
    (F : (T ⟶ H) → M) (y : Fin 2 → (T ⟶ H)) (hy : y 0 = 1) :
    ∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) • F (psum H y I.down) = 0 := by
  refine (Fintype.sum_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => ((-1 : ℤ) ^ (2 - I.card)) • F (psum H y I))
    (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide]
  simp only [ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.psum_eq_prod]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [hy]

theorem gAdj_snd_of_isProdUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have cL : cls _ hL = CechPic.pull (fst G₁ G₂).left (cls _ hL₁) + CechPic.pull (snd G₁ G₂).left (cls _ hL₂) :=
    (cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj cubeLB
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL₂ _ _)).1 ?_
  rw [cls_linComb hL, cls_linComb hL₂, cL]
  simp only [map_add (f := _), ← CechPic.pull_comp, smul_add, Finset.sum_add_distrib]
  have h₁ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (fst G₁ G₂).left = (psum G₁ ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  have h₂ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (snd G₁ G₂).left = (psum G₂ ![fst G₂ (G₁ ⊗ G₂), snd G₂ (G₁ ⊗ G₂) ≫ snd G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  simp only [h₁, h₂]
  exact add_eq_right.2 (sum_cube_zero
    (fun u : G₂ ⊗ G₁ ⊗ G₂ ⟶ G₁ => CechPic.pull u.left (cls _ hL₁)) ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] rfl)

end GlobalTheory.MumProd.SndAdj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem c_inc_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.P.A ⟶ D.P.A) (j₁ : D₁.X →+ D.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → ∀ y, D.c (j₁ y) = D₁.c y ≫ i₁ := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ y
  haveI := hS.lim
  apply (cancel_mono (lift p₁ p₂)).1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
    rw [hS.c_pr₁, hq₁, e₁, Category.comp_id]
  · simp only [Category.assoc, lift_snd]
    rw [hS.c_pr₂, hq₂, e₂, degPre_c_zero, Hom.one_def, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _

end GlobalTheory.MumProd
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

theorem _root_.GlobalTheory.T.exists_product_principallyPolarised_abelianScheme : ∀ (S : Scheme.{0}) (P₁ P₂ : PolAV S), ∃ (P : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A), IsSumPolAV P P₁ P₂ a₁ a₂ ∧ P.L = extLB P₁.L P₂.L a₁.left a₂.left := by
  first | exact @GlobalTheory.MumProd.SumPol.exists_sum_polAV | exact GlobalTheory.MumProd.SumPol.exists_sum_polAV | (intros; apply GlobalTheory.MumProd.SumPol.exists_sum_polAV <;> assumption)
end
