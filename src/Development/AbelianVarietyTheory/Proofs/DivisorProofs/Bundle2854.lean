module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull

namespace GlobalTheory.Poinc.Sep.BaseChangeLabels

theorem qkToAkU_pullback_common_field : ∀ {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], IsCN V → IsCN V' → ∀ (j : V →+* V') (hj : Function.Injective j), IsLocalHom j → ∀ {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg j D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V')))) (gA : A'.A.left ⟶ A.A.left) (U' : Unif (maximalIdeal V') D' A' ((Over.pullback (specOf j)).obj G)), IsPullUnif j hD (Iso.refl _) U U' → IsGrpPullback A'.A A.A (spMap (fracMap hj)) gA → gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf j)).obj G).hom (jK V') ≫ pullback.fst G.hom (specOf j) → ∀ (F' : Type) [Field F'] [Algebra (FractionRing V) F'] [Algebra (FractionRing V') F'], (∀ r : V, algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) r) = algebraMap (FractionRing V') F' (algebraMap V' (FractionRing V') (j r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p₁ : QkPt D.toPre F' k) (x₁ : TFK (R := V) F' ⟶ A.A), QkToAkU U.toUnifPre F' k p₁ x₁ → ∃ (p' : QkPt D'.toPre F' k) (x' : TFK (R := V') F' ⟶ A'.A), p'.y = hD.xe.symm p₁.y ∧ QkToAkU U'.toUnifPre F' k p' x' ∧ x'.left ≫ gA = x₁.left := by
  intro V V' _ _ _ _ _ _ hV hV' j hj _ D A G _ _ _ U D' hD A' gA U' hPU hgU hgA F' _ _ _ hF k hk p₁ x₁ hQ

  have hcomp : algebraMap (FractionRing V) F' = (algebraMap (FractionRing V') F').comp (fracMap hj) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors V)
    ext r
    simp only [RingHom.comp_apply, fracMap_algebraMap]
    exact hF r

  have P := GlobalTheory.UT.EndBaseChange.points GlobalTheory.firstFiveLaws.1.globalFns hD D.tau_bimult D'.tau_bimult F' hF
  obtain ⟨g', hg', -⟩ := P.1 p₁.g
  obtain ⟨h, hn, hi⟩ := p₁.eq
  obtain ⟨h', hh', -⟩ := P.1 h
  have hn' := (P.2.2.2 k p₁.g g' h h' hg' hh').1 hn
  have hi' : GtPtF.IsIota (hD.xe.symm p₁.y) h' := (P.2.2.1 h h' (hD.xe.symm p₁.y) hh').1 (by simpa using hi)
  let p' : QkPt D'.toPre F' k := ⟨hD.xe.symm p₁.y, g', ⟨h', hn', hi'⟩⟩

  have sq : x₁.left ≫ A.A.hom = (TFK (R := V') F').hom ≫ spMap (fracMap hj) := by
    rw [Over.w x₁]
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F')) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V') F')) ≫ Spec.map (CommRingCat.ofHom (fracMap hj))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let l := hgU.1.lift x₁.left (TFK (R := V') F').hom sq
  have hl₁ : l ≫ gA = x₁.left := hgU.1.lift_fst _ _ sq
  have hl₂ : l ≫ A'.A.hom = (TFK (R := V') F').hom := hgU.1.lift_snd _ _ sq
  let x' : TFK (R := V') F' ⟶ A'.A := Over.homMk l hl₂
  have hx' : x'.left ≫ gA = x₁.left := hl₁

  have hA : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have hA' : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf j)).obj G)).hom := by
    show IsMonHom (𝟙 _); infer_instance
  refine ⟨p', x', rfl, ?_, hx'⟩
  refine GlobalTheory.firstFiveLaws.2.2.2.2.qkBaseChange V V' (maximalIdeal V) (maximalIdeal V') hA hA' j D A G U
    ((Over.pullback (specOf j)).obj G) (Iso.refl _) mR A' D' hD U' hPU F' hF k hk p₁ x₁ p' x' rfl hg' ?_ hQ
  rw [Iso.refl_hom, Over.id_left, Category.id_comp, ← hx', Category.assoc, hgA]

end GlobalTheory.Poinc.Sep.BaseChangeLabels
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G']

def lamC (x y : T ⟶ G) : Pic G.left →+ Pic T.left where
  toFun c := lam c x y
  map_zero' := by simp only [lam, map_zero]; abel
  map_add' c d := by simp only [lam, map_add (f := _)]; abel

theorem lamC_apply (c : Pic G.left) (x y : T ⟶ G) : lamC x y c = lam c x y := rfl

theorem lam_pull_of (g : G' ⟶ G) (c : Pic G.left) (u v : T ⟶ G')
    (hm : (u * v) ≫ g = (u ≫ g) * (v ≫ g)) (h1 : (1 : T ⟶ G') ≫ g = 1) :
    lam (pull g.left c) u v = lam c (u ≫ g) (v ≫ g) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, hm, h1]

end Pairing

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
  {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right' (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm, lam_comm _ z]

def lamHom (z : T ⟶ G) : (T ⟶ G) →* Multiplicative (Pic T.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_zpow_left (x z : T ⟶ G) (k : ℤ) :
    lam (cls L hL) (x ^ k) z = k • lam (cls L hL) x z := by
  have h := map_zpow (lamHom hL hΘ z) x k
  exact congrArg Multiplicative.toAdd h

theorem lam_prod_left : ∀ (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G),
    lam (cls L hL) (List.ofFn fun v => x v ^ e v).prod z = ∑ v, e v • lam (cls L hL) (x v) z
  | 0, x, e, z => by simp [lam_one_left]
  | n + 1, x, e, z => by
    rw [List.ofFn_succ, List.prod_cons, lam_mul_left hL hΘ, lam_zpow_left hL hΘ,
      lam_prod_left n (fun v => x v.succ) (fun v => e v.succ) z, Fin.sum_univ_succ]

theorem lam_prod_right (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G) :
    lam (cls L hL) z (List.ofFn fun v => x v ^ e v).prod = ∑ v, e v • lam (cls L hL) z (x v) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ z]

theorem lam_lam (p q : G' ⟶ G) [IsMonHom p] [IsMonHom q] (u v : T ⟶ G') :
    lam (lam (cls L hL) p q) u v = lam (cls L hL) (u ≫ p) (v ≫ q) + lam (cls L hL) (u ≫ q) (v ≫ p) := by
  have e : lam (lam (cls L hL) p q) u v = lamC u v (lam (cls L hL) p q) := rfl
  rw [e, show lam (cls L hL) p q = pull (p * q).left (cls L hL) - pull p.left (cls L hL) - pull q.left (cls L hL)
      + pull (1 : G' ⟶ G).left (cls L hL) from rfl, map_add, map_sub, map_sub]
  simp only [lamC_apply]
  rw [lam_pull_of (p * q) _ u v (by rw [MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp, MonObj.comp_mul,
      MonObj.comp_mul, _root_.mul_mul_mul_comm]) (by rw [MonObj.comp_mul, MonObj.one_comp, MonObj.one_comp, _root_.mul_one]),
    lam_pull_of p _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of q _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of (1 : G' ⟶ G) _ u v (by rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, _root_.mul_one])
      (MonObj.comp_one _)]
  rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, lam_one_left,
    lam_mul_left hL hΘ, lam_mul_right' hL hΘ, lam_mul_right' hL hΘ]
  abel

end Bilinear

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

theorem alg_left {M : Type*} [AddCommGroup M] (S a : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a i v • B v j = ∑ v, ∑ j, (a.transpose * S) v j • B v j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  simp_rw [smul_comm (S _ _) (a _ _)]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem alg_right {M : Type*} [AddCommGroup M] (S a' : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a' j v • B i v = ∑ i, ∑ v, (S * a') i v • B i v := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_comm

def precomp {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') : (T' ⟶ G) →* (T ⟶ G) where
  toFun y := h ≫ y
  map_one' := MonObj.comp_one h
  map_mul' := MonObj.comp_mul h

theorem comp_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') :
    ∀ (n : ℕ) (x : Fin n → (T' ⟶ G)) (e : Fin n → ℤ),
      h ≫ (List.ofFn fun v => x v ^ e v).prod = (List.ofFn fun v => (h ≫ x v) ^ e v).prod
  | 0, x, e => by simp [MonObj.comp_one]
  | n + 1, x, e => by
    rw [List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_prod h n, List.ofFn_succ, List.prod_cons]
    congr 1
    exact map_zpow (precomp (G := G) h) (x 0) (e 0)

theorem lbIso_cubeLB_adjoint : ∀ (K : Type) [Field K] (A A' : PolAV (Sp K)) (W : Matrix (Fin 8) (Fin 8) ℤ) (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ (f f' : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → (∀ u, f' ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → LBIso (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L) (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L) := by
  intro K _ A A' W pr hpr hiso a a' hS f f' hf hf'
  have := A.isAb.comm
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨cs⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp K) A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta A.A A.L), t.IsGen := ⟨cs.t, cs.isGen⟩
  have hL := A.isLB
  have hL' := A'.isLB
  have hLam : (abelian₂ A.A A.L).IsLB := LB.isLB_linComb hL _ _
  have hLC := LB.isLB_linComb hLam (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have hcA : cls A'.L hL' = ∑ ab : Fin 8 × Fin 8, W ab.1 ab.2 • lam (cls A.L hL) (pr ab.1) (pr ab.2) := by
    rw [(cls_eq_iff hL' hLC).2 hiso, cls_linComb hLam]
    refine Finset.sum_congr rfl fun ab _ => ?_
    congr 1
    rw [show cls (abelian₂ A.A A.L) hLam = lam (cls A.L hL) (fst A.A A.A) (snd A.A A.A) from cls_cube_two hL _ _ _,
      pull_lam, lift_fst, lift_snd]
  have key : ∀ {T : Over (Sp K)} (u v : T ⟶ A'.A), lam (cls A'.L hL') u v =
      ∑ i, ∑ j, (W + W.transpose) i j • lam (cls A.L hL) (u ≫ pr i) (v ≫ pr j) := by
    intro T u v

    rw [← lamC_apply, hcA, map_sum]
    simp only [map_zsmul, lamC_apply, lam_lam hL hΘ, smul_add, Finset.sum_add_distrib, Matrix.add_apply,
      Matrix.transpose_apply, add_smul]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 1
    exact Finset.sum_comm
  have h₁ : (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L).IsLB := LB.isLB_linComb hL' _ _
  have h₂ : (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L).IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff h₁ h₂).1 ?_
  rw [cls_cube_two hL', cls_cube_two hL', key, key]
  simp only [Category.assoc, hf, hf', comp_prod, lam_prod_left hL hΘ, lam_prod_right hL hΘ]
  refine (alg_left (W + W.transpose) a
    (fun v j => lam (cls A.L hL) (fst A'.A A'.A ≫ pr v) (snd A'.A A'.A ≫ pr j))).trans ?_
  rw [← hS]
  exact (alg_right (W + W.transpose) a'
    (fun i v => lam (cls A.L hL) (fst A'.A A'.A ≫ pr i) (snd A'.A A'.A ≫ pr v))).symm

end GlobalTheory.E8AdjointPairing
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UpExt
open GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R]

def baseK (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F]
    [IsScalarTower (FractionRing R) E F] : TFK (R := R) F ⟶ TFK (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F
    rw [jFK, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

variable (A : PolAV (Sp (FractionRing R)))

def secBase (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (TFK (R := R) F ⊗ A.A).left ⟶ Spec (CommRingCat.of F) := (fst (TFK (R := R) F) A.A).left

abbrev SecF (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) : Type :=
  SecOver (secBase A F) (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (N : ℤ)))

variable (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F]
    [IsScalarTower (FractionRing R) E F]

def secMap : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) E ⊗ A.A := lift (fst _ _ ≫ baseK E F) (snd _ _)

theorem secMap_snd : secMap A E F ≫ snd _ _ = snd _ _ := lift_snd _ _

theorem secMap_fst : secMap A E F ≫ fst _ _ = fst _ _ ≫ baseK E F := lift_fst _ _

theorem secMap_base : (secMap A E F).left ≫ secBase A E =
    secBase A F ≫ Spec.map (CommRingCat.ofHom (algebraMap E F)) :=
  congrArg (fun q => q.left) (secMap_fst A E F)

def secPull (N : ℕ) : SecF A E N →ₛₗ[algebraMap E F] SecF A F N :=
  pullOver A.L _ (secMap_base A E F) (fun _ => (congrArg (fun q => q.left) (secMap_snd A E F)).symm)

theorem isPullback_secMap : IsPullback (secMap A E F).left (secBase A F) (secBase A E)
    (Spec.map (CommRingCat.ofHom (algebraMap E F))) := by
  have h₁ : IsPullback (snd (TFK (R := R) E) A.A).left (secBase A E)
      A.A.hom (TFK (R := R) E).hom := (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (snd (TFK (R := R) F) A.A).left (secBase A F)
      A.A.hom (TFK (R := R) F).hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (secMap_base A E F) h₁
  have e₁ : (secMap A E F).left ≫ (snd (TFK (R := R) E) A.A).left =
      (snd (TFK (R := R) F) A.A).left := congrArg (fun q => q.left) (secMap_snd A E F)
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫
      (TFK (R := R) E).hom = (TFK (R := R) F).hom := Over.w (baseK (R := R) E F)
  rw [e₁, e₂]
  exact h₂

instance noeth : TopologicalSpace.NoetherianSpace (TFK (R := R) E ⊗ A.A).left := by
  have := A.isAb.proper
  have : IsProper (secBase A E) := inferInstanceAs (IsProper (pullback.fst _ _))
  have : IsLocallyNoetherian (TFK (R := R) E ⊗ A.A).left := LocallyOfFiniteType.isLocallyNoetherian (secBase A E)
  have : CompactSpace (TFK (R := R) E ⊗ A.A).left := QuasiCompact.compactSpace_of_compactSpace (secBase A E)
  have : IsNoetherian (TFK (R := R) E ⊗ A.A).left := {}
  infer_instance

theorem isExtension_secPull (N : ℕ) : IsExtension (secPull A E F N) :=
  isExtension_pullOver (isPullback_secMap A E F) A.isLB _ _

end GlobalTheory.Mum.UpExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem qkPt_finite_reps : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), k ≠ 0 → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → ∃ Rep : Set (QkPt D F k), Rep.Finite ∧ ∀ p : QkPt D F k, ∃ p' ∈ Rep, ∃ (z : D.X) (t : GtPtF D F), t.b = 1 ∧ (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0 ∧ p.g = p'.g + GlobalTheory.TorusExt.iota hB F z + t) := by
  intro R _ _ D hB F _ _ k hk hfin
  letI := GlobalTheory.TorusExt.gtGroup D F
  classical
  by_cases hne : Nonempty (QkPt D F k)
  swap
  · exact ⟨∅, Set.finite_empty, fun p => (hne ⟨p⟩).elim⟩
  let K : AddSubgroup D.X := (nsmulAddMonoidHom (α := D.X) k).range
  haveI : K.FiniteIndex := ⟨by
    simp only [K, AddSubgroup.index_range_nsmul]; exact pow_ne_zero _ hk⟩
  haveI : Finite (D.X ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex
  let Q : QkPt D F k → D.X ⧸ K := fun p => (p.y : D.X ⧸ K)
  let bp : D.X ⧸ K → QkPt D F k := Function.invFun Q
  have hbp : ∀ p, Q (bp (Q p)) = Q p := fun p => Function.invFun_eq ⟨p, rfl⟩
  have hz : ∀ p, ∃ z : D.X, k • z = -(bp (Q p)).y + p.y := by
    intro p
    have h := QuotientAddGroup.eq.mp (hbp p)
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mp h
    exact ⟨z, by simpa using hz⟩
  let zOf : QkPt D F k → D.X := fun p => (hz p).choose
  have hzOf : ∀ p, k • zOf p = -(bp (Q p)).y + p.y := fun p => (hz p).choose_spec
  let δ : QkPt D F k → GtPtF D F := fun p =>
    p.g - (bp (Q p)).g - GlobalTheory.TorusExt.iota hB F (zOf p)
  have hδk : ∀ p, k • δ p = 0 := by
    intro p
    simp only [δ, smul_sub, GlobalTheory.TorusExt.qk_nsmul hB, ← map_nsmul, hzOf]
    rw [map_add (f := _), map_neg]; abel
  have hδb : ∀ p, (δ p).b ^ k = 1 := by
    intro p
    rw [← GlobalTheory.TorusExt.nsmul_b, hδk p, GlobalTheory.TorusExt.zero_b]
  let Φ : QkPt D F k → (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} :=
    fun p => (Q p, ⟨(δ p).b, hδb p⟩)
  let rep : (D.X ⧸ K) × {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → QkPt D F k :=
    Function.invFun Φ
  have hrep : ∀ p, Φ (rep (Φ p)) = Φ p := fun p => Function.invFun_eq ⟨p, rfl⟩
  refine ⟨Set.range (rep ∘ Φ), ?_, ?_⟩
  · rw [Set.range_comp]; exact (Set.toFinite _).image _
  intro p
  set p' := rep (Φ p) with hp'
  have h1 : Q p' = Q p := congrArg Prod.fst (hrep p)
  have h2 : (δ p').b = (δ p).b := congrArg (fun x => x.2.1) (hrep p)
  refine ⟨p', ⟨p, rfl⟩, zOf p - zOf p', δ p - δ p', ?_, ?_, ?_⟩
  · rw [sub_eq_add_neg, GlobalTheory.TorusExt.add_b, GlobalTheory.TorusExt.neg_b, h2, mul_inv_cancel]
  · rw [smul_sub, hδk, hδk, sub_zero]
  · have hb : bp (Q p') = bp (Q p) := by rw [h1]
    simp only [δ, hb, map_sub]
    abel

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompData

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ (∀ x, hD.xe x = xe x) ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ D'.P.A.left) (y : Y) (a : D.P.L.ι) (c : D'.P.L.ι), gw hD.w f y a c = gw w f y a c := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := hψ x y J J' hJ hJ'
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, fun _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

end GlobalTheory.PullDegCompData

namespace GlobalTheory.Mum

end GlobalTheory.Mum
end
end
