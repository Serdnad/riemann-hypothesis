module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle072
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
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
import Mathlib.RingTheory.PicardGroup
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TensAct

open GlobalTheory.Mum

section Hom

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]

end Hom

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def matAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) : D'.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D'.P.A fun i ↦ ∏ j, T.pr j ^ A i j)

theorem matAct_pr (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    matAct T A ≫ T.pr i = ∏ j, T.pr j ^ A i j :=
  T.lim.fac (Fan.mk D'.P.A fun i ↦ ∏ j, T.pr j ^ A i j) ⟨i⟩

theorem hom_ext (T : Tens D D' W) {X : Over (Spec (CommRingCat.of R))} {a b : X ⟶ D'.P.A}
    (h : ∀ i, a ≫ T.pr i = b ≫ T.pr i) : a = b :=
  T.lim.hom_ext fun i ↦ h i.as

def latAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) : D'.X :=
  T.xe.symm fun i ↦ ∑ j, A i j • T.xe y j

theorem xe_latAct (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) (i : Fin r) :
    T.xe (latAct T A y) i = ∑ j, A i j • T.xe y j := by
  simp [latAct]

section Ring

theorem zpow_finsetSum {M : Type} [CommGroup M] (a : M) {K : Type} (s : Finset K) (f : K → ℤ) :
    a ^ (∑ k ∈ s, f k) = ∏ k ∈ s, a ^ f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem matAct_hom (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) : IsMonHom (matAct T A) := by
  have hp := T.pr_hom
  refine GlobalTheory.MatrixAction.isMonHom_of_points _ (fun X ↦ hom_ext T fun i ↦ ?_) (fun X x y ↦ hom_ext T fun i ↦ ?_)
  · rw [Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, MonObj.one_comp (T.pr i)]
    refine Finset.prod_eq_one fun l _ ↦ ?_
    rw [GrpObj.comp_zpow, MonObj.one_comp, one_zpow]
  · rw [MonObj.mul_comp _ _ (T.pr i), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd, GlobalTheory.MatrixAction.comp_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    rw [GrpObj.comp_zpow, GrpObj.comp_zpow, GrpObj.comp_zpow, MonObj.mul_comp, mul_zpow]

theorem matAct_one (T : Tens D D' W) : matAct T 1 = 𝟙 _ := by
  refine hom_ext T fun i ↦ ?_
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · rw [Matrix.one_apply_eq, zpow_one]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl.symm, zpow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem matAct_mul (T : Tens D D' W) (A B : Matrix (Fin r) (Fin r) ℤ) :
    matAct T (A * B) = matAct T B ≫ matAct T A := by
  refine hom_ext T fun i ↦ ?_
  rw [Category.assoc, matAct_pr, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd]
  have e1 : ∀ k, matAct T B ≫ T.pr k ^ A i k = ∏ l, T.pr l ^ (A i k * B k l) := fun k ↦ by
    rw [GrpObj.comp_zpow, matAct_pr, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun l _ ↦ ?_
    rw [← zpow_mul, mul_comm]
  rw [Finset.prod_congr rfl fun k _ ↦ e1 k, Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [Matrix.mul_apply, zpow_finsetSum]

theorem matAct_add (T : Tens D D' W) (A B : Matrix (Fin r) (Fin r) ℤ) :
    matAct T (A + B) = matAct T A * matAct T B := by
  refine hom_ext T fun i ↦ ?_
  have := T.pr_hom i
  rw [MonObj.mul_comp, matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ ↦ ?_
  rw [Matrix.add_apply, zpow_add]

def latEnd (T : Tens D D' W) : Matrix (Fin r) (Fin r) ℤ →+* Module.End ℤ D'.X where
  toFun A :=
    { toFun := latAct T A
      map_add' := fun y z ↦ T.xe.injective (funext fun i ↦ by
        simp only [xe_latAct, map_add (f := _), Pi.add_apply, smul_add, Finset.sum_add_distrib])
      map_smul' := fun n y ↦ T.xe.injective (funext fun i ↦ by
        simp only [xe_latAct, map_zsmul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _) }
  map_one' := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, Module.End.one_apply]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl.symm, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h)
  map_mul' A B := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, Module.End.mul_apply, Matrix.mul_apply,
      Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm)
  map_zero' := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp [xe_latAct])
  map_add' A B := LinearMap.ext fun y ↦ T.xe.injective (funext fun i ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, xe_latAct, LinearMap.add_apply, map_add (f := _), Pi.add_apply,
      Matrix.add_apply, add_smul, Finset.sum_add_distrib])

abbrev tensModule (T : Tens D D' W) {O : Type} [Ring O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : Module O D'.X :=
  Module.compHom D'.X ((latEnd T).comp ρ)

def ringAct (T : Tens D D' W) {O : Type} [Ring O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : RingAct D'.P.A O where
  act a := matAct T (ρ a)
  hom a := matAct_hom T (ρ a)
  map_one := by rw [map_one, matAct_one]
  map_mul a b := by rw [map_mul, matAct_mul]
  map_add a b := by rw [map_add (f := _), matAct_add]; rfl

def cHom (D : DegPre R) : D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :=
  AddMonoidHom.mk' (fun x ↦ Additive.ofMul (D.c x)) fun a b ↦ by rw [D.c_add]; rfl

theorem c_lin (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) :
    D'.c (latAct T A y) = D'.c y ≫ matAct T A := by
  refine hom_ext T fun i ↦ ?_
  rw [T.c_pr, Category.assoc, matAct_pr, GlobalTheory.MatrixAction.comp_finsetProd, xe_latAct]
  have e := map_sum (cHom D) (fun j ↦ A i j • T.xe y j) Finset.univ
  simp only [map_zsmul] at e
  apply Additive.ofMul.injective
  refine e.trans ?_
  rw [ofMul_prod]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [GrpObj.comp_zpow, T.c_pr, ofMul_zpow]
  rfl

end Ring

end GlobalTheory.TensAct
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DivDeep

open GlobalTheory.ThetaCompare

theorem torsFrame_two_levels {S : Scheme.{0}} (P : PolAV S) {T : Over S} {m M : ℕ}
    {rig rig' : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ τ'} (H : IsTorsFrame P rig m x τ)
    (H' : IsTorsFrame P rig' M x τ') {y : T.left} {J} (hJ : Good P.L y J) :
    (val τ (𝟙 _) y J / val τ' (𝟙 _) y J) ^ (m ^ 2 * M ^ 2) =
      (val rig T.hom y J / val rig' T.hom y J) ^ (m ^ 2 * M ^ 2) := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨β, hβ⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P M T
  have a := torsFrame_pow hG P hα H hJ
  have b := torsFrame_pow hG P hβ H' hJ
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rβ := Reg.two (y := y) (J := J) β hβ (snd T P.A) (snd T P.A ^ M) rfl rfl
  have c := (((rα.pow hJ (M ^ 2)).mul hJ (rβ.pull hJ (snd T P.A ^ m))).mul hJ
    ((rβ.pow hJ (m ^ 2)).mul hJ (rα.pull hJ (snd T P.A ^ M))).inv).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul, mul_comm M m]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) x 1
  simp only [SymLiftOdd.comp_pow', pt_snd, H.1, H'.1, one_pow] at c
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div] at a b c ⊢
  linear_combination (norm := module) (M ^ 2) • a - (m ^ 2) • b + c

theorem exists_cst {K : Type} [Field K] (z : Sp K) : ∃ c : K →+* (Sp K).presheaf.stalk z, Function.Injective c ∧
    ∀ a, gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = c a :=
  ⟨((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom, RingHom.injective _,
    fun _ => gs_eq (𝟙 _) z ⊤ trivial _⟩

theorem same_ratio {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ε} {ρ' : S'.Real} {ε'} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
    (h : Same ρ ε ρ' ε' lab φ) (a b : S.Gam) :
    ∃ k, 0 < k ∧ (S'.th (lab a) * φ (S.th b)) ^ k = (S'.th (lab b) * φ (S.th a)) ^ k := by
  obtain ⟨P₀, f, f', -, gp, gp', lb, lb', -, hw⟩ := h
  choose w hw hw' using hw
  have hs : ∀ x, w x ≫ P₀.A.hom = 𝟙 _ := fun x => by
    have e : (w x ≫ P₀.A.hom) ≫ spMap S'.R.val.toRingHom = 𝟙 _ ≫ spMap S'.R.val.toRingHom := by
      rw [Category.assoc, ← gp'.1.w, ← Category.assoc, hw', Category.assoc, Over.w, Category.id_comp]
      exact Category.comp_id _
    haveI : IsFractionRing S'.R Ω' := IsFractionRing.of_field _ _ fun x => by
      obtain ⟨a, ha, b, hb, e⟩ := S'.frac x
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
    haveI : IsPreimmersion (spMap S'.R.val.toRingHom) :=
      IsPreimmersion.of_isLocalization (R := S'.R) (S := Ω') (nonZeroDivisors S'.R)
    exact (cancel_mono _).1 e
  let x : S.Gam → (baseOver (Sp Ω') ⟶ P₀.A) := fun a => Over.homMk (w a) (hs a)
  obtain ⟨rig, τ, -, hτ, ht⟩ := FrameMove.exists_move (T := baseOver (Sp S.R)) (T' := baseOver (Sp Ω'))
    (h := spMap (φ.comp S.R.val.toRingHom)) gp lb ((Category.comp_id _).trans (Category.id_comp _).symm) ρ.rig_gen
    (x := ρ.pt) (x' := x) hw ρ.fr_tors
  obtain ⟨rig', τ', -, hτ', ht'⟩ := FrameMove.exists_move (T := baseOver (Sp S'.R)) (T' := baseOver (Sp Ω'))
    (h := spMap S'.R.val.toRingHom) gp' lb' ((Category.comp_id _).trans (Category.id_comp _).symm) ρ'.rig_gen
    (x := fun a => ρ'.pt (lab a)) (x' := x) hw' (fun a => ρ'.fr_tors (lab a))
  obtain ⟨t, ht⟩ := ht 1 ρ.th₁
  obtain ⟨t', ht'⟩ := ht' 1 ρ'.th₁
  let z : Sp Ω' := IsLocalRing.closedPoint Ω'
  obtain ⟨V, hV, hθ⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny P₀ z
  obtain ⟨θ, hθ⟩ := hθ Ω' (𝟙 _) (by rintro _ ⟨v, rfl⟩; rw [Subsingleton.elim v z]; exact hV)
  obtain ⟨r, hr⟩ := hθ t
  obtain ⟨r', hr'⟩ := hθ t'
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' (Z := (baseOver (Sp Ω')).left) P₀.isLB z
  obtain ⟨c, hc, hcv⟩ : ∃ c : Ω' →+* (baseOver (Sp Ω')).left.presheaf.stalk z, Function.Injective c ∧
      ∀ a, gs (𝟙 (Sp Ω')) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom a) = c a := exists_cst z
  have pf : ∀ {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
      (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
      powFrame A L x τ 1 = τ := fun x τ => congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))
  have v : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (φ (S.th a)) * (val (τ a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr (x a) hJ).symm.trans (ht a _ (by rw [pf]; exact ρ.th_val a) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have v' : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r' * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (S'.th (lab a)) * (val (τ' a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr' (x a) hJ).symm.trans (ht' a _ (by rw [pf]; exact ρ'.th_val (lab a)) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have q := (torsFrame_two_levels P₀ (hτ a) (hτ' a) hJ).trans (torsFrame_two_levels P₀ (hτ b) (hτ' b) hJ).symm
  have p₁ : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have p₂ : 0 < S'.r * S'.N := Nat.mul_pos S'.r_pos (by have := S'.N_ge; omega)
  refine ⟨(S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2, by positivity, hc ?_⟩
  generalize (S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2 = k at q
  have va := v a
  have vb := v b
  have va' := v' a
  have vb' := v' b
  generalize val (τ a) (𝟙 _) z J = ua at *
  generalize val (τ b) (𝟙 _) z J = ub at *
  generalize val (τ' a) (𝟙 _) z J = ua' at *
  generalize val (τ' b) (𝟙 _) z J = ub' at *
  have e : c (S'.th (lab a) * φ (S.th b)) * (ua' * ub).val = c (S'.th (lab b) * φ (S.th a)) * (ub' * ua).val := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm, ← va', ← vb, _root_.mul_mul_mul_comm (c _), ← vb', ← va]
    ring
  have q' : (ua' * ub) ^ k = (ub' * ua) ^ k := by
    apply Additive.ofMul.injective
    replace q := congrArg Additive.ofMul q
    simp only [ofMul_mul, ofMul_pow, ofMul_div] at q ⊢
    linear_combination (norm := module) -q
  have e' := congrArg (· ^ k) e
  simp only [mul_pow, ← Units.val_pow_eq_pow_val, q'] at e'
  rw [map_pow, map_pow]
  exact (Units.mul_left_inj _).1 e'

end GlobalTheory.Poinc.DivDeep
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautEx

theorem toUnit_left {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

section Gen

variable {Y : Scheme.{0}} {M : LB Y}

def mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun j => res le_top u * t.s j⟩

theorem gm_mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) {y : Y} {i : M.ι} (h : y ∈ M.U i) :
    gm (𝟙 Y) y (M.U i) ((mulU u t).s i) = gm (𝟙 Y) y ⊤ u * gm (𝟙 Y) y (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res (𝟙 Y) y _ h _))

theorem isGen_mulU (u : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (mulU u t).IsGen := by
  intro i j
  refine unit_ext fun x hx => ?_
  have e := congrArg (gm (𝟙 Y) x _) (ht i j)
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx] at e
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx, gm_mulU u t hx.1, gm_mulU u t hx.2, e]
  exact mul_left_comm _ _ _

variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem val_mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι)
    (hJ : Good L z J) : val (mulU u t) r z J = gm r z ⊤ u * val t r z J :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ (hJ.mem φ r) _))

end Gen

section Base

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

abbrev fC : Sp (MvPowerSeries (Fin N) W) ⟶ Sp W := spMap MvPowerSeries.C

abbrev Bp : Over (Sp (MvPowerSeries (Fin N) W)) := (Over.pullback (fC (W := W) N)).obj T.B

theorem isAb_Bp : IsAbelianScheme (Bp T N) := GlobalTheory.isAbelianScheme_pullback_obj _ _ T.isAb

instance : IsCommMonObj (Bp T N) := (isAb_Bp T N).comm

theorem cart : IsGrpPullback (Bp T N) T.B (fC N) (pullback.fst T.B.hom (fC N)) := isGrpPullback_pullback T.B _

abbrev cm : CubeMap (Bp T N) T.B := cubeMapOf (cart T N)

theorem pullSt : ∃ (hL : (T.M.L.pull (cm T N).F).IsLB) (hr : ((cm T N).rigPull T.M.L T.M.rig).IsGen),
    (∃ c' : CubicalStr (Bp T N) ((cm T N).rigLB T.M hL hr), (cm T N).IsPullCubical c' T.cub) ∧
      (T.M.IsSymmetric → ((cm T N).rigLB T.M hL hr).IsSymmetric) :=
  proved_CubePullSt _ _ T.B (Bp T N) (cm T N) T.M T.cub

abbrev Mp : RigLB (Bp T N) := (cm T N).rigLB T.M (pullSt T N).fst (pullSt T N).snd.fst

abbrev cubP : CubicalStr (Bp T N) (Mp T N) := CubePf.cubical (cm T N) T.M T.cub _ _

end Base

section Pts

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

theorem lamPts_w {S : Scheme.{0}} {G Tt : Over S} [GrpObj G] (x y : Tt ⟶ G) (k : Fin 4) :
    lamPts x y k ≫ G.hom = Tt.hom := by
  fin_cases k <;> simp [lamPts]

theorem unit_hom (S : Scheme.{0}) : (𝟙_ (Over S)).hom = 𝟙 S := rfl

end Pts

section Periods

variable (W : Type) [CommRing W] [IsDomain W] (N : ℕ)

end Periods

section Charts

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)


end Charts

section Tau

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

theorem unitOn_mul {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v := map_mul _ _ _

theorem triple_lift_comp_projections {S : Scheme.{0}} {G Tt : Over S} (x y w : Tt ⟶ G) :
    lift x (lift y w) ≫ x3 G 0 = x ∧ lift x (lift y w) ≫ x3 G 1 = y ∧ lift x (lift y w) ≫ x3 G 2 = w := by
  simp [x3]

theorem alg_step {G : Type} [CommGroup G] {g₁ g₂ v c a b : G} (e : v * c = a * b) :
    g₁ * g₂ * v * c = g₁ * a * (g₂ * b) := by
  rw [mul_assoc (g₁ * g₂), e, _root_.mul_mul_mul_comm]

end Tau

section Main

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

end Main

end GlobalTheory.PolDeg.TautEx
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_common_baseChange_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (σ : R →+* K) (σ' : R' →+* K) (u : Sp K ⟶ Xo.XF cf), UOver Xo cf P σ u → UOver Xo cf P' σ' u → ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsGrpPullback P₀.A P.A (spMap σ) a ∧ IsGrpPullback P₀.A P'.A (spMap σ') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro E _ _ _ H Dw l Xo cf K R R' _ _ _ P P' σ σ' u h h'
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  obtain ⟨G', _, α', β', hα', hβ', hL'⟩ := h'
  obtain ⟨P₀, φ, hφ, hLφ⟩ := exists_pol_baseChange P (spMap σ)
  obtain ⟨e₀, _, he₀⟩ := grpPullback_iso hφ hα
  obtain ⟨e, _, he⟩ := grpPullback_iso hβ hβ'
  haveI : IsMonHom (e₀ ≪≫ e).hom := inferInstanceAs (IsMonHom (e₀.hom ≫ e.hom))
  have hU := Xo.univ.t.PP.isLB
  have X1 : LBIso (P.L.pull φ) (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp e₀.hom.left he₀.symm rfl hL
  have X2 : LBIso (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) (P'.L.pull ((e₀.hom.left ≫ e.hom.left) ≫ α')) :=
    GlobalTheory.GenSpread.lbIso_pull_comp (e₀.hom.left ≫ e.hom.left) (by rw [← he, Category.assoc]) rfl hL'.symm
  refine ⟨P₀, φ, (e₀.hom.left ≫ e.hom.left) ≫ α', hφ,
    ((isGrpPullback_of_iso (e₀ ≪≫ e)).comp hα').congr (Category.id_comp _) rfl, hLφ,
    LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB P'.isLB _) hLφ
      (LBIso.trans (pull_isLB P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) X1 X2)⟩

end GlobalTheory.UPoinc
end
end
