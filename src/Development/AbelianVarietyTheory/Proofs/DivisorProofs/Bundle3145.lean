module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle712
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentOpenInvariantSubscheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Mathlib.Tactic.Polynomial.Basic

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

noncomputable section

namespace GlobalTheory.Poinc.EighthPow

def matAct {X : Type} [AddCommGroup X] (M : Matrix (Fin 8) (Fin 8) ℤ) (t : Fin 8 → X) : Fin 8 → X :=
  fun v => ∑ u, M v u • t u

theorem matAct_mul {X : Type} [AddCommGroup X] (N M : Matrix (Fin 8) (Fin 8) ℤ) (t : Fin 8 → X) :
    matAct N (matAct M t) = matAct (N * M) t := by
  funext v
  simp only [matAct, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

theorem matAct_one {X : Type} [AddCommGroup X] (t : Fin 8 → X) : matAct 1 t = t := by
  funext v
  simp [matAct, Matrix.one_apply, ite_smul]

def matEquiv {X : Type} [AddCommGroup X] (M : Matrix (Fin 8) (Fin 8) ℤ) (h : M.det = 1) :
    (Fin 8 → X) ≃+ (Fin 8 → X) where
  toFun := matAct M
  invFun := matAct M.adjugate
  left_inv t := by rw [matAct_mul, Matrix.adjugate_mul, h, one_smul, matAct_one]
  right_inv t := by rw [matAct_mul, Matrix.mul_adjugate, h, one_smul, matAct_one]
  map_add' s t := by funext v; simp [matAct, smul_add, Finset.sum_add_distrib]

def sumHom {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (c : Fin 8 → (X →+ Y)) : (Fin 8 → X) →+ Y :=
  AddMonoidHom.mk' (fun y => ∑ v, c v (y v)) fun s t => by simp [Finset.sum_add_distrib]

end GlobalTheory.Poinc.EighthPow


open GlobalTheory.Poinc.EighthPow in
theorem GlobalTheory.Poinc.EighthPow.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∃ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL ϖ β hs hp hτ
  haveI := hdvr
  have hext : ∀ v, ∃ p : G' ⟶ G, IsMonHom p ∧
      (Over.pullback (jK R)).map p ≫ U.gen.hom = U'.gen.hom ≫ pr v := by
    intro v
    have h1 := U'.gen_hom
    have h2 := U.gen_hom
    have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    haveI := hpr v
    obtain ⟨F, ⟨hF, hFe⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G' G hG' hG
      (U'.gen.hom ≫ pr v ≫ U.gen.symm.hom) inferInstance
    refine ⟨F, hF, ?_⟩
    have hFe' : (Over.pullback (jK R)).map F = U'.gen.hom ≫ pr v ≫ U.gen.inv := hFe
    rw [hFe']
    simp
  choose pG hpGm hpG using hext
  have hc : ∀ v, ∃ ρ, TorMatch U U' (RingHom.id R) (pG v).left ρ := fun v =>
    GlobalTheory.Poinc.HomTor.exists_torMatch R hRb G hG D A U G' hG' D' A' U' (pG v) (hpGm v)
  choose c hc using hc
  obtain ⟨hbij, hmat⟩ := GlobalTheory.T.characters_eighthPower_elementaryMatrices_alt R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hpG c hc
  let Φ : (Fin 8 → D.toPre.X) ≃+ D'.toPre.X := AddEquiv.ofBijective (sumHom c) hbij
  let Mq : (Fin 8 → D.toPre.X) ≃+ (Fin 8 → D.toPre.X) := matEquiv (W + W.transpose) hW.2
  let e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X) := (Mq.trans Φ).symm
  have he : ∀ y, Φ (Mq (e y)) = y := fun y => (Mq.trans Φ).apply_symm_apply y
  have he' : ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := he
  refine ⟨e, ?_, ?_⟩
  · intro y r hr
    have hlab := fun v => GlobalTheory.T.torsionLabels_eighthPower_projections R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hpG c hc e
      he' v
    refine GlobalTheory.Poinc.E8Order.main R hdvr D.toPre D'.toPre D'.tau_bimult D'.psi_even D.tau_bimult W hW ϖ β hs hp hτ c e
      he' ?_ y r hr
    intro v a' b x x' hx hx'
    exact GlobalTheory.TauFormHom.main R hRb hdvr G hG D A U G' hG' D' A' U' (pG v) (hpGm v) (c v)
      ((Pi.evalAddMonoidHom (fun _ => D.toPre.X) v).comp e.toAddMonoidHom) (hc v) (hlab v) a' b x x' hx hx'
  · intro a b f f₁ m hf hf₁ hcomp hm y
    have hmc := hmat a b f f₁ m hf hf₁ hcomp hm
    have hy : y = Φ (Mq (e y)) := (he y).symm
    let t' : Fin 8 → D.toPre.X := fun w => if w = b then Mq (e y) a else 0
    have hmy : m y = Φ t' := by
      conv_lhs => rw [hy]
      show m (∑ w, c w (Mq (e y) w)) = ∑ w, c w (t' w)
      have hL : m (∑ w, c w (Mq (e y) w)) = c b (Mq (e y) a) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]; simp [hmc]
      have hR : ∑ w, c w (t' w) = c b (Mq (e y) a) := by
        rw [Finset.sum_eq_single b (fun w _ hw => by simp only [t', if_neg hw, map_zero]) (by simp)]
        simp only [t', if_pos rfl]
      rw [hL, hR]
    have hkey : Mq (e (m y)) = t' := Φ.injective (by rw [he, hmy])
    intro v
    have h := congrFun hkey v
    change ∑ u, (W + W.transpose) v u • e (m y) u = _ at h
    rw [h]
    rfl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalMono

theorem coords_eq_zero {O : Type} [CommRing O] [StarRing O] [IsDedekindDomain O]
    [Module.Finite ℤ O] [Module.Free ℤ O] {w : O} (hw : w + star w = 1)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {J : Type} [Fintype J] (ε : Module.Basis J ℤ (PolFan.balForms (star : O → O) X))
    {B : Type} [AddCommGroup B] (c : J → B)
    (hc : ∀ a b, ∑ k, (ε k : LinearMap.BilinForm ℤ X) a b • c k = 0) (k : J) : c k = 0 := by
  classical
  have := Forms.projective_of_int O X
  have := Forms.finite_balTensor (O := O) (X := X)
  have := Forms.free_balTensor (X := X) hw
  let e := Module.Free.chooseBasis ℤ ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X))
  have hm := Forms.balTensorMk_mem_balForms O X
  let β : _ → PolFan.balForms (star : O → O) X := fun j =>
    ⟨(Forms.balTensorMk O).compr₂ (e.coord j),
      fun y x => congrArg (e.coord j) (hm.1 y x), fun a y x => congrArg (e.coord j) (hm.2 a y x)⟩
  let L : J → ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X)) →+ ℤ := fun i =>
    Forms.balTensorLift (O := O) ⟨(ε i : LinearMap.BilinForm ℤ X), (ε i).2.1, (ε i).2.2⟩
  have hL (i a b) : L i (Forms.balTensorMk O a b) = (ε i : LinearMap.BilinForm ℤ X) a b := rfl
  let Φ : ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X)) →+ B :=
    ∑ i, (zmultiplesHom B (c i)).comp (L i)
  have hΦa (t) : Φ t = ∑ i, L i t • c i := by
    simp [Φ, AddMonoidHom.finsetSum_apply]
  have hΦ : Φ = 0 := Forms.balTensor_hom_ext fun a b => by
    rw [hΦa]
    exact hc a b
  have hε (i) : ε i = ∑ j, L i (e j) • β j := by
    apply Subtype.ext
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]

    rw [← hL, ← e.sum_repr (Forms.balTensorMk O a b), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_eq_mul, _root_.mul_comm]
    rfl
  have hδ (i) : L i (∑ j, ε.repr (β j) k • e j) = ε.repr (ε i) k := by
    have h1 := congrArg (ε.coord k) (hε i)

    rw [map_sum] at h1

    rw [map_sum, ← ε.coord_apply, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, _root_.mul_comm, ε.coord_apply]
  have h := hΦa (∑ j, ε.repr (β j) k • e j)
  simp only [hδ, hΦ, AddMonoidHom.zero_apply] at h
  simpa [Finsupp.single_apply] using h.symm

theorem eq_of_prod_zpow_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F] (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms H.bar X)) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ X) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ X) a b) → x = y := by
  intro E _ _ _ H X _ _ _ _ F _ I _ ε x y hx hy h
  letI : StarRing (𝓞 E) :=
    { star := H.bar
      star_involutive := fun a => by
        apply Subtype.ext
        change ((H.bar (H.bar a) : 𝓞 E) : E) = a
        rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
      star_mul := fun a b => by rw [map_mul, _root_.mul_comm]
      star_add := fun a b => map_add H.bar a b }
  have hw : H.w0 + H.bar H.w0 = 1 := PullbackSections.CVA.cmHostUnit_add_conj_eq_one H
  let u : I → Fˣ := fun i => Units.mk0 (x i) (hx i)
  let v : I → Fˣ := fun i => Units.mk0 (y i) (hy i)
  have huv : ∀ a b, ∏ i, (u i / v i) ^ ((ε i : LinearMap.BilinForm ℤ X) a b) = 1 := by
    intro a b
    rw [Finset.prod_congr rfl (fun i _ => div_zpow _ _ _), Finset.prod_div_distrib, div_eq_one]
    apply Units.ext
    simpa [u, v, Units.coe_prod] using h a b
  funext k
  have hk := coords_eq_zero (O := 𝓞 E) hw ε (fun i => Additive.ofMul (u i / v i))
    (fun a b => by
      apply Additive.toMul.injective
      simp only [toMul_sum, toMul_zsmul, toMul_ofMul, toMul_zero]
      exact huv a b) k
  have hk' : u k / v k = 1 := hk
  simpa [u, v] using congrArg Units.val (div_eq_one.1 hk')

end GlobalTheory.BalMono
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.eq_self_of_cone_congMod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)) (q : ℕ), IsPolFan H.bar q φ → NoSelfInt H.bar q φ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Finite (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ δ → (∀ y, y ≠ 0 → 0 < ∑ i, δ i y y) → ∀ (u : X ≃ₗ[𝓞 E] X) (a a' : Fin m → ℕ), (∀ i, 0 < a i) → (∀ i, 0 < a' i) → (∀ y z, ∑ i, (a i : ℤ) * δ i (u y) (u z) = ∑ i, (a' i : ℤ) * δ i y z) → ∀ N : ℕ, 3 ≤ N → (∀ y, ∃ z, u y = y + N • z) → ∀ y, u y = y := by
  intro E _ _ _ H φ q hfan hno X _ _ _ _ _ hX m δ hδ hdef u a a' ha ha' hsum N hN hcong
  haveI : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int (𝓞 E) X
  have hon : IsPolFanOn H.bar φ X := hfan X hX
  have hu : IsCone H.bar φ fun i => pull u.toLinearMap (δ i) := hδ.pull_equiv u
  have heq : ∑ j, a j • pull u.toLinearMap (δ j) = ∑ j, a' j • δ j := LinearMap.ext₂ fun y z => by
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using hsum y z
  have hfix : ∀ j, pull u.toLinearMap (δ j) = δ j := by
    intro j
    obtain ⟨j', hj'⟩ := GlobalTheory.Poinc.intCone_face (𝓞 E) H.bar φ X hon _ _ _ δ hu hδ a a' ha heq j
    obtain rfl := hno X hX m δ hδ u j j' hj'
    exact hj'
  have hβ : ∀ y z, (∑ i, δ i) (u y) (u z) = (∑ i, δ i) y z := fun y z => by
    simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun₂ (hfix i) y z
  have he := GlobalTheory.Poinc.eq_refl_of_isometry_congMod X (∑ i, δ i)
    (fun y hy => by simpa [LinearMap.sum_apply] using hdef y hy) (u.restrictScalars ℤ) (fun y z => hβ y z) N hN
    (fun y => hcong y)
  intro y
  exact LinearEquiv.congr_fun he y
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.BalRank.finrank_balForms : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], Module.finrank ℤ (balForms H.bar X) = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) X * Module.finrank (𝓞 E) X := by
  intro E _ _ _ H X _ _ _ _
  obtain ⟨f, m, hm, hf, hmf⟩ := GlobalTheory.T.exists_free_submodule_finite_index_numberField (E := E) X
  have h1 := GlobalTheory.T.two_mul_finrank_balancedSymmIntBilinForms H X
  have h2 := GlobalTheory.T.finrank_balancedIntBilinForms_eq_of_finite_index H.bar X _ f m hm hf hmf
  have h3 := GlobalTheory.T.finrank_balancedIntBilinForms_pi H (Fin (Module.finrank (𝓞 E) X))
  rw [Fintype.card_fin] at h3
  obtain ⟨k, hk⟩ : 2 ∣ Module.finrank ℚ E := ⟨_, IsTotallyComplex.finrank E⟩
  rw [hk, Nat.mul_div_cancel_left _ two_pos]
  rw [← h2, h3, hk] at h1
  nlinarith [h1]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.eq_of_prod_zpow_symmetricFormBasis_eq : ∀ (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) → x = y := by
  first | exact @GlobalTheory.SymMono.eq_of_prod_zpow_eq | exact GlobalTheory.SymMono.eq_of_prod_zpow_eq | (intros; apply GlobalTheory.SymMono.eq_of_prod_zpow_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (r m N n : ℕ), 1 ≤ n → ∀ (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin r → ℤ)) (s₁ s₂ : (Fin m ⊕ Fin N) → V) (ga : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)), (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → (∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (a) (b))) → ∃ c₁ c₂ : Fin m → ℕ, (∀ k, 0 < c₁ k) ∧ (∀ k, 0 < c₂ k) ∧ ∑ k, c₁ k • ε (.inl k) = ∑ k, c₂ k • pull ga.toLinearMap (ε (.inl k)) := by
  first | exact @GlobalTheory.TInj.coneval | exact GlobalTheory.TInj.coneval | (intros; apply GlobalTheory.TInj.coneval <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.smoothCone_sum_generators_eq_of_common_interiorPoint : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m m' : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (δ' : Fin m' → LinearMap.BilinForm ℤ X), IsCone id φ δ → IsCone id φ δ' → ∀ (c : Fin m → ℕ) (c' : Fin m' → ℕ), (∀ k, 0 < c k) → (∀ k, 0 < c' k) → ∑ k, c k • δ k = ∑ k, c' k • δ' k → ∑ k, δ k = ∑ k, δ' k := by
  first | exact @GlobalTheory.TInj.coneSum_eq | exact GlobalTheory.TInj.coneSum_eq | (intros; apply GlobalTheory.TInj.coneSum_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.ThetaTermAdic

theorem decomp (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (hm : 0 < m) :
    ∃ (mu rh : X → X), (Set.range rh).Finite ∧ ∀ χ, χ = m • mu χ + rh χ := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  refine ⟨fun χ => ∑ i, (b.repr χ i / (m : ℤ)) • b i, fun χ => ∑ i, (b.repr χ i % (m : ℤ)) • b i, ?_, fun χ => ?_⟩
  · have hS : (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ X => Set.Ico (0 : ℤ) m).Finite :=
      Set.Finite.pi fun _ => Set.finite_Ico _ _
    refine (hS.image fun f => ∑ i, f i • b i).subset ?_
    rintro _ ⟨χ, rfl⟩
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    exact ⟨fun i => b.repr χ i % m, fun i _ => ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩, rfl⟩
  · conv_lhs => rw [← b.sum_repr χ]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul, ← add_smul, Int.mul_ediv_add_emod]

theorem mul_mem_smul_top {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (a s : S)
    (hs : s ∈ (I • ⊤ : Submodule R S)) : a * s ∈ (I • ⊤ : Submodule R S) := by
  rw [Ideal.smul_top_eq_map] at hs ⊢
  exact Ideal.mul_mem_left _ a hs

theorem core {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (N : GlobalTheory.Ex.NumD (Kb R))
    (S : Subalgebra R (Kb R)) [Module.Finite R S] (m : ℕ) (hm : 0 < m) (q : N.QT (m ^ 2))
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}),
      (N.θ x x' x'' : Kb R) ∈ S ∧ (((N.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}), (N.σ x : Kb R) ∈ S ∧ (((N.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S)
    (hthS : ∀ χ, N.th (N.c χ * (q.1.2 ^ m).b) ∈ S) (hψS : ∀ χ, (N.ψ χ : Kb R) ∈ S)
    (hψn : ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N.ψ χ}.Finite) :
    ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R),
      (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧
      ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  classical
  set h := q.1.2 ^ m with hdef
  set y := q.1.1.toAdd with hy
  have hh : h ^ m = N.io y := by rw [hdef, ← pow_mul, ← sq]; exact N.mem_QT.1 q.2
  obtain ⟨mu, rh, hrf, hχ⟩ := decomp N.X m hm
  choose w hwS hw using GlobalTheory.T.thetaSeriesTerm_smul_add_decomposition (Kb R) N S.toSubring m h y hh hθ hσ
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  obtain ⟨e, he⟩ : ∃ e, m ^ 2 = e + 1 := ⟨m ^ 2 - 1, by have := pow_pos hm 2; omega⟩
  let K : N.X → Kb R := fun b => ((N.wQ q / mulq N.θ N.σ m q.1.2.b : (Kb R)ˣ) : Kb R) *
    ((N.ψ b * h.s b * (N.ψ (m • b + y))⁻¹ : (Kb R)ˣ) : Kb R)
  let z0 : N.X → Kb R := fun χ => (w (mu χ) (rh χ) : Kb R) * (N.ψ (mu χ) : Kb R) ^ e * N.th (N.c χ * h.b) *
    N.ψ (mu χ + (m • rh χ + y))
  have key : ∀ χ, N.txT m q χ = K (rh χ) * z0 χ := fun χ => by
    have a := hw (mu χ) (rh χ)
    rw [← hχ χ, he, NumD.τ] at a
    simp only [NumD.txT, NumD.vt, K, z0]
    rw [← hdef, a]
    push_cast
    field_simp
    ring
  have hz0 : ∀ χ, z0 χ ∈ S := fun χ =>
    S.mul_mem (S.mul_mem (S.mul_mem (Subalgebra.mem_toSubring.1 (hwS _ _)) (S.pow_mem (hψS _) _)) (hthS χ)) (hψS _)
  let zS : N.X → S := fun χ => ⟨z0 χ, hz0 χ⟩
  have hzn : ∀ n : ℕ, {χ | zS χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R S)}.Finite := fun n => by
    refine (hrf.biUnion fun b _ => (hψn n).image fun χ' => m • (χ' - (m • b + y)) + b).subset ?_
    intro χ hχn
    refine Set.mem_biUnion (Set.mem_range_self χ) ⟨mu χ + (m • rh χ + y), ?_, ?_⟩
    · rintro ⟨s', hs', he'⟩
      refine hχn ?_
      have e1 : zS χ = (⟨(w (mu χ) (rh χ) : Kb R) * (N.ψ (mu χ) : Kb R) ^ e * N.th (N.c χ * h.b),
          S.mul_mem (S.mul_mem (Subalgebra.mem_toSubring.1 (hwS _ _)) (S.pow_mem (hψS _) _)) (hthS χ)⟩ : S) * s' :=
        Subtype.ext (by simp only [zS, z0, Subalgebra.coe_mul, he'])
      rw [e1]
      exact mul_mem_smul_top _ _ _ hs'
    · change m • (mu χ + (m • rh χ + y) - (m • rh χ + y)) + rh χ = χ
      rw [add_sub_cancel_right]; exact (hχ χ).symm
  obtain ⟨c, hc, hcn⟩ := GlobalTheory.T.exists_coeffs_adic_finite_of_span_eq_univ R S r s hs N.X zS hzn
  haveI : Fintype (Set.range rh) := hrf.fintype
  refine ⟨Fin r × Set.range rh, inferInstance, fun k => K k.2 * (s k.1 : Kb R),
    fun χ k => if (⟨rh χ, Set.mem_range_self χ⟩ : Set.range rh) = k.2 then c χ k.1 else 0, fun χ => ?_, fun n => ?_⟩
  · rw [key, Fintype.sum_prod_type]
    have hz : z0 χ = ∑ j, algebraMap R (Kb R) (c χ j) * (s j : Kb R) := by
      have := congrArg Subtype.val (hc χ)
      simpa [zS, Algebra.smul_def] using this
    rw [hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← IsScalarTower.algebraMap_apply]
    ring
  · refine (hcn n).subset fun χ hχ hall => hχ fun k => ?_
    dsimp only
    split_ifs
    · exact hall _
    · exact zero_mem _

theorem terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)) (q : N.QT (m ^ 2)), ν.QPt p q → ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R), (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧ ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  intro R _ _ _ hB D N ν m hm hmu p q hq
  haveI : IsNoetherianRing R := hB.1.1
  obtain ⟨N', ν', q', S, hth, hq', hfin, hθ, hσ, hthS, hψS, hψn⟩ := GlobalTheory.T.exists_integral_gauge_finite_extension R hB D N ν m hm hmu p
  haveI := hfin
  obtain ⟨I, hl, -, hI⟩ := GlobalTheory.GaugeHom.exists_hom R D.toPre (Kb R) (Kb R) (RingHom.id _) (RingHom.id_comp _) N N' ν ν' hth
  obtain ⟨e1, e2⟩ := hI (m ^ 2) p p q q' (GlobalTheory.SeriesCompare.qkExt_id p) hq hq'
  have htx : ∀ χ, N.txT m q χ = N'.txT m q' (I.e χ) := fun χ => by
    rw [I.txT_eq hm q q' e1 e2 χ, hl, Units.val_one, _root_.one_mul, RingHom.id_apply]
  obtain ⟨Jx, fJ, g, c, hc, hcn⟩ := core N' S m hm.pos q' hθ hσ hthS hψS hψn
  exact ⟨Jx, fJ, g, fun χ => c (I.e χ), fun χ => by rw [htx, hc], fun n => (hcn n).preimage I.e.injective.injOn⟩

end GlobalTheory.ThetaTermAdic
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → ∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) := by
  first | exact @GlobalTheory.Mum.OneTraitTheta.isThetaPt_of_series | exact GlobalTheory.Mum.OneTraitTheta.isThetaPt_of_series | (intros; apply GlobalTheory.Mum.OneTraitTheta.isThetaPt_of_series <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.galois_descent_open_invariant_subscheme : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ x : H.toScheme, spMap (algebraMap R R') (G'.hom (H.ι x)) = closedPoint R → ∃ (V : X.left.Opens) (O : Y.left.Opens), π x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen O ∧ φ 0 ⁻¹ᵁ O = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ (H.ι ''ᵁ (π ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.Mum.exists_affine_chart | exact GlobalTheory.Mum.exists_affine_chart | (intros; apply GlobalTheory.Mum.exists_affine_chart <;> assumption)
end
