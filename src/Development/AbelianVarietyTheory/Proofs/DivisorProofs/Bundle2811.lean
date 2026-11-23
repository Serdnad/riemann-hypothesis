module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqZeroOfValR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle095
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.TauTwist ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem degenerationPointOfLattice_zsmul (T : Over (Spec (CommRingCat.of R))) (n : ℤ) (b : D.X) : cP D T (n • b) = cP D T b ^ n := by
  let f : Multiplicative D.X →* (T ⟶ D.P.A) :=
    { toFun := fun x => cP D T x.toAdd
      map_one' := by simpa using cPoint_nsmul D T 0 0
      map_mul' := fun x y => cPoint_add D T _ _ }
  have := map_zpow f (Multiplicative.ofAdd b) n
  simpa [f] using this

theorem overSpec_comp_zpow_grpObj {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (y : T ⟶ D.P.A) (n : ℤ) :
    ρ ≫ y ^ n = (ρ ≫ y) ^ n := by
  let f : (T ⟶ D.P.A) →* (T' ⟶ D.P.A) :=
    { toFun := fun x => ρ ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  exact map_zpow f y n

theorem value_tau_add_nsmul_mul_iteratedCube (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (a₀ m v : D.X) (k : ℕ) :
    val (D.tau (a₀ + k • m) v) (𝟙 (TK R).left) z J *
        cubN (th D z J) k (cP D (TK R) a₀) (cP D (TK R) m) (cP D (TK R) v) =
      val (D.tau a₀ v) (𝟙 (TK R).left) z J * val (D.tau m v) (𝟙 (TK R).left) z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero]; simp [cubN]
  | succ k ih =>
    have e := val_tau_add (𝟙 (TK R)) hJ hB (a₀ + k • m) m v
    rw [cPoint_add, cPoint_nsmul] at e
    simp only [Over.id_left] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ]
    simp only [cubN] at ih
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e' ih' ⊢
    rw [succ_nsmul]
    linear_combination (norm := abel) e' + ih'

theorem exists_lamGen_zpow : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℤ),
    ∃ g : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ n))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A))) (Sum.elim Oε (fun l => -n * Oε l))), g.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a (n • b)) (𝟙 _) z J *
          val g (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J = val (D.tau a b) (𝟙 _) z J ^ n := by
  intro R _ _ D hB n
  have hL := D.P.isLB
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (1 : D.P.A ⊗ D.P.A ⟶ D.P.A) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left, (1 * snd D.P.A D.P.A ^ k).left,
          (1 * fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left, (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        ![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)]
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (k : ℤ)))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(k : ℤ) * Oε l)) := by
      intro U _ h
      have e1 : (1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (k : ℤ) := by rw [_root_.one_mul, zpow_natCast, mul_comm]
      have e2 : (1 * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = snd D.P.A D.P.A ^ (k : ℤ) := by
        rw [_root_.one_mul, zpow_natCast]
      have e3 : (1 * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A := _root_.one_mul _
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      rw [e1, e2, e3, e4, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF t ht
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, hv (TK R) _ z J hJ, MonObj.comp_one, lift_fst, lift_snd]
    have e := val_tau_nsmul (𝟙 (TK R)) hJ hB k b a
    rw [val_tau_symm _ hJ (k • b) a, val_tau_symm _ hJ b a] at e
    simp only [Over.id_left] at e
    rw [natCast_zsmul, zpow_natCast]
    exact e
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (snd D.P.A D.P.A ^ (-(k : ℤ))) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A).left, (snd D.P.A D.P.A ^ (-(k : ℤ))).left,
          (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        (fun i => -(![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)] : Fin 8 → ℤ) i)
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (-(k : ℤ))))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(-(k : ℤ)) * Oε l)) := by
      intro U _ h
      have e0 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = 1 := by
        rw [zpow_neg, zpow_natCast, inv_mul_cancel]
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      have e5 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (-(k : ℤ)) := mul_comm _ _
      rw [e0, _root_.one_mul, e4, e5, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF (LB.invGen _ _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, val_inv, hv (TK R) _ z J hJ, overSpec_comp_zpow_grpObj, lift_fst, lift_snd]
    have c1 : (toUnit (TK R) ≫ D.c b) ^ (-(k : ℤ)) = cP D (TK R) ((-(k : ℤ)) • b) := (degenerationPointOfLattice_zsmul _ _ _).symm
    rw [c1]
    have e := value_tau_add_nsmul_mul_iteratedCube hB hJ ((-(k : ℤ)) • b) b a k
    have z0 := val_tau_nsmul (𝟙 (TK R)) hJ hB 0 b a
    rw [zero_nsmul] at z0
    simp only [Over.id_left, pow_zero, cubN, Finset.range_zero, Finset.prod_empty, _root_.mul_one] at z0
    have s0 : (-(k : ℤ)) • b + k • b = 0 := by rw [← natCast_zsmul, ← add_smul, neg_add_cancel, zero_smul]
    rw [s0, z0, _root_.one_mul] at e
    have s1 := val_tau_symm (𝟙 (TK R)) hJ a ((-(k : ℤ)) • b)
    have s2 := val_tau_symm (𝟙 (TK R)) hJ a b
    simp only [Over.id_left] at s1 s2
    rw [s1, s2]
    rw [show cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c a) =
      cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (cP D (TK R) b) (cP D (TK R) a) from rfl, e,
      mul_inv_rev, zpow_neg, zpow_natCast, mul_comm (_ ^ k)⁻¹, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

end GlobalTheory.Mum
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.AbConst

open GlobalTheory.KS.GlueDer

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

theorem desc_agree (hdd : ∀ a, IsField ⊤ (dd a)) {K : Type} [Field K] [CharZero K] (φ : R →+* K)
    (hΘ : ∀ a b, φ (h.Θ a b) = 0) {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left)
    (hm : m ≫ Q.P.A.hom = p ≫ spMap φ) (V : h.J → Q.P.A.left.Opens) (hV : ∀ i, h.W i = Y.q.left ⁻¹ᵁ V i)
    (e : h.J → Fld Q.P.A.left)
    (hq : ∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (e i V' f) = h.d i _ ((Y.q.left.app V').hom f))
    (i i' : h.J) (W : Q.P.A.left.Opens) (hW : W ≤ V i ⊓ V i') (f : Γ(Q.P.A.left, W)) :
    (m.app W).hom (e i W f) = (m.app W).hom (e i' W f) := by
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  let a := pullback.fst Y.q.left m
  let b := pullback.snd Y.q.left m
  have w : a ≫ Y.q.left = b ≫ m := pullback.condition
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  let π := (a.appLE _ _ hle).hom
  have key : ∀ x, (b.app _).hom ((m.app W).hom x) = π ((Y.q.left.app W).hom x) := fun x => by
    have k : ∀ (c : pullback Y.q.left m ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W),
        (b.app _).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
      rintro _ rfl hc
      rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE b]
      rfl
    rw [k _ w hle]
    exact congrArg (fun ψ => ψ.hom x) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)
  have hc : ∀ r, π (constFn Y.H.hom _ r) = constFn (b ≫ p) _ (φ r) := fun r => by
    rw [← res_const (b ≫ p) hle, ← app_const φ Y.H.hom (b ≫ p) a (by
      rw [← Over.w Y.q, reassoc_of% w, hm, Category.assoc])]
    rfl
  refine FunDescent.app_injective b _ ?_
  show (b.app _).hom ((m.app W).hom _) = (b.app _).hom ((m.app W).hom _)
  rw [key, key, hq i W (hW.trans inf_le_left), hq i' W (hW.trans inf_le_right)]
  refine lift_agree h hdd i i' _ (le_inf ((pre_mono _ (hW.trans inf_le_left)).trans (hV i).ge)
    ((pre_mono _ (hW.trans inf_le_right)).trans (hV i').ge)) π ?_ (fun a b => ?_) _
  · have := (two_ne_zero (α := K)).isUnit.map ((((b ≫ p).appLE ⊤ (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (fun _ _ => trivial)).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    rwa [map_ofNat] at this
  · rw [hc, hΘ, constFn, map_zero, map_zero]

end Ray

theorem exists_locDerK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a, IsField ⊤ (dd a)) → IsBasic Y h → ∀ {K : Type} [Field K] [CharZero K] (φ : R →+* K), (∀ a b, φ (h.Θ a b) = 0) → ∀ {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left), m ≫ Q.P.A.hom = p ≫ spMap φ → ∃ dl : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(Z, m ⁻¹ᵁ W), GlobalTheory.KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) ⊤ dl ∧ (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ Z), a ≫ Y.q.left = b ≫ m → ∀ (i : h.J) (W : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m ⁻¹ᵁ W))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB K _ _ φ hΘ Z p m hm
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  choose V hV using fun i => (hB i).1
  choose e he hq using fun i => exists_desc Y (V i) (h.d i) D (hV i ▸ h.lift i)
    fun V' hV' => (hB i).2.2.2 0 V' ((pre_mono _ hV').trans (hV i).ge)
  have hc := fun i i' W hW f => desc_agree Y h hdd φ hΘ p m hm V hV e hq i i' W hW f
  have hcov : ∀ y, ∃ i, m y ∈ V i := fun y => by
    obtain ⟨x, hx⟩ := Y.q.left.surjective (m y)
    have hx' : x ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    rw [hV] at hi
    exact ⟨i, hx ▸ hi⟩
  have hloc : ∀ i, KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) (V i) (fun W f => (m.app W).hom (e i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(he i).1.1 W hW, map_add (f := _)]
    · rw [(he i).1.2.1 W hW, map_add (f := _), map_mul, map_mul]
    · rw [(he i).1.2.2 W W' h' hW, rsT_eq (pre_mono m h'), res_app m h']
    · rw [(he i).2 W hW, app_const φ _ p m hm]
  obtain ⟨dl, hdl, hu⟩ := InteriorKS.glue_along p Q.P.A.hom m _ V hcov (fun i W f => (m.app W).hom (e i W f)) hloc hc
  refine ⟨dl, hdl, fun Z' a b w i W hWi f => ?_⟩
  have hWV : W ≤ V i := fun x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    exact (hWi.trans (hV i).le) hx
  have e1 : dl W f = (m.app W).hom (e i W f) := by
    refine hu W f _ fun j => ?_
    rw [res_app m inf_le_left, ← (he i).1.2.2 W (W ⊓ V j) inf_le_left hWV f]
    exact hc i j _ (le_inf (inf_le_left.trans hWV) inf_le_right) _
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  rw [e1, pbT, pbT, dite_eq_left (le_refl _), dite_eq_left hle, ← hq i W hWV]
  have k : ∀ (c : Z' ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W) x,
      (b.appLE (m ⁻¹ᵁ W) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (le_refl _)).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
    rintro _ rfl hc x
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [k (a ≫ Y.q.left) w (by rw [Scheme.Hom.comp_preimage]; exact hle)]
  exact congrArg (fun ψ => ψ.hom (e i W f)) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)

end GlobalTheory.Heat.AbConst
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Heat.AbDescent

theorem pbT_id {X : Scheme.{0}} {U V : X.Opens} (hV : V ≤ U) (s : Γ(X, U)) : pbT (𝟙 X) s V = rsT s V := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 X) hV, GlobalTheory.KS.rsT_of_le hV]
  simp [Scheme.Hom.appLE, resG]
  rfl

theorem pbT_pbT_id {Z X : Scheme.{0}} (q : Z ⟶ X) {U V : X.Opens} (hV : V ≤ U) {W : Z.Opens} (hW : W ≤ q ⁻¹ᵁ V)
    (s : Γ(X, U)) : pbT q (pbT (𝟙 X) s V) W = pbT q s W := by
  rw [pbT_id hV, GlobalTheory.KS.pbT_rsT q hV hW]

theorem descent : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (δH : Fld Y.H.left) (δ : Fld Q.P.A.left), (∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U → δH W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = dlg Y.H Y.q.left Q.P.L δH (jk k) (jk k') Wo) → ∃ (V : K → Q.P.A.left.Opens) (b : ∀ k, Γ(Q.P.A.left, V k)), ⨆ k, V k = ⊤ ∧ (∀ k, V k ≤ Q.P.L.U (jk k)) ∧ ∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg Q.P.A (𝟙 _) Q.P.L δ (jk k) (jk k') (V k ⊓ V k') := by
  intro R _ _ Q O _ _ _ oa Y δH δ hpb K Wk jk hV hcov hle P hP hrel
  have := Y.smooth_q
  have := (AbConst.surjective_q Y).1
  choose V hV using hV
  have hb : ∀ k, ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b (Wk k) = P k := by
    intro k
    have key : ∀ (W : Y.H.left.Opens) (hW : W = Y.q.left ⁻¹ᵁ V k) (p : Γ(Y.H.left, W)), IsWt Y 0 W p →
        ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b W = p := by
      intro W hW p hp
      subst hW
      obtain ⟨a, ha⟩ := AbConst.exists_app_eq Y hp
      exact ⟨a, by rw [GlobalTheory.KS.pbT_of_le _ le_rfl, ← ha, Scheme.Hom.app_eq_appLE]⟩
    exact key _ (hV k) _ (hP k)
  choose b hb using hb
  have hVle : ∀ k, V k ≤ Q.P.L.U (jk k) := by
    intro k y hy
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ Wk k := by rw [hV k]; exact hy
    exact hle k hx
  refine ⟨V, b, ?_, hVle, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ ⨆ k, Wk k := by rw [hcov]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [hV k] at hk; exact hk⟩
  · intro k k'
    have hWo : Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk k ⊓ Wk k' := by
      rw [hV k, hV k']
      exact fun x hx => ⟨hx.1, hx.2⟩
    have h := hrel k k' _ hWo
    apply FunDescent.app_injective Y.q.left (V k ⊓ V k')
    have e : ∀ s : Γ(Q.P.A.left, V k ⊓ V k'),
        (Y.q.left.app (V k ⊓ V k')).hom s = pbT Y.q.left s (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := fun s => by
      rw [GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
    rw [e, e, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_rsT _ inf_le_right le_rfl, GlobalTheory.KS.pbT_rsT _ inf_le_left le_rfl]
    have hbk : ∀ j, Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk j →
        pbT Y.q.left (b j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) = rsT (P j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := by
      intro j hj
      rw [← hb j, GlobalTheory.KS.rsT_pbT _ (hV j).le hj]
    rw [hbk k' (hWo.trans inf_le_right), hbk k (hWo.trans inf_le_left), h]
    have hUo : V k ⊓ V k' ≤ Q.P.L.U (jk k) ⊓ Q.P.L.U (jk k') := inf_le_inf (hVle k) (hVle k')
    unfold dlg
    rw [GlobalTheory.KS.pbT_mul, ← hpb (V k ⊓ V k') (pbT (𝟙 _) (Q.P.L.g (jk k) (jk k')).val (V k ⊓ V k')) _ le_rfl,
      pbT_pbT_id _ hUo le_rfl, pbT_pbT_id _ hUo le_rfl]

end GlobalTheory.Heat.AbDescent
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.AbConstGlob

open GlobalTheory.KS.GlueDer

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem app_rsT {U V : Q.P.A.left.Opens} (h : V ≤ U) (a : Γ(Q.P.A.left, U)) :
    (Y.q.left.app V).hom (rsT a V) = rsT ((Y.q.left.app U).hom a) (Y.q.left ⁻¹ᵁ V) := by
  rw [rsT_eq h, rsT_eq (pre_mono _ h), res_app]

theorem app_constFn (V : Q.P.A.left.Opens) (r : R) :
    (Y.q.left.app V).hom (constFn Q.P.A.hom V r) = constFn Y.H.hom _ r :=
  app_const (RingHom.id R) Q.P.A.hom Y.H.hom Y.q.left
    ((Over.w Y.q).trans ((Category.comp_id _).symm.trans (congrArg (Y.H.hom ≫ ·) (Spec.map_id _).symm))) V r

theorem exists_constFn_top (t : Γ(Q.P.A.left, ⊤)) : ∃ r : R, t = constFn Q.P.A.hom ⊤ r := by
  obtain ⟨s, rfl⟩ := (GlobalTheory.allSixLaws.1.globalFns (Sp R) Q.P.A Q.P.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s, ?_⟩
  simp only [constFn]
  rw [Iso.hom_inv_id_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem exists_const_of_preimage [IsLocalRing R] [IsNoetherianRing R] {K : Type} (V : K → Q.P.A.left.Opens)
    (hc : ⨆ k, Y.q.left ⁻¹ᵁ V k = ⊤) (F : ∀ k, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V k)) (hF : ∀ k, IsWt Y 0 _ (F k))
    (hag : ∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Y.q.left ⁻¹ᵁ V k ⊓ Y.q.left ⁻¹ᵁ V k' →
      rsT (F k) Wo = rsT (F k') Wo) :
    ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  have := Y.smooth_q
  have := (GlobalTheory.Heat.AbConst.surjective_q Y).1
  have inj := FunDescent.app_injective Y.q.left
  choose a ha using fun k => GlobalTheory.Heat.AbConst.exists_app_eq Y (hF k)
  have cov : (⊤ : Q.P.A.left.Opens) ≤ ⨆ k, V k := by
    intro y _
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ ⨆ k, Y.q.left ⁻¹ᵁ V k := by rw [hc]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq V (O := ⊤) (fun _ => le_top) cov a fun k l => by
    apply inj
    rw [app_rsT Y inf_le_left, app_rsT Y inf_le_right, ha, ha]
    exact hag k l _ (le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right))
  obtain ⟨r, rfl⟩ := exists_constFn_top t
  refine ⟨r, fun k => ?_⟩
  rw [← ha, ← ht k, GlobalTheory.KS.rsT_constFn _ le_top, app_constFn]

end GlobalTheory.Heat.AbConstGlob

open GlobalTheory.Heat.AbConstGlob in
theorem GlobalTheory.Heat.AbConstGlob.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (K : Type) (Wk : K → Y.H.left.Opens), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → ∀ F : ∀ k, Γ(Y.H.left, Wk k), (∀ k, IsWt Y 0 _ (F k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (F k) Wo = rsT (F k') Wo) → ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  intro R _ _ _ _ Q O _ _ _ oa Y K Wk hW hc F hF hag
  choose V hV using hW
  obtain rfl : Wk = fun k => Y.q.left ⁻¹ᵁ V k := funext hV
  exact exists_const_of_preimage Y V hc F hF hag
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_genericPoint_abelianVariety_through_formalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) ∧ ξ ≫ P.A.A.hom = spMap ψ ∧ ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' ∧ ∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0 := by
  first | exact @GlobalTheory.UnifGenPoint.main | exact GlobalTheory.UnifGenPoint.main | (intros; apply GlobalTheory.UnifGenPoint.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.leibniz_along_baseConstants_at_points : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (v : Fin n → TanM (𝟙 (Sp R)) G) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat G m L dd ⇑D) (k : ℕ) (a b : R) (ρ τ ρ' τ' : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ r z J) → h.Acts k ρ ρ' → h.Acts k τ τ' → ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D b)) * sval τ r z J := by
  first | exact @GlobalTheory.Heat.Heat.acts_const_at_points | exact GlobalTheory.Heat.Heat.acts_const_at_points | (intros; apply GlobalTheory.Heat.Heat.acts_const_at_points <;> assumption)
end
