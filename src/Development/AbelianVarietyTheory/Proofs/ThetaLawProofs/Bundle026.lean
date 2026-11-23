module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundlePowSectionsEqThetaLevel
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle021
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.lineBundlePow_sections_eq_theta_level : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → Wit x h u τ a b → (∀ s : RR x l, ∃! F, IsLevel τ a b l F ∧ FnPw x u s F) ∧ ∀ F, IsLevel τ a b l F → ∃! s : RR x l, FnPw x u s F := by
  first | exact @GlobalTheory.LevelDict.sections_eq_level | exact GlobalTheory.LevelDict.sections_eq_level | (intros; apply GlobalTheory.LevelDict.sections_eq_level <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.BoxDetUnique

theorem isProper_powObj {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) :
    ∀ n, IsProper (Out.powObj A n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => (AbelianSchemeGerms.isAbelianScheme_powObj A hA n).proper

theorem box_indep {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    (hL : L.IsLB) {m : ℤ} {N : ℕ} (b : Fin N → LB.Sec (pw L m))
    (hb : ∀ c : Fin N → K, (∀ i, ∑ k, cst A.hom (L.U i) (c k) * (show Γ(A.left, L.U i) from (b k).f i) = 0) → c = 0) :
    ∀ (n : ℕ) (q : (Fin n → Fin N) → K), (∀ (y : (Out.powObj A n).left) J, Good L y J →
      ∑ I, kv (Out.powObj A n).hom y (q I) * ∏ c, gs (Out.powPr A c).left y (L.U (J (Out.powPr A c).left))
        ((b (I c)).f (J (Out.powPr A c).left)) = 0) → q = 0 := by
  intro n
  induction n with
  | zero =>
    intro q hq
    let y : (Out.powObj A 0).left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : (Out.powObj A 0).left ⟶ A.left => exists_chart hL (χ y)
    have := hq y J hJ
    rw [Fintype.sum_unique, Fintype.prod_empty, _root_.mul_one, map_eq_zero] at this
    exact funext fun I => (congrArg q (Subsingleton.elim _ _)).trans this
  | succ n ih =>
    intro q hq
    haveI := hA.proper
    haveI := isProper_powObj A hA n
    choose a ha using fun i : Fin N => exists_boxSec (L := L) (fun _ : Unit => 𝟙 A.left) A.hom (fun _ : Unit => (1 : K))
      (fun _ _ => b i)
    choose d hd using fun i : Fin N => exists_boxSec (L := L) (fun c : Fin n => (Out.powPr A c).left) (Out.powObj A n).hom
      (fun I : Fin n → Fin N => q (Fin.cons i I)) (fun I c => b (I c))
    have H := (GlobalTheory.T.section_lin_comb_fiber_product_separated K _ L hL A (Out.powObj A n) Unit (Fin n) (fun _ => 𝟙 A.left) (fun _ => m)
      (fun c => (Out.powPr A c).left) (fun _ => m)).2 N a d (fun c hc => hb c fun i => fn_ext fun y hy => by
        have hy' : (𝟙 A.left : A.left ⟶ A.left) y ∈ LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i) :=
          Set.mem_iInter.2 fun _ => hy
        have := congrArg (gs (𝟙 A.left) y (LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i))) (hc (fun _ => i))
        refine Eq.trans ?_ (((gs_sum' _ y _ hy' _ _).symm.trans this).trans
          ((gs_zero' _ y _ hy').trans (gs_zero' _ y _ hy).symm))
        refine (gs_sum' (𝟙 A.left) y _ hy _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
        refine (gs_mul (𝟙 A.left) y _ hy _ _).trans (Eq.trans ?_ (gs_mul (𝟙 A.left) y _ hy' _ _).symm)
        refine congrArg₂ (· * ·) ((gs_cst A.hom _ y _ hy _).trans (gs_cst A.hom _ y _ hy' _).symm) ?_
        rw [ha k _ _ y _ hy', Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id])
      (fun z J hJ => by
        refine Eq.trans ?_ (hq z J hJ)
        rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Fin N).sum_comp, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine (congrArg₂ (· * ·) (ha i _ _ z _ (hJ.mem _ _)) (hd i _ _ z _ (hJ.mem _ _))).trans ?_
        rw [Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Fin.prod_univ_succ, mul_left_comm, Over.w (snd A (Out.powObj A n))]
        rfl)
    funext I
    have := ih (fun I' => q (Fin.cons (I 0) I')) (fun y J hJ => by
      have h1 := hd (I 0) _ (𝟙 _) y (fun c => J (Out.powPr A c).left) (Set.mem_iInter.2 fun c => hJ _)
      have h0 := h1.symm.trans ((congrArg (gs (𝟙 _) y _) (H _ _)).trans
        (gs_zero' _ y _ (Set.mem_iInter.2 fun c => hJ _)))
      simpa only [Category.id_comp] using h0)
    have h2 := congrFun this (Fin.tail I)
    rwa [Fin.cons_self_tail] at h2

theorem isSquareDetComparison_eq_mul_det_pow_of_basis_change : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b b' : Fin (m ^ x.P.g) → RR x m) (B : (Matrix (Fin (m ^ x.P.g)) (Fin (m ^ x.P.g)) K)ˣ) (lam lam' : Kˣ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → (∀ k, Coords x b (fun k' => B.val k' k) (b' k).f) → IsSquareDeterminantComparison x m al b lam → IsSquareDeterminantComparison x m al b' lam' → lam' = lam * (Matrix.GeneralLinearGroup.det B) ^ (-8 * (m ^ (3 * x.P.g + 2) : ℕ) : ℤ) := by
  intro laws K _ x m al b b' B lam lam' hm hal hb hB
    ⟨ξ, mu, w, Q, rho, hne, hker, hmu, hw, hn, hQ, hlam⟩ ⟨ξ', mu', w', Q', rho', hne', hker', hmu', hw', hn', hQ', hlam'⟩
  have inj : ∀ ζ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x,
      (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ζ I r).left p ≠ (ζ I' r).left p) → Function.Injective ζ := by
    intro ζ h I I' e
    by_contra hI
    obtain ⟨r, hr⟩ := h I I' hI (IsLocalRing.closedPoint K)
    exact hr (by rw [e])
  obtain ⟨σ, rfl⟩ := exists_perm laws.mulN x.P m al hm hal ξ ξ' (inj _ hne) (inj _ hne') hker hker'
  have hL := x.P.isLB
  have hmm : ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) (J), Good x.P.L z J → val mu' r z J = val mu r z J := by
    haveI := x.P.isAb.comm
    exact gen_unique hL (S₀ := Sp K) x.P.A.hom (eSec x.P.A) (Over.w η[x.P.A]) (laws.globalFns _ _ x.P.isAb).2 hmu' hmu
      (fun y J hJ => (hn' y J hJ).1.trans (hn y J hJ).1.symm)
  choose c hc using fun I => gen_ratio hL (Out.powObj x.P.A 4).hom
    (laws.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_powObj _ x.P.isAb 3)).2 (hw (σ I)) (hw' I)
  have hr : ∀ I, (rho' I : K) = c I ^ (m ^ 2) * rho (σ I) := by
    intro I
    let p : (𝟙_ (Over (Sp K))).left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : (𝟙_ (Over (Sp K))).left ⟶ x.P.A.left => exists_chart hL (χ p)
    have h1 := (hn p J hJ).2 (σ I)
    have h2 := (hn' p J hJ).2 I
    simp only [hmm _ _ p J hJ] at h2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, gs_cst _ _ p ⊤ trivial, Category.comp_id] at h1 h2
    rw [hc I _ _ p J hJ, mul_pow, _root_.mul_assoc, h1, ← _root_.mul_assoc, Units.mul_left_inj,
      show eSec (Out.powObj x.P.A 4) ≫ (Out.powObj x.P.A 4).hom = (𝟙_ (Over (Sp K))).hom from Over.w η[Out.powObj x.P.A 4],
      ← map_pow, ← map_mul] at h2
    exact ((kv _ p).injective h2).symm
  have hind := box_indep x.P.A x.P.isAb hL b (fun c hc => by
    obtain ⟨c₀, -, hu⟩ := hb ⟨fun _ => 0, fun i j => by rw [map_zero, map_zero, mul_zero]⟩
    exact (hu c fun i => (hc i).symm).trans (hu 0 fun i =>
      (Finset.sum_eq_zero fun k _ => by rw [Pi.zero_apply, map_zero, zero_mul]).symm).symm) 4
  have hq : ∀ I I', Q (σ I) I' = c I * ∑ d, Q' I d *
      (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d := by
    intro I I'
    refine sub_eq_zero.1 (congrFun (hind (fun I' => Q (σ I) I' - c I * ∑ d, Q' I d *
      (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d) fun y J hJ => ?_) I')
    have h1 := (hQ (σ I) y J hJ).symm.trans (hQ' I y J hJ)
    rw [hc I _ _ y J hJ, mul_comm (kv _ _ _), _root_.mul_assoc, Units.mul_right_inj] at h1
    simp only [gs_cst _ _ y ⊤ trivial, Category.id_comp] at h1
    have h3 : ∀ (r : (Out.powObj x.P.A 4 ⟶ x.P.A)) k, gs r.left y (x.P.L.U (J r.left)) ((b' k).f (J r.left)) =
        ∑ k', kv (Out.powObj x.P.A 4).hom y (B.val k' k) * gs r.left y (x.P.L.U (J r.left)) ((b k').f (J r.left)) := by
      intro r k
      refine (congrArg (gs r.left y (x.P.L.U (J r.left))) (hB k (J r.left))).trans ?_
      refine (gs_sum' _ y _ (hJ _) _ _).trans (Finset.sum_congr rfl fun k' _ => ?_)
      rw [gs_mul _ y _ (hJ _), gs_cst _ _ y _ (hJ _), Over.w r]
    simp only [h3] at h1

    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, h1, map_mul, map_sum, Matrix.of_apply, map_prod,
    _root_.mul_assoc, ← Finset.mul_sum]
    rw [sub_eq_zero]
    congr 1
    simp only [Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_sum, Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp only [Finset.prod_mul_distrib]
  have key := det_calc σ Q Q' _ c (fun I => rho I) (fun I => rho' I) (m ^ 2) hq hr
  rw [← hlam, ← hlam', GlobalTheory.det_kroneckerPower, ← pow_mul] at key
  have e : lam = lam' * (Matrix.GeneralLinearGroup.det B) ^ (8 * m ^ (3 * x.P.g + 2)) := by
    apply Units.ext
    rw [key, Units.val_mul, Units.val_pow_eq_pow_val]
    congr 2
    ring
  rw [e, _root_.mul_assoc, ← zpow_natCast, ← zpow_add]
  simp

end GlobalTheory.BoxDetUnique
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta
open Matrix

variable {g : ℕ}

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma exists_column_sum_eq_add_two_mul (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (c : Fin 4) :
    ∃ s : ℤ, ∑ r, al r c = m + 2 * s := by
  have h1 : ∑ r, al r c * al r c = m := by
    have := congrFun (congrFun hal c) c
    simpa [Matrix.mul_apply] using this
  have h2 : Even (∑ r, al r c * (al r c - 1)) := Finset.even_sum _ fun r _ => Int.even_mul_pred_self _
  obtain ⟨s, hs⟩ := h2
  refine ⟨-s, ?_⟩
  have : ∑ r, al r c * (al r c - 1) = ∑ r, al r c * al r c - ∑ r, al r c := by
    simp [mul_sub, Finset.sum_sub_distrib]
  linarith

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma exists_int_two_mul_dotProduct_of_half_integral {g : ℕ} (a : Fin g → ℂ) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (k : Fin g → ℤ) :
    ∃ t : ℤ, 2 * (a ⬝ᵥ fun i => (k i : ℂ)) = t := by
  refine ⟨∑ i, if a i = 0 then 0 else k i, ?_⟩
  simp only [dotProduct, Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases ha i with h | h <;> simp [h]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma sum_intCast_mul_column_eq_of_transpose_mul_eq_smul (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (c c' : Fin 4) :
    ∑ r, (al r c : ℂ) * al r c' = if c = c' then (m : ℂ) else 0 := by
  have := congrFun (congrFun hal c) c'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
  split_ifs at this ⊢ with h <;> [skip; skip] <;> exact_mod_cast (by simpa using this)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma sum_column_smul_add_tors_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (m : ℕ) (hm : 1 ≤ m) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) (c : Fin 4) :
    ∑ r, (al r c : ℂ) • (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r) = (m : ℂ) • y c + _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold _root_.GlobalTheory.SimilTheta.tors
  simp only [← Int.cast_smul_eq_zsmul ℂ, smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun r c' => ((al r c : ℂ) * al r c') • y c')]
  simp only [← Finset.sum_smul, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal]
  have h2 : ∀ x x_1, (↑(al x c) * ((↑m)⁻¹ * ↑(al x x_1)) : ℂ) = (↑m)⁻¹ * (↑(al x c) * ↑(al x x_1)) := fun _ _ => by ring
  have h3 : ∑ x, ∑ x_1, (↑(al x c) * ((↑m)⁻¹ * ↑(al x x_1)) : ℂ) • _root_.GlobalTheory.SimilTheta.lat τ (k x_1) (n x_1) = _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
    rw [Finset.sum_comm]
    simp only [h2, ← Finset.sum_smul, ← Finset.mul_sum, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal]
    simp [mul_ite, inv_mul_cancel₀ hm0]
  rw [h3]
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
private lemma intCast_zsmul_vector {g : ℕ} (α : ℤ) (v : Fin g → ℤ) :
    (fun i => (((α • v) i : ℤ) : ℂ)) = (α : ℂ) • fun i => (v i : ℂ) := by
  ext i; simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
theorem _root_.GlobalTheory.SimilTheta.aut_similitude_and_mul : ∀ (g m : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), _root_.GlobalTheory.KeyPow.charHalf g a b → τ.IsSymm → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) (c : Fin 4) (k₀ n₀ : Fin g → ℤ), (∏ r, _root_.GlobalTheory.SimilTheta.aut τ a b (al r c • k₀) (al r c • n₀) (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r)) * Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ _root_.GlobalTheory.SimilTheta.lat τ k₀ n₀)) = _root_.GlobalTheory.SimilTheta.aut τ a b k₀ n₀ (y c) ^ m) ∧ ∀ (k₀ n₀ : Fin g → ℤ) (z : Fin g → ℂ), _root_.GlobalTheory.SimilTheta.aut τ a b ((m : ℤ) • k₀) ((m : ℤ) • n₀) ((m : ℤ) • z) = _root_.GlobalTheory.SimilTheta.aut τ a b k₀ n₀ z ^ (m ^ 2) := by
  intro g m τ a b al hab hτ hm hal
  refine ⟨fun k n y c k₀ n₀ => ?_, fun k₀ n₀ z => ?_⟩
  · obtain ⟨s, hs⟩ := exists_column_sum_eq_add_two_mul m al hal c
    obtain ⟨ta, hta⟩ := exists_int_two_mul_dotProduct_of_half_integral a hab.1 k₀
    obtain ⟨tb, htb⟩ := exists_int_two_mul_dotProduct_of_half_integral b hab.2 n₀
    have hV := sum_column_smul_add_tors_eq τ m hm al hal k n y c
    unfold _root_.GlobalTheory.SimilTheta.aut
    simp only [intCast_zsmul_vector, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]
    rw [← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    set K₀ : Fin g → ℂ := fun i => (k₀ i : ℂ)
    set N₀ : Fin g → ℂ := fun i => (n₀ i : ℂ)
    set Kc : Fin g → ℂ := fun i => (k c i : ℂ)
    set Nc : Fin g → ℂ := fun i => (n c i : ℂ)
    have hterm : ∀ x, (2 * ↑Real.pi * Complex.I *
            (((↑(al x c) * a ⬝ᵥ K₀) - ↑(al x c) * b ⬝ᵥ N₀) -
                ↑(al x c) * (↑(al x c) * N₀ ⬝ᵥ τ *ᵥ N₀) / 2 -
              ↑(al x c) * N₀ ⬝ᵥ (∑ c', al x c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n x)) : ℂ) =
        2 * ↑Real.pi * Complex.I * ((al x c : ℂ) * (a ⬝ᵥ K₀ - b ⬝ᵥ N₀) - (al x c : ℂ) * al x c * (N₀ ⬝ᵥ τ *ᵥ N₀ / 2)
          - N₀ ⬝ᵥ ((al x c : ℂ) • (∑ c', al x c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n x))) := by
      intro x
      rw [dotProduct_smul, smul_eq_mul]
      ring
    simp only [hterm]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      ← dotProduct_sum, hV, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal c c, if_pos rfl]
    have hs' : ∑ x, (al x c : ℂ) = m + 2 * s := by exact_mod_cast hs
    rw [hs']
    have hsym : Nc ⬝ᵥ τ *ᵥ N₀ = N₀ ⬝ᵥ τ *ᵥ Nc := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hτ.eq, dotProduct_comm]
    have hNK : Nc ⬝ᵥ K₀ = ((n c ⬝ᵥ k₀ : ℤ) : ℂ) := by simp [Nc, K₀, dotProduct]
    have hNK' : N₀ ⬝ᵥ Kc = ((n₀ ⬝ᵥ k c : ℤ) : ℂ) := by simp [N₀, Kc, dotProduct]
    unfold _root_.GlobalTheory.SimilTheta.lat
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    refine ⟨s * (ta - tb) + (n c ⬝ᵥ k₀ - n₀ ⬝ᵥ k c), ?_⟩
    push_cast
    rw [← hNK, ← hNK', ← hta, ← htb]
    linear_combination (2 * ↑Real.pi * Complex.I) * hsym
  · obtain ⟨ta, hta⟩ := exists_int_two_mul_dotProduct_of_half_integral a hab.1 k₀
    obtain ⟨tb, htb⟩ := exists_int_two_mul_dotProduct_of_half_integral b hab.2 n₀
    unfold _root_.GlobalTheory.SimilTheta.aut
    simp only [intCast_zsmul_vector, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]
    rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    obtain ⟨u, hu⟩ := Int.even_mul_pred_self (m : ℤ)
    have hmu : (m : ℂ) * (m - 1) = u + u := by exact_mod_cast hu
    refine ⟨-u * (ta - tb), ?_⟩
    simp only [zsmul_eq_mul, Int.cast_natCast]
    push_cast
    rw [← hta, ← htb]
    linear_combination (-(2 * ↑Real.pi * Complex.I) * ((a ⬝ᵥ fun i ↦ (k₀ i : ℂ)) - b ⬝ᵥ fun i ↦ (n₀ i : ℂ))) * hmu

end GlobalTheory.SimilTheta
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta.Frame
open Matrix

private lemma add_lat_eq_add_mulVec_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k n : Fin g → ℤ)
    (z : Fin g → ℂ) :
    z + lat τ k n = z + τ *ᵥ ReciprocityTheory.PTheta.ofIntVec n + ReciprocityTheory.PTheta.ofIntVec k := by
  have hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ) := rfl
  have hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ) := rfl
  rw [hk, hn, lat]
  abel

private lemma autFactor_re_eq_aut_of_half_characteristics {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
    (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (k n : Fin g → ℤ) (z : Fin g → ℂ) :
    ReciprocityTheory.PTheta.autFactor (fun i => (a i).re) (fun i => (b i).re) τ n k z =
      aut τ a b k n z := by
  rw [ReciprocityTheory.PTheta.autFactor, TorusAlg.ofRealVec_re ha, TorusAlg.ofRealVec_re hb]
  have hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ) := rfl
  have hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ) := rfl
  simp only [aut, ReciprocityTheory.PTheta.eC, hk, hn, ← Complex.exp_add]
  congr 1
  ring

theorem thetaChar_law {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (hab : charHalf g a b) :
    Differentiable ℂ (thetaChar τ a b) ∧ thetaChar τ a b ≠ 0 ∧
      ∀ k n z, thetaChar τ a b (z + lat τ k n) = aut τ a b k n z * thetaChar τ a b z := by
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨hne, hspan, -⟩ := TorusAlg.thetaChar_level hs hp ha hb
  have hmem : thetaChar τ a b ∈
      thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self _
  rw [mem_thetaLevelChar_iff_autFactor] at hmem
  refine ⟨hmem.1, hne, fun k n z => ?_⟩
  have hper := hmem.2 n k z
  rw [pow_one] at hper
  rw [add_lat_eq_add_mulVec_add, hper, autFactor_re_eq_aut_of_half_characteristics ha hb]

theorem eq_zero_of_mul_eq_zero {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hD : ContinuousOn D S) (h : ∀ w ∈ S, θ w * D w = 0)
    {z : Fin g → ℂ} (hz : z ∈ S) : D z = 0 := by
  by_contra hDz
  have hθa : AnalyticOnNhd ℂ θ Set.univ :=
    SCV.analyticOnNhd_of_differentiableOn isOpen_univ hθ.differentiableOn
  have hin : ∀ᶠ w in nhds z, w ∈ S := hS.mem_nhds hz
  have hnear : ∀ᶠ w in nhds z, w ∈ S ∧ D w ≠ 0 :=
    hin.and ((hD.continuousAt (hS.mem_nhds hz)).eventually_ne hDz)
  have hθz : θ =ᶠ[nhds z] 0 := by
    filter_upwards [hnear] with w hw
    rcases mul_eq_zero.1 (h w hw.1) with h' | h'
    · exact h'
    · exact absurd h' hw.2
  have hall := hθa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) hθz
  exact h0 (funext fun w => hall (Set.mem_univ w))

theorem frame_eq_aut_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), charHalf g a b → Wit x h u τ a b → ∀ (k n : Fin g → ℤ) (i : x.P.L.ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = aut τ a b k n z * u.fr i (z + lat τ k n) := by
  intro g x h u τ a b hab hw k n i z hz
  obtain ⟨hs, hp, hΛ, -, hth, -⟩ := hw
  have hlaw := thetaChar_law hs hp hab
  obtain ⟨ha, hb⟩ := hab
  have hlatΛ : lat τ k n ∈ u.Λ := (hΛ _).2 ⟨k, n, rfl⟩
  have hex : ∀ w, u.ex (w + lat τ k n) = u.ex w := fun w =>
    CubeValues.ex_add_period u w _ hlatΛ
  let S : Set (Fin g → ℂ) := {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i}
  have hSo : IsOpen S := (u.hol (x.P.L.U i) 0).1
  have hfr : ContinuousOn (u.fr i) S := (u.fr_hol i).continuousOn
  have hfr' : ContinuousOn (fun w => u.fr i (w + lat τ k n)) S := by
    refine hfr.comp (continuous_id.add continuous_const).continuousOn fun w hw => ?_
    show ⊤ ≤ (u.ex (w + lat τ k n)).left ⁻¹ᵁ x.P.L.U i
    rw [hex]
    exact hw
  have haut : Continuous fun w => aut τ a b k n w := by
    unfold aut
    simp only [dotProduct]
    fun_prop
  have hD : ContinuousOn (fun w => u.fr i w - aut τ a b k n w * u.fr i (w + lat τ k n)) S :=
    hfr.sub (haut.continuousOn.mul hfr')
  refine sub_eq_zero.1 (eq_zero_of_mul_eq_zero hlaw.1 hlaw.2.1 hSo hD (fun w hwS => ?_) hz)
  by_cases hθ : thetaChar τ a b w = 0
  · rw [hθ, zero_mul]
  · have hf := TorusAlg.frame_eq_autFactor_mul u x.th hs ha hb hΛ hth n k i w hwS hθ
    rw [autFactor_re_eq_aut_of_half_characteristics ha hb, ← add_lat_eq_add_mulVec_add] at hf
    rw [← hf, sub_self, mul_zero]

end GlobalTheory.SimilTheta.Frame
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kTriv_boxLB_powObj : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (j : ℕ),
    Out.KTriv (Out.powObj P.A j) (Out.boxLB P.L (Out.powPr P.A (n := j))) := by
  intro R _ P j
  have : IsCommMonObj P.A := P.isAb.comm
  exact T.kTriv_external_tensor_power_lineBundle _ (Out.powObj P.A j) P.A j (Out.powIsPowGrp P.A j) P.L P.isLB P.ktriv

end GlobalTheory
end
