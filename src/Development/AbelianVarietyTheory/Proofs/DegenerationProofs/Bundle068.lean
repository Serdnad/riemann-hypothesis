module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsIntegralMulPowOfSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle043
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.PsiForm

open ReciprocityTheory.ChartRestriction.G.DVR

variable {V : Type} [CommRing V] [IsDomain V]

theorem hasVal_valF {ϖ : V} [IsDiscreteValuationRing V] {X : Scheme.{0}} (L : LB X)
    (x : Spec (CommRingCat.of V) ⟶ X) (x' : Spec (CommRingCat.of (FractionRing V)) ⟶ X) (hx : x' = jK V ≫ x)
    (ε : ℤ) (t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε))) {n : ℤ}
    (hn : GenHasVal ϖ L (fun _ => x) (fun _ => x') (fun _ => hx) (fun _ => ε) t n)
    (j : PUnit → L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit)) :
    HasVal ϖ (valF (𝟙 (Sp (FractionRing V))) _ (t.s j).val) n := by
  subst hx
  have htop : LB.wchart L (fun _ : PUnit => x) j = ⊤ :=
    eq_top_iff.2 fun y hy => Set.mem_iInter.2 fun _ => hj hy
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤ LB.wchart L (fun _ : PUnit => jK V ≫ x) j :=
    fun y _ => by
      have hy : (jK V).base y ∈ LB.wchart L (fun _ : PUnit => x) j := by rw [htop]; trivial
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  obtain ⟨c, hc, eV, hce⟩ := genHasVal_top L (fun _ : PUnit => x) (fun _ => ε) t hn j htop hK
  have e : valF (𝟙 (Sp (FractionRing V))) _ (t.s j).val = c * algebraMap V (FractionRing V) (eV : V) := by
    rw [← hce]
    exact (dif_pos hK).trans rfl
  rw [e]
  exact hasVal_mul_unit hc eV

variable {F : Type} [NormedField F] [Algebra (FractionRing V) F]
  (hle : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))

omit [IsDomain V] in
include hle in
theorem norm_unit (w : Vˣ) : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V))‖ = 1 := by
  have h1 := (hle _).2 ⟨(w : V), rfl⟩
  have h2 := (hle _).2 ⟨((w⁻¹ : Vˣ) : V), rfl⟩
  have h3 : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V))‖ *
      ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_pos_of_irreducible {ϖ : V} (hϖ : Irreducible ϖ) :
    0 < ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ :=
  norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero))

include hle in
theorem norm_lt_one_of_irreducible {ϖ : V} (hϖ : Irreducible ϖ) :
    ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ < 1 := by
  by_contra h
  have h0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  obtain ⟨w, hw⟩ := (hle (algebraMap V (FractionRing V) ϖ)⁻¹).1 (by
    rw [map_inv₀, norm_inv]
    exact inv_le_one_of_one_le₀ (not_lt.1 h))
  refine hϖ.not_isUnit (IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_))
  rw [map_mul, hw, mul_inv_cancel₀ h0, map_one]

include hle in
theorem norm_of_hasVal {ϖ : V} (hϖ : Irreducible ϖ) {c : FractionRing V} {n : ℤ} (hc : HasVal ϖ c n) :
    ‖algebraMap (FractionRing V) F c‖ =
      Real.exp (-(-Real.log ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ * n)) := by
  obtain ⟨w, rfl⟩ := hc
  rw [map_mul, norm_mul, norm_unit hle, _root_.mul_one, map_zpow₀, norm_zpow, neg_mul, neg_neg,
    ← Real.rpow_def_of_pos (norm_pos_of_irreducible hϖ), Real.rpow_intCast]

theorem tendsto_val [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) :
    Filter.Tendsto Q Filter.cofinite Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => Filter.eventually_cofinite.2 ((D.psi_tendsto b.toNat).subset fun χ hχ hin => hχ ?_)
  exact (Int.self_le_toNat b).trans (genHasVal_ge_of_in hϖ D.toPre.P.L D.toPre.P.isLB (D.toPre.c χ).left (D.toPre.xK χ)
    (QForm.ptK_eq D.toPre χ) (-1) (D.toPre.psi χ) b.toNat hin (hQ χ))

theorem exists_quadraticMap [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) (a : ℝ) :
    ∃ q : QuadraticMap ℤ D.toPre.X ℝ, ∀ χ, q χ = a * Q χ := by
  have h0 := QForm.Q_zero hϖ D hQ
  have hd : HasConstSecondDiff fun χ => a * (Q χ : ℝ) := by
    refine (hasConstSecondDiff_iff _).2 fun b m ν => ?_
    have h := QForm.bOf_add_left hϖ D hQ b m ν
    simp only [QForm.bOf] at h
    have h' : Q (b + m + ν) - Q (b + m) - Q (b + ν) + Q b = Q (m + ν) - Q m - Q ν + Q 0 := by rw [h0]; linarith
    have h'' := congrArg (fun z : ℤ => a * (z : ℝ)) h'
    push_cast at h''
    linarith
  refine ⟨hd.quadraticMap fun χ => by rw [QForm.Q_neg hϖ D hQ], fun χ => ?_⟩
  change a * (Q χ : ℝ) - a * (Q 0 : ℝ) = a * (Q χ : ℝ)
  simp [h0]

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ q : QuadraticMap ℤ u.D.toPre.X ℝ, Filter.Tendsto q Filter.cofinite Filter.atTop ∧ ∀ χ, u.PsiNorm χ (Real.exp (-q χ)) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using QForm.exists_QVal hϖ u.D
  obtain ⟨q, hq⟩ := exists_quadraticMap hϖ u.D hQ
    (-Real.log ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖)
  refine ⟨q, ?_, fun χ j hj => ?_⟩
  · refine Filter.Tendsto.congr (fun χ => (hq χ).symm) (Filter.Tendsto.const_mul_atTop ?_ ?_)
    · exact neg_pos.2 (Real.log_neg (norm_pos_of_irreducible hϖ) (norm_lt_one_of_irreducible u.norm_le hϖ))
    · exact tendsto_intCast_atTop_atTop.comp (tendsto_val hϖ u.D hQ)
  · rw [hq]
    exact norm_of_hasVal u.norm_le hϖ (hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) j hj)

end GlobalTheory.ZH.PsiForm
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem exists_mul_isIntegral_chart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type} (t : J → Ω)
    {i : J} (hi : t i ≠ 0)
    (hfin : Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω)
    (x : Ω) : ∃ a ∈ Algebra.adjoin o (Set.range fun j => t j / t i), a ≠ 0 ∧
      IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) (a * x) := by
  set A := Algebra.adjoin o (Set.range fun j => t j / t i) with hA
  set K := Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) with hKdef
  have hK : K ≤ Subfield.closure (A : Set Ω) := by
    refine Subfield.closure_le.mpr ?_
    rintro x (⟨a, rfl⟩ | ⟨k, j, rfl⟩)
    · exact Subfield.subset_closure (A.algebraMap_mem a)
    · have : t j / t k = (t j / t i) / (t k / t i) := by
        rw [div_div_div_cancel_right₀ hi]
      rw [this]
      exact div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩))
        (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))
  have hAK : ∀ y ∈ A, y ∈ K := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩)
    | algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  letI : Algebra A K := (A.val.toRingHom.codRestrict K fun y => hAK y y.2).toAlgebra
  haveI : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).2 fun a b h =>
    Subtype.ext (congrArg (fun c : K => (c : Ω)) h)
  haveI : IsFractionRing A K := by
    refine IsFractionRing.of_field _ _ fun c => ?_
    obtain ⟨y, hy, w, hw, hc⟩ := Subfield.mem_closure_iff.mp (hK c.2)
    have hAA : Subring.closure (A : Set Ω) = A.toSubring := Subring.closure_eq A.toSubring
    rw [hAA] at hy hw
    exact ⟨⟨y, hy⟩, ⟨w, hw⟩, Subtype.ext hc.symm⟩
  have h1 : IsAlgebraic A x := (IsFractionRing.isAlgebraic_iff A K Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨a, ha, h⟩ := h1.exists_integral_multiple
  exact ⟨a, a.2, fun h0 => ha (Subtype.ext h0), h⟩

theorem exists_isNm_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsDedekindDomain o] [CharZero Ω], Function.Injective (algebraMap o Ω) → ∀ (J : Type) [Fintype J] (t : J → Ω), (∃ i, t i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω → ∃ M : RatModel o Ω, M.IsNm t ∧ IsProjOver M.s := by
  intro o Ω _ _ _ _ _ hinj J _ t ht hfin
  obtain ⟨e, n, z, he, hk, hint, hsum⟩ := GlobalTheory.exists_tuple_normalisation_charts o Ω hinj J t ht hfin
  obtain ⟨i, hi⟩ := ht
  obtain ⟨k, hzk⟩ := hk i
  have hL : ∀ y ∈ Algebra.adjoin o (Set.range fun l => z l / t i ^ e),
      y ∈ Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = z j / z i}) := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Subfield.subset_closure (Or.inr ⟨k, j, by rw [hzk]⟩)
    | algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  obtain ⟨M, hM, hP⟩ := GlobalTheory.T.exists_projectiveClosure_isProjOver o Ω n z ⟨k, by rw [hzk]; exact pow_ne_zero _ hi⟩ (by
    refine top_unique fun x _ => ?_
    obtain ⟨a, ha, ha0, h⟩ := exists_mul_isIntegral_chart t hi hfin x
    have h1 := hL _ ((hint i hi _).2 h)
    have h2 := hL _ ((hint i hi a).2 (isIntegral_algebraMap
      (R := Algebra.adjoin o (Set.range fun j => t j / t i)) (x := ⟨a, ha⟩)))
    have h3 := div_mem h1 h2
    rwa [mul_div_cancel_left₀ _ ha0] at h3)
  exact ⟨M, isNm_of_isCl_veronese o Ω M J t e n z he hM hk hint hsum, hP⟩

end GlobalTheory.ZH
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.Nest
variable {O : Type} [CommRing O] (N : NumD O)

theorem wQ_nest {n k l : ℕ} (hk : Odd k) (hl : Odd l) (e : l = n * (k * n)) (p'' : N.QT l) (p : N.QT k)
    (hy : p''.1.1 = p.1.1 ^ n) (hg : p.1.2 = p''.1.2 ^ n) :
    N.wQ p * mulq N.θ N.σ n p''.1.2.b ^ k = N.wQ p'' := by
  subst e
  have hb : p.1.2.b = p''.1.2.b ^ n := by rw [hg, NumD.Gt.pow_b]
  have hc : N.c p.1.1.toAdd = p''.1.2.b ^ (k * n) := by
    rw [← N.QT_pow_b p, hb, ← pow_mul']
  have hy' : p''.1.1.toAdd = n • p.1.1.toAdd := by rw [hy, toAdd_pow]
  obtain ⟨hA, hB⟩ := (SymLift.wQ_iff N hk p (N.wQ p)).mp rfl
  refine (SymLift.wQ_iff N hl p'' _).mpr ⟨?_, ?_⟩
  · simp only [NumD.tk, hg, NumD.Gt.pow_b] at hA
    have ps := NumD.Gt.pow_s p''.1.2 n p.1.1.toAdd
    have ss := PsiQuadratic.s_nsmul N p''.1.2 n p.1.1.toAdd
    have db := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB n 0 p''.1.2.b p''.1.2.b).2.2.1
    have cm1 := CubeBalance.cubN_mul N.cub n (k * n) p''.1.2.b p''.1.2.b
    have cm2 := CubeBalance.cubN_mul N.cub k n p''.1.2.b p''.1.2.b
    have sw := CubeBalance.cubN_swap N.cub k n (p''.1.2.b ^ n) p''.1.2.b
    rw [hc] at ps ss
    rw [← pow_mul'] at sw
    simp only [NumD.tk]
    rw [hy']
    apply Additive.ofMul.injective
    replace hA := congrArg Additive.ofMul hA
    replace ps := congrArg Additive.ofMul ps
    replace ss := congrArg Additive.ofMul ss
    replace db := congrArg Additive.ofMul db
    replace cm1 := congrArg Additive.ofMul cm1
    replace cm2 := congrArg Additive.ofMul cm2
    replace sw := congrArg Additive.ofMul sw
    simp only [ofMul_mul, ofMul_pow] at hA ps ss db cm1 cm2 sw ⊢
    linear_combination (norm := module) hA - (k : ℤ) • db + sw + ps - ss - cm1 - (n : ℤ) • cm2
  · rw [hb] at hB
    have hψ := PsiQuadratic.ψ_nsmul N n p.1.1.toAdd
    have hm1 := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB n (k * n) p''.1.2.b p''.1.2.b).1
    have hm2 := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k n p''.1.2.b p''.1.2.b).1
    rw [hc] at hψ
    rw [hy']
    apply Additive.ofMul.injective
    replace hB := congrArg Additive.ofMul hB
    replace hψ := congrArg Additive.ofMul hψ
    replace hm1 := congrArg Additive.ofMul hm1
    replace hm2 := congrArg Additive.ofMul hm2
    simp only [ofMul_mul, ofMul_pow] at hB hψ hm1 hm2 ⊢
    linear_combination (norm := module)
      ((n : ℤ) ^ 2) • hB - hψ - hm1 - ((n : ℤ) ^ 2) • hm2

theorem txT_nest : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n m : ℕ), Odd n → Odd m → ∀ (p'' : N.QT ((n * m) ^ 2)) (p : N.QT (m ^ 2)), p''.1.1 = p.1.1 ^ n → p.1.2 = p''.1.2 ^ n → ∀ χ, N.txT (n * m) p'' χ = N.txT m p χ := by
  intro O _ N n m hn hm p'' p hy hg χ
  have hw := wQ_nest N hm.pow (hn.mul hm).pow (by ring) p'' p hy hg
  have hq := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m n p''.1.2.b p''.1.2.b).1
  rw [mul_comm m n] at hq
  have hb : p.1.2.b = p''.1.2.b ^ n := by rw [hg, NumD.Gt.pow_b]
  have hu : N.wQ p'' / mulq N.θ N.σ (n * m) p''.1.2.b = N.wQ p / mulq N.θ N.σ m p.1.2.b := by
    rw [← hw, hq, hb, mul_div_mul_right_eq_div]
  simp only [NumD.txT]
  rw [hu, hg, ← pow_mul]

end GlobalTheory.Ex.Nest
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero_eq_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val _ _ _ τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

def chartPullH {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) :
    ChartPull (Φ.H 1) (LB.LinComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ))) (𝟙 _) :=
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l _ hy => Set.mem_iInter.2 fun _ => c.le l hy
  { idx := fun l _ => c.idx l
    le := le
    g := fun y l l' hl hl' => by
      refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) (𝟙 _) y _ _
        (le l hl) (le l' hl')).symm
      have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hl hl'
      have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hl, hl'⟩ (Φ.N₀.g l l')
      refine (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).trans (Eq.symm ?_)
      refine Eq.trans ?_ (map_pow _ _ _).symm
      refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
      rw [Category.assoc]
      rfl }

theorem trF_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (q : Y' ⟶ Y) (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (j j' : K → L.ι) :
    trF (fun a => q ≫ ψ a) ε r z j j' = trF ψ ε (r ≫ q) z j j' := by
  simp only [trF, Category.assoc]

theorem exists_red_of_pure : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ b : LB.Sec (LB.LinComb L ψ ε), UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF α hw φ hp
  have := Φ.D.q_hom
  have := Φ.D.q_flat
  have := Φ.D.q_surjective
  obtain ⟨s, hs⟩ := exists_sec_of_refine _ _ _ (Φ.H_isLB 1) (DVR.linComb_isLB L hL _ _) (chartPullH Φ c) φ
  have hF' : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ Φ.D.q.left ≫ π) φt)
      (Sum.elim (fun _ => (N : ℤ)) (fun a => - εt a)) (fun a => Φ.D.q.left ≫ ψ a) ε := by
    intro U _ h
    have e := hF U h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_neg,
      Finset.prod_inv_distrib] at e ⊢
    rw [← e, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF' (pullMulSec s (𝟙 _) (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have vσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
      r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
      gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval σ r z J * (val t r z J).val := by
    intro Z r z J hJ l hl e
    rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, val_inv, Category.comp_id, Units.inv_mul_cancel_right,
      sval_of s r z J (fun _ => c.idx l) (fun _ => e)]
    exact hs l Z r z hl
  have le : ∀ j : K → L.ι, Φ.D.q.left ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j :=
    fun j y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Φ.E.B.left, LB.wchart L ψ j),
      (Φ.D.q.left.app _).hom a = (Φ.G.left.presheaf.map (homOfLE (le j)).op).hom (σ.f j) := by
    intro j
    refine exists_app_eq_of_hasWt_zero k Φ.E Φ.G Φ.D _ _ fun Z τ g z hz => ?_
    have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
      congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
    have hz' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left (g.left z))
    have hl' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hl
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hl)
    have hwt : HasWt Φ.D.i _ (φ.f l) α :=
      (PureWt.hasWt_iff_weight k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).2 fun χ hne => by
        by_contra h
        exact hne (hp ⟨l, h⟩)
    have h₀ := hwt Z τ g z hl
    have h₁ := vσ _ g.left z J hJ l hl (e ())
    have h₂ := vσ _ ((τ ≫ Φ.D.i) * g).left z J hJ l hl' (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
    have h₃ : sval σ ((τ ≫ Φ.D.i) * g).left z J = sval σ g.left z J := by
      have h₄ := h₂.symm.trans (h₀.trans (congrArg _ h₁))
      rw [hw Z τ g z J hJ, mul_left_comm, ← Units.val_mul] at h₄
      exact (Units.mul_left_inj _).1 h₄
    rw [gm_charUnit_zero_eq_one, Units.val_one, _root_.one_mul]
    refine (gs_res _ z (le j) hz' _).trans (Eq.trans ?_ (gs_res _ z (le j) hz _).symm)
    refine (sec_trans σ _ z (le j hz') (hJ.mem _ _)).trans (Eq.trans ?_ (sec_trans σ _ z (le j hz) (hJ.mem _ _)).symm)
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) h₃
    simp only [trF_comp, ← Category.assoc, hq]
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z), Φ.D.q.left (r z) ∈ LB.wchart L ψ j →
      gs (r ≫ Φ.D.q.left) z (LB.wchart L ψ j) (a j) =
        gs r z (LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j) (σ.f j) := fun j Z r z hz =>
    (gs_pull r _ z _ hz _).symm.trans ((congrArg (gs r z _) (ha j)).trans (gs_res r z (le j) hz _))
  refine ⟨⟨a, fun j j' => FunDescent.app_injective Φ.D.q.left (LB.wchart L ψ j ⊓ LB.wchart L ψ j')
    (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ l hl e => ?_⟩
  · have hy' : Φ.D.q.left y ∈ LB.wchart L ψ j ⊓ LB.wchart L ψ j' := hy
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).symm)
    refine ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (sec_trans σ (𝟙 _) y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (gs_mul (𝟙 _ ≫ Φ.D.q.left) y _ hy' _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (congrArg Units.val
        ((gm_linComb L ψ ε (𝟙 _ ≫ Φ.D.q.left) y j j' hy'.1 hy'.2).trans (trF_comp _ _ _ _ _ _ _).symm)))
      ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  · refine (vσ Z r z J hJ l hl e).trans (congrArg₂ (· * ·) (Eq.symm ?_) rfl)
    rw [sval_of _ (r ≫ Φ.D.q.left) z J (fun a => J (r ≫ Φ.D.q.left ≫ ψ a)) (fun a => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun a => hJ (r ≫ Φ.D.q.left ≫ ψ a))

end GlobalTheory.ZH.UFib
end
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.homogeneousCoordinates_mulVec_of_genericValue : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N N' : RatModel o Ω') (a : N'.Z ⟶ N.Z) (q : N'.Z ⟶ M.Z) (W : M.Z.Opens) (H : LB N.Z) (d : H.ι → Ω') (J : Type) [Fintype J] (st : J → H.Sec) (σ : J → (H.pull a).Sec) (t u : J → Ω') (c : Matrix J J Γ(M.Z, W)), N.IsHom N' (AlgHom.id o Ω') a → M.IsHom N' φ q → (∀ z, q z ∈ W) → (∀ j, N.HasVal d (st j) (t j)) → (∀ j, N'.HasVal (H := H.pull a) (fun k => d (k PUnit.unit)) (σ j) (u j)) → t = (c.map fun g => φ (valF M.pt W g)).mulVec u → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ N'.Z) (w : J → R), Crd (H.pull a) σ x w → Crd H st (x ≫ a) ((c.map (valR (x ≫ q) W)).mulVec w) := by
  first | exact @GlobalTheory.ZH.RatModel.crd_mulVec_of_hasVal | exact GlobalTheory.ZH.RatModel.crd_mulVec_of_hasVal | (intros; apply GlobalTheory.ZH.RatModel.crd_mulVec_of_hasVal <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.isClosedImmersion_of_coordinate_divisibility : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  first | exact @GlobalTheory.ZH.RatModel.immBy_of_div | exact GlobalTheory.ZH.RatModel.immBy_of_div | (intros; apply GlobalTheory.ZH.RatModel.immBy_of_div <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.exists_isLB_genTriv_of_ratios' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | exact GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | (intros; apply GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

theorem _root_.GlobalTheory.T.genericTrivialisation_section_and_pullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω), M.GenTriv H d → (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧ ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z), M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  first | exact @GlobalTheory.ZH.RatModel.genTriv_sec_and_pull | exact GlobalTheory.ZH.RatModel.genTriv_sec_and_pull | (intros; apply GlobalTheory.ZH.RatModel.genTriv_sec_and_pull <;> assumption)
end
