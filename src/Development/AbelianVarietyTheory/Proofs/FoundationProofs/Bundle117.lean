module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle096
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralBasisOfIntegralAlgebraicElements
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReparametrizationByTowerParameter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle098
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle100
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009

@[expose] public section

section

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.NormDelta

def conjM (γ : SL(2, ℤ)) (l : ℕ) (j k B : ℤ) (hB : (l : ℤ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) : SL(2, ℤ) :=
  ⟨!![γ 0 0 + j * γ 1 0, B; l * γ 1 0, γ 1 1 - k * γ 1 0], by
    have hd := γ.2
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 at hd
    linear_combination hd - γ 1 0 * hB⟩

open scoped MatrixGroups in
private lemma toGQ_mul_ofSL_eq_ofSL_mul_toGQ (γ γ' : SL(2, ℤ)) (l : ℕ) (hl : 0 < l) (j k B : ℤ)
    (hB : (l : ℤ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0))
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 0 0 + j * γ 1 0, B; l * γ 1 0, γ 1 1 - k * γ 1 0]) :
    _root_.GlobalTheory.KZ.toGQ !![1, j; 0, (l : ℤ)] * _root_.GlobalTheory.KZ.ofSL γ =
      _root_.GlobalTheory.KZ.ofSL γ' * _root_.GlobalTheory.KZ.toGQ !![1, k; 0, (l : ℤ)] := by
  have hdet : ∀ m : ℤ, 0 < (!![1, m; 0, (l : ℤ)]).det := by
    intro m
    simp only [Matrix.det_fin_two_of, one_mul, mul_zero, sub_zero]
    exact_mod_cast hl
  unfold _root_.GlobalTheory.KZ.toGQ _root_.GlobalTheory.KZ.ofSL
  rw [dite_eq_left (hdet j), dite_eq_left (hdet k)]
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i i'
  have h00 := congrFun (congrFun hγ' 0) 0
  have h01 := congrFun (congrFun hγ' 0) 1
  have h10 := congrFun (congrFun hγ' 1) 0
  have h11 := congrFun (congrFun hγ' 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at h00 h01 h10 h11
  have hBq : ((l : ℚ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) := by exact_mod_cast hB
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.toGLPos,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, h00, h01, h10, h11] <;>
    first | ring1 | linear_combination -hBq


open scoped MatrixGroups in
theorem _root_.GlobalTheory.NormDelta.norm_delta (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : _root_.GlobalTheory.KZ.Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ)
    (hn : 0 < n) (hlN : ¬ l ∣ N) (f : X.K) (hf : _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f)
    (hδ : ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (_root_.GlobalTheory.KZ.ofSL δ) f = g ^ (l ^ n)) :
    ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧
        (∏ j ∈ Finset.range l, X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) *
          X.sl (_root_.GlobalTheory.KZ.ofSL δ) (∏ j ∈ Finset.range l, X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) = g ^ (l ^ n) := by
  intro δ hδN hδl
  obtain ⟨g, hg, hfg⟩ := hδ δ hδN hδl
  have hlp : l.Prime := Fact.out
  have hl0 : 0 < l := hlp.pos
  refine ⟨∏ j ∈ Finset.range l,
      X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g,
    _root_.GlobalTheory.normInv_gamma1 Ω ε X N l n hn g hg, ?_⟩
  rw [CongruenceSubgroup.Gamma1_mem] at hδN
  obtain ⟨-, -, hcN⟩ := hδN
  rw [CongruenceSubgroup.Gamma_mem] at hδl
  obtain ⟨ha', hb', hc', hd'⟩ := hδl
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at ha' hb' hc' hd'
  have hlpow : ∀ x : ℤ, ((x : ZMod (l ^ n)) = 0) → (l : ℤ) ∣ x := fun x hx =>
    (dvd_pow_self (l : ℤ) hn.ne').trans (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd x (l ^ n)).1 hx)
  obtain ⟨xa, hxa⟩ := hlpow (δ 0 0 + 1) (by push_cast; linear_combination -ha')
  obtain ⟨xd, hxd⟩ := hlpow (δ 1 1 + 1) (by push_cast; linear_combination -hd')
  obtain ⟨xb, hxb⟩ := hlpow (δ 0 1) (by linear_combination -hb')
  obtain ⟨xc, hxc⟩ := hlpow (δ 1 0) (by linear_combination -hc')
  have hcop : IsCoprime (N : ℤ) ((l : ℤ) ^ n) := by
    have := Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hlp).2 hlN).symm
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  have hcM : ((δ 1 0 : ℤ) : ZMod (N * l ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    refine hcop.mul_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hcN) ?_
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 1 0) (l ^ n)).1 (by linear_combination -hc')
    exact_mod_cast this
  have hdetM : ((δ 0 0 : ℤ) : ZMod (N * l ^ n)) * (δ 1 1 : ℤ) = 1 := by
    have hdet := δ.2
    rw [Matrix.det_fin_two] at hdet
    have := congrArg (Int.cast : ℤ → ZMod (N * l ^ n)) hdet
    push_cast at this
    rw [hcM] at this
    simpa using this
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hB : (l : ℤ) * (xb + j * xd - j * xa - j * j * xc) =
      δ 0 1 + j * δ 1 1 - j * (δ 0 0 + j * δ 1 0) := by
    linear_combination -hxb - j * hxd + j * hxa + j * j * hxc
  have hη : _root_.GlobalTheory.NormDelta.conjM δ l j j _ hB * δ⁻¹ ∈ CongruenceSubgroup.Gamma1 (N * l ^ n) := by
    rw [CongruenceSubgroup.Gamma1_mem, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [_root_.GlobalTheory.NormDelta.conjM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons]
    push_cast
    rw [hcM]
    refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | linear_combination hdetM
  have hsplit : _root_.GlobalTheory.KZ.ofSL (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB) =
      _root_.GlobalTheory.KZ.ofSL (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB * δ⁻¹) *
        _root_.GlobalTheory.KZ.ofSL δ := by
    rw [← map_mul, inv_mul_cancel_right]
  have hact : X.sl (_root_.GlobalTheory.KZ.ofSL δ)
      (X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) =
      X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)])
        (X.sl (_root_.GlobalTheory.KZ.ofSL δ) f) := by
    rw [← _root_.GlobalTheory.KZ.Tower.sl_mul,
      toGQ_mul_ofSL_eq_ofSL_mul_toGQ δ (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB) l hl0 j j _ hB rfl,
      _root_.GlobalTheory.KZ.Tower.sl_mul, hsplit,
      _root_.GlobalTheory.KZ.Tower.sl_mul, hf _ hη]
  rw [hact, ← map_mul, hfg, map_pow]

end GlobalTheory.NormDelta
end
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.modularTower_rootOfInvariant_T_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ), l.Prime → l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ∀ (u : X.K), u ≠ 0 → Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)) → (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) → ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) → X.sl (ofSL ModularGroup.T) u = u := by
  first | exact @GlobalTheory.TInv.sl_T_eq | exact GlobalTheory.TInv.sl_T_eq | (intros; apply GlobalTheory.TInv.sl_T_eq <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

theorem _root_.GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (d : ℕ) (E : Fin d → Ω),
        (∀ t, IsInt (p := p) (E t) ∧ IsAlgZp (p := p) (E t)) →
        ∀ v : ℕ, ∃ (m : ℕ) (f : Fin m → Ω),
          (∀ j, IsInt (p := p) (f j) ∧ IsAlgZp (p := p) (f j)) ∧
          ∀ (l : Fin d → ℤ_[p]) (y : Ω), IsInt (p := p) y →
            (p : Ω) ^ v * y = ∑ t, zp Ω (l t) * E t →
            ∃ μ : Fin m → ℤ_[p], y = ∑ j, zp Ω (μ j) * f j := by
  intro p _ Ω _ _ hc d E hE v
  let : Algebra ℤ_[p] Ω := zpAlg (p := p) (Ω := Ω)
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hAlg (x : Ω) : IsAlgZp (p := p) x ↔ IsAlgebraic ℤ_[p] x := by
    unfold IsAlgZp IsAlgebraic
    simp only [Polynomial.aeval_map_algebraMap]
  have hsmul (c : ℤ_[p]) (x : Ω) : c • x = zp Ω c * x := by
    rw [Algebra.smul_def]
    congr 1
    change algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) c) = zp Ω c
    rw [zp, algebraMap_zp_eq, HahnSeries.C_apply]
  have hpv : ((p : Ω) ^ v) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E)
  let S' : Submodule ℤ_[p] Ω :=
    { carrier := {y | IsInt (p := p) y ∧ (p : Ω) ^ v * y ∈ S}
      add_mem' := by
        rintro x y ⟨hxInt, hxS⟩ ⟨hyInt, hyS⟩
        exact ⟨IsIntegral.add hxInt hyInt, by rw [mul_add]; exact S.add_mem hxS hyS⟩
      zero_mem' := ⟨isIntegral_zero, by simp⟩
      smul_mem' := by
        rintro c x ⟨hxInt, hxS⟩
        refine ⟨?_, ?_⟩
        · change IsIntegral (O0 p) (c • x)
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω]
          exact IsIntegral.mul isIntegral_algebraMap hxInt
        · change (p : Ω) ^ v * (c • x) ∈ S
          rw [mul_smul_comm]
          exact S.smul_mem c hxS }
  let U := Submodule.span ℤ_[p] (Set.range fun t => E t / (p : Ω) ^ v)
  have hle : S' ≤ U := by
    rintro y ⟨_, hy⟩
    change (p : Ω) ^ v * y ∈ Submodule.span ℤ_[p] (Set.range E) at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hy
    apply (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).2
    refine ⟨c, ?_⟩
    calc
      ∑ t, c t • (E t / (p : Ω) ^ v) = (∑ t, c t • E t) / (p : Ω) ^ v := by
        simp only [Finset.sum_div, smul_div_assoc]
      _ = y := (div_eq_iff hpv).2 (hc.trans (mul_comm _ _))
  have hnoeth : IsNoetherian ℤ_[p] U :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  have hfg : S'.FG := isNoetherian_submodule.1 hnoeth S' hle
  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hfmem (j : Fin m) : IsInt (p := p) (f j) ∧ (p : Ω) ^ v * f j ∈ S := by
    change f j ∈ S'
    rw [← hf]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hAlgS : ∀ x ∈ S, IsAlgebraic ℤ_[p] x := by
    intro x hx
    change x ∈ Submodule.span ℤ_[p] (Set.range E) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact (hAlg _).1 (hE t).2
    | zero => exact isAlgebraic_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact (isAlgebraic_algebraMap c).mul hx
  refine ⟨m, f, fun j => ⟨(hfmem j).1, ?_⟩, ?_⟩
  · apply (hAlg _).2
    have hInv : IsAlgebraic ℤ_[p] (((p : Ω) ^ v)⁻¹) :=
      ((isAlgebraic_natCast p : IsAlgebraic ℤ_[p] (p : Ω)).pow v).inv
    have h := hInv.mul (hAlgS _ (hfmem j).2)
    rwa [← mul_assoc, inv_mul_cancel₀ hpv, one_mul] at h
  · intro l y hy hyl
    have hyS : y ∈ S' := by
      refine ⟨hy, ?_⟩
      rw [hyl]
      refine S.sum_mem fun t _ => ?_
      rw [← hsmul]
      exact S.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩)
    rw [← hf] at hyS
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hyS
    exact ⟨μ, by simpa only [hsmul] using hμ.symm⟩
end

section

open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.exists_integral_basis_of_integral_algebraic_elements : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) → 0 < v (p : Ω) → v (p : Ω) < 1 → ∀ (d : ℕ) (e : Fin d → Ω), (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) → ∃ (E F : ℕ) (π : Ω) (κ : Fin F → Ω) (lam : Fin d → Fin F → Fin E → ℤ_[p]), 1 ≤ E ∧ IsAlgZp (p := p) π ∧ v π ^ E = v (p : Ω) ∧ (∀ j, IsInt (p := p) (κ j) ∧ IsAlgZp (p := p) (κ j)) ∧ (∀ μ : Fin F → ℤ_[p], (∃ j, ¬ (p : ℤ_[p]) ∣ μ j) → v (∑ j, κ j * zp Ω (μ j)) = 1) ∧ ∀ t, e t = ∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * zp Ω (lam t j s) := by
  first | exact @GlobalTheory.K5.OkBasis.okbasis | exact GlobalTheory.K5.OkBasis.okbasis | (intros; apply GlobalTheory.K5.OkBasis.okbasis <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.exists_reparametrizationByTowerParameter : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∃ ψ : O0 p →+* Ω, IsReb T n ψ := by
  first | exact @GlobalTheory.Glue.exists_isReb | exact GlobalTheory.Glue.exists_isReb | (intros; apply GlobalTheory.Glue.exists_isReb <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.isCuspFunctionalValue_galB_equivariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (s : Ω ≃ₐ[ℚ] Ω), (l : Ω) ∈ A.nonunits → (∀ x, x ∈ A ↔ s x ∈ A) → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n (X.galB l s b) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  first | exact @GlobalTheory.isThB_galB | exact GlobalTheory.isThB_galB | (intros; apply GlobalTheory.isThB_galB <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.theta_basis_linear_combination : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (b b' : X.Fn l), b ∈ X.B N l w → b' ∈ X.B N l w → ∀ (c c' : ℤ_[l]) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l n b φ → IsThB X A N l n b' φ' →
    IsThB X A N l n (c • b + c' • b') (((c.appr n : ℕ) : Ω) • φ + ((c'.appr n : ℕ) : Ω) • φ') := by
  intro Ω _ _ _ ε X A N l _ n w b b' _ _ c c' φ φ' h h'
  obtain ⟨f, hfi, hfc, hfd, hfl⟩ := h
  obtain ⟨f', hfi', hfc', hfd', hfl'⟩ := h'
  refine ⟨f ^ (c.appr n) * f' ^ (c'.appr n), ?_, ?_, ?_, ?_⟩
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact GlobalTheory.ThAdd.inv_mul (GlobalTheory.ThAdd.inv_pow hfi _) (GlobalTheory.ThAdd.inv_pow hfi' _)
  · rw [← GlobalTheory.ThAdd.cls_comb, ← hfc, ← hfc', ← map_smul, ← map_smul, ← map_add (f := _)]
    rfl
  · intro δ hδ hδ'
    obtain ⟨g, hgi, hg⟩ := hfd δ hδ hδ'
    obtain ⟨g', hgi', hg'⟩ := hfd' δ hδ hδ'
    refine ⟨g ^ (c.appr n) * g' ^ (c'.appr n), GlobalTheory.ThAdd.inv_mul (GlobalTheory.ThAdd.inv_pow hgi _) (GlobalTheory.ThAdd.inv_pow hgi' _), ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    calc (f : X.K) ^ (c.appr n) * (f' : X.K) ^ (c'.appr n) *
          (X.sl (ofSL δ) f ^ (c.appr n) * X.sl (ofSL δ) f' ^ (c'.appr n))
        = ((f : X.K) * X.sl (ofSL δ) f) ^ (c.appr n) * ((f' : X.K) * X.sl (ofSL δ) f') ^ (c'.appr n) := by ring
      _ = _ := by rw [hg, hg']; ring
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact GlobalTheory.ThAdd.isDl_mul (GlobalTheory.ThAdd.isDl_pow hfl _) (GlobalTheory.ThAdd.isDl_pow hfl' _)
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.SlPLaws
open MvPolynomial

variable {R : Type} [CommRing R]

theorem slP_X (m : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    slP (R := R) m (X i) = (m i 0 : R) • X 0 + (m i 1 : R) • X 1 := by
  simp [slP]

theorem polySlash_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP (m * m') p = slP m' (slP m p) := by
  have h : (slP (R := R) (m * m')) = (slP m').comp (slP m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, slP_X, map_add (f := _), map_smul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    simp only [smul_add, add_smul, smul_smul, mul_comm]
    abel
  rw [h]; rfl

theorem polySlash_one' (p : MvPolynomial (Fin 2) R) : slP 1 p = p := by
  have h : (slP (R := R) 1) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [h]; rfl

theorem polySlash_isHomogeneous (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R)
    (hp : p.IsHomogeneous w) : (slP m p).IsHomogeneous w := by
  have := IsHomogeneous.aeval (τ := Fin 2) (S := R) (n := 1) hp (fun i => (m i 0 : R) • X 0 + (m i 1 : R) • X 1) (fun i => by
    apply IsHomogeneous.add
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 0).C_mul _
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 1).C_mul _)
  rw [one_mul] at this
  simpa [slP] using this

theorem eval_slP (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    eval u (slP m p) = eval (m.map (Int.castRingHom R) *ᵥ u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, eval_X]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem map_slP {S : Type} [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, map_X, map_add (f := _)]
    simp [MvPolynomial.smul_eq_C_mul]

theorem polySlash_congr (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R)
    (h : ∀ i j, (m i j : R) = (m' i j : R)) : slP m p = slP m' p := by
  simp only [slP, h]

theorem polySlash_neg_one (w : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p.IsHomogeneous w) :
    slP (-1) p = (-1 : R) ^ w • p := by
  have e : (slP (R := R) (-1)) = aeval fun i => (-1 : R) • X i := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [e]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hw := hp (mem_support_iff.mp hv)
  rw [aeval_monomial]
  simp only [smul_pow, Finsupp.prod_pow]
  have hw' : v 0 + v 1 = w := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]; simp
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, ← hw']
  simp only [smul_eq_C_mul, algebraMap_eq, pow_add, map_mul, map_pow, map_neg, map_one]
  ring

end GlobalTheory.KZ.SlPLaws

namespace GlobalTheory.KZ

theorem polySlash_laws : ∀ (R : Type) [CommRing R], (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), slP (m * m') p = slP m' (slP m p)) ∧ (∀ p : MvPolynomial (Fin 2) R, slP 1 p = p) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → (slP m p).IsHomogeneous w) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R), MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p)) ∧ (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), (∀ i j, (m i j : R) = (m' i j : R)) → slP m p = slP m' p) ∧ (∀ (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → slP (-1) p = (-1 : R) ^ w • p) := by
  intro R _
  exact ⟨SlPLaws.polySlash_mul, SlPLaws.polySlash_one', SlPLaws.polySlash_isHomogeneous, SlPLaws.eval_slP, fun S _ f => SlPLaws.map_slP f,
    fun m m' p h => SlPLaws.polySlash_congr m m' p h, fun w p hp => SlPLaws.polySlash_neg_one w p hp⟩

end GlobalTheory.KZ
end

section

open GlobalTheory.Col PowerSeries

theorem _root_.GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R), normOp p (smap σ h) = smap σ (normOp p h) := by
  first | exact @GlobalTheory.Col.NormCoeff.normOp_smap | exact GlobalTheory.Col.NormCoeff.normOp_smap | (intros; apply GlobalTheory.Col.NormCoeff.normOp_smap <;> assumption)
end

section

open GlobalTheory.Col PowerSeries

theorem _root_.GlobalTheory.T.exists_colemanLevelRing_basis_one_add_X_pow : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R → ∃ b : Module.Basis (Fin (Nat.totient (p ^ m))) R (lev R p m), ∀ i, b i = ev R p m ((1 + X) ^ (i : ℕ)) := by
  first | exact @GlobalTheory.Col.lev_basis | exact GlobalTheory.Col.lev_basis | (intros; apply GlobalTheory.Col.lev_basis <;> assumption)
end

section

open GlobalTheory.Col PowerSeries

theorem _root_.GlobalTheory.T.X_mul_mem_span_of_colemanLevels : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime], IsDomain R → Prime (p : R) → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (h : PowerSeries R) (k c : ℕ), (∀ r, 1 ≤ r → r ≤ k → ∃ y : PowerSeries R, ev R p r h = ev R p r ((p : PowerSeries R) ^ c * y)) → ∀ j, j ≤ k → j ≤ c → X * h ∈ Ideal.span {(p : PowerSeries R) ^ (c - j), (1 + X) ^ (p ^ j) - 1} := by
  first | exact @GlobalTheory.Col.X_mul_mem_span_of_levels | exact GlobalTheory.Col.X_mul_mem_span_of_levels | (intros; apply GlobalTheory.Col.X_mul_mem_span_of_levels <;> assumption)
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt (p := p) (x ^ b / (p : Ω) ^ a) ∧
    IsInt (p := p) ((p : Ω) ^ a / x ^ b) := by
  intro p _ Ω _ _ hΩ x hx
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]
    exact o0_isAdicComplete_span_p p
  have : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hΩ.inj
  let _ : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  have : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
  have : Algebra.IsAlgebraic (O0 p) Ω := hΩ.alg
  have : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  have hIntegral := exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p)
    hirr x hx
  simpa only [IsInt, map_natCast] using hIntegral
end
