module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Mathlib.RepresentationTheory.Semisimple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocalLatticeRepresentationSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.SpCharpoly

theorem charpoly_blockDiag {m o R : Type*} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] [CommRing R] (B : o → Matrix m m R) :
    (Matrix.blockDiagonal B).charpoly = ∏ k, (B k).charpoly := by
  have e : Matrix.charmatrix (Matrix.blockDiagonal B) =
      Matrix.blockDiagonal (fun k => Matrix.charmatrix (B k)) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [Matrix.charpoly, e, Matrix.det_blockDiagonal]
  rfl

theorem charpoly_map_diagEnd {n m : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (c : Fin m → ℂ) :
    LinearMap.charpoly (TensorProduct.map f (diagEnd c)) = ∏ i, LinearMap.charpoly (c i • f) := by
  classical
  set b := Pi.basisFun ℂ (Fin n)
  have e : LinearMap.toMatrix (Pi.basisFun ℂ (Fin m)) (Pi.basisFun ℂ (Fin m)) (diagEnd c) =
      Matrix.diagonal c := by
    ext i j
    simp [Matrix.diagonal_apply, Pi.single_apply]
  rw [← LinearMap.charpoly_toMatrix _ (b.tensorProduct (Pi.basisFun ℂ (Fin m))),
    TensorProduct.toMatrix_map, e]
  have e2 : Matrix.kroneckerMap (· * ·) (LinearMap.toMatrix b b f) (Matrix.diagonal c) =
      Matrix.blockDiagonal fun i => LinearMap.toMatrix b b (c i • f) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply,
      map_smul, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [mul_comm]
  rw [e2, charpoly_blockDiag]
  exact Finset.prod_congr rfl fun i _ => LinearMap.charpoly_toMatrix _ _

end GlobalTheory.WeilDeligne.SpCharpoly

namespace GlobalTheory.WeilDeligne

theorem charPol_lpTw_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), (x.lpTw 0).lpChar (WD.lpSp (h := h) 1) = x ∧ ∀ (l : ℕ) (σ : Weil h), ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) l)).charPol σ = ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
  intro E Ω _ _ _ _ _ A w h x
  refine ⟨?_, fun l σ => ?_⟩
  · rw [WD.lpTw_zero]
    induction x using WD.ind with
    | hP n a =>
      rw [WD.lpSp, WD.lpChar_mk]
      refine WD.sound (WDRep.Iso.symm ⟨(TensorProduct.rid ℂ (Fin n → ℂ)).symm ≪≫ₗ
        TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm,
        fun σ v => ?_, fun v => ?_⟩)
      · have : (WDRep.sp (h := h) 1).ρ σ = 1 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [WDRep.spEig]
        rw [WDRep.tensor_ρ, this]
        simp
      · have : (WDRep.sp (h := h) 1).N = 0 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [shiftEnd_apply]
        rw [WDRep.tensor_N, this]
        simp
  · induction x using WD.ind with
    | hP n a =>
      have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
      rw [WD.lpSp, WD.lpTw_mk, WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
        SpCharpoly.charpoly_map_diagEnd]
      change _ = ∏ j ∈ Finset.range l, ((WD.mk a).lpTw (j : ℕ)).charPol σ
      rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => ((WD.mk a).lpTw (j : ℕ)).charPol σ)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.tw_ρ, smul_smul, ← mul_zpow, WDRep.spEig,
        coe_qPow, ← Complex.cpow_add _ _ hq, ← Complex.ofReal_add, sub_add_cancel]

end GlobalTheory.WeilDeligne
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_frob_pow_mul_ineIncl_mul (m : ℕ) (hm : 0 < m) (σ : Weil h) :
    ∃ (r : ℕ) (τ : Ine (F := E) A) (q : ℤ), r < m ∧
      σ = frob h ^ r * ineIncl h τ * (frob h ^ m) ^ q := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdeg : deg (σ * (frob h ^ m) ^ (-(deg σ / m))) = deg σ % m := by
    rw [deg_mul, deg_zpow, deg_pow, deg_frob, Int.emod_def]
    ring
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (σ * (frob h ^ m) ^ (-(deg σ / m)))
  have hr0 : 0 ≤ deg σ % (m : ℤ) := Int.emod_nonneg _ hm'
  have hr1 : deg σ % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  refine ⟨(deg σ % m).toNat, τ, deg σ / m, by omega, ?_⟩
  have hz : frob h ^ (deg σ % (m : ℤ)).toNat = frob h ^ (deg σ % (m : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hr0]
  rw [hz, ← hdeg, ← hτ, mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]

theorem isSemisimpleRepresentation_of_isSmooth [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ∀ σ, Module.End.IsSemisimple (ρ σ)) : ρ.IsSemisimpleRepresentation := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 < m := ⟨1, one_pos⟩
  refine ⟨fun P => ?_⟩
  have hPinv : P.toSubmodule ∈ Module.End.invtSubmodule (ρ (frob h ^ m)) := by
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    exact P.apply_mem_toSubmodule _ hv
  obtain ⟨Q, hQ, hc⟩ := (Module.End.isSemisimple_iff.mp (hss (frob h ^ m))) _ hPinv
  rw [Module.End.mem_invtSubmodule] at hQ
  let p : Module.End ℂ V := P.toSubmodule.projection Q hc
  have hp1 : ∀ v ∈ P.toSubmodule, p v = v := fun v hv => Submodule.projection_apply_left hc ⟨v, hv⟩
  have hp2 : ∀ v ∈ Q, p v = 0 := fun v hv => Submodule.projection_apply_right hc ⟨v, hv⟩
  have hpm : ∀ v, p v ∈ P.toSubmodule := fun v => Submodule.projection_apply_mem hc v
  have hpT : ρ (frob h ^ m) * p = p * ρ (frob h ^ m) := by
    ext v
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      Submodule.mem_sup.1 (show v ∈ P.toSubmodule ⊔ Q by rw [hc.sup_eq_top]; trivial)
    simp only [Module.End.mul_apply, map_add (f := _), hp1 _ hx, hp2 _ hy, add_zero,
      hp1 _ (hPinv hx), hp2 _ (hQ hy), map_zero]
  have hinv : ∀ σ : Weil h, ρ σ * ρ σ⁻¹ = 1 := fun σ => by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ∀ σ : Weil h, ρ σ⁻¹ * ρ σ = 1 := fun σ => by rw [← map_mul, inv_mul_cancel, map_one]
  let c : Weil h → Module.End ℂ V := fun σ => ρ σ * p * ρ σ⁻¹
  have hcm : ∀ σ v, c σ v ∈ P.toSubmodule := fun σ v => P.apply_mem_toSubmodule σ (hpm _)
  have hc1 : ∀ σ, ∀ v ∈ P.toSubmodule, c σ v = v := by
    intro σ v hv
    show ρ σ (p (ρ σ⁻¹ v)) = v
    rw [hp1 _ (P.apply_mem_toSubmodule _ hv), ← Module.End.mul_apply, hinv, Module.End.one_apply]
  have hper : ∀ σ, c (σ * frob h ^ m) = c σ := by
    intro σ
    simp only [c, _root_.mul_inv_rev, map_mul]
    calc ρ σ * ρ (frob h ^ m) * p * (ρ (frob h ^ m)⁻¹ * ρ σ⁻¹)
        = ρ σ * (ρ (frob h ^ m) * p * ρ (frob h ^ m)⁻¹) * ρ σ⁻¹ := by simp only [mul_assoc]
      _ = ρ σ * (p * (ρ (frob h ^ m) * ρ (frob h ^ m)⁻¹)) * ρ σ⁻¹ := by rw [hpT]; simp only [mul_assoc]
      _ = ρ σ * p * ρ σ⁻¹ := by rw [hinv, mul_one]
  have hzper : ∀ σ (q : ℤ), c (σ * (frob h ^ m) ^ q) = c σ := by
    intro σ q
    induction q using Int.induction_on with
    | zero => simp
    | succ q ih => rw [_root_.zpow_add_one, ← mul_assoc, hper, ih]
    | pred q ih =>
      rw [← ih, ← hper, mul_assoc, ← _root_.zpow_add_one]
      congr 3
      ring
  have hFfin := hρ.finite_range
  have hCfin : (Set.range c).Finite := by
    refine (((Set.finite_Iio m).prod (hFfin.prod hFfin)).image
      (fun t : ℕ × (Module.End ℂ V × Module.End ℂ V) =>
        ρ (frob h ^ t.1) * (t.2.1 * p * t.2.2) * ρ ((frob h ^ t.1)⁻¹))).subset ?_
    rintro _ ⟨σ, rfl⟩
    obtain ⟨r, τ, q, hr, rfl⟩ := exists_frob_pow_mul_ineIncl_mul m hm σ
    refine ⟨(r, ρ (ineIncl h τ), ρ (ineIncl h τ⁻¹)), ⟨hr, ⟨τ, rfl⟩, ⟨τ⁻¹, rfl⟩⟩, ?_⟩
    show _ = c _
    rw [hzper]
    simp only [c, _root_.mul_inv_rev, map_mul, map_inv, mul_assoc]
  set Cf := hCfin.toFinset with hCf
  have hCmem : ∀ x, x ∈ Cf ↔ ∃ σ, c σ = x := fun x => by simp [Cf]
  have hcard : Cf.card ≠ 0 := Finset.card_ne_zero_of_mem ((hCmem _).2 ⟨1, rfl⟩)
  let S : Module.End ℂ V := ∑ x ∈ Cf, x
  let qa : Module.End ℂ V := (Cf.card : ℂ)⁻¹ • S
  have hSm : ∀ v, S v ∈ P.toSubmodule := by
    intro v
    simp only [S]
    rw [LinearMap.sum_apply]
    refine P.toSubmodule.sum_mem fun x hx => ?_
    obtain ⟨σ, rfl⟩ := (hCmem x).1 hx
    exact hcm σ v
  have hS1 : ∀ v ∈ P.toSubmodule, S v = (Cf.card : ℂ) • v := by
    intro v hv
    simp only [S]
    rw [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    obtain ⟨σ, rfl⟩ := (hCmem x).1 hx
    exact hc1 σ v hv
  have hSeq : ∀ g : Weil h, ρ g * S = S * ρ g := by
    intro g
    have h1 : ∑ x ∈ Cf, ρ g * x * ρ g⁻¹ = ∑ x ∈ Cf, x := by
      refine Finset.sum_nbij' (fun x => ρ g * x * ρ g⁻¹) (fun x => ρ g⁻¹ * x * ρ g)
        ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨σ, rfl⟩ := (hCmem x).1 (Finset.mem_coe.1 hx)
        exact Finset.mem_coe.2 ((hCmem _).2 ⟨g * σ, by simp only [c, _root_.mul_inv_rev, map_mul, mul_assoc]⟩)
      · intro x hx
        obtain ⟨σ, rfl⟩ := (hCmem x).1 (Finset.mem_coe.1 hx)
        exact Finset.mem_coe.2 ((hCmem _).2 ⟨g⁻¹ * σ, by
          simp only [c, _root_.mul_inv_rev, map_mul, inv_inv, mul_assoc]⟩)
      · intro x _
        simp only [← mul_assoc, hinv', one_mul]
        rw [mul_assoc, hinv', mul_one]
      · intro x _
        simp only [← mul_assoc, hinv, one_mul]
        rw [mul_assoc, hinv, mul_one]
    calc ρ g * S = (∑ x ∈ Cf, ρ g * x * ρ g⁻¹) * ρ g := by
          rw [Finset.sum_mul]
          simp only [S, Finset.mul_sum, mul_assoc, hinv', mul_one]
      _ = S * ρ g := by rw [h1]
  have hqm : ∀ v, qa v ∈ P.toSubmodule := fun v => P.toSubmodule.smul_mem _ (hSm v)
  have hq1 : ∀ v ∈ P.toSubmodule, qa v = v := by
    intro v hv
    show (Cf.card : ℂ)⁻¹ • S v = v
    rw [hS1 v hv, inv_smul_smul₀ (by exact_mod_cast hcard)]
  have hqe : ∀ g v, qa (ρ g v) = ρ g (qa v) := by
    intro g v
    show (Cf.card : ℂ)⁻¹ • S (ρ g v) = ρ g ((Cf.card : ℂ)⁻¹ • S v)
    rw [map_smul, ← Module.End.mul_apply S, ← hSeq, Module.End.mul_apply]
  let q' : V →ₗ[ℂ] P.toSubmodule := qa.codRestrict P.toSubmodule hqm
  have hcompl : IsCompl P.toSubmodule (LinearMap.ker q') :=
    LinearMap.isCompl_of_proj fun x => Subtype.ext (hq1 x x.2)
  refine ⟨⟨LinearMap.ker q', fun g v hv => ?_⟩, ?_⟩
  · have h0 : qa v = 0 := congrArg Subtype.val hv
    apply Subtype.ext
    show qa (ρ g v) = 0
    rw [hqe, h0, map_zero]
  · rw [isCompl_iff, disjoint_iff, codisjoint_iff,
      ← Subrepresentation.toSubmodule_injective.eq_iff,
      ← Subrepresentation.toSubmodule_injective.eq_iff]
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl
    exact hcompl

end GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.WDRep

theorem isSemisimpleRepresentation_rho : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (n : ℕ) (a : WDRep h (Fin n → ℂ)), a.ρ.IsSemisimpleRepresentation := by
  intro E Ω _ _ _ _ _ A w h n a
  exact isSemisimpleRepresentation_of_isSmooth a.ρ a.smooth a.semisimple

end GlobalTheory.WeilDeligne.WDRep
end
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.HerrClass

namespace GlobalTheory.RedDense

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_pred_sub_one_le {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l]) ^ (l - 1) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
  let u : ℤ_[l] := ⟨(χ g : ℚ_[l]), hχ.norm_le_one g⟩
  have hu : IsUnit u := PadicInt.isUnit_iff.2 (hχ.norm_eq_one g)
  have h3 : PadicInt.toZMod (u ^ (l - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one (hu.map _).ne_zero, sub_self]
  have h4 : u ^ (l - 1) - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := by
    rw [pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
    exact h3
  have h5 := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 h4
  rw [PadicInt.norm_def] at h5
  exact h5

theorem card_and_dense {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} {s : ℕ} (h2 : l ≠ 2)
    (hK : K.1 ≤ Ks K s)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    ¬ l ∣ W.DelF.card ∧ ∀ γ : W.Gam, (W.χΓ γ : ↥(OL LL)) = 1 + (l : ↥(OL LL)) →
      ∀ U : Subgroup ↥(GK K), IsClosed (U : Set ↥(GK K)) →
        (∀ g, (W.resΓ g ∈ W.DelF ∨ W.resΓ g = γ) → g ∈ U) → ∀ g, g ∈ U := by
  have hl : l.Prime := Fact.out
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨-, -, hG⟩ := cyc_basic l P.χQ hχ
  have hH0 : ∀ x ∈ Hinf K, x ∈ (K0 K).fixingSubgroup := fun x hx y =>
    hx ⟨y.1, (le_sup_left : K0 K ≤ Kinf K) y.2⟩
  have hH : Hinf K ≤ GK K := by
    intro x hx
    have h1 : x ∈ Gj K s := ((hG K x (hH0 x hx)).1 s).2 (by
      rw [(hG K x (hH0 x hx)).2.1 hx, Units.val_one, sub_self, norm_zero]
      positivity)
    exact fun y => h1 ⟨y.1, hK y.2⟩
  have hj : Lev l 1 := ⟨le_rfl, fun e => absurd e h2⟩
  have hN : ¬ l ∣ l - 1 := by
    have := hl.two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpow := norm_pow_pred_sub_one_le hχ
  have hN0 : l - 1 ≠ 0 := by have := hl.two_le; omega
  refine ⟨?_, fun γ hγ U hU hp g => ?_⟩
  · have htor : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := by
      intro δ hδ
      obtain ⟨g, rfl⟩ := W.resΓ_onto δ
      obtain ⟨k, hk, hk'⟩ := (W.DelF_def _).1 hδ
      rw [res_pow_eq_one_iff] at hk' ⊢
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      refine eq_one_of_pow hj (hpow g) hk.ne' ?_
      rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hk', Units.val_one, one_pow]
    have h1Δ : (1 : W.Gam) ∈ W.DelF := (mem_DelF_iff W _).2 (one_mem _)
    intro hdv
    haveI : Finite ↥(CommGroup.torsion W.Gam) := Nat.finite_of_card_ne_zero (by
      rw [card_torsion]; exact Finset.card_ne_zero.2 ⟨1, h1Δ⟩)
    rw [← card_torsion] at hdv
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hdv
    apply hN
    have h3 : orderOf x ∣ l - 1 :=
      orderOf_dvd_iff_pow_eq_one.2 (Subtype.ext (htor x ((mem_DelF_iff W _).2 x.2)))
    rwa [hx] at h3
  · have hmemΔ : ∀ g : ↥(GK K), P.χQ g ^ (l - 1) = 1 → W.resΓ g ∈ W.DelF := fun g hg =>
      (W.DelF_def _).2 ⟨l - 1, Nat.pos_of_ne_zero hN0, (res_pow_eq_one_iff W g _).2 hg⟩
    obtain ⟨γ', hγ'⟩ := W.resΓ_onto γ
    have hv : (P.χQ γ' : ℚ_[l]) = 1 + l := by
      apply (algebraMap ℚ_[l] ↥LL.1).injective
      rw [← chi_res W γ', hγ', hγ]
      simp
    have hn : ‖(P.χQ γ' : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [hv, add_sub_cancel_left, Padic.norm_p]
      simp
    refine mem_of_tors_gen ha hχ K hH hj hN hN (fun x _ => hpow x) (fun x _ hx => hx) U hU
      (fun x hx => hp x (Or.inl (hmemΔ x hx))) γ' (hp γ' (Or.inr hγ')) (fun x => ?_) g
    rw [norm_pow_sub_one hj hn.le hN, hn]
    exact hpow x

theorem exists_closed_stab {G Qp LL O k : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL] [Field k]
    [Algebra O k] (hO : IsOpen (Set.range (algebraMap O LL))) {c : O} (hc : algebraMap O LL c ≠ 0)
    (hk : algebraMap O k c = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (hq : Onto T A q) (t : Fin A.m → k) :
    ∃ U : Subgroup G, IsClosed (U : Set G) ∧ ∀ g, g ∈ U ↔ A.ρ g t = t := by
  obtain ⟨x, rfl⟩ := hq.1 t
  have hlc : IsLocallyConstant fun g => q (latRep T.L g x) :=
    GlobalTheory.FiniteAdm.isLocallyConstant_comp hO T.L.T T.L.fg T.L.span hc q
      (fun y => by rw [← algebraMap_smul k, hk, zero_smul]) _ (T.cont x)
  let U : Subgroup G :=
    { carrier := {g | A.ρ g (q x) = q x}
      mul_mem' := fun {a b} ha hb => by
        change A.ρ a (q x) = q x at ha
        change A.ρ b (q x) = q x at hb
        change A.ρ (a * b) (q x) = q x
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        change A.ρ a (q x) = q x at ha
        change A.ρ a⁻¹ (q x) = q x
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  refine ⟨U, ?_, fun g => Iff.rfl⟩
  have := hlc.isClosed_fiber (q x)
  simp only [hq.2] at this
  exact this

theorem fixed_of_fixed_lifts : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → (((S.W H).DelF.card : ℕ) : k) ≠ 0 ∧ ∀ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)), Onto T A q → ∀ t : Fin A.m → k, (∀ g, ((S.W H).resΓ g ∈ (S.W H).DelF ∨ (S.W H).resΓ g = γ) → A.ρ g t = t) → ∀ g, A.ρ g t = t := by
  intro l _ P AI H S k _ _ _ _
  have hl : l.Prime := Fact.out
  obtain ⟨h1, h2⟩ := card_and_dense AI S.hyp.1.2.1.2.1 S.hyp.1.2.1.2.2.2.2.1 (S.W H)
  refine ⟨fun h => h1 ((CharP.cast_eq_zero_iff k l _).1 h), fun γ hγ T A q hq t ht => ?_⟩
  haveI : IsTopologicalRing ↥S.LL.1 :=
    inferInstanceAs (IsTopologicalRing ↥S.LL.1.toSubalgebra.toSubring)
  obtain ⟨U, hU, hm⟩ := exists_closed_stab (c := (l : S.O)) (GlobalTheory.LocalIntegers.isOpen_integers l S.LL)
    (by rw [map_natCast]; exact Nat.cast_ne_zero.2 hl.ne_zero)
    (by rw [map_natCast, CharP.cast_eq_zero]) T A q hq t
  exact fun g => (hm g).1 (h2 γ hγ U hU (fun g hg => (hm g).2 (ht g hg)) g)

end GlobalTheory.RedDense
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem largePrimeLengthVanishing_and_exceptionalBounded_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ)
    (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.LargePrimeLengthVanishing L (tab L X tf C) ∧ TwistedPlaces.ExceptionalPrimesBounded L (tab L X tf C) := by
  intro D L P X C tf h
  obtain ⟨h3, hq, hd, -, -, hsl⟩ := h.small
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hlt, -, hexc⟩ := hl
    have hexc' : D.nd.l i ∉ X.exc := hexc
    have h2 : D.nd.l i ∉ D.host.small := fun he => by linarith [hsl _ he]
    have h3' : D.nd.l i ≠ 3 := by
      rintro he; rw [he] at hlt; push_cast at hlt; linarith
    have hq' : D.nd.l i ≠ D.host.q := by
      rintro he; rw [he] at hlt; linarith
    have hd' : D.nd.l i ≠ D.host.d := by
      rintro he; rw [he] at hlt; linarith
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.2.2 ⟨hlt, hexc'⟩
    refine ⟨fun lam _ => ?_, ?_⟩
    · simp only [tab, h2, h3', hR, if_false]
    · simp only [tab, h2, hR, if_false]
      rw [if_neg (by rintro (he | he) <;> contradiction)]
  · exact h.exc.1
  · exact h.exc.2

end GlobalTheory.NLink
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem adm5_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm5 L (tab L X tf C) C := by
  classical
  intro D L P X C tf h i hi hl
  obtain ⟨h2, hq, hd, hg⟩ := hl
  have hqd : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by tauto
  have hR0 : 0 ≤ C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 := by
    have := h.pos
    positivity
  show (if D.nd.l i ∈ D.host.small then TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i
    else if D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d then TwistedPlaces.midG L C (D.nd.l i)
    else if KillingConditions.RangeAD L X.exc (D.nd.l i) then KillingConditions.supZ i (X.errorBoundHub i) else 0) ≤ _
  rw [if_neg h2, if_neg hqd]
  split_ifs with hR
  · unfold KillingConditions.supZ
    split_ifs with hne
    · exact Finset.sup'_le hne _ (fun π hπ => h.bb i hi hg hR π hπ)
    · exact hR0
  · exact hR0

end GlobalTheory.NLink
end
