module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle010
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle627
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle005

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.BasisPf

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

theorem basis_of (hI : Iwa) (hD : CayleyBlocksInvertible) (hM : Mult) (hC : CycSec) (hH : HolParam) : Basis := by
  intro m n ε c t p q e sL ρ hL _ _ W hW hWρ ν κ hν hκ ha hb P hP
  have := hν
  have := hW
  let sK := secK sL hL.cont
  let V : Submodule ℂ C(KR n, ℂ) := W.map sK
  let κC : C(KR n, ℂ) := ⟨κ, hκ⟩
  have hF0c := continuous_weight_factor (n := n) hD p q e

  have hflat : ∀ y : GR n, ∃ Q ∈ W, ∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y' := by
    intro y
    obtain ⟨Q, hQW, hQ⟩ := hb 0 (fun g => F0 p q e (g * y)) (hF0c.comp (continuous_id.mul continuous_const))
      (fun y0 g hy0 => by
        simp only [Complex.cpow_zero, one_mul]
        rw [mul_assoc, ((hM n p q e).2 y0 (g * y) hy0).1])
    exact ⟨Q, hQW, fun y' => by simpa using hQ y'⟩
  choose QF hQFW hQF using hflat
  let v : GR n → V := fun y => ⟨sK (QF y), Submodule.mem_map_of_mem (hQFW y)⟩
  have hpi_v : ∀ y (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → piL ν κC h = sK (QF y) := by
    intro y h hh
    ext k'
    rw [piL_apply, secK_apply, ← hQF y (k' : GR n)]
    congr 1; funext k
    rw [hh]; simp [κC, mul_assoc]
  have hpi_W : ∀ Q ∈ W, piL ν κC (sK Q) = sK Q := by
    intro Q hQ
    ext k'
    rw [piL_apply, secK_apply, ← ha Q hQ (k' : GR n)]
    rfl

  have hspan : Submodule.span ℂ (range v) = ⊤ := by
    by_contra hne
    have hlt : Submodule.span ℂ (range v) < ⊤ := lt_top_iff_ne_top.2 hne
    obtain ⟨ℓ, hℓ0, hℓS⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    obtain ⟨pr, hpr⟩ := Submodule.ClosedComplemented.of_finiteDimensional V
    let ℓc : V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap ℓ
    let L : C(KR n, ℂ) →L[ℂ] ℂ := ℓc.comp (pr.comp (piL ν κC))
    have hLv : ∀ (y : GR n) (h : C(KR n, ℂ)), (∀ k, h k = F0 p q e ((k : GR n) * y)) → L h = 0 := by
      intro y h hh
      have e1 : L h = ℓ (pr (piL ν κC h)) := rfl
      rw [e1, hpi_v y h hh]
      have e2 : pr (sK (QF y)) = v y := hpr (v y)
      rw [e2]
      have hmem : v y ∈ Submodule.span ℂ (range v) := Submodule.subset_span ⟨y, rfl⟩
      have : ℓ (v y) ∈ (Submodule.span ℂ (range v)).map ℓ := Submodule.mem_map_of_mem hmem
      rw [hℓS] at this
      simpa using this
    apply hℓ0
    ext ⟨x, hx⟩
    obtain ⟨Q, hQ, rfl⟩ := hx
    have h0 := hC m n ε c t p q e sL ρ hL L hLv Q (sK Q) (fun k => rfl)
    have e1 : L (sK Q) = ℓ (pr (piL ν κC (sK Q))) := rfl
    rw [e1, hpi_W Q hQ] at h0
    have e2 : pr (sK Q) = ⟨sK Q, Submodule.mem_map_of_mem hQ⟩ := hpr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩
    rw [e2] at h0
    simpa using h0

  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℂ (range v)
  have hs_top : ⊤ ≤ Submodule.span ℂ (range ((↑) : s → V)) := by
    rw [Subtype.range_coe, hs_span, hspan]
  let bV := Module.Basis.mk hs_li hs_top
  have : Finite s := Module.Finite.finite_basis bV
  have : Fintype s := Fintype.ofFinite s
  let N := Fintype.card s
  let b : Module.Basis (Fin N) ℂ V := bV.reindex (Fintype.equivFin s)
  have hbv : ∀ i, ∃ y, v y = b i := by
    intro i
    have hb' : (b i : V) = ((Fintype.equivFin s).symm i : V) := by
      simp [b, bV]
    rw [hb']
    exact hs_sub ((Fintype.equivFin s).symm i).2
  choose yy hyy using hbv
  let QQ : Fin N → PX m n := fun i => QF (yy i)
  have hQQ : ∀ i (k : KR n), ((b i : V) : C(KR n, ℂ)) k = sL (QQ i) (k : GR n) := by
    intro i k; rw [← hyy i]; rfl
  have hcoord : ∀ Q (hQ : Q ∈ W) (k : KR n), sL Q (k : GR n) =
      ∑ j, b.repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩ j * sL (QQ j) (k : GR n) := by
    intro Q hQ k
    have h := congrArg (fun x : V => ((x : C(KR n, ℂ)) k)) (b.sum_repr ⟨sK Q, Submodule.mem_map_of_mem hQ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ] at h
    rw [h]; rfl
  have hsum_sL : ∀ (d : Fin N → ℂ) (y : GR n), sL (∑ j, d j • QQ j) y = ∑ j, d j * sL (QQ j) y := by
    intro d y

    simp [map_sum, map_smul, Finset.sum_apply]
  let cc : Fin N → ℂ := fun j => b.repr ⟨sK P, Submodule.mem_map_of_mem hP⟩ j
  have hPsum : ∀ y, sL P y = ∑ j, cc j * sL (QQ j) y := by
    intro y
    rw [flatEq_of hI m n ε c t p q e sL ρ hL P (∑ j, cc j • QQ j) (fun k hk => by
      rw [hcoord P hP ⟨k, hk⟩, hsum_sL]) y, hsum_sL]

  let f : Fin N → KR n → ℂ := fun j k => sL (QQ j) (k : GR n)
  have hfli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 : ∑ j, g j • b j = 0 := by
      apply Subtype.ext
      ext k
      have := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, f] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hQQ, Submodule.coe_zero, ContinuousMap.zero_apply]
      exact this
    exact Fintype.linearIndependent_iff.1 b.linearIndependent g h2
  obtain ⟨kk, hkk⟩ := exists_pts N f hfli
  let A : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun j l => f j (kk l)
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 hkk
  let Ev : ℂ → Matrix (Fin N) (Fin N) ℂ := fun w => Matrix.of fun i l =>
    ∫ k, κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i)) ∂ν
  let M : ℂ → Matrix (Fin N) (Fin N) ℂ := fun w => Ev w * A⁻¹
  have hEv0 : Ev 0 = A := by
    ext i l
    simp only [Ev, A, f, Matrix.of_apply, Complex.cpow_zero, one_mul]
    exact hQF (yy i) (kk l)
  have hM0 : M 0 = 1 := by
    show Ev 0 * A⁻¹ = 1
    rw [hEv0]; exact Matrix.mul_nonsing_inv A hA
  have hEvd : ∀ i l, Differentiable ℂ (fun w => Ev w i l) := by
    intro i l
    have hcg : Continuous (fun k : KR n => (kk l : GR n) * (k : GR n) * yy i) :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have hpos : ∀ k : KR n, 0 < hLoc ((kk l : GR n) * (k : GR n) * yy i) := fun k => hLoc_pos hD _
    have h := (hH (KR n) ν univ isCompact_univ (by simp) univ
      (fun k w => κ k * ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e ((kk l : GR n) * (k : GR n) * yy i)))
      isOpen_univ ?_ ?_).1
    · exact differentiableOn_univ.1 h
    · refine Continuous.continuousOn ?_
      refine (hκ.comp continuous_fst).mul (Continuous.mul ?_ (hF0c.comp (hcg.comp continuous_fst)))
      exact Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp (hcg.comp continuous_fst)))
        continuous_snd (fun y => Complex.ofReal_mem_slitPlane.2 (hpos y.1))
    · intro k _
      have hne : ((hLoc ((kk l : GR n) * (k : GR n) * yy i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos k).ne'
      exact ((((differentiable_id.const_cpow (Or.inl hne)).mul_const _).const_mul _)).differentiableOn
  have hMd : ∀ i j, Differentiable ℂ (fun w => M w i j) := by
    intro i j
    show Differentiable ℂ (fun w => (Ev w * A⁻¹) i j)
    simp only [Matrix.mul_apply]
    exact Differentiable.fun_sum fun l _ => (hEvd i l).mul_const _
  refine ⟨N, yy, QQ, cc, M, fun j => hQFW (yy j), hPsum, hM0, hMd, fun i y' => hQF (yy i) y', ?_⟩
  intro w i y'
  let fw : GR n → ℂ := fun g => (hLoc (g * yy i) : ℂ) ^ w * F0 p q e (g * yy i)
  have hfwc : Continuous fw := by
    have hg : Continuous (fun g : GR n => g * yy i) := continuous_id.mul continuous_const
    refine Continuous.mul ?_ (hF0c.comp hg)
    exact Continuous.cpow (Complex.continuous_ofReal.comp ((continuous_hLoc hD).comp hg)) continuous_const
      (fun g => Complex.ofReal_mem_slitPlane.2 (hLoc_pos hD _))
  have hfwlaw : ∀ (y0 g : GR n), (mR y0).toBlocks₂₁ = 0 → fw (y0 * g) = (hLoc y0 : ℂ) ^ w * F0 p q e y0 * fw g := by
    intro y0 g hy0
    simp only [fw]
    rw [mul_assoc y0 g (yy i)]
    obtain ⟨h1, h2⟩ := (hM n p q e).2 y0 (g * yy i) hy0
    rw [h1, h2]
    push_cast
    rw [Complex.mul_cpow_ofReal_nonneg (hLoc_pos hD y0).le (hLoc_pos hD _).le]
    ring
  obtain ⟨Qw, hQwW, hQw⟩ := hb w fw hfwc hfwlaw
  let a := b.repr ⟨sK Qw, Submodule.mem_map_of_mem hQwW⟩
  have hEva : ∀ l, Ev w i l = ∑ j, a j * A j l := by
    intro l
    have h1 := hQw (kk l : GR n)
    rw [hLoc_K hM _ (kk l).2] at h1
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h1
    rw [hcoord Qw hQwW (kk l)] at h1
    simp only [Ev, A, f, Matrix.of_apply]
    rw [← h1]
  have hrow : (fun l => Ev w i l) = Matrix.vecMul a A := by
    funext l; rw [hEva l]; simp [Matrix.vecMul, dotProduct]
  have hMa : ∀ j, M w i j = a j := by
    intro j
    have e1 : M w i j = Matrix.vecMul (fun l => Ev w i l) A⁻¹ j := by
      simp [M, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [e1, hrow, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hA, Matrix.vecMul_one]
  have hflatw : ∀ y, sL Qw y = ∑ j, M w i j * sL (QQ j) y := by
    intro y
    rw [flatEq_of hI m n ε c t p q e sL ρ hL Qw (∑ j, M w i j • QQ j) (fun k hk => by
      rw [hcoord Qw hQwW ⟨k, hk⟩, hsum_sL]
      simp only [hMa]; rfl) y, hsum_sL]
  rw [show (∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w * F0 p q e (y' * (k : GR n) * yy i)) ∂ν) =
      ∫ k, κ k * fw (y' * (k : GR n)) ∂ν from rfl, hQw y', hflatw]

end PositivityTheory.Rg.Sw.AbsSt.BasisPf

namespace PositivityTheory.Rg.Sw.AbsSt

theorem basis (hI : Iwa) (hD : CayleyBlocksInvertible) (hM : Mult) (hC : CycSec) (hH : HolParam) : Basis :=
  BasisPf.basis_of hI hD hM hC hH

end PositivityTheory.Rg.Sw.AbsSt
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem aE_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) = NormedSpace.exp (-((σ : ℂ) • H)) := by
  simp [aE, neg_smul]

theorem aE_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H (-σ) * aE H σ = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem aE_mul_neg' (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : aE H σ * aE H (-σ) = 1 := by
  rw [aE_neg, aE, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem aE_herm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (σ : ℝ) : (aE H σ)ᴴ = aE H σ := by
  rw [aE, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]
  congr 1
  simp

theorem det_aE (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : (aE H σ).det = Complex.exp ((σ : ℂ) * H.trace) := by
  rw [aE, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul]

private theorem JJ_mul_self_eq_neg_one (n : ℕ) : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp
private theorem mul_JJ_mul_conjTranspose_eq_JJ_of_inG {n : ℕ} (G Gi : M2 n) (hGi : G * Gi = 1) (hG : InG G) :
    G * JJ n * Gᴴ = JJ n := by
  have hJ := JJ_mul_self_eq_neg_one n
  have h1 : Gᴴ * JJ n = JJ n * Gi := by
    calc Gᴴ * JJ n = Gᴴ * JJ n * (G * Gi) := by rw [hGi, Matrix.mul_one]
      _ = (Gᴴ * JJ n * G) * Gi := by simp only [Matrix.mul_assoc]
      _ = JJ n * Gi := by rw [hG]
  calc G * JJ n * Gᴴ = G * JJ n * Gᴴ * (JJ n * (-JJ n)) := by
        rw [Matrix.mul_neg, hJ, neg_neg, Matrix.mul_one]
    _ = G * (JJ n * (Gᴴ * JJ n)) * (-JJ n) := by simp only [Matrix.mul_assoc]
    _ = G * ((JJ n * JJ n) * Gi) * (-JJ n) := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = JJ n := by
        rw [hJ]
        simp [hGi]
private theorem exists_GR_mR_eq_of_inG_of_inverse {n : ℕ} (M Mi : M2 n) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hM : InG M) : ∃ x : GR n, mR x = M ∧ mR x⁻¹ = Mi :=
  ⟨⟨⟨M, Mi, h1, h2⟩, hM⟩, rfl, rfl⟩
private theorem inG_JJ_mul_nU_of_isHermitian {n : ℕ} (c : Matrix (Fin n) (Fin n) ℂ) (hc : c.IsHermitian) :
    InG (JJ n * nU c) := by
  unfold InG JJ nU
  rw [fromBlocks_multiply, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc.eq]
private theorem inG_fromBlocks_diag_of_hermitian_inverse {n : ℕ} (a a' : Matrix (Fin n) (Fin n) ℂ) (ha : a.IsHermitian)
    (ha' : a'.IsHermitian) (h : a * a' = 1) (h' : a' * a = 1) :
    InG (fromBlocks a' 0 0 a) := by
  unfold InG JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ha.eq, ha'.eq]
  simp [h, h']

theorem cellM : CellM := by
  intro n H hH f hf g hC
  have hG : mR g = fromBlocks (toBlocks₁₁ (mR g)) (toBlocks₁₂ (mR g)) (toBlocks₂₁ (mR g))
      (toBlocks₂₂ (mR g)) := (fromBlocks_toBlocks _).symm
  set A := toBlocks₁₁ (mR g)
  set B := toBlocks₁₂ (mR g)
  set C := toBlocks₂₁ (mR g)
  set D := toBlocks₂₂ (mR g)
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  have hgi : mR g * mR g⁻¹ = 1 := congrArg mR (mul_inv_cancel g)
  have hgJ : mR g * JJ n * (mR g)ᴴ = JJ n := mul_JJ_mul_conjTranspose_eq_JJ_of_inG (mR g) (mR g⁻¹) hgi g.2
  have hCD : C * Dᴴ = D * Cᴴ := by
    have h22 := congrArg toBlocks₂₂ hgJ
    rw [hG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h22
    simp at h22
    exact ((neg_add_eq_zero).mp h22).symm
  have hCHu : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hCu.star
  have hbH : (C⁻¹ * D).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * (Cᴴ)⁻¹ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hCD]
      _ = C⁻¹ * D := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one]
  have hnU : ∀ c : Matrix (Fin n) (Fin n) ℂ, nU c * nU (-c) = 1 ∧ nU (-c) * nU c = 1 := by
    intro c
    constructor <;> rw [nU, nU, fromBlocks_multiply, ← fromBlocks_one] <;> simp
  have hJ := JJ_mul_self_eq_neg_one n
  have hWinv : ∀ c : Matrix (Fin n) (Fin n) ℂ,
      JJ n * nU c * (nU (-c) * -JJ n) = 1 ∧ nU (-c) * -JJ n * (JJ n * nU c) = 1 := by
    intro c
    constructor
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (nU c), (hnU c).1, Matrix.one_mul, Matrix.mul_neg, hJ,
        neg_neg]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (-JJ n), Matrix.neg_mul, hJ, neg_neg, Matrix.one_mul,
        (hnU c).2]
  obtain ⟨w₀, hw₀, hw₀i⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (C⁻¹ * D)).1 (hWinv (C⁻¹ * D)).2
    (inG_JJ_mul_nU_of_isHermitian _ hbH)
  refine ⟨g * w₀⁻¹, C⁻¹ * D, ?_, hbH, ?_⟩
  · show toBlocks₂₁ (mR g * mR w₀⁻¹) = 0
    rw [hw₀i, hG, nU, JJ, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply]
    simp [← Matrix.mul_assoc, mul_nonsing_inv _ hCu]
  intro p q e σ
  have h1 : aE H σ * aE H (-σ) = 1 := aE_mul_neg' H σ
  have h2 : aE H (-σ) * aE H σ = 1 := aE_mul_neg H σ
  have ha : (aE H σ).IsHermitian := aE_herm hH σ
  have ha' : (aE H (-σ)).IsHermitian := aE_herm hH (-σ)
  have hc : (aE H (-σ) * (C⁻¹ * D) * aE H (-σ)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, ha'.eq, hbH.eq, ← Matrix.mul_assoc]
  obtain ⟨mA, hmA, -⟩ := exists_GR_mR_eq_of_inG_of_inverse (fromBlocks (aE H (-σ)) 0 0 (aE H σ))
    (fromBlocks (aE H σ) 0 0 (aE H (-σ)))
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (by rw [fromBlocks_multiply, ← fromBlocks_one]; simp [h1, h2])
    (inG_fromBlocks_diag_of_hermitian_inverse _ _ ha ha' h1 h2)
  obtain ⟨w, hw, -⟩ := exists_GR_mR_eq_of_inG_of_inverse _ _ (hWinv (aE H (-σ) * (C⁻¹ * D) * aE H (-σ))).1
    (hWinv _).2 (inG_JJ_mul_nU_of_isHermitian _ hc)
  refine ⟨mA, w, ?_, ?_, hw, hc, ?_⟩
  · show toBlocks₂₁ (mR mA) = 0
    rw [hmA]
    simp
  · unfold F0 f0 u1 u2
    rw [hmA]
    simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_zero, zero_add, neg_zero,
      det_fromBlocks_zero₂₁]
    rw [← det_mul, h2, det_one, _root_.one_zpow, one_mul, det_aE, ← Complex.exp_int_mul,
      ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · apply Subtype.ext
    apply Units.ext
    show mR g * mR (f σ) = mR g * mR w₀⁻¹ * mR mA * mR w
    rw [hf σ, hw₀i, hmA, hw, Matrix.mul_assoc (mR g), Matrix.mul_assoc (mR g)]
    congr 1
    change fromBlocks (aE H σ) 0 0 (NormedSpace.exp (-((σ : ℂ) • H))) = _
    rw [← aE_neg, nU, nU, JJ, fromBlocks_neg]
    simp [fromBlocks_multiply, ← Matrix.mul_assoc, h1]

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end
