module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle363
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle364
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle349
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridReal

open GlobalTheory.SignedHC

theorem num_real_bounds : ∀ (D : D7) (large₂ : SizeData₂ D), SizeRows large₂ → ∀ τ : D.what₂.Tau, (∀ i, 2 ≤ i → i < (GlobalTheory.ChiGrid.num D 1 τ).k → (GlobalTheory.ChiGrid.num D 1 τ).v (i + 1) + 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v i) ∧ 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k + (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (∀ l, 1 ≤ l → l < (GlobalTheory.ChiGrid.num D 1 τ).m → ((GlobalTheory.ChiGrid.num D 1 τ).b l : ℝ) + 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).b (l + 1)) ∧ 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).ga ∧ 0 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k ∧ 0 < (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (((GlobalTheory.ChiGrid.num D 1 τ).a 0 : ℚ) : ℝ) ≤ large₂.sc.b ^ 2 ∧ ((GlobalTheory.ChiGrid.num D 1 τ).b (GlobalTheory.ChiGrid.num D 1 τ).m : ℝ) ≤ large₂.sc.b ^ 2 ∧ 1 ≤ large₂.sc.b ∧ 8 * ((D.R.r : ℝ) + 1) ≤ large₂.sc.b ^ 4 := by
  intro D large₂ hS τ
  obtain ⟨⟨Pm, -, -⟩, -, -, hm44, -, -, -, -, -, -, -, hSb, hpos, -⟩ := hS
  set G := GlobalTheory.ChiGrid.num D 1 τ with hG
  have hk : G.k = D.R.k := rfl
  have hm : G.m = D.R.m := rfl
  have hga : G.ga = GlobalTheory.ChiGrid.gap D 1 := rfl
  obtain ⟨hv0, hb0, -⟩ := GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1)
    (GlobalTheory.ChiGrid.cen D 1 τ)
  have hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ) := by
    intro i
    have e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ) := hv0 i
    rw [e, Rat.cast_intCast]
  have hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ) := hb0 l
    rw [e, Rat.cast_intCast]
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr6 : 6 ≤ D.R.r := by unfold Ranks.r; omega
  set X : ℝ := (D.R.r : ℝ) + 1 with hX
  have hX7 : 7 ≤ X := by
    have : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    linarith
  have hX3 : 0 ≤ X ^ 3 := by positivity

  have hgapS : (2 : ℝ) ≤ Formalism.BasicNotions.LevelStarExponents.gapS D Pm.Cgap := by
    unfold Formalism.BasicNotions.LevelStarExponents.gapS
    have h1 : 0 ≤ Pm.Cgap * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 := by
      have := Pm.Cgap_pos; positivity
    have hN : (2 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      have : 2 ≤ D.R.N D.R.m := by unfold Ranks.N; exact le_trans (by omega) (Nat.le_add_right _ _)
      exact_mod_cast this
    have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))
    nlinarith

  have hgap : 1000 * X ^ 3 ≤ (G.ga : ℝ) := by
    have hB := ((GlobalTheory.ChiGrid.gapBound_iff D 1 (GlobalTheory.ChiGrid.gap D 1)).2 le_rfl).1
    have hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = X := by unfold GlobalTheory.ChiGrid.nRk; push_cast; rfl
    rw [hn] at hB
    have h1 : 0 ≤ (1 : ℝ) * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 3 := by positivity
    have h2 : 0 ≤ (1 : ℝ) * X ^ 3 * Real.sqrt (GlobalTheory.ChiGrid.cloudLen D) := by
      have := Real.sqrt_nonneg (GlobalTheory.ChiGrid.cloudLen D : ℝ); positivity
    have h4 : (1000 : ℝ) ≤ X ^ 4 := by
      have : (7 : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX7 4
      norm_num at this; linarith
    have h7 : 1000 * X ^ 3 ≤ X ^ 7 := by
      have : X ^ 7 = X ^ 4 * X ^ 3 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right h4 hX3
    rw [hga]; linarith
  have hX1 : (1 : ℝ) ≤ 1000 * X ^ 3 := by
    have : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ (by linarith)
    linarith

  have hga0 : (0 : ℝ) ≤ (G.ga : ℝ) := by positivity
  have hSb' : large₂.Sc + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) + 1 / 2 ≤ large₂.sc.b := by rw [hga]; exact hSb
  have hSc := large₂.Sc_pos
  have hbga : (G.ga : ℝ) ≤ large₂.sc.b := by
    have : (G.ga : ℝ) ≤ ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      have : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
      nlinarith
    linarith
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hbsq : large₂.sc.b ≤ large₂.sc.b ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb1, ?_⟩
  ·
    intro i hi1 hi2
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hi1
    have hlt : a + 1 < D.R.k - 1 := by rw [hk] at hi2; omega
    have h := (Pm.sig_gaps τ).1 a hlt
    have e := hv ⟨a, by omega⟩
    have e' := hv ⟨a + 1, hlt⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have : ((G.v (a + 2 + 1) : ℤ) : ℝ) + 2 ≤ ((G.v (a + 2) : ℤ) : ℝ) := by
      rw [show a + 2 + 1 = a + 1 + 2 by omega]; linarith
    exact_mod_cast this
  ·
    have h := (Pm.sig_gaps τ).2.1 (by omega) (by omega)
    have e := hv ⟨D.R.k - 2, by omega⟩
    have e' := hb ⟨0, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    have : (2 : ℝ) ≤ ((G.v (D.R.k - 2 + 2) : ℤ) : ℝ) + ((G.b (0 + 1) : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  ·
    intro l hl1 hl2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hl1
    have hlt : j + 1 < D.R.m := by rw [hm] at hl2; omega
    have h := (Pm.nodes_gap τ j hlt).1
    have hf := Pm.heightBound_ge_rank_cubic
    have e := hb ⟨j + 1, hlt⟩
    have e' := hb ⟨j, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have hY : 10 * X ≤ (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
      have h44 : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
      have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
      have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
      nlinarith
    have hY3 : (10 * X) ^ 3 ≤ ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hY 3
    have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
    have : ((G.b (j + 1) : ℤ) : ℝ) + 1000 * X ^ 3 ≤ ((G.b (j + 1 + 1) : ℤ) : ℝ) := by nlinarith
    exact this
  · exact hgap
  ·
    have h := (large₂.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
    rw [hv] at h
    simp only at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    exact_mod_cast h
  ·
    have h := (hpos τ ⟨0, by omega⟩).1
    have e := hb ⟨0, by omega⟩
    have h' : (0 : ℝ) < (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast h
    rw [e] at h'
    exact_mod_cast h'
  ·
    have h := (large₂.cloud_v τ ⟨0, by omega⟩).2
    rw [hv] at h
    simp only [zero_add] at h
    have e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      unfold GridData.a; rw [hm]; push_cast; ring
    rw [e]; linarith
  ·
    have h := large₂.b_le τ ⟨D.R.m - 1, by omega⟩
    rw [hb] at h
    simp only at h
    rw [hm, show D.R.m = D.R.m - 1 + 1 by omega]
    exact h
  ·
    have h8 : 8 * X ≤ 1000 * X ^ 3 := by
      have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ (by linarith)
      have : X ^ 3 = X * X ^ 2 := by ring
      have hXX : X ≤ X ^ 3 := by rw [this]; nlinarith
      linarith
    have hb4 : large₂.sc.b ≤ large₂.sc.b ^ 4 := by
      have : large₂.sc.b ^ 4 = large₂.sc.b * large₂.sc.b ^ 3 := by ring
      rw [this]
      have : (1 : ℝ) ≤ large₂.sc.b ^ 3 := one_le_pow₀ hb1
      nlinarith
    linarith

end GlobalTheory.GridReal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.SympForm

theorem symplO_eq_symp_one {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x y =
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) 1 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹)) x y := by
  unfold symplO GlobalTheory.WeilM.symp hO GlobalTheory.WeilM.hTens
  congr 1
  have h : ∀ j l, (1 : AE D) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) j l =
      incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := fun j l => by
    rw [one_mul, ← map_mul]
    rfl
  have hc : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig z = cA D z := fun z => rfl
  simp only [Finset.mul_sum, hc]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
  have h' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ d c = incA D (T.gram c d) := rfl
  rw [h']
  linear_combination (-(x d a * incA D (T.gram c d) * cA D (y c b))) * h a b

end GlobalTheory.SquareAgree.SympForm


open GlobalTheory.SquareAgree.SympForm in
theorem GlobalTheory.SquareAgree.SympForm.symp_model_eq_symplO : ∀ (D : D7) (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
    Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram → Ws.J = D.host.xi0 • reindex e e X.gramᵀ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ u v, GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) u v = symplO (sgn ε S) X (cS u) (cS v) := by
  intro D ε S X d e Vs Ws hJ hJW cS hc u v
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E,
    (if ε then -1 else 1 : D.host.E) • S.gram = G := ⟨_, rfl⟩
  rw [hGdef] at hc
  have hs : (sgn ε S).gram = G := by
    rw [← hGdef]
    cases ε
    · ext i j; simp [sgn, HSpace.gram]
    · ext i j; simp [HSpace.gram]
  have hVJ : Vs.J = -G := by
    rw [hJ, ← hGdef]; cases ε <;> simp
  have hdet : IsUnit G.det := by rw [← hs]; exact (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hHG : (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hherm : ∀ i j, D.sp.cm.sig (G i j) = G j i := by
    intro i j
    have h := (sgn ε S).herm.eq ((sgn ε S).frame i) ((sgn ε S).frame j)
    rw [← hs]
    simpa [HSpace.gram, CMData.sig, starRingEnd_apply] using h
  have hG : (G.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (G.map (incA D))ᵀ := by
    ext i j
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (G i j)) = incA D (G j i)
    rw [← hherm i j]
    rfl
  have key := hTens_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e (X.gram.map (incA D)) (incA D D.host.xi0) hHG hG u v
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -(G.map (incA D)) := by
    rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = incA D D.host.xi0 • reindex e e (X.gram.map (incA D))ᵀ := by
    rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _
  have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) = incA D D.host.xi0 • (G⁻¹).map (incA D) := by
    rw [hs]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _
  have e4 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ = (X.gram.map (incA D))ᵀ := rfl
  rw [symplO_eq_symp_one, e3, e4, hc, hc, e1, e2]
  have e5 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G = G.map (incA D) := by ext i j; rfl
  simp only [e5]
  unfold GlobalTheory.WeilM.symp
  simp only [key, one_mul, neg_one_mul]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ConjLineSplit

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (conjU continuous_conjU)
open GlobalTheory.ConjUTransport (conjUInv conjEquiv continuous_conjUInv)

theorem exists_lie_eq_exp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (hc : Continuous M)
    (h0 : M 0 = 1) (hm : ∀ s t, M (s + t) = M s * M t) (hU : ∀ t, (M t)ᴴ * H * M t = H) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, Yᴴ * H + H * Y = 0 ∧ ∀ t : ℝ, NormedSpace.exp (t • Y) = M t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨Y, hY⟩ := GlobalTheory.banach_oneParamGroup_eq_exp M hc h0 hm
  refine ⟨Y, ?_, hY⟩
  have hd : HasDerivAt M Y 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul, funext hY] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun c A => by rw [Matrix.conjTranspose_smul]; simp }
  have hT : HasDerivAt (fun t => (M t)ᴴ) Yᴴ 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hd
  have hF := (hT.mul_const H).fun_mul hd
  rw [funext hU] at hF
  have huniq := hF.unique (hasDerivAt_const (0 : ℝ) H)
  rwa [h0, Matrix.conjTranspose_one, mul_one, one_mul] at huniq

variable {D : D7}

theorem finTens_eq_zero {z : AE D} (h : ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0 → u • z = 0) :
    GlobalTheory.LFun.finTens D.host.F D.host.E z = 0 := by
  let e : AF D.host.F := ((0, 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
  have he : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F e = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
  have h1 := congrArg (GlobalTheory.LFun.finTens D.host.F D.host.E) (h e he)
  rw [Algebra.smul_def, map_mul, map_zero] at h1
  have h2 : GlobalTheory.LFun.finTens D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) e) = 1 := rfl
  rwa [h2, one_mul] at h1

theorem cA_smul (u : AF D.host.F) (z : AE D) : cA D (u • z) = u • cA D z :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig) u z

theorem smul_cA_sub (u : AF D.host.F) {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) (i j : Fin n) :
    (u • (A.map (cA D) - 1)) i j = cA D ((u • (A - 1)) i j) := by
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, cA_smul, map_sub, Matrix.one_apply]
  split_ifs <;> simp

theorem conjU_mem_UAt_iff (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram) (g : GA D W) :
    conjU W 1 hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) ↔ g ∈ GinfC W := by
  have hone : ∀ a b : Fin W.rank, GlobalTheory.LFun.finTens D.host.F D.host.E ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) a b) =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro h
    show finHom W g = 1
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h1 : GlobalTheory.LFun.finTens D.host.F D.host.E ((Formalism.L2.Theta.mt W g - 1) a b) = 0 := by
      refine finTens_eq_zero fun u hu => ?_
      have h2 : (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0 := congrFun (congrFun (h u hu) a) b
      rw [smul_cA_sub] at h2
      have h3 := congrArg (cA D) h2
      rw [Formalism.L2.Theta.cA_cA, map_zero] at h3
      exact h3
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero] at h1
    exact h1
  · intro hg u hu
    have hf : finHom W g = 1 := hg
    refine Matrix.ext fun a b => ?_
    show (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0
    rw [smul_cA_sub, Matrix.smul_apply, GlobalTheory.KapXLine.smul_eq_zero_of_finTens hu, map_zero]
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero]
    exact congrArg (fun k : GL (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf

theorem ext_of_infMat {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g h : GA D W} (hg : g ∈ GinfC W) (hh : h ∈ GinfC W)
    (e : ∀ τ, infMat D.sp.cm.sig W.gram (θ τ) g = infMat D.sp.cm.sig W.gram (θ τ) h) : g = h := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have a : (finHom W g).1 = (finHom W h).1 := by
    rw [show finHom W g = 1 from hg, show finHom W h = 1 from hh]
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)))
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun a i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (e τ) i) j


open Classical in
theorem infMat_prod {θ : InfFam D} (W : HSp D) (m : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (x : D.what₂.Tau → GA D W) (hx : ∀ τ, IsAtTau θ W τ (m τ) (x τ)) (τ : D.what₂.Tau) (l : List D.what₂.Tau)
    (hl : l.Nodup) : infMat D.sp.cm.sig W.gram (θ τ) (l.map x).prod = if τ ∈ l then m τ else 1 := by
  induction l with
  | nil => simpa using GlobalTheory.PointAtPlaceHom.infMat_one W (θ τ)
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, GlobalTheory.PointAtPlaceHom.infMat_mul, ih hl.2]
    by_cases c : τ = a
    · subst c
      rw [(hx τ).2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [(hx a).2.2 τ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

theorem exists_eq_prod_oneP {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (g : ℝ → GA D W) (hc : Continuous g)
    (h0 : g 0 = 1) (hm : ∀ s t, g (s + t) = g s * g t) (hg : ∀ t, g t ∈ GinfC W) :
    ∃ Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, Y τ ∈ lieAt W τ) ∧
      ∀ t, g t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => oneP θ W τ (Y τ) t).prod := by
  have h1 : Continuous (matHom W) := continuous_subtype_val
  choose Y hY hexp using fun τ => exists_lie_eq_exp (gramAt D W τ) (fun t => infMat D.sp.cm.sig W.gram (θ τ) (g t))
    (continuous_matrix fun i j => (GlobalTheory.FockCompare.continuous_comp hθ τ).comp
      ((Units.continuous_val.comp (h1.comp hc)).matrix_elem i j))
    (by rw [h0, GlobalTheory.PointAtPlaceHom.infMat_one]) (fun s t => by rw [hm, GlobalTheory.PointAtPlaceHom.infMat_mul])
    (fun t => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W (g t) τ)
  refine ⟨Y, hY, fun t => ext_of_infMat hθ W (hg t) ?_ fun τ => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem W τ _
  · rw [infMat_prod W _ _ (fun τ' => GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hY τ') t) τ _ (Finset.nodup_toList _),
      if_pos (Finset.mem_toList.2 (Finset.mem_univ τ)), hexp]

theorem line_eq_prod : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram), ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ (Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
      (γs : D.what₂.Tau → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J)),
      (∀ τ, Y τ ∈ lieAt W τ) ∧ (∀ τ, γs τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd) ∧
      (∀ τ t, γs τ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W τ (Y τ) t)) ∧
      ∀ t, γ t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => γs τ t).prod := by
  intro D θ hθ W Wd hJ γ hγ
  let φ := conjEquiv W 1 one_ne_zero hJ
  obtain ⟨Y, hY, hprod⟩ := exists_eq_prod_oneP hθ W (fun t => φ.symm (γ (Multiplicative.ofAdd t)))
    ((continuous_conjUInv W 1 one_ne_zero hJ).comp (hγ.1.comp continuous_ofAdd))
    (by rw [ofAdd_zero, map_one, map_one]) (fun s t => by rw [ofAdd_add, map_mul, map_mul])
    (fun t => (conjU_mem_UAt_iff W Wd hJ _).1 (by
      have e : conjU W 1 hJ (φ.symm (γ (Multiplicative.ofAdd t))) = γ (Multiplicative.ofAdd t) := φ.apply_symm_apply _
      rw [e]
      exact hγ.2 _))
  let p : D.what₂.Tau → (Multiplicative ℝ →* GA D W) := fun τ =>
    { toFun := fun t => oneP θ W τ (Y τ) (Multiplicative.toAdd t)
      map_one' := GlobalTheory.Mem.Lift.oneP_zero hθ
      map_mul' := fun s t => GlobalTheory.Mem.Lift.oneP_add hθ (hY τ) _ _ }
  refine ⟨Y, fun τ => φ.toMonoidHom.comp (p τ), hY, fun τ => ⟨?_, fun t => ?_⟩, fun τ t => rfl, fun t => ?_⟩
  · exact (continuous_conjU W 1 hJ).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ (hY τ)).comp continuous_toAdd)
  · exact (conjU_mem_UAt_iff W Wd hJ _).2 (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _)
  · have e := congrArg φ (hprod (Multiplicative.toAdd t))
    rw [φ.apply_symm_apply, map_list_prod, List.map_map] at e
    exact e

end GlobalTheory.ConjLineSplit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_fundamentalDomain : ∀ (D : D7) (S : HSp D) (c : D.host.E) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hJ : J = c • S.gram), c ≠ 0 →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), IsHaarFD S ν 𝓕 →
      (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕)
        (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)) := by
  first | exact @GlobalTheory.HaarConjImage.map_isHaarFD | exact GlobalTheory.HaarConjImage.map_isHaarFD | (intros; apply GlobalTheory.HaarConjImage.map_isHaarFD <;> assumption)
end
