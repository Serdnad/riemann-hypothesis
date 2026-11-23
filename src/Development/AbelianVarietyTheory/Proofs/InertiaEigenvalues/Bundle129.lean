module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle110
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle111
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle070
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open GlobalTheory.JR Matrix

noncomputable section

namespace GlobalTheory.JR.Step

section MapLemmas
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')

theorem mom_glMap (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by
  simp only [mom, glMap]
  rw [RingHom.map_dotProduct, ← Matrix.map_pow]
  congr 1
  ext j
  simp [RingHom.map_mulVec]
  rfl

theorem inv_glMap (Y : Gl r k) : inv (glMap φ Y) = (inv Y).map φ := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i
    simp [inv, Inv.map, glMap, Matrix.charpoly_map]
  · ext i
    simp only [inv, Inv.map]
    exact mom_glMap φ Y i
  · rfl

theorem sec_map (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp only [sec, glMap, companion, Inv.map, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  · ext i
    simp only [sec, glMap]
    split_ifs <;> simp
  · rfl
  · rfl

theorem Delta_map (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  have : hankel (a.map φ) = (hankel a).map φ := by
    ext i j
    simp only [hankel, Matrix.of_apply, Matrix.map_apply, sec_map, mom_glMap]
  rw [Delta, Delta, this, RingHom.map_det]
  rfl

theorem full_glMap (Y : Gl r k) : full (glMap φ Y) = (full Y).map φ := by
  ext i j
  simp only [full, glMap, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (finSumFinEquiv.symm i) with a | a <;> rcases (finSumFinEquiv.symm j) with b | b <;> simp

end MapLemmas

section Blocks
variable {r : ℕ} {k : Type} [CommRing k]

theorem blocks_full (Y : Gl r k) : blocks (full Y) = Y := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · simp [blocks, full, finSumFinEquiv_symm_last]

theorem full_injective : Function.Injective (full : Gl r k → _) :=
  Function.LeftInverse.injective blocks_full

theorem full_act (g : GL (Fin r) k) (Y : Gl r k) :
    full (act g Y) = embHom r k g * full Y * embHom r k ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  simp only [full, embHom, act, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  congr 1
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]

theorem det_embHom (h : Matrix (Fin r) (Fin r) k) : (embHom r k h).det = h.det := by
  simp [embHom, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Blocks

theorem hasInv_of_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E),
    ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) → HasInv X (inv Z) := by
  intro F E _ _ _ _ _ r Z X μ l ν hν hμ hΔ hX
  have hφ : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hμ' : algebraMap F E μ ≠ 0 := fun h => hμ (hφ (h.trans (map_zero _).symm))
  have hsν : star ν ≠ 0 := by
    intro h; apply hμ'; rw [← hν, h, mul_zero]
  have hinv : inv (liftH X ν l).toGl = inv (glMap (algebraMap F E) (lift Z μ l)) := by
    rw [inv_glMap]; exact hX
  have hD : Delta (inv (glMap (algebraMap F E) (lift Z μ l))) ≠ 0 := by
    rw [inv_glMap, Delta_map]
    exact fun h => hΔ (hφ (h.trans (map_zero _).symm))
  obtain ⟨g, ⟨hg, -⟩, -⟩ := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E (r + 1)).2.2.2.2 _ _ hD hinv
  set G : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (g : Matrix (Fin (r + 1)) (Fin (r + 1)) E) with hG
  set Gi : Matrix (Fin (r + 1)) (Fin (r + 1)) E := ((g⁻¹ : GL (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi, Units.inv_mul]
  have h1 : G * full (glMap (algebraMap F E) Z) * Gi = full X.toGl := by
    rw [full_glMap]; exact congrArg Prod.fst hg
  have h2 : G *ᵥ (fun i => algebraMap F E ((μ • eL r F) i)) = ν • eL r E := congrArg (fun Y => Y.2.1) hg
  have h3 : (fun i => algebraMap F E (eL r F i)) ᵥ* Gi = star (ν • eL r E) := congrArg (fun Y => Y.2.2.1) hg
  have hv1 : (fun i => algebraMap F E ((μ • eL r F) i)) = algebraMap F E μ • eL r E := by
    ext i; simp only [eL, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp
  have hv2 : (fun i => algebraMap F E (eL r F i)) = eL r E := by
    ext i; simp only [eL, Pi.single_apply]; split_ifs <;> simp
  have hv3 : star (ν • eL r E) = star ν • eL r E := by
    ext i; simp only [eL, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp
  rw [hv1] at h2
  rw [hv2, hv3] at h3
  have hcol : ∀ i, G i (Fin.last r) * algebraMap F E μ = ν * eL r E i := by
    intro i
    have := congrFun h2 i
    rw [Matrix.mulVec_smul, eL, Matrix.mulVec_single_one] at this
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply] at this
    rw [mul_comm]
    exact this
  have hrow : eL r E ᵥ* G = (star ν)⁻¹ • eL r E := by
    have hs : star ν • (eL r E ᵥ* G) = eL r E := by
      rw [← Matrix.smul_vecMul, ← h3, Matrix.vecMul_vecMul, hGiG, Matrix.vecMul_one]
    calc eL r E ᵥ* G = (star ν)⁻¹ • (star ν • (eL r E ᵥ* G)) := by
          rw [smul_smul, inv_mul_cancel₀ hsν, one_smul]
      _ = (star ν)⁻¹ • eL r E := by rw [hs]
  have eLL : G (Fin.last r) (Fin.last r) = (star ν)⁻¹ := by
    have := congrFun hrow (Fin.last r)
    simpa [eL, Matrix.single_one_vecMul] using this
  have eLc : ∀ b : Fin r, G (Fin.last r) (Fin.castSucc b) = 0 := by
    intro b
    have := congrFun hrow (Fin.castSucc b)
    simpa [eL, Matrix.single_one_vecMul, Fin.castSucc_ne_last] using this
  have ecL : ∀ a : Fin r, G (Fin.castSucc a) (Fin.last r) = 0 := by
    intro a
    have := hcol (Fin.castSucc a)
    simp only [eL, Pi.single_apply, Fin.castSucc_ne_last, if_false, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hμ'
  set H : Matrix (Fin (r + 1)) (Fin (r + 1)) E := star ν • G with hH
  set h' : Matrix (Fin r) (Fin r) E := H.submatrix Fin.castSucc Fin.castSucc with hh'
  have hHemb : H = embHom r E h' := by
    ext i j
    refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
    all_goals simp [embHom, H, h', finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last, eLL, eLc, ecL, hsν]
  have hdetG : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det G).mp g.isUnit).ne_zero
  have hdet : h'.det ≠ 0 := by
    rw [← det_embHom, ← hHemb, hH, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hsν) hdetG
  set u : GL (Fin r) E := Matrix.GeneralLinearGroup.mkOfDetNeZero h' hdet with hu_def
  have hu : (u : Matrix (Fin r) (Fin r) E) = h' := rfl
  have hGM : G * full (glMap (algebraMap F E) Z) = full X.toGl * G := by
    calc G * full (glMap (algebraMap F E) Z) = G * full (glMap (algebraMap F E) Z) * (Gi * G) := by
          rw [hGiG, Matrix.mul_one]
      _ = (G * full (glMap (algebraMap F E) Z) * Gi) * G := by
          rw [Matrix.mul_assoc (G * full (glMap (algebraMap F E) Z))]
      _ = full X.toGl * G := by rw [h1]
  have hHM : H * full (glMap (algebraMap F E) Z) = full X.toGl * H := by
    rw [hH, Matrix.smul_mul, Matrix.mul_smul, hGM]
  have key : full (act u (glMap (algebraMap F E) Z)) = full X.toGl := by
    rw [full_act, hu, ← hHemb, hHM, hHemb, Matrix.mul_assoc, ← map_mul (embHom r E), ← hu, Units.mul_inv,
      map_one, Matrix.mul_one]
  have hXeq : X.toGl = act u (glMap (algebraMap F E) Z) := (full_injective key).symm
  unfold HasInv
  rw [hXeq, (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E r).1, inv_glMap]

end GlobalTheory.JR.Step
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.borderedInvariants_and_hankelDet_map_ringHom : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ), (∀ Y : Gl r k, inv (GlobalTheory.JR.Step.glMap φ Y) = (inv Y).map φ) ∧ (∀ a : Inv r k, Delta (a.map φ) = φ (Delta a)) := by
  first | exact @GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | exact GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | (intros; apply GlobalTheory.JR.Step.InvMap.inv_and_Delta_map <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_integralGL_mul_diagOne_of_unitIndicator_lift_ne_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 → ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  first | exact @GlobalTheory.JR.GLift.support_lift | exact GlobalTheory.JR.GLift.support_lift | (intros; apply GlobalTheory.JR.GLift.support_lift <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.MatchNotIm

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

theorem full_act (g : GL (Fin r) k) (Y : Gl r k) :
    full (act g Y) = embHom r k (g : Matrix (Fin r) (Fin r) k) * full Y *
      embHom r k ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  simp only [full, act, embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  congr 1
  all_goals (ext i j; simp [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct])

theorem last_eq : (Fin.last r) = finSumFinEquiv (Sum.inr (0 : Fin 1)) := by
  ext; simp

theorem embHom_last_row (g : Matrix (Fin r) (Fin r) k) (j : Fin (r + 1)) :
    embHom r k g (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim j 0]; simp [embHom, Matrix.reindex_apply]

theorem embHom_last_col (g : Matrix (Fin r) (Fin r) k) (i : Fin (r + 1)) :
    embHom r k g i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
  rw [last_eq]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · simp [embHom, Matrix.reindex_apply, Fin.ext_iff, (Fin.is_lt _).ne]
  · rw [Subsingleton.elim i 0]; simp [embHom, Matrix.reindex_apply]

theorem conj_last (g g' : Matrix (Fin r) (Fin r) k) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    (embHom r k g * N * embHom r k g') (Fin.last r) (Fin.last r) = N (Fin.last r) (Fin.last r) := by
  simp [Matrix.mul_apply, embHom_last_row, embHom_last_col]

theorem eL_dot (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    eL r k ⬝ᵥ (N *ᵥ eL r k) = N (Fin.last r) (Fin.last r) := by
  simp [eL, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem full_glMap {k' : Type} [CommRing k'] (φ : k →+* k') (Y : Gl r k) :
    full (glMap φ Y) = (full Y).map φ := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [full, glMap, Matrix.reindex_apply]

end Alg

end GlobalTheory.JR.Step.MatchNotIm

namespace GlobalTheory.JR.Step.MatchNotIm

theorem conj_pow {n : Type} [Fintype n] [DecidableEq n] {k : Type} [CommRing k] (P Q N : Matrix n n k)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (i : ℕ) : (P * N * Q) ^ i = P * N ^ i * Q := by
  induction i with
  | zero => simp [hPQ]
  | succ i ih =>
    rw [pow_succ, ih, pow_succ]
    calc P * N ^ i * Q * (P * N * Q) = P * N ^ i * (Q * P) * N * Q := by simp only [Matrix.mul_assoc]
      _ = P * (N ^ i * N) * Q := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P]

theorem hasInv_liftH : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E),
    ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 →
    HasInv X (inv Z) → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) := by
  intro F E _ _ _ _ _ r Z X μ l ν hν _ _ hΔ hX
  have hΔ' : Delta (inv (glMap (algebraMap F E) Z)) ≠ 0 := by
    rw [InvMap.inv_glMap, InvMap.Delta_map]
    exact (map_ne_zero (algebraMap F E)).2 hΔ
  have hX' : inv X.toGl = inv (glMap (algebraMap F E) Z) := by
    rw [InvMap.inv_glMap]; exact hX
  obtain ⟨g, ⟨hg, -⟩, -⟩ := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E r).2.2.2.2 _ _ hΔ' hX'
  have hfull : full X.toGl = embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := by
    rw [← hg, full_act, full_glMap]
  have hPQ : embHom r E (g : Matrix (Fin r) (Fin r) E) * embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hQP : embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * embHom r E (g : Matrix (Fin r) (Fin r) E)
      = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hs : star (ν • eL r E) = star ν • eL r E := by
    funext j
    simp only [Pi.star_apply, Pi.smul_apply, eL, Pi.single_apply, smul_eq_mul, star_mul']
    split_ifs <;> simp [mul_comm]
  replace hfull : full ((X.1.1, X.2.1, star X.2.1, algebraMap F E X.2.2) : Gl r E) =
      embHom r E (g : Matrix (Fin r) (Fin r) E) * (full Z).map (algebraMap F E) *
      embHom r E ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := hfull
  unfold HasInv
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift]
    rw [hfull]
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, Hn.toGl, liftH, lift, mom]
    rw [hs, hfull, conj_pow _ _ _ hPQ hQP, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_smul, eL_dot, eL_dot, conj_last]
    have hp : ((full Z).map (algebraMap F E)) ^ (i : ℕ) = ((full Z) ^ (i : ℕ)).map (algebraMap F E) := by
      have := map_pow (algebraMap F E).mapMatrix (full Z) (i : ℕ)
      simpa only [RingHom.mapMatrix_apply] using this.symm
    rw [hp, Matrix.map_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, ← hν]
    ring

end GlobalTheory.JR.Step.MatchNotIm
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → IsTest (WeilMix.ptrB M ψ f) := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_isTest | exact GlobalTheory.JR.WeilMix.ptrB_isTest | (intros; apply GlobalTheory.JR.WeilMix.ptrB_isTest <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ π : K.O, ∃ π' : K'.O, algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {π} ∧ IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_unif | exact GlobalTheory.UnitLemma.Unr.exists_unif | (intros; apply GlobalTheory.UnitLemma.Unr.exists_unif <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ x : K.O, ∃ y : K'.O, algebraMap K'.O K'.E y = φ (algebraMap K.O K.E x) := by
  first | exact @GlobalTheory.UnitLemma.Unr.map_int | exact GlobalTheory.UnitLemma.Unr.map_int | (intros; apply GlobalTheory.UnitLemma.Unr.map_int <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.IntBasis Polynomial

theorem _root_.GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
    letI : Algebra K.E K'.E := φ.toAlgebra
    ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E,
      (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
  intro K K' d φ h hd
  let : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, key⟩ := exists_key h
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmax (a : Fin d → K.E) : ∃ m, ∀ k, adicVal K (a k) ≤ adicVal K (a m) :=
    Finite.exists_max (fun k => adicVal K (a k))
  have hli : LinearIndependent K.E w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨m, hm⟩ := hmax g
    have hk := key g m hm
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at hg
    rw [hg, map_zero] at hk
    have hgm : g m = 0 := (Valuation.zero_iff _).1 hk.symm
    intro k
    have hkm := hm k
    rw [hgm, map_zero] at hkm
    exact (Valuation.zero_iff _).1 (le_antisymm hkm zero_le)
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin]
    exact h.2.2.2.2.symm)
  refine ⟨B, fun z => ?_⟩
  have hz : ∑ k, φ (B.repr z k) * w k = z := by
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  obtain ⟨m, hm⟩ := hmax (B.repr z)
  have hv := key _ m hm
  rw [hz] at hv
  rw [← adicVal_le_one_iff K' z]
  constructor
  · intro hzO k
    rw [← adicVal_le_one_iff]
    exact (hm k).trans (hv ▸ hzO)
  · intro hall
    rw [hv]
    exact (adicVal_le_one_iff K _).2 (hall m)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.isUnit_traceForm_discr_unramifiedExt :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (π : K.O) (π' : K'.O),
      algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) →
      IsLocalRing.maximalIdeal K.O = Ideal.span {π} →
      IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} →
      (letI : Algebra K.E K'.E := φ.toAlgebra
       ∀ w : Module.Basis (Fin d) K.E K'.E,
         (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔
           ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) →
         ∃ u : K.O, IsUnit u ∧
           algebraMap K.O K.E u = (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)).det) := by
  apply _root_.GlobalTheory.UnitLemma.Unr.ResDisc.discr_trace_isUnit <;> assumption
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), B.P.Separable → (overExt φ B ψ hψ hσ).P.Separable := by
  first | exact @GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable | exact GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable | (intros; apply GlobalTheory.UnitLemma.Unr.charpoly_overExt_separable <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

theorem _root_.GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by
  first | exact @GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers | exact GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers | (intros; apply GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers <;> assumption)
end

section

open GlobalTheory.UnimodMass

theorem _root_.GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass : ∀ (G : Type) [Group G] (Γ W K : Subgroup G), W ≤ K → Finite (GlobalTheory.UnimodMass.DC Γ W) → (∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) → W.relIndex K ≠ 0 ∧ GlobalTheory.UnimodMass.mass Γ W = (W.relIndex K : ℚ) * GlobalTheory.UnimodMass.mass Γ K := by
  first | exact @GlobalTheory.UnimodMass.mass_eq_relIndex_mul | exact GlobalTheory.UnimodMass.mass_eq_relIndex_mul | (intros; apply GlobalTheory.UnimodMass.mass_eq_relIndex_mul <;> assumption)
end
