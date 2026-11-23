module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle108
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle109
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

@[expose] public section

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F) (L U : ℕ), 1 ≤ L → ∀ (z : Fin h → F) (r : Fin h), (rowS p ϖ lam L U (winPt p π L z) r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) = gsum (p ^ h) (L + U) (coefB p ϖ lam π L U) z r := by
  first | exact @GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | exact GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB | (intros; apply GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.continuousOn_hermitianBlockMatrixOfInvariants : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E), ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det) → ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := by
  first | exact @GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det | exact GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det | (intros; apply GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step.UNormal

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

theorem exists_algebraMap_of_star_eq (y : E) (hy : star y = y) : ∃ x : F, algebraMap F E x = y := by
  have hU : Unram F E := inferInstance
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  let S : Submodule F E :=
    { carrier := {z | star z = z}
      add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [star_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq] at *
        rw [Algebra.smul_def, star_mul, hz, hU.star_fix, mul_comm] }
  have h1 : (Submodule.span F {(1 : E)}) ≤ S := by
    rw [Submodule.span_le]; intro z hz; simp only [Set.mem_singleton_iff] at hz; subst hz
    show star (1 : E) = 1; exact star_one E
  have hne : S ≠ ⊤ := by
    obtain ⟨z, hz⟩ := hU.star_ne
    intro h; apply hz; have : z ∈ S := h ▸ Submodule.mem_top; exact this
  have hlt : Module.finrank F S < 2 := by
    rw [← hU.finrank_eq]; exact Submodule.finrank_lt hne
  have hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
  have heq : Submodule.span F {(1 : E)} = S :=
    Submodule.eq_of_le_of_finrank_le h1 (by omega)
  have hyS : y ∈ S := hy
  rw [← heq, Submodule.mem_span_singleton] at hyS
  obtain ⟨c, hc⟩ := hyS
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

end GlobalTheory.JR.Step.UNormal

noncomputable section

namespace GlobalTheory.JR.Step.UNormal

section Full
variable {r : ℕ} {k : Type} [CommRing k]

theorem full_cc (Y : Gl r k) (i j : Fin r) : full Y (Fin.castSucc i) (Fin.castSucc j) = Y.1 i j := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_cl (Y : Gl r k) (i : Fin r) : full Y (Fin.castSucc i) (Fin.last r) = Y.2.1 i := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_lc (Y : Gl r k) (j : Fin r) : full Y (Fin.last r) (Fin.castSucc j) = Y.2.2.1 j := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_ll (Y : Gl r k) : full Y (Fin.last r) (Fin.last r) = Y.2.2.2 := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

end Full

end GlobalTheory.JR.Step.UNormal

noncomputable section

namespace GlobalTheory.JR.Step


open GlobalTheory.JR.Step.UNormal in
theorem uNormal : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (X : Hn (r + 1) F E) (a : Inv (r + 1) F), HasInv X a →
    ‖a.2.1 0‖ = 1 → ∃ (g : Matrix.unitaryGroup (Fin (r + 1)) E) (X' : Hn r F E) (ν : E),
      ν * star ν = algebraMap F E (a.2.1 0) ∧ actU g X = GlobalTheory.JR.Step.liftH X' ν a.2.2 := by
  intro F E _ _ _ _ _ r X a hX ha
  have h0 : star X.2.1 ⬝ᵥ X.2.1 = algebraMap F E (a.2.1 0) := by
    have := congrArg (fun p => p.2.1 0) hX
    simpa [inv, mom, Hn.toGl, Inv.map] using this
  have hl : X.2.2 = a.2.2 := by
    have := congrArg (fun p => p.2.2) hX
    simp only [inv, Hn.toGl, Inv.map] at this
    exact (algebraMap F E).injective this
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E (a.2.1 0) ha
  have ha0 : algebraMap F E (a.2.1 0) ≠ 0 := by
    rw [map_ne_zero]
    intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hνn : star (ν • eL r E) ⬝ᵥ (ν • eL r E) = ν * star ν := by
    simp [eL, dotProduct, Pi.single_apply, mul_comm]
  have hv : star X.2.1 ⬝ᵥ X.2.1 = star (ν • eL r E) ⬝ᵥ (ν • eL r E) := by
    rw [h0, hνn, hν]
  obtain ⟨g, hg⟩ := GlobalTheory.unitary_transitive_of_norm F E (r + 1) X.2.1 _ hv (h0 ▸ ha0)
  set M := g.1 * X.1.1 * star g.1 with hMdef
  have hM : Mᴴ = M := IsSelfAdjoint.conjugate X.1.2 g.1
  have hMe : ∀ i j, M j i = star (M i j) := by
    intro i j
    have := congrFun (congrFun hM j) i
    rw [conjTranspose_apply] at this
    exact this.symm
  obtain ⟨l', hl'⟩ := exists_algebraMap_of_star_eq (F := F) (M (Fin.last r) (Fin.last r))
    (hMe _ _).symm
  have hsub : M.submatrix Fin.castSucc Fin.castSucc ∈ selfAdjoint (Matrix (Fin r) (Fin r) E) := by
    rw [selfAdjoint.mem_iff, star_eq_conjTranspose, conjTranspose_submatrix, hM]
  refine ⟨g, (⟨M.submatrix Fin.castSucc Fin.castSucc, hsub⟩, fun i => M (Fin.castSucc i) (Fin.last r), l'), ν, hν, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Subtype.ext
    show M = full _
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rw [full_ll]; simp [Hn.toGl, hl']
      | cast j => rw [full_lc]; simp [Hn.toGl, hMe (Fin.castSucc j) (Fin.last r)]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [full_cl]; simp [Hn.toGl]
      | cast j => rw [full_cc]; simp [Hn.toGl]
  · exact hg
  · exact hl

end GlobalTheory.JR.Step
end
end
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DeltaLift

variable {k : Type} [Field k] {r : ℕ}

theorem full_cc (Z : Gl r k) (i j : Fin r) : full Z (Fin.castSucc i) (Fin.castSucc j) = Z.1 i j := by
  simp [full]

theorem full_cl (Z : Gl r k) (i : Fin r) : full Z (Fin.castSucc i) (Fin.last r) = Z.2.1 i := by
  simp [full]

theorem full_lc (Z : Gl r k) (j : Fin r) : full Z (Fin.last r) (Fin.castSucc j) = Z.2.2.1 j := by
  simp [full]

theorem full_mulVec_cs (Z : Gl r k) (V : Fin (r + 1) → k) (i : Fin r) :
    (full Z *ᵥ V) (Fin.castSucc i) = (Z.1 *ᵥ (fun j => V (Fin.castSucc j))) i + V (Fin.last r) * Z.2.1 i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, full_cc, full_cl]
  ring

theorem vecMul_full_cs (Z : Gl r k) (V : Fin (r + 1) → k) (j : Fin r) :
    (V ᵥ* full Z) (Fin.castSucc j) = ((fun i => V (Fin.castSucc i)) ᵥ* Z.1) j + V (Fin.last r) * Z.2.2.1 j := by
  simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, full_cc, full_lc]

theorem dot_split (W V : Fin (r + 1) → k) :
    W ⬝ᵥ V = (fun i => W (Fin.castSucc i)) ⬝ᵥ (fun i => V (Fin.castSucc i)) + W (Fin.last r) * V (Fin.last r) := by
  simp only [dotProduct, Fin.sum_univ_castSucc]

theorem dot_pow_all (A : Matrix (Fin r) (Fin r) k) (w b : Fin r → k)
    (h : ∀ i < r, w ⬝ᵥ (A ^ i *ᵥ b) = 0) (m : ℕ) : w ⬝ᵥ (A ^ m *ᵥ b) = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [dotProduct]
  have hP : A.charpoly.Monic := Matrix.charpoly_monic A
  have hdeg : A.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim A
  have hne : A.charpoly ≠ 1 := by
    intro h1; rw [h1, Polynomial.natDegree_one] at hdeg; omega
  have hlt : (Polynomial.X ^ m %ₘ A.charpoly).natDegree < r := by
    simpa [hdeg] using Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ m) hP hne
  rw [Matrix.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hlt]
  have key : ∀ (s : Finset ℕ), (∀ i ∈ s, i < r) → ∀ c : ℕ → k,
      w ⬝ᵥ ((∑ i ∈ s, c i • A ^ i) *ᵥ b) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ c; simp
    | insert a s ha ih =>
      intro hs c
      rw [Finset.sum_insert ha, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul,
        h a (hs a (Finset.mem_insert_self a s)), ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) c]
      simp
  exact key _ (fun i hi => Finset.mem_range.mp hi) _

theorem det_Bm_lift (Z : Gl r k) (μ l : k) (h : (Bm Z).det = 0) :
    (Bm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := Bm Z)).mpr h
  have hw' : ∀ m, w ⬝ᵥ (Z.1 ^ m *ᵥ Z.2.1) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hw ⟨i, hi⟩
    simpa [vecMul, Bm, dotProduct] using this
  set A' := full Z
  let x : ℕ → Fin r → k := fun j i => (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.castSucc i)
  have hx : ∀ j m, w ⬝ᵥ (Z.1 ^ m *ᵥ x j) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : x 0 = 0 := by
        funext i; simp [x, GlobalTheory.JR.Step.eL, Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, mulVec_zero, dotProduct_zero]
    | succ j ih =>
      intro m
      have hxs : x (j + 1) = Z.1 *ᵥ x j + (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.last r) • Z.2.1 := by
        funext i
        simp only [x, pow_succ', ← mulVec_mulVec]
        rw [full_mulVec_cs]
        simp [mul_comm]
      rw [hxs, mulVec_add, dotProduct_add, mulVec_mulVec, ← pow_succ, ih, mulVec_smul, dotProduct_smul, hw']
      simp
  refine (Matrix.exists_vecMul_eq_zero_iff (M := Bm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 w i, ?_, ?_⟩
  · intro h0
    apply hw0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · have e : (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ᵥ* Bm (GlobalTheory.JR.Step.lift Z μ l)
        = fun j : Fin (r + 1) => μ * (w ⬝ᵥ x (j : ℕ)) := by
      funext j
      show (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ⬝ᵥ (A' ^ (j : ℕ) *ᵥ (μ • GlobalTheory.JR.Step.eL r k)) = _
      rw [mulVec_smul, dotProduct_smul, dot_split]
      simp [x, smul_eq_mul]
    rw [e]
    funext j
    simpa using congrArg (μ * ·) (hx j 0)

theorem det_Cm_lift (Z : Gl r k) (μ l : k) (h : (Cm Z).det = 0) :
    (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Cm Z)).mpr h
  have hv' : ∀ m, Z.2.2.1 ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    rw [dotProduct_mulVec]
    simpa [mulVec, Cm, dotProduct] using this
  set A' := full Z
  let u : ℕ → Fin r → k := fun j i => (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.castSucc i)
  have hu : ∀ j m, u j ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : u 0 = 0 := by
        funext i
        simp only [u, pow_zero, vecMul_one, GlobalTheory.JR.Step.eL]
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, zero_dotProduct]
    | succ j ih =>
      intro m
      have hus : u (j + 1) = u j ᵥ* Z.1 + (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.last r) • Z.2.2.1 := by
        funext i
        simp only [u, pow_succ, ← vecMul_vecMul]
        rw [vecMul_full_cs]
        simp [mul_comm]
      rw [hus, add_dotProduct, ← dotProduct_mulVec, mulVec_mulVec, ← pow_succ', ih, smul_dotProduct, hv']
      simp
  refine (Matrix.exists_mulVec_eq_zero_iff (M := Cm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 v i, ?_, ?_⟩
  · intro h0
    apply hv0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · funext j
    simp only [mulVec, Cm, GlobalTheory.JR.Step.lift, Matrix.of_apply]
    rw [dot_split]
    simpa [u, A'] using hu j 0

end GlobalTheory.JR.DeltaLift


open GlobalTheory.JR.DeltaLift in
theorem GlobalTheory.JR.Step.delta_lift_ne : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k),
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  intro k _ r Z μ l h
  have e1 := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k (r + 1)).2.2.1 (GlobalTheory.JR.Step.lift Z μ l)
  have e0 := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k r).2.2.1 Z
  unfold Delta at h ⊢
  rw [← e1, det_mul] at h
  rw [← e0, det_mul]
  have hC : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := left_ne_zero_of_mul h
  have hB : (Bm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := right_ne_zero_of_mul h
  exact mul_ne_zero (fun hc => hC (det_Cm_lift Z μ l hc)) (fun hb => hB (det_Bm_lift Z μ l hb))
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitaryActHermitianBlock_diagOne_liftLastBasis : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F), actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := by
  first | exact @GlobalTheory.JR.Step.actU_uEmb_liftH | exact GlobalTheory.JR.Step.actU_uEmb_liftH | (intros; apply GlobalTheory.JR.Step.actU_uEmb_liftH <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.borderedConjugation_diagOne_liftBlockMatrix : ∀ (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k), act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  first | exact @GlobalTheory.JR.Step.ActEmbLift.act_emb_lift | exact GlobalTheory.JR.Step.ActEmbLift.act_emb_lift | (intros; apply GlobalTheory.JR.Step.ActEmbLift.act_emb_lift <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 → ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  first | exact @GlobalTheory.JR.Step.glNormal_of_ne_zero | exact GlobalTheory.JR.Step.glNormal_of_ne_zero | (intros; apply GlobalTheory.JR.Step.glNormal_of_ne_zero <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding : ∀ (F : Type) [NontriviallyNormedField F] (r : ℕ), Topology.IsClosedEmbedding (GlobalTheory.JR.Step.emb r F) := by
  first | exact @GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | exact GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb | (intros; apply GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isClosedEmbedding_diagOneUnitaryGroupEmbedding : ∀ (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E], Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := by
  first | exact @GlobalTheory.JR.Step.isClosedEmbedding_uEmb | exact GlobalTheory.JR.Step.isClosedEmbedding_uEmb | (intros; apply GlobalTheory.JR.Step.isClosedEmbedding_uEmb <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.preimage_diagOneGeneralLinearEmbedding_integralGLSet : ∀ (F : Type) [NormedField F] (r : ℕ), ⇑(GlobalTheory.JR.Step.emb r F) ⁻¹' glO (r + 1) F = glO r F := by
  first | exact @GlobalTheory.JR.GLift.emb_preimage_glO | exact GlobalTheory.JR.GLift.emb_preimage_glO | (intros; apply GlobalTheory.JR.GLift.emb_preimage_glO <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_liftBlockMatrixWithLastBasis : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 → unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  first | exact @GlobalTheory.JR.UnitGLift.unitG_lift | exact GlobalTheory.JR.UnitGLift.unitG_lift | (intros; apply GlobalTheory.JR.UnitGLift.unitG_lift <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitIndicatorHermitianBlock_liftLastBasis_of_norm_le_one : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ ≤ 1 → unitU (r + 1) F E (GlobalTheory.JR.Step.liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := by
  first | exact @GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one | exact GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one | (intros; apply GlobalTheory.JR.Step.unitU_liftH_of_norm_le_one <;> assumption)
end
