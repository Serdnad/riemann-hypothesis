module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.StatementC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.StatementQ

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

def MeasM (A : X → Matrix (Fin n) (Fin n) ℂ) : Prop := Measurable fun x => (Matrix.of.symm (A x) : Fin n → Fin n → ℂ)

theorem measM_iff {A : X → Matrix (Fin n) (Fin n) ℂ} : MeasM A ↔ ∀ i j, Measurable fun x => A x i j := by
  simp only [MeasM, measurable_pi_iff]
  exact Iff.rfl

theorem measM_const (C : Matrix (Fin n) (Fin n) ℂ) : MeasM (fun _ : X => C) := measurable_const

theorem measM_of_cont {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {f : Y → Matrix (Fin n) (Fin n) ℂ} (hf : Continuous fun y => (Matrix.of.symm (f y) : Fin n → Fin n → ℂ))
    {g : X → Y} (hg : Measurable g) : MeasM (fun x => f (g x)) := hf.measurable.comp hg

theorem measM_mul {A B : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) (hB : MeasM B) : MeasM (fun x => A x * B x) := by
  rw [measM_iff] at hA hB ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hA i l).mul (hB l j)

theorem measM_star {A : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) : MeasM (fun x => (A x)ᴴ) := by
  rw [measM_iff] at hA ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.measurable.comp (hA j i)

theorem cont_det : Continuous fun M : Fin n → Fin n → ℂ => (Matrix.of M).det :=
  Continuous.matrix_det continuous_id

theorem cont_adj : Continuous fun M : Fin n → Fin n → ℂ => (Matrix.of.symm (Matrix.of M).adjugate : Fin n → Fin n → ℂ) :=
  Continuous.matrix_adjugate continuous_id

theorem measM_inv {A : X → Matrix (Fin n) (Fin n) ℂ} (hA : MeasM A) : MeasM (fun x => (A x)⁻¹) := by
  have hd : Measurable fun x => (A x).det := cont_det.measurable.comp hA
  have hadj : MeasM (fun x => (A x).adjugate) := cont_adj.measurable.comp hA
  rw [measM_iff] at hadj ⊢
  intro i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hd.inv.mul (hadj i j)

variable {k r : ℕ}

theorem measM_nEich (z : Fin (2 * r + k + 1) → ℂ) {ξ : X → Fin r → ℂ} (hξ : Measurable ξ) :
    MeasM (fun x => C2.nEich k r z (ξ x)) := by
  have hxi : Continuous fun ξ : Fin r → ℂ => C2.xiV k r ξ := by
    refine continuous_pi fun i => ?_
    by_cases h : i.val < r
    · simp only [C2.xiV, h, ↓reduceDIte]
      exact continuous_apply _
    · simp only [C2.xiV, h, ↓reduceDIte]
      exact continuous_const
  have hc : Continuous fun ξ : Fin r → ℂ => (C2.nEich k r z ξ : Matrix _ _ ℂ) := by
    unfold C2.nEich
    have h1 : Continuous fun ξ : Fin r → ℂ => vecMulVec (C2.xiV k r ξ) (star (Hpk k r *ᵥ z)) :=
      hxi.matrix_vecMulVec continuous_const
    have h2 : Continuous fun ξ : Fin r → ℂ => vecMulVec z (star (Hpk k r *ᵥ C2.xiV k r ξ)) :=
      continuous_const.matrix_vecMulVec (continuous_const.matrix_mulVec hxi).star
    have h3 : Continuous fun ξ : Fin r → ℂ => vecMulVec (C2.xiV k r ξ) (star (Hpk k r *ᵥ C2.xiV k r ξ)) :=
      hxi.matrix_vecMulVec (continuous_const.matrix_mulVec hxi).star
    fun_prop
  exact measM_of_cont (f := fun ξ => C2.nEich k r z ξ) hc hξ

theorem measM_submatrix_castSucc {A : X → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hA : MeasM A) :
    MeasM (fun x => (A x).submatrix Fin.castSucc Fin.castSucc) := by
  rw [measM_iff] at hA ⊢
  intro i j
  exact hA _ _

theorem measM_mX {A : X → Matrix (Fin r) (Fin r) ℂ} (hA : MeasM A) : MeasM (fun x => C2.mX k r (A x)) := by
  have hinv : MeasM fun x => ((A x)ᴴ)⁻¹ := measM_inv (measM_star hA)
  rw [measM_iff] at hA hinv ⊢
  intro i j
  simp only [C2.mX]
  split_ifs
  all_goals first | exact measurable_const | exact hA _ _ | exact hinv _ _

theorem measM_tau (z : Fin (2 * r + k + 1) → ℂ) {v : X → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hv : MeasM v) :
    MeasM (fun x => C2.tauM k r z (v x)) := by
  show MeasM fun x => C2.nEich k r z (fun a => v x a.castSucc (Fin.last r)) *
    C2.mX k r ((v x).submatrix Fin.castSucc Fin.castSucc)
  refine measM_mul (measM_nEich z ?_) (measM_mX (measM_submatrix_castSucc hv))
  exact Measurable.of_eval fun a => (measM_iff.1 hv) _ _

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM
end

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

theorem determinant_nonzero : C2.DetNonzero := by
  intro k r z z' hz hz' g hG hdet
  have hD : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := rfl
  have h1 : Complex.normSq (Dmin k r z z' g (Fin.last (r + 1))) = 0 := by
    rw [hD, hdet, map_zero]
  unfold Gf at hG
  rw [h1] at hG
  have h2 := mul_nonneg (mul_nonneg hz.2.le hz'.2.le)
    (Complex.normSq_nonneg (Dmin k r z z' g ⟨r, by omega⟩))
  linarith

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

def lowP {m : ℕ} (w : Equiv.Perm (Fin m)) (y : C2.LPidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  C2.lowOf (fun q : C2.LPidx w => q.1) y

def lowS {m : ℕ} (w : Equiv.Perm (Fin m)) (x : C2.Lstidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  C2.lowOf (fun q : C2.Lstidx w => q.1) x

def utc {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : G.UT m → ℂ := fun q => u q.1.1 q.1.2

def lsc {m : ℕ} (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) : C2.Lstidx w → ℂ := fun q => l q.1.1 q.1.2

def SplitUT : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)), ∃ e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT m → ℂ),
    MeasurePreserving e volume volume ∧ ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ

def UTLeft : Prop :=
  ∀ (m : ℕ) (a : Matrix (Fin m) (Fin m) ℂ), a ∈ C2.UTset m →
    MeasurePreserving (fun u : G.UT m → ℂ => utc (a * G.upper u)) volume volume

def LstLeft : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) → ∀ x0 : C2.Lstidx w → ℂ,
    MeasurePreserving (fun x : C2.Lstidx w → ℂ => lsc w (lowS w x0 * lowS w x)) volume volume ∧
    ∀ x, lowS w x0 * lowS w x = lowS w (lsc w (lowS w x0 * lowS w x))

def MinorsLU : Prop :=
  ∀ (r : ℕ) (L M U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), L ∈ C2.LTset (r + 1) → U ∈ C2.UTset (r + 1) →
    (L * M * U).det = M.det ∧
      ((L * M * U).submatrix Fin.castSucc Fin.castSucc).det = (M.submatrix Fin.castSucc Fin.castSucc).det

def PhiTopCoords : Prop :=
  ∀ (m : ℕ) (σ w : Equiv.Perm (Fin m)) (d d' : Fin m → ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : G.Mat m → V), (∀ a, d' a ≠ 0) → U.hMat σ d = C2.monoP w d' →
    U.PhiTop (p := m) (s := 0) U.betaU σ d Φ (fun x => x.elim0) =
      ∫ q : (C2.LPidx w → ℂ) × (G.UT m → ℂ),
        (C2.psiC cStd (C2.simpleUp (lowP w q.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper q.2)))) •
          Φ (Matrix.of.symm (lowP w q.1 * C2.monoP w d' * G.upper q.2))

def ExistsHaarStabilizer : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∃ μ0 : Measure (Mt k r), B.IsHaarOn (C2.N0set k r z) μ0

def DisintN : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∀ μ0 μN : Measure (Mt k r),
    B.IsHaarOn (C2.N0set k r z) μ0 → B.IsHaarOn (Nset k r) μN →
    ∃ c : NNReal, 0 < c ∧ μN = c • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r z (G.upper p.1) * Matrix.of p.2))

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem sfinite_of_isHaarOn {k r : ℕ} (U : Set (B.Mat k r)) (μ : Measure (Mt k r)) (h : B.IsHaarOn U μ) :
    SFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

end Formalism.FourierDecayAlt.P5
end
end

section

namespace Formalism.FourierDecayAlt.P

open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C

open scoped ComplexOrder

noncomputable section

open Classical

namespace Cx1

theorem psd_pullback {α β : Type} (Y : Finset α) (φ : α → β) (k : β → β → ℂ) (Z : Finset β)
    (hZ : ∀ x ∈ Y, φ x ∈ Z) (h : TB.PSDOn Z k) : TB.PSDOn Y (fun x y => k (φ x) (φ y)) := by
  simp only [TB.PSDOn] at h ⊢
  exact h.submatrix (fun x : Y => (⟨φ x, hZ x x.2⟩ : Z))

theorem psd_zero {α : Type} (Y : Finset α) : TB.PSDOn Y (fun _ _ => (0 : ℂ)) := by
  simp only [TB.PSDOn]
  exact Matrix.PosSemidef.zero

end Cx1

theorem gram_positive_semidefinite : C.GramPSDOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hP _ Kr hK0 Th e ε hε i w Y
  show TB.PSDOn Y (S.gram ε i w.1)
  have prodPSD : ∀ (s : Finset (Fin S.f)) (k : Fin S.f → TB.Pt E → TB.Pt E → ℂ),
      (∀ v, TB.PSDOn Y (k v)) → TB.PSDOn Y (fun p q => ∏ v ∈ s, k v p q) := by
    intro s k hk
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, TB.PSDOn]
      let A : Matrix Unit Y ℂ := Matrix.of fun _ _ => 1
      have h2 := Matrix.posSemidef_conjTranspose_mul_self A
      convert h2 using 1
      ext x y
      simp [A, Matrix.mul_apply]
    | @insert a s ha ih =>
      simp only [TB.PSDOn] at ih ⊢
      have h1 : (Matrix.of fun x y : Y => ∏ v ∈ insert a s, k v x y) =
          (Matrix.of fun x y : Y => k a x y).hadamard (Matrix.of fun x y : Y => ∏ v ∈ s, k v x y) := by
        ext x y
        simp [Finset.prod_insert ha, Matrix.hadamard]
      rw [h1]
      exact (hk a).hadamard ih
  by_cases hi : i ≤ S.G.r + 1
  · have hg : S.gram ε i w.1 =
        fun p q => ∏ v, S.gramLoc v ε i (w.1 v) (loc (S.σ v) p) (loc (S.σ v) q) := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact prodPSD Finset.univ _ fun v =>
      Cx1.psd_pullback Y (loc (S.σ v)) _ _ (fun x hx => Finset.mem_image_of_mem _ hx)
        (hP v ε hε i hi w _)
  · have hg : S.gram ε i w.1 = fun _ _ => 0 := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact Cx1.psd_zero Y

theorem words_pos_of_parts : C.WordsPosOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG Kr hK0 Th e w
  show 0 < Word.size S.P w.1
  unfold Word.size
  apply Finset.prod_pos
  intro v _
  apply List.prod_pos
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  apply abs_pos.mpr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
  have hadm := w.2.1.1 v j hj
  by_cases hb : ((w.1 v)[j]'hj).1 = true
  · rw [if_pos hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact ((hG v).2.2.2.2.2 _ hy).2.2.1
  · rw [if_neg hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := ((hG v).2.2.2.2.2 _ hy).2.2.2
    rwa [sub_add_cancel] at this

theorem wave_estimate_of_integral : C.EstWaveOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG hI hP Kr hK0 Th e ε hε i hi1 hi2 w hw hcnt
  obtain ⟨θ, hθ, hb⟩ := hP ε hε i hi1 hi2 w hw hcnt
  exact ⟨θ, hθ, fun Y hY κ hκ => ⟨(hI ε hε i hi1 hi2 w Y hY κ hκ).2,
    fun l hl hl0 => ⟨S.bigPlaces i l, hb Y hY κ hκ l hl hl0⟩⟩⟩

theorem lift_estimate_of_base : C.EstLiftOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S h Kr hK0 Th e
  exact h

theorem block_estimate_of_base : C.EstBlockOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S C₄ h Kr hK0 Th e
  exact h

theorem level_zero_estimate_product : C.EstEOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S jv hG hE Kr hK0 Th e w _
  have hgram : ∀ ε, (S.mkData Kr hK0 Th e).gram ε 0 w [] [] = ∏ v, (S.pd v).RR ε 0 (w.1 v) [] [] := by
    intro ε
    show S.gram ε 0 w.1 [] [] = _
    simp [HidaSetting.gram, HidaSetting.gramLoc, loc, nLoc, nAux]
  have hsize : (S.mkData Kr hK0 Th e).wt w = ∏ v, S.sizeAt v (w.1 v) := rfl
  have hpos : 0 < ∏ v, S.sizeAt v (w.1 v) := by
    rw [← hsize]
    exact words_pos_of_parts E Wp Wq S hG Kr hK0 Th e w
  have hlim : Tendsto (fun ε => ∏ v, (S.pd v).RR ε 0 (w.1 v) [] []) (𝓝[>] 0)
      (𝓝 (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ))) :=
    tendsto_finsetProd _ (fun v _ => hE w v)
  have hre := ((Complex.continuous_re.tendsto _).comp hlim).div_const (∏ v, S.sizeAt v (w.1 v))
  have key : (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ)).re /
      (∏ v, S.sizeAt v (w.1 v)) = ∏ v, jv v := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib,
      mul_div_cancel_left₀ _ hpos.ne']
  rw [key] at hre
  simp_rw [hgram, hsize]
  exact hre

theorem cutoff_of_parts : C.CutoffOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S H _ _ Vt hPG Kr hK0 Th e Y hY
  filter_upwards [hPG Y hY] with ε hε p hp q hq _
  exact hε p hp q hq

end

end Formalism.FourierDecayAlt.P
end
