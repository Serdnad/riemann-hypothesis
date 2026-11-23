module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.StatementTL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLG

open Formalism.FourierDecayAlt.P.HermitianFormRankFour

variable {k r : ℕ}

def cvec2 (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ) : JJ r ⊕ Unit → Fin (2 * r + k + 1) → ℂ :=
  Sum.elim (cvec k r z) (fun _ => e)

def cvec2' (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ) : JJ r ⊕ Unit → Fin (2 * r + k + 1) → ℂ :=
  Sum.elim (cvec' k r z) (fun _ => e)

theorem sum_unitB {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    colM Bs * B * ((colM Bs)ᴴ * Hpk k r) = ∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2 := by
  ext i j
  have hu : ∀ a b, unitB (Hpk k r) Bs a b i j = Bs a i * ∑ q, star (Bs b q) * Hpk k r q j := by
    intro a b
    simp only [unitB, Matrix.of_apply, herm, dotProduct, Matrix.mulVec, bvec, Pi.star_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Pi.single_apply]
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, hu, Matrix.mul_apply, colM, Matrix.of_apply,
    Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem stab_exp {z e : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (he : inWb k r e)
    (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z, e] Bs) {h : Mx k r} (hh : h ∈ UWset k r z) (hhe : h *ᵥ e = e) :
    ∃ B : Matrix (Fin (k - 1)) (Fin (k - 1)) ℂ, Bᴴ = -B ∧
      NormedSpace.exp (colM Bs * B * ((colM Bs)ᴴ * Hpk k r)) = h := by
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    intro e0
    unfold Tz at hT
    rw [e0] at hT
    simp at hT
  have hBz : IsFrameOf k r [z] Bs := ⟨hB.1, hB.2.1, fun a v hv => hB.2.2 a v (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; exact Or.inl hv)⟩
  have hE : IsFrameOf k r [z] (fun _ : Fin 1 => e) := ⟨fun _ => he, fun a b => by
    simp [Subsingleton.elim a b, hee], fun _ v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    exact hez⟩
  have hBe : ∀ a, herm (Hpk k r) (Bs a) e = 0 := fun a => hB.2.2 a e (by simp)
  have hBe' : ∀ a, herm (Hpk k r) e (Bs a) = 0 := fun a => by rw [← Qx2.herm_star, hBe a, star_zero]
  have g1 : (colM Bs)ᴴ * Hpk k r * colM Bs = 1 := by
    ext a b
    rw [gramM_apply, hB.2.1, Matrix.one_apply]
    simp [eq_comm]
  have g2 : (colM Bs)ᴴ * Hpk k r * colM (cvec2 k r z e) = 0 := by
    ext a j
    rw [gramM_apply]
    rcases j with j | _
    · exact gram_VC hBz a j
    · exact hBe' a
  have g3 : (colM (cvec2' k r z e))ᴴ * Hpk k r * colM Bs = 0 := by
    ext j a
    rw [gramM_apply]
    rcases j with j | _
    · exact gram_CV hBz a j
    · exact hBe a
  have g4 : (colM (cvec2' k r z e))ᴴ * Hpk k r * colM (cvec2 k r z e) = 1 := by
    ext i j
    rw [gramM_apply, Matrix.one_apply]
    rcases i with i | _ <;> rcases j with j | _
    · simp only [cvec2, cvec2', Sum.elim_inl, Sum.inl.injEq]
      exact gram_CC hz hzz i j
    · simp only [cvec2, cvec2', Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact gram_CV hE 0 i
    · simp only [cvec2, cvec2', Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact gram_VC hE 0 j
    · simp [cvec2, cvec2', hee]
  have hJ : Fintype.card (JJ r ⊕ Unit) ≤ Fintype.card (Fin (2 * r + k + 1)) := by
    have h1 := Matrix.rank_mul_le_right ((colM (cvec2' k r z e))ᴴ * Hpk k r) (colM (cvec2 k r z e))
    rw [g4, Matrix.rank_one] at h1
    exact h1.trans (Matrix.rank_le_card_height _)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at hJ
  have hc := complete (Fintype.equivOfCardEq (by simp; omega)) g1 g2 g3 g4
  have hC : h * colM (cvec2 k r z e) = colM (cvec2 k r z e) := by
    rw [mul_colM]
    congr 1
    funext j
    rcases j with j | _
    · exact fix_c hh j
    · exact hhe
  have hC' : h * colM (cvec2' k r z e) = colM (cvec2' k r z e) := by
    rw [mul_colM]
    congr 1
    funext j
    rcases j with j | _
    · exact fix_c' hh j
    · exact hhe
  have hCd := dual_fix hh.1 hC'
  obtain ⟨e1, e2⟩ := decomp hc g3 h hC hCd
  obtain ⟨B, hBs, hBe⟩ := unitary_log _ (unitary_of Qx8.hpk_herm hh.1 g1 e1)
  refine ⟨B, hBs, ?_⟩
  rw [exp_lift hc g1 g2 B, hBe, ← e2]

end KLG

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def rcAct {k p ρ : ℕ} (y : B.Mat k ρ) (x : U.RC k p ρ) : U.RC k p ρ := (fun v a => (y * Matrix.of x.1) v a, x.2)

def lhOf {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  U.wP σ * U.lowW σ v * (U.wP σ)⁻¹

def MMapEmbG : Prop := ∀ (k p ρ : ℕ) (Z : Matrix (Fin p) (Fin p) ℂ) (γ y₁ y₂ : B.Mat k ρ),
  U.mMap k p ρ Z (y₁ * γ * y₂) = U.embG k p ρ y₁ * U.mMap k p ρ Z γ * U.embG k p ρ y₂

def MMapLZU : Prop := ∀ (k p ρ : ℕ) (l Z u : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ), IsUnit l.det →
  U.mMap k p ρ (l * Z * u) γ = U.muP k p ρ (lᴴ)⁻¹ * U.mMap k p ρ Z γ * U.muP k p ρ u

def EmbGMuP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (q : Matrix (Fin p) (Fin p) ℂ),
  U.embG k p ρ y * U.muP k p ρ q = U.muP k p ρ q * U.embG k p ρ y

def EmbGRn : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (x : U.RC k p ρ), yᴴ * Hpk k ρ * y = Hpk k ρ →
  U.embG k p ρ y * U.Rn k p ρ x = U.Rn k p ρ (rcAct y x) * U.embG k p ρ y

def HeadHEq : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (v : U.LW σ → ℂ) (u : G.UT p → ℂ),
  U.headH σ d v u = lhOf σ v * U.hMat σ d * G.upper u ∧ G.IsLowerUni (lhOf σ v)

def ZjHZero : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : U.XiH p 0 σ) (Z : G.Mat 0),
  U.ZjH σ d η Z = U.headH σ d η.2.1 η.2.2

def GaXiSplit : Prop := ∀ (k p ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : U.Xi k p 0 ρ σ) (Z : G.Mat 0)
  (h ν h' ν' g : B.Mat k ρ), IsUnit h.det → IsUnit ν.det → h'ᴴ * Hpk k ρ * h' = Hpk k ρ →
  U.gaXi k ρ σ d ξ Z (h⁻¹ * ν⁻¹ * g * ν' * h') =
    (U.Rn k p ρ (-ξ.1.1) * U.muP k p ρ (lhOf σ ξ.2.2.1)ᴴ⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)) *
      U.mMap k p ρ (U.hMat σ d) g *
      (U.embG k p ρ ν' * U.muP k p ρ (G.upper ξ.2.2.2) * U.Rn k p ρ (rcAct h' ξ.1.2)) * U.embG k p ρ h'

def LeftMem : Prop := ∀ (k p ρ : ℕ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.RC k p ρ) (l : Matrix (Fin p) (Fin p) ℂ)
  (h ν : B.Mat k ρ), inWb k ρ z → G.IsLowerUni l → h ∈ UWset k ρ z → ν ∈ Nset k ρ →
  U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹) ∈ Sset k (p + ρ) (liftVec k p ρ z)

def PsiRight : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (ν' : B.Mat k ρ) (u : G.UT p → ℂ)
  (x : U.RC k p ρ), inWb k ρ z' → ν' ∈ Nset k ρ →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.embG k p ρ ν' * U.muP k p ρ (G.upper u) * U.Rn k p ρ x) =
    psi k ρ z' cStd ν' * psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u)) *
      psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiRnAct : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (h' : B.Mat k ρ) (x : U.RC k p ρ),
  inWb k ρ z' → h' ∈ UWset k ρ z' →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ (rcAct h' x)) = psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiMuP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (u : G.UT p → ℂ), inWb k ρ z' →
  star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u))) = G.psi U.betaU (U.supS (G.upper u))

def MuNLeft : Prop := ∀ (k p ρ : ℕ),
  D.muN k (p + ρ) = ((U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ))).map
    (fun x => Matrix.of.symm (U.embG k p ρ (Matrix.of x.2.2) * U.muP k p ρ (G.upper x.2.1) * U.Rn k p ρ x.1))

def RcActMP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ), ‖y.det‖ = 1 →
  MeasurePreserving (rcAct (p := p) y) (U.muRC k p ρ) (U.muRC k p ρ)

def RightMP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (μj : Measure (Mt k ρ)) (μ0' : Measure (Mt k (p + ρ))),
  B.IsHaarOn (UWset k ρ z') μj → μj Set.univ = 1 → μ0' = μj.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
  MeasurePreserving
    (fun y : (Mt k ρ × Mt k ρ) × (U.RC k p ρ × (G.UT p → ℂ)) =>
      (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl y.1.1,
        Matrix.of.symm (U.embG k p ρ (Matrix.of y.1.2) * U.muP k p ρ (G.upper y.2.2) *
          U.Rn k p ρ (rcAct (Matrix.of y.1.1) y.2.1))))
    ((μj.prod (D.muN k ρ)).prod ((U.muRC k p ρ).prod volume)) (μ0'.prod (D.muN k (p + ρ)))

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

theorem glev_last_eq (r : ℕ) : Glev k r (Fin.last r) = B2.UWb k r := by
  ext g
  simp only [Glev, B2.UWb, Fin.val_last]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => h2 a a.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a _ => h2 a⟩

theorem image_glev : ιLev k 1 ρ '' Glev k ρ (Fin.last ρ) = Glev k (1 + ρ) (Fin.last (1 + ρ)) := by
  rw [glev_last_eq, glev_last_eq, Formalism.FourierDecayAlt.P.LongWeylElement.uWbRec k ρ]

theorem map_levM_smul {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs) :
    ∃ c : NNReal, μs.map (B2.levM k ρ) = c • μ := by
  rw [glev_last_eq] at hμs hμ
  have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k ρ
  obtain ⟨_, hν⟩ := Formalism.FourierDecayAlt.P.levi_haar_measure_exists k ρ _ μs hU hμs
  have e : ιLev k 1 ρ '' B2.UWb k ρ = B2.UWb k (1 + ρ) := by
    rw [← glev_last_eq, ← glev_last_eq, image_glev]
  rw [e] at hν
  exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (1 + ρ) _ μ _ (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k (1 + ρ)) hμ hν.conc
    hν.left hν.finite_compact

theorem zeta_levM (z z' : Fin (2 * ρ + k + 1) → ℂ) (x : Mt k ρ) :
    zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of (B2.levM k ρ x)) =
      zetaL k ρ z z' (Fin.last ρ) (Matrix.of x) := by
  have hf : ∀ (r : ℕ) (v : Fin (2 * r + k + 1) → ℂ), fvec k r v (Fin.last r) = v := fun r v => by
    simp [fvec]
  change herm (Hpk k (1 + ρ)) (ιLev k 1 ρ (Matrix.of x) *ᵥ fvec k (1 + ρ) (liftVec k 1 ρ z') (Fin.last (1 + ρ)))
      (fvec k (1 + ρ) (liftVec k 1 ρ z) (Fin.last (1 + ρ))) =
    herm (Hpk k ρ) (Matrix.of x *ᵥ fvec k ρ z' (Fin.last ρ)) (fvec k ρ z (Fin.last ρ))
  rw [hf, hf, hf, hf, Formalism.FourierDecayAlt.P.B2x5.lev_lift, Formalism.FourierDecayAlt.P.B2x4.herm_lift]

theorem measurable_levM : Measurable (B2.levM k ρ) := by
  exact (Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ).measurable

theorem continuous_zetaL (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun x : Mt k r => zetaL k r z z' (Fin.last r) (Matrix.of x) := by
  exact (LinearMap.continuous_of_finiteDimensional (Formalism.FourierDecayAlt.P.Qx5.zetaLin k r z z' (Fin.last r))).comp continuous_id

theorem map_levM_eq {z z' : Fin (2 * ρ + k + 1) → ℂ} {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (wt : ℂ → ℝ≥0∞) (hfin : ∀ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ < (⊤ : ℝ≥0∞))
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, wt ζ * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ z z' (Fin.last ρ) (Matrix.of x)) ∂μs = ∫⁻ ζ, wt ζ * ψ ζ) :
    μs.map (B2.levM k ρ) = μ := by
  obtain ⟨c, hc⟩ := map_levM_smul hμ hμs
  have key : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → c • ∫⁻ ζ, wt ζ * ψ ζ = ∫⁻ ζ, wt ζ * ψ ζ := by
    intro ψ hψ
    have hm : Measurable fun y : Mt k (1 + ρ) =>
        ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of y)) :=
      hψ.comp (continuous_zetaL (1 + ρ) _ _).measurable
    rw [← hlaw ψ hψ, ← lintegral_smul_measure, ← hc, lintegral_map hm measurable_levM]
    simp_rw [zeta_levM]
    rw [hlaws ψ hψ, hlaw ψ hψ]
  by_cases hR : ∃ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ ≠ 0
  · obtain ⟨R, hR⟩ := hR
    have hψ : Measurable ((Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞)) :=
      measurable_one.indicator Metric.isClosed_closedBall.measurableSet
    have h1 := key _ hψ
    have e : ∫⁻ ζ, wt ζ * (Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) ζ =
        ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
      congr 1
      funext ζ
      by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) R <;> simp [hζ]
    rw [e, ENNReal.smul_def] at h1
    have h2 : (c : ℝ≥0∞) * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ = 1 * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [one_mul]
      exact h1
    have hc1 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hR (hfin R).ne).mp h2
    rw [hc, ENNReal.coe_eq_one.mp hc1, one_smul]
  · push_neg at hR
    have h0 : ∫⁻ ζ, wt ζ = 0 := by
      rw [← setLIntegral_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ)]
      refine le_antisymm ((lintegral_iUnion_le _ _).trans ?_) zero_le'
      simp [hR]
    have hμ0 : μ = 0 := by
      have h3 := hlaw (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    have hμs0 : μs = 0 := by
      have h3 := hlaws (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    rw [hμ0, hμs0, Measure.map_zero]

end Formalism.FourierDecayAlt.P.PBH
end
end

section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

theorem identity_operator : TL.IdOp := by
  intro k r Wp Wq _ _ _ _ _ Bs
  let T : B.DTerm k r Wp Wq :=
    { coef := fun _ => 1
      coefAdj := fun _ => 1
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun _ _ _ => rfl }
  have hap : ∀ F, B.opApply [T] F = F := by
    intro F
    funext g
    simp [B.opApply, B.Rw, T]
  refine ⟨[T], ⟨?_, ?_, ?_⟩, hap⟩
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨?_, ?_⟩ <;> intro g₀ _ <;>
      refine ⟨Set.univ, fun _ => 1, ?_, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩
    all_goals
      first
      | exact isOpen_univ
      | exact contDiffOn_const
      | (open scoped Formalism.FourierDecayAlt.B in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Elementwise in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Operator in exact contDiffOn_const)
      | exact @contDiffOn_const _ _ _ _ _ _ _ _ _ _ _ _
  · intro p _ f _ g _
    simp only [hap]
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨fun _ => 1, 0, 0, 0, [], ⟨1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp
    · intro g
      simp
    · intro l _ _
      simp
    · simp [T]
    · simp
    · intro g _
      simp [C6.monoM, C6.Epart, T]

end

end Formalism.FourierDecayAlt.P
end

section

namespace Formalism.FourierDecayAlt.TL

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

theorem wordLiftOfParts : WordLiftOfParts := by
  intro hstep hlet A S _ _ _ _ _ _ r n L st Lf w hA hL hn
  induction w with
  | nil =>
    intro _ e
    have h1 : ((ofWord L st ([] : List (Letter ℂ S))).F * bTA L ([] : List (Letter ℂ S))) = 1 := by
      simp [ofWord, bTA, bT, Start.frame]
    rw [h1, Matrix.one_apply]
    split_ifs
    · simpa using hL.one
    · exact hL.zero _ _
  | cons l w ih =>
    intro hw e
    have hw' : admitted st w := by
      obtain ⟨h1, h2, h3, h4⟩ := hw
      refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'),
        fun l' hl' => h3 l' (List.mem_cons_of_mem _ hl'), h4.of_cons⟩
      simp only [List.map_cons, List.nodup_cons] at h1
      exact h1.2
    rw [hstep A S r L st l w hA hw e, Matrix.mul_apply]
    refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
    intro f _
    have hcoef : Lf n (9 * (r + 1) * n) ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * letterCol L st l w i : SlopeTestRemainingChoices S A) e f) := by
      rw [Matrix.sum_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro i _
      rw [Matrix.mul_apply]
      refine Finset.sum_induction _ (Lf _ _) (fun a b ha hb => hL.add ha hb) (hL.zero _ _) ?_
      intro g _
      simp only [eU, Matrix.of_apply]
      split_ifs
      · rw [one_mul]
        exact hlet A S r n L st Lf l w hA hL hn hw i g f
      · rw [zero_mul]
        exact hL.zero _ _
    refine hL.mono ?_ ?_ (hL.mul hcoef (ih hw' f))
    · simp only [List.length_cons]
      exact le_of_eq (by ring)
    · simp only [List.length_cons]
      exact le_of_eq (by ring)

end Formalism.FourierDecayAlt.TL
end
