module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCSplit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocSupStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBBLiftV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftVectorZeroBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

def projM (y : Mt k (1 + ρ)) : Mt k ρ := fun a b => y ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩

theorem projM_levM (x : Mt k ρ) : projM (B2.levM k ρ x) = x := by
  funext a b
  simp only [projM, B2.levM, ιLev, Matrix.of_apply]
  rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem continuous_levM : Continuous (B2.levM k ρ) := by
  exact Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ

theorem continuous_projM : Continuous (projM (k := k) (ρ := ρ)) := by
  unfold projM
  fun_prop

theorem measurableEmbedding_levM : MeasurableEmbedding (B2.levM k ρ) := by
  refine MeasurableEmbedding.of_measurable_inverse continuous_levM.measurable ?_
    continuous_projM.measurable (fun x => projM_levM x)
  have hr : Set.range (B2.levM k ρ) = {y | B2.levM k ρ (projM y) = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      simp only [Set.mem_setOf_eq, projM_levM]
    · intro hy
      exact ⟨projM y, hy⟩
  rw [hr]
  exact (isClosed_eq (continuous_levM.comp continuous_projM) continuous_id).measurableSet

theorem zWeight_fin (T T' R : ℝ) :
    ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ) < ⊤ := by
  have hC : ∀ ζ ∈ Metric.closedBall (0 : ℂ) R,
      ENNReal.ofReal (B2.zWeight k T T' ζ) ≤ ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) := by
    intro ζ hζ
    apply ENNReal.ofReal_le_ofReal
    have hn : ‖ζ‖ ≤ R := by simpa using hζ
    have hns : Complex.normSq ζ ≤ R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    simp only [B2.zWeight]
    split_ifs with h
    · apply pow_le_pow_left₀ (by linarith)
      linarith [neg_abs_le (T * T')]
    · positivity
  calc ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ)
      ≤ ∫⁻ _ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) :=
        setLIntegral_mono' measurableSet_closedBall hC
    _ = ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) * MeasureTheory.volume (Metric.closedBall (0 : ℂ) R) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

section pair

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem pairAt_tr {t : ℂ} (ht : t ≠ 0) {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hmap : μs.map (B2.levM k ρ) = μ) (Φ Ψ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (c : Fin ρ → ℂ) :
    P5.pairAt μs (trL ht z z' π π' Φ) (trL ht z z' π π' Ψ) c = P5.pairAt μ Φ Ψ (consC t c) := by
  subst hmap
  simp only [P5.pairAt]
  rw [measurableEmbedding_levM.integral_map]
  rfl

end pair

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mem_Wb_iff (S : C.HidaSetting E Wp Wq) (m : ℕ) (u : S.W) : u ∈ S.base.Wb m ↔ u ∈ S.base.Wall ∧ S.base.cnt u ≤ m :=
  Finset.mem_filter

theorem Wb_mono (S : C.HidaSetting E Wp Wq) {m m' : ℕ} (h : m ≤ m') : S.base.Wb m ⊆ S.base.Wb m' := by
  intro u hu
  rw [mem_Wb_iff] at hu ⊢
  exact ⟨hu.1, hu.2.trans h⟩

theorem prob_sum_sub {W : Type} {A Wd : Finset W} {θ : W → ℝ} (hθ : TB.IsProb A θ) (h : A ⊆ Wd) :
    ∑ u ∈ Wd, θ u = 1 := by
  rw [← hθ.2.2]
  exact (Finset.sum_subset h fun u _ hu => hθ.2.1 u hu).symm

theorem blockPSD_same {α : Type} (Y : Finset α) (κ : α → α → ℂ) (hκ : TB.PSDOn Y κ) : KB.BlockPSD Y Y κ κ κ := by
  rw [blockPSD_iff]
  have := JCx1.decay.psd_pull Y κ hκ (Y.disjSum Y) (Sum.elim id id) (by
    intro x hx
    rcases x with p | p
    · rw [Finset.inl_mem_disjSum] at hx; exact hx
    · rw [Finset.inr_mem_disjSum] at hx; exact hx)
  refine PBB.psd_congr _ _ _ (fun x hx y hy => ?_) this
  rcases x with p | p <;> rcases y with q | q
  · rfl
  · rfl
  · rw [Finset.inr_mem_disjSum] at hx
    rw [Finset.inl_mem_disjSum] at hy
    simp only [blk, Sum.elim_inl, Sum.elim_inr, id]
    exact psd_herm Y κ hκ hy hx
  · rfl

theorem image_prod_loc {X : Type} (σ : E →+* ℂ) (Y : Finset (TB.Pt E)) (Xs : Finset X) :
    (Y ×ˢ Xs).image (fun p : TB.Pt E × X => (C.loc σ p.1, p.2)) = (Y.image (C.loc σ)) ×ˢ Xs := by
  ext ⟨a, x⟩
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨h, x', ⟨hh, hx'⟩, rfl, rfl⟩; exact ⟨⟨h, hh, rfl⟩, hx'⟩
  · rintro ⟨⟨h, hh, rfl⟩, hx⟩; exact ⟨h, x, ⟨hh, hx⟩, rfl, rfl⟩

theorem germ_global (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (w' : S.W)
    (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop) (Y : Finset (TB.Pt E)) (hY : ∀ h ∈ Y, TB.level h = b - 1) :
    ∃ (P Q : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ),
      (∀ v, ∀ h ∈ Y, ∀ h' ∈ Y,
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)]))) ∧
      GermData Y (fun v p q => KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)])
          (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])) P Q
        (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
  have hloc : ∀ v, ∀ h ∈ Y.image (C.loc (S.σ v)), D.ptSize h = b - 1 := by
    intro v h hh
    obtain ⟨h0, hh0, rfl⟩ := Finset.mem_image.1 hh
    rw [JCx1.needs.ptSize_loc]; exact hY h0 hh0
  have hsup : ∀ v, ∃ B : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w'.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t)])‖ ≤ B := by
    intro v
    have hs : ∀ h ∈ Y.image (C.loc (S.σ v)), LocSup S v ε (n - 1) b (w'.1 v) h := by
      intro h hh
      refine locSup_all S hpos hI hg v Λ (hLL v) (hGL v) (fun b s hb hs hbs => hΛ0 b s hb hs hbs v) ε hε (n - 1)
        (by omega) b hb (by omega) h (hloc v h hh) (w'.1 v) ⟨w', rfl⟩ ?_
      have := PBB.len_le_cnt S w' v
      have hk : (n - 1 - 1) * C.Kst ≤ n * C.Kst := Nat.mul_le_mul_right _ (by omega)
      omega
    choose! Bh hBh using hs
    refine ⟨∑ h ∈ Y.image (C.loc (S.σ v)), max (Bh h) 0, fun h hh t ht => ?_⟩
    have := hBh h hh t ht
    rw [show b + (n - 1) - 1 = b + n - 2 by omega] at this
    exact this.trans ((le_max_left _ _).trans (Finset.single_le_sum (f := fun h => max (Bh h) 0)
      (fun _ _ => le_max_right _ _) hh))
  have hG' : ∀ v, ∃ (Pu Pa : C.LPt × ℂ → C.LPt × ℂ → ℂ),
      (∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)),
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)]))) ∧
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (fun p q => KB.gN S v ε (b + n - 2) (w'.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])) Pu Pa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ x : ℂ, x ≠ 0 → ‖Pa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)), ∀ σ : ℂ,
        Tendsto (fun x => Pa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => Pu (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => conj (Pu (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) := by
    intro v
    obtain ⟨h1, Pu, Pa, h2, h3, h4⟩ := hGL v ε hε b n hb hn hbn (w'.1 v) ⟨w', rfl⟩ (Y.image (C.loc (S.σ v)))
      (hloc v) (hsup v)
    exact ⟨Pu, Pa, h1, h2, h3, h4⟩
  choose Pu Pa hcont hblk hB' hlim using hG'
  choose Bs hBs using hsup
  choose B' hB'' using hB'
  have mem : ∀ v, ∀ h ∈ Y, C.loc (S.σ v) h ∈ Y.image (C.loc (S.σ v)) := fun v h hh => Finset.mem_image_of_mem _ hh
  refine ⟨fun v p q => Pu v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v p q => Pa v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v h hh h' hh' => hcont v _ (mem v h hh) _ (mem v h' hh'), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro v Xs hXs
    have := hblk v Xs hXs
    rw [← image_prod_loc (S.σ v) Y Xs] at this
    exact PBB.blockPSD_pull (Y ×ˢ Xs) (fun p : TB.Pt E × ℂ => (C.loc (S.σ v) p.1, p.2)) _ _ _ this
  · refine ⟨∑ v, (max (Bs v) 0 + max (B' v) 0), Finset.sum_nonneg fun v _ => by positivity,
      fun v h hh x hx => ⟨?_, ?_⟩⟩
    · refine ((hBs v _ (mem v h hh) x⁻¹ (inv_ne_zero hx)).trans (le_max_left (Bs v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_right (le_max_right (B' v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
    · refine ((hB'' v _ (mem v h hh) x hx).trans (le_max_left (B' v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_left (le_max_right (Bs v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.2

end

end Formalism.FourierDecayAlt.P.PBC
end

section

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lift

variable {k i r' : ℕ}

theorem ιLev_apply_lev (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    ιLev k i r' g ⟨p.val + i, by omega⟩ ⟨q.val + i, by omega⟩ = g p q := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [ιLev]
  rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp

theorem ιLev_inj' {g g' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ}
    (h : ιLev k i r' g = ιLev k i r' g') : g = g' := by
  ext p q
  have := congrFun (congrFun h ⟨p.val + i, by omega⟩) ⟨q.val + i, by omega⟩
  rwa [ιLev_apply_lev, ιLev_apply_lev] at this

theorem contDiff_ιLev' : ContDiff ℝ ∞ (ιLev k i r') := by
  refine contDiff_pi.2 fun p => contDiff_pi.2 fun q => ?_
  unfold ιLev
  split_ifs
  · exact (contDiff_apply ℝ (fun _ => ℂ) _).comp (contDiff_apply ℝ (fun _ => (Fin (2 * r' + k + 1) → ℂ)) _)
  all_goals exact contDiff_const

theorem zeta_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    zetaL k (i + r') (liftVec k i r' z) (liftVec k i r' z') (Fin.last (i + r')) (ιLev k i r' g) =
      zetaL k r' z z' (Fin.last r') g := by
  unfold zetaL
  rw [fvec_last, fvec_last, fvec_last, fvec_last, PIQnLT.mulVec_liftVec, PIQnLT.herm_liftVec]

theorem tz_lift (z : Fin (2 * r' + k + 1) → ℂ) : Tz k (i + r') (liftVec k i r' z) = Tz k r' z := by
  unfold Tz; rw [PIQnLT.herm_liftVec]

theorem ggl_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    GGl k (i + r') (liftVec k i r' z) (liftVec k i r' z') (ιLev k i r' g) = GGl k r' z z' g := by
  unfold GGl; rw [zeta_lift, tz_lift, tz_lift]

theorem fnVal_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (j : Fin 6) (g : Mx k r') :
    fnVal k (i + r') (liftVec k i r' z) (liftVec k i r' z') j (ιLev k i r' g) = fnVal k r' z z' j g := by
  unfold fnVal
  split <;> simp only [zeta_lift, ggl_lift]

theorem glev_lift (hr' : r' = 0) (g : Mx k r') :
    ιLev k i r' g ∈ Glev k (i + r') (Fin.last (i + r')) ↔ g ∈ Glev k r' (Fin.last r') := by
  have hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1)) := Fin.ext (by simp; omega)
  have himg := QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k i r'
  have hG : ∀ x : Mx k r', x ∈ Glev k r' (Fin.last r') ↔ x ∈ UH (Hpk k r') := fun x =>
    ⟨fun h => h.1, fun h => ⟨h, fun a _ => absurd a.isLt (by omega)⟩⟩
  rw [hl, himg, hG]
  constructor
  · rintro ⟨g0, hg0, e⟩
    rwa [← ιLev_inj' e]
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem domR_lift (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) (zs zs' : Fin (2 * r' + k + 1) → ℂ)
    (c' : Fin r' → ℂ) (g : Mx k r') :
    (c, ιLev k i r' g) ∈ DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') ↔ (c', g) ∈ DomR k r' zs zs' := by
  show (c ∈ OmX (i + r') ∧ ιLev k i r' g ∈ Glev k (i + r') (Fin.last (i + r')) ∧
      0 < GGl k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') (ιLev k i r' g)) ↔
    (c' ∈ OmX r' ∧ g ∈ Glev k r' (Fin.last r') ∧ 0 < GGl k r' zs zs' g)
  rw [glev_lift hr', ggl_lift]
  exact ⟨fun h => ⟨fun l => absurd l.isLt (by omega), h.2⟩, fun h => ⟨hc, h.2⟩⟩

def rsF {E : Type*} (c : Fin (i + r') → ℂ) (Φ : Fn k (i + r') E) : Fn k r' E := fun _ g => Φ c (ιLev k i r' g)

end lift

section rs

variable {k i r' : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rs_mem (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) {zs zs' : Fin (2 * r' + k + 1) → ℂ}
    {π : Mx k (i + r') → (Wp →L[ℂ] Wp)} {π' : Mx k (i + r') → (Wq →L[ℂ] Wq)} {Φ : Fn k (i + r') (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    rsF c Φ ∈ RadSp k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y)) := by
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨fun x hx => h0 _ fun h => hx ((domR_lift hr' hc zs zs' x.1 x.2).1 h), fun x₀ hx₀ => ?_,
    fun x hx h hh h' hh' => ?_⟩
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs _ ((domR_lift hr' hc zs zs' x₀.1 x₀.2).2 hx₀)
    let e : (Fin r' → ℂ) × Mx k r' → (Fin (i + r') → ℂ) × Mx k (i + r') := fun x => (c, ιLev k i r' x.2)
    have he_c : ContDiff ℝ ∞ e := contDiff_const.prodMk (contDiff_ιLev'.comp contDiff_snd)
    refine ⟨e ⁻¹' U, F ∘ e, hU.preimage he_c.continuous, hxU, hF.comp he_c.contDiffOn (fun x hx => hx),
      fun x hx hg => ?_⟩
    exact hΦF (e x) hx ((glev_lift hr' x.2).2 hg)
  · have hx' := (domR_lift hr' hc zs zs' x.1 x.2).2 hx
    show Φ c (ιLev k i r' (h * x.2 * h')) = _
    rw [(PI.QnLevBasicsW.level_group_homomorphism k i r').2, (PI.QnLevBasicsW.level_group_homomorphism k i r').2]
    exact he _ hx' _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs h hh) _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs' h' hh')

def rsL (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) (zs zs' : Fin (2 * r' + k + 1) → ℂ)
    (π : Mx k (i + r') → (Wp →L[ℂ] Wp)) (π' : Mx k (i + r') → (Wq →L[ℂ] Wq)) :
    RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π' →ₗ[ℂ]
      RadSp k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y)) where
  toFun Φ := ⟨rsF c (Φ : Fn k (i + r') (Wq →L[ℂ] Wp)), rs_mem hr' hc Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) {zs zs' : Fin (2 * r' + k + 1) → ℂ}
  {π : Mx k (i + r') → (Wp →L[ℂ] Wp)} {π' : Mx k (i + r') → (Wq →L[ℂ] Wq)}

theorem t_rs (X₀ : ActualOps k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π')
    (X : ActualOps k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y))) (Y : ℂ) (a b : Fin 2)
    (Φ : RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    X.t Y a b (rsL hr' hc zs zs' π π' Φ) = rsL hr' hc zs zs' π π' (X₀.t Y a b Φ) := by
  apply Subtype.ext
  funext c' g
  by_cases hx : (c', g) ∈ DomR k r' zs zs'
  · have hx' := (domR_lift hr' hc zs zs' c' g).2 hx
    rw [X.t_apply Y a b _ (c', g) hx]
    show _ = (X₀.t Y a b Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)
    rw [X₀.t_apply Y a b Φ (c, ιLev k i r' g) hx']
    have hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1)) := Fin.ext (by simp; omega)
    have h0 : (Fin.last r') = (0 : Fin (r' + 1)) := Fin.ext (by simp; omega)
    rw [hl, h0]
    exact (Formalism.FourierDecayAlt.P.level_transfer _ k i r' zs zs' Y a b ((Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c) g
      hx.2.1.1).symm
  · rw [(X.t Y a b (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]
    exact ((X₀.t Y a b Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm

theorem fn_rs (X₀ : ActualOps k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π')
    (X : ActualOps k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y))) (j : Fin 6)
    (Φ : RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    X.fn j (rsL hr' hc zs zs' π π' Φ) = rsL hr' hc zs zs' π π' (X₀.fn j Φ) := by
  apply Subtype.ext
  funext c' g
  by_cases hx : (c', g) ∈ DomR k r' zs zs'
  · have hx' := (domR_lift hr' hc zs zs' c' g).2 hx
    rw [X.fn_apply j _ (c', g) hx]
    show _ = (X₀.fn j Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)
    rw [X₀.fn_apply j Φ (c, ιLev k i r' g) hx', fnVal_lift]
    rfl
  · rw [(X.fn j (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]
    exact ((X₀.fn j Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm

end rs

end Formalism.FourierDecayAlt.P.WordCorrespondence
end
end
