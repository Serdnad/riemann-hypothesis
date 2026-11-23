module

public import Formalism.HermitianCurvature.Bundle007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReflectionTransposeEntriesMem
public import Formalism.HermitianCurvature.StatementB
public import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.Bundle004

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def LocSup (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (n b : ℕ) (a : List C.Letter) (h : C.LPt) : Prop :=
  ∃ B : ℝ, ∀ t : ℂ, t ≠ 0 → ‖KB.gN S v ε (b + n - 1) a (h ++ [(n, t)]) (h ++ [(n, t)])‖ ≤ B

theorem psd_single_one {α : Type} (h : α) : TB.PSDOn ({h} : Finset α) (fun _ _ => (1 : ℂ)) := by
  unfold TB.PSDOn
  have hA : (Matrix.of fun (x y : ↥({h} : Finset α)) => (1 : ℂ)) =
      (Matrix.of fun (_ : ↥({h} : Finset α)) (_ : Unit) => (1 : ℂ)) *
        Matrix.conjTranspose (Matrix.of fun (_ : ↥({h} : Finset α)) (_ : Unit) => (1 : ℂ)) := by
    ext x y
    simp [Matrix.mul_apply]
  rw [hA]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem dlB_pos (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (b s : ℕ) : 0 < KB.dlB S b s := by
  have hd : (0 : ℝ) < ((|discr E| : ℤ) : ℝ) := by
    have := NumberField.discr_ne_zero E
    exact_mod_cast abs_pos.2 this
  have hrd : 0 < S6.rd E := Real.rpow_pos_of_pos hd _
  unfold KB.dlB D.deG
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  refine div_pos ?_ (div_pos two_pos (mul_pos hrd (pow_pos hg' 3)))
  first
  | exact pow_pos hrd _
  | exact zpow_pos hrd _
  | exact Real.rpow_pos_of_pos hrd _

theorem exists_word_of_admissible_at_place (S : C.HidaSetting E Wp Wq) {v : Fin S.f} {a : List C.Letter} (ha : D.AdmAt S v a) :
    ∃ w : S.W, w.1 v = a := ha

theorem locSup_one (S : C.HidaSetting E Wp Wq) (hI : KB.IntAll S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (b : ℕ)
    (hb : 1 ≤ b) (hbr : b ≤ S.G.r + 1) (a : List C.Letter) (ha : D.AdmAt S v a) (h : C.LPt)
    (hh : D.ptSize h = b - 1) : LocSup S v ε 1 b a h := by
  obtain ⟨w, hw⟩ := exists_word_of_admissible_at_place S ha
  obtain ⟨φ, -, hφ, ⟨Cφ, hCφ⟩, -⟩ := hI v ε hε b hb hbr w h h hh hh
  refine ⟨|Cφ| * ‖((S.sizeAt v a : ℝ) : ℂ)‖⁻¹, fun t ht => ?_⟩
  have hb1 : b + 1 - 1 = b := Nat.add_sub_cancel b 1
  unfold KB.gN
  rw [hb1, norm_div, div_eq_mul_inv, ← hw, ← hφ t ht]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
  have h1 : ((1 + ‖t‖) ^ 3)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg t]))
  have h2 : 0 ≤ ((1 + ‖t‖) ^ 3)⁻¹ := inv_nonneg.2 (by positivity)
  calc ‖φ t‖ ≤ Cφ * ((1 + ‖t‖) ^ 3)⁻¹ := hCφ t
    _ ≤ |Cφ| * ((1 + ‖t‖) ^ 3)⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) h2
    _ ≤ |Cφ| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |Cφ| := mul_one _

theorem mL_one (K : ℕ) (L : ℝ) (σ : crystallineComparison.V 1) : crystallineComparison.mL K (fun _ => L) σ = crystallineComparison.mfac K L ‖σ 0‖ := by
  simp [crystallineComparison.mL]

theorem offdiag_bound {Z : Type} (w : Z → Z → ℂ) (a b : Z → Z → ℂ) (p : Z) (Y : Finset Z) (hp : p ∈ Y)
    (hB : KB.BlockPSD Y Y a w b) (Ba Bb : ℝ) (ha : (a p p).re ≤ Ba) (hb : (b p p).re ≤ Bb) :
    ‖w p p‖ ^ 2 ≤ Ba * Bb := by
  have hpsd := hB
  unfold KB.BlockPSD TB.PSDOn at hpsd
  let f : Fin 2 → ↥(Y.disjSum Y) := ![⟨Sum.inl p, by simp [hp]⟩, ⟨Sum.inr p, by simp [hp]⟩]
  have hs := hpsd.submatrix f
  have hdet := hs.det_nonneg
  have hd0 := hs.diag_nonneg (i := 0)
  have hd1 := hs.diag_nonneg (i := 1)
  rw [Matrix.det_fin_two] at hdet
  simp [f, Matrix.submatrix_apply] at hdet hd0 hd1
  rw [Complex.le_def] at hdet
  rw [Complex.nonneg_iff] at hd0 hd1
  have hw : ‖w p p‖ ^ 2 ≤ (a p p).re * (b p p).re := by
    have h3 := hdet.1
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, ← hd0.2, ← hd1.2] at h3
    nlinarith [h3]
  calc ‖w p p‖ ^ 2 ≤ (a p p).re * (b p p).re := hw
    _ ≤ Ba * Bb := mul_le_mul ha hb hd1.1 (le_trans hd0.1 ha)

end

end Formalism.FourierDecayAlt.P.PBC
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Pres

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def presAlg (U : Submodule ℂ V) : StarSubalgebra ℂ (Pr V) where
  carrier := {a | (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ ∀ Φ ∈ U, a.2.unop Φ ∈ U}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ)⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ)⟩
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
    · show (algebraMap ℂ (Module.End ℂ V) a) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · show (algebraMap ℂ (Module.End ℂ V) (conj a)) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
  star_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨ha2, ha1⟩

end Pres

section Words

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem entries_mem_transpose {M : M2 (SlopeTestRemainingChoices S A)} (h : E2 𝒜 M) : E2 𝒜 Mᵀ := fun i j => h j i

theorem transfer_word_entries_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : star Y = Y) : E2 𝒜 (TTw QQ w Y) := by
  induction w with
  | nil =>
    intro a b
    show io (QQ Y a b) ∈ entSub 𝒜
    exact io_mem (hQ Y hY a b)
  | cons l w ih =>
    by_cases hp : l.plus
    · rw [TTw, if_pos hp]; exact entries_mem_mul ih (reflection_entries_mem _ _)
    · rw [TTw, if_neg hp]; exact entries_mem_mul (reflection_transpose_entries_mem _ _) ih

theorem rrw_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRw QQ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [RRw]
    refine (entSub 𝒜).mul_mem (ih fun l' hl' => hw l' (by simp [hl'])) (ins_mem _ ?_)
    have hT := transfer_word_entries_mem QQ hQ w l.pt (hw l (by simp))
    split_ifs
    · exact hT
    · exact entries_mem_transpose hT

end Words

section Levels

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem matrix_two_entries_mem {𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))} {a b c d : Pr (RadSp k r z z' π π')}
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (hd : d ∈ 𝒜) : ∀ i j, (!![a, b; c, d] : M2 _) i j ∈ 𝒜 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem tprod_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π')))
    (Y : ℂ) (i : ℕ) (hS : ∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) (a b : Fin 2) :
    tprod L Y i a b ∈ 𝒜 := by
  suffices H : ∀ n i, r - i = n → (∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) →
      ∀ a b, tprod L Y i a b ∈ 𝒜 from H _ i rfl hS a b
  intro n
  induction n with
  | zero =>
    intro i hi _ a b
    unfold tprod
    rw [dite_eq_right (by omega), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ n ih =>
    intro i hi hS a b
    unfold tprod
    rw [dite_eq_left (by omega), Matrix.mul_apply]
    refine sum_mem fun e _ => mul_mem (ih (i + 1) (by omega) (fun l hl => hS l (by omega)) a e) ?_
    obtain ⟨hp, hc, hci⟩ := hS ⟨i, by omega⟩ le_rfl
    have h00 : algebraMap ℂ _ Y + L.p ⟨i, by omega⟩ ∈ 𝒜 := add_mem (𝒜.algebraMap_mem Y) hp
    fin_cases e <;> fin_cases b <;> simp [Ts, Formalism.YangianSpanCharacter.T.Tm, site, h00, hc, hci]

theorem QQi_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1))
    (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, st.QQ Y a b ∈ 𝒜)
    (hS : ∀ l : Fin r, i.val ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) :
    ∀ Y : ℂ, star Y = Y → ∀ a b, QQi L st i Y a b ∈ 𝒜 := by
  intro Y hY a b
  unfold QQi
  rw [Matrix.mul_apply]
  refine sum_mem fun e _ => mul_mem ?_ (tprod_mem L 𝒜 Y i.val hS e b)
  rw [Matrix.mul_apply]
  refine sum_mem fun f _ => mul_mem ?_ (hQ Y hY f e)
  rw [Matrix.conjTranspose_apply]
  exact star_mem (tprod_mem L 𝒜 (star Y) i.val hS f a)

end Levels

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Gen

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem Ts_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (Y : ℂ) (i j : Fin 2) :
    Ts σ Y i j ∈ 𝒜 := by
  unfold Ts Formalism.YangianSpanCharacter.T.Tm
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (algebraMap_mem 𝒜 Y) hp
  · exact neg_mem hc
  · exact hci
  · exact zero_mem 𝒜

theorem bT_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (w : List (Letter ℂ S)) :
    bT σ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [bT]
    refine (entSub 𝒜).mul_mem (ins_mem _ fun i j => ?_) ih
    show io ((if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) i j) ∈ entSub 𝒜
    apply io_mem
    split_ifs
    · exact Ts_mem σ hp hc hci l.pt i j
    · exact (star_mem (Ts_mem σ hp hc hci l.pt i j) : star _ ∈ 𝒜)

end Gen

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellInversePair

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  have hu := WeylGroupFacts.isUnit_of_uh hh.1
  have key : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨WeylGroupFacts.uh_inv hh.1, fun a => ⟨key _ (hh.2.1 a).1, key _ (hh.2.1 a).2⟩, key _ hh.2.2⟩

def invP (p : SS k r) : SS k r :=
  ((((Matrix.of p.1.1 : Mat k r)⁻¹ : Mat k r),
      ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * (Matrix.of p.1.1 : Mat k r) : Mat k r)),
    (((Matrix.of p.2.1 : Mat k r)⁻¹ : Mat k r),
      ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 : Mat k r)⁻¹ * (Matrix.of p.2.1 : Mat k r) : Mat k r)))

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem invP_inSS (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) : D.inSS (invP p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hu1 := WeylGroupFacts.isUnit_of_uh h1.1
  have hu3 := WeylGroupFacts.isUnit_of_uh h3.1
  refine ⟨uw_inv h1, ?_, uw_inv h3, ?_⟩
  · have := (uWNormal k r D.z D.z_mem (Matrix.of p.1.1)⁻¹ (uw_inv h1) _ (WeylGroupFacts.mem_n_inv h2)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu1] at this
  · have := (uWNormal k r D.z' D.z'_mem (Matrix.of p.2.1)⁻¹ (uw_inv h3) _ (WeylGroupFacts.mem_n_inv h4)).1
    rwa [Matrix.nonsing_inv_nonsing_inv _ hu3] at this

theorem sgs_invP (p : SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : Mat k r).det) (hp2 : IsUnit (Matrix.of p.1.2 : Mat k r).det)
    (hp3 : IsUnit (Matrix.of p.2.1 : Mat k r).det) (hp4 : IsUnit (Matrix.of p.2.2 : Mat k r).det) (x : Mat k r) :
    sgs (invP p) (sgs p x) = x := by
  show (Matrix.of p.1.1 : Mat k r)⁻¹⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ *
      Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * x *
      Matrix.of p.2.2 * Matrix.of p.2.1) * ((Matrix.of p.2.1 : Mat k r)⁻¹ * (Matrix.of p.2.2 : Mat k r)⁻¹ *
      Matrix.of p.2.1) * (Matrix.of p.2.1 : Mat k r)⁻¹ = x
  generalize (Matrix.of p.1.1 : Mat k r) = A at hp1 ⊢
  generalize (Matrix.of p.1.2 : Mat k r) = B at hp2 ⊢
  generalize (Matrix.of p.2.1 : Mat k r) = C at hp3 ⊢
  generalize (Matrix.of p.2.2 : Mat k r) = D at hp4 ⊢
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv A hp1,
    Matrix.nonsing_inv_nonsing_inv B hp2]
  simp only [mul_assoc, Matrix.mul_nonsing_inv_cancel_left, Matrix.nonsing_inv_mul_cancel_left,
    Matrix.mul_nonsing_inv, hp1, hp2, hp3, hp4, mul_one]

end Formalism.FourierDecayAlt.P.BigCellInversePair

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ellreg

variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

end ellreg

def lieOf {k r : ℕ} (Sx : Set (B.Mat k r)) : Set (B.Mat k r) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Sx}

def OmQ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | 0 < Gf k r z z' g ∧ ∀ a : Fin r, Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def SymbolNil : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g ∈ B.GV k r, g ∈ OmQ k r z z' → ∀ ξ : B.Mat k r, B.inLie k r ξ → IsNilpotent ξ →
      (∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ξ * X)).re = 0) →
      (∀ X ∈ lieOf (Sset k r z'), (Matrix.trace (ξ * (g * X * g⁻¹))).re = 0) →
      ξ = 0

theorem lieOf_mono {k r : ℕ} {A B' : Set (B.Mat k r)} (h : A ⊆ B') : lieOf A ⊆ lieOf B' :=
  fun _ hX t => h (hX t)

theorem UWset_sub_Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : UWset k r z ⊆ Sset k r z :=
  fun h hh => ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JfS
end
