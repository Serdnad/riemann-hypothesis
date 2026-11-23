module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle014
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle171
public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R

def lstN (K m : ℕ) (y : Fin K → ℝ) : List ℝ :=
  List.ofFn fun b : Fin m => if hb : m - 1 - b < K then y ⟨m - 1 - b, hb⟩ else 0

theorem lstN_succ (K : ℕ) (a : Fin K) (y : Fin K → ℝ) (t : ℝ) :
    lstN K ((a : ℕ) + 1) (Function.update y a t) = t :: lstN K a y := by
  unfold lstN
  rw [List.ofFn_succ]
  congr 1
  · rw [dite_eq_left (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - ((0 : Fin ((a : ℕ) + 1)) : ℕ), by omega⟩ : Fin K) = a := Fin.ext (by simp)
    rw [e, Function.update_self]
  · congr 1
    funext i
    have hi := i.isLt
    rw [dite_eq_left (by simp; omega), dite_eq_left (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - (i.succ : ℕ), by simp; omega⟩ : Fin K) = ⟨(a : ℕ) - 1 - i, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e, Function.update_of_ne]
    intro h'
    have := congrArg Fin.val h'
    simp at this
    omega

theorem lstN_full (K : ℕ) (z : Fin K → ℝ) : lstN K K z = List.ofFn fun b => z (Fin.rev b) := by
  unfold lstN
  congr 1
  funext b
  rw [dite_eq_left (by omega)]
  congr 1
  ext
  simp [Fin.val_rev]
  omega

theorem cutWord_plusW {P : M.Par} {l0 : ℕ} {w : List C.Letter} :
    ∀ ys : List ℝ, KB.CutWord P l0 (KB.plusW ys w) → KB.CutWord P l0 w
  | [], h => h
  | _ :: ys, h => cutWord_plusW ys (cutWord_tail h)

section deg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def aaIter {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (F0 : B.Mat k r → (Wq →L[ℂ] Wp)) :
    List ℝ → B.Mat k r → (Wq →L[ℂ] Wp)
  | [] => F0
  | y :: ys => aaTop Bs y (aaIter Bs F0 ys)

def aPIter {V : Type} [AddCommGroup V] [Module ℂ V] {r : ℕ} (L : R.LevelData (Q.Pr V) r) : List ℝ → V → V
  | [], Ψ => Ψ
  | y :: ys, Ψ => (TL.aP L (y : ℂ)).1 (aPIter L ys Ψ)

theorem aaIter_rad (hRA : RadAATop) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ)
    (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) {F0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF0 : KB.CptCoef Bs F0) {Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'} (hΨ : Top.IsRadOf P Bs Ψ F0) :
    ∀ ys : List ℝ, KB.CptCoef Bs (aaIter Bs F0 ys) ∧ Top.IsRadOf P Bs (aPIter L ys Ψ) (aaIter Bs F0 ys) := by
  intro ys
  induction ys with
  | nil => exact ⟨hF0, hΨ⟩
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := hRA Wp Wq P Bs X μ L st l0 y hD _ h1
    exact ⟨h3, h4 _ h2⟩

theorem rad_plusW (hWS : TL.WordStep) (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (hD : P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X μ L st p.l0) (w : List C.Letter)
    (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (e : Ix (Fin w.length)) :
    ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      P5.act ((Fr.ofWord L st (D.positionted (KB.plusW ys w))).F * P5.bTall L (D.positionted (KB.plusW ys w)))
          (Top.firstStateVector Φ) (KB.firstSt ys e) =
        aPIter L ys (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e) := by
  intro ys
  induction ys with
  | nil => intro; rfl
  | cons y ys ih =>
    intro hc
    have h1 := rad_plus hWS P p X μ L st hD (KB.plusW ys w) y hc Φ (KB.firstSt ys e)
    exact h1.trans (congrArg (fun Ψ => (TL.aP L (y : ℂ)).1 Ψ) (ih (cutWord_tail hc)))

end deg

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBN

theorem degree_top_of_parts : PBN.DegTopOfParts := by
  intro hWS hRA hPT hDC Wp Wq _ _ _ _ _ _ P p F s w h t K grid e Cb hCb hs hloc hF hgrid hcut
  obtain ⟨X, μ, L, st, hD, hTL⟩ := p.hΘ
  have hcw : KB.CutWord P p.l0 w := cutWord_plusW _ (hcut fun _ => 0)
  obtain ⟨F0, hF0, hF0eq, hV0⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hcw
  obtain ⟨Φ, hΦ⟩ := radExists p hF
  have hΨ := isRadOf_congr p.T.base (hTL w hcw F hF Φ hΦ e) hF0eq
  have hIt := aaIter_rad hRA P p.T.base X μ L st p.l0 hD hF0 hΨ

  have hVit : ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      p.V (aaIter p.T.base F0 ys) (h ++ [(s, t)]) =
        p.V (p.Θ.Θ (KB.plusW ys w) (KB.firstSt ys e) F) (h ++ [(s, t)]) := by
    intro ys hc
    obtain ⟨Fn, hFn, hFneq, hVn⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F (KB.plusW ys w) (KB.firstSt ys e) Cb hCb hF hc
    rw [hVn]
    have hrad := isRadOf_congr p.T.base (hTL (KB.plusW ys w) hc F hF Φ hΦ (KB.firstSt ys e)) hFneq
    rw [rad_plusW hWS P p X μ L st hD w Φ e ys hc] at hrad
    exact vecV_eq_of_rad hDC p (hIt ys).1 hFn (hIt ys).2 hrad _
  set W : ℕ → (Fin K → ℝ) → (Wq →L[ℂ] Wp) := fun m y => p.V (aaIter p.T.base F0 (lstN K m y)) (h ++ [(s, t)])
    with hW
  have hPS : F7.PolyStep K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W := by
    intro a y
    obtain ⟨c, hc, hpoly⟩ := hPT Wp Wq P p (aaIter p.T.base F0 (lstN K a y)) s h t hs hloc (hIt _).1
    refine ⟨c, hc, fun t' => ?_⟩
    simp only [hW]
    rw [lstN_succ]
    exact hpoly t'
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound (Wq →L[ℂ] Wp) K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W
    (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hE
  have hW0 : W 0 (fun _ => 0) = p.V (p.Θ.Θ w e F) (h ++ [(s, t)]) := by
    simp only [hW, lstN, List.ofFn_zero, aaIter]
    rw [hV0]
  rw [hW0] at hE
  rw [hE]
  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW]
  rw [lstN_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2, hVit _ (hcut _)]

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem nice_mono {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k ρ Wp Wq} {ε ε' : ℝ} {F : B.Mat k ρ → (Wq →L[ℂ] Wp)}
    (h : JC.NiceCoef Bs ε F) (hε : ε' ≤ ε) : JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => hε.trans (h.2.2 g hg hne)⟩

theorem poly_coeff_unique {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (A B : Fin n → V)
    (h : ∀ y : ℝ, ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • A l = ∑ l : Fin n, ((y : ℂ) ^ (l : ℕ)) • B l) : A = B := by
  set τ : Fin n → ℂ := fun i => (((i : ℕ) : ℝ) : ℂ) with hτdef
  have hτ : Function.Injective τ := by
    intro a b hab
    simp only [hτdef, Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  have key : ∀ (C : Fin n → V) (l : Fin n),
      C l = ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i • ∑ m : Fin n, (τ i ^ (m : ℕ)) • C m := by
    intro C l
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    simp only [vand_row τ hτ l, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  funext l
  rw [key A l, key B l]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact h ((i : ℕ) : ℝ)

section lift

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem sum_pad {V : Type} [AddCommGroup V] [Module ℂ V] {d n : ℕ} (hdn : d ≤ n) (c : Fin (d + 1) → V) (y : ℂ) :
    ∑ m : Fin (d + 1), (y ^ (m : ℕ)) • c m =
      ∑ l : Fin (n + 1), (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0) := by
  classical
  have e := Finset.sum_map (Finset.univ : Finset (Fin (d + 1))) (Fin.castLEEmb (by omega : d + 1 ≤ n + 1))
    (fun l : Fin (n + 1) => (y ^ (l : ℕ)) • (if hl : (l : ℕ) ≤ d then c ⟨l, by omega⟩ else 0))
  symm
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin (d + 1))).map
    (Fin.castLEEmb (by omega : d + 1 ≤ n + 1)))) ?_, e]
  · apply Finset.sum_congr rfl
    intro m _
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    rw [dite_eq_left (by omega)]
  · intro l _ hl
    rw [dite_eq_right, smul_zero]
    intro hle
    apply hl
    rw [Finset.mem_map]
    exact ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem reduceJ {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j) (hs : s ≤ j)
    (hSP : SlicePoly T F j hj (h ++ [(s, τ)]) ha) (hLD : LiftDeg T F j s hj h τ ha)
    (w' : List C.Letter) (hN : ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a'))
    (b : Bool) (δ : ℝ) :
    ∃ E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp),
      (∀ l, ∃ ε, ∀ a', JC.NiceCoef (T.bs j) ε (E l a')) ∧ (∀ l : Fin (j + 1), j - s < (l : ℕ) → E l = 0) ∧
      E ⟨j - s, by omega⟩ = cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha ∧
      ∀ (y : ℝ) (a' : Wd.Ix (Fin w'.length)), ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z',
        B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
          B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • E l) a') g := by
  classical
  obtain ⟨C1, -, hC1n, hC1⟩ := hSP w' b δ 1
  obtain ⟨εN, hεN⟩ := hN
  set E : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) := fun l =>
    if (l : ℕ) < j - s then C1 l else if (l : ℕ) = j - s then cLift s τ b • KB.slv T F j hj w' (h ++ [(s, τ)]) ha
    else 0 with hE

  choose εC hεC using hC1n
  set ε0 : ℝ := min εN (Finset.univ.inf' Finset.univ_nonempty εC) with hε0
  have hC1n' : ∀ l a', JC.NiceCoef (T.bs j) ε0 (C1 l a') := fun l a' =>
    nice_mono (hεC l a') ((min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ l)))
  have hNn' : ∀ a', JC.NiceCoef (T.bs j) ε0 (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a') := fun a' =>
    nice_mono (hεN a') (min_le_left _ _)
  have hEn : ∀ l a', JC.NiceCoef (T.bs j) ε0 (E l a') := by
    intro l a'
    simp only [hE]
    split_ifs
    · exact hC1n' l a'
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hNn' a')
    · exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  refine ⟨E, fun l => ⟨ε0, hEn l⟩, fun l hl => ?_, ?_, fun y a' g hg => ?_⟩
  · simp only [hE]; rw [if_neg (by omega), if_neg (by omega)]
  · simp only [hE]; rw [if_neg (by simp), if_pos (by simp)]
  ·
    have hsum : ∀ (y : ℝ) (V : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp)),
        (∀ l, JC.NiceCoef (T.bs j) ε0 (V l a')) →
        B.JF (T.bs j) ((∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a') g =
          ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (V l a') g := by
      intro y V hV
      have e1 : (∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l) a' = ∑ l : Fin (j + 1), ((y : ℂ) ^ (l : ℕ)) • V l a' := by
        simp [Finset.sum_apply]
      rw [e1, Formalism.FourierDecayAlt.P.JCx2.bc_JF_sum Finset.univ (fun l : Fin (j + 1) => ((y : ℂ) ^ (l : ℕ)) • V l a')
        (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (hV l)) hg]
      apply Finset.sum_congr rfl
      intro l _
      exact Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _
    have hgGV : g ∈ B.GV k (r - j) := hg.1

    have hL : ∀ y' : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y' + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
        ∑ l : Fin (j + 1), ((y' : ℂ) ^ (l : ℕ)) • B.JF (T.bs j) (C1 l a') g := by
      intro y'
      rw [Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr (T.bs j) (fun g' hg' => hC1 y' a' g' hg') hgGV]
      exact hsum y' C1 (fun l => hC1n' l a')
    obtain ⟨c, hcl, hcy⟩ := hLD w' a' b δ g hg
    have hcomp := poly_coeff_unique (j + 1) (fun l => B.JF (T.bs j) (C1 l a') g)
      (fun l => if hl : (l : ℕ) ≤ j - s then c ⟨l, by omega⟩ else 0) (fun y' => by
        rw [← hL y', hcy y', sum_pad (n := j) (by omega) c (y' : ℂ)])
    rw [hL y, hsum y E (fun l => hEn l a')]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    have hcl' := congrFun hcomp l
    by_cases h1 : (l : ℕ) < j - s
    · simp only [hE, if_pos h1]
    · rw [show B.JF (T.bs j) (C1 l a') g = _ from hcl']
      by_cases h2 : (l : ℕ) = j - s
      · simp only [hE, if_neg h1, if_pos h2]
        rw [dite_eq_left (by omega)]
        have e3 : (⟨(l : ℕ), by omega⟩ : Fin (j - s + 1)) = Fin.last (j - s) := Fin.ext (by simp [h2])
        rw [e3, hcl]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul _ _ _).symm
      · simp only [hE, if_neg h1, if_neg h2]
        rw [dite_eq_right (by omega)]
        exact (Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero g).symm

theorem nice_lincomb {k ρ : ℕ} {Bs : B.RealPlaceData k ρ Wp Wq} {S ι : Type} [Fintype S] [Fintype ι] [Nonempty ι]
    (V : ι → Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) (hV : ∀ l, ∃ ε, ∀ a, JC.NiceCoef Bs ε (V l a)) (c : ι → ℂ) :
    ∃ ε, ∀ a, JC.NiceCoef Bs ε ((∑ l, c l • V l) a) := by
  classical
  choose ε hε using hV
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ε, fun a => ?_⟩
  have e : (∑ l, c l • V l) a = fun g => ∑ l, c l • V l a g := by
    funext g; simp [Finset.sum_apply]
  rw [e]
  exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum Finset.univ (fun l g => c l • V l a g)
    (fun l _ => Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul _ (nice_mono (hε l a) (Finset.inf'_le _ (Finset.mem_univ l))))

end lift

end Formalism.FourierDecayAlt.P.PBG
end
end
