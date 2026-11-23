module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle204
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle209
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle003
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle198
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbSplitPt

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace FExpR

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rep (m : ℕ∞) (O : Set (B.Mat k r)) (φ : B.Mat k r → E) : Prop :=
  ∃ F : B.Mat k r → E, ContDiffOn ℝ (m : WithTop ℕ∞) F O ∧ ∀ x ∈ O, x ∈ B.GV k r → φ x = F x

theorem rep_mono {m m' : ℕ∞} (hmm : m ≤ m') {O : Set (B.Mat k r)} {φ : B.Mat k r → E} (h : Rep m' O φ) :
    Rep m O φ := by
  obtain ⟨F, hF, he⟩ := h
  exact ⟨F, hF.of_le (by exact_mod_cast hmm), he⟩

theorem rep_RdV {m : ℕ∞} {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {X : B.Mat k r}
    (hX : B.inLie k r X) (h : Rep (m + 1) O φ) : Rep m O (RdV X φ) := by
  obtain ⟨F, hF, he⟩ := h
  refine ⟨fun x => fderiv ℝ F x (x * X), ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hO (by push_cast; exact le_rfl)
    exact h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ F x :=
      (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
    exact (Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext hO hx hxG hX hd he).deriv

theorem rep_Rw {O : Set (B.Mat k r)} (hO : IsOpen O) {f : B.Mat k r → E} {N : ℕ} (h : Rep (N : ℕ∞) O f)
    (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) :
    Rep (m : ℕ∞) O (B.Rw w f) := by
  induction w generalizing m with
  | nil => exact rep_mono (by exact_mod_cast (by simpa using hle)) h
  | cons X w ih =>
    have e : B.Rw (X :: w) f = RdV X (B.Rw w f) := rfl
    rw [e]
    apply rep_RdV hO (hw X (by simp))
    have := ih (fun Y hY => hw Y (by simp [hY])) (m + 1) (by simp at hle; omega)
    exact_mod_cast this

theorem rep_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {x X : B.Mat k r}
    (hx : x ∈ O) (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (h : Rep ((1 : ℕ) : ℕ∞) O φ) :
    HasDerivAt (fun t : ℝ => φ (x * NormedSpace.exp ((t : ℂ) • X))) (RdV X φ x) 0 := by
  obtain ⟨F, hF, he⟩ := h
  have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
  exact (Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext hO hx hxG hX hd he).differentiableAt.hasDerivAt

theorem rdV_congr {O : Set (B.Mat k r)} (hO : IsOpen O) {φ ψ : B.Mat k r → E}
    (he : ∀ y ∈ O, y ∈ B.GV k r → φ y = ψ y) {x X : B.Mat k r} (hx : x ∈ O) (hxG : x ∈ B.GV k r)
    (hX : B.inLie k r X) : RdV X φ x = RdV X ψ x := by
  show deriv (fun t : ℝ => φ (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => ψ (x * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hγ := hasDerivAt_mul_exp_smul_zero x X
  have hγ0 := Formalism.FourierDecayAlt.P.B5.curve_zero x X
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, x * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hx)
  filter_upwards [hmem] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)

theorem wsEvalR_append (a b : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E)
    (x : B.Mat k r) : wsEvalR (a ++ b) u f x = wsEvalR a u f x + wsEvalR b u f x := by
  simp [wsEvalR, List.map_append, List.sum_append]

theorem wsEvalR_flatMap {α : Type} (F : α → List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ L : List α, wsEvalR (L.flatMap F) u f x = (L.map fun a => wsEvalR (F a) u f x).sum
  | [] => by simp [wsEvalR]
  | a :: L => by
    rw [List.flatMap_cons, wsEvalR_append, wsEvalR_flatMap F u f x L, List.map_cons, List.sum_cons]

theorem wsEvalR_map_mul (p : Polynomial ℂ) (φ : List (B.Mat k r) → List (B.Mat k r)) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)),
      wsEvalR (ws.map fun t => (p * t.1, φ t.2)) u f x = p.eval u • wsEvalR (ws.map fun t => (t.1, φ t.2)) u f x
  | [] => by simp [wsEvalR]
  | t :: ws => by
    have ih := wsEvalR_map_mul p φ u f x ws
    simp only [wsEvalR, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, smul_add, Polynomial.eval_mul, mul_smul]

theorem fexp_words : ∀ (gens : List (GenW k r)), (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) →
    ∀ t ∈ fexp gens, t.2.length ≤ gens.length ∧ ∀ X ∈ t.2, B.inLie k r X
  | [], _, t, ht => by
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | gn :: gs, hL, t, ht => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have ih := fexp_words gs hL'
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨dX, hdX, s, hs, rfl⟩
    · have := (ih s hs).1
      refine ⟨?_, (ih s hs).2⟩
      show s.2.length ≤ (gn :: gs).length
      simp only [List.length_cons]; omega
    · have := (ih s hs).1
      refine ⟨?_, ?_⟩
      · show (dX.2 :: s.2).length ≤ (gn :: gs).length
        simp only [List.length_cons]; omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact hL gn (by simp) dX hdX
        · exact (ih s hs).2 X hX

theorem ws_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {x X : B.Mat k r} (hx : x ∈ O)
    (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (u : ℂ) (f : B.Mat k r → E) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)), (∀ t ∈ ws, Rep ((1 : ℕ) : ℕ∞) O (B.Rw t.2 f)) →
      HasDerivAt (fun s : ℝ => wsEvalR ws u f (x * NormedSpace.exp ((s : ℂ) • X)))
        (wsEvalR (ws.map fun t => (t.1, X :: t.2)) u f x) 0
  | [], _ => by
    have e : ∀ y, wsEvalR ([] : List (Polynomial ℂ × List (B.Mat k r))) u f y = (0 : E) := fun y => by
      simp [wsEvalR]
    simp only [List.map_nil, e]
    exact hasDerivAt_const _ _
  | t :: ws, h => by
    have h1 := (rep_hasDerivAt hO hx hxG hX (h t (by simp))).const_smul (t.1.eval u)
    have h2 := ws_hasDerivAt hO hx hxG hX u f ws (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have e1 : (fun s : ℝ => wsEvalR (t :: ws) u f (x * NormedSpace.exp ((s : ℂ) • X))) =
        fun s : ℝ => t.1.eval u • B.Rw t.2 f (x * NormedSpace.exp ((s : ℂ) • X)) +
          wsEvalR ws u f (x * NormedSpace.exp ((s : ℂ) • X)) := by
      funext s; simp only [wsEvalR, List.map_cons, List.sum_cons]
    have e2 : wsEvalR ((t :: ws).map fun t => (t.1, X :: t.2)) u f x =
        t.1.eval u • RdV X (B.Rw t.2 f) x + wsEvalR (ws.map fun t => (t.1, X :: t.2)) u f x := by
      simp only [wsEvalR, List.map_cons, List.sum_cons] <;> rfl
    rw [e1, e2]
    exact h1.add h2

theorem right_generator_word_evaluation (u : ℂ) : ∀ (gens : List (GenW k r)) (O : Set (B.Mat k r)) (f : B.Mat k r → E), IsOpen O →
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → Rep (gens.length : ℕ∞) O f → ∀ x ∈ O, x ∈ B.GV k r →
      (gens.map (fun gn => genOpR gn u)).foldr (fun T h => T h) f x = wsEvalR (fexp gens) u f x
  | [], O, f, _, _, _, x, _, _ => by simp [fexp, wsEvalR, B.Rw]
  | gn :: gs, O, f, hO, hL, hf, x, hx, hxG => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have hf' : Rep (gs.length : ℕ∞) O f := rep_mono (by exact_mod_cast (by simp : gs.length ≤ (gn :: gs).length)) hf
    have IH := right_generator_word_evaluation u gs O f hO hL' hf'
    have hW := fexp_words gs hL'
    have hrep : ∀ t ∈ fexp gs, Rep ((1 : ℕ) : ℕ∞) O (B.Rw t.2 f) := fun t ht =>
      rep_Rw hO hf t.2 (hW t ht).2 1 (by have := (hW t ht).1; simp only [List.length_cons]; omega)
    have hD : ∀ X, B.inLie k r X → RdV X (wsEvalR (fexp gs) u f) x =
        wsEvalR ((fexp gs).map fun t => (t.1, X :: t.2)) u f x := fun X hX =>
      (ws_hasDerivAt hO hx hxG hX u f (fexp gs) hrep).deriv
    have hR : wsEvalR (fexp (gn :: gs)) u f x = gn.1.eval u • wsEvalR (fexp gs) u f x +
        (gn.2.map fun dX => dX.1 • wsEvalR ((fexp gs).map fun t => (t.1, dX.2 :: t.2)) u f x).sum := by
      simp only [fexp]
      rw [wsEvalR_append, wsEvalR_flatMap]
      congr 1
      · have := wsEvalR_map_mul gn.1 id u f x (fexp gs)
        simpa using this
      · congr 1
        apply List.map_congr_left
        intro dX _
        have := wsEvalR_map_mul (Polynomial.C dX.1) (fun w => dX.2 :: w) u f x (fexp gs)
        simpa using this
    set Φ := (gs.map fun gn => genOpR gn u).foldr (fun T h => T h) f with hΦdef
    have hΦ : ∀ X, B.inLie k r X → RdV X Φ x = RdV X (wsEvalR (fexp gs) u f) x := fun X hX =>
      rdV_congr hO (fun y hy hyG => IH y hy hyG) hx hxG hX
    rw [hR]
    change gn.1.eval u • Φ x + (gn.2.map fun dX => dX.1 • RdV dX.2 Φ x).sum = _
    rw [IH x hx hxG]
    congr 2
    apply List.map_congr_left
    intro dX hdX
    have hX := hL gn (by simp) dX hdX
    rw [hΦ dX.2 hX, hD dX.2 hX]

end FExpR

theorem right_exponential_evaluation : FExpEvalR := by
  intro k r E _ _ gens u UU f hL hf g hg hgG
  obtain ⟨U, f', hU, hgU, hf', he⟩ := hf g hg
  exact FExpR.right_generator_word_evaluation u gens U f hU hL ⟨f', hf', he⟩ g hgU hgG

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open MvPolynomial Finset

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem detShift_prod_coeff {σ ι : Type*} [Fintype ι] (h c : ι → MvPolynomial σ ℂ)
    (hh : ∀ i, (h i).IsHomogeneous 1) (hc : ∀ i, (c i).IsHomogeneous 0)
    (d : σ →₀ ℕ) (hd : d.degree = Fintype.card ι) :
    AddMonoidAlgebra.coeff (∏ i, (h i + c i)) d = AddMonoidAlgebra.coeff (∏ i, h i) d := by
  classical
  rw [Finset.prod_add, coeff_sum, Finset.sum_eq_single Finset.univ]
  · simp
  · intro S _ hS
    have hH : ((∏ i ∈ S, h i) * ∏ i ∈ univ \ S, c i).IsHomogeneous S.card := by
      have := (IsHomogeneous.prod S h (fun _ => 1) (fun i _ => hh i)).mul
        (IsHomogeneous.prod (univ \ S) c (fun _ => 0) (fun i _ => hc i))
      simpa using this
    apply hH.coeff_eq_zero
    rw [hd]
    intro hcard
    exact hS (Finset.eq_univ_of_card S hcard.symm)
  · intro hn
    exact absurd (Finset.mem_powerset.mpr (Finset.subset_univ _)) hn

def detShiftSub : Fin 2 → Polynomial ℂ := ![Polynomial.X, -1]

theorem detShift_aeval_monomial (d : Fin 2 →₀ ℕ) (a : ℂ) :
    aeval detShiftSub (monomial d a) = Polynomial.C (a * (-1) ^ d 1) * Polynomial.X ^ d 0 := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [detShiftSub, Polynomial.algebraMap_eq, map_mul, map_pow, map_neg]
  ring

theorem detShift_aeval_coeff (Q : MvPolynomial (Fin 2) ℂ) (t j : ℕ) (hj : j ≤ t)
    (hQ : Q.IsHomogeneous t) :
    (aeval detShiftSub Q).coeff (t - j) =
      (-1) ^ j * AddMonoidAlgebra.coeff Q (Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j) := by
  classical
  set D : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j with hD
  have hD0 : D 0 = t - j := by simp [hD]
  have hD1 : D 1 = j := by simp [hD]
  have hterm : ∀ d : Fin 2 →₀ ℕ, (aeval detShiftSub (monomial d (AddMonoidAlgebra.coeff Q d))).coeff (t - j) =
      if t - j = d 0 then AddMonoidAlgebra.coeff Q d * (-1) ^ d 1 else 0 := by
    intro d
    rw [detShift_aeval_monomial, Polynomial.coeff_C_mul_X_pow]
  conv_lhs => rw [Q.as_sum]

  rw [map_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single D]
  · rw [hterm, hD0, hD1, if_pos rfl, mul_comm]
  · intro d hd hne
    rw [hterm]
    split_ifs with h0
    · exfalso
      have hdeg : d.degree = t := by
        by_contra hne'
        exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero hne')
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      apply hne
      ext i
      fin_cases i
      · simp [hD0, ← h0]
      · simp only [Fin.mk_one, Fin.isValue, hD1]
        omega
    · rfl
  · intro hn
    rw [hterm, notMem_support_iff.mp hn]
    simp

theorem detShift_factor {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then X 0 - C ((i : ℕ) : ℂ) else 0) + X 1 * C (M (σ i) i) : MvPolynomial (Fin 2) ℂ) =
      ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i)) +
        (if σ i = i then -C ((i : ℕ) : ℂ) else 0) := by
  split_ifs <;> ring

theorem detShift_hom {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i) : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := by
  apply IsHomogeneous.add
  · split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _
  · rw [mul_comm]
    exact isHomogeneous_C_mul_X _ _

theorem detShift_const {t : ℕ} (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then -C ((i : ℕ) : ℂ) else 0) : MvPolynomial (Fin 2) ℂ).IsHomogeneous 0 := by
  split_ifs
  · exact (isHomogeneous_C _ _).neg
  · exact isHomogeneous_zero _ _ _

theorem detShift_subst {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) :
    aeval detShiftSub (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
      ∏ i : Fin t, ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i))) = M.charpoly := by

  rw [Matrix.charpoly, Matrix.det_apply', map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : σ i = i
  · rw [h]
    simp [detShiftSub, Matrix.charmatrix_apply_eq, Polynomial.algebraMap_eq]
    ring
  · simp [detShiftSub, h, Polynomial.algebraMap_eq]

theorem determinant_shift_coefficient : DetShiftCoeff := by
  intro t M j hj
  set D : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j with hD
  set Q : MvPolynomial (Fin 2) ℂ := ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
      ∏ i : Fin t, ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i)) with hQdef
  have hdeg : D.degree = t := by
    rw [hD, map_add (f := _), Finsupp.degree_single, Finsupp.degree_single]
    omega
  have hQ : Q.IsHomogeneous t := by
    apply IsHomogeneous.sum
    intro σ _
    rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin 2) ℂ)]
    simpa using (isHomogeneous_C (Fin 2) (((Equiv.Perm.sign σ : ℤ) : ℂ))).mul
      (IsHomogeneous.prod (univ : Finset (Fin t)) _ (fun _ => 1) (fun i _ => detShift_hom M σ i))
  have hPQ : AddMonoidAlgebra.coeff (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
        ∏ i : Fin t, ((if σ i = i then X 0 - C ((i : ℕ) : ℂ) else 0) + X 1 * C (M (σ i) i))) D =
      AddMonoidAlgebra.coeff Q D := by
    rw [hQdef, coeff_sum, coeff_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin 2) ℂ), coeff_C_mul, coeff_C_mul]
    congr 1
    simp_rw [detShift_factor M σ]
    exact detShift_prod_coeff _ _ (detShift_hom M σ) (detShift_const σ) D (by simp [hdeg])
  rw [hPQ]
  have hC := detShift_aeval_coeff Q t j hj hQ
  rw [hQdef, detShift_subst] at hC
  rw [hC, ← hQdef, ← mul_assoc, ← mul_pow, show ((-1 : ℂ) * -1) = 1 by norm_num, one_pow, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ae_left {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) :
    ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧
      (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
  have := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarN
  have a1 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarW)
  have a2 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarN)
  filter_upwards [a1, a2] with x h1 h2 using ⟨h1, h2⟩

theorem polyTop_of (hKA : KrAA) : PBN.PolyTop := by
  intro Wp Wq _ _ _ _ _ _ P p G s h t hs hq hG
  set q : C.LPt := h ++ [(s, t)] with hqdef
  set Bs := p.T.base with hBs
  by_cases hpos : D.IsLocPt q (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') P.r q
  · by_cases h' : ∃ γ ∈ B.GV P.k P.r, Zhat P.k P.r Bs.z Bs.z' γ = D.ptMatN q (P.r + 1) ∧ D.IsDFrame Bs p.ν' p.m₀ γ
    · obtain ⟨θL, hsplit⟩ := vecV_split Bs p.ν' p.m₀ q hpos h'
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r Bs.z Bs.z' q h'.choose hpos.1 hZ
      have hposG : 0 < Gf P.k P.r Bs.z Bs.z' h'.choose := hGq ▸ hpos.2
      set κ : ℂ := (-1) ^ (s - 1) / t with hκ
      have hA : ∀ y : ℝ, KB.CptCoef Bs (PBN.aaTop Bs y G) := fun y => Formalism.FourierDecayAlt.P.raising_compact_support P.k P.r Wp Wq Bs G y hG
      obtain ⟨c, hc, hcy⟩ := poly_integral (Bs.μW.prod Bs.μN) (D.ptSize h)
        (fun y x => lint Bs h'.choose θL (PBN.aaTop Bs y G) x) (fun x => κ • lint Bs h'.choose θL G x)
        (fun y => (hsplit _ (hA y)).1)
        (by
          filter_upwards [ae_left Bs] with x hx
          obtain ⟨c, hc, hcy⟩ := pt_poly hKA Bs hG h s t hs hq hγ hZ hposG hx
          set a : ℂ := ((θL x : ℝ) : ℂ) * psi P.k P.r Bs.z cStd (Matrix.of x.2) with ha
          set L := ContinuousLinearMap.compL ℂ Wq Wp Wp (Bs.π (Matrix.of x.1)) with hL
          refine ⟨fun n => a • L (c n), ?_, fun y => ?_⟩
          · simp only
            rw [hc, map_smul, smul_comm]
            rfl
          · show a • L (PBG.Kr Bs (PBN.aaTop Bs y G) _) = _

            rw [hcy y, map_sum, Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro n _
            rw [map_smul, smul_comm])
      refine ⟨c, ?_, fun y => ?_⟩
      · rw [hc, integral_smul, ← (hsplit G hG).2]
        rfl
      · show D.vecV Bs p.ν' p.m₀ (PBN.aaTop Bs y G) q = _
        rw [(hsplit _ (hA y)).2, hcy y]
    · refine ⟨fun _ => 0, ?_, fun y => ?_⟩
      · show (0 : Wq →L[ℂ] Wp) = _ • D.vecV Bs p.ν' p.m₀ G q
        unfold D.vecV
        rw [dite_eq_left hpos, dite_eq_right h', smul_zero]
      · show D.vecV Bs p.ν' p.m₀ _ q = _
        unfold D.vecV
        rw [dite_eq_left hpos, dite_eq_right h']
        simp
  · refine ⟨fun _ => 0, ?_, fun y => ?_⟩
    · show (0 : Wq →L[ℂ] Wp) = _ • D.vecV Bs p.ν' p.m₀ G q
      unfold D.vecV
      rw [dite_eq_right hpos, smul_zero]
    · show D.vecV Bs p.ν' p.m₀ _ q = _
      unfold D.vecV
      rw [dite_eq_right hpos]
      simp

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end
