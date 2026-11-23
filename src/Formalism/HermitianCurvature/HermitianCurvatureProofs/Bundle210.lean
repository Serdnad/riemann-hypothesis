module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAInv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjugateBlockSingleLastColumn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlkUUMapMuPRn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle148
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle196
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectNonneg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle150
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChiLIntegrable

@[expose] public section

section

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal Formalism.FourierDecayAlt.P.FourTermExpansion
  Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdV_right (X S x : Mat k r) (f : Mat k r → E) (h1 : S * S⁻¹ = 1) (h2 : S⁻¹ * S = 1) :
    RdV X (fun y => f (y * S)) x = RdV (S⁻¹ * X * S) f (x * S) := by
  unfold RdV
  congr 1
  funext t
  have e1 : ((t : ℂ) • (S⁻¹ * X * S)) = S⁻¹ * ((t : ℂ) • X) * S := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, Formalism.QuantumDeterminants.ioh_exp_conj S⁻¹ S _ h1 h2]
  show f (x * NormedSpace.exp ((t : ℂ) • X) * S) = f (x * S * (S⁻¹ * NormedSpace.exp ((t : ℂ) • X) * S))
  congr 1
  calc x * NormedSpace.exp ((t : ℂ) • X) * S
      = x * (S * S⁻¹) * NormedSpace.exp ((t : ℂ) • X) * S := by rw [h1, Matrix.mul_one]
    _ = x * S * (S⁻¹ * NormedSpace.exp ((t : ℂ) • X) * S) := by simp only [Matrix.mul_assoc]

theorem rdV_left (X A x : Mat k r) (f : Mat k r → E) :
    RdV X (fun y => f (A * y)) x = RdV X f (A * x) := by
  unfold RdV
  simp only [Matrix.mul_assoc]

theorem EZ_right (S : Mat k r) (hS : S ∈ GV k r) (f : Mat k r → E) (a b : Fin (2 * r + k + 1)) (x : Mat k r) :
    EZ (Msg k r a b) (fun y => f (y * S)) x = EZ (Mc S a b) f (x * S) := by
  have h := congrFun (congrFun (congrFun (congrFun (EHc_eq_LT (E := E) S hS) a) b) f) (x * S)
  refine Eq.trans ?_ h
  obtain ⟨h1, h2⟩ := gv_inv hS
  show RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) (fun y => f (y * S)) x +
      Complex.I • RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) (fun y => f (y * S)) x = _
  rw [rdV_right _ _ _ _ h1 h2, rdV_right _ _ _ _ h1 h2]
  rfl

theorem EZ_left (A : Mat k r) (Z : Mat k r) (f : Mat k r → E) (x : Mat k r) :
    EZ Z (fun y => f (A * y)) x = EZ Z f (A * x) := by
  unfold EZ
  rw [rdV_left, rdV_left]

theorem fold_right (S : Mat k r) (hS : S ∈ GV k r) (f : Mat k r → E) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      fold (Msg k r) ts (fun y => f (y * S)) = fun x => fold (Mc S) ts f (x * S)
  | [] => rfl
  | t :: ts => by
    funext x
    rw [fold_cons, fold_cons, fold_right S hS f ts, top_apply'', top_apply'']
    congr 1
    exact EZ_right S hS (fold (Mc S) ts f) t.2.1 t.2.2 x

theorem fold_left (A : Mat k r) (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) (f : Mat k r → E) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      fold M ts (fun y => f (A * y)) = fun x => fold M ts f (A * x)
  | [] => rfl
  | t :: ts => by
    funext x
    rw [fold_cons, fold_cons, fold_left A M f ts, top_apply'', top_apply'']
    congr 1
    exact EZ_left A (M t.2.1 t.2.2) (fold M ts f) x

theorem qminor_left {t : ℕ} (A : Mat k r) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E)
    (x : Mat k r) :
    qminorOp (Q.EH k r) a b u (fun y => f (A * y)) x = qminorOp (Q.EH k r) a b u f (A * x) := by
  rw [qm_eq, qm_eq]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [PP]
  rw [fold_left]

theorem qminor_right_all (S : Mat k r) (hS : S ∈ GV k r) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (x : Mat k r) (hx : x * S ∈ GV k r) (hloc : Loc (t : ℕ∞) f (x * S)) :
    qminorOp (Q.EH k r) a b u (fun y => f (y * S)) x =
      ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
        ((∏ j, (S⁻¹) (c j) (a j)) * ∏ j, S (b j) (d j)) • qminorOp (Q.EH k r) c d u f (x * S) := by
  set P := S⁻¹
  set A : (Fin t → Fin (2 * r + k + 1)) → ℂ := fun c => ∏ j, P (c j) (a j) with hA
  set B : (Fin t → Fin (2 * r + k + 1)) → ℂ := fun d => ∏ j, S (b j) (d j) with hB
  have step : ∀ σ : Equiv.Perm (Fin t),
      fold (Mc S) (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) f (x * S) =
        ∑ c, ∑ d, (A c * B d) • PP c d u σ f (x * S) := by
    intro σ
    rw [expandM S hS t _ f (x * S) hx hloc]
    refine (Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ (fun c => ?_)).symm
    simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    congr 1
    · simp only [Function.comp_apply, hA, hB]
      rw [Finset.prod_mul_distrib]
      congr 1
      exact (Equiv.prod_comp σ (fun j => P (c j) (a j))).symm
  rw [qm_eq]
  simp only [PP]
  simp_rw [fold_right S hS f]
  rw [show (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      fold (Mc S) (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) f (x * S)) =
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∑ c, ∑ d, (A c * B d) • PP c d u σ f (x * S) from
    Finset.sum_congr rfl (fun σ _ => by rw [step σ])]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [qm_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal Formalism.FourierDecayAlt.P.FourTermExpansion
  Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open Classical in
theorem sum_sortM {M : Type*} [AddCommGroup M] [Module ℂ M] {t N : ℕ} (F : (Fin t → Fin N) → M)
    (hF : ∀ (d : Fin t → Fin N) (τ : Equiv.Perm (Fin t)), F (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • F d)
    (hF0 : ∀ d : Fin t → Fin N, ¬ Function.Injective d → F d = 0) (W : (Fin t → Fin N) → ℂ) :
    ∑ d, W d • F d = ∑ C ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
      (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * W (C ∘ σ)) • F C := by
  rw [Formalism.FourierDecayAlt.P.CutMP.CapInv.groupingM (fun i : Fin N => (i : ℕ)) Fin.val_injective F hF hF0 W,
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  by_cases h : StrictMono C
  · rw [if_pos h, if_pos (show StrictMono fun l => ((C l : Fin N) : ℕ) from h)]
  · rw [if_neg h, if_neg (show ¬ StrictMono fun l => ((C l : Fin N) : ℕ) from h)]


open Classical in
theorem collapse2 {M : Type*} [AddCommGroup M] [Module ℂ M] {t N : ℕ}
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (A B : (Fin t → Fin N) → ℂ)
    (hr : ∀ c d (τ : Equiv.Perm (Fin t)), D (c ∘ τ) d = ((Equiv.Perm.sign τ : ℤ) : ℂ) • D c d)
    (hr0 : ∀ c d, ¬ Function.Injective c → D c d = 0)
    (hc : ∀ c d (τ : Equiv.Perm (Fin t)), D c (d ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • D c d)
    (hc0 : ∀ c d, ¬ Function.Injective d → D c d = 0) :
    ∑ c, ∑ d, (A c * B d) • D c d =
      ∑ c ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
        ∑ d ∈ Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C),
          ((∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * A (c ∘ σ)) *
            (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * B (d ∘ σ))) • D c d := by
  set S := Finset.univ.filter (fun C : Fin t → Fin N => StrictMono C)
  set Y : (Fin t → Fin N) → M := fun c =>
    ∑ d ∈ S, (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * B (d ∘ σ)) • D c d with hY
  have inner : ∀ c, ∑ d, (A c * B d) • D c d = A c • Y c := by
    intro c
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, sum_sortM (D c) (hc c) (hc0 c) B]
  simp_rw [inner]
  rw [sum_sortM Y (fun c τ => by simp only [hY, hr, smul_comm _ (((Equiv.Perm.sign τ : ℤ) : ℂ)), Finset.smul_sum])
    (fun c hcn => by simp [hY, hr0 c _ hcn]) A]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [hY, Finset.smul_sum, smul_smul]

theorem det_rows {t N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (c a : Fin t → Fin N) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, P ((c ∘ σ) j) (a j) = (P.submatrix c a).det := by
  rw [Matrix.det_apply']
  rfl

theorem det_cols {t N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (b d : Fin t → Fin N) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, S (b j) ((d ∘ σ) j) = (S.submatrix b d).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]


open Classical in
theorem qminor_right (S : Mat k r) (hS : S ∈ GV k r) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (x : Mat k r) (hx : x * S ∈ GV k r) (hloc : Loc (t : ℕ∞) f (x * S)) :
    qminorOp (Q.EH k r) a b u (fun y => f (y * S)) x =
      ∑ c ∈ Finset.univ.filter (fun C : Fin t → Fin (2 * r + k + 1) => StrictMono C),
        ∑ d ∈ Finset.univ.filter (fun C : Fin t → Fin (2 * r + k + 1) => StrictMono C),
          ((S⁻¹.submatrix c a).det * (S.submatrix b d).det) • qminorOp (Q.EH k r) c d u f (x * S) := by
  rw [qminor_right_all S hS a b u f x hx hloc]
  rw [collapse2 (fun c d => qminorOp (Q.EH k r) c d u f (x * S)) (fun c => ∏ j, (S⁻¹) (c j) (a j))
    (fun d => ∏ j, S (b j) (d j))
    (fun c d τ => skewRow c d u f (x * S) τ) (fun c d hc => row_zero c d u f (x * S) hc)
    (fun c d τ => skewCol c u f (x * S) hx hloc d τ) (fun c d hd => col_zero c d u f (x * S) hx hloc hd)]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  rw [det_rows, det_cols]

end Formalism.FourierDecayAlt.P.CutMP.RInvCov
end
end

section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section helpers

variable {k : ℕ}

theorem cast_cancel (a : ℕ) (h1 : a = 0) (h2 : 0 = a) (γ : B.Mat k 0) : h1 ▸ D.castM h2 γ = γ := by
  subst h1; exact Dx2.MN.castM_rfl γ

theorem phiFun_tr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R j ρ' : ℕ) (hj : j = R) (hρ : ρ' = 0)
    (σ : Equiv.Perm (Fin j)) (d : Fin j → ℂ) (z z' : Fin (2 * R + k + 1) → ℂ) (F : B.Mat k R → E)
    (e1 : R = j + 0 + ρ') (e2 : j + 0 + ρ' = R) (γ : B.Mat k ρ') :
    U.PhiFun (s := 0) k ρ' σ d (D.castV e1 z) (D.castV e1 z') (D.castF e2 F) (fun a => a.elim0) γ =
      U.PhiFun (s := 0) k 0 (hj ▸ σ) (hj ▸ d) z z' F (fun a => a.elim0) (hρ ▸ γ) := by
  subst hj; subst hρ
  have h1 : D.castV e1 z = z := Dx2.Tower.castV_rfl z
  have h2 : D.castV e1 z' = z' := Dx2.Tower.castV_rfl z'
  have h3 : D.castF e2 F = F := by funext g; exact congrArg F (Dx2.MN.castM_rfl g)
  rw [h1, h2, h3]

theorem ptMatN_one (ζ : ℂ) : D.ptMatN [(1, ζ)] (0 + 1) = Matrix.of fun _ _ => ζ := by
  ext a b
  have ha : a.val = 0 := by have := a.isLt; omega
  have hb : b.val = 0 := by have := b.isLt; omega
  simp [D.ptMatN, D.ptEntry, ha, hb]

theorem ptMatN_append_head (h : C.LPt) (ζ : ℂ) (R : ℕ) (hR : D.ptSize h = R) :
    D.ptMatN (h ++ [(1, ζ)]) R = D.ptMatN h R := by
  ext a b
  simp only [D.ptMatN, ptEntry_append, hR, a.isLt, b.isLt, and_self, if_true]

theorem isLocPt_app (h : C.LPt) (R : ℕ) (hh : D.IsLocPt h R) (ζ : ℂ) (hζ : ζ ≠ 0) :
    D.IsLocPt (h ++ [(1, ζ)]) (R + 1) := by
  refine ⟨fun b hb => ?_, CompactCoefficientAppend.ptSize_app h R hh ζ⟩
  rcases List.mem_append.1 hb with hb | hb
  · exact hh.1 b hb
  · simp at hb; subst hb; exact ⟨le_refl _, hζ⟩

theorem Tz_lift (R : ℕ) (v : Fin (2 * 0 + k + 1) → ℂ) : Tz k (R + 0) (liftVec k R 0 v) = Tz k 0 v := by
  unfold Tz; rw [herm_lift]

end helpers

section master

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lev_inv {k R : ℕ} (y : B.Mat k 0) (hy : IsUnit y.det) : ιLev k R 0 y⁻¹ = (ιLev k R 0 y)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Dx2.Tower.lev_mul, Matrix.nonsing_inv_mul _ hy, Dx2.Tower.lev_one]



theorem vecV_append_singleton_eq_vecV_sliceAt (k R ρ : ℕ) (hρ : ρ = 0) (e : R + ρ = R) (S : B.RealPlaceData k R Wp Wq) (S0 : B.RealPlaceData k ρ Wp Wq)
    (hzL : D.castV e (liftVec k R ρ S0.z) = S.z) (hzL' : D.castV e (liftVec k R ρ S0.z') = S.z')
    (hπ : ∀ y, S0.π y = S.π (D.castM e (ιLev k R ρ y))) (hπ' : ∀ y, S0.π' y = S.π' (D.castM e (ιLev k R ρ y)))
    (hN : S.μN = D.muN k R) (hW1 : S.μW Set.univ = 1) (hW1' : S.μW' Set.univ = 1)
    (hW01 : S0.μW Set.univ = 1) (hW01' : S0.μW' Set.univ = 1) (hN0 : S0.μN = D.muN k ρ)
    (ν' : Fin (2 * R + k + 1) → ℂ) (m₀ : B.Mat k R) (ν'r : Fin (2 * ρ + k + 1) → ℂ) (m₀r : B.Mat k ρ)
    (hν : D.castV e (liftVec k R ρ ν'r) = ν') (hm : D.castM e (ιLev k R ρ m₀r) = m₀)
    (hFb : D.IsBaseFrame S ν' m₀) (hF0 : D.IsBaseFrame S0 ν'r m₀r)
    (h : C.LPt) (hh : D.IsLocPt h R) (ζ : ℂ) (hζ : ζ ≠ 0)
    (F : B.Mat k R → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef S F) (hR : 1 ≤ R) (e' : ρ = R - D.ptSize h) :
    D.vecV S ν' m₀ F (h ++ [(1, ζ)]) = D.vecV S0 ν'r m₀r (D.castF e' (D.sliceAt k R S.z S.z' F h)) [(1, ζ)] := by
  subst hρ
  have hzS : S.z = liftVec k R 0 S0.z := by rw [← hzL]; exact (Dx2.Tower.castV_rfl _).symm
  have hzS' : S.z' = liftVec k R 0 S0.z' := by rw [← hzL']; exact (Dx2.Tower.castV_rfl _).symm
  have hνS : ν' = liftVec k R 0 ν'r := by rw [← hν]; exact Dx2.Tower.castV_rfl _
  have hmS : m₀ = ιLev k R 0 m₀r := by rw [← hm]; exact Dx2.MN.castM_rfl _
  have hT : Tz k R S.z = Tz k 0 S0.z := by rw [hzS]; exact Tz_lift R S0.z
  have hT' : Tz k R S.z' = Tz k 0 S0.z' := by rw [hzS']; exact Tz_lift R S0.z'
  obtain ⟨hZh, hdR, hQmono, hdd, hw⟩ := CompactCoefficientAppend.perm_app h R hh ζ hζ
  set σR := hh.2 ▸ D.ptPerm h with hσR
  set dR := hh.2 ▸ D.ptDiag h with hdRdef
  set Z := U.hMat σR dR with hZdef
  have hZu : IsUnit Z.det := by rw [hZdef, hMat_monoP]; exact C2x2.isUnit_det_monomialMatrix _ _ hdR
  have hq := isLocPt_app h R hh ζ hζ
  have hG : D.ptG (Tz k R S.z * Tz k R S.z') R (h ++ [(1, ζ)]) =
      Complex.normSq (D.ptMatN h R).det * (Complex.normSq ζ - Tz k R S.z * Tz k R S.z') := by
    unfold D.ptG
    rw [ptMatN_append_one h ζ R hh.2, det_extendOne, ptMatN_append_head h ζ R hh.2, Complex.normSq_mul]
    ring
  have hdetpos : 0 < Complex.normSq (D.ptMatN h R).det := by
    rw [← hZh]; exact Complex.normSq_pos.2 hZu.ne_zero
  by_cases hζT : Complex.normSq ζ ≤ Tz k R S.z * Tz k R S.z'
  · have hL : D.vecV S ν' m₀ F (h ++ [(1, ζ)]) = 0 := by
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨_, hpos⟩
      rw [hG] at hpos
      nlinarith
    rw [hL, vector_level_zero_degenerate rfl S0 ν'r m₀r _ ζ (by rw [← hT, ← hT']; exact hζT)]
  push_neg at hζT
  have hζT0 : Tz k 0 S0.z * Tz k 0 S0.z' < Complex.normSq ζ := by rw [← hT, ← hT']; exact hζT
  obtain ⟨γ0, hγ0G, hZ0, hD0⟩ := exists_frame_level_zero rfl S0 ν'r m₀r hF0 ζ hζT0
  rw [vector_level_zero_eq_jacquet rfl S0 ν'r m₀r hF0 _ ζ hζT0 γ0 hγ0G hZ0 hD0, jacquet_integral_level_zero rfl S0 hN0 _ γ0]
  have hZ0' : Zhat k 0 S0.z S0.z' γ0 = Matrix.of fun _ _ => ζ := by rw [hZ0, ptMatN_one]
  have hγG : U.mMap k R 0 Z γ0 ∈ B.GV k R := (Formalism.FourierDecayAlt.P.slice_membership k R 0).1 Z γ0 hZu.ne_zero hγ0G
  have hZhat : Zhat k R S.z S.z' (U.mMap k R 0 Z γ0) = D.ptMatN (h ++ [(1, ζ)]) (R + 1) := by
    have h1 := zhat_mMap (j := R) S.z S.z' S.z_mem S.z'_mem Z γ0
    refine h1.trans ?_
    rw [hzS, hzS', lowV_liftVec, lowV_liftVec, hZ0', ptMatN_append_one h ζ R hh.2, hZh]
  have hDγ : D.IsDFrame S ν' m₀ (U.mMap k R 0 Z γ0) := by
    rw [hνS, hmS]
    exact dFrame_mMap S S0 hzS hzS' ν'r m₀r Z hZu γ0 (gv_unit hγ0G) ζ hζ hZ0' hD0
  have hpos : 0 < D.ptG (Tz k R S.z * Tz k R S.z') R (h ++ [(1, ζ)]) := by
    rw [hG]; exact mul_pos hdetpos (by linarith)
  rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep k R Wp Wq S ν' m₀ F _ hq _ hFb hpos hγG hZhat hDγ]
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k R Wp Wq S _ _ hq hγG hZhat
  obtain ⟨hFc, Rb, hFs⟩ := CompactCoefficientAppend.cptCoef_cont_supp S F hF
  have hZw : Zhat k R S.z S.z' (U.mMap k R 0 Z γ0) =
      C2.monoP (hq.2 ▸ D.ptPerm (h ++ [(1, ζ)])) (hq.2 ▸ D.ptDiag (h ++ [(1, ζ)])) := by
    rw [hZhat]; exact hQmono
  rw [orbJ_mMap S hN hW1 hW1' S0.z S0.z' hzS hzS' σR dR hdR γ0 hγ0G hrel _ _ hdd hZw hw F hFc hR Rb hFs]

  have hsW0 : SigmaFinite S0.μW := Dx2.OrbJ.sigmaF S0.haarW
  have hsW0' : SigmaFinite S0.μW' := Dx2.OrbJ.sigmaF S0.haarW'
  have hH := haar_lev R 0 e S0.z S.z hzL S.μW S0.μW S.haarW S0.haarW hW1 hW01
  have hH' := haar_lev R 0 e S0.z' S.z' hzL' S.μW' S0.μW' S.haarW' S0.haarW' hW1' hW01'
  rw [hH, hH', Measure.map_prod_map _ _ (levMt_cont R 0 e).measurable (levMt_cont R 0 e).measurable,
    ((levMt_emb R 0 e).prodMap (levMt_emb R 0 e)).integral_map]
  have hae : ∀ᵐ y ∂(S0.μW.prod S0.μW'), Matrix.of y.1 ∈ UWset k 0 S0.z ∧ Matrix.of y.2 ∈ UWset k 0 S0.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S0.μW) (ν := S0.μW')).ae (Dx2.OrbJ.ae_mem S0.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S0.μW) (ν := S0.μW')).ae (Dx2.OrbJ.ae_mem S0.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  obtain ⟨y1, y2⟩ := y
  have hlev : ∀ x : Mt k 0, Matrix.of (levMt R 0 e x) = ιLev k R 0 (Matrix.of x) := by
    intro x; simp only [levMt, Equiv.apply_symm_apply]; exact Dx2.MN.castM_rfl _
  simp only [Prod.map_apply, conjL_apply, hlev, midB_lev]
  have hy2u : IsUnit (Matrix.of y2).det := gv_unit hy.2.1
  rw [← lev_inv _ hy2u, hπ (Matrix.of y1), hπ' (Matrix.of y2)⁻¹, Dx2.MN.castM_rfl, Dx2.MN.castM_rfl]
  congr 2

  show _ = D.sliceAt k R S.z S.z' F h (D.castM e' ((Matrix.of y1)⁻¹ * γ0 * Matrix.of y2))
  unfold D.sliceAt
  rw [dite_eq_left (by rw [hh.2]), phiFun_tr R (D.ptSize h) (R - D.ptSize h) hh.2 (by rw [hh.2]; simp),
    cast_cancel]

end master

end Formalism.FourierDecayAlt.P.PBM
end
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section wts

variable {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ) (C : ℝ)

def RHyp : List ℝ → Prop
  | [] => True
  | y :: ys => (0 < (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re ∧
      (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) ∧ RHyp ys

theorem prodR_props (hC : 0 ≤ C) : ∀ ys : List ℝ, RHyp l0 a e ρ Pv C ys →
    (topRprod l0 a e ρ ys).im = 0 ∧ 0 < (topRprod l0 a e ρ ys).re ∧
      (ys.map fun y => |Pv y|).prod ≤ C ^ ys.length * (topRprod l0 a e ρ ys).re := by
  intro ys
  induction ys with
  | nil => simp [topRprod]
  | cons y ys ih =>
    intro h
    rw [RHyp] at h
    obtain ⟨⟨h1, h2, h3⟩, hr⟩ := h
    obtain ⟨i1, i2, i3⟩ := ih hr
    simp only [topRprod, Complex.mul_im, Complex.mul_re, List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨by rw [i1, h2]; ring, by rw [i1, h2]; simp only [mul_zero, sub_zero]; positivity, ?_⟩
    rw [i1, h2]
    simp only [mul_zero, sub_zero]
    have hp : 0 ≤ (ys.map fun y => |Pv y|).prod := List.prod_nonneg fun x hx => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    calc |Pv y| * (ys.map fun y => |Pv y|).prod ≤ (C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) *
          (C ^ ys.length * (topRprod l0 a e ρ ys).re) := mul_le_mul h3 i3 hp (by positivity)
      _ = C ^ (ys.length + 1) * ((topRprod l0 a e ρ ys).re * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) := by
          ring

end wts

section wts2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem second_defect_plus_word_le (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) (C : ℝ) (hC : 0 ≤ C) (ys : List ℝ)
    (hR : RHyp (p v).l0 a e ρ (S.P v) C ys) :
    del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
      C ^ ys.length * del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ := by
  obtain ⟨i1, i2, i3⟩ := prodR_props (p v).l0 a e ρ (S.P v) C hC ys hR
  have hd : del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ = del2 S p v a e ρ * (topRprod (p v).l0 a e ρ ys).re := by
    unfold del2
    rw [cW_plusW, Complex.mul_re, i1, mul_zero, sub_zero, Real.sqrt_mul' _ i2.le]
    rw [show √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re *
        (√(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re) =
        √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re *
          (√(topRprod (p v).l0 a e ρ ys).re * √(topRprod (p v).l0 a e ρ ys).re) by ring,
      Real.mul_self_sqrt i2.le]
  rw [hd]
  have h0 := second_defect_nonneg S p v a e ρ
  calc del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
        del2 S p v a e ρ * (C ^ ys.length * (topRprod (p v).l0 a e ρ ys).re) := mul_le_mul_of_nonneg_left i3 h0
    _ = _ := by ring

end wts2

end

end Formalism.FourierDecayAlt.P.PBL
end
