module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle006
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle097
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Module.HahnBanach
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCx2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section poly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

private theorem deriv_smul_const_at_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℂ) (T : E) :
    deriv (fun t => φ t • T) 0 = deriv φ 0 • T := by
  by_cases hφ : DifferentiableAt ℝ φ 0
  · exact deriv_smul_const hφ T
  by_cases hT : T = 0
  · simp [hT]
  rw [deriv_zero_of_not_differentiableAt hφ, zero_smul]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hφ

  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.2 hT)
  have hℓT : ℓ T ≠ 0 := by
    rw [hℓ]
    exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hT)
  have h2 : DifferentiableAt ℝ (fun t => ℓ (φ t • T) / ℓ T) 0 :=
    ((ℓ.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd).div_const _
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show φ t = ℓ (φ t • T) / ℓ T
  rw [map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hℓT]

private theorem dLR_smul_const_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : B.Mat k r → ℂ) (T : E)
    (u v : List (B.Mat k r)) : B.dLR u v (fun g => φ g • T) = fun g => B.dLR u v φ g • T := by
  have hR : ∀ v : List (B.Mat k r), B.Rw v (fun g => φ g • T) = fun g => B.Rw v φ g • T := by
    intro v
    induction v with
    | nil => rfl
    | cons X v ih =>
      funext g
      show Formalism.REAL.RdV X (B.Rw v fun g => φ g • T) g = Formalism.REAL.RdV X (B.Rw v φ) g • T
      rw [ih]
      exact deriv_smul_const_at_zero _ T
  unfold B.dLR
  rw [hR v]
  induction u with
  | nil => rfl
  | cons X u ih =>
    funext g
    show B.LdV X (u.foldr B.LdV fun g => B.Rw v φ g • T) g = B.LdV X (u.foldr B.LdV (B.Rw v φ)) g • T
    rw [ih]
    exact deriv_smul_const_at_zero _ T

private theorem ckOn_of_contDiff_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (m : ℕ∞) (UU : Set (B.Mat k r)) : B.CkOn m UU f :=
  fun _ _ => ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn, fun _ _ _ => rfl⟩

private theorem pdGood_of_isPolyDeg {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) : pdGood Wp Wq κ c := by
  obtain ⟨hcd, hwb⟩ := PI.UnitaryCorollaryDerivatives.polynomial_bound k r κ c hc
  refine ⟨fun F hF => ?_, fun A m => ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hF g₀ hg₀
    refine ⟨U, fun g => c g • f' g, hU, hgU, hcd.contDiffOn.smul hf', fun g hg hgv => ?_⟩
    simp only [hfe g hg hgv]
  · obtain ⟨C, hC⟩ := hwb m
    refine ⟨2 ^ m * |C|, by positivity, fun F b hF => ?_⟩
    have hab : ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
        u.length + v.length ≤ m → ∀ g ∈ B.GV k r, g ∉ (∅ : Set (B.Mat k r)) →
          ‖B.dLR u v (fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) g‖ ≤ C * B.gN g ^ (κ : ℝ) := by
      intro u v hu hv hl g hg _
      have h1 := hC u v hu hv hl g hg
      simp only [List.map_append, List.sum_append] at h1
      simp only [dLR_smul_const_right, norm_smul]
      have h1' : ‖B.dLR u v c g‖ ≤ C * B.gN g ^ (κ : ℝ) := by simpa using h1
      calc ‖B.dLR u v c g‖ * ‖ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ ≤ ‖B.dLR u v c g‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ C * B.gN g ^ (κ : ℝ) := by rw [mul_one]; exact h1'
    obtain ⟨hP1, hP2⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := B.GV k r)
      (a := fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) isOpen_empty (fun g hg => Or.inr hg)
      (ckOn_of_contDiff_infty _ (hcd.smul contDiff_const) _ _) hab hF (fun g _ h => by simp at h)
    have hfun : Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap (fun g => c g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) F =
        fun g => c g • F g := by
      funext g
      simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap]
    rw [hfun] at hP1 hP2
    refine ⟨hP1, fun u v hu hv hl g hg => ?_⟩
    have hb0 : 0 ≤ b := le_trans
      (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _))
      (hF.2 [] [] (by simp) (by simp) (by simp) g hg)
    calc _ ≤ 2 ^ m * (|C| * |b|) := hP2 u v hu hv hl g hg
      _ = 2 ^ m * |C| * b := by rw [abs_of_nonneg hb0]; ring

theorem pd_good_pow {d : ℕ} {c : B.Mat k r → ℂ} (hc : pdGood Wp Wq d c) :
    ∀ e : ℕ, pdGood Wp Wq (d * e) (fun g => c g ^ e)
  | 0 => pd_good_congr (fun g _ => by simp) (pd_good_const (Wp := Wp) (Wq := Wq) (d * 0) (1 : ℂ))
  | e + 1 => pd_good_congr (fun g _ => (pow_succ (c g) e).symm)
      (pd_good_mul (by rw [Nat.mul_succ]) (pd_good_pow hc e) hc)

theorem pd_good_of_poly {κ : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg κ c) : pdGood Wp Wq κ c :=
  pdGood_of_isPolyDeg hc

end poly

section decay

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pd_good_Gpow (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) :
    pdGood Wp Wq ((2 * r + 2) * q) (fun g : B.Mat k r => ((Gf k r z z' g ^ q : ℝ) : ℂ)) := by
  have := pd_good_pow (Wp := Wp) (Wq := Wq) (pd_good_of_poly (Formalism.FourierDecayAlt.P.gram_function_polynomial k r z z')) q
  simpa only [Complex.ofReal_pow] using this

theorem inCC_Gpow_smul (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) {A₀ : ℝ} {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hf : ∀ m : ℕ, B.InCC A₀ m f) :
    ∀ m : ℕ, B.InCC (A₀ - (((2 * r + 2) * q : ℕ) : ℝ)) m (fun g => ((Gf k r z z' g ^ q : ℝ) : ℂ) • f g) := by
  intro m
  obtain ⟨c, hc⟩ := hf m
  obtain ⟨K, -, hb⟩ := (pd_good_Gpow (Wp := Wp) (Wq := Wq) z z' q).2 (A₀ - (((2 * r + 2) * q : ℕ) : ℝ)) m
  exact ⟨K * c, hb f c (by rwa [sub_add_cancel])⟩

theorem ckOn_Gpow_smul (z z' : Fin (2 * r + k + 1) → ℂ) (q : ℕ) {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hf : B.CkOn ⊤ (B.GV k r) f) : B.CkOn ⊤ (B.GV k r) (fun g => ((Gf k r z z' g ^ q : ℝ) : ℂ) • f g) :=
  (pd_good_Gpow (Wp := Wp) (Wq := Wq) z z' q).1 f hf

end decay

section fpm

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem fpm_id (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) :
    TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ =
      fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g := by
  funext g
  simp only [TBBx4.fpm, ContinuousLinearMap.comp_id]

theorem inCC_fpm_id (p : KB.Pl P Wp Wq) {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (p₀ : ℕ) {A₀ : ℝ}
    (hf : ∀ m : ℕ, B.InCC A₀ m f) :
    ∀ m : ℕ, B.InCC (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) m
      (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) := by
  rw [fpm_id]
  exact inCC_Gpow_smul _ _ p₀ hf

end fpm

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section betaJ

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congrJ_left (D : RealPlaceData k r Wp Wq) {F F₂ G : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D F g = JF D F₂ g) : beta D F G = beta D F₂ G := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F₂ (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

theorem beta_congrJ_right (D : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D G g = JF D G₂ g) : beta D F G = beta D F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

end betaJ

section formJ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)

theorem formLev_congrJ_left (x y x' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hx : ∀ a, JC.NiceCoef (T.bs j) ε (x a)) (hy : ∀ a, JC.NiceCoef (T.bs j) ε (y a))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x x' = D.formLev T s j w y x' := by
  have hQQ : ∀ Y p q, BcGood (T.bs j) ε (D.QQlev T s j Y p q) := fun Y p q => bcGood_tL s Y p q
  have hR := mn_rrop_closure bcGood_closed (D.QQlev T s j) hQQ (D.positionted w)
  unfold D.formLev
  refine Finset.sum_congr rfl fun a _ => beta_congrJ_left (T.bs j) fun h hh => ?_
  rw [bc_core (D.RRlev T s j w) hR x hx a hh, bc_core (D.RRlev T s j w) hR y hy a hh]
  show (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (x b) g)) h =
    (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (y b) g)) h
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (hR a b).2.2 _ _ (fun g hg hgG => hJ b g ⟨hgG, hg⟩) h hh.2 hh.1

theorem formLev_congrJ_right (x' x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x' x = D.formLev T s j w x' y := by
  unfold D.formLev
  exact Finset.sum_congr rfl fun a _ => beta_congrJ_right (T.bs j) (hJ a)

theorem pairJ_congrJ_left (ε : ℝ) : ∀ (ys : List ℝ)
    (x y : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, JC.NiceCoef (T.bs j) ε (x a)) → (∀ a, JC.NiceCoef (T.bs j) ε (y a)) →
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x x' = KB.pairJ (D.formLev T s j w) ys y x'
  | [], x, y, x', hx, hy, hJ => formLev_congrJ_left P0 T s j w x y x' ε hx hy hJ
  | _ :: ys, x, y, x', hx, hy, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_left ε ys (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _),
      pairJ_congrJ_left ε ys (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _)]

theorem pairJ_congrJ_right : ∀ (ys : List ℝ)
    (x' : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x' x = KB.pairJ (D.formLev T s j w) ys x' y
  | [], x', x, y, hJ => formLev_congrJ_right P0 T s j w x' x y hJ
  | _ :: ys, x', x, y, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_right ys _ (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) (fun _ => hJ _),
      pairJ_congrJ_right ys _ (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) (fun _ => hJ _)]

end formJ

end Formalism.FourierDecayAlt.P.PBG
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix
open scoped ComplexConjugate

theorem norm_letter_scal (σ : ℂ) (b : Bool) : ‖(if b then σ else conj σ)‖ = ‖σ‖ := by
  cases b <;> simp

theorem uInv_ccle {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (σ : ℂ)
    (hσ : ‖σ‖ ≤ 2) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat k r → E) (c : ℝ), (∀ e, B.CCle A m (x e) c) →
      ∀ e, B.CCle A m (KB.uInv σ w x e) (3 ^ w.length * c) ∧
        B.CCle A m (fun g => KB.uInv σ w x e g - x e g) (3 ^ w.length * ‖σ‖ * c) := by
  intro w
  induction w with
  | nil =>
    intro x c hx e
    have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
    refine ⟨by simpa [KB.uInv] using hx e, ?_⟩
    simp only [KB.uInv, sub_self, List.length_nil, pow_zero, one_mul]
    exact JCx2.pd_ccle_mono_c BetaSesquilinearity.CCle_zero (by positivity)
  | cons l w ih =>
    intro x c hx e
    have hc : 0 ≤ c := JCx2.pd_ccle_nonneg (hx e)
    have ih0 := ih (fun e' => x (Fin.cons (0 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
    have ih1 := ih (fun e' => x (Fin.cons (1 : Fin 2) e')) c (fun e' => hx _) (fun a => e a.succ)
    have hs : ‖(if l.1 then σ else conj σ)‖ = ‖σ‖ := norm_letter_scal σ l.1
    have h3 : (0 : ℝ) ≤ 3 ^ w.length := by positivity
    have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg _
    have hlen : (l :: w).length = w.length + 1 := rfl
    have hce : e = Fin.cons (e 0) (fun a => e a.succ) := (Fin.cons_self_tail e).symm
    have hp : (3 : ℝ) ^ (l :: w).length = 3 * 3 ^ w.length := by rw [hlen, pow_succ, mul_comm]
    simp only [KB.uInv]
    by_cases he : e 0 = 0
    · rw [ite_eq_left he]
      have hxe : x e = x (Fin.cons (0 : Fin 2) (fun a => e a.succ)) := by
        conv_lhs => rw [hce, he]
      refine ⟨JCx2.pd_ccle_mono_c ih0.1 (by rw [hp]; nlinarith), ?_⟩
      rw [hxe]
      exact JCx2.pd_ccle_mono_c ih0.2 (by rw [hp]; nlinarith [mul_nonneg h3 hσ0])
    · rw [ite_eq_right he]
      have he1 : e 0 = 1 := by
        rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
        · exact absurd h he
        · exact h
      have hxe : x e = x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) := by
        conv_lhs => rw [hce, he1]
      refine ⟨?_, ?_⟩
      · have := BetaSesquilinearity.CCle_add ih1.1 (BetaSesquilinearity.CCle_smul (if l.1 then σ else conj σ) ih0.1)
        rw [hs] at this
        exact JCx2.pd_ccle_mono_c (show B.CCle A m ((KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ)) +
          (if l.1 then σ else conj σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) _ from this)
          (by rw [hp]; nlinarith [mul_nonneg h3 hc])
      · have := BetaSesquilinearity.CCle_add ih1.2 (BetaSesquilinearity.CCle_smul (if l.1 then σ else conj σ) ih0.1)
        rw [hs] at this
        rw [hxe]
        have hf : (fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
            (if l.1 then σ else conj σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ)) g -
            x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) =
            fun g => (KB.uInv σ w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) g -
              x (Fin.cons (1 : Fin 2) (fun a => e a.succ)) g) +
              (if l.1 then σ else conj σ) • KB.uInv σ w (fun e' => x (Fin.cons (0 : Fin 2) e')) (fun a => e a.succ) g := by
          funext g
          simp only [Pi.add_apply, Pi.smul_apply]
          abel
        rw [hf]
        exact JCx2.pd_ccle_mono_c this (by rw [hp]; nlinarith [mul_nonneg h3 hc, mul_nonneg (mul_nonneg h3 hσ0) hc])

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end
end

section

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt

noncomputable section

theorem compact_support_facts : TL.CptFacts := by
  intro k r Wp Wq _ _ _ _ _ Bs F hF
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  refine ⟨⟨ε, hε, ?_⟩, fun Dop hDop => ?_⟩
  · set R' : ℝ := |R| + 1 with hR'
    have hR0 : 0 < R' := by positivity
    obtain ⟨h1, h2⟩ := JCx2.pd_cut_nice (E := Wq →L[ℂ] Wp) hR0 hFs
    have hN : JC.NiceCoef Bs ε (fun g => JCx2.pdPhi (R'⁻¹ • g) • F g) :=
      ⟨h1, fun A m => h2 A m, fun g hg hne => by
        refine hεF g hg ?_
        intro h0; apply hne; simp [h0]⟩
    refine JCx2.mn_nice_congr (fun g hg => ?_) hN
    by_cases h0 : F g = 0
    · simp [h0]
    · have hgR : gN g ≤ R := hR g hg h0
      have hg0 : 0 ≤ gN g := Real.sqrt_nonneg _
      have hsq : JCx2.pdSq (R'⁻¹ • g) ≤ 1 := by
        rw [JCx2.pd_sq_smul, JCx2.pd_sq_eq, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
        have : gN g ≤ R' := by rw [hR']; linarith [le_abs_self R]
        nlinarith
      simp [JCx2.pdPhi, JCx2.pd_chi_one hsq]
  · have hGc : Continuous (Gf k r Bs.z Bs.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _
    have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | Gf k r Bs.z Bs.z' g < ε}, g ∈ GV k r →
        Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
        (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | R < gN g}, g ∈ GV k r → Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
        (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hcl : IsClosed {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} :=
      Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
    have hsub : {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} ⊆ C6.domL Bs ∅ :=
      fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
    have hsF : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
    have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      intro T hT
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg
      refine ⟨hg.1, ?_⟩
      by_contra hlt
      exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
    refine ⟨⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg hgn => ?_⟩
    · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hDop T hT).1) hsT
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
    · refine PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g ?_ hg
      show Gf k r Bs.z Bs.z' g < ε
      by_contra hge
      exact hgn ⟨hg, lt_of_lt_of_le hε (not_lt.1 hge), by simp⟩

end

end Formalism.FourierDecayAlt.P
end
