module

public import Formalism.FormalDegreeBessel.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.Bundle019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003

@[expose] public section

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient

open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open PI.BesselMapUniq (psiGen)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

variable {k r : ℕ}

def IsClosedMatGroup (U : Set (Mat k r)) : Prop :=
  IsClosed U ∧ (1 : Mat k r) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧
    ∀ a ∈ U, IsUnit a.det ∧ a⁻¹ ∈ U

def IsHaarOn (U : Set (Mat k r)) (μ : Measure (Mt k r)) : Prop :=
  μ {x | Matrix.of x ∉ U} = 0 ∧ (∀ a ∈ U, μ.map (lmulM a) = μ) ∧
    (∀ C : Set (Mt k r), IsCompact C → (∀ x ∈ C, Matrix.of x ∈ U) → μ C < ⊤) ∧ μ ≠ 0

def IsQuotRep (G : Set (Mat k r)) (μG μS ν : Measure (Mt k r)) : Prop :=
  ν {x | Matrix.of x ∉ G} = 0 ∧
    ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = ∫⁻ g, (∫⁻ s, f (lmulM (Matrix.of s) g) ∂μS) ∂ν

def leviW (k r : ℕ) (s : Mat k r) : Mat k r := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then s i j
  else if i = j then 1 else 0

section Twist

variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

end Twist

section Period

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

end Period

theorem col_of_fix {h : Mat k r} {j : Fin (2 * r + k + 1)}
    (hj : h *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  have := congrFun hj i
  simpa [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one, Pi.single_apply] using this

theorem col_out {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {j : Fin (2 * r + k + 1)} (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  apply col_of_fix
  by_cases h1 : j.val < r
  · have := (hh.2.1 ⟨j.val, h1⟩).1
    simpa [Formalism.QuantumDeterminants.eI] using this
  · have h2 : 2 * r + k - j.val < r := by omega
    have := (hh.2.1 ⟨_, h2⟩).2
    have e : Formalism.QuantumDeterminants.esI k r ⟨_, h2⟩ = j := by
      apply Fin.ext; simp only [Formalism.QuantumDeterminants.esI]; omega
    rwa [e] at this

theorem Hpk_row {i i' : Fin (2 * r + k + 1)} (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k))
    (e : i.val + i'.val = 2 * r + k) (l : Fin (2 * r + k + 1)) :
    Hpk k r i' l = if l = i then 1 else 0 := by
  unfold Hpk
  have := l.isLt
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem row_out {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {i : Fin (2 * r + k + 1)} (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  have hlt := i.isLt
  let i' : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have e : i.val + i'.val = 2 * r + k := by simp only [i']; omega
  have hi' : ¬ (r ≤ i'.val ∧ i'.val ≤ r + k) := by omega
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have h1 := congrFun (congrFun hU i') j
  have hrow : ∀ m, (hᴴ * Hpk k r) i' m = Hpk k r i' m := by
    intro m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, col_out hh hi']
    rw [Finset.sum_eq_single i'] <;> simp +contextual
  rw [Matrix.mul_apply] at h1
  simp only [hrow, Hpk_row hi e] at h1
  simpa [eq_comm] using h1

theorem leviW_mul {z : Fin (2 * r + k + 1) → ℂ} {h n : Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : leviW k r (h * n) = h := by
  funext i j
  unfold leviW
  split_ifs with h1 h2
  · rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hn.2.2 j j h1.2.1 h1.2.2 h1.2.1]; simp
    · intro l _ hl
      by_cases hr : r ≤ l.val
      · rw [hn.2.2 l j h1.2.1 h1.2.2 hr]; simp [hl]
      · rw [col_out hh (j := l) (by omega) i, if_neg, zero_mul]
        rintro rfl
        omega
    · simp
  · subst h2
    rw [col_out hh (j := i) (by tauto) i]; simp
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [row_out hh (i := i) (by tauto) j, if_neg h2]
    · rw [col_out hh hj i, if_neg h2]

theorem measurable_lmulM (a : Mat k r) : Measurable (lmulM a : Mt k r → Mt k r) := by
  apply Continuous.measurable
  exact continuous_const.matrix_mul continuous_id

end GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient

end
end

section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsInv (X : Data E r) (φ : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x

def levi (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((φ (cpt X x0 y) : ℝ) : ℂ)) z ξ).re

def rh (X : Data E r) (x : Frame X.Ψ r) : ℝ :=
  -∑ τ, Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖

def phK (X : Data E r) (x : Frame X.Ψ r) : ℝ :=
  -2 * ∑ τ, ∑ i : Fin r, Real.log ‖dmin X.Gm x τ i.castSucc‖

def Everywhere (X : Data E r) (p : ((Frame X.Ψ r → ℝ) → ℝ) → Prop) : Prop :=
  ∀ x0 : Frame X.Ψ r, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    p fun φ => levi X x0 φ z ξ

def EverywhereNe (X : Data E r) (p : ((Frame X.Ψ r → ℝ) → ℝ) → Prop) : Prop :=
  ∀ x0 : Frame X.Ψ r, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    p fun φ => levi X x0 φ z ξ

def GapsGe (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) : Prop :=
  ∀ (τ : X.Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → g ≤ ((la τ i - la τ j : ℤ) : ℝ)

def PairingGe (X : Data E r) (la : Wt X.Ψ r) (m : ℝ) : Prop :=
  ∀ (τ : X.Ψ) (i0 i1 : Fin r), (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → m ≤ ((la τ i1 - la τ i0 : ℤ) : ℝ)

def IsTwoDelta (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ (τ : X.Ψ) (i j : Fin r),
    (((i : ℕ) < X.p0 ↔ (j : ℕ) < X.p0) → la τ i = la τ j) ∧
    ((i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → la τ j = la τ i + 2)

def CuspDecay (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ, (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)) ∧
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
      (∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ : X.Ψ, X.tt ξ x τ

def IsExtra (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  0 ≤ a ∧ IsInv X ps ∧ ContDiffOn ℝ ∞ ps X.dom ∧ (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C) ∧
    CuspDecay X ps a

def wnorm (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm la (w j) x ^ 2)

def bb (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2

def Crh (X : Data E r) : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ)

structure ThetaIn (X : Data E r) where

  L : Wt X.Ψ r

  Fp : Wt X.Ψ r

  de2 : Wt X.Ψ r
  twoDelta_spec : IsTwoDelta X de2
  L_gaps : GapsGe X L 0
  L_pair : PairingGe X L 1
  Fp_gaps : GapsGe X Fp 0
  Fp_pair : PairingGe X Fp 1

  T : ℕ

  i : ℕ

  g0h : ℕ

  c : ℝ

  RR : ℝ
  dp : ℝ
  qp : ℝ

  a1 : ℝ

  η : ℝ
  two_le_D : 2 ≤ nd X
  T_ge : 11 * nd X ^ 2 ≤ T
  i_pos : 0 < i
  genusHeight_pos : 0 < g0h
  c_pos : 0 < c
  one_le_RR : 1 ≤ RR
  dp_pos : 0 < dp
  qp_pos : 0 < qp
  frame_theta_weight_pos : 0 < a1
  η_pos : 0 < η

  Tcg : (T : ℝ) * c * (2 * g0h) ≤ 1

  tr_le : (1 + RR * T * c * dp ^ 2 * qp / 2 / a1) * r ≤ 2 * T

  marginA : bb X < 19 / 5 * (T : ℝ) - 2 * T

  marginB : bb X ^ 2 * Crh X + bb X < 19 / 10 * ((nd X : ℝ) + 2) * T

  N : ℕ
  w : Fin N → Frame X.Ψ r → ℂ
  et : Frame X.Ψ r → ℂ
  th1 : Frame X.Ψ r → ℂ
  th2 : Frame X.Ψ r → ℂ
  thp : Frame X.Ψ r → ℂ
  w_bdd : ∀ j, X.IsBddSec L (w j)

  et_bdd : X.IsBddSec ((i * g0h) • de2) et

  firstTheta_bounded : X.IsBddSec (2 • L - de2) th1

  secondTheta_bounded : X.IsBddSec ((nd X + 4) • L - Fp) th2
  thp_bdd : X.IsBddSec Fp thp
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  firstTheta_ne_zero : ∃ x ∈ X.dom, th1 x ≠ 0
  secondTheta_ne_zero : ∃ x ∈ X.dom, th2 x ≠ 0
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0

  ph : Frame X.Ψ r → ℝ
  ph_inv : IsInv X ph
  ph_nonneg : ∀ x ∈ X.dom, 0 ≤ ph x

  w_lower : ∃ C : ℝ, ∀ x ∈ X.dom, Real.exp (-(C + c * ph x)) ≤ wnorm X L w x

  et_upper : ∃ P : ℝ, ∀ x ∈ X.dom,
    X.pnorm ((i * g0h) • de2) et x ≤ Real.exp (-((i : ℝ) * (ph x - P)))

  ph_lower : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, X.la1 x < ε →
    1 / (4 * RR * dp ^ 2 * X.la1 x ^ 2) ≤ ph x

  ph_upper : ∀ x ∈ X.dom, ph x ≤ qp * dp ^ 2 / (2 * X.la1 x ^ 2)

  ps0 : Frame X.Ψ r → ℝ
  extraDivisor_isExtra : IsExtra X ps0 a1

  curvature_lower_bound : Everywhere X fun Lv => -((r : ℝ) / 2 * Lv (phla X de2)) ≤ Lv ps0

  L_curv : EverywhereNe X fun Lv => 0 < Lv (phla X L)

  Lde_curv : EverywhereNe X fun Lv => 1 / 2 * Lv (phla X de2) < Lv (phla X L)

  curvA : Everywhere X fun Lv =>
    2 * η * Lv (phla X L) + 19 / 5 * (T : ℝ) * Lv (rh X) ≤
      Lv (phla X Fp) - Lv (phK X) - (nd X : ℝ) * Lv (phla X L)

  curvB : Everywhere X fun Lv =>
    19 / 10 * ((nd X : ℝ) + 2) * T * Lv (rh X) ≤ Lv (phla X Fp) - Lv (phK X)

namespace ThetaIn

variable {X : Data E r} (I : ThetaIn X)

end ThetaIn

end

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.LamCM

section Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R]

abbrev epsAt (t : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ t)

def IsTan {G : Over S} [GrpObj G] (t : Sp R ⟶ S) (v : epsAt t ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left

def IsMultiple {G : Over S} {t : Sp R ⟶ S} (x : R) (v w : epsAt t ⟶ G) : Prop :=
  w.left = spMap (epsScaleR x) ≫ v.left

end Lie

section Line

variable {K : Type} [Field K] [NumberField K]

abbrev genPt (K : Type) [Field K] [NumberField K] : Sp K ⟶ Sp (𝓞 K) := spMap (algebraMap (𝓞 K) K)

end Line

section Pol

variable {K : Type} [Field K] [NumberField K]

end Pol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

def psi (H : Host E) : Set (E →+* ℂ) := {τ | τ (H.rt : E) = H.rt0}

def psiBar (H : Host E) : Set (E →+* ℂ) := {τ | τ (H.rt : E) = -H.rt0}

structure CMObj (c : Coeff l) (p q : ℕ) : Type 1 where

  K : Type
  [field : Field K]
  [numberField : NumberField K]
  [alg : Algebra c.F K]

  B : Out.PolAV (Sp (𝓞 K))

  AP : Out.PolAV (Sp (𝓞 K))

  AC : Out.PolAV (Sp (𝓞 K))
  ιB : Out.RingAct B.A (𝓞 E)
  ιP : Out.RingAct AP.A (𝓞 E)
  ιC : Out.RingAct AC.A (𝓞 E)

  φP : Fin p → (AP.A ⟶ B.A)
  φP_hom : ∀ j, IsMonHom (φP j)
  φP_lin : ∀ j a, ιP.act a ≫ φP j = φP j ≫ ιB.act a

  φC : Fin q → (AC.A ⟶ B.A)
  φC_hom : ∀ j, IsMonHom (φC j)
  φC_lin : ∀ j a, ιC.act a ≫ φC j = φC j ≫ ιB.act a

  hP : Fin p → 𝓞 E

  hC : Fin q → 𝓞 E

  ηP : psi H → (epsAt (genPt K) ⟶ AP.A)

  ηC : psiBar H → (epsAt (genPt K) ⟶ AC.A)

  ℓP : psi H → MLine K

  ℓC : psiBar H → MLine K

attribute [instance] CMObj.field CMObj.numberField CMObj.alg

namespace CMObj

variable {c : Coeff l} {p q : ℕ} (o : CMObj c p q)

end CMObj

end GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull
end
end
