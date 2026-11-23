module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle076
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle040
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle088
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

section K

variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]

def Kset (k r : ℕ) (z b : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) : Set Wp :=
  {x | ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, b] Fr → ∀ w : ℂ, capRep k r π Fr w x = f w • x}

def K (k r : ℕ) (z b : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) : Submodule ℂ Wp :=
  Submodule.span ℂ (Kset k r z b π f)

end K

def FrameLoc : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 2 ≤ k → inWb k r z → 0 < Tz k r z →
    ∀ a₀ : Fin (2 * r + k + 1) → ℂ, 0 < PRho.nrmW k r z a₀ →
      ∃ Fr : (Fin (2 * r + k + 1) → ℂ) → Fin (k - 1) → Fin (2 * r + k + 1) → ℂ,
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fr a₀ ∧ ∀ᶠ a in 𝓝 a₀, IsFrameOf k r [z, SSn.prWv k r z a] (Fr a)

def CapSmooth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r m : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)), Qr.IsRepW k r z π → ∀ w : ℂ,
    ∃ C : (Fin m → Fin (2 * r + k + 1) → ℂ) → (Wp →L[ℂ] Wp), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C ∧
      ∀ Bs, IsFrameOf k r [z] Bs → ∀ v, C Bs v = capRep k r π Bs w v

def EigOrth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r : ℕ)
    (z e : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Qr.IsRepW k r z π →
    (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) →
    (∃ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, e] Fr) →
    ∀ (f g : ℂ → ℂ) (x y : Wp), x ∈ Kset k r z e π f → y ∈ Kset k r z e π g → (∃ w, f w ≠ g w) → inner ℂ x y = 0

def Lagrange : Prop :=
  EigOrth → ∀ (P : M.Par), P.OK → 2 ≤ P.k → ∃ (w : ℂ) (p : M.Ty P → Polynomial ℂ),
    ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      (z e : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)),
      inWb P.k P.r z → 0 < Tz P.k P.r z → IsType P.k P.r z π P.u →
      inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 → herm (Hpk P.k P.r) e e = 1 →
      ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [z, e] Fr →
      ∀ C : Wp →L[ℂ] Wp, (∀ v, C v = capRep P.k P.r π Fr w v) →
      ∀ ρ : M.Ty P, Polynomial.aeval C (p ρ) =
        (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2))).starProjection

def Assembly : Prop := FrameLoc → CapSmooth → EigOrth → Lagrange → PRho.PRhoExists

theorem pRhoExists_of_cut (hA : Assembly) (hF : FrameLoc) (hC : CapSmooth) (hO : EigOrth) (hL : Lagrange) :
    PRho.PRhoExists :=
  hA hF hC hO hL

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

open Formalism.FourierDecayAlt.P.Qx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section iter

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ}

def lev (r i : ℕ) : Fin (r + 1) := ⟨min i r, by omega⟩

theorem lev_castSucc (i : ℕ) (h : i < r) : (⟨i, h⟩ : Fin r).castSucc = lev r i := Fin.ext (by simp [lev]; omega)
theorem lev_succ (i : ℕ) (h : i < r) : (⟨i, h⟩ : Fin r).succ = lev r (i + 1) := Fin.ext (by simp [lev]; omega)
theorem lev_r : lev r r = Fin.last r := Fin.ext (by simp [lev])
theorem lev_zero : lev r 0 = 0 := Fin.ext (by simp [lev])

def Dn (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) : Set (Mx k r) :=
  if h : i < r then D0 k r ⟨i, h⟩ (Dn z z' (i + 1)) else Qx8.Dp k r z z'
termination_by r - i

def Kn (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) (i : ℕ) : Fn k r (Wq →L[ℂ] Wp) :=
  if h : i < r then JxF ⟨i, h⟩ z z' (Kn z z' Φ (i + 1)) else Φ
termination_by r - i

theorem Dn_lt (z z' : Fin (2 * r + k + 1) → ℂ) {i : ℕ} (h : i < r) :
    Dn z z' i = D0 k r ⟨i, h⟩ (Dn z z' (i + 1)) := by
  rw [Dn, dite_eq_left h]

theorem Dn_ge (z z' : Fin (2 * r + k + 1) → ℂ) {i : ℕ} (h : ¬ i < r) : Dn z z' i = Qx8.Dp k r z z' := by
  rw [Dn, dite_eq_right h]

theorem Kn_lt (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) {i : ℕ} (h : i < r) :
    Kn z z' Φ i = JxF ⟨i, h⟩ z z' (Kn z z' Φ (i + 1)) := by
  rw [Kn, dite_eq_left h]

theorem Kn_ge (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) {i : ℕ} (h : ¬ i < r) :
    Kn z z' Φ i = Φ := by
  rw [Kn, dite_eq_right h]

theorem famR {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    FamD z z' π π' (Fin.last r) (Qx8.Dp k r z z') Φ := by
  refine ⟨fun c hc => ?_, fun c₀ hc₀ g₀ hg₀ => ?_⟩
  · have h := Qx8.slice_FF hz hz' hΦ hc
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2.1 (c₀, g₀) ⟨hc₀, hg₀.1, hg₀.2⟩
    exact ⟨U, F, hU, hx, hF, fun x hx _ hg _ => hΦF x hx hg⟩

theorem allLev {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    ∀ j, j ≤ r → IsDom k r z z' (lev r (r - j)) (Dn z z' (r - j)) ∧
      FamD z z' π π' (lev r (r - j)) (Dn z z' (r - j)) (Kn z z' Φ (r - j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.sub_zero]
    rw [lev_r, Dn_ge z z' (lt_irrefl r), Kn_ge z z' Φ (lt_irrefl r)]
    exact ⟨Qx8.Dp_dom k r z z', famR hz hz' hΦ⟩
  | succ j ih =>
    intro hj
    obtain ⟨hD, hF⟩ := ih (by omega)
    have hi : r - (j + 1) < r := by omega
    have e : r - j = r - (j + 1) + 1 := by omega
    rw [e, ← lev_succ _ hi] at hD hF
    rw [← lev_castSucc _ hi, Dn_lt z z' hi, Kn_lt z z' Φ hi]
    exact ⟨descended_set_is_domain _ hD, famStep hz hz' _ hF⟩

def mix (i : ℕ) (c d : Fin r → ℂ) : Fin r → ℂ := fun a => if a.val < i then c a else d a

theorem vals {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (Φ : Fn k r (Wq →L[ℂ] Wp))
    (d : Fin r → ℂ) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    ∀ i, i ≤ r → ∀ X ∈ Glev k r (lev r i) ∩ Dn z z' i,
      wCell k r (lev r i) c * X ∈ Glev k r 0 ∩ Dn z z' 0 ∧
        Kn z z' Φ 0 d (wCell k r (lev r i) c * X) = Kn z z' Φ i (mix i c d) X := by
  intro i
  induction i with
  | zero =>
    intro _ X hX
    have hm : mix 0 c d = d := funext fun a => by simp [mix]
    rw [lev_zero] at hX ⊢
    rw [Qx6.wCell_zero, Matrix.one_mul, hm]
    exact ⟨hX, rfl⟩
  | succ i ih =>
    intro hi X hX
    have hlt : i < r := by omega
    obtain ⟨l, hl⟩ : ∃ l : Fin r, l = ⟨i, hlt⟩ := ⟨_, rfl⟩
    have hli : l.val = i := by rw [hl]
    have hcs : l.castSucc = lev r i := by rw [hl]; exact lev_castSucc i hlt
    have hsc : l.succ = lev r (i + 1) := by rw [hl]; exact lev_succ i hlt
    have hDi : Dn z z' i = D0 k r l (Dn z z' (i + 1)) := by rw [hl]; exact Dn_lt z z' hlt
    have hKi : Kn z z' Φ i = JxF l z z' (Kn z z' Φ (i + 1)) := by rw [hl]; exact Kn_lt z z' Φ hlt
    rw [← hsc] at hX ⊢
    have hcl : c l ≠ 0 := hc l
    have hX' : w1 k r l (c l) * X ∈ Glev k r (lev r i) ∩ Dn z z' i := by
      rw [← hcs, hDi]
      exact ⟨glev_mul (weyl_cell_mem_level_group (l := l) hcl) (glev_succ_le hX.1), (w1_mul_mem_descended_set_iff l _ hcl hX.1).2 hX.2⟩
    obtain ⟨hmem, hval⟩ := ih (by omega) _ hX'
    have hmix : Function.update (mix i c d) l (c l) = mix (i + 1) c d := by
      funext a
      by_cases ha : a = l
      · subst ha; simp [mix, hli]
      · have hne : a.val ≠ i := fun h => ha (Fin.ext (by rw [h, hli]))
        simp only [mix, Function.update_apply, ha, if_false]
        by_cases h1 : a.val < i
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    rw [Qx6.wCell_succ, Matrix.mul_assoc, hcs]
    refine ⟨hmem, ?_⟩
    rw [hval, hKi, descended_function_apply_w1_mul hz hz' l _ _ hcl hX.1, hmix]

end iter

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

theorem self_adjoint_descent_holds : SADescend := by
  intro Wp Wq _ _ _ _ k r z z' π π' hz hz' Φ hΦ
  have hall := allLev (π := π) (π' := π') hz hz' hΦ r le_rfl
  rw [Nat.sub_self, lev_zero] at hall
  obtain ⟨hD, hF⟩ := hall
  refine ⟨Dn z z' 0, hD, Kn z z' Φ 0 (fun _ => 1), famD_FFl hD.1 hF (fun _ => one_ne_zero), ?_⟩
  intro c hc g hg hGG
  have hv := vals hz hz' Φ (fun _ => 1) hc r le_rfl g
    ⟨by rw [lev_r]; exact hg, by rw [Dn_ge z z' (lt_irrefl r)]; exact hGG⟩
  rw [lev_r] at hv
  have hm : mix r c (fun _ => 1) = c := funext fun a => by simp [mix, a.isLt]
  rw [hm, Kn_ge z z' Φ (lt_irrefl r)] at hv
  exact ⟨hv.1.2, hv.2⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end
end

section

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)}
    (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (n : ℕ) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) →
      UBL (C6.Epart fib es) S n (3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  intro es
  induction es with
  | nil =>
    intro _
    have e0 : C6.Epart fib ([] : List (Fin nf × List (Mat k r))) = fun _ => 1 := by
      funext g
      simp [C6.Epart]
    rw [e0]
    simpa using ubl_const (1 : C6.EndH Wp Wq) hSG n (3 * (r + 1))
  | cons e es ih =>
    intro hes
    have hA := ubl_fib D (fib e.1) (hfib e.1) hε hS e.2 (hes e (by simp)) n
    have hB := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have hL := ubl_clm ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ) hSG hA
    have hAB := ubl_app hSG hL hB
    have e1 : C6.Epart fib (e :: es) =
        fun g => ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ
          (Rw e.2 (fib e.1) g)) (C6.Epart fib es g) := by
      funext g
      simp [C6.Epart]
    rw [e1]
    convert hAB using 2
    simp only [List.map_cons, List.sum_cons]
    ring

lemma ubl_coefP (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) (L : Finset (Fin (r + 2))) {κ : ℕ} (P : Mat k r → ℂ)
    (a b : Fin (r + 2) → ℕ) (c : ℕ) (es : List (Fin nf × List (Mat k r))) (hP : U.IsPolyDeg κ P)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) (hes : ∀ e ∈ es, ∀ X ∈ e.2, inLie k r X)
    {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) S n
      (κ + 3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  have hP' := ubl_poly hP S hSG n (3 * (r + 1))
  have hM := ubl_mono hSG (ubl_monoM D L a b c hab hSG hc₀ hSD hSGf n) le_rfl
    (show 2 * r + 2 ≤ 3 * (r + 1) by omega)
  have hPM := ubl_mul hSG hP' hM
  have hE := ubl_epart D fib hfib hε hS n es hes
  let Lm : ℂ →L[ℝ] (C6.EndH Wp Wq →L[ℂ] C6.EndH Wp Wq) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (C6.EndH Wp Wq))).restrictScalars ℝ
  have hA := ubl_clm Lm hSG hPM
  have hAE := ubl_app hSG hA hE
  have e1 : (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) =
      fun g => Lm (P g * C6.monoM D a b c g) (C6.Epart fib es g) := by
    funext g
    simp [Lm]
  rw [e1]
  simpa using hAE

end fac

section cut

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end cut

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def ActHyp (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) : Prop :=
  Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' ∧ Q.IsActualLevel X d.L ∧ Fr.IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y

def GQQ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
    Gauge.FamR P Bs Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ

def IsSSPt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (l : ℕ) (S : ℂ → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) : Prop :=
  ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ), c ∈ OmX P.r → ∀ ζ ∈ Gauge.GC.Ann P,
    ((d.SS l).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      S ζ ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))

end preds

def GQQSSF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → GQQ P Bs e → Gauge.GC.SSF P Bs d e

def SSPointwise : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∃ S, IsSSPt P Bs d l S

def ThConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∃ θ : M.Ty P → ℂ, ∀ ζ ∈ Gauge.GC.Ann P, ∀ π ρ : M.Ty P, M.Up P l π ρ →
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          θ π • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def SSEntry : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → Gauge.GC.SSF P Bs d e →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S → ∀ ζ ∈ Gauge.GC.Ann P, ∀ π ρ : M.Ty P,
      inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (S ζ (e π ζ))) =
        if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) else 0

def ThtGaugeConstOfCore : Prop :=
  GQQSSF → SSPointwise → ThConst → SSEntry → PRho.PRhoExists → PRho.GaugeLines → DatumUnit → ThtGaugeConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

theorem locPt_zero {h : C.LPt} {n : ℕ} (hh : D.IsLocPt h n) (hn : n = 0) : h = [] := by
  rcases h with _ | ⟨b, t⟩
  · rfl
  · exfalso
    have h1 := (hh.1 b (by simp)).1
    have h2 := hh.2
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_cons] at h2
    omega

theorem top_unipotent_integral_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)) (hR : P.r = 0)
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have hh0 : h = [] := locPt_zero hh hR
  subst hh0
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hR
  subst hR
  have e1 : p.ν' = ν'r := by
    rw [← hν]
    funext i
    simp only [D.castV, liftVec]
    rw [dite_eq_left (by simp; omega)]
    exact congrArg ν'r (Fin.ext (by simp))
  have e2 : p.m₀ = m₀r := by
    rw [← hm]
    ext i j
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega)]
    exact congrArg₂ m₀r (Fin.ext (by simp)) (Fin.ext (by simp))
  have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' F []) = F := by
    funext γ
    simp only [D.castF]
    refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem F _).trans ?_
    exact congrArg F (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ)
  simp only [List.nil_append]
  rw [e3]
  subst e1
  subst e2
  rfl

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end
