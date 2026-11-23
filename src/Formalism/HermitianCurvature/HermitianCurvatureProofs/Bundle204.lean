module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle193
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle191
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle107
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace IdentityZeroOperators

variable {d : ℕ}

def idOp (d : ℕ) : SOp d := ⟨0, fun _ _ _ => 1⟩

def zeroOp (d m : ℕ) : SOp d := ⟨m, fun _ _ _ => 0⟩

lemma idOp_app (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : (idOp d).app u x = u x := by
  change ∑ k : Fin 1, ∑ w : Fin k → Fin d, (1 : ℂ) * pdc (List.ofFn w) u x = u x
  rw [Fin.sum_univ_one]
  change ∑ w : Fin 0 → Fin d, (1 : ℂ) * pdc (List.ofFn w) u x = u x
  simp [pdc]

lemma idOp_symb (x ξ : Fin d → ℝ) : (idOp d).symb x ξ = 1 := by
  change ∑ w : Fin 0 → Fin d, (∏ i : Fin 0, (ξ (w i) : ℂ)) * (1 : ℂ) = 1
  simp

lemma zeroOp_app (m : ℕ) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : (zeroOp d m).app u x = 0 := by
  simp [SOp.app, zeroOp]

lemma zeroOp_symb (m : ℕ) (x ξ : Fin d → ℝ) : (zeroOp d m).symb x ξ = 0 := by
  simp [SOp.symb, zeroOp]

lemma word (hF : SOpField) (O : Set (Fin d → ℝ)) (hO : IsOpen O) :
    ∀ Vs : List ((Fin d → ℝ) → (Fin d → ℝ)), (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) →
    ∃ S : SOp d, S.ord = Vs.length ∧ (∀ i w, ContDiffOn ℝ ∞ (S.a i w) O) ∧
      (∀ u : (Fin d → ℝ) → ℂ, ContDiffOn ℝ (Vs.length : WithTop ℕ∞) u O → ∀ x ∈ O,
        S.app u x = vfW Vs u x) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, S.symb x ξ = (Vs.map fun V => ((ξ ⬝ᵥ V x : ℝ) : ℂ)).prod := by
  intro Vs
  induction Vs with
  | nil =>
    intro _
    exact ⟨idOp d, rfl, fun _ _ => contDiffOn_const, fun u _ x _ => by simp [idOp_app, vfW],
      fun x _ ξ => by simp [idOp_symb]⟩
  | cons V Vs ih =>
    intro hV
    obtain ⟨S, hSo, hSc, hSa, hSs⟩ := ih (fun W hW => hV W (List.mem_cons_of_mem _ hW))
    obtain ⟨S', hS'o, hS'c, hS'a, hS's⟩ := hF d S V O hO hSc (hV V List.mem_cons_self)
    refine ⟨S', by rw [hS'o, hSo]; rfl, hS'c, ?_, ?_⟩
    · intro u hu x hx
      have hl : (V :: Vs).length = S.ord + 1 := by rw [hSo]; rfl
      rw [hl] at hu
      have hu0 : ContDiffOn ℝ (Vs.length : WithTop ℕ∞) u O :=
        hu.of_le (by rw [hSo]; exact_mod_cast Nat.le_succ _)
      rw [hS'a u hu x hx]
      have he : S.app u =ᶠ[nhds x] vfW Vs u := by
        filter_upwards [hO.mem_nhds hx] with y hy
        exact hSa u hu0 y hy
      simp only [vfW, vfD]
      rw [he.fderiv_eq]
    · intro x hx ξ
      rw [hS's x hx ξ, hSs x hx ξ]
      simp

end IdentityZeroOperators

open IdentityZeroOperators in
theorem vector_to_symbol_operator : VOpToSOpOfSteps := by
  intro hF hL hLin d m P O hO hP
  induction P with
  | nil =>
    exact ⟨zeroOp d m, rfl, fun _ _ => contDiffOn_const, fun u _ x _ => by simp [zeroOp_app, WOp.app],
      fun x _ ξ => by simp [zeroOp_symb, WOp.symb]⟩
  | cons t P ih =>
    obtain ⟨T, hTo, hTc, hTa, hTs⟩ := ih (fun s hs => hP s (List.mem_cons_of_mem _ hs))
    obtain ⟨hlen, hsm⟩ := hP t List.mem_cons_self
    obtain ⟨S, hSo, hSc, hSa, hSs⟩ := word hF O hO t.2 hsm
    obtain ⟨S', hS'o, hS'c, hS'a, hS's⟩ := hL d S m O (by rw [hSo]; exact hlen) hSc
    obtain ⟨R, hRo, hRc, hRa, hRs⟩ := hLin d S' T t.1 O (hS'o.trans hTo.symm) hS'c hTc
    refine ⟨R, hRo.trans hS'o, hRc, ?_, ?_⟩
    · intro u hu x hx
      rw [hRa, hS'a, hSa u (hu.of_le (by exact_mod_cast hlen)) x hx, hTa u hu x hx]
      simp [WOp.app]
    · intro x hx ξ
      rw [hRs, hS's, hSs x hx ξ, hTs x hx ξ, hSo]
      simp only [WOp.symb, List.map_cons, List.sum_cons]
      split_ifs <;> simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdGerm

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutMP

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}

theorem pbOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    pbOp l f₁ =ᶠ[𝓝 c] pbOp l f₂ := by
  filter_upwards [h.eventuallyEq_nhds] with c' hc'
  simp only [pbOp, wirtBar, hc'.fderiv_eq]

theorem cbOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbOp l f₁ =ᶠ[𝓝 c] cbOp l f₂ := by
  filter_upwards [h] with c' hc'
  simp only [cbOp, hc']

theorem cbiOp_germ (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbiOp l f₁ =ᶠ[𝓝 c] cbiOp l f₂ := by
  filter_upwards [h] with c' hc'
  simp only [cbiOp, hc']

theorem pbN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    pbN r i f₁ =ᶠ[𝓝 c] pbN r i f₂ := by
  unfold pbN
  split_ifs with hi
  · exact pbOp_germ _ h
  · exact EventuallyEq.rfl

theorem cbN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbN r i f₁ =ᶠ[𝓝 c] cbN r i f₂ := by
  unfold cbN
  split_ifs with hi
  · exact cbOp_germ _ h
  · exact EventuallyEq.rfl

theorem cbiN_germ (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} {c : Fin r → ℂ} (h : f₁ =ᶠ[𝓝 c] f₂) :
    cbiN r i f₁ =ᶠ[𝓝 c] cbiN r i f₂ := by
  unfold cbiN
  split_ifs with hi
  · exact cbiOp_germ _ h
  · exact EventuallyEq.rfl

theorem iteratedOperator_germ (w : ℂ) : ∀ (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X) (c : Fin r → ℂ), f₁ =ᶠ[𝓝 c] f₂ →
    (kvP r w m).1 f₁ =ᶠ[𝓝 c] (kvP r w m).1 f₂ ∧ (kvP r w m).2 f₁ =ᶠ[𝓝 c] (kvP r w m).2 f₂ := by
  intro m
  induction m with
  | zero =>
    intro f₁ f₂ c h
    exact ⟨h, EventuallyEq.rfl⟩
  | succ m ih =>
    intro f₁ f₂ c h
    have hin : (fun c' => (w - (m : ℂ)) • f₁ c' - pbN r (r - m - 1) f₁ c') =ᶠ[𝓝 c]
        (fun c' => (w - (m : ℂ)) • f₂ c' - pbN r (r - m - 1) f₂ c') := by
      filter_upwards [h, pbN_germ (r - m - 1) h] with c' h1 h2
      rw [h1, h2]
    have ih1 := ih _ _ c hin
    have ih2 := ih f₁ f₂ c h
    simp only [kvP]
    refine ⟨?_, ih2.1⟩
    show (fun c' => (kvP r w m).1 _ c' - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₁)) c') =ᶠ[𝓝 c]
      (fun c' => (kvP r w m).1 _ c' - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₂)) c')
    filter_upwards [ih1.1, cbN_germ (r - m) (cbiN_germ (r - m - 1) ih2.2)] with c' h1 h2
    rw [h1, h2]

theorem vABm_germ (y : ℂ) : ∀ (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X) (c : Fin r → ℂ), f₁ =ᶠ[𝓝 c] f₂ →
    (vABm r y m).1 f₁ =ᶠ[𝓝 c] (vABm r y m).1 f₂ ∧ (vABm r y m).2 f₁ =ᶠ[𝓝 c] (vABm r y m).2 f₂ := by
  intro m
  induction m with
  | zero =>
    intro f₁ f₂ c h
    exact ⟨h, EventuallyEq.rfl⟩
  | succ i ih =>
    intro f₁ f₂ c h
    have hgerm := ih f₁ f₂ c h
    by_cases hi : i < r
    · simp only [vABm, dite_eq_left hi]
      refine ⟨?_, cbiOp_germ _ hgerm.1⟩
      filter_upwards [hgerm.1, pbOp_germ ⟨i, hi⟩ hgerm.1, cbOp_germ ⟨i, hi⟩ hgerm.2] with c' h1 h2 h3
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [h1, h2, h3]
    · simp only [vABm, dite_eq_right hi]
      exact hgerm

end Formalism.FourierDecayAlt.P.CutMP.TVCrdGerm
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev GenW (k r : ℕ) := Polynomial ℂ × List (ℂ × B.Mat k r)

def fexp {k r : ℕ} : List (GenW k r) → List (Polynomial ℂ × List (B.Mat k r))
  | [] => [(1, [])]
  | gn :: gs => (fexp gs).map (fun t => (gn.1 * t.1, t.2)) ++
      gn.2.flatMap (fun dX => (fexp gs).map (fun t => (Polynomial.C dX.1 * t.1, dX.2 :: t.2)))

section ops

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def genOpR (gn : GenW k r) (u : ℂ) (F : B.Mat k r → E) : B.Mat k r → E :=
  fun h => gn.1.eval u • F h + (gn.2.map fun dX => dX.1 • Formalism.REAL.RdV dX.2 F h).sum

def genOpL (gn : GenW k r) (u : ℂ) (F : B.Mat k r → E) : B.Mat k r → E :=
  fun h => gn.1.eval u • F h + (gn.2.map fun dX => dX.1 • Q.LdV dX.2 F h).sum

def wsEvalR (ws : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E) (g : B.Mat k r) : E :=
  (ws.map fun t => t.1.eval u • B.Rw t.2 f g).sum

def wsEvalL (ws : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E) (g : B.Mat k r) : E :=
  (ws.map fun t => t.1.eval u • t.2.foldr Q.LdV f g).sum

end ops

def capGen {k r t : ℕ} (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) (i : Fin t) : GenW k r :=
  (if σ i = i then Polynomial.X - Polynomial.C ((i : ℕ) : ℂ) else 0,
    [(1, hpart1 (Hpk k r) (Zg (σ i) i)), (Complex.I, hpart2 (Hpk k r) (Zg (σ i) i))])

def capGens {k r t : ℕ} (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) : List (GenW k r) :=
  List.ofFn (capGen Zg σ)

def zgCV (k r : ℕ) : Fin (Q.mdim k r 0) → Fin (Q.mdim k r 0) → B.Mat k r :=
  fun a b => Matrix.single (Q.posL k r 0 a) (Q.posL k r 0 b) (1 : ℂ)

def zgB {k r : ℕ} (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) : Fin k → Fin k → B.Mat k r :=
  fun a b => Q.unitB (Hpk k r) Bs a b

def RdVRep : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (X : B.Mat k r) (U : Set (B.Mat k r))
    (F f : B.Mat k r → E), B.inLie k r X → IsOpen U → ContDiffOn ℝ 1 F U →
    (∀ g ∈ U, g ∈ B.GV k r → f g = F g) → ∀ h ∈ U, h ∈ B.GV k r →
      Formalism.REAL.RdV X f h = fderiv ℝ F h (h * X) ∧ Q.LdV X f h = fderiv ℝ F h (X * h)

def FExpEvalR : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (gens : List (GenW k r)) (u : ℂ)
    (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → B.CkOn (gens.length : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
      (gens.map (fun gn => genOpR gn u)).foldr (fun T h => T h) f g = wsEvalR (fexp gens) u f g

def FExpEvalL : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (gens : List (GenW k r)) (u : ℂ)
    (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → B.CkOn (gens.length : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
      (gens.map (fun gn => genOpL gn u)).foldr (fun T h => T h) f g = wsEvalL (fexp gens) u f g

def CVAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) (f : B.Mat k r → E) (g : B.Mat k r),
    Q.CV k r Y f g = ∑ σ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgCV k r) σ).map (fun gn => genOpR gn (Q.uC k r 0 Y))).foldr (fun T h => T h) f g

def CapRAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (f : B.Mat k r → E) (g : B.Mat k r),
    Q.capR k r Bs w f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgB Bs) σ).map (fun gn => genOpR gn w)).foldr (fun T h => T h) f g

def CapLAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (f : B.Mat k r → E) (g : B.Mat k r),
    Q.capLft k r Bs w f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgB Bs) σ).reverse.map (fun gn => genOpL gn w)).foldr (fun T h => T h) f g

def FExpDeg : Prop :=
  ∀ (k r : ℕ) (gens : List (GenW k r)), (∀ gn ∈ gens, gn.1.natDegree ≤ 1) →
    ∀ t ∈ fexp gens, t.1.natDegree + t.2.length ≤ gens.length ∧ ∀ X ∈ t.2, ∃ gn ∈ gens, ∃ d : ℂ, (d, X) ∈ gn.2

def FExpSymb : Prop :=
  ∀ (k r : ℕ) (gens : List (GenW k r)) (τ : B.Mat k r → ℂ) (u s : ℂ),
    ((fexp gens).map fun t => t.1.eval u * s ^ t.2.length * (t.2.map τ).prod).sum =
      (gens.map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod

def DetShiftCoeff : Prop :=
  ∀ (t : ℕ) (M : Matrix (Fin t) (Fin t) ℂ) (j : ℕ), j ≤ t →
    AddMonoidAlgebra.coeff (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
        ∏ i : Fin t, ((if σ i = i then MvPolynomial.X 0 - MvPolynomial.C ((i : ℕ) : ℂ) else 0) +
          MvPolynomial.X 1 * MvPolynomial.C (M (σ i) i)))
      (Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j) =
      (-1) ^ j * M.charpoly.coeff (t - j)

def CoeffInterp : Prop :=
  ∀ (N m : ℕ), m ≤ N → ∃ (Ys : Fin (N + 1) → ℝ) (lam : Fin (N + 1) → ℂ),
    ∀ q : Polynomial ℂ, q.natDegree ≤ N → ∑ i, lam i * q.eval (Ys i : ℂ) = q.coeff m

def CapWordsOfParts : Prop :=
  RdVRep → FExpEvalR → CVAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapWords

def CapRWordsOfParts : Prop :=
  RdVRep → FExpEvalR → CapRAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapRWords

def CapLWordsOfParts : Prop :=
  RdVRep → FExpEvalL → CapLAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapLWords

theorem capWords_all_of (hJ : CapWordsOfParts) (hJR : CapRWordsOfParts) (hJL : CapLWordsOfParts) (h1 : RdVRep)
    (hR : FExpEvalR) (hL : FExpEvalL) (hCV : CVAsGens) (hCR : CapRAsGens) (hCL : CapLAsGens) (hD : FExpDeg)
    (hS : FExpSymb) (hDet : DetShiftCoeff) (hI : CoeffInterp) : CapWords ∧ CapRWords ∧ CapLWords :=
  ⟨hJ h1 hR hCV hD hS hDet hI, hJR h1 hR hCR hD hS hDet hI, hJL h1 hL hCL hD hS hDet hI⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def RightRuleEv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z' → IsOpen D → Q.SmoothLev k r 0 D f →
    Q.RightEq k r z' 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (esI k r a) (esI k r b) f g = (if a.val = b.val + 1 then (1 : ℂ) else 0) • f g

def LeftRuleCellv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Q.Mx k r)) (f : Q.Mx k r → E), inWb k r z → IsOpen D →
    (∀ g ∈ Q.Glev k r 0 ∩ D, ∀ n ∈ Q.Nlev k r 0, n * g ∈ D) → Q.SmoothLev k r 0 D f → Q.LeftEq k r z 0 D f →
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D → ∀ a b : Fin r, b.val < a.val →
      Q.EH k r (esI k r b) (esI k r a) f (Q.wCell k r (Fin.last r) c * g) =
        (if a.val = b.val + 1 then star (c a) / star (c b) else 0) • f (Q.wCell k r (Fin.last r) c * g)

def TorusCellv : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r 0 D f → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
    Q.wCell k r (Fin.last r) c * g ∈ D → ∀ l : Fin r,
      Q.EH k r (esI k r l) (esI k r l) f (Q.wCell k r (Fin.last r) c * g) =
        -pbOp l (fun c' => f (Q.wCell k r (Fin.last r) c' * g)) c

def MirrorChainExpansion : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r : ℕ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) (ρ : ℂ), GlRel E →
    ∀ (m : ℕ) (hm : m + 2 ≤ r) (u : ℂ),
    (∀ (x : A) (a : Fin r), r - m - 1 < a.val → La (x * E (esI k r a) (esI k r ⟨r - m - 2, by omega⟩)) = 0) →
    (∀ x : A, La (x * E (esI k r ⟨r - m - 1, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) = La x) →
    (∀ (x : A) (b : Fin r), r - m - 2 < b.val →
      La (E (esI k r ⟨r - m - 2, by omega⟩) (esI k r b) * x) = (if b.val = r - m - 1 then ρ else 0) • La x) →
    La (qminor E (colsVm k r (m + 2)) (colsVm k r (m + 2)) u) =
      La (qminor E (colsVm k r (m + 1)) (colsVm k r (m + 1)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) -
        ρ • La (qminor E (colsVm k r m) (colsVm k r m) u)

end Formalism.FourierDecayAlt.P.CutMP.TVG
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem symbol_operator_linear_holds : SOpLin := by
  intro d S T c O hST hS hT
  obtain ⟨o, a⟩ := S
  obtain ⟨o', b⟩ := T
  simp only at hST
  subst hST
  refine ⟨⟨o, fun k w x => c * a k w x + b k w x⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    exact (contDiffOn_const.mul (hS i w)).add (hT i w)
  · intro u x
    simp only [SOp.app, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  · intro x ξ
    simp only [SOp.symb, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem nilpotent_lie_finite_holds : LieNFin := by
  intro k r
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ (JfS.lieOf (Nset k r))
  have hfin : b.Finite := hli.setFinite
  have : Fintype b := hfin.fintype
  let Xs : Fin (Fintype.card b) → B.Mat k r := fun i => ((Fintype.equivFin b).symm i : B.Mat k r)
  have hrange : Set.range Xs = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin b).symm i).2
    · intro hx
      refine ⟨Fintype.equivFin b ⟨x, hx⟩, ?_⟩
      simp [Xs]
  refine ⟨Fintype.card b, Xs, fun i => hbS ((Fintype.equivFin b).symm i).2, fun X hX => ⟨?_, ?_⟩⟩
  · exact LieSplitPf.lieHpk_of (fun t => (hX t).1)
  · have hmem : X ∈ Submodule.span ℝ (Set.range Xs) := by
      rw [hrange, hspan]
      exact Submodule.subset_span hX
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    refine ⟨a, ?_⟩
    rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext p q
    simp [Matrix.smul_apply, Complex.real_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

namespace Formalism.FourierDecayAlt.P

theorem slice_induction_level : Formalism.FourierDecayAlt.KB.SliceStep :=
  Formalism.FourierDecayAlt.P.PBH.sliceStep_of Formalism.FourierDecayAlt.P.PBH.jfStep (Formalism.FourierDecayAlt.P.PBH.asm_pointStepT Formalism.FourierDecayAlt.P.PBH.pointStep)

end Formalism.FourierDecayAlt.P
end
