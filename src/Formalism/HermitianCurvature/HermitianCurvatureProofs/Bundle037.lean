module

public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.StatementMA
public import Formalism.HermitianCurvature.StatementNF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def kapB (n : ℕ) : ℝ := Real.pi ^ ((n + 1) * (n + 4) / 2)

theorem ptSize_two (h : C.LPt) (n : ℕ) (t c : ℂ) :
    D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1) := by
  simp [D.ptSize, List.map_append, List.sum_append]

def SliceOmBlock : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h p : C.LPt) (n : ℕ) (t c : ℂ)
    (hp : p = h ++ [(n + 1, t), (1, c)]) (hle : D.ptSize p ≤ r) (γ : B.Mat k (r - D.ptSize p)),
    D.IsLocPt p (D.ptSize p) →
    Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) z) (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p)) →
    D.sliceAt k r z z' F p γ =
      ((kapB n : ℝ) : ℂ) •
        G.OmBlock U.betaU (n + 1) (fun Z => U.PhiFun k (r - D.ptSize p) (D.ptPerm h) (D.ptDiag h)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z')
          (D.castF (by subst hp; rw [ptSize_two] at hle ⊢; omega) F) Z γ) t c

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section aux

variable {P : M.Par}

theorem nf_actA_fsum (a : MA.A P (MA.DQ P)) {κ : Type} (s : Finset κ) (g : κ → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (∑ k ∈ s, g k) = ∑ k ∈ s, MA.actA P a (g k) := by
  funext π
  rw [Finset.sum_apply]
  unfold MA.actA
  calc ∑ π', (a π π').1 ((∑ c ∈ s, g c) π') = ∑ π', ∑ c ∈ s, (a π π').1 (g c π') := by
        refine Finset.sum_congr rfl fun π' _ => ?_
        rw [Finset.sum_apply]
        exact map_sum (a π π').1 (fun c => g c π') s
    _ = ∑ c ∈ s, ∑ π', (a π π').1 (g c π') := Finset.sum_comm

theorem nf_norm_sum_sq {E : Type*} [SeminormedAddCommGroup E] {κ : Type*} (s : Finset κ) (a : κ → E) :
    ‖∑ k ∈ s, a k‖ ^ 2 ≤ s.card * ∑ k ∈ s, ‖a k‖ ^ 2 := by
  calc ‖∑ k ∈ s, a k‖ ^ 2 ≤ (∑ k ∈ s, ‖a k‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ s.card * ∑ k ∈ s, ‖a k‖ ^ 2 := sq_sum_le_card_mul_sum_sq

theorem nf_pow_le (G : ℝ) (hG : 0 ≤ G) {a N : ℕ} (ha : a ≤ N) : G ^ a ≤ 1 + G ^ (2 * N) := by
  rcases le_total G 1 with h | h
  · have h1 : G ^ a ≤ 1 := pow_le_one₀ hG h
    have h2 : 0 ≤ G ^ (2 * N) := pow_nonneg hG _
    linarith
  · have h1 : G ^ a ≤ G ^ (2 * N) := pow_le_pow_right₀ h (by omega)
    linarith

end aux

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def OmB {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Set (B.Mat k r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g ∧
    ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def IsFrameB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ

def rawJ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) : MA.Qp P.r P.TT → ℂ :=
  fun q => ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq Bs q.1)))

def trJB (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawJ P Bs e J ρ)

def wR (k : ℕ) (TT : ℝ) (ζ : ℂ) : ℝ := Real.sqrt ((Complex.normSq ζ - TT) ^ (k - 1))

def rawR (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) : MA.Qp P.r P.TT → ℂ :=
  fun q => ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
    inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (Φ q.1.1 (NF.muZ P.k P.r μsec q.1.2)))

def FamR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r))
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) : Prop :=
  IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r ∧ x.2 ∈ Dc x.1} ∧
  (∀ c ∈ OmX P.r, Q.IsDom P.k P.r Bs.z Bs.z' (Fin.last P.r) (Dc c)) ∧
  (∀ q : MA.Qp P.r P.TT, NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Dc q.1.1) ∧
  Q.FamFF P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) Dc Φ

end defs

def GTrChain : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs),
      FamR P Bs (fun c => {g | Q.wCell P.k P.r (Fin.last P.r) c * g ∈ OmB Bs}) (Q.resG P.k P.r (Fin.last P.r) J) ∧
      (∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P),
        rawJ P Bs e J ρ = rawR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) ρ) ∧
      ∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (Y : ℝ),
        rawJ P Bs e (Q.CV P.k P.r (Y : ℂ) J) ρ =
          ∑ a : Fin 2, ∑ b : Fin 2, rawR P Bs.μsec e
            (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
              (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
                (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) (Q.resG P.k P.r (Fin.last P.r) J)))) ρ

def GRawSmooth : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ ρ, rawR P Bs.μsec e Φ ρ ∈ MA.smSub P.r P.TT

def GQLFam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2), FamR P Bs Dc (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ)

def GVTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (b : Fin 2),
        FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ∧
        ∀ ρ, MA.toSm P (rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ρ) =
          MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def GVsTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a : Fin 2),
        FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a) Φ) ∧
        ∀ ρ, MA.toSm P (rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a) Φ) ρ) =
          MA.actA P (star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a)) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def GCore : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧
      ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

section act

variable (P : M.Par)

theorem fst_zero : (0 : (MA.DQ P).Pr).1 = 0 := rfl

theorem fst_add (x y : (MA.DQ P).Pr) : (x + y).1 = x.1 + y.1 := rfl

theorem fst_mul (x y : (MA.DQ P).Pr) : (x * y).1 = x.1 * y.1 := rfl

def fstHom : (MA.DQ P).Pr →+ (MA.DQ P).Op where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

theorem fst_sum {ι : Type} (s : Finset ι) (x : ι → (MA.DQ P).Pr) : (∑ i ∈ s, x i).1 = ∑ i ∈ s, (x i).1 :=
  map_sum (fstHom P) x s

theorem op_zero_apply (g : (MA.DQ P).R) : (0 : (MA.DQ P).Op) g = 0 := rfl

theorem op_add_apply (X Z : (MA.DQ P).Op) (g : (MA.DQ P).R) : (X + Z) g = X g + Z g := rfl

def evalHom (g : (MA.DQ P).R) : (MA.DQ P).Op →+ (MA.DQ P).R where
  toFun X := X g
  map_zero' := rfl
  map_add' _ _ := rfl

theorem op_sum_apply {ι : Type} (s : Finset ι) (X : ι → (MA.DQ P).Op) (g : (MA.DQ P).R) :
    (∑ i ∈ s, X i) g = ∑ i ∈ s, X i g :=
  map_sum (evalHom P g) X s

theorem actA_zero (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 0 f = 0 := by
  funext π
  simp only [MA.actA, Matrix.zero_apply, fst_zero, Pi.zero_apply]
  exact Finset.sum_eq_zero fun π' _ => op_zero_apply P (f π')

theorem actA_add (x y : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (x + y) f = MA.actA P x f + MA.actA P y f := by
  funext π
  simp only [MA.actA, Matrix.add_apply, fst_add, Pi.add_apply]
  exact (Finset.sum_congr rfl fun π' _ => op_add_apply P _ _ (f π')).trans Finset.sum_add_distrib

theorem actA_sum {ι : Type} (s : Finset ι) (x : ι → MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (∑ i ∈ s, x i) f = ∑ i ∈ s, MA.actA P (x i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, actA_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, actA_add, ih]

theorem actA_mul (x y : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (x * y) f = MA.actA P x (MA.actA P y f) := by
  funext π
  simp only [MA.actA, Matrix.mul_apply, fst_sum, fst_mul]
  have h1 : ∀ π'' : M.Ty P, (∑ j, (x π j).1 * (y j π'').1) (f π'') =
      ∑ j, (x π j).1 ((y j π'').1 (f π'')) := fun π'' =>
    op_sum_apply P Finset.univ (fun j => (x π j).1 * (y j π'').1) (f π'')
  have h2 : ∀ π' : M.Ty P, (x π π').1 (∑ π'', (y π' π'').1 (f π'')) =
      ∑ π'', (x π π').1 ((y π' π'').1 (f π'')) := fun π' => map_sum (x π π').1 _ _
  exact (Finset.sum_congr rfl fun π'' _ => h1 π'').trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun π' _ => (h2 π').symm))

theorem toSm_of_mem {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) : MA.toSm P u = ⟨u, h⟩ := by
  simp [MA.toSm, h]

theorem toSm_add {u v : MA.Qp P.r P.TT → ℂ} (hu : u ∈ MA.smSub P.r P.TT) (hv : v ∈ MA.smSub P.r P.TT) :
    MA.toSm P (u + v) = MA.toSm P u + MA.toSm P v := by
  rw [toSm_of_mem P hu, toSm_of_mem P hv, toSm_of_mem P (add_mem hu hv)]
  rfl

end act

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end
