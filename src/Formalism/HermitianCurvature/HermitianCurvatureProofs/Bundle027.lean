module

public import Formalism.HermitianCurvature.StatementQ
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section tdUv

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def tdUv (r : ℕ) (Y : ℂ) : ℕ → Fin 2 → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0, b => if b = 0 then id else fun _ => 0
  | 1, b => if h : 1 ≤ r then (if b = 0 then fun f => Y • f - pbOp ⟨r - 1, by omega⟩ f else cbiOp ⟨r - 1, by omega⟩)
      else fun _ => 0
  | m + 2, b => if h : m + 2 ≤ r then
        fun f => Y • tdUv r Y (m + 1) b f - pbOp ⟨r - (m + 2), by omega⟩ (tdUv r Y (m + 1) b f) -
          cbOp ⟨r - (m + 1), by omega⟩ (cbiOp ⟨r - (m + 2), by omega⟩ (tdUv r Y m b f))
      else fun _ => 0

end tdUv

def JDRvCont : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (r : ℕ) (Y : ℂ) (O : Set (Fin r → ℂ)), IsOpen O → O ⊆ OmX r →
    ∀ f : (Fin r → ℂ) → X, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O → ∀ c ∈ O, ∀ b : Fin 2,
      tdUv r Y r b f c = Q.cmp (Q.vABs r Y r) b f c

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section tdU

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def tdU (r : ℕ) (Y : ℂ) : ℕ → Fin 2 → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0, b => if b = 0 then id else fun _ => 0
  | 1, b => if h : 1 ≤ r then (if b = 0 then fun f => Y • f + pOp ⟨r - 1, by omega⟩ f else ciOp ⟨r - 1, by omega⟩)
      else fun _ => 0
  | m + 2, b => if h : m + 2 ≤ r then
        fun f => Y • tdU r Y (m + 1) b f + pOp ⟨r - (m + 2), by omega⟩ (tdU r Y (m + 1) b f) -
          cOp ⟨r - (m + 1), by omega⟩ (ciOp ⟨r - (m + 2), by omega⟩ (tdU r Y m b f))
      else fun _ => 0

end tdU

def JDRCont : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (r : ℕ) (Y : ℂ) (O : Set (Fin r → ℂ)), IsOpen O → O ⊆ OmX r →
    ∀ f : (Fin r → ℂ) → X, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O → ∀ c ∈ O, ∀ b : Fin 2,
      tdU r Y r b f c = Q.cmp (Q.vAB r Y r) b f c

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.FourierDecayAlt MeasureTheory NumberField

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

noncomputable section

section cls

variable {r : ℕ} {TT : ℝ}

def smM (m : ℕ∞) : WithTop ℕ∞ := ((m : ℕ∞) : WithTop ℕ∞)

end cls

section jets

variable {r : ℕ} {TT : ℝ}


end jets

section ord

variable {r : ℕ} {TT : ℝ}

end ord

section En

variable (P : M.Par) (m : ℕ∞)

end En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FFlM {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (m : ℕ∞) (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (i : Fin (r + 1)) (Dm : Set (Q.Mx k r)) : Set (Q.Mx k r → (Wq →L[ℂ] Wp)) :=
  {J | (∀ g₀ ∈ Q.Glev k r i ∩ Dm, ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ (smM m) F U ∧ ∀ g ∈ U, g ∈ Q.Glev k r i → J g = F g) ∧
    Q.LeftEq k r z i Dm J ∧ Q.RightEq k r z' i Dm J ∧
    ∀ g ∈ Q.Glev k r i ∩ Dm, ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z',
      J (h * g * h') = (π h).comp ((J g).comp (π' h'))}

section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

end place

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def rhoSum (P : M.Par) (ρ : M.Ty P) : ℝ := ∑ i ∈ Finset.Icc 1 (P.k - 1), M.rho P ρ i

def uSum (P : M.Par) : ℝ := ∑ i ∈ Finset.Icc 1 P.k, (P.u i + P.u' i)

theorem aC_eq (P : M.Par) (ρ : M.Ty P) : M.aC P ρ = uSum P / 2 - rhoSum P ρ := rfl

def ThetaNF (P : M.Par) {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜) : 𝒜 :=
  d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs + d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ)) +
    algebraMap ℂ 𝒜 d.L.TT * d.L.GGi * d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))

def GTRTopNF : Prop :=
  ∀ (P : M.Par) (𝒜 : Type) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : Q.NFData P 𝒜),
    P.OK → 2 ≤ P.k → Fr.IsStarLevel d.L → d.Rel → d.L.TT = ((P.TT : ℝ) : ℂ) →
    ∃ c : ℕ → 𝒜, (∀ Y : ℂ, d.QQ Y 0 0 = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) ∧
      ∃ s : ℤ, c P.k = ThetaNF P d + ((s : ℂ)) • (1 : 𝒜)

def GTRTopAct : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ X : Q.ActualOps P.k P.r z z' π π',
    ∃ c : ℕ → Module.End ℂ (Q.RadSp P.k P.r z z' π π'),
      (∀ Y : ℂ, X.t Y 0 0 = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) ∧
      ∃ s : ℤ, ∀ (Φ : Q.RadSp P.k P.r z z' π π'), ∀ x ∈ Q.DomR P.k P.r z z',
        (c P.k Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
            Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
              ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2) +
            ((s : ℂ)) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

def JDRPComm : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Dc : (Fin r → ℂ) → Set (Q.Mx k r)) (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} →
    Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ →
    ∀ (l : Fin r) (Y : ℂ) (a b : Fin 2), ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
      Q.crd (Formalism.QuantumDeterminants.pOp l) (Q.QL k r z z' (Fin.last r) Y a b Ψ) c g =
        Q.QL k r z z' (Fin.last r) Y a b (Q.crd (Formalism.QuantumDeterminants.pOp l) Ψ) c g

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section Struct

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem inK_act_span {G G' : Set V} (M : SlopeTestRemainingChoices S (Pr V)) (hM : ∀ a b, ∀ Φ ∈ G, (M a b).1 Φ ∈ Submodule.span ℂ G')
    (x : Ix S → V) (hx : ∀ a, x a ∈ Submodule.span ℂ G) : ∀ a, ∑ b, (M a b).1 (x b) ∈ Submodule.span ℂ G' := by
  intro a
  refine Submodule.sum_mem _ (fun b _ => ?_)
  have hle : Submodule.span ℂ G ≤ (Submodule.span ℂ G').comap (M a b).1 :=
    Submodule.span_le.mpr (fun Φ hΦ => hM a b Φ hΦ)
  exact hle (hx b)

end Struct

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

end Classes

end Formalism.FourierDecayAlt.P5
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Qx1

theorem model_level_multiplier (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.m0 Y = M.m0A P Y := by
  obtain ⟨-, -, -, -, -, -, hz, -, -, -, -, hGGi, -, hnabs, -⟩ := hL
  simp only [R.LevelData.m0, M.m0A, hz, hGGi, hnabs]

theorem model_level_lowering (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.l0 Y = M.l0A P Y := by
  obtain ⟨-, -, -, -, -, -, -, -, hzb, -, -, hGGi, hnab, -, -⟩ := hL
  simp only [R.LevelData.l0, M.l0A, hzb, hGGi, hnab]

end Qx1

theorem model_is_normal_form : Formalism.FourierDecayAlt.Q.ModelIsNF := by
  intro P L hL Y
  have hm := Qx1.model_level_multiplier P L hL Y
  have hl := Qx1.model_level_lowering P L hL Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -, -, -⟩ := hL
  simp only [NFData.QQ, hm, hl, hGG, hGGi]
  rfl

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem pr_add_fst (p q : Q.Pr V) : (p + q).1 = p.1 + q.1 := rfl
theorem pr_mul_fst (p q : Q.Pr V) : (p * q).1 = p.1 * q.1 := rfl
theorem pr_zero_fst : (0 : Q.Pr V).1 = 0 := rfl
theorem pr_one_fst : (1 : Q.Pr V).1 = 1 := rfl

theorem pr_sum_fst {ι : Type*} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, pr_zero_fst]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_fst, ih]

def actP (M : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : Ix S → V := fun a => ∑ b, (M a b).1 (X b)

theorem polyAction_mul (M N : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : actP (M * N) X = actP M (actP N X) := by
  funext a
  unfold actP

  simp only [Matrix.mul_apply, pr_sum_fst, pr_mul_fst, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  exact Finset.sum_comm

theorem polyAction_one₂ (X : Ix S → V) : actP (1 : SlopeTestRemainingChoices S (Q.Pr V)) X = X := by
  funext a
  unfold actP
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, pr_one_fst]
    rfl
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), pr_zero_fst]
    rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blockMulVec_add (M : SlopeTestRemainingChoices S (Q.Pr V)) (X Y : Ix S → V) : actP M (X + Y) = actP M X + actP M Y := by
  funext a
  simp only [actP, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]

theorem actP_smul (M : SlopeTestRemainingChoices S (Q.Pr V)) (c : ℂ) (X : Ix S → V) : actP M (c • X) = c • actP M X := by
  funext a
  simp only [actP, Pi.smul_apply, map_smul, Finset.smul_sum]

end Act

end Formalism.FourierDecayAlt.P.PBF
end
