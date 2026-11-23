module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] (ι : K → Type*) {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M]


variable {ι}

end Objects

section Support

variable {S : Type*} [CommRing S] (M : Type*) [AddCommGroup M] [Module S M]

end Support

section Cycle

variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
variable (M : Type*) [AddCommGroup M] [Module (MRing ι F) M]

end Cycle

section Statements

def HilbertIncrement.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)) (b : K) (i : ι b),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    1 ≤ d → (X ⟨b, i⟩ : MRing ι F) ∉ q →
    (∀ a : K → ℤ, hilbFn q a - hilbFn q (a - Pi.single b 1) =
        hilbFn (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) a) ∧
    ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d - 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

end Statements

section Examples

variable {K : Type*} [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def DegreePositive.Statement : Prop :=
  ∀ (F : Type) [Field F] (ι₀ : Type) [Fintype ι₀] (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (D : ℕ),
    IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def MultiDegreePositive.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin e => fun _ : K => (1 : ℤ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} (F : Type) [Field F]

def segreMap : MRing (fun _ : Unit => ∀ k, ι k) F →ₐ[F] MRing ι F :=
  aeval fun v => ∏ k, X ⟨k, v.2 k⟩

def segrePrime (q : Ideal (MRing ι F)) : Ideal (MRing (fun _ : Unit => ∀ k, ι k) F) :=
  q.comap (segreMap F)

theorem segreMap_X (f : ∀ k, ι k) :
    segreMap F (X ⟨(), f⟩ : MRing (fun _ : Unit => ∀ k, ι k) F) = ∏ k, X ⟨k, f k⟩ :=
  aeval_X _ _

instance segrePrime.isPrime (q : Ideal (MRing ι F)) [q.IsPrime] : (segrePrime F q).IsPrime :=
  Ideal.comap_isPrime _ _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Classical

noncomputable section

universe u v

section Objects

variable {K : Type*} [DecidableEq K]

def unitDeg (k : K) : K → ℤ := Pi.single k 1

variable [Fintype K] {ι : K → Type*} {F : Type*} [Field F]

structure IsMultigrading (ι : K → Type*) (M : Type*) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    (piece : (K → ℤ) → Submodule F M) : Prop where
  internal : DirectSum.IsInternal piece
  smul_mem : ∀ (v : Σ k, ι k) (m : K → ℤ) (x : M), x ∈ piece m →
    (X v : MRing ι F) • x ∈ piece (m + unitDeg v.1)

def modMultAt {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module (MRing ι R) M]
    (W : Ideal (MRing ι R)) [W.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M)


open Classical in
def topCycleNum (F : Type*) [Field F] (ι : K → Type*) (M : Type*) [AddCommGroup M] [Module (MRing ι F) M] (d : ℕ) (bs : Fin d → K → ℤ) :
    ℤ :=
  ∑ᶠ W : Ideal (MRing ι F),
    if h : IsMultiProjPrime W ∧ Module.annihilator (MRing ι F) M ≤ W ∧
        ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
      haveI : W.IsPrime := h.1.isPrime
      ((modMultAt M W).toNat : ℤ) * intNum F W bs
    else 0

end Objects

def MultigradedFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] [Module.Finite (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    ∃ (n : ℕ) (N : Fin (n + 1) → Submodule (MRing ι F) M) (x : Fin n → M) (c : Fin n → K → ℤ)
      (q : Fin n → Ideal (MRing ι F)),
      N 0 = ⊥ ∧ N (Fin.last n) = ⊤ ∧
      (∀ j : Fin n, x j ∈ piece (c j) ∧
        N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ s : MRing ι F, s • x j ∈ N j.castSucc ↔ s ∈ q j) ∧
      ∀ (W : Ideal (MRing ι F)) (hW : W ∈ (Module.annihilator (MRing ι F) M).minimalPrimes),
        (((Finset.univ.filter fun j => q j = W).card : ℕ) : ℕ∞) =
          haveI : W.IsPrime := hW.1.1
          modMultAt M W

def HilbertDimZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ a₀ : ℕ, ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      hilbFn q (fun k => (a k : ℤ)) = intNum F q (![] : Fin 0 → K → ℤ)

def HilbertPrime.AtDim (d : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(hilbFn q (fun k => (a k : ℤ)) : ℝ) -
          (intNum F q (fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)

def HilbertPrime.Statement : Prop := ∀ d : ℕ, HilbertPrime.AtDim.{u} d

def HilbertModule.AtDim (d : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] [Module.Finite (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    (∀ W : Ideal (MRing ι F), IsMultiProjPrime W → Module.annihilator (MRing ι F) M ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(Module.finrank F (piece fun k => (a k : ℤ)) : ℝ) -
          (topCycleNum F ι M d (fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)

def ModulesFromPrimes.Statement : Prop :=
  ∀ d : ℕ, (∀ e ≤ d, HilbertPrime.AtDim.{u} e) → HilbertModule.AtDim.{u, v} d

def HilbertIncrement.Statement : Prop :=
  ∀ d : ℕ, HilbertModule.AtDim.{u, u} d →
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ b : K, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |((hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) : ℤ) : ℝ) -
          (intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) /
            d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)


open Classical in
def IntersectionRecursion.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b : K) (i : ι b), (X ⟨b, i⟩ : MRing ι F) ∉ q → ∀ bs : Fin d → K → ℤ,
      intNum F q (Matrix.vecCons (unitDeg b) bs) =
        ∑ᶠ W : Ideal (MRing ι F),
          if h : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧
              ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
            haveI : W.IsPrime := h.1.isPrime
            ((multAt (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) W).toNat : ℤ) * intNum F W bs
          else 0

def MixedNumberPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ (σ : Equiv.Perm (Fin d)) (bs : Fin d → K → ℤ), intNum F q (bs ∘ σ) = intNum F q bs) ∧
    ∀ (bs : Fin d → K → ℤ) (j : Fin d) (x y : K → ℤ),
      intNum F q (Function.update bs j (x + y)) =
        intNum F q (Function.update bs j x) + intNum F q (Function.update bs j y)

def MultigradedHilbertPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (p : MvPolynomial K ℚ) (a₀ : ℕ), p.totalDegree ≤ d ∧
      ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
        (hilbFn q (fun k => (a k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (a k : ℚ)) p

def RankOfSections.Statement : Prop :=
  ∀ (ι₀ : Type) [Fintype ι₀] (q : Ideal (MRing (fun _ : Unit => ι₀) ℚ)) (D : ℕ),
    IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) ℚ ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    ∃ C : ℝ, ∀ n : ℕ,
      |(hilbFn q (fun _ => (n : ℤ)) : ℝ) -
          (intNum ℚ q (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ) * (n : ℝ) ^ D / D.factorial| ≤
        C * ((n : ℝ) + 1) ^ ((D : ℝ) - 1)

section Examples

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type u} [Field F]

def intWeight : (Σ k, ι k) → K → ℤ := fun v => unitDeg v.1

def ringPiece (m : K → ℤ) : Submodule F (MRing ι F) :=
  weightedHomogeneousSubmodule F (intWeight (ι := ι)) m


omit [∀ k, Fintype (ι k)] in
theorem isMultigrading_ring : IsMultigrading ι (MRing ι F) (ringPiece (F := F) (ι := ι)) := by
  refine ⟨(weightedDecomposition F (intWeight (ι := ι))).isInternal, ?_⟩
  intro v m x hx
  change IsWeightedHomogeneous (intWeight (ι := ι)) x m at hx
  rw [smul_eq_mul]
  change IsWeightedHomogeneous (intWeight (ι := ι)) (X v * x) (m + unitDeg v.1)
  rw [add_comm m (unitDeg v.1)]
  exact (isWeightedHomogeneous_X F (intWeight (ι := ι)) v).mul hx

end Examples

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology NNReal

theorem RootsBounded.continuous_aeval {e : ℕ} (g : MvPolynomial (Fin e) ℚ) :
    Continuous fun y : Fin e → ℂ => aeval y g := by
  have h := MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℂ) g)
  refine h.congr fun y => ?_
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

theorem RootsBounded.proof : RootsBounded.Statement := by
  intro e G hG y₀
  set m := G.natDegree
  let a : ℕ → (Fin e → ℂ) → ℂ := fun k y => aeval y (G.coeff k)
  refine ⟨((1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) : ℝ≥0) : ℝ), ?_⟩
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k ∈ Finset.range m, ‖a k y‖₊ ≤ ‖a k y₀‖₊ + 1 := by
    rw [eventually_all_finset]
    intro k _
    have hc : Continuous fun y => ‖a k y‖₊ :=
      (RootsBounded.continuous_aeval (G.coeff k)).nnnorm
    exact hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _)) |>.mono fun _ h => h.le
  filter_upwards [hev] with y hy t ht
  set P : Polynomial ℂ := G.map (aeval y).toRingHom
  have hPm : P.Monic := hG.map _
  have hdeg : P.natDegree = m := hG.natDegree_map _
  have hroot : P.IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]; exact ht
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hPm.ne_zero hroot
  have hcb : Polynomial.cauchyBound P ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := by
    rw [Polynomial.cauchyBound, hPm.leadingCoeff, nnnorm_one, div_one, add_comm]
    gcongr
    rw [hdeg]
    refine Finset.sup_le fun k hk => ?_
    have hcoeff : P.coeff k = a k y := by
      simp [P, a, Polynomial.coeff_map]
    rw [hcoeff]
    exact (hy k hk).trans (Finset.single_le_sum (f := fun k => ‖a k y₀‖₊ + 1)
      (fun _ _ => bot_le) hk)
  have : ‖t‖₊ ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := (hlt.trans_le hcb).le
  exact_mod_cast this

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

theorem RootsNear.pow_card_le_norm_prod (s : Multiset ℂ) (t₀ : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a ∈ s, ε ≤ dist a t₀) :
    ε ^ Multiset.card s ≤ ‖(s.map fun a => t₀ - a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm]
    have h1 : ε ≤ ‖t₀ - a‖ := by
      rw [← dist_eq_norm, dist_comm]; exact h a (Multiset.mem_cons_self _ _)
    have h2 := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    exact mul_le_mul h1 h2 (pow_nonneg hε _) (norm_nonneg _)

theorem RootsNear.continuous_eval₂ {e : ℕ} (G : Polynomial (MvPolynomial (Fin e) ℚ)) (t : ℂ) :
    Continuous fun y : Fin e → ℂ => G.eval₂ (aeval y).toRingHom t := by
  simp only [Polynomial.eval₂_eq_sum_range]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  have : (fun y : Fin e → ℂ => (aeval y).toRingHom (G.coeff i)) =
      fun y => eval y (MvPolynomial.map (algebraMap ℚ ℂ) (G.coeff i)) := by
    funext y
    simp [MvPolynomial.eval_map, MvPolynomial.aeval_def]
  rw [this]
  exact MvPolynomial.continuous_eval _

theorem RootsNear.proof : RootsNear.Statement := by
  intro e G hG y₀ t₀ h0 ε hε
  have hpos : (0 : ℝ) < ε ^ G.natDegree := pow_pos hε _
  have ht := (RootsNear.continuous_eval₂ G t₀).tendsto y₀
  rw [h0] at ht
  filter_upwards [ht (Metric.ball_mem_nhds 0 hpos)] with y hy
  rw [Set.mem_preimage, mem_ball_zero_iff] at hy
  by_contra hno
  push Not at hno
  set p := G.map (aeval y).toRingHom with hp
  have hpm : p.Monic := hG.map _
  have hdeg : p.natDegree = G.natDegree := hG.natDegree_map _
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm hcard
  have hev : G.eval₂ (aeval y).toRingHom t₀ = (p.roots.map fun a => t₀ - a).prod := by
    rw [← Polynomial.eval_map, ← hp]
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hle := RootsNear.pow_card_le_norm_prod p.roots t₀ hε.le (fun a ha => by
    have ha' : p.eval₂ (RingHom.id ℂ) a = 0 := by
      rw [Polynomial.eval₂_id]; exact (Polynomial.mem_roots hpm.ne_zero).1 ha
    have := hno a (by rw [hp, Polynomial.eval₂_map] at ha'; simpa using ha')
    exact this)
  rw [hcard, hdeg, ← hev] at hle
  exact absurd hy (not_lt.2 hle)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm

noncomputable section

def ChartBergmanBound.Statement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (ψ ρ : (Fin D → ℂ) → ℝ) (y₀ : Fin D → ℂ), IsOpen U → y₀ ∈ U →
    ContDiffOn ℝ 2 ψ U → ContinuousOn ρ U → 0 < ρ y₀ → (∀ w, 0 ≤ levi ψ y₀ w) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ F : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ F U →
      ENNReal.ofReal (‖F y₀‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y₀)) ≤
        ENNReal.ofReal (((((1 / Real.pi : ℝ) : ℂ) • hessC ψ y₀).det.re / ρ y₀ + ε) *
            (n : ℝ) ^ D) *
          ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ρ y)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
