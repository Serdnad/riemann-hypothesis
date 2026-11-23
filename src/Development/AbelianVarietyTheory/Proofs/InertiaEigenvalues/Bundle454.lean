module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle305
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle112
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle442
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per



theorem GlobalTheory.PMon.extCoc_dies_in_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → AdmDR P ρ → AdmDR P ρ₂ → ∀ m : ℕ, ∃ v : a × b → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (v i)) - v := by
  intro l _ P AI T a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ hQ hR m
  obtain ⟨Q, hQm⟩ := hQ m
  obtain ⟨R, hRm⟩ := hR m
  let f : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (kd P).comp (fr l m)
  let σ : ↥(GK K) → P.R.BdR →+* P.R.BdR := fun g => ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR)

  let A : ↥(GK K) → Matrix a a P.R.BdR := fun g => (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map f
  let C : ↥(GK K) → Matrix a b P.R.BdR := fun g => (c g).map f
  let D : ↥(GK K) → Matrix b b P.R.BdR := fun g => (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  let Di : ↥(GK K) → Matrix b b P.R.BdR := fun g => (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  have hDDi : ∀ g, D g * Di g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hDiD : ∀ g, Di g * D g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hM : ∀ g, matD P ρ m g = Matrix.fromBlocks (A g) (C g) 0 (D g) := fun g => by
    show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map f = _
    rw [hρ g, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]
  let Qa : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
  let Qb : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
  have hb : ∀ g, D g * Qb.map (σ g) = Qb := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inr i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qb, σ] using h
  have ha : ∀ g, A g * Qa.map (σ g) + C g * Qb.map (σ g) = Qa := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inl i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qa, Qb, σ] using h
  have hRg : ∀ g, D g * (R : Matrix b b P.R.BdR).map (σ g) = R := fun g => hRm g
  let S : Matrix b b P.R.BdR := ((R⁻¹ : GL b P.R.BdR) : Matrix b b P.R.BdR)
  have hSR : S * R = 1 := by simp only [S]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRS : (R : Matrix b b P.R.BdR) * S = 1 := by simp only [S]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgSR : ∀ g, S.map (σ g) * (R : Matrix b b P.R.BdR).map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hSR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgRS : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgS : ∀ g, S.map (σ g) = S * D g := fun g => by
    calc S.map (σ g) = (S * (D g * (R : Matrix b b P.R.BdR).map (σ g))) * S.map (σ g) := by
          rw [hRg g, hSR, Matrix.one_mul]
      _ = S * D g * ((R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g)) := by
          simp only [Matrix.mul_assoc]
      _ = S * D g := by rw [hgRS g, Matrix.mul_one]
  have hgR : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) = Di g * R := fun g => by
    symm
    conv_lhs => rw [← hRg g]
    rw [← Matrix.mul_assoc, hDiD g, Matrix.one_mul]
  obtain ⟨κ, hκdef⟩ : ∃ κ : Matrix b (a ⊕ b) P.R.BdR, κ = S * Qb := ⟨_, rfl⟩
  have hκ : ∀ g, κ.map (σ g) = κ := fun g => by
    rw [hκdef, Matrix.map_mul, hgS g, Matrix.mul_assoc, hb g]
  let Y : Matrix (a ⊕ b) b P.R.BdR :=
    (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) * (R : Matrix b b P.R.BdR)
  have hQQ : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQb : Qb * (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) = 1 := by
    ext i j
    have h := congrFun (congrFun hQQ (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Matrix.one_apply, Qb] using h
  have hY : κ * Y = 1 := by
    simp only [Y]
    rw [hκdef, Matrix.mul_assoc, ← Matrix.mul_assoc Qb, hQb, Matrix.one_mul, hSR]
  obtain ⟨Λ, hκΛ, hΛ⟩ := GlobalTheory.T.exists_invariant_right_inverse P.R.BdR (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1 (↥(GK K)) σ (a ⊕ b) b κ Y hY hκ
  have hQbR : Qb = (R : Matrix b b P.R.BdR) * κ := by
    rw [hκdef, ← Matrix.mul_assoc, hRS, Matrix.one_mul]
  have hgQb : ∀ g, Qb.map (σ g) = (R : Matrix b b P.R.BdR).map (σ g) * κ := fun g => by
    conv_lhs => rw [hQbR]
    rw [Matrix.map_mul, hκ g]
  let Z : Matrix a b P.R.BdR := Qa * Λ
  have hAZ : ∀ g, A g * Z.map (σ g) = Z - C g * (R : Matrix b b P.R.BdR).map (σ g) := fun g => by
    have e : A g * Qa.map (σ g) = Qa - C g * ((R : Matrix b b P.R.BdR).map (σ g) * κ) := by
      rw [← hgQb g]
      exact eq_sub_of_add_eq (ha g)
    simp only [Z]
    rw [Matrix.map_mul, hΛ g, ← Matrix.mul_assoc, e, Matrix.sub_mul, Matrix.mul_assoc (C g),
      Matrix.mul_assoc ((R : Matrix b b P.R.BdR).map (σ g)), hκΛ, Matrix.mul_one]
  refine ⟨vecM (-(Z * S)), fun g => ?_⟩
  have hL : (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = vecM (C g * Di g) := by
    show vecM ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map f) = _
    rw [Matrix.map_mul]
  have hR' : (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (vecM (-(Z * S)) i)) =
      vecM (A g * (-(Z * S)).map (σ g) * Di g) := by
    show (((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map f).mulVec
      (vecM ((-(Z * S)).map (σ g))) = _
    rw [homUnit_mulVec]
  rw [hL, hR']
  have hsub : ∀ X Y : Matrix a b P.R.BdR, vecM X - vecM Y = vecM (X - Y) := fun _ _ => rfl
  rw [hsub]
  congr 1
  have hneg : (-(Z * S)).map (σ g) = -(Z.map (σ g) * S.map (σ g)) := by
    rw [Matrix.map_neg _ (map_neg (σ g)), Matrix.map_mul]
  rw [hneg, hgS g, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc (A g), hAZ g, hgR g]
  simp only [Matrix.sub_mul, Matrix.mul_assoc, hDDi g, hRS, Matrix.mul_one]
  abel
end

section

noncomputable section

namespace GlobalTheory.Cyc.Decomp.Coord

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem inC_zero (F : IntermediateField ℚ_[l] (Om l)) : (0 : PadicComplex l) ∈ inC F :=
  ⟨0, F.zero_mem, UniformSpace.Completion.coe_zero⟩

theorem inC_add {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x + y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u + v, F.add_mem hu hv, UniformSpace.Completion.coe_add _ _⟩

theorem inC_mul {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x * y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u * v, F.mul_mem hu hv, UniformSpace.Completion.coe_mul _ _⟩

theorem inC_zC (F : IntermediateField ℚ_[l] (Om l)) (x : ℤ_[l]) : zC x ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) (x : ℚ_[l]), F.algebraMap_mem _, rfl⟩

theorem inC_sum {F : IntermediateField ℚ_[l] (Om l)} {ι : Type} (s : Finset ι)
    (g : ι → PadicComplex l) (h : ∀ i ∈ s, g i ∈ inC F) : ∑ i ∈ s, g i ∈ inC F :=
  Finset.sum_induction g (· ∈ inC F) (fun _ _ => inC_add) (inC_zero F) h

theorem kap_sum {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) {ι : Type}
    (s : Finset ι) (g : ι → OCO LL) (k : Fin f) :
    kap o (∑ i ∈ s, g i) k = ∑ i ∈ s, kap o (g i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, kap_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, kap_add, ih]

theorem kap_mul_one_tmul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (x : OCO LL) (a : ↥(OL LL)) (k : Fin f) :
    kap o (x * ((1 : OC l) ⊗ₜ[ℤ_[l]] a)) k = ∑ j, kap o x j * zC (o.repr (o j * a) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (OC l) o).sum_repr x]
  rw [Finset.sum_mul, kap_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul,
    kap_tmul, smul_eq_mul, mul_one, mul_one]
  rfl

theorem let_split {O : Type} [CommRing O] {n : ℕ} [NeZero n] (a : LetA O n) :
    ∃ a' : LetA O n, a = ∑ i, letE i * algebraMap O (LetA O n) (PowerSeries.constantCoeff (a i))
      + letπ * a' := by
  refine ⟨fun i => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i), funext fun j => ?_⟩
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [letE, letπ, Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.algebraMap_apply]
    rw [add_comm]
    exact PowerSeries.eq_X_mul_shift_add_const (a j)
  · intro i _ hij
    simp [letE, Pi.single_eq_of_ne hij.symm]
  · simp

theorem coord (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n]
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l)
    (hO : ∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a)
    (hπ : φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) (hc : ‖(c : PadicComplex l)‖ < 1)
    (hcF : (c : PadicComplex l) ∈ inC (Ks K m))
    (hE : ∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) :
    ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  haveI := GlobalTheory.TateDecomp.finite_Ks K m
  have hcl : IsClosed (intC (Ks K m)) := (GlobalTheory.TateDecomp.isCompact_intC (Ks K m)).isClosed
  have key : ∀ (N : ℕ) (k : Fin f) (a : LetA ↥(OL LL) n), ∃ s ∈ inC (Ks K m),
      ∃ r : PadicComplex l, ‖r‖ ≤ 1 ∧ kap o (φ a) k = s + (c : PadicComplex l) ^ N * r := by
    intro N k
    induction N with
    | zero => exact fun a => ⟨0, inC_zero _, kap o (φ a) k, norm_kap_le _ _ _, by simp⟩
    | succ N ih =>
      intro a
      obtain ⟨a', ha⟩ := let_split a
      obtain ⟨s, hs, r, hr, h⟩ := ih a'
      refine ⟨∑ i, kap o (φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))) k
        + (c : PadicComplex l) * s, inC_add (inC_sum _ _ fun i _ => ?_) (inC_mul hcF hs), r, hr, ?_⟩
      · rw [kap_mul_one_tmul]
        exact inC_sum _ _ fun j _ => inC_mul (hE i j) (inC_zC _ _)
      · have e : φ a = ∑ i, φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))
            + (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * φ a' := by
          refine (congrArg φ ha).trans ((φ.map_add _ _).trans ?_)
          congr 1
          · refine (map_sum φ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
            exact (φ.map_mul _ _).trans (congrArg (φ (letE i) * ·) (hO _))
          · exact (φ.map_mul _ _).trans (congrArg (· * φ a') hπ)
        rw [e, kap_add, kap_sum, kap_tmul_one_mul, h, pow_succ', mul_add, mul_assoc, add_assoc]
  intro a k
  refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hc
  obtain ⟨s, hs, r, hr, h⟩ := key N k a
  have hb : ‖(c : PadicComplex l) ^ N * r‖ ≤ ‖(c : PadicComplex l)‖ ^ N := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) hr
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · have e : s = kap o (φ a) k + -((c : PadicComplex l) ^ N * r) := by rw [h]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_kap_le _ _ _) ?_)
    rw [norm_neg]
    exact hb.trans (pow_le_one₀ (norm_nonneg _) hc.le)
  · rw [dist_eq_norm, h, add_sub_cancel_left]
    exact hb.trans_lt hN

end GlobalTheory.Cyc.Decomp.Coord
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
noncomputable section

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def actM (g : GQ l) : P.R.BdR →* P.R.BdR := (P.actQdR g).toRingEquiv.toRingHom.toMonoidHom

theorem actM_apply (g : GQ l) (b : P.R.BdR) : actM P g b = P.actQdR g b := rfl

variable {P}

theorem unit_zpow_mem {u : P.R.BdRˣ} (h0 : (u : P.R.BdR) ∈ Fil P 0)
    (h1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) (k : ℤ) : ((u ^ k : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one]; exact one_mem_Fil
  | succ k ih => rw [zpow_add_one, Units.val_mul]; exact Fil_mul_left ih h0
  | pred k ih => rw [zpow_sub_one, Units.val_mul]; exact Fil_mul_left ih h1

theorem unitM_scal {n : Type} [Fintype n] [DecidableEq n] {U : GL n P.R.BdR} (hU : UnitM P U) {v : P.R.BdRˣ}
    (h0 : (v : P.R.BdR) ∈ Fil P 0) (h1 : ((v⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) :
    UnitM P (scalGL n v * U) := by
  constructor
  · intro i j
    rw [scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h0 (hU.1 i j)
  · intro i j
    rw [mul_inv_rev, ← map_inv, ← (scalGL_commute n v⁻¹ U⁻¹).eq, scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h1 (hU.2 i j)

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frame_scal {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (m : ℕ) (v : n → ℤ) (d : ℤ)
    (U : GL n P.R.BdR) (hU : ∀ g : ↥(GK K), matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]))
    (u : P.R.BdRˣ) (hu : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (u : P.R.BdR) =
      kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-d) : ℚ_[l]ˣ) : ℚ_[l]) * u)
    (g : ↥(GK K')) :
    matD P (twist hK ρ χ a) m g *
        ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l]) := by
  set F : P.R.BdRˣ := Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g)) with hFdef
  set Q : P.R.BdRˣ := Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l)) with hQdef
  have hF : ∀ k : ℤ, ((F ^ k : P.R.BdRˣ) : P.R.BdR) = kd P (fr l m ((χ g ^ k : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l))) := by
    intro k
    have : F ^ k = Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g ^ k)) := by
      simp only [hFdef, map_zpow]
    rw [this]; rfl
  have hQ : ∀ k : ℤ, ((Q ^ k : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ k : ℚ_[l]ˣ) : ℚ_[l]) := by
    intro k
    have : Q ^ k = Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l) ^ k) := by
      simp only [hQdef, map_zpow]
    rw [this]; rfl
  have hu' : Units.map (actM P (g : GQ l)) u = F * Q ^ (-d) * u := by
    apply Units.ext
    rw [Units.coe_map, actM_apply, hu g, Units.val_mul, Units.val_mul, hQ]
    have := hF 1
    rw [zpow_one, zpow_one] at this
    rw [this]
  have hs : P.actQdR (g : GQ l) ((u ^ (-a) : P.R.BdRˣ) : P.R.BdR) = (((F * Q ^ (-d) * u) ^ (-a) : P.R.BdRˣ) : P.R.BdR) := by
    rw [← hu', ← map_zpow, Units.coe_map, actM_apply]
  have hmat : matD P (twist hK ρ χ a) m g =
      ((F ^ a : P.R.BdRˣ) : P.R.BdR) • matD P ρ m ⟨g, GK_le hK g.2⟩ := by
    ext i j
    simp only [matD, twist_val, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hF]
  have hmap : ∀ (s : P.R.BdR) (M : Matrix n n P.R.BdR),
      (s • M).map (P.actQdR (g : GQ l)) = P.actQdR (g : GQ l) s • M.map (P.actQdR (g : GQ l)) := by
    intro s M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hdiag : (Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l])) =
      ((Q ^ (d * a) : P.R.BdRˣ) : P.R.BdR) • Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]) := by
    rw [hQ, ← Matrix.diagonal_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, zpow_add, Units.val_mul, map_mul]
    exact mul_comm _ _
  rw [hmat, scalGL_mul_val, hmap, hs, hdiag, smul_mul_smul_comm, smul_mul_smul_comm]
  have hUg := hU ⟨g, GK_le hK g.2⟩
  rw [hUg, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [mul_zpow, mul_zpow, ← zpow_mul, neg_mul_neg, ← mul_assoc, ← mul_assoc, ← zpow_add, add_neg_cancel,
    zpow_zero, one_mul, mul_comm]

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist



theorem framed_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type)
    [Fintype n] [DecidableEq n] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r N : ℕ) (hr : 0 < r)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ),
    IsRat r ρ → Framed P ρ w →
    (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) →
    P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < r * N → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) →
    Framed P (GlobalTheory.PMon.Twist.twist hK ρ χ a)
      (fun (m : Fin (r * N)) j => w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then a else 0) := by
  intro l _ P AI T n _ _ K K' hK r N hr ρ w χ x a hρ hf hx hx1 hx2 hev m
  obtain ⟨-, -, hshift, hunit, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have hgal : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (ev P m x) = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * ev P m x := by
    intro g
    rw [← ev_act, hx g, ← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  obtain ⟨e, he0, he1, hegal⟩ : ∃ e : P.R.BdR, e ∈ Fil P 0 ∧ e ∉ Fil P 1 ∧ ∀ g : ↥(GK K'),
      P.actQdR (g : GQ l) e = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) *
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-(if (m : ℕ) = 0 then 1 else 0 : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * e := by
    by_cases hm : (m : ℕ) = 0
    · have e0 : ev P (m : ℕ) x = P.ιB x := by rw [hm]; rfl
      refine ⟨tz P (-1) * ev P m x, ?_, ?_, fun g => ?_⟩
      · have h := (hshift 1 (-1) (P.ιB x)).1 hx1
        rw [show (1 : ℤ) + -1 = 0 by norm_num] at h
        rwa [e0]
      · intro h
        rw [e0] at h
        apply hx2
        refine (hshift 2 (-1) (P.ιB x)).2 ?_
        rwa [show (2 : ℤ) + -1 = 1 by norm_num]
      · rw [if_pos hm, map_mul, GlobalTheory.PMon.Model.act_tz, hgal g]
        ring
    · have hj := hev m (Nat.pos_of_ne_zero hm) m.2
      refine ⟨ev P m x, hj.1, hj.2, fun g => ?_⟩
      rw [if_neg hm, hgal g, neg_zero, zpow_zero, Units.val_one, map_one, mul_one]
  obtain ⟨y, hy0, hey⟩ := hunit e he0 he1
  let u : P.R.BdRˣ := ⟨e, y, hey, by rw [mul_comm]; exact hey⟩
  have hu0 : (u : P.R.BdR) ∈ Fil P 0 := he0
  have hu1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := hy0
  obtain ⟨U, hUm, hU⟩ := hf ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩
  have hper : ∀ g, matD P ρ m g = matD P ρ ((m : ℕ) % r) g := fun g => by
    ext i j
    simp only [matD, Matrix.map_apply]
    rw [fr_mod (hρ.rat g i j)]
  refine ⟨scalGL n (u ^ (-a)) * U, unitM_scal hUm (unit_zpow_mem hu0 hu1 _)
    (by rw [← zpow_neg]; exact unit_zpow_mem hu0 hu1 _), fun g => ?_⟩
  have key := frame_scal hK ρ χ a m (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩) (if (m : ℕ) = 0 then 1 else 0) U
    (fun g' => by rw [hper]; exact hU g') u hegal g
  have hda : (if (m : ℕ) = 0 then (1 : ℤ) else 0) * a = if (m : ℕ) = 0 then a else 0 := by
    split_ifs <;> simp
  simp only [hda] at key
  exact key

end GlobalTheory.PMon.Twist
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinLocalInj

theorem artin_localIdele_injective : ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ w : HeightOneSpectrum (𝓞 E), Function.Injective fun x : (w.adicCompletion E)ˣ => art (Neutral.B1.localIdele E w x) := by
  intro hC E Ω _ _ _ _ _ art ha w
  have hker : ∀ x : (w.adicCompletion E)ˣ, art (Neutral.B1.localIdele E w x) = 1 → x = 1 := by
    intro x hx
    have hx' : art (Neutral.B1.localIdele E w x⁻¹) = 1 := by rw [map_inv, map_inv, hx, inv_one]
    have hv : Valued.v (x : w.adicCompletion E) = 1 := by
      rcases le_total (Valued.v (x : w.adicCompletion E)) 1 with h | h
      · exact GlobalTheory.T.valuation_eq_one_of_congruent_global_approx E w x x.ne_zero h (GlobalTheory.T.exists_global_approx_of_artin_trivial E Ω art ha w x hx)
      · have h2 : Valued.v ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀]
          exact inv_le_one_of_one_le₀ h
        have h3 := GlobalTheory.T.valuation_eq_one_of_congruent_global_approx E w _ (x⁻¹).ne_zero h2 (GlobalTheory.T.exists_global_approx_of_artin_trivial E Ω art ha w x⁻¹ hx')
        rw [Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one] at h3
        exact h3
    exact Units.ext (GlobalTheory.T.eq_one_of_approx_by_congruent_global_units hC E w x hv (GlobalTheory.T.exists_global_approx_of_artin_trivial E Ω art ha w x hx))
  intro x y hxy
  have : art (Neutral.B1.localIdele E w (x * y⁻¹)) = 1 := by
    simp only at hxy
    rw [map_mul, map_mul, map_inv, map_inv, hxy, mul_inv_cancel]
  exact mul_inv_eq_one.mp (hker _ this)

end GlobalTheory.ArtinLocalInj
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.DegreeOne

theorem classOfDegreeOne_eq_ofChar : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), x.1 = 1 →
    ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), x = IrrGL.ofChar χ hχ := by
  intro _ k _ _ _ _ _ x hx
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.LocLanglands.DegreeOne
end
