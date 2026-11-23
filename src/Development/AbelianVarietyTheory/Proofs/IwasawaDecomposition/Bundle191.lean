module

import Development.WeilBound.ThetaLifts.Reductions.WeightConstants.Bridge
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualAtScaled
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingNonvanishingIffEventuallyNonzero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle185
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.FrobeniusOrbits.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.InfTypeLocal

theorem denseRange_atInf (L : Type) [Field L] [NumberField L] :
    DenseRange (fun (k : Lˣ) (w : InfinitePlace L) => atInf w k) := by
  apply PositivityTheory.ThKRed.HK.dense_atInf <;> assumption

theorem continuous_infIdele (L : Type) [Field L] [NumberField L] (w : InfinitePlace L) :
    Continuous (infIdele L w) := by
  classical
  refine Continuous.units_map _ ?_
  exact Continuous.prodMk (continuous_mulSingle w) continuous_const

theorem exists_ext {L : Type} [Field L] (φ : L →+* ℂ) :
    ∃ e : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous e ∧
      ∀ k : L, e (algebraMap L _ k) = φ k := by
  have h0 : ∀ k : L, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ) (algebraMap L _ k) =
      (InfinitePlace.mk φ).embedding k := fun k => by
    rw [InfinitePlace.Completion.algebraMap_apply]
    simpa using InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ k)
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨_, hc, fun k => by rw [h0, h]⟩
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp hc, fun k => ?_⟩
    rw [RingHom.comp_apply, h0, h]
    simp


open Classical in
theorem infType_iff_local : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ n : I → ℤ, ((∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ↔ ∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) := by
  intro L _ _ I _ φ hφ ψ hψ n
  have hd : ∀ k : Lˣ, ((ψ (infDiag k) : ℂˣ) : ℂ) = ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) := by
    intro k
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]
    rfl
  constructor
  · intro h
    choose e hec he using fun i => exists_ext (φ i)
    have key : (fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => ∏ w, ((ψ (infIdele L w (u w)) : ℂˣ) : ℂ)) =
        fun u => ∏ i, (e i (u (InfinitePlace.mk (φ i))) / ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ)) ^ n i := by
      refine (denseRange_atInf L).equalizer ?_ ?_ ?_
      · refine continuous_finsetProd _ fun w _ => ?_
        exact Units.continuous_val.comp (hψ.comp ((continuous_infIdele L w).comp (continuous_apply w)))
      · refine continuous_finsetProd _ fun i _ => ?_
        have h1 : Continuous fun u : ∀ w : InfinitePlace L, (w.Completion)ˣ => e i (u (InfinitePlace.mk (φ i))) :=
          (hec i).comp (Units.continuous_val.comp (continuous_apply _))
        have h2 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, e i (u (InfinitePlace.mk (φ i))) ≠ 0 := fun u =>
          (map_ne_zero _).2 (Units.ne_zero (u (InfinitePlace.mk (φ i))))
        have h3 : ∀ u : ∀ w : InfinitePlace L, (w.Completion)ˣ, ((‖e i (u (InfinitePlace.mk (φ i)))‖ : ℝ) : ℂ) ≠ 0 := fun u => by
          exact_mod_cast norm_ne_zero_iff.2 (h2 u)
        exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _ fun u => Or.inl (div_ne_zero (h2 u) (h3 u))
      · funext k
        show ∏ w, ((ψ (infIdele L w (atInf w k)) : ℂˣ) : ℂ) =
          ∏ i, (e i (algebraMap L _ (k : L)) / ((‖e i (algebraMap L _ (k : L))‖ : ℝ) : ℂ)) ^ n i
        rw [← hd, h]
        simp only [he]
    intro i k
    have h1 := congrFun key (Pi.mulSingle (InfinitePlace.mk (φ i)) (atInf _ k))
    beta_reduce at h1
    rw [Finset.prod_eq_single (InfinitePlace.mk (φ i)), Finset.prod_eq_single i] at h1
    · rw [Pi.mulSingle_eq_same] at h1
      rw [h1, ← he i k]
      rfl
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne (fun hh => hj (hφ.1 hh))]
      simp
    · simp
    · intro w _ hw
      rw [Pi.mulSingle_eq_of_ne hw]
      simp
    · simp
  · intro h k
    rw [hd, ← hφ.prod_comp]
    exact Finset.prod_congr rfl fun i _ => h i k

end GlobalTheory.InfTypeLocal
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (b : Per.Bcris l), Per.φB l b = b → C.ι b ∈ Per.FilD l 0 → ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = b := by
  first | exact @GlobalTheory.MemLoc.fundamental_exact | exact GlobalTheory.MemLoc.fundamental_exact | (intros; apply GlobalTheory.MemLoc.fundamental_exact <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsRationalUnitaryDeterminantMap H (e1T H) ∧ (letI := H.cmStar; ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k) := by
  first | exact @GlobalTheory.Mem.RatPts.rat_points | exact GlobalTheory.Mem.RatPts.rat_points | (intros; apply GlobalTheory.Mem.RatPts.rat_points <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscPairDer

open MvPolynomial

variable {P Q : ℕ}

def derForm (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ) (T : MvPolynomial (Ix P Q) ℂ → ℂ)
    (f : MvPolynomial (Ix P Q) ℂ) : ℂ :=
  ∑ i, ∑ j, A' i j * T (pderiv (Sum.inl i) (pderiv (Sum.inr j) f)) + ∑ l, x' l * T (pderiv l f)

theorem derForm_comb {κ : Type} [Fintype κ] (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T U : MvPolynomial (Ix P Q) ℂ → ℂ) (a : ℂ) (b : κ → ℂ) (e : κ → Ix P Q)
    (hU : ∀ g, U g = a * T g + ∑ k, b k * T (pderiv (e k) g)) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' U f = a * derForm A' x' T f + ∑ k, b k * derForm A' x' T (pderiv (e k) f) := by
  simp only [derForm, hU, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : ∑ i, ∑ j, ∑ k, A' i j * (b k * T (pderiv (e k) (pderiv (Sum.inl i) (pderiv (Sum.inr j) f)))) =
      ∑ k, ∑ i, ∑ j, b k * (A' i j * T (pderiv (Sum.inl i) (pderiv (Sum.inr j) (pderiv (e k) f)))) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset κ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), mul_left_comm]
  have h2 : ∑ l, ∑ k, x' l * (b k * T (pderiv (e k) (pderiv l f))) =
      ∑ k, ∑ l, b k * (x' l * T (pderiv l (pderiv (e k) f))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Oscillator.pderiv_pderiv_comm (e k), mul_left_comm]
  rw [h1, h2]
  simp only [mul_left_comm a]
  ring

theorem pderiv_X_mul (m l : Ix P Q) (f : MvPolynomial (Ix P Q) ℂ) :
    pderiv m (X l * f) = X l * pderiv m f + if m = l then f else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
  by_cases h : m = l
  · simp [h]
  · simp [h, Ne.symm h]

theorem derForm_X_inl (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : MvPolynomial (Ix P Q) ℂ →+ ℂ) (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' T (X (Sum.inl i) * f) = derForm A' x' (fun g => T (X (Sum.inl i) * g)) f +
      (x' (Sum.inl i) * T f + ∑ j, A' i j * T (pderiv (Sum.inr j) f)) := by
  simp only [derForm, pderiv_X_mul, map_add (f := _), apply_ite T, map_zero, mul_add, Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, reduceCtorEq, if_false, add_zero, Sum.inl.injEq]
  rw [Finset.sum_comm (f := fun i' j => if i' = i then A' i' j * T (pderiv (Sum.inr j) f) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem derForm_X_inr (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : MvPolynomial (Ix P Q) ℂ →+ ℂ) (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ) :
    derForm A' x' T (X (Sum.inr j) * f) = derForm A' x' (fun g => T (X (Sum.inr j) * g)) f +
      (x' (Sum.inr j) * T f + ∑ i, A' i j * T (pderiv (Sum.inl i) f)) := by
  simp only [derForm, pderiv_X_mul, map_add (f := _), apply_ite T, apply_ite (pderiv _), map_zero, mul_add,
    Finset.sum_add_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, reduceCtorEq, if_false, add_zero, Sum.inr.injEq]
  ring

def pair (F : Fock (Ix P Q)) (v : F.H) : MvPolynomial (Ix P Q) ℂ →+ ℂ where
  toFun f := inner ℂ (F.ι f) v
  map_zero' := by simp
  map_add' f g := by simp [inner_add_left]

theorem step {κ : Type} [Fintype κ] (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ)
    (T : ℝ → MvPolynomial (Ix P Q) ℂ → ℂ) (l : Ix P Q) (a : ℝ → ℂ) (b : ℝ → κ → ℂ) (a' : ℂ) (b' : κ → ℂ)
    (e : κ → Ix P Q) (ha : HasDerivAt a a' 0) (hb : ∀ k, HasDerivAt (fun t => b t k) (b' k) 0)
    (hU : ∀ t g, T t (X l * g) = a t * T t g + ∑ k, b t k * T t (pderiv (e k) g)) (f : MvPolynomial (Ix P Q) ℂ)
    (h0 : HasDerivAt (fun t => T t f) (derForm A' x' (T 0) f) 0)
    (h1 : ∀ m, HasDerivAt (fun t => T t (pderiv m f)) (derForm A' x' (T 0) (pderiv m f)) 0) :
    HasDerivAt (fun t => T t (X l * f)) (derForm A' x' (fun g => T 0 (X l * g)) f +
      (a' * T 0 f + ∑ k, b' k * T 0 (pderiv (e k) f))) 0 := by
  rw [derForm_comb A' x' (T 0) _ (a 0) (b 0) e (hU 0)]
  simp only [hU]
  refine ((ha.fun_mul h0).fun_add (HasDerivAt.fun_sum (u := Finset.univ)
    fun k _ => (hb k).fun_mul (h1 (e k)))).congr_deriv ?_
  rw [Finset.sum_add_distrib]
  ring

theorem hasDerivAt_inner_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : ℝ → Matrix (Fin P) (Fin Q) ℂ) (x : ℝ → Ix P Q → ℂ) (v : ℝ → F.H) (A' : Matrix (Fin P) (Fin Q) ℂ) (x' : Ix P Q → ℂ), (∀ t, HasCoeff F (v t) (expPS (gaussPoly (A t) (x t)))) → (∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) → (∀ l, HasDerivAt (fun t => x t l) (x' l) 0) → ∀ f : MvPolynomial (Ix P Q) ℂ, HasDerivAt (fun t => inner ℂ (F.ι f) (v t)) (∑ i, ∑ j, A' i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) (v 0) + ∑ l, x' l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) (v 0)) 0 := by
  intro P Q F A x v A' x' hv hA hx f
  change HasDerivAt (fun t => pair F (v t) f) (derForm A' x' (pair F (v 0)) f) 0
  have key : ∀ (N : ℕ) (α : Ix P Q →₀ ℕ), α.degree ≤ N → ∀ c : ℂ,
      HasDerivAt (fun t => pair F (v t) (monomial α c)) (derForm A' x' (pair F (v 0)) (monomial α c)) 0 := by
    have h0 : ∀ c : ℂ, HasDerivAt (fun t => pair F (v t) (monomial 0 c))
        (derForm A' x' (pair F (v 0)) (monomial 0 c)) 0 := fun c => by
      have e : ∀ t, pair F (v t) (monomial 0 c) = (starRingEnd ℂ) c := fun t => by
        have e1 : (monomial 0 c : MvPolynomial (Ix P Q) ℂ) = c • monomial 0 1 := by
          rw [smul_monomial, smul_eq_mul, mul_one]
        change inner ℂ (F.ι (monomial 0 c)) (v t) = _
        rw [e1, map_smul, inner_smul_left, hv t 0]
        simp [expPS, MvPowerSeries.coeff_apply]
      simp only [e]
      refine (hasDerivAt_const _ _).congr_deriv ?_
      simp [derForm]
    intro N
    induction N with
    | zero =>
      intro α hα c
      obtain rfl : α = 0 := (Finsupp.degree_eq_zero_iff α).1 (Nat.le_zero.1 hα)
      exact h0 c
    | succ N ih =>
      intro α hα c
      by_cases hz : α = 0
      · subst hz; exact h0 c
      obtain ⟨l, hl⟩ : ∃ l, α l ≠ 0 := by
        by_contra hh
        push Not at hh
        exact hz (Finsupp.ext hh)
      obtain ⟨β, rfl⟩ : ∃ β, α = Finsupp.single l 1 + β :=
        exists_add_of_le (Finsupp.single_le_iff.2 (Nat.pos_of_ne_zero hl))
      have hβ : β.degree ≤ N := by
        rw [map_add (f := _), Finsupp.degree_single] at hα
        omega
      have e : (monomial (Finsupp.single l 1 + β) c : MvPolynomial (Ix P Q) ℂ) = X l * monomial β c := by
        rw [X, monomial_mul, one_mul]
      have h1 : ∀ m, HasDerivAt (fun t => pair F (v t) (pderiv m (monomial β c)))
          (derForm A' x' (pair F (v 0)) (pderiv m (monomial β c))) 0 := fun m => by
        rw [pderiv_monomial]
        exact ih _ ((Finsupp.degree_mono tsub_le_self).trans hβ) _
      rw [e]
      rcases l with i | j
      · rw [derForm_X_inl]
        exact step A' x' (fun t => pair F (v t)) _ (fun t => x t (Sum.inl i)) (fun t j => A t i j) _ _ Sum.inr
          (hx _) (hA i) (fun t => (GlobalTheory.T.gaussianVector_annihilator_equations P Q F _ _ _ (hv t)).1 i) _ (ih _ hβ c) h1
      · rw [derForm_X_inr]
        exact step A' x' (fun t => pair F (v t)) _ (fun t => x t (Sum.inr j)) (fun t i => A t i j) _ _ Sum.inl
          (hx _) (fun i => hA i j) (fun t => (GlobalTheory.T.gaussianVector_annihilator_equations P Q F _ _ _ (hv t)).2 j) _ (ih _ hβ c) h1
  induction f using MvPolynomial.induction_on' with
  | monomial α c => exact key _ α le_rfl c
  | add f g hf hg =>
    simp only [map_add (f := _)]
    refine (hf.fun_add hg).congr_deriv ?_
    simp only [derForm, map_add (f := _), mul_add, Finset.sum_add_distrib]
    ring

end GlobalTheory.OscPairDer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.inner_gaussianVectors_fockSpace : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A B : Matrix (Fin P) (Fin Q) ℂ) (x y : Ix P Q → ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → ∀ v w : F.H, HasCoeff F v (expPS (gaussPoly A x)) → HasCoeff F w (expPS (gaussPoly B y)) → let a : Fin P → ℂ := fun i => star (x (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (x (Sum.inr j)); let c : Fin P → ℂ := fun i => y (Sum.inl i); let d : Fin Q → ℂ := fun j => y (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; inner ℂ v w = ((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c) := by
  first | exact @GlobalTheory.GaussInner.inner_gauss_gauss | exact GlobalTheory.GaussInner.inner_gauss_gauss | (intros; apply GlobalTheory.GaussInner.inner_gauss_gauss <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.tDat_laws_of_ok : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → A.Laws T := by
  first | exact @GlobalTheory.Mem.Col2.TDat.laws_of_ok | exact GlobalTheory.Mem.Col2.TDat.laws_of_ok | (intros; apply GlobalTheory.Mem.Col2.TDat.laws_of_ok <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LevelClosure

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter Topology

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open Classical in
def cutIdem (T : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun v => if v ∈ T then 1 else 0, Eventually.of_forall fun v => by
    by_cases h : v ∈ T
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem evalV_cutIdem_of_mem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 1 := by
  classical
  exact if_pos h

theorem evalV_cutIdem_of_notMem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 0 := by
  classical
  exact if_neg h

theorem tendsto_cutIdem_mul (a : Af F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutIdem T * a) atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ principal S := by
    rw [le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T =>
    ⟨fun v => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v, by
      rw [eventually_principal]
      intro w hw
      by_cases h : w ∈ T
      · simp only [evalV_cutIdem_of_mem h, one_mul]; exact hw
      · simp only [evalV_cutIdem_of_notMem h, zero_mul]; exact zero_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [eventually_principal]; exact fun w hw => hw⟩
  have hf : Tendsto f atTop (𝓝 a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v
    rw [evalV_cutIdem_of_mem this, one_mul]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem tendsto_cutIdem_smul (z : Af F ⊗[F] E) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => (cutIdem T : Af F) • z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  induction z using TensorProduct.induction_on with
  | zero => simpa using tendsto_const_nhds
  | add x y hx hy => simpa only [smul_add] using hx.add hy
  | tmul a x =>
    have h := (tendsto_cutIdem_mul a).smul_const ((1 : Af F) ⊗ₜ[F] x)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def cutPt (T : Finset (HeightOneSpectrum (𝓞 F))) : GAd σ J →* GAd σ J := (embAt σ J T).comp (projAt σ J T)

omit [NumberField E] in
theorem map_smul_cut (v : HeightOneSpectrum (𝓞 F)) (c : Af F) (z : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (c • z) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c • Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul a x => simp [TensorProduct.smul_tmul']

omit [NumberField E] in
theorem cutPt_entry (T : Finset (HeightOneSpectrum (𝓞 F))) (g : GAd σ J) (i j : Fin n) :
    (matHom _ σ J (projFin σ J (cutPt σ J T g))).1 i j =
      (cutIdem T : Af F) • ((matHom _ σ J (projFin σ J g)).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) +
        (1 : Matrix (Fin n) (Fin n) _) i j := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => ?_
  have e : ∀ g : GAd σ J, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((matHom _ σ J (projFin σ J g)).1 i j) = (matHom _ σ J (proj σ J v g)).1 i j := fun g => by
    rw [← projFinLoc_projFin]; rfl
  have e1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _ =
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _
  rw [map_add (f := _), map_smul_cut, map_sub, e, e, e1]
  by_cases hv : v ∈ T
  · have : proj σ J v (cutPt σ J T g) = proj σ J v g := proj_embAt σ J T _ ⟨v, hv⟩
    rw [this, evalV_cutIdem_of_mem hv, one_smul, sub_add_cancel]
  · have : proj σ J v (cutPt σ J T g) = 1 := (mem_atPts.1 (embAt_mem σ J T _)).2 v hv
    rw [this, evalV_cutIdem_of_notMem hv, zero_smul, zero_add, map_one, Units.val_one]

theorem tendsto_projFin_cutPt (g : GAd σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => projFin σ J (cutPt σ J T g)) atTop (𝓝 (projFin σ J g)) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  have h : ∀ g : GAd σ J, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (matHom _ σ J (projFin σ J (cutPt σ J T g))).1) atTop (𝓝 (matHom _ σ J (projFin σ J g)).1) := fun g => by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [cutPt_entry]
    have := (tendsto_cutIdem_smul ((matHom _ σ J (projFin σ J g)).1 i j -
      (1 : Matrix (Fin n) (Fin n) _) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
    rwa [sub_add_cancel] at this
  rw [(isEmbedding_matHom _ σ J).tendsto_nhds_iff, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h g).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h g⁻¹
  simp only [map_inv] at h2
  exact h2

theorem tendsto_cutPt {g : GAd σ J} (hg : g ∈ finPts σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutPt σ J T g) atTop (𝓝 g) := by
  have e : ∀ g ∈ finPts σ J, ofFin σ J (projFin σ J g) = g := fun g hg =>
    ext_inf_fin σ J (by simp [mem_finPts.1 hg]) (by simp)
  have h := ((continuous_ofFin σ J).tendsto _).comp (tendsto_projFin_cutPt σ J g)
  rw [e g hg] at h
  exact h.congr fun T => e _ (mem_atPts.1 (embAt_mem σ J T _)).1

theorem mem_of_isClosed {H : Subgroup (GAd σ J)} (hH : IsClosed (H : Set (GAd σ J))) {g : GAd σ J}
    (hg : g ∈ finPts σ J) (h : ∀ v, emb σ J v (proj σ J v g) ∈ H) : g ∈ H :=
  hH.mem_of_tendsto (tendsto_cutPt σ J hg) (Eventually.of_forall fun T =>
    Subgroup.noncommProd_mem H (f := fun v : T => emb σ J v (proj σ J v g))
      (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => h v)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ksph_le_of_isClosed : ∀ (D : D7) (V : HSp D) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (H : Subgroup (GA D V)), IsClosed (H : Set (GA D V)) → (∀ v, v ∉ Z → ∀ ε, IsPlaceIdem D v ε → ∀ g ∈ KsphC V ∅, SuppPl ε V g → g ∈ H) → ∀ k ∈ KsphC V Z, k ∈ H := by
  intro D V Z H hH h k hk
  rw [KsphC_eq] at hk
  obtain ⟨h1, h2, h3⟩ := mem_levelOff.1 hk
  refine mem_of_isClosed D.sp.cm.sig V.gram hH h1 fun v => ?_
  by_cases hv : v ∈ Z
  · rw [h2 v hv, map_one]; exact one_mem _
  · have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleFin v 1)) :=
      ⟨_, rfl, evalV_singleFin_self v 1, fun _ hu => evalV_singleFin_ne hu 1⟩
    exact h v hv _ hε _ ((Model.emb_mem_KsphC_iff V v _).2 (h3 v hv)) ((Model.suppF_iff V hε _).2 ⟨_, rfl⟩)

end GlobalTheory.LevelClosure

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.hasLatticeNormalForm_of_between : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ (h ρ : AutY X R j) (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → Between j P h → (ρ * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z → GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P (ρ * h) := by
  first | exact @GlobalTheory.Proof.hasLatticeNormalForm_of_between.nf_of_between | exact GlobalTheory.Proof.hasLatticeNormalForm_of_between.nf_of_between | (intros; apply GlobalTheory.Proof.hasLatticeNormalForm_of_between.nf_of_between <;> assumption)
end
