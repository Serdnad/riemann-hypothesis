module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftSumDifferentialCompat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle226
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle224
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle228
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem exists_monic_eval₂_of_span {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (S : Subring B)
    (T : Finset B) (hW : ∀ a, f a ∈ S) (hT : ∀ t ∈ T, t ∈ S)
    (hS : ∀ s ∈ S, ∃ a : B → A, s = ∑ t ∈ T, t * f (a t)) (e : B) (he : e ∈ S) :
    ∃ P : Polynomial A, P.Monic ∧ P.eval₂ f e = 0 := by
  letI : Algebra A B := f.toAlgebra
  let C : Subalgebra A B := { S with algebraMap_mem' := hW }
  have hfg : (Subalgebra.toSubmodule C).FG := by
    refine ⟨T, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 fun t ht => hT t ht
    · intro s hs
      obtain ⟨a, rfl⟩ := hS s hs
      refine Submodule.sum_mem _ fun t ht => ?_
      have : t * f (a t) = a t • t := by
        rw [Algebra.smul_def, mul_comm]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ht)
  exact IsIntegral.of_mem_of_fg C hfg e he

theorem pow_natDegree_eq_zero_of_eval₂ {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    (f : A →+* B) (hf : Function.Injective f) (c : A →+* R) (P : Polynomial A) (hP : P.Monic)
    (e : B) (he : P.eval₂ f e = 0) (n v : A) (hn : c n = 0) (hv : f n * e = f v) :
    c v ^ P.natDegree = 0 := by
  have h1 : (P.scaleRoots n).eval₂ f (f v) = 0 := by
    rw [← hv, Polynomial.scaleRoots_eval₂_mul, he, mul_zero]
  have h2 : (P.scaleRoots n).eval v = 0 := by
    apply hf
    rw [← Polynomial.eval₂_at_apply, h1, map_zero]
  have h3 : (P.scaleRoots n).eval₂ c (c v) = 0 := by
    rw [Polynomial.eval₂_at_apply, h2, map_zero]
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.natDegree_scaleRoots,
    Finset.sum_eq_single P.natDegree] at h3
  · rw [Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_natDegree,
      hP.leadingCoeff, map_one, one_mul] at h3
    exact h3
  · intro i hi hne
    have hlt : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hne
    rw [Polynomial.coeff_scaleRoots, map_mul, map_pow, hn, zero_pow (Nat.sub_ne_zero_of_lt hlt)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

theorem tch_ne_mul_of_pow_eq {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (T : Finset (Formalism.Per6.BdRp l)) :
    (∀ a, wB l a ∈ S) → (∀ t ∈ T, t ∈ S) →
    (∀ s ∈ S, ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t)) →
    ∀ (ϖ y : Formalism.Per6.BdRp l) (N : ℕ), y ∈ S → ϖ ^ N = (l : Formalism.Per6.BdRp l) * y →
    ∀ u : Tl l, u ≠ 0 → ∀ s ∈ S, tch l u ≠ ϖ * s := by
  intro hW hT hS ϖ y N hy hN u hu s hs h
  haveI := GroundTheory.PAdicHodge.IsPerfectoidField.isDomain_preTilt (K := ℂ_[l]) l
  obtain ⟨P, hP, hev⟩ := exists_monic_eval₂_of_span (wB l) S T hW hT hS (y * s ^ N)
    (S.mul_mem hy (S.pow_mem hs N))
  have hinj : Function.Injective (wB l) := PositivityTheory.LocInh.wittTo_injective
  have hv : wB l (l : Wl l) * (y * s ^ N) = wB l (WittVector.teichmuller l (u ^ N)) := by
    have h1 : wB l (WittVector.teichmuller l (u ^ N)) = tch l u ^ N := by
      rw [map_pow, map_pow]; rfl
    rw [h1, h, mul_pow, hN, map_natCast, mul_assoc]
  have hc : (WittVector.constantCoeff : Wl l →+* Tl l) (l : Wl l) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero _ _
  have h0 := pow_natDegree_eq_zero_of_eval₂ (wB l) hinj WittVector.constantCoeff P hP _ hev
    (l : Wl l) _ hc hv
  have h2 : (WittVector.constantCoeff : Wl l →+* Tl l) (WittVector.teichmuller l (u ^ N)) = u ^ N :=
    WittVector.teichmuller_coeff_zero l _
  rw [h2] at h0
  exact hu (eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero h0))

end GlobalTheory.CompanionTheory.LTPer
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.mvE_empty_of_mvE_nonempty : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (k : I → ℕ) (ς : I → ℤˣ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι) (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n), (∀ (u : I) (S : Finset ι) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : ((A u).K S).X m), (T.K S).d n (g u S h x) = (ς u : ℤ) • g u S h' (((A u).K S).d m x)) → (∀ (u : I) {S S' : Finset ι} (hS : S ⊆ S') {m n : ℕ} (h : m + k u = n) (x : ((A u).K S).X m), (T.res hS).f n (g u S h x) = g u S' h (((A u).res hS).f m x)) → (∀ u, (A u).Desc) → T.Desc → (∀ S : Finset ι, S.Nonempty → ∀ n, MvE k A T g S n) → ∀ n, MvE k A T g ∅ n := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.MvSum.mvSum | exact GlobalTheory.CompanionTheory.KunGlue.MvSum.mvSum | (intros; apply GlobalTheory.CompanionTheory.KunGlue.MvSum.mvSum <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ValPhi

open PowerSeries

section
variable {A : Type} [Ring A] (N : A) (τ : ℕ → A)

theorem bco_of_lt : ∀ (m j : ℕ), m < j → bco N τ m j = 0 := by
  intro m
  induction m with
  | zero =>
    intro j h
    cases j with
    | zero => omega
    | succ j => simp [bco]
  | succ m ih =>
    intro j h
    cases j with
    | zero => omega
    | succ j => rw [bco, ih j (by omega), ih (j + 1) (by omega)]; simp

theorem bco_self (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => simp [bco]
  | succ m ih => rw [bco, ih, bco_of_lt N τ m (m + 1) (by omega)]; simp

theorem eq_phiSeq (p : ℕ → A) (h : ∀ m, ∑ j ∈ range (m + 1), bco N τ m j * p j = τ m) (m : ℕ) :
    p m = phiSeq N τ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have e : ∑ j ∈ range m, bco N τ m j * phiSeq N τ j = ∑ j ∈ range m, bco N τ m j * p j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.1 hj)]
    rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m, e, ← h m,
      sum_range_succ, bco_self, one_mul]
    abel
end

section
variable (N : ℂ) (τ : ℕ → ℂ)

noncomputable def bser (j : ℕ) : PowerSeries ℂ := PowerSeries.mk (fun m => bco N τ m j)

theorem coeff_bser (j m : ℕ) : coeff m (bser N τ j) = bco N τ m j := by simp [bser]

theorem constantCoeff_bser (j : ℕ) : constantCoeff (bser N τ j) = bco N τ 0 j := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bser]

theorem bser_zero : (1 - C N * X) * bser N τ 0 = 1 - X * PowerSeries.mk τ := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul, coeff_one]

theorem bser_succ (j : ℕ) : (1 - C N * X) * bser N τ (j + 1) = X * bser N τ j := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul]

theorem bser_eq {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1) (j : ℕ) :
    bser N τ j = (1 - X * PowerSeries.mk τ) * w ^ (j + 1) * X ^ j := by
  induction j with
  | zero =>
    have := bser_zero N τ
    rw [← this]
    linear_combination (-(bser N τ 0)) * hw
  | succ j ih =>
    have := bser_succ N τ j
    rw [ih] at this
    linear_combination (-(bser N τ (j + 1))) * hw + w * this

end

theorem mk_decomp (g : ℕ → ℂ) (m : ℕ) :
    PowerSeries.mk g = ∑ j ∈ range (m + 1), g j • (X : PowerSeries ℂ) ^ j
      + X ^ (m + 1) * PowerSeries.mk (fun i => g (i + (m + 1))) := by
  ext k

  simp only [map_add (f := _), map_sum, coeff_mk, coeff_X_pow_mul', LinearMap.map_smul, coeff_X_pow,
  smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : m + 1 ≤ k
  · rw [if_pos hk, Nat.sub_add_cancel hk, sum_ite_eq]
    simp [mem_range]
    omega
  · rw [if_neg hk, sum_ite_eq, if_pos (mem_range.2 (by omega))]
    simp

theorem sum_of_subst (N : ℂ) (τ g : ℕ → ℂ) {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1)
    (ha : HasSubst (-(X * w)))
    (h : (1 - X * PowerSeries.mk τ) * subst (-(X * w)) (1 - X * PowerSeries.mk g) = 1) (m : ℕ) :
    ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j) = τ m := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  set H := PowerSeries.mk (fun i => g (i + (m + 1))) with hH
  set Q := 1 - X * PowerSeries.mk τ with hQ
  have hG : θ (PowerSeries.mk g) = ∑ j ∈ range (m + 1), g j • (-(X * w)) ^ j
      + (-(X * w)) ^ (m + 1) * θ H := by
    conv_lhs => rw [mk_decomp g m]

    simp only [map_add (f := _), map_sum, map_smul, map_mul, map_pow, hX, hH]
  rw [hθ, map_sub, map_one, map_mul, hX, hG] at h
  have hterm : ∀ j, Q * (X * w) * (g j • (-(X * w)) ^ j)
      = (g j * (-1) ^ j) • (X * bser N τ j) := by
    intro j
    rw [bser_eq N τ hw j, neg_pow]
    simp only [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one]
    ring
  have hfin : Q + ∑ j ∈ range (m + 1), (g j * (-1) ^ j) • (X * bser N τ j)
      + X ^ (m + 2) * (Q * w * (-w) ^ (m + 1) * θ H) = 1 := by
    rw [← h, ← sum_congr rfl fun j _ => hterm j, ← mul_sum, neg_mul_eq_mul_neg X w, mul_pow]
    ring
  have hc := congrArg (coeff (m + 1)) hfin

  simp only [map_add (f := _), map_sum, LinearMap.map_smul, coeff_succ_X_mul, coeff_bser, coeff_X_pow_mul',
  smul_eq_mul, hQ, map_sub, coeff_mk, coeff_one] at hc
  simp at hc
  have e : ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j)
      = ∑ x ∈ range (m + 1), g x * (-1) ^ x * bco N τ m x :=
    sum_congr rfl fun j _ => by ring
  rw [e]
  linear_combination hc

theorem mul_subst_eq_one (n : ℕ) (cc : Fin n → ℂ) {w : PowerSeries ℂ}
    (hw : (1 - C (n : ℂ) * X) * w = 1) (ha : HasSubst (-(X * w))) :
    (1 - X * gser cc) * subst (-(X * w)) (1 - X * gser (fun a => - cc a)) = 1 := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  have hC : ∀ c : ℂ, θ (C c) = C c := fun c => θ.commutes c
  have e1 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2 + 1) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2) + C (cc i + ((n : ℂ) - 1) / 2 + 1) := by
      rw [← map_add (f := _)]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have e2 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2 + 1) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2 + 1) + C (cc i + ((n : ℂ) - 1) / 2) := by
      rw [← map_add (f := _)]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have h1 := GlobalTheory.T.gelfand_series_shift_identity n cc
  have h2 := congrArg θ (GlobalTheory.T.gelfand_series_shift_identity n (fun a => - cc a))
  simp only [map_mul, map_prod, map_sub, map_one, hC, hX, e1, e2, prod_mul_distrib, prod_const,
    card_univ, Fintype.card_fin] at h2
  set D := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2 + 1) * (X : PowerSeries ℂ)) with hD
  set E := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2) * (X : PowerSeries ℂ)) with hE
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hD0 : D ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i _ h0 => ?_
    have := congrArg constantCoeff h0
    simp at this
  rw [hθ, map_sub, map_one, map_mul, hX]
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero n hw0) hD0) ?_
  linear_combination (1 - X * gser cc) * h2 + w ^ n * h1

theorem gelfVal_neg_eq_phiSeq : ∀ (n : ℕ) (cc : Fin n → ℂ) (m : ℕ),
    (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc) m := by
  intro n cc m
  have hu : constantCoeff (1 - C (n : ℂ) * X : PowerSeries ℂ) ≠ 0 := by simp
  have hw := PowerSeries.mul_inv_cancel _ hu
  have ha : HasSubst (-(X * (1 - C (n : ℂ) * X : PowerSeries ℂ)⁻¹)) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  exact eq_phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc)
    (fun m => (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m)
    (sum_of_subst (n : ℂ) _ _ hw ha (mul_subst_eq_one n cc hw ha)) m

end GlobalTheory.CompanionTheory.WaveMult.ValPhi
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinVol

theorem volChar_one_eq {k : Type} [Field k] [NumberField k] :
    ∃ V : ℝ, 0 < V ∧ volChar (1 : HeckeCharacter k) = (V : ℂ) := by
  haveI := GroundTheory.Global.isHaarMeasure_normOneMeasure k
  haveI : Countable ↥(GroundTheory.Global.diagonalNormOne k).op := by
    haveI := GroundTheory.Global.countable_diagonalNormOne k
    refine Function.Injective.countable (f := fun x : ↥(GroundTheory.Global.diagonalNormOne k).op =>
      (⟨x.1.unop, Subgroup.mem_op.mp x.2⟩ : ↥(GroundTheory.Global.diagonalNormOne k))) ?_
    intro x y h
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact congrArg Subtype.val h
  have hfin : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) < ⊤ :=
    GroundTheory.Global.normOneMeasure_normOneFundamentalDomain_lt_top k
  have hne : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) ≠ 0 :=
    (GroundTheory.Global.isFundamentalDomain_normOneFundamentalDomain k
      (GroundTheory.Global.normOneMeasure k)).measure_ne_zero (NeZero.ne _)
  refine ⟨(GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k)).toReal,
    ENNReal.toReal_pos hne hfin.ne, ?_⟩
  have h2 : volChar (1 : HeckeCharacter k) =
      ∫ _u in GroundTheory.Global.normOneFundamentalDomain k, (1 : ℂ) ∂GroundTheory.Global.normOneMeasure k := by
    unfold volChar
    congr 1
  rw [h2, MeasureTheory.setIntegral_const]
  simp [Measure.real]

end GlobalTheory.CompanionTheory.EpsteinVol
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries

theorem thetaC_neg {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) :
    thetaC (fun x ↦ F (-x)) h = thetaC F h := by
  unfold thetaC
  rw [← (Equiv.neg (ι → k)).tsum_eq (fun ξ => F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))]
  refine tsum_congr fun ξ => ?_
  have hr : ratV (-ξ) = -ratV ξ := by
    funext i
    simp [ratV]
  simp only [Equiv.neg_apply, hr, Matrix.mulVec_neg]

theorem thetaCInt_neg : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k),
    thetaCInt w (fun x ↦ F (-x)) ω = thetaCInt w F ω := by
  intro k _ _ ι _ _ w F ω
  funext t
  unfold thetaCInt
  simp only [thetaC_neg]

end GlobalTheory.CompanionTheory.AdelicThetaSeries
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.He2M1

theorem thetaC_smul {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) :
    thetaC (c • F) h = c * thetaC F h := by
  unfold thetaC
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem thetaCInt_smul : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}), thetaCInt w (c • F) ω t = c * thetaCInt w F ω t := by
  intro k _ _ ι _ _ w c F ω t
  unfold thetaCInt
  simp only [thetaC_smul, mul_assoc]
  exact integral_const_mul c _

end GlobalTheory.CompanionTheory.He2M1
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.unramified_local_formula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.unrFormula | exact GlobalTheory.CompanionTheory.UnrDens.unrFormula | (intros; apply GlobalTheory.CompanionTheory.UnrDens.unrFormula <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.expansion_surjective_additive_linear : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.expand ∧ (∀ c c' : ℕ →₀ A.A, A.expand (c + c') = A.expand c + A.expand c') ∧ (∀ (a : A.A) (c : ℕ →₀ A.A), A.expand (a • c) = A.aTo1 a * A.expand c) ∧ ∀ k, A.aTo1 (A.pi ^ l) * A.dxi 1 k = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.Expand.main | exact GlobalTheory.CompanionTheory.PerfFil.Expand.main | (intros; apply GlobalTheory.CompanionTheory.PerfFil.Expand.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.prime_pow_annihilator_reduction : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n m : ℕ), Function.Surjective (A.red (Nat.le_add_right n m)) ∧ (∀ x : A.Acr (n + m), A.red (Nat.le_add_right n m) x = 0 ↔ x ∈ Ideal.span {(l : A.Acr (n + m)) ^ n}) ∧ (∀ x : A.Acr (n + m), (l : A.Acr (n + m)) ^ n * x = 0 ↔ A.red (Nat.le_add_left m n) x = 0) ∧ ∀ x : A.U, (l : A.U) ^ n * x ∈ Ideal.span {(l : A.U) ^ (n + m)} ↔ x ∈ Ideal.span {(l : A.U) ^ m} := by
  first | exact @GlobalTheory.CompanionTheory.PerfAlg.lseq | exact GlobalTheory.CompanionTheory.PerfAlg.lseq | (intros; apply GlobalTheory.CompanionTheory.PerfAlg.lseq <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.sharp_map_congruence_properties : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), (∀ (a b : A.A) (n : ℕ), a - b ∈ Ideal.span {A.pi} → A.sharp (a ^ l ^ n) - A.sharp (b ^ l ^ n) ∈ Ideal.span {(l : A.U) ^ (n + 1)}) ∧ (∀ a b : A.A, A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi}) ∧ ∀ e : A.A, IsIdempotentElem e → A.sharp (1 - e) = 1 - A.sharp e := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.sharp_congruences | exact GlobalTheory.CompanionTheory.Untilt.sharp_congruences | (intros; apply GlobalTheory.CompanionTheory.Untilt.sharp_congruences <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.crystalline_graded_pieces_description : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ), (∀ z ∈ A.Fil0 r, ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1)) ∧ (∀ w : A.W, algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi}) ∧ ∀ z ∈ A.Fil0 r, ∃ (N : ℕ) (w : A.W), (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces | exact GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces | (intros; apply GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.exists_graded_form_on_affine_chart : KH.LocGr → KH.PolyTf → ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {W₀ : X.Opens} {d : ℕ}
    (c : Coord q W₀ d) (r : ℕ) (hr : r < s),
    ∃ ω : Idx r d → HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) (St (TF l s) {W₀}) r,
      ∀ (W : X.Opens) (hW : IsAffineOpen W) (hle : W ≤ W₀) (Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))))
        (hQ : Q = St (TF l s) {W}) (hQ₀ : Q ≤ St (TF l s) {W₀}) (hF : IsFil (sP Q) (sFil Q)) (hQW : ∀ T, Q T → InU W T)
        (h : HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) Q r),
        ∃! f : Idx r d → Γ(X, W), h = ∑ k, GlobalTheory.CompanionTheory.GrCech.fAct hF hQW r (f k) ((resU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) hQ₀).pull r (ω k)) := by
  first | exact @GlobalTheory.CompanionTheory.GrCech.Omega.basis | exact GlobalTheory.CompanionTheory.GrCech.Omega.basis | (intros; apply GlobalTheory.CompanionTheory.GrCech.Omega.basis <;> assumption)
end
