module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MovedOfSplitPl
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominator
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle053
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle052
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemImage

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def lin {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : Fin m → MvPowerSeries (Fin n) C :=
  fun a => ∑ b, N a b • X b

theorem lin_const {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : constantCoeff (lin N a) = 0 := by
  simp [lin]

theorem lin_hs {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : HasSubst (lin N) :=
  hasSubst_of_constantCoeff_zero (lin_const N)

theorem int_comb {σ ι : Type} [Fintype ι] {c : ι → C} (hc : ∀ i, IsIntV v (c i))
    {f : ι → MvPowerSeries σ C} (hf : ∀ i, MvIsInt v (f i)) : MvIsInt v (∑ i, c i • f i) :=
  (ptIntSer v σ).sum_mem fun i _ => ptIntSer_smul (hc i) (hf i)

theorem lin_int {m n : ℕ} {N : Matrix (Fin m) (Fin n) C} (h : ∀ a b, IsIntV v (N a b)) (a : Fin m) :
    MvIsInt v (lin N a) := int_comb (h a) fun b => ptIntSer_X b

theorem lin_coeff {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (lin N a) = N a i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin, map_sum, pt_coeff_single_X]

theorem const_comb {σ ι : Type} [Fintype ι] (c : ι → C) {f : ι → MvPowerSeries σ C}
    (hf : ∀ i, constantCoeff (f i) = 0) : constantCoeff (∑ i, c i • f i) = 0 := by
  simp [hf]

theorem comb_comb {σ : Type} {l m n : ℕ} (A : Matrix (Fin l) (Fin m) C) (B : Matrix (Fin m) (Fin n) C)
    (f : Fin n → MvPowerSeries σ C) (b : Fin l) :
    ∑ a, A b a • ∑ e, B a e • f e = ∑ e, (A * B) b e • f e := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem comb_one {σ : Type} {n : ℕ} (f : Fin n → MvPowerSeries σ C) (b : Fin n) :
    ∑ e, (1 : Matrix (Fin n) (Fin n) C) b e • f e = f b := by
  simp [Matrix.one_apply, ite_smul]

theorem subst_lin {σ : Type} {m n : ℕ} {s : Fin n → MvPowerSeries σ C} (hs : HasSubst s)
    (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : subst s (lin N a) = ∑ b, N a b • s b := by
  rw [lin, subst_sum_smul hs]
  simp only [subst_X hs]

theorem coeff_comb_lg {d m n : ℕ} (G : LogFGL v d) (N : Matrix (Fin m) (Fin d) C)
    (L : Matrix (Fin d) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (∑ e, N a e • (subst (lin L) (G.lg e) : MvPowerSeries (Fin n) C)) = (N * L) a i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, pt_coeff_single_subst (lin_hs L) (lin_const L) (G.lg_const _), G.lg_lin, lin_coeff,
    Matrix.mul_apply]

theorem lg_add {σ : Type} [Finite σ] {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    subst (fun b => (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C)) (G.lg a) =
      subst x (G.lg a) + subst y (G.lg a) := by
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero (by rintro (b | b) <;> simp [hx, hy])
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) hs, G.lg_F, subst_add hs,
    subst_comp_subst_apply hl hs, subst_comp_subst_apply hr hs]
  simp only [subst_X hs, Sum.elim_inl, Sum.elim_inr]

theorem add_const {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (b : Fin d) :
    constantCoeff (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) = 0 :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (G.F_const b)

theorem add_int {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0)
    (ix : ∀ a, MvIsInt v (x a)) (iy : ∀ a, MvIsInt v (y a)) (b : Fin d) :
    MvIsInt v (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  ptIntSer_subst (hasSubst_of_constantCoeff_zero h) (by rintro (b | b); exacts [ix b, iy b]) (G.F_int b)

theorem lg_hom {σ : Type} {d m : ℕ} {f : MvPowerSeries (Fin d) C} {φ : Fin d → MvPowerSeries (Fin m) C}
    (h0 : ∀ a, constantCoeff (φ a) = 0) {c : Fin m → C} {g : Fin m → MvPowerSeries (Fin m) C}
    (h : subst φ f = ∑ a, c a • g a) {s : Fin m → MvPowerSeries σ C} (hs : HasSubst s) :
    subst (fun b => (subst s (φ b) : MvPowerSeries σ C)) f = ∑ a, c a • (subst s (g a) : MvPowerSeries σ C) := by
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hs, h, subst_sum_smul hs]

theorem exists_retraction [CharZero C] {d d' : ℕ} (G : LogFGL v d) {I : Matrix (Fin d) (Fin d') C}
    {P : Matrix (Fin d') (Fin d) C} (hI : ∀ a b, IsIntV v (I a b)) (hP : ∀ a b, IsIntV v (P a b))
    (hPI : P * I = 1) {φ ψ : Fin d → MvPowerSeries (Fin d) C} (hφ : IsIntHom G G φ (I * P))
    (hψ : IsIntHom G G ψ (1 - I * P)) :
    ∃ q : Fin d' → MvPowerSeries (Fin d) C, (∀ b, constantCoeff (q b) = 0) ∧ (∀ b, MvIsInt v (q b)) ∧
      ∀ b, subst q (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) = ∑ a, P b a • G.lg a := by
  have hMi : ∀ a b, IsIntV v ((I * P) a b) := fun a b => by
    rw [Matrix.mul_apply]
    exact (ptIntSub v).sum_mem fun c _ => (ptIntSub v).mul_mem (hI a c) (hP c b)
  have hNi : ∀ a b, IsIntV v ((1 - I * P : Matrix (Fin d) (Fin d) C) a b) := fun a b => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine (ptIntSub v).sub_mem ?_ (hMi a b)
    split_ifs
    exacts [(ptIntSub v).one_mem, (ptIntSub v).zero_mem]
  have hPM : P * (I * P) = P := by rw [← Matrix.mul_assoc, hPI, Matrix.one_mul]
  have hPN : P * (1 - I * P : Matrix (Fin d) (Fin d) C) = 0 := by rw [Matrix.mul_sub, hPM, Matrix.mul_one, sub_self]
  have hMM : I * P * (I * P) = I * P := by rw [Matrix.mul_assoc, hPM]
  have hsq : I * P * (I * P) + (1 - I * P : Matrix (Fin d) (Fin d) C) * (1 - I * P : Matrix (Fin d) (Fin d) C) = 1 := by
    rw [mul_sub, sub_mul, sub_mul, hMM]; simp
  generalize hM : I * P = M at *
  generalize (1 - M : Matrix (Fin d) (Fin d) C) = N at *
  set x : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin M) (φ a) with hx
  set y : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin N) (ψ a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs M) (lin_const M) (hφ.1 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs N) (lin_const N) (hψ.1 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst (lin_hs M) (lin_int hMi) (hφ.2.1 a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst (lin_hs N) (lin_int hNi) (hψ.2.1 a)
  set Θ : Fin d → MvPowerSeries (Fin d) C := fun b => subst (Sum.elim x y) (G.F b) with hΘ
  have Θ0 : ∀ a, constantCoeff (Θ a) = 0 := add_const G x0 y0
  have Θs : HasSubst Θ := hasSubst_of_constantCoeff_zero Θ0
  have hlg : ∀ a, subst Θ (G.lg a) = ∑ e, M a e • (subst (lin M) (G.lg e) : MvPowerSeries (Fin d) C) +
      ∑ e, N a e • (subst (lin N) (G.lg e) : MvPowerSeries (Fin d) C) := fun a => by
    rw [hΘ, lg_add G x0 y0, hx, hy, lg_hom hφ.1 (hφ.2.2 a) (lin_hs M), lg_hom hψ.1 (hψ.2.2 a) (lin_hs N)]
  have Θ1 : ∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0 := fun a b => by
    have h := congrArg (coeff (Finsupp.single b 1)) (hlg a)
    rw [map_add (f := _), coeff_comb_lg, coeff_comb_lg, ← Matrix.add_apply, hsq, Matrix.one_apply,
      pt_coeff_single_subst Θs Θ0 (G.lg_const a)] at h
    simpa [G.lg_lin] using h
  obtain ⟨Ψ, Ψi, Ψ0, hΨ, -⟩ := GlobalTheory.IntInv.exists_int_inv C v d Θ (add_int G x0 y0 xi yi) Θ0 Θ1
  have Ψs : HasSubst Ψ := hasSubst_of_constantCoeff_zero Ψ0
  refine ⟨fun b => ∑ a, P b a • Ψ a, fun b => const_comb _ Ψ0, fun b => int_comb (hP b) Ψi, fun b => ?_⟩
  have key : subst (lin P) (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) =
      subst Θ (∑ a, P b a • G.lg a) := by
    have hl : (fun a => (subst (lin P) (lin I a) : MvPowerSeries (Fin d) C)) = lin M := by
      funext a
      rw [subst_lin (lin_hs P), ← hM]
      exact comb_comb I P _ a
    rw [subst_sum_smul (lin_hs P), subst_sum_smul Θs]
    simp only [hlg, smul_add, Finset.sum_add_distrib, comb_comb, hPM, hPN,
      subst_comp_subst_apply (lin_hs I) (lin_hs P), hl]
    simp
  have h := congrArg (subst Ψ) key
  rw [subst_comp_subst_apply (lin_hs P) Ψs, subst_comp_subst_apply Θs Ψs] at h
  simp only [subst_lin Ψs, hΨ] at h
  rw [h, show (fun a => (X a : MvPowerSeries (Fin d) C)) = X from rfl, subst_self]
  rfl

theorem exists_image (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d d' : ℕ) (G : LogFGL v d)
    (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C) (hI : ∀ a b, IsIntV v (I a b))
    (hP : ∀ a b, IsIntV v (P a b)) (hPI : P * I = 1) (hφ : ∃ φ, IsIntHom G G φ (I * P))
    (hψ : ∃ ψ, IsIntHom G G ψ (1 - I * P)) :
    ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨ψ, hψ⟩ := hψ
  obtain ⟨q, q0, qi, hq⟩ := exists_retraction G hI hP hPI hφ hψ
  set lg' : Fin d' → MvPowerSeries (Fin d') C := fun b => ∑ a, P b a • subst (lin I) (G.lg a) with hlg'
  set j : Fin d → MvPowerSeries (Fin d') C := fun a => subst (lin I) (φ a) with hjdef
  have j0 : ∀ a, constantCoeff (j a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (hφ.1 a)
  have ji : ∀ a, MvIsInt v (j a) := fun a => ptIntSer_subst (lin_hs I) (lin_int hI) (hφ.2.1 a)
  have hj : ∀ a, subst j (G.lg a) = ∑ e, I a e • lg' e := fun a => by
    rw [hjdef, lg_hom hφ.1 (hφ.2.2 a) (lin_hs I), hlg']
    exact (comb_comb I P _ a).symm
  have hl0 : ∀ b : Fin d', constantCoeff (X (Sum.inl b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hr0 : ∀ b : Fin d', constantCoeff (X (Sum.inr b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hl := hasSubst_of_constantCoeff_zero hl0
  have hr := hasSubst_of_constantCoeff_zero hr0
  set x : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inl b)) (j a) with hx
  set y : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inr b)) (j a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a => constantCoeff_subst_eq_zero hl hl0 (j0 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a => constantCoeff_subst_eq_zero hr hr0 (j0 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst hl (fun _ => ptIntSer_X _) (ji a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst hr (fun _ => ptIntSer_X _) (ji a)
  have s0 := add_const G x0 y0
  have ss := hasSubst_of_constantCoeff_zero s0
  refine ⟨{ lg := lg'
            lg_const := fun b => const_comb _ fun a =>
              constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (G.lg_const a)
            lg_lin := fun a b => by rw [hlg', coeff_comb_lg, hPI, Matrix.one_apply]
            F := fun b => subst (fun a => (subst (Sum.elim x y) (G.F a) : MvPowerSeries (Fin d' ⊕ Fin d') C)) (q b)
            F_int := fun b => ptIntSer_subst ss (add_int G x0 y0 xi yi) (qi b)
            F_const := fun b => constantCoeff_subst_eq_zero ss s0 (q0 b)
            lg_F := fun b => ?_ }, ⟨j, j0, ji, hj⟩, q, q0, qi, hq⟩
  rw [lg_hom q0 (hq b) ss]
  simp only [lg_add G x0 y0, smul_add, Finset.sum_add_distrib]
  simp only [hx, hy, lg_hom j0 (hj _) hl, lg_hom j0 (hj _) hr, comb_comb, hPI, comb_one]

end GlobalTheory.IdemImage
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SplitMove

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.UnRep.FullReps GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open scoped TensorProduct Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_conj (v : Fin n → E) :
    (fun j => IsCMField.complexConj E (IsCMField.complexConj E (v j))) = v :=
  funext fun j => IsCMField.complexConj_apply_apply E (v j)

theorem unimod_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} (hU : Λ.Unimod) :
    (conjLat H Λ.La).Unimod := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range → IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨H.bar a, H.bar_eq a⟩
  intro v
  rw [mem_conjLat, hU]
  constructor
  · intro hv w hw
    have := hr _ (hv _ hw)

    simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this
  · intro hv w hw
    have := hr _ (hv (fun j => IsCMField.complexConj E (w j)) (by rw [mem_conjLat, conj_conj]; exact hw))

    simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this

theorem trivAt_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} {N : ℕ} (hT : Λ.TrivAt N) :
    (conjLat H Λ.La).TrivAt N := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  exact ⟨k, hk, conjLat_le H (by rw [← H.bar_eq, map_natCast])
    ⟨(Move.span_smul_le _ _ _).1 h1, (Move.span_smul_le _ _ _).1 h2⟩⟩

theorem congAt_of_congAtA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    {N M : ℕ} (hM : 0 < M) {γ : Matrix (Fin n) (Fin n) E} (h : CongAtA F L N M (fm F γ)) :
    GlobalTheory.UnRep.CongAt L N M γ := by
  obtain ⟨t, ht, h⟩ := h
  have hrat := (hat_rational_points_and_approx F E n L hfg hsp).1
  refine ⟨t, ht, fun v hv => ?_⟩
  obtain ⟨w, hw, e⟩ := h _ ((hrat v).2 hv)
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
  have key : t • (γ *ᵥ v - v) = M • ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) := by
    rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
  refine ⟨_, ?_, key⟩
  rw [← hrat]
  have e' : fv F ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) = w := by
    refine Move.nsmul_cancel _ hM ?_
    rw [← cap_fv_nsmul, ← key, cap_fv_nsmul, Move.fv_sub, Move.fv_mulVec, e]
  rw [e']
  exact hw

theorem exists_move_matrix (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (N : ℕ) (hN : 0 < N) (Λ : GenLat E n)
    (hU : Λ.Unimod) (hT : Λ.TrivAt N) :
    ∃ (γ : Matrix (Fin n) (Fin n) E) (h : GL (Fin n) (RA (maximalRealSubfield E) E))
      (Lh : Submodule (𝓞 E) (Fin n → E)), IsUnitaryM γ ∧
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) ∧
      IsUnA (IsCMField.complexConj E) 1 h.1 ∧ SuppSplit (IsCMField.complexConj E) N h.1 ∧
      (Lh : Set (Fin n → E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield E) h.1 (stdLat E n) ∧
      actLat γ Λ = conjLat H Lh := by
  obtain ⟨hherm, hrk, hfg, hsp, -, -, -, hun⟩ := StdInhab.main E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.AdelTranslate.exists_adelic_translate E H n N _ hN (unimod_conj H hU)
    (trivAt_conj H hT)
  obtain ⟨γ, h, k, hγ, hh, -, e, hs, hk, hk'⟩ := GlobalTheory.UnRep.exists_rep_suppSplit (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g N hg hN
  obtain ⟨Lh, hLh, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E n (stdLat E n) h hfg hsp
  have hu : adjM γ.1 * γ.1 = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← (hun _).1 hγ i j]
    rfl
  have hu' : γ.1 * adjM γ.1 = 1 := mul_eq_one_comm.1 hu
  have hδ : adjM γ.1ᵀ * γ.1ᵀ = 1 := by
    rw [show adjM γ.1ᵀ = (adjM γ.1)ᵀ from rfl, ← Matrix.transpose_mul, hu', Matrix.transpose_one]
  have hδ' : γ.1ᵀ * adjM γ.1ᵀ = 1 := mul_eq_one_comm.1 hδ
  have ck : CongAtA (maximalRealSubfield E) (stdLat E n) N N (k⁻¹).1 := by
    refine ⟨1, Nat.coprime_one_left _, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hk _ (hk' z hz)
    refine ⟨-w, neg_mem hw, ?_⟩
    rw [one_smul, smul_neg, ← e, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, neg_sub]
  have ch : CongAtA (maximalRealSubfield E) (stdLat E n) N N (h⁻¹).1 := by
    obtain ⟨ε, -, -, he, hcut⟩ := hs
    obtain ⟨t, ht, hb⟩ := (idempotent_adeles_small_matrices (maximalRealSubfield E) E n (stdLat E n) hfg hsp).2.2.2.1
      N N ε ((h⁻¹).1 - 1) hN fun v hv => by
        by_contra h0
        exact (he v h0).2 hv
    refine ⟨t, ht, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hb z hz
    rw [cut_inv h _ hcut, Matrix.sub_mulVec, Matrix.one_mulVec] at e
    exact ⟨w, hw, e⟩
  have eγ : fm (maximalRealSubfield E) γ.1 = g.1 * (k⁻¹).1 * (h⁻¹).1 := by
    rw [e, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have cγ : GlobalTheory.UnRep.CongAt (stdLat E n) N N γ.1 := by
    refine congAt_of_congAtA (F := maximalRealSubfield E) _ hfg hsp hN ?_
    rw [eγ]
    exact LatForm.congAtA_mul _ _ _ _ _ (LatForm.congAtA_mul _ _ _ _ _ (hgc N hN) ck) ch
  have hmove : ∀ u, u ∈ Lh ↔ γ.1 *ᵥ u ∈ (conjLat H Λ.La).La := by
    intro u
    rw [← SetLike.mem_coe, ← SetLike.mem_coe (p := (conjLat H Λ.La).La), hΛ, hLh]
    constructor
    · rintro ⟨z, hz, ez⟩
      refine ⟨_, hk' z hz, ?_⟩
      rw [Move.fv_mulVec, ← ez, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, Units.mul_inv_cancel_right]
    · rintro ⟨z, hz, ez⟩
      refine ⟨k.1 *ᵥ z, ?_, ?_⟩
      · obtain ⟨w, hw, e⟩ := hk z hz
        rw [sub_eq_iff_eq_add.1 e]
        exact add_mem (nsmul_mem hw _) hz
      · have := congrArg (fun x => fm (maximalRealSubfield E) (γ⁻¹).1 *ᵥ x) ez
        rw [← Move.fv_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, e,
          ← mul_assoc, ← mul_assoc, ← FullReps.fm_mul, Units.inv_mul, FullReps.fm_one, one_mul] at this
        rw [Matrix.mulVec_mulVec, this]
  refine ⟨γ.1ᵀ, h, Lh, hδ, fun j => ?_, hh, hs, hLh, congrArg GenLat.mk (Submodule.ext fun v => ?_)⟩
  · obtain ⟨t, ht, hc⟩ := cγ
    refine ⟨t, ht, fun i => ?_⟩
    obtain ⟨w, hw, ew⟩ := hc _ (StdInhab.single_mem n i)
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hw j trivial)
    refine ⟨b, ?_⟩
    have := congrFun ew j
    rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← hb, Pi.sub_apply,
      Matrix.mulVec_single_one] at this
    refine Eq.trans ?_ this
    congr 2
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Pi.single_apply, Ne.symm hij]
  · have hc : (fun j => IsCMField.complexConj E ((γ.1 *ᵥ fun j => IsCMField.complexConj E (v j)) j)) =
        adjM γ.1ᵀ *ᵥ v := by
      funext j
      simp [Matrix.mulVec, dotProduct, adjM]
    change v ∈ (actLat γ.1ᵀ Λ).La ↔ v ∈ (conjLat H Lh).La
    rw [mem_conjLat, hmove, mem_conjLat, hc]
    constructor
    · rintro ⟨u, hu, rfl⟩
      change adjM γ.1ᵀ *ᵥ (γ.1ᵀ *ᵥ u) ∈ Λ.La
      rw [Matrix.mulVec_mulVec, hδ, Matrix.one_mulVec]
      exact hu
    · intro hv
      refine ⟨_, hv, ?_⟩
      change γ.1ᵀ *ᵥ (adjM γ.1ᵀ *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hδ', Matrix.one_mulVec]

end General

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_move_to_split : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (H : Geo.Tor.Host D.host.E) (N : ℕ), 0 < N → ∀ Λ : GenLat D.host.E V.rank, Λ.Unimod → Λ.TrivAt N → ∃ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ ∧ (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) i j : 𝓞 D.host.E) : D.host.E)) ∧ h ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V h).1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ Λ = GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h)) := by
  intro D V hg hL H N hN Λ hU hT
  obtain ⟨γ, h', Lh, h1, h2, h3, h4, h5, h6⟩ := exists_move_matrix H N hN Λ hU hT
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨h, hh, eh⟩ := lift h' (by
    rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc]
    exact h3)
  refine ⟨γ, h, h1, h2, hh, ?_, ?_⟩
  · rw [eh, hc]; exact h4
  · rw [GlobalTheory.SplitReps.hLat_one] at hL
    rw [GlobalTheory.SplitReps.hLat_eq V (FWT.fin V h) Lh (by
      rw [hL]
      change _ = GlobalTheory.AdLat.latOf D.host.F (finHom V h).1 _
      rw [eh]
      exact h5)]
    exact h6

end GlobalTheory.SplitMove
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_decay_step : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ t : ℝ, 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a ψ hψ t ht i j hij Ω hΩ
  have hL : {k | finRep E a k ψ = ψ} ∈ nhds (1 : GL (Fin a) (Af E)) :=
    hψ.1.level.mem_nhds (by simp)
  obtain ⟨R, hR0, hcov⟩ := GlobalTheory.T.unipotentRadical_adelic_eq_rat_mul_boundedReal_mul_level E a (j : ℕ) _ hL
  obtain ⟨Ω', B, C, hΩ', hC, hvar⟩ := GlobalTheory.T.siegelCone_smooth_variation_along_bounded_unipotent E a t ht i j hij Ω hΩ R hR0
  refine ⟨Ω', B, C, hΩ', hC, fun r d hr hrt hd M hM hY c hc => ?_⟩
  refine GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation E a ψ hψ (j : ℕ) (by omega) j.2 (infGL E a (d * c)) (C * (r j / r i) * M) fun x => ?_
  obtain ⟨ξ, z, k, hk, hz, hx⟩ := hcov x
  have hk' : finRep E a k ψ = ψ := hk
  have e : ψ.1 (unip x * infGL E a (d * c)) = ψ.1 (infGL E a (unip z * (d * c))) := by
    rw [hx, mul_assoc, mul_assoc, ← infGL_comm, ← mul_assoc (infGL E a (unip z)), ← map_mul, hψ.1.left]
    have := congrArg (fun φ : Sm E a => φ.1 (infGL E a (unip z * (d * c)))) hk'
    exact this
  rw [e]
  exact hvar ψ r d hr hrt hd M hM hY c hc z hz

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.finitePart_mem_fullLevel_of_keeps_selfDualLattice : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Links.IsSDFrame V β Λ 1 → V.rank ≤ L.r → L.P.H = ⊤ → ∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L := by
  first | exact @GlobalTheory.CovTop.VolUp.FullLevel.finE_mem_lev_of_isKM | exact GlobalTheory.CovTop.VolUp.FullLevel.finE_mem_lev_of_isKM | (intros; apply GlobalTheory.CovTop.VolUp.FullLevel.finE_mem_lev_of_isKM <;> assumption)
end
