module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle051
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceExtField

open IsDedekindDomain

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem vV_unit (u : Vˣ) : vV V (algebraMap V K' u) = 0 := by
  have : valV V (algebraMap V K' u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]

theorem vV_pos {a : V} (ha : a ≠ 0) (hu : ¬ IsUnit a) : 0 < vV V (algebraMap V K' a) := by
  have h0 : algebraMap V K' a ≠ 0 := by simpa using ha
  have : valV V (algebraMap V K' a) < 1 := by
    rw [valV, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hu
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h0) one_ne_zero).2 this
  simp only [vV]; simp at this; omega

theorem vV_irr {a : V} (ha : Irreducible a) : vV V (algebraMap V K' a) = 1 := by
  have : valV V (algebraMap V K' a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem exists_index {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (j : V →+* V') [IsLocalHom j] (i : K' →+* K'')
    (hi : ∀ v, i (algebraMap V K' v) = algebraMap V' K'' (j v)) :
    ∃ r : ℕ, 0 < r ∧ ∀ x, vV V' (i x) = (r : ℤ) * vV V x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  have inj : ∀ v, v ≠ 0 → algebraMap V' K'' (j v) ≠ 0 := fun v hv => by
    rw [← hi]; simpa using hv
  have pos : 0 < vV V' (algebraMap V' K'' (j p)) :=
    vV_pos (fun h => inj p hp.ne_zero (by simp [h])) (fun h => hp.not_isUnit (isUnit_of_map_unit j p h))
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le pos.le
  have key : ∀ v : V, v ≠ 0 → vV V' (i (algebraMap V K' v)) = (r : ℤ) * vV V (algebraMap V K' v) := by
    intro v hv
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hp
    have h1 : algebraMap V K' p ≠ 0 := by simpa using hp.ne_zero
    have h2 : algebraMap V K' u ≠ 0 := by simp
    rw [hi, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
      vV_mul (inj _ u.ne_zero) (pow_ne_zero _ (inj p hp.ne_zero)), vV_mul h2 (pow_ne_zero _ h1),
      vV_pow (inj p hp.ne_zero), vV_pow h1, vV_unit, vV_irr hp, hr]
    have := vV_unit (K' := K'') (Units.map j.toMonoidHom u)
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at this
    rw [this]; ring
  refine ⟨r, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, vV]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hb1 : algebraMap V K' b ≠ 0 := by simpa using hb0
  have e : algebraMap V K' a / algebraMap V K' b * algebraMap V K' b = algebraMap V K' a := div_mul_cancel₀ _ hb1
  have e1 := vV_mul (V := V) hx hb1
  have e2 := vV_mul (V := V') ((map_ne_zero i).2 hx) ((map_ne_zero i).2 hb1)
  rw [← map_mul, e, key a ha0, key b hb0] at e2
  rw [e] at e1
  rw [e1] at e2
  linarith

end Val

theorem exists_cdvr_finite_extension : ∀ (T : CDVR) (L : Type) [Field L] [Algebra T.Fr L] [FiniteDimensional T.Fr L], ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (ψ : L ≃+* T'.Fr) (φ : T.V →+* T'.V), 0 < e ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) ∧ (∀ a, ψ (algebraMap T.Fr L a) = iT a) ∧ (∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ (T.FinRes → T'.FinRes) := by
  intro T L _ _ _
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  haveI : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  let iT : T.Fr →+* FractionRing W := ψ.toRingHom.comp (algebraMap T.Fr L)
  have hφ : ∀ a, iT (algebraMap T.V T.Fr a) = algebraMap W (FractionRing W) (algebraMap T.V W a) := by
    intro a
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr a) = algebraMap W L (algebraMap T.V W a) :=
      (RingHom.congr_fun hc a).symm
    change (FractionRing.algEquiv W L).symm (algebraMap T.Fr L (algebraMap T.V T.Fr a)) = _
    rw [h1, AlgEquiv.commutes]
  obtain ⟨e, he, hv⟩ := exists_index (algebraMap T.V W) iT hφ
  refine ⟨T', iT, e, ψ, algebraMap T.V W, he, hv, fun a => rfl, fun a => (hφ a).symm, fun h => ?_⟩
  haveI : Finite (ResidueField T.V) := h
  exact Module.finite_of_finite (ResidueField T.V) (M := ResidueField W)

end GlobalTheory.PlaceExtField
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem invariants_and_trace_of_card_eq_finrank :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (G : Finset (R →ₐ[A] R)), G.card = Module.finrank A R → (∀ x : R, (∀ g ∈ G, g x = x) → x ∈ (algebraMap A R).range) ∧ ∀ x : R, algebraMap A R (Algebra.trace A R x) = ∑ g ∈ G, g x := by
  classical
  intro A R _ _ _ _ _ _ _ G hG
  let b : Module.Basis G A R := (Module.finBasis A R).reindex
    (Fintype.equivOfCardEq (by simp [hG]))
  let M : Matrix G G R := Matrix.of fun g i => g.1 (b i)
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    have hli : LinearIndependent R (fun g : G => ((g.1 : R →* R) : R → R)) := by
      refine (linearIndependent_monoidHom R R).comp (fun g : G => (g.1 : R →* R)) ?_
      intro g g' hgg
      apply Subtype.ext
      ext x
      exact DFunLike.congr_fun hgg x
    apply hv
    funext g
    refine Fintype.linearIndependent_iff.1 hli v ?_ g
    have hz : (∑ g : G, v g • g.1.toLinearMap) = 0 := by
      apply b.ext
      intro i
      have := congrFun hvM i
      simpa [Matrix.vecMul, dotProduct, M] using this
    funext x
    have := LinearMap.congr_fun hz x
    simpa using this
  have key : ∀ x : R, Matrix.diagonal (fun g : G => g.1 x) * M =
      M * (Algebra.leftMulMatrix b x).map (algebraMap A R) := by
    intro x
    ext g j
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [M, Matrix.of_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [← map_mul]
    conv_lhs => rw [← b.sum_repr (x * b j)]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def, mul_comm]
  have key2 : ∀ x : R, M.adjugate * (Matrix.diagonal (fun g : G => g.1 x) * M) =
      M.det • (Algebra.leftMulMatrix b x).map (algebraMap A R) := by
    intro x
    rw [key, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨i⟩ : Nonempty G := b.index_nonempty
    have h1 : Matrix.diagonal (fun g : G => g.1 x) = x • (1 : Matrix G G R) := by
      rw [Matrix.smul_one_eq_diagonal]
      congr 1
      funext g
      exact hx g.1 g.2
    have h2 := key2 x
    rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.adjugate_mul] at h2
    have h3 := congrFun (congrFun h2 i) i
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one,
      Matrix.map_apply] at h3
    rw [mul_comm] at h3
    exact ⟨_, (mul_left_cancel₀ hdet h3).symm⟩
  · have h2 := congrArg Matrix.trace (key2 x)
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      Matrix.trace_diagonal] at h2
    have h3 := mul_left_cancel₀ hdet h2
    rw [Algebra.trace_eq_matrix_trace b, ← Finset.sum_coe_sort G (fun g => g x), h3]
    simp [Matrix.trace]

end GlobalTheory.PlaceInt
end
