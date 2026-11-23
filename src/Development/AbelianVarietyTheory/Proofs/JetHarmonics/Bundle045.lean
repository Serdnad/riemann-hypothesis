module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle042
public import Formalism.RealPlaceAnalysis.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle003
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Mathlib.RingTheory.MvPowerSeries.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Proof.ColumnMapShift

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem aeval_weightedHomogeneous {K σ τ : Type} [CommRing K] {w : σ → ℕ} {w' : τ → ℕ}
    {φ : MvPolynomial σ K} {m : ℕ} (hφ : IsWeightedHomogeneous w φ m)
    (v : σ → MvPolynomial τ K) (hv : ∀ i, IsWeightedHomogeneous w' (v i) (w i)) :
    IsWeightedHomogeneous w' (aeval v φ) m := by
  classical

  rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : (Finsupp.weight w) d = m := hφ (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (d.prod fun i k => v i ^ k) (∑ i ∈ d.support, d i • w i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hv i).pow (d i)
  have h2 : (∑ i ∈ d.support, d i • w i) = m := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
  rw [h2] at h1
  have h3 := (isWeightedHomogeneous_C w' (AddMonoidAlgebra.coeff φ d)).mul h1
  rw [zero_add] at h3
  rw [MvPolynomial.algebraMap_eq]
  exact h3

section Col

variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]

def colMap (r : T → ℕ) (g : T → Fin n → Fin n → k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ : Letter T r n => ∑ b, C (g ℓ.1 b ℓ.2.2) * X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter T r n)

theorem rowShift_X_self (σ : T) (i i' : Fin (r σ)) (t : k) (b : Fin n) :
    rowShift r n k σ i i' t (X ⟨σ, i, b⟩) = X ⟨σ, i, b⟩ + C t * X ⟨σ, i', b⟩ := by
  rw [rowShift, aeval_X, if_pos ⟨b, rfl⟩]

theorem rowShift_X_ne (σ : T) (i i' : Fin (r σ)) (t : k) (τ : T) (j : Fin (r τ))
    (h : (⟨τ, j⟩ : Σ s, Fin (r s)) ≠ ⟨σ, i⟩) (b : Fin n) :
    rowShift r n k σ i i' t (X ⟨τ, j, b⟩) = X ⟨τ, j, b⟩ := by
  rw [rowShift, aeval_X, if_neg]
  rintro ⟨b', hb⟩
  apply h
  exact congrArg (fun ℓ : Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ s, Fin (r s))) hb

theorem colMap_X (g : T → Fin n → Fin n → k) (τ : T) (j : Fin (r τ)) (b : Fin n) :
    colMap r g (X ⟨τ, j, b⟩) = ∑ b', C (g τ b' b) * X (⟨τ, j, b'⟩ : Letter T r n) := by
  rw [colMap, aeval_X]

theorem rowShift_colMap (g : T → Fin n → Fin n → k) (σ : T) (i i' : Fin (r σ)) (t : k)
    (P : MvPolynomial (Letter T r n) k) :
    rowShift r n k σ i i' t (colMap r g P) = colMap r g (rowShift r n k σ i i' t P) := by
  have h : (rowShift r n k σ i i' t).comp (colMap r g) = (colMap r g).comp (rowShift r n k σ i i' t) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, j, b⟩
    simp only [AlgHom.comp_apply]
    by_cases h : (⟨τ, j⟩ : Σ s, Fin (r s)) = ⟨σ, i⟩
    · cases h

      simp only [rowShift_X_self, colMap_X, map_sum, map_mul, map_add (f := _), algHom_C, algebraMap_eq,
      Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring

    · simp only [rowShift_X_ne σ i i' t τ j h, colMap_X, map_sum, map_mul, algHom_C, algebraMap_eq]
  exact DFunLike.congr_fun h P

theorem rowInv_colMap (g : T → Fin n → Fin n → k) {P : MvPolynomial (Letter T r n) k}
    (hP : RowInv r n k P) : RowInv r n k (colMap r g P) := by
  intro σ i i' hi t
  rw [rowShift_colMap, hP σ i i' hi t]


open Classical in
def rowWt (n : ℕ) (σ : T) (i : Fin (r σ)) (ℓ : Letter T r n) : ℕ :=
  if (⟨ℓ.1, ℓ.2.1⟩ : Σ s, Fin (r s)) = ⟨σ, i⟩ then 1 else 0

theorem weight_rowWt [Fintype T] (σ : T) (i : Fin (r σ)) (m : Letter T r n →₀ ℕ) :
    Finsupp.weight (rowWt n σ i) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
    Finset.sum_eq_single σ, Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [rowWt]
  · intro j _ hj
    simp [rowWt, hj]
  · simp
  · intro σ' _ hσ
    simp [rowWt, hσ]
  · simp

theorem rowDeg_colMap [Fintype T] (g : T → Fin n → Fin n → k) {a : T → ℕ → ℕ}
    {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) : RowDeg r n k a (colMap r g P) := by
  intro m hm σ i
  have h1 : IsWeightedHomogeneous (rowWt n σ i) P (a σ i) := by
    intro d hd
    rw [weight_rowWt]
    exact hP d (mem_support_iff.2 hd) σ i
  have h2 : IsWeightedHomogeneous (rowWt n σ i) (colMap r g P) (a σ i) := by
    refine aeval_weightedHomogeneous h1 _ fun ℓ => ?_
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    exact IsWeightedHomogeneous.C_mul (isWeightedHomogeneous_X k (rowWt n σ i) ⟨ℓ.1, ℓ.2.1, b⟩) _
  rw [← weight_rowWt]
  exact h2 (mem_support_iff.1 hm)

end Col

theorem push_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F), ∀ (a : (E →+* ℂ) → ℕ → ℕ), (RowInv Dw.mult n c.F P → RowInv Dw.mult n c.F (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P)) ∧ (RowDeg Dw.mult n c.F a P → RowDeg Dw.mult n c.F a (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P)) := by
  intro E _ _ _ H Dw l c n γ P a
  have e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ = colMap Dw.mult fun σ b j => embF c σ (γ b j) := rfl
  rw [e]
  exact ⟨rowInv_colMap _, rowDeg_colMap _⟩

end GlobalTheory.Proof.ColumnMapShift
end
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.integralMvPowerSeries_two_eq_zero_of_vanish_on_squares : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ H : MvPowerSeries (Fin 2) K, Intg H → (∀ n, ∀ x ∈ G n, ∀ y ∈ G n, ev H ![x, y] = 0) → H = 0 := by
  first | exact @GlobalTheory.ConvSer.eq_zero_of_ev_vanish | exact GlobalTheory.ConvSer.eq_zero_of_ev_vanish | (intros; apply GlobalTheory.ConvSer.eq_zero_of_ev_vanish <;> assumption)
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.unitary_glModule_proj_components_level_add_two : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (j : ℕ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → Lev ε E μ j w → ∀ s c d, Lev ε E μ (j + 2) (io s (pr s (Pi.single c w)) d) := by
  first | exact @GlobalTheory.lev_io_pr_single | exact GlobalTheory.lev_io_pr_single | (intros; apply GlobalTheory.lev_io_pr_single <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ComatrixEigen

open Formalism.REAL

theorem qminor_exists_poly {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) :
    ∃ p : Polynomial A, ∀ u : ℂ, qminor E a b u = ∑ d ∈ p.support, u ^ d • p.coeff d := by
  refine ⟨∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : Polynomial A) *
    (List.ofFn fun k : Fin t => ((if a (σ k) = b k then
      Polynomial.X - Polynomial.C (algebraMap ℂ A (k : ℂ)) else 0) + Polynomial.C (E (a (σ k)) (b k)) :
        Polynomial A)).prod, fun u => ?_⟩
  let φ : Polynomial A →+* A := Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u)
    (fun x => (Algebra.commutes u x).symm)
  have hφ : ∀ p : Polynomial A, φ p = ∑ d ∈ p.support, u ^ d • p.coeff d := by
    intro p
    change Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) p = _
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]
  have hX : φ Polynomial.X = algebraMap ℂ A u := Polynomial.eval₂_X _ _
  have hC : ∀ x, φ (Polynomial.C x) = x := fun x => Polynomial.eval₂_C _ _

  rw [← hφ, map_sum, qminor]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp_apply, Tm, map_add, hC]
  split_ifs
  · rw [map_sub φ, hX, hC, map_sub]
  · rw [map_zero]

theorem continuous_qminor_apply {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n t : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin t → Fin n) (v : M) :
    Continuous fun u : ℂ => qminor E a b u v := by
  obtain ⟨p, hp⟩ := qminor_exists_poly E a b
  simp only [hp, LinearMap.sum_apply, LinearMap.smul_apply]
  fun_prop

theorem cof_eigen {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {m : ℕ}
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (x : Fin (m + 1) → M)
    (hE : GlRel E)
    (hq : ∀ (Y : ℂ) (w : M), qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w)
    (t : Fin (m + 1))
    (hx : splitCas E x = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • x) (i : Fin (m + 1)) (Y : ℂ) :
    ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) =
      (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
  have key : ∀ Y : ℂ, (Y + (mu t : ℂ)) • ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) =
      (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
    intro Y
    have hT : ∀ j, ∑ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) = (Y + (mu t : ℂ)) • x j := by
      intro j
      have h1 := congrFun hx j
      simp only [splitCas, Pi.smul_apply] at h1
      have h2 : ∀ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) =
          (if j = l then (Y + (m : ℂ) / 2 - (m : ℂ)) • x l else 0) + E j l (x l) := by
        intro l
        rw [Tm, LinearMap.add_apply]
        split_ifs
        · rw [Module.algebraMap_end_apply]
        · rw [LinearMap.zero_apply]
      simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [neg_eq_iff_eq_neg] at h1
      rw [h1, ← neg_smul, ← add_smul]
      congr 1
      push_cast
      ring
    have hu : Y + (m : ℂ) / 2 = Y + (((m + 1 : ℕ) : ℂ) - 1) / 2 := by push_cast; ring
    have h3 : ∑ l, (if i = l then qdet E (Y + (m : ℂ) / 2) else 0) (x l) =
        (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, hu, hq, smul_smul, Finset.mul_prod_erase _ (fun r => Y + (mu r : ℂ)) (Finset.mem_univ t)]
      · intro l _ hl
        rw [if_neg (Ne.symm hl), LinearMap.zero_apply]
      · simp
    rw [← h3]
    simp only [← qComatrix (Module.End ℂ M) m E hE (Y + (m : ℂ) / 2) i, LinearMap.sum_apply]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Module.End.mul_apply]

    rw [← map_sum, ← map_sum, hT, map_smul, map_smul, Module.End.intCast_apply,
    ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    rfl
  have hc1 : Continuous fun Y : ℂ => ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) := by
    refine continuous_finsetSum _ fun j _ => Continuous.const_smul ?_ _
    exact (continuous_qminor_apply E _ _ (x j)).comp (continuous_add_const _)
  have hc2 : Continuous fun Y : ℂ => (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by fun_prop
  have hd : Dense ({-(mu t : ℂ)}ᶜ : Set ℂ) := dense_compl_singleton _
  refine congrFun (Continuous.ext_on hd hc1 hc2 fun Z hZ => ?_) Y
  have hne : Z + (mu t : ℂ) ≠ 0 := fun h => hZ (eq_neg_of_add_eq_zero_left h)
  exact smul_right_injective M hne (key Z)

end GlobalTheory.ComatrixEigen

namespace GlobalTheory

theorem comatrix_picks_eigencomponent : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (y : Fin (m + 1) → Fin (m + 1) → M), Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ t, splitCas E (y t) = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∀ s i, ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) • Formalism.REAL.qminor E (Fin.succAbove j) (Fin.succAbove i) (-(mu s : ℂ) + (m : ℂ) / 2) (∑ t, y t j) = (∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s)) • y s i := by
  intro M _ _ m E mu y hE hq hy s i

  simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [fun t => ComatrixEigen.cof_eigen E mu (y t) hE hq t (hy t) i (-(mu s : ℂ))]
  rw [Finset.sum_eq_single s]
  · simp only [neg_add_eq_sub]
  · intro t _ ht
    rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨Ne.symm ht, Finset.mem_univ _⟩) (neg_add_cancel _),
      zero_smul]
  · simp

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelEigen

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem sval_act {n : ℤ} {θ : ThetaGrp A L n T} {s s' : LB.Sec (LPow A L n T)} (H : IsActOf A L n θ s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J) (hJ : Good L z J) :
    sval s' r z J = (tval θ r z J).val * sval s (r ≫ (translT A θ.pt).left) z J := by
  have l₁ := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _)
  let j : Fin 2 → L.ι := fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)
  have hz : r z ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j := hJ.mem _ r
  have e : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  rw [sval_of s _ z J (fun _ => j 1) (fun _ => by rw [Category.assoc, e]; rfl)]
  exact (gs_res r z (chart_le_zero A L _ j) hz _).symm.trans ((congrArg (gs r z _) (H j)).trans
    ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _)
      ((gs_res r z (l₁ j) hz _).trans (gs_pull r (translT A θ.pt).left z
        (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1)) (l₁ j hz) _)))))

theorem translT_snd_comp (a : A ⟶ A) [IsMonHom a] {c : T ⟶ A} (hc : c ≫ a = 1) :
    translT A c ≫ snd T A ≫ a = snd T A ≫ a := by
  rw [← Category.assoc, translT, lift_snd]
  show ((fst T A ≫ c) * snd T A) ≫ a = _
  rw [MonObj.mul_comp, Category.assoc, hc, MonObj.comp_one, _root_.one_mul]

theorem translT_whisker (a : A ⟶ A) [IsMonHom a] {c : T ⟶ A} (hc : c ≫ a = 1) :
    translT A c ≫ T ◁ a = T ◁ a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, whiskerLeft_snd, translT_snd_comp a hc]

theorem translT_comm [IsCommMonObj A] (x y : T ⟶ A) : translT A x ≫ translT A y = translT A y ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Category.assoc, H1.transl_snd]
    exact H1.transl_comm x y

theorem exists_kernel_lift (hL : L.IsLB) (a : A ⟶ A) [IsMonHom a] {m k : ℤ}
    (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ≫ a).left] ![m, -k])) (hmu : mu.IsGen)
    {c : T ⟶ A} (hc : c ≫ a = 1) :
    ∃ θ : ThetaGrp A L m T, θ.pt = c ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval θ r z J = val mu r z J * (val mu (r ≫ (translT A c).left) z J)⁻¹ := by
  have e₀ : (translT A c).left ≫ (snd T A).left = (translPt A c).left := by
    rw [← Over.comp_left, translT, lift_snd]
  have e₁ : (translT A c).left ≫ (snd T A ≫ a).left = (snd T A ≫ a).left := by
    rw [← Over.comp_left, translT_snd_comp a hc]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A c).left]) (ε' := ![m, -m])
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₀, e₁,
        zpow_neg, inv_inv, Pi.neg_apply]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L _ _ _ _ mu (LB.invGen L _ _ (LB.pullGen L _ _ mu (translT A c).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hmu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hmu _)))
  refine ⟨⟨c, u, hu⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
  rw [val_mul hJ, val_inv, val_pull hJ]

theorem commIsOf_of_weilIs (hL : L.IsLB) [Unique T.left] {n : ℤ} (θx θy : ThetaGrp A L n T)
    {e : Γ(T.left, ⊤)ˣ} (H : WeilIs A L n θx.pt θy.pt e) : CommIsOf A L n θx θy e := by
  obtain ⟨V, hV, -, H⟩ := H default
  obtain rfl : V = ⊤ := top_le_iff.1 fun x _ => by rw [Subsingleton.elim x default]; exact hV
  let h := overResι (T := T) ⊤
  have : IsIso h.left := inferInstanceAs (IsIso (Scheme.topIso T.left).hom)
  have : IsIso ((Over.forget S).map h) := this
  have : IsIso h := isIso_of_reflects_iso h (Over.forget S)
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1 (H θx' θy' hx hy)
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  obtain ⟨r', rfl⟩ : ∃ r' : Z ⟶ (overRes (T := T) ⊤ ⊗ A).left, r = r' ≫ (h ▷ A).left :=
    ⟨r ≫ (inv (h ▷ A)).left, by rw [Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.comp_id]⟩
  have t : ∀ x : T ⟶ A, (r' ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r' ≫ (h ▷ A).left) ≫ (translT A x).left := fun x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (r' ≫ (fst (overRes (T := T) ⊤) A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom e) =
      gm ((r' ≫ (h ▷ A).left) ≫ (fst T A).left) z ⊤ e := by
    refine (gm_pull (r' ≫ (fst (overRes (T := T) ⊤) A).left) h.left z ⊤ trivial e).trans ?_
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  have := H' Z r' z J hJ
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t] at this
  exact this.trans (congrArg _ g)

end GlobalTheory.KernelEigen

namespace GlobalTheory


open KernelEigen CommPairing in
theorem translate_pullback_eigensection : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (K : Type) [Field K] (p : Spec (CommRingCat.of K) ⟶ S) (a : A ⟶ A), IsMonHom a → ∀ (N k : ℕ) (mu : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (Over.mk p) A).left, (snd (Over.mk p) A ≫ a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)])), mu.IsGen → ∀ (s : LB.Sec (LPow A L (k : ℤ) (Over.mk p))) (t' t : LB.Sec (LPow A L ((k * N : ℕ) : ℤ) (Over.mk p))), (∀ (z : (Over.mk p ⊗ A).left) (J), Good L z J → sval t' (𝟙 _) z J = (val mu (𝟙 _) z J).val * sval s (Over.mk p ◁ a).left z J) → ∀ θ : ThetaGrp A L ((k * N : ℕ) : ℤ) (Over.mk p), IsActOf A L ((k * N : ℕ) : ℤ) θ t' t → ∀ (c : Over.mk p ⟶ A) (e : Γ((Over.mk p).left, ⊤)ˣ), c ≫ a = 1 → WeilIs A L ((k * N : ℕ) : ℤ) c θ.pt e → ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk p ⊗ A).left) (z : Z) (J), Good L z J → sval t (r ≫ (translT A c).left) z J * (val mu r z J).val = gs (r ≫ (fst (Over.mk p) A).left) z ⊤ e.val * (sval t r z J * (val mu (r ≫ (translT A c).left) z J).val) := by
  intro S A _ _ L hL K _ p a ha N k mu hmu s t' t ht' θ hθ c e hc hW Z r z J hJ
  haveI : Unique (Over.mk p).left := inferInstanceAs (Unique (PrimeSpectrum K))
  obtain ⟨θc, rfl, hv⟩ := exists_kernel_lift hL a mu hmu hc
  have hC := (commIsOf_iff hL _ _ _).1 (commIsOf_of_weilIs hL θc θ hW) Z r z J hJ
  have hs := ReciprocityTheory.ChartRestriction.G.Geo.Tor.secRel_iff hL _ _ t' _ _ s (Over.mk p ◁ a).left _ _ mu
  have ht := hs.1 (hs.2 fun y J hJ => by rw [ht' y J hJ, Category.id_comp, _root_.mul_comm])
  have e₁ : (r ≫ (translT A θc.pt).left) ≫ (translT A θ.pt).left =
      (r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, translT_comm]
  have e₂ : ((r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left) ≫ (Over.mk p ◁ a).left =
      (r ≫ (translT A θ.pt).left) ≫ (Over.mk p ◁ a).left := by
    rw [Category.assoc, ← Over.comp_left, translT_whisker a hc]
  rw [sval_act hθ _ z J hJ, sval_act hθ _ z J hJ, e₁, ht _ _ z J hJ, ht _ _ z J hJ, e₂,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_unit _ z ⊤ trivial]
  rw [hv _ _ z J hJ, hv _ _ z J hJ] at hC
  generalize tval θ (r ≫ (translT A θc.pt).left) z J = x₁ at hC ⊢
  generalize tval θ r z J = x₂ at hC ⊢
  generalize val mu ((r ≫ (translT A θ.pt).left) ≫ (translT A θc.pt).left) z J = x₃ at hC ⊢
  generalize val mu (r ≫ (translT A θ.pt).left) z J = x₄ at hC ⊢
  generalize val mu (r ≫ (translT A θc.pt).left) z J = x₅ at hC ⊢
  generalize val mu r z J = x₆ at hC ⊢
  generalize ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm (r ≫ (fst (Over.mk p) A).left) z ⊤ e = x₇ at hC ⊢
  have key : x₁ * x₃ * x₆ = x₇ * x₂ * x₄ * x₅ := by
    apply Additive.ofMul.injective
    have a₀ := congrArg Additive.ofMul hC
    simp only [ofMul_mul, ofMul_inv] at a₀ ⊢
    linear_combination (norm := abel) a₀
  have key' := congrArg Units.val key
  simp only [Units.val_mul] at key'
  linear_combination (sval s ((r ≫ (translT A θ.pt).left) ≫ (Over.mk p ◁ a).left) z J) * key'

end GlobalTheory
end
end
