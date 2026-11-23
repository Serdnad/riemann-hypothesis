module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072

@[expose] public section

section

namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial Classical

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ := ∑ i, m ⟨k, i⟩

def padExp (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) : (Σ k, ι k) →₀ ℕ :=
  ∑ k, Finsupp.single ⟨k, p k⟩ (T - blkDeg m k)

theorem padExp_apply (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) (k : K) (i : ι k) :
    padExp p T m ⟨k, i⟩ = if i = p k then T - blkDeg m k else 0 := by
  classical
  simp only [padExp, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Finsupp.single_apply]
    by_cases h : i = p k
    · subst h; simp
    · rw [if_neg, if_neg h]
      intro e
      exact h (eq_of_heq (Sigma.mk.inj_iff.1 e).2).symm
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact hb (Sigma.mk.inj_iff.1 e).1
  · simp

theorem blkDeg_padExp (p : (k : K) → ι k) (T : ℕ) (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    blkDeg (padExp p T m) k = T - blkDeg m k := by
  classical
  unfold blkDeg
  simp only [padExp_apply]
  rw [Finset.sum_eq_single (p k)]
  · simp [blkDeg]
  · intro b _ hb; rw [if_neg hb]
  · simp

theorem blkDeg_le_totalDegree {Q : MvPolynomial (Σ k, ι k) ℂ} {m : (Σ k, ι k) →₀ ℕ} (hm : m ∈ Q.support)
    (k : K) : blkDeg m k ≤ Q.totalDegree := by
  classical
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  exact Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem exists_homogenize (p : (k : K) → ι k) (Q : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :
    ∃ (G : MvPolynomial (Σ k, ι k) ℂ) (T : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G (fun _ => T) ∧
      (∀ z : (Σ k, ι k) → ℂ, (∀ k, z ⟨k, p k⟩ ≠ 0) →
        eval z G = (∏ k, z ⟨k, p k⟩ ^ T) * eval (ReciprocityTheory.AnForm.R.renPt (ReciprocityTheory.AnForm.R.affCoord p z)) Q) ∧
      ∀ z : (Σ k, ι k) → ℂ, (∃ k, z ⟨k, p k⟩ = 0) → eval z G = 0 := by
  classical
  set Q' : MvPolynomial (Σ k, ι k) ℂ := rename (Fintype.equivFin (Σ k, ι k)).symm Q with hQ'
  have hren : ∀ v : (Σ k, ι k) → ℂ, eval (ReciprocityTheory.AnForm.R.renPt v) Q = eval v Q' := fun v => by
    rw [hQ', eval_rename]
  set T := Q'.totalDegree + 1 with hT
  have hlt : ∀ m ∈ Q'.support, ∀ k, blkDeg m k < T := fun m hm k =>
    Nat.lt_succ_of_le (blkDeg_le_totalDegree hm k)
  refine ⟨∑ m ∈ Q'.support, monomial (m + padExp p T m) (AddMonoidAlgebra.coeff Q' m), T, ?_, ?_, ?_⟩
  · intro n hn k
    obtain ⟨m, hm, hn'⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hn)
    have hn'' := support_monomial_subset hn'
    rw [Finset.mem_singleton] at hn''
    subst hn''
    have e1 : ∑ i, (m + padExp p T m) ⟨k, i⟩ = blkDeg (m + padExp p T m) k := rfl
    rw [e1]
    unfold blkDeg
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    have := blkDeg_padExp p T m k
    unfold blkDeg at this
    rw [this]
    have h2 := (hlt m hm k).le
    unfold blkDeg at h2
    omega
  · intro z hz

    rw [map_sum]

    conv_rhs => rw [hren, Q'.as_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [Fintype.prod_sigma, Fintype.prod_sigma, Fintype.prod_sigma]
    have hpad : ∀ k, ∏ i, z ⟨k, i⟩ ^ padExp p T m ⟨k, i⟩ = z ⟨k, p k⟩ ^ (T - blkDeg m k) := fun k => by
      rw [Finset.prod_eq_single (p k)]
      · rw [padExp_apply, if_pos rfl]
      · intro b _ hb; rw [padExp_apply, if_neg hb, pow_zero]
      · simp
    simp only [hpad, ReciprocityTheory.AnForm.R.affCoord, div_pow]
    have hden : ∀ k, ∏ i, z ⟨k, p k⟩ ^ m ⟨k, i⟩ = z ⟨k, p k⟩ ^ blkDeg m k := fun k => by
      rw [Finset.prod_pow_eq_pow_sum]; rfl
    rw [show (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩ / z ⟨k, p k⟩ ^ m ⟨k, i⟩) =
        (∏ k, ∏ i, z ⟨k, i⟩ ^ m ⟨k, i⟩) / ∏ k, z ⟨k, p k⟩ ^ blkDeg m k by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Finset.prod_div_distrib, hden]]
    have hsub : ∀ k, z ⟨k, p k⟩ ^ (T - blkDeg m k) = z ⟨k, p k⟩ ^ T / z ⟨k, p k⟩ ^ blkDeg m k := fun k =>
      pow_sub₀ _ (hz k) (hlt m hm k).le
    simp only [hsub, Finset.prod_div_distrib]
    have h0 : (∏ k, z ⟨k, p k⟩ ^ blkDeg m k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
    field_simp
  · rintro z ⟨k, hk⟩

    rw [map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨k, p k⟩) ?_)
    rw [hk, Finsupp.coe_add, Pi.add_apply, padExp_apply, if_pos rfl]
    exact zero_pow (by have := hlt m hm k; omega)

end

end PositivityTheory.Xgp.c_bm_exists_boundary
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

open GlobalTheory GlobalTheory.FibreDeriv GlobalTheory.VerticalDeriv

theorem exists_isDerivAt0_loc {g : ℕ} {Z : Scheme.{0}} {B : Set (Fin g → ℂ)} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)}
    (hol : IsHolTo B e) (hB : 0 ∈ B) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber ℂ) ⟶ Z, IsDerivAt0 e w v := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have hd := LocalLift.hol_differentiableAt hol hB h0
  let J : Γ(Z, U) →+* DualNumber ℂ :=
    { toFun := fun f => jet w (fun z => valAt' (e z) U f)
      map_one' := by
        have : (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1 := by
          filter_upwards [LocalLift.hol_eventually_mem hol hB h0] with z hz
          exact valAt'_one _ hz.2
        rw [jet_congr w this, jet_const, map_one]
      map_zero' := by
        simp only [valAt'_zero]
        rw [jet_const, map_zero]
      map_add' := fun f f' => by
        simp only [valAt'_add]
        exact jet_add w (hd f) (hd f')
      map_mul' := fun f f' => by
        simp only [valAt'_mul]
        exact jet_mul w (hd f) (hd f') }
  obtain ⟨v, hv, hve⟩ := TangentOrigin.exists_evalPt_eq hU J
  refine ⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩
  refine TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
  refine (TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_
  rw [hve, ← TangentOrigin.valAt'_eq_evalPt]
  exact fst_jet w (fun z => valAt' (e z) U f)

end PositivityTheory.Xgp.c_bm_exists_period
end
end
