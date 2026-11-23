module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMeasurePreservingFrameChangeProportionalHe
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_measurePreserving_frameChange_proportional_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (y : Frame X.Ψ r) (y' : Frame X'.Ψ r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → y ∈ OrthFr X → y' ∈ OrthFr X' → (∀ (τ : X.Ψ), ∃ t : ℝ, t ≠ 0 ∧ X'.Gm.map τ.1 = (t : ℂ) • X.Gm.map τ.1) → ∃ (e : RealGrp X ≃ᵐ RealGrp X') (α : RealGrp X → RealGrp X) (u : RealGrp X), MeasurePreserving e (haarR X) (haarR X') ∧ Measurable α ∧ (∀ t, α (α t) = u⁻¹ * t * u) ∧ ∀ t (τ : X.Ψ) (τ' : X'.Ψ), τ.1 = τ'.1 → mat y' τ' * ((e (α t) τ' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y' τ')⁻¹ = mat y τ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y τ)⁻¹ := by
  first | exact @GlobalTheory.PeterssonFrameChange.frame_change | exact GlobalTheory.PeterssonFrameChange.frame_change | (intros; apply GlobalTheory.PeterssonFrameChange.frame_change <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_framePeriods_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, ∃ Pf, IsPerFr e F M k Pf ∧ (∀ Pf', IsPerFr e F M k Pf' → Pf' = Pf) ∧ (∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (Pf x)) ∧ (∀ a, DifferentiableOn ℂ (fun x => Pf x a) (M.X k).dom) ∧ ∀ P, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ x ∈ (M.X k).dom, Pf x = P := by
  first | exact @GlobalTheory.exists_framePeriods | exact GlobalTheory.exists_framePeriods | (intros; apply GlobalTheory.exists_framePeriods <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.triangularFrame_moves_period_blockTriangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, ∀ b ∈ Bor (M.X k).Ψ r, ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ a, Pf (rmul x b) a = h₀ *ᵥ Pf x a) ∧ (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ ‖h₀.det‖ = ∏ j, ‖h₀ j j‖ ∧ ((∀ τ i, ‖b τ i i‖ = 1) → ‖h₀.det‖ = 1) ∧ ∀ (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t₀ : ℂ), Even n → t₀ ^ 2 * h₀.det = 1 → (∏ j, h₀⁻¹ j j ^ a ((e j).1, (e j).2)) * t₀ ^ n = bchar (laU (unfOf e F M un) a n k) b := by
  first | exact @GlobalTheory.per_bor | exact GlobalTheory.per_bor | (intros; apply GlobalTheory.per_bor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p = 0 ∨ D.q = 0 → SplitLat D := by
  first | exact @GlobalTheory.CompRat.splitLat_of_definite | exact GlobalTheory.CompRat.splitLat_of_definite | (intros; apply GlobalTheory.CompRat.splitLat_of_definite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.PeriodFormPos


open Matrix in
theorem real_pos_of_int_pos {ι : Type} [Fintype ι] (M : ι → ι → ℤ) (hs : ∀ i k, M i k = M k i)
    (hM : ∀ z : ι → ℤ, z ≠ 0 → 0 < ∑ i, ∑ k, z i * z k * M i k) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ k, x i * x k * (M i k : ℝ) := by
  classical
  have hM0 : ∀ z : ι → ℤ, 0 ≤ ∑ i, ∑ k, z i * z k * M i k := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · exact (hM z hz).le
  have hQ : ∀ q : ι → ℚ, (0 : ℝ) ≤ ∑ i, ∑ k, (q i : ℝ) * (q k : ℝ) * (M i k : ℝ) := by
    intro q
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
    choose z hz using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero d.2
    have hz' : ∀ i, (z i : ℝ) = ((d : ℤ) : ℝ) * (q i : ℝ) := by
      intro i
      have h := hz i
      simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at h
      have := congrArg (fun t : ℚ => (t : ℝ)) h
      simpa using this
    have h1 : (0 : ℝ) ≤ ∑ i, ∑ k, (z i : ℝ) * (z k : ℝ) * (M i k : ℝ) := by exact_mod_cast hM0 z
    have h2 : ∑ i, ∑ k, (z i : ℝ) * (z k : ℝ) * (M i k : ℝ) =
        ((d : ℤ) : ℝ) ^ 2 * ∑ i, ∑ k, (q i : ℝ) * (q k : ℝ) * (M i k : ℝ) := by
      simp only [Finset.mul_sum, hz']
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [h2] at h1
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h1
  have hR : ∀ y : ι → ℝ, (0 : ℝ) ≤ ∑ i, ∑ k, y i * y k * (M i k : ℝ) := by
    intro y
    have hdr : DenseRange (Pi.map (fun (_ : ι) (q : ℚ) => (q : ℝ))) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hdr.induction_on y (isClosed_le continuous_const (by fun_prop)) ?_
    intro q
    exact hQ q
  have hform : ∀ y : ι → ℝ, star y ⬝ᵥ ((Matrix.of M).map (Int.cast : ℤ → ℝ)) *ᵥ y =
      ∑ i, ∑ k, y i * y k * (M i k : ℝ) := by
    intro y
    simp only [dotProduct, mulVec, Finset.mul_sum, star_trivial, map_apply, of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hpsd : ((Matrix.of M).map (Int.cast : ℤ → ℝ)).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun y => by rw [hform]; exact hR y⟩
    ext i k
    simp [hs i k]
  have hdet : (Matrix.of M).det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have h1 := hM v hv
    have h2 : ∑ i, ∑ k, v i * v k * M i k = v ⬝ᵥ (Matrix.of M) *ᵥ v := by
      simp only [dotProduct, mulVec, Finset.mul_sum, of_apply]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [h2, hv0] at h1
    simp at h1
  have hpd : ((Matrix.of M).map (Int.cast : ℤ → ℝ)).PosDef := by
    refine hpsd.posDef_iff_det_ne_zero.2 ?_
    have := (Int.castRingHom ℝ).map_det (Matrix.of M)
    rw [RingHom.mapMatrix_apply] at this
    simp only [Int.coe_castRingHom, eq_intCast] at this
    rw [← this]
    exact_mod_cast hdet
  rw [← hform]
  exact hpd.dotProduct_mulVec_pos hx

theorem real_pos_of_discrete {X ι : Type} [AddCommGroup X] [Fintype ι] (b : Module.Basis ι ℤ X)
    (β : X → X → ℝ) (hs : ∀ a a', β a a' = β a' a)
    (hadd : ∀ a a' y, β (a + a') y = β a y + β a' y) (c : ℝ) (hc : 0 < c)
    (hint : ∀ a a', ∃ n : ℤ, β a a' = c * n) (hpos : ∀ a, a ≠ 0 → 0 < β a a)
    (x : ι → ℝ) (hx : x ≠ 0) : 0 < ∑ i, ∑ k, x i * x k * β (b i) (b k) := by
  choose n hn using hint
  have hsum : ∀ (z : ι → ℤ) (y : X), β (∑ i, z i • b i) y = ∑ i, (z i : ℝ) * β (b i) y := by
    intro z y
    have := map_sum (AddMonoidHom.mk' (fun a => β a y) (fun a a' => hadd a a' y))
      (fun i => z i • b i) Finset.univ
    simp only [map_zsmul, AddMonoidHom.mk'_apply, zsmul_eq_mul] at this
    exact this
  have key := real_pos_of_int_pos (fun i k => n (b i) (b k)) (fun i k => by
      have h := hs (b i) (b k)
      rw [hn, hn] at h
      exact_mod_cast mul_left_cancel₀ hc.ne' h) (fun z hz => by
      have hne : ∑ i, z i • b i ≠ 0 := fun h =>
        hz (funext (Fintype.linearIndependent_iff.1 b.linearIndependent z h))
      have h := hpos _ hne
      rw [hsum] at h
      have h2 : ∑ i, (z i : ℝ) * β (b i) (∑ k, z k • b k) =
          c * ((∑ i, ∑ k, z i * z k * n (b i) (b k) : ℤ) : ℝ) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hs, hsum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hs, hn]
        ring
      rw [h2] at h
      exact_mod_cast (mul_pos_iff_of_pos_left hc).1 h) x hx
  have h3 : ∑ i, ∑ k, x i * x k * β (b i) (b k) =
      c * ∑ i, ∑ k, x i * x k * (n (b i) (b k) : ℝ) := by
    simp only [Finset.mul_sum, hn]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h3]
  exact mul_pos hc key

theorem betaAt_pos : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] [IsDiscreteValuationRing R] (Dg : DegData R (maximalIdeal R)) (C : Type) [NormedField C] [IsUltrametricDist C] (f : R →+* C) (p : ℕ), 1 < p → (∀ a ∈ maximalIdeal R, ‖f a‖ < 1) → (∀ a, ‖f a‖ ≤ 1) → (∀ χ r, PsiCoord Dg.toPre χ r → f r ≠ 0) → ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Dg.toPre.X), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * betaAt Dg.toPre f p (b i) (b k) := by
  intro R _ _ _ _ _ Dg C _ _ f p hp hm hle hne
  have hic : IsIntegrallyClosed R := inferInstance
  obtain ⟨hadd, hsq⟩ := GlobalTheory.T.betaAt_add_left_and_diag_eq_two_order R Dg C f p hic hle hne
  have hco := GlobalTheory.T.psiCoord_exists_unique_up_to_unit_local R Dg hic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hunit : ∀ u : Rˣ, ‖f u‖ = 1 := by
    intro u
    have h1 : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul]; simp
    have h2 := hle (u⁻¹ : Rˣ)
    have h3 := hle u
    nlinarith [norm_nonneg (f u), norm_nonneg (f (u⁻¹ : Rˣ))]
  have hv : ∀ χ, ∃ r, PsiCoord Dg.toPre χ r ∧ vPsiAt Dg.toPre f p χ = -Real.logb p ‖f r‖ := by
    intro χ
    obtain ⟨r, hr, -⟩ := (hco χ).1
    have h : ∃ r, PsiCoord Dg.toPre χ r := ⟨r, hr⟩
    exact ⟨h.choose, h.choose_spec, by simp only [vPsiAt, dif_pos h]⟩
  have hvn : ∀ χ, ∃ n : ℕ, vPsiAt Dg.toPre f p χ = (-Real.logb p ‖f ϖ‖) * n := by
    intro χ
    obtain ⟨r, hr, hvr⟩ := hv χ
    have hr0 : r ≠ 0 := fun h => hne χ r hr (by rw [h, map_zero])
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
    refine ⟨n, ?_⟩
    rw [hvr, hu, map_mul, norm_mul, hunit, one_mul, map_pow, norm_pow, Real.logb_pow]
    ring
  have hvpos : ∀ χ, χ ≠ 0 → 0 < vPsiAt Dg.toPre f p χ := by
    intro χ hχ
    obtain ⟨r, hr, hvr⟩ := hv χ
    obtain ⟨r₀, hr₀, -, hmem, -⟩ := (hco χ).1
    obtain ⟨u, hu⟩ := (hco χ).2.1 r₀ r hr₀ hr
    have hrm : r ∈ maximalIdeal R := hu ▸ Ideal.mul_mem_left _ _ (hmem hχ)
    rw [hvr, neg_pos]
    exact Real.logb_neg hp' (norm_pos_iff.2 (hne χ r hr)) (hm r hrm)
  refine ⟨Module.Free.ChooseBasisIndex ℤ Dg.toPre.X, inferInstance,
    Module.Free.chooseBasis ℤ Dg.toPre.X, fun x hx => ?_⟩
  obtain ⟨i, -⟩ := Function.ne_iff.1 hx
  have hc : 0 < -Real.logb p ‖f ϖ‖ := by
    obtain ⟨n, hn⟩ := hvn (Module.Free.chooseBasis ℤ Dg.toPre.X i)
    have h := hvpos _ ((Module.Free.chooseBasis ℤ Dg.toPre.X).ne_zero i)
    rw [hn] at h
    by_contra hneg
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) (Nat.cast_nonneg (α := ℝ) n)
    linarith
  refine real_pos_of_discrete _ _ (betaAt_symm Dg.toPre f p) hadd _ hc (fun a a' => ?_)
    (fun a ha => ?_) x hx
  · obtain ⟨n₁, h₁⟩ := hvn (a + a')
    obtain ⟨n₂, h₂⟩ := hvn a
    obtain ⟨n₃, h₃⟩ := hvn a'
    refine ⟨(n₁ : ℤ) - n₂ - n₃, ?_⟩
    rw [betaAt, h₁, h₂, h₃]
    push_cast
    ring
  · rw [hsq]
    exact mul_pos two_pos (hvpos a ha)

end GlobalTheory.PeriodFormPos
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.EigenBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem dualMap_comp_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  refine RingHom.ext fun x => ?_
  simp [dualMap]

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

theorem isTanAt_baseChange {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_spMap, dualMap_comp_alg, ← spMap_spMap,
      Category.assoc]
  · rw [← Category.assoc, spMap_spMap, fst_comp_dualMap, ← spMap_spMap, Category.assoc, h2]
    simp only [Hom.one_def, Over.comp_left]
    simp

theorem isEigAt_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →ₐ[c.F] T) (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_comp_epsMul, ← spMap_spMap,
    Category.assoc]
  congr 3
  exact ψ.commutes _

end GlobalTheory.Frames.EigenBaseChange


open GlobalTheory.Frames.EigenBaseChange in
theorem GlobalTheory.Frames.eigenbasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (τ : E →+* ℂ) (w : (Sp (DualNumber T) ⟶ Xo.univ.t.G.left)), IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ ψ y τ w hw he
  let e := (Fintype.equivFin ((σ : E →+* ℂ) × Fin (Dw.mult σ))).symm
  have hS := (eigBasis_iff_tanBasis E H Dw l Xo c S y.x y.u _ e y.tan y.eig).1 y.basis
  have hT := tanBasis_baseChange E H Dw l Xo S T ψ.toRingHom y.x _ _ hS
  have key := (eigBasis_iff_tanBasis E H Dw l Xo c T (spMap ψ.toRingHom ≫ y.x)
    (fun σ i => spMap (dualMap ψ.toRingHom) ≫ y.u σ i) _ e
    (fun σ i => EigenBaseChange.isTanAt_baseChange ψ.toRingHom (y.tan σ i))
    (fun σ i => EigenBaseChange.isEigAt_baseChange ψ σ (y.eig σ i))).2 hT
  exact key τ w hw he
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology

namespace GlobalTheory

namespace UniformLift

def toAddHom {V A : Type*} [AddGroup V] [Group A] (e : V → A) (he : ∀ z w, e (z + w) = e z * e w) :
    V →+ Additive A :=
  AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => by rw [he, ofMul_mul]

theorem map_zero_eq_one {V A : Type*} [AddGroup V] [Group A] (e : V → A) (he : ∀ z w, e (z + w) = e z * e w) :
    e 0 = 1 :=
  (toAddHom e he).map_zero

theorem addMonoidHom_eq_of_eventuallyEq_addGroup {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddGroup A]
    {e e' : V →+ A} (h : e =ᶠ[𝓝 0] e') : e = e' := by
  ext v
  have ht : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const v
  obtain ⟨j, hj⟩ := (ht.eventually h).exists
  have hv : v = (2 ^ j : ℕ) • (2⁻¹ : ℝ) ^ j • v := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp
  rw [hv, map_nsmul, map_nsmul, hj]

theorem existsUnique_linearMap_lift_of_germ {V W A : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [AddGroup A] {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {k : V → W} (hd : DifferentiableAt ℂ k 0) (h0 : k 0 = 0)
    (hk : ∀ᶠ z in 𝓝 0, ex' (k z) = ex z) : ∃! L : V →ₗ[ℂ] W, ∀ z, ex' (L z) = ex z := by
  have hadd : Tendsto (fun p : V × V ↦ p.1 + p.2) (𝓝 0) (𝓝 0) := by
    simpa using continuous_add.tendsto (0 : V × V)
  have hL := eventuallyEq_fderiv_of_eventually_add_mod_discrete hker hd h0 <| by
    filter_upwards [hadd.eventually hk, (continuous_fst.tendsto (0 : V × V)).eventually hk,
      (continuous_snd.tendsto (0 : V × V)).eventually hk] with p h1 h2 h3
    rw [AddMonoidHom.mem_ker, sub_sub, map_sub, map_add (f := _), h1, h2, h3, map_add (f := _), sub_self]
  have hL' : ex'.comp (fderiv ℂ k 0 : V →+ W) = ex := addMonoidHom_eq_of_eventuallyEq_addGroup <| by
    filter_upwards [hL, hk] with z h1 h2
    change ex' (fderiv ℂ k 0 z) = ex z
    rw [← h1, h2]
  have hL'' : ∀ z, ex' (fderiv ℂ k 0 z) = ex z := fun z => DFunLike.congr_fun hL' z
  refine ⟨(fderiv ℂ k 0 : V →ₗ[ℂ] W), hL'', fun L h => ?_⟩
  have := realLinear_eq_of_sub_mem_discrete hker (L := L.restrictScalars ℝ)
    (L' := (fderiv ℂ k 0 : V →ₗ[ℂ] W).restrictScalars ℝ) fun x => by
      rw [AddMonoidHom.mem_ker, map_sub]
      exact sub_eq_zero.2 ((h x).trans (hL'' x).symm)
  exact LinearMap.ext fun z => DFunLike.congr_fun this z

theorem fibPt_fst {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G) :
    fibPt G x ≫ pullback.fst _ _ = x.left := pullback.lift_fst _ _ _

theorem fibPt_snd {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G) :
    fibPt G x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

theorem fibPt_injective {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} {x x' : Over.mk y ⟶ G}
    (h : fibPt G x = fibPt G x') : x = x' :=
  Over.OverMorphism.ext (by rw [← fibPt_fst, h, fibPt_fst])

end UniformLift


open UniformLift in
theorem existsUnique_linear_lift_fibre :
    ∀ (X X' : Scheme.{0}) (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (y : Sp ℂ ⟶ X) (y' : Sp ℂ ⟶ X') (g g' : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G')) (ψ : pullback G.hom y ⟶ pullback G'.hom y') (ψp : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G')), Smooth G'.hom → (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) → IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) → ((∀ w, ∃! v : epsPt y' ⟶ G', IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) → DiscreteTopology {z // e' z = 1} → ψ ≫ pullback.snd _ _ = pullback.snd _ _ → (∀ x, fibPt G x ≫ ψ = fibPt G' (ψp x)) → ∃! h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), ∀ z, e' (h z) = ψp (e z) := by
  intro X X' G G' _ _ y y' g g' e e' ψ ψp hsm he he' hol hol' hder hdisc hψ hψp
  have hsm' : Smooth (pullback.snd G'.hom y') := inferInstance
  have hd := isDerivAt0_fibre X' G' y' g' e' _ _ _ (fun z => fibPt G' (e' z)) (IsPullback.of_hasPullback G'.hom y')
    (fun z => ⟨fibPt_fst _ _, fibPt_snd _ _⟩) hol' hder
  obtain ⟨k, k0, hka, hk⟩ := LocalLift.exists_local_lift _ (pullback.snd G'.hom y') g g'
    (fun z => fibPt G (e z) ≫ ψ) (fun z => fibPt G' (e' z)) hsm'
    (fun z => by rw [Category.assoc, hψ, fibPt_snd]) (fun z => fibPt_snd _ _)
    ((T.isHolTo_fibPt_and_comp_fibre X G y g e hol).2 _ ψ) (T.isHolTo_fibPt_and_comp_fibre X' G' y' g' e' hol').1 hd
    (by simp only [hψp, map_zero_eq_one e he, map_zero_eq_one e' he', map_one])
  exact existsUnique_linearMap_lift_of_germ
    (ex := toAddHom (fun z => ψp (e z)) fun z w => by rw [he, map_mul]) (ex' := toAddHom e' he')
    ⟨hdisc⟩ hka.differentiableAt k0 (hk.mono fun z hz => fibPt_injective G' (hz.trans (hψp _)))

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem weilIs_baseChange_of_comm : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] [IsCommMonObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (_ : IsGrpPullback G' G f φ) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S') (n : ℤ) (x' y' : Over.mk t ⟶ G') (x y : Over.mk (t ≫ f) ⟶ G) (c : Rˣ), x.left = x'.left ≫ φ → y.left = y'.left ≫ φ → (Out.WeilIs G' L' n x' y' (unitOn c) ↔ Out.WeilIs G L n x y (unitOn c)) :=
  fun S S' G G' _ _ _ f φ h L L' hL hL' hw _ _ t n x' y' x y c ex ey =>
    weilIs_grpPullback_of_comm' S S' G G' f φ L L' hL hL' h hw (Over.mk t) n x' y' x y (unitOn c) ex ey

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Exist.CubicalExtension

theorem exists_sabMap_of_groupIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (t t' : SAB H (Sp T)) (tK : SAB H (Sp K)) (m : SABMap tK t (spMap (algebraMap T K))) (m' : SABMap tK t' (spMap (algebraMap T K))) (ψ : t.G ≅ t'.G), IsMonHom ψ.hom → m.φ ≫ ψ.hom.left = m'.φ → (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) → ∃ n : SABMap t t' (𝟙 _), n.φ = ψ.hom.left :=
  sabMap_of_iso_of_extendGen GlobalTheory.Exist.extendGen

end GlobalTheory.Exist.CubicalExtension
end

section

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

theorem _root_.GlobalTheory.T.unitFrame_real_unitary_orbit_gram_rigid : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) (X : Comp → Data E r) (G : Type) [Group G] (Gi : Subgroup G) (dict : G → Σ k, Frame (X k).Ψ r) (ar : ∀ k, G → (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (J : ∀ k, (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (x0 : ∀ k, Frame (X k).Ψ r), (∀ k τ, (J k τ).IsHermitian ∧ (J k τ).det ≠ 0) → (∀ k (u : (X k).Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ, (u τ)ᵀ * J k τ * (u τ).map (starRingEnd ℂ) = J k τ) → ∃ h ∈ Gi, ∀ τ, ar k h τ = u τ) → (∀ k, x0 k ∈ (X k).dom ∧ ∃ g, dict g = ⟨k, x0 k⟩) → (∀ g, ∀ h ∈ Gi, ∃ γ ∈ (X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ (rmul (dict g).2 fun τ => ((mat (x0 (dict g).1) τ)⁻¹ * ar (dict g).1 h τ * mat (x0 (dict g).1) τ : Matrix (Fin r) (Fin r) ℂ))⟩) → (∀ g, (dict g).2 ∈ (X (dict g).1).dom) → (∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) → (∀ k (τ : (X k).Ψ), ∃ t : ℝ, t ≠ 0 ∧ (X k).Gm.map τ.1 = (t : ℂ) • J k τ) ∧ ∀ g τ, gram τ.1 (X (dict g).1).Gm (mat (dict g).2 τ) = gram τ.1 (X (dict g).1).Gm (mat (x0 (dict g).1) τ) := by
  first | exact @GlobalTheory.PeterssonRigid.rigid | exact GlobalTheory.PeterssonRigid.rigid | (intros; apply GlobalTheory.PeterssonRigid.rigid <;> assumption)
end
