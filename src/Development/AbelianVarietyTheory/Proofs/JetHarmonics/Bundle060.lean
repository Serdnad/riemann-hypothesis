module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle053
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle051
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtTie

section Move
open GlobalTheory.FieldBaseChange
variable {X' X X₁ X₂ Y Y₁ : Scheme.{0}} {L' : LB X'}

def isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) : LB.Iso (L'.pull (𝟙 X')) (L.pull m) :=
  ⟨fun p => res (fun _ hy => ⟨hy.1, mem_pull.1 hy.2⟩ :
    (L.pull m).U p.1 ⊓ (L'.pull (𝟙 X')).U p.2 ≤ (L.pull m).U p.1 ⊓ L'.U (p.2 PUnit.unit)) (w.s (p.1, p.2 PUnit.unit))⟩

theorem isoVal_isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z)
    (j : L.ι) (k : L'.ι) (hj : m (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    isoVal (isoFromPullId w) r z j k = gv w r z (fun _ => j) k := by
  have hm : r z ∈ (L.pull m).U (fun _ => j) ⊓ (L'.pull (𝟙 X')).U (fun _ => k) := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  show gm r z _ (res _ (w.s (fun _ => j, k))) = _
  exact gm_res r z _ hm _

theorem isoFromPullId_isGen {L : LB X} {m : X' ⟶ X} {w : LB.Iso L' (L.pull m)} (hw : w.IsGen) :
    (isoFromPullId w).IsGen := by
  refine (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_
  have ik : r z ∈ L'.U (k PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk
  have ik' : r z ∈ L'.U (k' PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk'
  have a := isoVal_isoFromPullId w r z j (k PUnit.unit) hj ik
  have a' := isoVal_isoFromPullId w r z j' (k' PUnit.unit) hj' ik'
  have b := (isGen_iff w).1 hw Z r z j j' _ _ hj hj' ik ik'
  have c := (gm_pull_g L' (𝟙 X') r z k k' hk hk').trans
    (congrArg (fun f : Z ⟶ X' => gm f z _ (L'.g (k PUnit.unit) (k' PUnit.unit))) (Category.comp_id r))
  refine a.trans (b.trans ?_)
  exact congrArg₂ (fun s t => _ * s⁻¹ * t) c.symm a'.symm

end Move

section Comparison₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : letI := io.toAlgebra; FrPt Xo c T.Fr}
  {I : IntData Xo c T io y} {F : Type} [Field F] [Algebra T.Fr F] {xF : Sp F ⟶ Xo.X}

variable (I) (P : PELUnif (maximalIdeal T.V) I.G)

end Comparison₂

end GlobalTheory.PtTie
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensLen

open Formalism.HermitianLatticeCounting.ExpansionTerms (majorantDistance)

section general

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem infDist_add_mem (S : Submodule ℂ V) (x w : V) (hw : w ∈ S) :
    Metric.infDist (x + w) (S : Set V) = Metric.infDist x (S : Set V) := by
  have h := Metric.infDist_image (isometry_add_right w) (x := x) (t := (S : Set V))
  have h2 : (fun y => y + w) '' (S : Set V) = S := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact S.add_mem hy hw
    · intro hv
      exact ⟨v - w, S.sub_mem hv hw, by simp⟩
  rwa [h2] at h

theorem len_eq_of_unitriangular {n : ℕ} (y y' : Fin n → V) (U : Matrix (Fin n) (Fin n) ℂ)
    (h0 : ∀ c a, a < c → U c a = 0) (h1 : ∀ c, U c c = 1) (h : ∀ a, y a = ∑ c, U c a • y' c) (a : Fin n) :
    majorantDistance y a = majorantDistance y' a := by
  have hrest : ∀ (S : Submodule ℂ V) (b : Fin n), (∀ c, c < b → y' c ∈ S) →
      ∑ c ∈ univ.erase b, U c b • y' c ∈ S := by
    intro S b hS
    refine S.sum_mem fun c hc => ?_
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · exact S.smul_mem _ (hS c hcb)
    · exact absurd hcb (Finset.ne_of_mem_erase hc)
    · rw [h0 c b hcb, zero_smul]; exact S.zero_mem
  have hy : ∀ b, y b = y' b + ∑ c ∈ univ.erase b, U c b • y' c := by
    intro b
    rw [h b, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), h1, one_smul]
  have hspan : Submodule.span ℂ (y '' {b | b < a}) = Submodule.span ℂ (y' '' {b | b < a}) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      rw [hy b]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨b, hb, rfl⟩)
        (hrest _ b fun c hc => Submodule.subset_span ⟨c, lt_trans hc hb, rfl⟩)
    · rw [Submodule.span_le]
      have key : ∀ b, b < a → y' b ∈ Submodule.span ℂ (y '' {b | b < a}) := by
        intro b
        induction b using WellFoundedLT.induction with
        | ind b ih =>
          intro hb
          rw [eq_sub_of_add_eq (hy b).symm]
          exact Submodule.sub_mem _ (Submodule.subset_span ⟨b, hb, rfl⟩)
            (hrest _ b fun c hc => ih c hc (lt_trans hc hb))
      rintro _ ⟨b, hb, rfl⟩
      exact key b hb
  unfold majorantDistance
  rw [hspan, hy a]
  exact infDist_add_mem _ _ _ (hrest _ a fun c hc => Submodule.subset_span ⟨c, hc, rfl⟩)

theorem len_pos {n : ℕ} (y : Fin n → V) (hy : LinearIndependent ℂ y) (a : Fin n) : 0 < majorantDistance y a := by
  unfold majorantDistance
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (y '' {b | b < a})) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  refine ((Submodule.closed_of_finiteDimensional _).notMem_iff_infDist_pos ⟨0, Submodule.zero_mem _⟩).1 ?_
  exact hy.notMem_span_image (by simp)

theorem len_zero {n : ℕ} (y : Fin (n + 1) → V) : majorantDistance y 0 = ‖y 0‖ := by
  unfold majorantDistance
  have : y '' {b | b < 0} = ∅ := by simp
  rw [this, Submodule.span_empty, Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]

end general

theorem cmp_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ wedge f = wedge (fun b => g *ᵥ f b) := by
  funext I
  have h := Formalism.HermitianLatticeCounting.P.ge_cauchyBinet (g.submatrix (I.1.orderEmbOfFin I.2) id)
    (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)
  refine Eq.trans ?_ (h.symm.trans ?_)
  · simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [mul_comm]
    rfl
  · rfl

theorem sum_norm_wedge {n l : ℕ} (f : Fin l → Fin n → ℂ) :
    ∑ J, ‖wedge f J‖ ^ 2 =
      ∏ a, majorantDistance (fun b => (WithLp.toLp 2 (f b) : EuclideanSpace ℂ (Fin n))) a ^ 2 := by
  have h := Formalism.HermitianLatticeCounting.P.gram_matrix_product_formula (EuclideanSpace ℂ (Fin n)) l (fun b => WithLp.toLp 2 (f b))
  have h2 := Formalism.HermitianLatticeCounting.P.ge_cauchyBinet (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)ᴴ
    (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)
  have h3 : (Matrix.of fun (i : Fin n) (b : Fin l) => f b i)ᴴ *
      (Matrix.of fun (i : Fin n) (b : Fin l) => f b i) =
      Matrix.of fun a b => inner ℂ (WithLp.toLp 2 (f a) : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 (f b)) := by
    ext a b
    simp [Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  rw [h3, h] at h2
  apply Complex.ofReal_injective
  rw [h2]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, Complex.mul_conj']
  rfl

theorem sum_norm_sq_eq {n : ℕ} (v : Fin n → ℂ) : ((∑ c, ‖v c‖ ^ 2 : ℝ) : ℂ) = v ⬝ᵥ star v := by
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj']

theorem sum_norm_dual {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (hg : gᴴ * H * g = H) (hu : IsUnit g.det) (f : Fin n → ℂ) :
    ∑ c, ‖(dualM g⁻¹ *ᵥ (fun c => Formalism.QuantumDeterminants.herm H (Pi.single c 1) f)) c‖ ^ 2 = ∑ c, ‖(g⁻¹ *ᵥ f) c‖ ^ 2 := by
  have h1 : (fun c => Formalism.QuantumDeterminants.herm H (Pi.single c 1) f) = star f ᵥ* H := by
    funext c
    simp [Formalism.QuantumDeterminants.herm, vecMul, dotProduct]
  have h2 : H * g = (g⁻¹)ᴴ * H := by
    conv_rhs => rw [← hg]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hu,
      conjTranspose_one, Matrix.one_mul]
  have h3 : dualM g⁻¹ *ᵥ (star f ᵥ* H) = star (H *ᵥ (g⁻¹ *ᵥ f)) := by
    rw [dualM, nonsing_inv_nonsing_inv _ hu, mulVec_transpose, vecMul_vecMul, h2, star_mulVec, star_mulVec,
      vecMul_vecMul, hH]
  rw [h1, h3]
  apply Complex.ofReal_injective
  rw [sum_norm_sq_eq, sum_norm_sq_eq, star_star, star_mulVec, hH, dotProduct_mulVec, vecMul_vecMul, hHH,
    vecMul_one, dotProduct_comm]

theorem fvec_indep (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) : LinearIndependent ℂ (Formalism.QuantumDeterminants.fvec k r z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm] at hT
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz0
  have hir : r ≤ i.val := by
    by_contra hlt
    exact hi (hz i (Or.inl (by omega)))
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  by_cases ha : a.val < r
  · have := congrFun hc ⟨a.val, by omega⟩
    rw [Finset.sum_apply, Finset.sum_eq_single a] at this
    · rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_lt z hz _ _ ha] at this
      simpa using this
    · intro b _ hb
      rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_lt z hz _ _ ha, if_neg (fun h => hb (Fin.ext h)), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have := congrFun hc i
    rw [Finset.sum_apply, Finset.sum_eq_single a] at this
    · rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_ge z _ _ hir, if_pos (by omega)] at this
      exact (mul_eq_zero.1 this).resolve_right hi
    · intro b _ hb
      rw [Pi.smul_apply, Formalism.QuantumDeterminants.fvec_apply_ge z _ _ hir,
        if_neg (fun h => hb (Fin.ext (by omega))), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem isUnit_det_of_unitary {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hHH : H * H = 1)
    (hg : gᴴ * H * g = H) : IsUnit g.det := by
  have h : (H * (gᴴ * H)) * g = 1 := by rw [Matrix.mul_assoc, hg, hHH]
  exact Matrix.isUnit_det_of_left_inverse h

theorem lengths : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∀ g ∈ GG k r, (∑ J, ‖(cmp (r + 1) g⁻¹ *ᵥ (wedge (Formalism.QuantumDeterminants.fvec k r z))) J‖ ^ 2 = ∏ a, lenA k r z g a ^ 2) ∧ (∑ c, ‖(dualM g⁻¹ *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0))) c‖ ^ 2 = lenA k r z g 0 ^ 2) ∧ (∀ a, 0 < lenA k r z g a) ∧ ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ a, lenA k r z (s * g) a = lenA k r z g a := by
  intro k r z hz hT g hg
  obtain ⟨hH, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hu : IsUnit g.det := isUnit_det_of_unitary hHH hg
  have hl : ∀ g a, lenA k r z g a = majorantDistance (fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a := fun _ _ => rfl
  refine ⟨?_, ?_, fun a => ?_, fun s hs a => ?_⟩
  · rw [cmp_mulVec_wedge, sum_norm_wedge]
    rfl
  · rw [hl, len_zero, EuclideanSpace.norm_sq_eq]
    exact sum_norm_dual _ g hH hHH hg hu _
  · rw [hl]
    refine len_pos _ ?_ a
    have hinj : Function.Injective (g⁻¹).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det g hu))
    have h1 := (fvec_indep k r z hz hT).map' (Matrix.mulVecLin g⁻¹) (LinearMap.ker_eq_bot.2 hinj)
    exact h1.map' (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
  · obtain ⟨U, h0, h1, hF⟩ := Formalism.QuantumDeterminants.S_F hz hs
    have hsu : IsUnit s.det := isUnit_det_of_unitary hHH (Formalism.QuantumDeterminants.Sset_UH hs)
    rw [hl, hl]
    symm
    refine len_eq_of_unitriangular _ _ U h0 h1 (fun b => ?_) a
    have hcol : s *ᵥ Formalism.QuantumDeterminants.fvec k r z b = ∑ c, U c b • Formalism.QuantumDeterminants.fvec k r z c := by
      funext i
      have := congrFun (congrFun hF i) b
      simpa [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, mulVec, dotProduct, mul_comm] using this
    have h2 : g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b = (s * g)⁻¹ *ᵥ (s *ᵥ Formalism.QuantumDeterminants.fvec k r z b) := by
      rw [mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ hsu, Matrix.mul_one]
    rw [h2, hcol, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, WithLp.toLp_sum, WithLp.toLp_smul]

end GlobalTheory.TensLen
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quantumMinor_columnSteps_partial (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp]
    [Module ℂ Wp] (k r : ℕ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp)
    (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ) (hE : Formalism.REAL.GlRel E)
    (hp : ∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) →
      (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ =
        (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ)
          else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ
          else 0))
    (w : Fin k → Fin (2 * r + k + 1)) (hw : ∀ i, (w i).val = r + i.val) (j : ℕ) :
    j ≤ r → ∀ (t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)), t = k + j →
      (∀ i, (a i).val = r + i.val) →
      (∀ i, (b i).val = if i.val < k then r + i.val else r + i.val + 1) →
      ∃ c : ℂ, ‖c‖ = (if j = 0 then 1 else τ) ∧ ∀ u v,
        l (Formalism.REAL.qminor E a b u v) = c • l (Formalism.REAL.qminor E w w (u - (j : ℂ)) v) := by
  induction j with
  | zero =>
    intro _ t a b ht ha hb
    obtain rfl : t = k := ht
    have h1 : a = w := funext fun i => Fin.ext (by rw [ha, hw])
    have h2 : b = w := funext fun i => Fin.ext (by rw [hb, hw, if_pos i.isLt])
    refine ⟨1, by simp, fun u v => ?_⟩
    simp [h1, h2]
  | succ j ih =>
    intro hj t a b ht ha hb
    obtain rfl : t = (k + j) + 1 := ht
    obtain ⟨c, hc, hcu⟩ := ih (by omega) (k + j) (fun i => a i.castSucc) (fun i => b i.castSucc) rfl
      (fun i => by simpa using ha i.castSucc) (fun i => by simpa using hb i.castSucc)
    have hai : Function.Injective a := fun x y h => by
      have h' := congrArg Fin.val h
      rw [ha, ha] at h'
      exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y h => by
      have h' := congrArg Fin.val h
      rw [hb, hb] at h'
      exact Fin.ext (by split_ifs at h' <;> omega)
    have hr : ∀ f : Fin (k + j + 1) → Fin (2 * r + k + 1),
        Set.range f = insert (f (Fin.last _)) (Set.range fun i : Fin (k + j) => f i.castSucc) := by
      intro f
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Fin.exists_fin_succ', eq_comm, or_comm]
    have hn : ∀ f : Fin (k + j + 1) → Fin (2 * r + k + 1), Function.Injective f →
        f (Fin.last _) ∉ Set.range fun i : Fin (k + j) => f i.castSucc := by
      rintro f hf ⟨i, hi⟩
      exact (Fin.castSucc_lt_last i).ne (hf hi)
    have hal : (a (Fin.last _)).val = r + (k + j) := by rw [ha]; simp
    have hbl : (b (Fin.last _)).val = r + (k + j) + 1 := by rw [hb]; simp
    have hlt : ∀ i, a i < b (Fin.last _) := fun i => by
      have := i.isLt
      rw [Fin.lt_def, ha, hbl]; omega
    have hq := fun i => hp (a i) (b (Fin.last _)) (hlt i) (by rw [hbl]; omega)
    obtain ⟨e, he, heu⟩ := GlobalTheory.T.quantumMinor_column_expansion_under_linearMap M Wp _ (k + j) E l a b (fun i => a i.castSucc)
      (fun i => b i.castSucc) (a (Fin.last _)) (b (Fin.last _))
      (p (a (Fin.last _)) (b (Fin.last _))) hE hai hbi
      (hai.comp (Fin.castSucc_injective _)) (hbi.comp (Fin.castSucc_injective _))
      (hr a) (hn a hai) (hr b) (hn b hbi)
      (by rintro ⟨i, hi⟩; exact (hlt i).ne hi)
      (by
        intro i v
        rw [(hq i).1 v]
        split_ifs with h
        · rw [h]
        · have h0 := (hq i).2
          have hi : (a i).val ≠ r + (k + j) := fun h' => h (Fin.ext (by rw [h', hal]))
          have hi2 := ha i
          rw [hbl, if_neg (by omega), if_neg (by omega)] at h0
          rw [norm_eq_zero.1 h0])
    refine ⟨e * p (a (Fin.last _)) (b (Fin.last _)) * c, ?_, fun u v => ?_⟩
    · have h0 := (hq (Fin.last _)).2
      rw [hal, hbl] at h0
      rw [norm_mul, norm_mul, he, hc, h0]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
        intro h; omega
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
        simp
    · rw [heu, hcu, smul_smul]
      congr 4
      push_cast
      ring

theorem qminor_column_chain : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) = c • l (Formalism.REAL.qminor E (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (u - (r : ℂ)) v) := by
  intro M Wp _ _ _ _ k r E l p τ _ hE hp hr
  have h := quantumMinor_columnSteps_partial M Wp k r E l p τ hE hp
    (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (fun _ => rfl) r le_rfl (r + k)
    (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
    (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
      by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) (Nat.add_comm _ _) (fun _ => rfl) (fun _ => rfl)
  rw [if_neg (by omega)] at h
  exact h

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem qminor_row_step_under_functional : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → a0 ∉ Set.range b → (∀ j v, l (E a0 (b j) v) = (if b j = b0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' u v) := by
  intro M Wp _ _ _ _ n t E l a b a' b' a0 b0 p hE ha hb ha' hb' hra ha0 hrb hb0 hab hl
  have hA : Function.Injective (Fin.cons a0 a' : Fin (t + 1) → Fin n) :=
    Fin.cons_injective_iff.2 ⟨ha0, ha'⟩
  have hB : Function.Injective (Fin.cons b0 b' : Fin (t + 1) → Fin n) :=
    Fin.cons_injective_iff.2 ⟨hb0, hb'⟩
  have hrB : Set.range b = Set.range (Fin.cons b0 b' : Fin (t + 1) → Fin n) := by
    rw [Fin.range_cons]; exact hrb
  obtain ⟨e, he, hq⟩ := GlobalTheory.T.quantumMinor_eq_unit_smul_of_range_eq (Module.End ℂ M) n (t + 1) E a (Fin.cons a0 a') b (Fin.cons b0 b') hE
    ha hA hb hB (by rw [Fin.range_cons]; exact hra) hrB
  refine ⟨e, he, fun u v => ?_⟩
  have key : ∀ (j : Fin (t + 1)) (w : ℂ) (x : M),
      l (Formalism.REAL.Tm E w a0 ((Fin.cons b0 b' : Fin (t + 1) → Fin n) j) x) = (if j = 0 then p else 0) • l x := by
    intro j w x
    have hmem : (Fin.cons b0 b' : Fin (t + 1) → Fin n) j ∈ Set.range b := by
      rw [hrB]; exact ⟨j, rfl⟩
    have hne : a0 ≠ (Fin.cons b0 b' : Fin (t + 1) → Fin n) j := fun h => hab (h ▸ hmem)
    obtain ⟨k, hk⟩ := hmem
    have hiff : b k = b0 ↔ j = 0 := by
      rw [hk]
      exact ⟨fun h => hB (by simpa using h), fun h => by subst h; rfl⟩
    unfold Formalism.REAL.Tm
    rw [if_neg hne, zero_add, ← hk, hl k x]
    simp only [hiff]

  rw [hq u, quantum_minor_row_expansion.1 (Module.End ℂ M) n t E hE, LinearMap.smul_apply, map_smul, LinearMap.sum_apply,
  map_sum, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero, mul_smul]
  · congr 1
    have h0 := key 0
    simp only [Fin.cons_zero, if_true] at h0
    simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Module.End.mul_apply, Fin.cons_zero, h0,
      Fin.succAbove_zero]
    rfl
  · intro j _
    rw [← zsmul_eq_mul, LinearMap.smul_apply, map_zsmul, Module.End.mul_apply, Fin.cons_zero, key,
      if_neg (Fin.succ_ne_zero j), zero_smul, smul_zero]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_boxFamily_multilinear_map : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  intro hG R _ _ j D D' pD F _ _ k
  have hexists := GlobalTheory.BoxFamily.exists_isBoxFam hG R j D D' pD F k
  choose bx hbx using hexists
  refine ⟨⟨bx, fun s i a b => GlobalTheory.BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
    fun s i c a => GlobalTheory.BoxLinear.box_smul pD (hbx _) (hbx _)⟩,
    fun s S => ⟨fun h => GlobalTheory.BoxLinear.box_unique pD h (hbx s), ?_⟩⟩
  rintro rfl
  exact hbx s
end
