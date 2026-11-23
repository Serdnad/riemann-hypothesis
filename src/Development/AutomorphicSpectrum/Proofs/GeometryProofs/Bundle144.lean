module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoords
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSmallGenHeightsNonneg
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLeviGen
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem diag_compare_of_triIn : ∀ (V F EC : Type) [CommRing V] [Field F] [Algebra V F] [AddCommGroup EC] [Module F EC] [Module V EC] [IsScalarTower V F EC] (r : ℕ) (u v w : Fin r → EC) (a b : Fin r → F) (d : V), LinearIndependent F u → FinRd.Roots.TriIn u a v → FinRd.Roots.TriIn u b w → (∀ i, b i ≠ 0) → (∀ x ∈ Submodule.span V (Set.range v), d • x ∈ Submodule.span V (Set.range w)) → ∀ i, ∃ c : V, algebraMap V F d * a i = algebraMap V F c * b i := by
  intro V F EC _ _ _ _ _ _ _ r u v w a b d hu hv hw hb hd i
  classical
  obtain ⟨e, he⟩ :=
    (Submodule.mem_span_range_iff_exists_fun V).1 (hd (v i) (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨cv, hcvi, hcv0, hvi⟩ := hv i
  choose cw hcwd hcw0 hw' using hw
  have key : ∀ m, algebraMap V F d * cv m = ∑ j, algebraMap V F (e j) * cw j m := by
    have hL : d • v i = ∑ m, (algebraMap V F d * cv m) • u m := by
      rw [hvi, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul, algebraMap_smul]
    have hR : ∑ j, e j • w j = ∑ m, (∑ j, algebraMap V F (e j) * cw j m) • u m := by
      simp_rw [hw', Finset.smul_sum, Finset.sum_smul, mul_smul, algebraMap_smul]
      exact Finset.sum_comm
    have h1 : ∑ m, (algebraMap V F d * cv m - ∑ j, algebraMap V F (e j) * cw j m) • u m = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, ← hL, ← hR, he, sub_self]
    intro m
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu _ h1 m)
  have hzero : ∀ j, i < j → algebraMap V F (e j) = 0 := by
    by_contra hcon
    push_neg at hcon
    set S := Finset.univ.filter (fun j => i < j ∧ algebraMap V F (e j) ≠ 0) with hSdef
    have hS : S.Nonempty := by
      obtain ⟨j, hj⟩ := hcon
      exact ⟨j, by simp [S, hj]⟩
    obtain ⟨J, hJS, hJmax⟩ : ∃ J ∈ S, ∀ j ∈ S, j ≤ J :=
      ⟨S.max' hS, S.max'_mem hS, fun j hj => S.le_max' j hj⟩
    have hJ : i < J ∧ algebraMap V F (e J) ≠ 0 := by simpa [S] using hJS
    have hmax : ∀ j, J < j → algebraMap V F (e j) = 0 := by
      intro j hj
      by_contra hne
      have hjS : j ∈ S := by simp [S, hne, hJ.1.trans hj]
      exact not_le.2 hj (hJmax j hjS)
    have hk := key J
    rw [hcv0 J hJ.1, mul_zero, Finset.sum_eq_single J, hcwd J] at hk
    · exact hJ.2 ((mul_eq_zero.1 hk.symm).resolve_right (hb J))
    · intro j _ hjJ
      rcases lt_or_gt_of_ne hjJ with h | h
      · rw [hcw0 j J h, mul_zero]
      · rw [hmax j h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ J) h
  refine ⟨e i, ?_⟩
  have hk := key i
  rw [hcvi, Finset.sum_eq_single i, hcwd i] at hk
  · exact hk
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hcw0 j i h, mul_zero]
    · rw [hzero j h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem differentials_basis_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 → ∀ (e : ℕ) (z : Fin e → A) (z' : Fin e → Mdl.invAdj A g), (∀ i, (z' i : Ω) = z i) → LinearIndependent A (fun i => KaehlerDifferential.D ℚ A (z i)) → Submodule.span A (Set.range fun i => KaehlerDifferential.D ℚ A (z i)) = ⊤ → LinearIndependent (Mdl.invAdj A g) (fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) ∧ Submodule.span (Mdl.invAdj A g) (Set.range fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) = ⊤ := by
  intro Ω _ _ A g hg hg0 e z z' hz hli hsp
  have hAB : A ≤ Mdl.invAdj A g := fun x hx =>
    show x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from
      Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
  have hginv : g⁻¹ ∈ Mdl.invAdj A g :=
    show g⁻¹ ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from
      Algebra.subset_adjoin (Set.mem_insert _ _)
  have hden : ∀ x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)), ∃ n : ℕ, x * g ^ n ∈ A := by
    let S : Subalgebra ℚ Ω :=
      { carrier := {x | ∃ n : ℕ, x * g ^ n ∈ A}
        mul_mem' := by
          rintro x y ⟨n, hn⟩ ⟨m, hm⟩
          refine ⟨n + m, ?_⟩
          rw [show x * y * g ^ (n + m) = (x * g ^ n) * (y * g ^ m) by ring]
          exact A.mul_mem hn hm
        one_mem' := ⟨0, by simpa using A.one_mem⟩
        add_mem' := by
          rintro x y ⟨n, hn⟩ ⟨m, hm⟩
          refine ⟨n + m, ?_⟩
          rw [show (x + y) * g ^ (n + m) = (x * g ^ n) * g ^ m + (y * g ^ m) * g ^ n by ring]
          exact A.add_mem (A.mul_mem hn (A.pow_mem hg m)) (A.mul_mem hm (A.pow_mem hg n))
        zero_mem' := ⟨0, by simpa using A.zero_mem⟩
        algebraMap_mem' := fun r => ⟨0, by simpa using A.algebraMap_mem r⟩ }
    have hle : Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) ≤ S := by
      refine Algebra.adjoin_le ?_
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hg0]; exact A.one_mem⟩
      · exact ⟨0, by simpa using hx⟩
    exact fun x hx => hle hx
  letI : Algebra A (Mdl.invAdj A g) := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  have hinc : ∀ a : A, ((algebraMap A (Mdl.invAdj A g) a : Mdl.invAdj A g) : Ω) = a := fun _ => rfl
  haveI : IsScalarTower ℚ A (Mdl.invAdj A g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let g' : A := ⟨g, hg⟩
  haveI : IsLocalization (Submonoid.powers g') (Mdl.invAdj A g) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      have hu : IsUnit (algebraMap A (Mdl.invAdj A g) g') :=
        isUnit_iff_exists_inv.mpr ⟨⟨g⁻¹, hginv⟩, Subtype.ext (by
          show g * g⁻¹ = 1
          exact mul_inv_cancel₀ hg0)⟩
      show IsUnit (algebraMap A (Mdl.invAdj A g) (g' ^ n))
      rw [map_pow]
      exact hu.pow n
    · intro b
      obtain ⟨n, hn⟩ := hden b b.2
      refine ⟨(⟨(b : Ω) * g ^ n, hn⟩, ⟨g' ^ n, n, rfl⟩), ?_⟩
      apply Subtype.ext
      show (b : Ω) * ((g' ^ n : A) : Ω) = (b : Ω) * g ^ n
      simp only [SubmonoidClass.coe_pow]
      rfl
    · intro x y h
      refine ⟨1, ?_⟩
      have hxy : x = y := Subtype.ext (by simpa [hinc] using congrArg Subtype.val h)
      rw [hxy]
  haveI : Algebra.FormallyEtale A (Mdl.invAdj A g) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g')
  have hzz : ∀ i, algebraMap A (Mdl.invAdj A g) (z i) = z' i := fun i =>
    Subtype.ext ((hinc (z i)).trans (hz i).symm)
  have key := GlobalTheory.CompanionTheory.Ar.SncRes.coords_of_formallyEtale (S := ↥(Mdl.invAdj A g)) z hli hsp
  simp only [hzz] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open Algebra GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ratioField_eq_blockFnField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ratioField y c = blockFnField y := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    have hp : y p / y ⟨p.1, c p.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨q.1, c q.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    have key : y p / y q = (y p / y ⟨p.1, c p.1⟩) / (y q / y ⟨q.1, c q.1⟩) := by
      rw [← hpq]
      have h0 := hc p.1
      by_cases hq0 : y q = 0
      · simp [hq0]
      · field_simp
    rw [key]
    exact div_mem hp hq

theorem ringKrullDim_coord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (blockFnField y) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  haveI hP : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime (mConeMap y)
  have hdim := GroundTheory.Heights₂.Heights.IntDomainDim.full (MRing ι ⧸ mCoordIdeal y)
    (algebraMap_injective _ (horizontal y))
  have hne : ∀ k, ∃ i, ratioPtL y c ⟨k, i⟩ ≠ 0 := by
    intro k
    refine ⟨c k, fun h0 => ?_⟩
    have h1 := congrArg Subtype.val h0
    change ratioPt y c ⟨k, c k⟩ = 0 at h1
    simp [ratioPt, hc k] at h1
  have htr := GroundTheory.Heights₂.Heights.ConeTrdeg.full K ι (ratioField y c) (ratioPtL y c)
    (birational y c hc) hne (horizontal _)
  rw [mCoordIdeal_ratioPtL y c hc] at htr
  rw [hdim, htr, ratioField_eq_blockFnField y c hc]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem trdeg_eq_of_le_of_isAlgebraic {L₁ L₂ : IntermediateField ℚ Ω} (h : L₁ ≤ L₂)
    (halg : ∀ t ∈ L₂, IsAlgebraic L₁ t) : Algebra.trdeg ℤ L₂ = Algebra.trdeg ℤ L₁ := by
  letI : Algebra L₁ L₂ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : FaithfulSMul L₁ L₂ :=
    (faithfulSMul_iff_algebraMap_injective L₁ L₂).2 (RingHom.injective _)
  let f : L₂ →ₐ[L₁] Ω :=
    { toRingHom := L₂.val.toRingHom
      commutes' := fun _ => rfl }
  haveI : Algebra.IsAlgebraic L₁ L₂ :=
    ⟨fun x => (isAlgebraic_algHom_iff f Subtype.val_injective).mp (halg x x.2)⟩
  have h0 : trdeg L₁ L₂ = 0 := trdeg_eq_zero
  rw [← trdeg_add_eq (R := ℤ) (S := L₁) (A := L₂), h0, add_zero]

end Dim

theorem isArithVar_of_isAlgebraic_image (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type)
    [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type)
    [Field Ω] [CharZero Ω] (y : (Σ k, ι' k) → Ω) (d : ℕ) (hv : IsBlockMap κ v)
    (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (hz : IsArithVar (mCoordIdeal (y ∘ v)) d)
    (halg : ∀ t ∈ blockFnField y, IsAlgebraic (blockFnField (y ∘ v)) t) : IsArithVar (mCoordIdeal y) d := by
  classical
  obtain ⟨hK, -, -, hdz⟩ := hz
  obtain ⟨hκ, -, hfst, hsurj⟩ := hv
  choose c' hc' using hy
  have hcv : ∀ k : K, ∃ i : ι k, (y ∘ v) ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨⟨k', i⟩, hp⟩ := hsurj ⟨κ k, c' (κ k)⟩ ⟨k, rfl⟩
    have h2 : k' = k := by
      apply hκ
      have h3 := hfst ⟨k', i⟩
      rw [hp] at h3
      exact h3.symm
    subst h2
    exact ⟨i, fun h0 => hc' _ (by rw [← hp]; exact h0)⟩
  choose c hc using hcv
  have e1 := hdz.symm.trans (ringKrullDim_coord (y ∘ v) c hc)
  have hle : blockFnField (y ∘ v) ≤ blockFnField y := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨v p, v q, by rw [hfst, hfst, hpq], rfl⟩
  have htr := trdeg_eq_of_le_of_isAlgebraic hle halg
  unfold IsArithVar IsMultiProjPrime
  refine ⟨⟨κ hK.some⟩, ⟨RingHom.ker_isPrime (mConeMap y), isMultiHomogIdeal y, relevant y c' hc'⟩,
    horizontal y, ?_⟩
  rw [ringKrullDim_coord y c' hc', htr]
  generalize Algebra.trdeg ℤ ↥(blockFnField (y ∘ v)) = T at e1 ⊢
  simp only [map_add (f := _), map_natCast] at e1 ⊢
  generalize Cardinal.toENat T = e at e1 ⊢
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    have h5 : ((d + Fintype.card K : ℕ) : ℕ∞) = ⊤ := by exact_mod_cast e1
    exact ENat.natCast_ne_top _ h5
  | coe m =>
    norm_cast at e1 ⊢
    omega

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FS

open MvPolynomial Filter Topology
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.FubiniStudyLeviForm

theorem log_rho_eq_phi (I : Type) [Fintype I] :
    (fun z : I → ℂ => Real.log ((fsMetric («ι» := I)).ρ z)) = FubiniLevi.phi := by
  funext z
  change Real.log ‖WithLp.toLp 2 z‖ = _
  rw [EuclideanSpace.norm_eq, Real.log_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [FubiniLevi.phi, FubiniLevi.sqSum, PiLp.toLp_apply]
  ring

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem exists_block_ne {z w : (Σ k, J k) → ℂ} (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    ∃ k, ∀ c : ℂ, (fun i => w ⟨k, i⟩) ≠ fun i => c * z ⟨k, i⟩ := by
  by_contra h
  push_neg at h
  choose c hc using h
  exact hw c (funext fun p => by
    obtain ⟨k, i⟩ := p
    exact congrFun (hc k) i)

theorem levi_fsMulti_pos {z w : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    0 < leviForm (fun y => Real.log ((fsMulti J).h y)) z w := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_block_ne hw
  set F : K → ((Σ k, J k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric («ι» := J k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsMulti J).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hpos : ∀ k, 0 < (fsMetric («ι» := J k)).ρ (fun i => y ⟨k, i⟩) := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact (fsMetric («ι» := J k)).pos _ fun h0 => hi (congrFun h0 i)
    simp only [fsMulti, HermLine.ofMetrics, zpow_one, hF]
    exact Real.log_prod fun k _ => (hpos k).ne'
  have hk0 : ∀ k, (fun i => z ⟨k, i⟩) ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h0 i)
  have hφ : ∀ k, ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric («ι» := J k)).ρ u)) (blockProj J k z) := by
    intro k
    have hne : blockProj J k z ≠ 0 := hk0 k
    have hsm := HilbertSamuel.ProjLine.isSmoothMetric_fs (J := J k)
    have hρ : ContDiffAt ℝ 2 (fsMetric («ι» := J k)).ρ (blockProj J k z) :=
      (hsm.contDiffAt (isOpen_ne.mem_nhds hne)).of_le (WithTop.coe_le_coe.2 le_top)
    exact hρ.log ((fsMetric («ι» := J k)).pos _ hne).ne'
  have hFk : ∀ k, F k = (fun u => Real.log ((fsMetric («ι» := J k)).ρ u)) ∘ blockProj J k := fun k => rfl
  have hC : ∀ k, ContDiffAt ℝ 2 (F k) z := fun k =>
    hFk k ▸ (hφ k).comp z ((blockProj J k).restrictScalars ℝ).contDiff.contDiffAt
  have hL : ∀ k v, ReciprocityTheory.AnForm.levi (F k) z v = leviForm (fun u => Real.log ((fsMetric («ι» := J k)).ρ u))
      (fun i => z ⟨k, i⟩) (fun i => v ⟨k, i⟩) := fun k v => by
    rw [hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj J k).analyticAt z) (hφ k), (blockProj J k).fderiv]
    rfl
  have hnn : ∀ k v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v := fun k v => by
    rw [hL]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (hk0 k) _
  have hpos : 0 < ReciprocityTheory.AnForm.levi (F k₀) z w := by
    rw [hL, log_rho_eq_phi]
    exact FubiniLevi.levi_phi_pos_of_ne (hz k₀) hk₀
  have hsum := levi_sum_nonneg F (fun k => hC k) hnn w (Finset.univ.erase k₀)
  change 0 < ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev]
  have hsplit : (fun y => ∑ k ∈ Finset.univ, F k y) =
      fun y => F k₀ y + 1 * ∑ k ∈ Finset.univ.erase k₀, F k y := by
    funext y
    rw [_root_.one_mul]
    exact (Finset.add_sum_erase Finset.univ (fun k => F k y) (Finset.mem_univ k₀)).symm
  rw [hsplit, ReciprocityTheory.AnForm.levi_add_smul 1 (hC k₀) hsum.1 w]
  linarith [hsum.2]

theorem isPositiveRel_fsMulti (P : Ideal (MRing J)) : IsPositiveRel P (fsMulti J) :=
  ⟨FsLineSmooth.proof K J, fun _ hz _ _ hw => levi_fsMulti_pos hz.1 hw⟩

theorem isConjInvariantH_fsMulti : IsConjInvariantH (fsMulti J) := by
  intro z
  simp [fsMulti, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

def chartForm (c : ∀ k, J k) : MRing J := ∏ k, X ⟨k, c k⟩

theorem isMultiHomog_chartForm (c : ∀ k, J k) :
    IsMultiHomog (chartForm c) fun k => ((fsMulti J).a k).toNat := by
  classical
  have h := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c (fun _ : K => 1)
  simpa [chartForm, fsMulti, HermLine.ofMetrics, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow] using h

theorem chartForm_le (c : ∀ k, J k) (z : (Σ k, J k) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) (chartForm c))‖ ≤ (fsMulti J).h z := by
  have e : eval z (map (Int.castRingHom ℂ) (chartForm c)) = ∏ k, z ⟨k, c k⟩ := by
    simp [chartForm, map_prod]
  rw [e, norm_prod]
  simp only [fsMulti, HermLine.ofMetrics, zpow_one]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
  exact PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) (c k)

theorem exists_chartForm_notMem {Q : Ideal (MRing J)} (hQ : IsMultiProjPrime Q) :
    ∃ c, chartForm c ∉ Q := by
  choose c hc using hQ.2.2
  refine ⟨c, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := (hQ.1.prod_mem_iff).1 h
  exact hc k hk

theorem heights_fsMulti {II : IntersectionSystem} (hII : IsIntersectionSystem II) {W : Ideal (MRing J)}
    (hW : IsArithVar W 1) : 0 ≤ II K J W 1 ![fsMulti J] := by
  classical
  let e := Fintype.equivFin (∀ k, J k)
  refine HilbertSamuel.SmallGenHeightsNonneg.proof K J ⊥ (fsMulti J) II _ (fun j => chartForm (e.symm j)) hII
    (FsLineSmooth.proof K J) (fun k => ?_) (fun j => isMultiHomog_chartForm _) (fun Q hQ _ => ?_)
    (fun j z _ => chartForm_le _ z) W hW bot_le
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · obtain ⟨c, hc⟩ := exists_chartForm_notMem hQ
    exact ⟨e c, by simpa using hc⟩

end GlobalTheory.CompanionTheory.Ar.FS

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem exists_fubiniStudy_line :
    ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)),
      IsFullIntersectionSystem II → ∃ A : HermLine J, (∀ k, A.a k = 1) ∧ IsPositiveRel P A ∧ IsConjInvariantH A ∧
        ∀ W : Ideal (MRing J), IsArithVar W 1 → 0 ≤ II K J W 1 ![A] :=
  fun _ _ _ _ _ P hII => ⟨GroundTheory.Heights₂.Heights.fsMulti _, fun _ => rfl, FS.isPositiveRel_fsMulti P,
    FS.isConjInvariantH_fsMulti, fun _ hW => FS.heights_fsMulti hII.1 hW⟩

end GlobalTheory.CompanionTheory.Ar
end
end
