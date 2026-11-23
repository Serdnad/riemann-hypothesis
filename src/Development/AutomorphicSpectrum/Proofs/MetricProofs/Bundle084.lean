module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETrunc
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETruncMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEWeight
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NzCase

theorem nz_eq_nzOf_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) (r : ℕ) (y : Fin r → Λ), IsCMFam σ → IsIsoSub R.form I → (∀ a, y a ∈ I) → LinearIndependent (𝓞 E) y → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → R.nz σ I = R.nzOf σ I y ∧ 0 < R.nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ I r y hσ hI hy hli hidx
  by_cases hbot : I = ⊥
  · subst hbot
    have hy0 : ∀ a, y a = 0 := fun a => by simpa using hy a
    have hr : r = 0 := by
      by_contra h
      exact hli.ne_zero (⟨0, Nat.pos_of_ne_zero h⟩ : Fin r) (hy0 _)
    subst hr
    have hno : ¬ ∃ r v, IsNzFamily (⊥ : Submodule (𝓞 E) Λ) r v := by
      rintro ⟨ρ, v, h1, hv, hl, -⟩
      exact hl.ne_zero (⟨0, h1⟩ : Fin ρ) (by simpa using hv ⟨0, h1⟩)
    have hnz : R.nz σ (⊥ : Submodule (𝓞 E) Λ) = 1 := by
      simp only [RiemLat.nz]
      exact dif_neg hno
    have hof : R.nzOf σ (⊥ : Submodule (𝓞 E) Λ) y = 1 := by
      have hs : Submodule.span (𝓞 E) (Set.range y) = ⊥ := by
        simp [Set.range_eq_empty]
      simp [RiemLat.nzOf, hs]
    rw [hnz, hof]
    exact ⟨rfl, one_pos⟩
  · have hr : 1 ≤ r := by
      by_contra h
      have hr0 : r = 0 := by omega
      subst hr0
      have hs : Submodule.span (𝓞 E) (Set.range y) = ⊥ := by
        simp [Set.range_eq_empty]
      have hb : (⊥ : Submodule (𝓞 E) Λ).toAddSubgroup = ⊥ := rfl
      rw [hs, hb, AddSubgroup.relIndex_bot_left] at hidx
      haveI : Finite I.toAddSubgroup := Nat.finite_of_card_ne_zero hidx
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      haveI := R.free
      have hfin : IsOfFinAddOrder (⟨x, hx⟩ : I.toAddSubgroup) := isOfFinAddOrder_of_finite _
      obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hfin
      have hnx' : n • x = 0 := congrArg Subtype.val hnx
      have hzx : (n : ℤ) • x = 0 := by rw [natCast_zsmul]; exact hnx'
      exact hx0 ((smul_eq_zero.1 hzx).resolve_left (by exact_mod_cast hn.ne'))
    have hfam : IsNzFamily I r y := ⟨hr, hy, hli, hidx⟩
    have h := (GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ R σ I hσ hI hbot).2 r y hfam
    exact ⟨h.1, h.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.NzCase
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S) (A : Matrix (Fin N) (Fin N) R)
    (I J : Finset (Fin N)) : minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · exact (map_zero f).symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem regAt_neg {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    RegAt x (mCoordIdeal z) (-s) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  refine ⟨d, -g, h, fun m hm k => hg m (by rwa [support_neg] at hm) k, hh, hn, ?_⟩
  rw [map_neg, heq, neg_mul]

def regRing (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : Subring Ω where
  carrier := {s | RegAt x (mCoordIdeal z) s}
  mul_mem' := ValRing.regAt_mul
  one_mem' := ValRing.regAt_one x z
  add_mem' := ValRing.regAt_add
  zero_mem' := ValRing.regAt_zero x z
  neg_mem' := regAt_neg

def regVal (x : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) : regRing x z →+* ℂ where
  toFun s := valAt x s z
  map_one' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1
  map_zero' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.1
  map_mul' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.1
  map_add' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.2

def valMat {N : ℕ} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (A : Matrix (Fin N) (Fin N) Ω) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a b => valAt x (A a b) z

variable {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem reg_sum (hz : z ∈ mcPts (mCoordIdeal x)) {σ : Type} (s : Finset σ) (f : σ → Ω)
    (hf : ∀ i ∈ s, RegAt x (mCoordIdeal z) (f i)) :
    RegAt x (mCoordIdeal z) (∑ i ∈ s, f i) ∧ valAt x (∑ i ∈ s, f i) z = ∑ i ∈ s, valAt x (f i) z := by
  revert hf
  refine Finset.induction_on s ?_ (fun a s ha ih hf => ?_)
  · intro _
    simp only [Finset.sum_empty]
    exact ⟨(ValRing.regAt_valAt_ring K ι Ω x z hz).1, (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.1⟩
  · rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨-, hadd, -, hval⟩ := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 _ _ hfa h1
    exact ⟨hadd, by rw [hval, h2]⟩

theorem reg_mul (hz : z ∈ mcPts (mCoordIdeal x)) {s t : Ω} (hs : RegAt x (mCoordIdeal z) s)
    (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z := by
  obtain ⟨hm, -, hv, -⟩ := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t hs ht
  exact ⟨hm, hv⟩

theorem regMat_mul {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A B : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (hB : ∀ a b, RegAt x (mCoordIdeal z) (B a b)) :
    (∀ a b, RegAt x (mCoordIdeal z) ((A * B) a b)) ∧ valMat x z (A * B) = valMat x z A * valMat x z B := by
  have key : ∀ a b, RegAt x (mCoordIdeal z) ((A * B) a b) ∧
      valAt x ((A * B) a b) z = ∑ c, valAt x (A a c) z * valAt x (B c b) z := by
    intro a b
    rw [Matrix.mul_apply]
    obtain ⟨h1, h2⟩ := reg_sum hz Finset.univ (fun c => A a c * B c b)
      (fun c _ => (reg_mul hz (hA a c) (hB c b)).1)
    refine ⟨h1, ?_⟩
    rw [h2]
    exact Finset.sum_congr rfl fun c _ => (reg_mul hz (hA a c) (hB c b)).2
  refine ⟨fun a b => (key a b).1, ?_⟩
  ext a b
  simp only [valMat, Matrix.of_apply, Matrix.mul_apply]
  exact (key a b).2

theorem reg_minor {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (I J : Finset (Fin N)) :
    RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (valMat x z A) I J := by
  let A' : Matrix (Fin N) (Fin N) (regRing x z) := fun a b => ⟨A a b, hA a b⟩
  have hmap : A'.map (regRing x z).subtype = A := by
    ext a b
    rfl
  have h1 : minorIJ A I J = ((minorIJ A' I J : regRing x z) : Ω) := by
    have h := minorIJ_map (regRing x z).subtype A' I J
    rw [hmap] at h
    exact h
  have h2 : valMat x z A = A'.map (regVal x hz) := by
    ext a b
    rfl
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (minorIJ A' I J).2
  · rw [h2, minorIJ_map, h1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GroundTheory.Heights₂.Heights.AnalyticLimit in
theorem lemmaETailMass : GroundTheory.Heights₂.Heights.AnalyticLimit.LemmaETailMass.Statement :=
  LemmaETailMass.proof LemmaETrunc.proof LemmaETruncMass.proof
    (LemmaETruncTail.proof LemmaEScale.proof LemmaEEnergy.proof LemmaEWeight.proof
      LogNormSecIntegrable.proof)

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ContDiff

namespace SecPot

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_continuousOn' {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) :
    ContinuousOn f W := by
  intro z hz
  obtain ⟨j, hj⟩ := A.cover z
  have h1 : (A.chart j).symm (A.chart j z) = z := (A.chart j).left_inv hj
  have hu : A.chart j z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, h1]; exact hz⟩
  have hc : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j z) := (h j _ hu).continuousAt
  have hc2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) z :=
    ContinuousAt.comp hc ((A.chart j).continuousAt hj)
  have hev : ((f ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 z] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  exact (hc2.congr hev).continuousWithinAt

end General

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

structure LocSec (M : CxModel P d) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ) : Prop where
  isOpen : IsOpen U
  sec : ∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y
  holo : ∀ p, M.atlas.HoloOn U fun y => s y p

theorem locSec_sections (M : CxModel P d) (x : M.Xc) :
    LocSec M (M.sections x).choose (M.sections x).choose_spec.2.2.choose :=
  ⟨(M.sections x).choose_spec.1, (M.sections x).choose_spec.2.2.choose_spec.1,
    (M.sections x).choose_spec.2.2.choose_spec.2⟩

theorem smoothOn_log_sec {M : CxModel P d} {U : Set M.Xc} {s : M.Xc → (Σ k, ι k) → ℂ}
    (hs : LocSec M U s) {B : HermLine ι} (hB : IsSmoothHerm B) :
    M.atlas.SmoothOn U (fun y => Real.log (B.h (s y))) := by
  intro j y hy
  have hσ : ContDiffAt ℝ ∞ (fun y' => s ((M.atlas.chart j).symm y')) y :=
    contDiffAt_pi.2 fun p => ((hs.holo p j y hy).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hm := (hs.sec _ hy.2).1.1
  have hn : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (s ((M.atlas.chart j).symm y)) := by
    refine IsOpen.mem_nhds ?_ hm
    simp only [Set.setOf_forall, Set.setOf_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h1 : ContDiffAt ℝ ∞ (fun y' => Real.log (B.h (s ((M.atlas.chart j).symm y')))) y :=
    ((hB.contDiffAt hn).comp y hσ).log (B.pos _ hm).ne'
  exact h1.contDiffWithinAt

theorem exists_re_holo_sections {M : CxModel P d} {U U' : Set M.Xc} {s s' : M.Xc → (Σ k, ι k) → ℂ}
    (hs : LocSec M U s) (hs' : LocSec M U' s') (B : HermLine ι) {y₀ : M.Xc} (hy : y₀ ∈ U)
    (hy' : y₀ ∈ U') :
    ∃ W : Set M.Xc, IsOpen W ∧ y₀ ∈ W ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn W G ∧
      ∀ z ∈ W ∩ U ∩ U', Real.log (B.h (s z)) - Real.log (B.h (s' z)) = (G z).re := by
  classical
  have hz := (hs.sec y₀ hy).1
  have hz' := (hs'.sec y₀ hy').1
  choose i hi using hz'.1
  obtain ⟨c₀, hc₀, hcz⟩ := (M.fibre _ hz' _ hz).1 (by rw [(hs.sec y₀ hy).2, (hs'.sec y₀ hy').2])
  have hn0 : ∀ k, s y₀ ⟨k, i k⟩ ≠ 0 := fun k => by
    rw [hcz]
    exact mul_ne_zero (hc₀ k) (hi k)

  let r : K → ℂ := fun k => s y₀ ⟨k, i k⟩ / s' y₀ ⟨k, i k⟩
  have hr : ∀ k, r k ≠ 0 := fun k => div_ne_zero (hn0 k) (hi k)
  let q : K → M.Xc → ℂ := fun k z => s z ⟨k, i k⟩ / s' z ⟨k, i k⟩ / r k
  have hO : IsOpen (U ∩ U') := hs.isOpen.inter hs'.isOpen
  let W : Set M.Xc := {z | z ∈ U ∩ U' ∧ ∀ k, s' z ⟨k, i k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ∀ k, ContinuousAt (fun z => s z ⟨k, i k⟩) z := fun k =>
      ((holoOn_continuousOn' (hs.holo _)).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ∀ k, ContinuousAt (fun z => s' z ⟨k, i k⟩) z := fun k =>
      ((holoOn_continuousOn' (hs'.holo _)).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
      eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
    exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
  have hyW : y₀ ∈ W := by
    refine ⟨⟨hy, hy'⟩, fun k => ⟨hi k, ?_⟩⟩
    have : q k y₀ = 1 := div_self (hr k)
    rw [this]
    exact Complex.one_mem_slitPlane
  let G : M.Xc → ℂ := fun z => ∑ k, ((B.a k : ℝ) : ℂ) *
    (Complex.log (q k z) + ((Real.log ‖r k‖ : ℝ) : ℂ))
  refine ⟨W, hW, hyW, G, fun j u hu => ?_, fun z hz => ?_⟩
  · have hzW : (M.atlas.chart j).symm u ∈ W := hu.2
    have hterm : ∀ k, AnalyticAt ℂ (fun u' => ((B.a k : ℝ) : ℂ) *
        (Complex.log (q k ((M.atlas.chart j).symm u')) + ((Real.log ‖r k‖ : ℝ) : ℂ))) u := by
      intro k
      have hn : AnalyticAt ℂ (fun u' => s ((M.atlas.chart j).symm u') ⟨k, i k⟩) u :=
        hs.holo _ j u ⟨hu.1, hzW.1.1⟩
      have hd : AnalyticAt ℂ (fun u' => s' ((M.atlas.chart j).symm u') ⟨k, i k⟩) u :=
        hs'.holo _ j u ⟨hu.1, hzW.1.2⟩
      have hq : AnalyticAt ℂ (fun u' => q k ((M.atlas.chart j).symm u')) u :=
        (hn.div hd (hzW.2 k).1).div analyticAt_const (hr k)
      have hl : AnalyticAt ℂ (Complex.log ∘ fun u' => q k ((M.atlas.chart j).symm u')) u :=
        AnalyticAt.comp (f := fun u' => q k ((M.atlas.chart j).symm u'))
          (analyticAt_clog (hzW.2 k).2) hq
      exact analyticAt_const.mul (hl.add analyticAt_const)
    exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
  · have hzW : z ∈ W := hz.1.1
    have hm := (hs.sec z hzW.1.1).1
    have hm' := (hs'.sec z hzW.1.2).1
    obtain ⟨c, hc, hcy⟩ := (M.fibre _ hm' _ hm).1
      (by rw [(hs.sec z hzW.1.1).2, (hs'.sec z hzW.1.2).2])
    have hpos : 0 < B.h (s' z) := B.pos _ hm'.1
    have hprod : (∏ k, ‖c k‖ ^ B.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    have hterm : ∀ k, Real.log ‖q k z‖ + Real.log ‖r k‖ = Real.log ‖c k‖ := by
      intro k
      have hck : s z ⟨k, i k⟩ = c k * s' z ⟨k, i k⟩ := by rw [hcy]; rfl
      have hqz : q k z = c k / r k := by
        simp only [q]
        rw [hck, mul_div_assoc, div_self (hzW.2 k).1, mul_one]
      rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc k)) (norm_ne_zero_iff.mpr (hr k))]
      ring
    have hsm : B.h (s z) = (∏ k, ‖c k‖ ^ B.a k) * B.h (s' z) := by
      rw [hcy]
      exact B.smul c _ hc
    rw [hsm, Real.log_mul hprod hpos.ne', add_sub_cancel_right,
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))]
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re,
      Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k, Real.log_zpow]

def potOfSections (M : CxModel P d) (B : HermLine ι) : LocPot M.Xc where
  U x := (M.sections x).choose
  isOpen_U x := (M.sections x).choose_spec.1
  mem_U x := (M.sections x).choose_spec.2.1
  φ x y := Real.log (B.h ((M.sections x).choose_spec.2.2.choose y))

end Model

end SecPot


open SecPot in
theorem exists_potential_of_smoothHerm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (B : HermLine ι), IsSmoothHerm B → ∃ Φ : LocPot M.Xc, IsPotential M.atlas Φ ∧ ∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (B.h z)) (s y') = (G y').re := by
  intro K _ ι _ P n M B hB
  refine ⟨potOfSections M B, ⟨fun x => smoothOn_log_sec (locSec_sections M x) hB, ?_⟩, ?_⟩
  · intro x x' y hy
    exact exists_re_holo_sections (locSec_sections M x) (locSec_sections M x') B hy.1 hy.2
  · intro x y₀ hy
    have hs := locSec_sections M x
    refine ⟨_, hs.isOpen, hy.1, fun z hz => ⟨hz, Set.mem_univ _⟩, _, hs.sec, hs.holo, fun _ => 0,
      fun j u _ => analyticAt_const, fun y' _ => ?_⟩
    simp [potOfSections]

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef

open scoped ComplexOrder

theorem star_form_eq {g : ℕ} {Hb : Matrix (Fin g) (Fin g) ℂ} (hH : Hb.IsHermitian)
    (x y : Fin g → ℂ) :
    star (x ⬝ᵥ Hb *ᵥ star y) = y ⬝ᵥ Hb *ᵥ star x := by
  have h1 : ∀ w : Fin g → ℂ, star (x ⬝ᵥ w) = star w ⬝ᵥ star x := by
    intro w
    simp [dotProduct, mul_comm]
  rw [h1, star_mulVec, star_star, hH.eq, dotProduct_mulVec]

theorem gram_form_eq {g k : ℕ} (Hb : Matrix (Fin g) (Fin g) ℂ) (q : Fin k → Fin g → ℂ)
    (l : Fin k → ℂ) :
    star l ⬝ᵥ (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)) *ᵥ l =
      (∑ c, l c • q c) ⬝ᵥ Hb *ᵥ star (∑ c, l c • q c) := by
  rw [star_sum, mulVec_sum, sum_dotProduct]
  simp only [dotProduct_sum, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  simp only [dotProduct, mulVec, of_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem gram_posDef {g k : ℕ} {Hb : Matrix (Fin g) (Fin g) ℂ}
    {U : Submodule ℂ (Fin g → ℂ)} {q : Fin k → Fin g → ℂ} (hH : Hb.IsHermitian)
    (hpos : ∀ v : Fin g → ℂ,
      0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U))
    (hind : ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) :
    (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext c c'
    simp only [conjTranspose_apply, of_apply]
    exact star_form_eq hH (q c) (q c')
  · intro l hl
    rw [gram_form_eq]
    set v : Fin g → ℂ := ∑ c, l c • q c with hv
    have hre : 0 < (v ⬝ᵥ Hb *ᵥ star v).re := by
      refine lt_of_le_of_ne (hpos v).1 fun h0 => hl (hind l ?_)
      exact (hpos v).2 h0.symm
    have him : (v ⬝ᵥ Hb *ᵥ star v).im = 0 :=
      Complex.conj_eq_iff_im.mp (star_form_eq hH v v)
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem gram_det_re_pos (g : ℕ) (Hb : Matrix (Fin g) (Fin g) ℂ)
    (U : Submodule ℂ (Fin g → ℂ)) (k : ℕ) (q : Fin k → Fin g → ℂ) (hH : Hb.IsHermitian)
    (hpos : ∀ v : Fin g → ℂ,
      0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U))
    (hind : ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) :
    0 < (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).det.re :=
  (Complex.lt_def.mp (gram_posDef hH hpos hind).det_pos).1

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.smooth_function_as_degree_zero_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D) (u : R.X → ℝ), R.A.Smooth u → ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ x, Real.log (B.h (R.lift x x)) = u x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth | exact GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth <;> assumption)
end
