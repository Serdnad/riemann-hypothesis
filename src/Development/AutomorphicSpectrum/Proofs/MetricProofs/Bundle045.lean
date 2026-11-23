module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import Mathlib.RingTheory.RingHom.Flat
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle025
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularPotentialLogGrowthPsh
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

section Weight

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_blockScale {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (fun p : Σ k, ι k => c p.1 * z p) s = (∏ k, c k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ q : (Σ k, ι k), (c q.1 * z q) ^ m q =
      (∏ k, c k ^ a k) * ∏ q : (Σ k, ι k), z q ^ m q := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [h1]; ring

theorem logNormC_blockScale (A : HermLine ι) {s : MRingOver ℂ ι} {a : K → ℕ}
    (hA : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : logNormC A s (fun p => c p.1 * z p) = logNormC A s z := by
  unfold logNormC
  rw [eval_blockScale hs c z]
  have hh : A.h (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ A.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hA k, zpow_natCast]
  rw [hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']

theorem segre_blockScale (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segre (fun p : Σ k, ι k => c p.1 * z p) i = (∏ k, c k) * segre z i := by
  simp only [segre, Finset.prod_mul_distrib]

theorem isClosed_domCell (i : (k : K) → ι k) : IsClosed (domCell i) := by
  have hc : ∀ j : (k : K) → ι k, Continuous fun z : (Σ k, ι k) → ℂ => ‖segre z j‖ := fun j => by
    have h : Continuous fun z : (Σ k, ι k) → ℂ => ∏ k, z ⟨k, j k⟩ :=
      continuous_finsetProd _ fun k _ => continuous_apply (⟨k, j k⟩ : Σ k, ι k)
    exact h.norm
  have : domCell i = ⋂ j, {z : (Σ k, ι k) → ℂ | ‖segre z j‖ ≤ ‖segre z i‖} := by
    ext z; simp [domCell]
  rw [this]
  exact isClosed_iInter fun j => isClosed_le (hc j) (hc i)

theorem blockScale_mem_domCell {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ)
    (i : (k : K) → ι k) : (fun p : Σ k, ι k => c p.1 * z p) ∈ domCell i ↔ z ∈ domCell i := by
  have hpos : 0 < ‖∏ k, c k‖ :=
    norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)
  simp only [domCell, Set.mem_setOf_eq, segre_blockScale, norm_mul]
  exact forall_congr' fun j =>
    ⟨fun h => le_of_mul_le_mul_left h hpos, fun h => mul_le_mul_of_nonneg_left h hpos.le⟩

theorem measurable_absLogNorm (A : HermLine ι) (hA : IsSmoothHerm A) (s : MRingOver ℂ ι) :
    Measurable (absLogNorm A s) := by
  classical
  set T : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hT
  have hTm : MeasurableSet T := isOpen_blockNonzero.measurableSet
  have hh : Measurable (T.piecewise A.h 1) :=
    hA.continuousOn.measurable_piecewise continuousOn_const hTm
  have heq : absLogNorm A s =
      T.piecewise (fun z => |Real.log (‖eval z s‖ / T.piecewise A.h 1 z)|) 0 := by
    funext z
    by_cases hz : z ∈ T
    · have hz' : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := hz
      rw [Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ hz]
      simp only [absLogNorm, if_pos hz', logNormC]
    · have hz' : ¬ ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := hz
      rw [Set.piecewise_eq_of_notMem _ _ _ hz]
      simp only [absLogNorm, if_neg hz', Pi.zero_apply]
  rw [heq]
  refine Measurable.piecewise hTm ?_ measurable_const
  exact continuous_abs.measurable.comp
    (Real.measurable_log.comp ((MvPolynomial.continuous_eval s).norm.measurable.div hh))

theorem absLogNorm_blockScale (A : HermLine ι) {s : MRingOver ℂ ι} {a : K → ℕ}
    (hAa : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : absLogNorm A s (fun p => c p.1 * z p) = absLogNorm A s z := by
  have hmem : (∀ k, ∃ j, c k * z ⟨k, j⟩ ≠ 0) ↔ ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, hc, false_or]
  by_cases hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0
  · simp only [absLogNorm, if_pos hz, if_pos (hmem.2 hz), logNormC_blockScale A hAa hs hc z]
  · simp only [absLogNorm, if_neg hz, if_neg (mt hmem.1 hz)]

end Weight

theorem cutWeight_measurable_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ) (i : (k : K) → ι k),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (domCell i).indicator (absLogNorm A s) (fun p => c p.1 * z p) =
        (domCell i).indicator (absLogNorm A s) z := by
  intro K _ ι _ A s a i hA hAa hs
  refine ⟨(measurable_absLogNorm A hA s).indicator (isClosed_domCell i).measurableSet, ?_⟩
  intro c z hc
  by_cases hz : z ∈ domCell i
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((blockScale_mem_domCell hc z i).2 hz),
      absLogNorm_blockScale A hAa hs hc z]
  · rw [Set.indicator_of_notMem hz,
      Set.indicator_of_notMem (mt (blockScale_mem_domCell hc z i).1 hz)]

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Abstract

variable {R R' : Type*} [CommRing R] [CommRing R']

theorem length_cut_of_flat (φ : R →+* R') (q : R') (J W : Ideal R) [W.IsPrime]
    (W' : Ideal R') [W'.IsPrime] (hW' : W' = W.map φ ⊔ Ideal.span {q}) (hc : W'.comap φ = W)
    (hflat : ((Ideal.Quotient.mk (Ideal.span {q})).comp φ).Flat) :
    Module.length (Localization.AtPrime W')
        (LocalizedModule W'.primeCompl (R' ⧸ (J.map φ ⊔ Ideal.span {q}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) := by
  let I : Ideal R' := Ideal.span {q}
  let π : R' →+* R' ⧸ I := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  let ψ : R →+* R' ⧸ I := π.comp φ
  have hker : RingHom.ker π = I := Ideal.mk_ker
  have hIW : I ≤ W' := hW' ▸ le_sup_right
  let P : Ideal (R' ⧸ I) := W'.map π
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective hπ (by rw [hker]; exact hIW)
  have hPc : W' = P.comap π := by
    show W' = (W'.map π).comap π
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hIW]
  have hPψ : W = P.comap ψ := by
    have h : P.comap ψ = (P.comap π).comap φ := (Ideal.comap_comap φ π).symm
    rw [h, ← hPc, hc]
  have hPmap : W.map ψ = P := by
    show W.map (π.comp φ) = W'.map π
    rw [hW', Ideal.map_sup, ← Ideal.map_map]
    have : (Ideal.span {q} : Ideal R').map π = ⊥ := Ideal.map_quotient_self I
    rw [this, sup_bot_eq]
  let L := Localization.localRingHom W P ψ hPψ
  have hLflat : L.Flat := RingHom.Flat.localRingHom hflat P W hPψ
  have hcomp : L.comp (algebraMap R (Localization.AtPrime W)) =
      (algebraMap (R' ⧸ I) (Localization.AtPrime P)).comp ψ :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hPψ z
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map L =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), Ideal.map_map, hcomp,
      ← Ideal.map_map, hPmap, IsLocalization.AtPrime.map_eq_maximalIdeal P]
  have hJ : (J.map (algebraMap R (Localization.AtPrime W))).map L =
      (J.map ψ).map (algebraMap (R' ⧸ I) (Localization.AtPrime P)) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  have hkerE : RingHom.ker ((Ideal.Quotient.mk (J.map ψ)).comp π) = J.map φ ⊔ I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    show ((J.map (π.comp φ))).comap π = _
    rw [← Ideal.map_map, Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, hker]
  let e : (R' ⧸ (J.map φ ⊔ I)) ≃+* ((R' ⧸ I) ⧸ J.map ψ) :=
    (Ideal.quotEquivOfEq hkerE.symm).trans (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk (J.map ψ)).comp π) (Ideal.Quotient.mk_surjective.comp hπ))
  have he : ∀ (s : R') (x : R' ⧸ (J.map φ ⊔ I)), e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (J.map ψ) (π (s * y)) =
      Ideal.Quotient.mk (J.map ψ) (π s) * Ideal.Quotient.mk (J.map ψ) (π y)
    rw [map_mul, map_mul]
  rw [GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_eq_of_surjective π hπ P W' hPc _ _
      e.toAddEquiv he,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    ← hJ]
  exact GroundTheory.Heights₂.Heights.Inter.BCMultProof.length_quot_map_of_flat L hLflat hmax _

end Abstract

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def toPoly : MRing (Tb ι) →+* Polynomial (Polynomial (MRing ι)) :=
  (aeval (fun q : Σ o, Tb ι o => match q with
    | ⟨none, j⟩ => (![Polynomial.X, Polynomial.C Polynomial.X] : Fin 2 → _) j
    | ⟨some k, i⟩ => Polynomial.C (Polynomial.C (X ⟨k, i⟩))) :
      MRing (Tb ι) →ₐ[ℤ] Polynomial (Polynomial (MRing ι))).toRingHom

def ofPoly : Polynomial (Polynomial (MRing ι)) →+* MRing (Tb ι) :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom inc yN) xN

theorem toPoly_xN : toPoly (xN : MRing (Tb ι)) = Polynomial.X := by
  simp only [toPoly, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toPoly_yN : toPoly (yN : MRing (Tb ι)) = Polynomial.C Polynomial.X := by
  simp only [toPoly, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toPoly_comp_inc : (toPoly.comp inc : MRing ι →+* _) = Polynomial.C.comp Polynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [toPoly, inc]
  · intro i; simp [toPoly, inc, oldIdx]

theorem toPoly_inc (f : MRing ι) : toPoly (inc f) = Polynomial.C (Polynomial.C f) :=
  congrArg (fun g => g f) (toPoly_comp_inc (ι := ι))

theorem ofPoly_comp_toPoly : (ofPoly.comp toPoly : MRing (Tb ι) →+* _) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [toPoly, ofPoly]
  · rintro ⟨o, i⟩
    cases o with
    | none =>
      change Fin 2 at i
      fin_cases i
      · have : (X ⟨none, (0 : Fin 2)⟩ : MRing (Tb ι)) = xN := rfl
        simp [this, toPoly_xN, ofPoly]
      · have : (X ⟨none, (1 : Fin 2)⟩ : MRing (Tb ι)) = yN := rfl
        simp [this, toPoly_yN, ofPoly]
    | some k =>
      simp [toPoly, ofPoly, inc, oldIdx]

theorem toPoly_comp_ofPoly :
    (toPoly.comp ofPoly : Polynomial (Polynomial (MRing ι)) →+* _) = RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · refine RingHom.ext fun f => ?_
      simp [ofPoly, toPoly_inc]
    · simp [ofPoly, toPoly_yN]
  · simp [ofPoly, toPoly_xN]

def polyEquiv : MRing (Tb ι) ≃+* Polynomial (Polynomial (MRing ι)) :=
  RingEquiv.ofRingHom toPoly ofPoly toPoly_comp_ofPoly ofPoly_comp_toPoly

theorem toPoly_quad (p : ℕ) : ∃ s : Polynomial (MRing ι),
    toPoly (quad p : MRing (Tb ι)) = Polynomial.X ^ 2 + Polynomial.C s := by
  refine ⟨Polynomial.C (C (p : ℤ)) * Polynomial.X ^ 2, ?_⟩
  have h : toPoly (C (p : ℤ) : MRing (Tb ι)) =
      Polynomial.C (Polynomial.C (C (p : ℤ) : MRing ι)) := by
    simpa [inc] using toPoly_inc (ι := ι) (C (p : ℤ) : MRing ι)
  simp [quad, toPoly_xN, toPoly_yN, h]

theorem flat_quad (p : ℕ) :
    ((Ideal.Quotient.mk (Ideal.span {quad p})).comp inc :
      MRing ι →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat := by
  obtain ⟨s, hs⟩ := toPoly_quad (ι := ι) p
  let g : Polynomial (Polynomial (MRing ι)) := Polynomial.X ^ 2 + Polynomial.C s
  have hg : g.Monic := Polynomial.monic_X_pow_add
    (lt_of_le_of_lt Polynomial.degree_C_le (by norm_num))
  have : Module.Free (Polynomial (MRing ι)) (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  have h1 : (Polynomial.C : MRing ι →+* Polynomial (MRing ι)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (MRing ι) (Polynomial (MRing ι)))
  have h2 : (AdjoinRoot.of g).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (inferInstance : Module.Flat (Polynomial (MRing ι)) (AdjoinRoot g))
  let E : (MRing (Tb ι) ⧸ Ideal.span {quad p}) ≃+* AdjoinRoot g :=
    Ideal.quotientEquiv _ _ (polyEquiv (ι := ι)) (by
      rw [Ideal.map_span, Set.image_singleton]
      show Ideal.span {g} = Ideal.span {toPoly (quad p)}
      rw [hs])
  have h3 : (E.symm : AdjoinRoot g →+* MRing (Tb ι) ⧸ Ideal.span {quad p}).Flat :=
    RingHom.Flat.of_bijective E.symm.bijective
  have hcomp : (Ideal.Quotient.mk (Ideal.span {quad p})).comp inc =
      (E.symm : AdjoinRoot g →+* _).comp ((AdjoinRoot.of g).comp Polynomial.C) := by
    refine RingHom.ext fun f => ?_
    show Ideal.Quotient.mk _ (inc f) = E.symm (AdjoinRoot.of g (Polynomial.C f))
    rw [RingEquiv.eq_symm_apply]
    show Ideal.Quotient.mk _ (toPoly (inc f)) = _
    rw [toPoly_inc]
    rfl
  rw [hcomp]
  exact (h1.comp h2).comp h3

theorem multAt_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (J W : Ideal (MRing ι)) (hW : W ∈ J.minimalPrimes) (hT : (twist p W).IsPrime) :
    multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  have hWp : W.IsPrime := hW.1.1
  unfold multAt
  rw [dite_eq_left hT, dite_eq_left hWp]
  exact congrArg ENat.toNat (length_cut_of_flat inc (quad p) J W (twist p W) rfl
    (comap_inc_twist p W) (flat_quad p))

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)


theorem _root_.GlobalTheory.T.setFibre_finite_of_goodProj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → ∀ y, (setFibre (conePts Q) Ψ y).Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | exact GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite <;> assumption)
end

section

open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.Metric.LocTail

theorem tailLog_on_compact_of_chart {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Yo : Set X) (r : X → ℝ) (Φ : Fin e → LocPot X) (CE : ℝ)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hr : ∀ x ∈ Yo, 1 ≤ r x)
    (hdens : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A Φ j y)
    (hT : GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A Yo r Φ CE)
    (j : Fin A.n) (S : Set (Fin e → ℂ)) (hSt : S ⊆ (A.chart j).target) (hSc : IsCompact S)
    (R₀ : ℝ) (hR₀ : Real.exp 1 ≤ R₀) :
    IntegrableOn (fun y => (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
      (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y) S ∧
    ∫ y in S, (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
      (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y ≤
      CE * Real.log R₀ ^ (e + 1) / R₀ := by
  classical
  obtain ⟨hI, hB⟩ := hT R₀ hR₀
  set h : X → ℝ := (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
    (fun x => Real.log (r x)) with hdef
  have hIS := hI j S hSt hSc
  refine ⟨hIS, ?_⟩
  have hh0 : ∀ x, 0 ≤ h x := by
    intro x
    refine Set.indicator_nonneg (fun x hx => ?_) x
    exact Real.log_nonneg (hr x hx.1)
  have hhYo : ∀ x, x ∉ Yo → h x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (by exact fun hm => hx hm.1) _
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  set ch := A.chart j with hch
  set Z : Set X := ch.symm '' S with hZ
  set g : X → ℝ := Z.indicator h with hgdef
  have hg0 : ∀ x, x ∉ ch.source → g x = 0 := by
    intro x hx
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨y, hy, rfl⟩
    exact hx (ch.map_target (hSt hy))
  set F : (Fin e → ℂ) → ℝ := fun y => h (ch.symm y) * locDens A Φ j y with hF
  have hgF : ∀ z ∈ ch.target, g (ch.symm z) * locDens A Φ j z = S.indicator F z := by
    intro z hz
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS, hgdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hzS)]
    · have hnZ : ch.symm z ∉ Z := by
        rintro ⟨y, hy, hyz⟩
        exact hzS ((ch.symm.injOn (by simpa using hSt hy) (by simpa using hz) hyz) ▸ hy)
      rw [Set.indicator_of_notMem hzS, hgdef, Set.indicator_of_notMem hnZ, zero_mul]
  have hFint : IntegrableOn (S.indicator F) ch.target :=
    ((integrable_indicator_iff hSm).2 hIS).integrableOn
  have hint : IntegrableOn (fun z => g (ch.symm z) * locDens A Φ j z) ch.target :=
    hFint.congr_fun (fun z hz => (hgF z hz).symm) ch.open_target.measurableSet
  have hne : Nonempty (ChartPartition A) := existsPartition A
  obtain ⟨hgt, hgI⟩ := integralWith_localize_support A hne.some Φ hΦ j g hg0 hint
  have hSint : ∫ z in ch.target, g (ch.symm z) * locDens A Φ j z = ∫ y in S, F y := by
    rw [setIntegral_congr_fun ch.open_target.measurableSet hgF,
      setIntegral_indicator hSm, Set.inter_eq_right.2 hSt]
  have hle : integralWith A hne.some Φ g ≤ integralWith A hne.some Φ h := by
    unfold integralWith
    refine Finset.sum_le_sum fun k _ => ?_
    refine setIntegral_mono_on (hgt k) (integrableOn_weight A hne.some Φ h hI k)
      (A.chart k).open_target.measurableSet fun y hy => ?_
    by_cases hx : (A.chart k).symm y ∈ Yo
    · have hd := hdens k y hy hx
      have hχ := hne.some.nonneg k ((A.chart k).symm y)
      have hgh : g ((A.chart k).symm y) ≤ h ((A.chart k).symm y) :=
        Set.indicator_le_self' (fun x _ => hh0 x) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgh hχ) hd
    · have h1 : h ((A.chart k).symm y) = 0 := hhYo _ hx
      have h2 : g ((A.chart k).symm y) = 0 := by
        rw [hgdef]
        by_cases hz : (A.chart k).symm y ∈ Z
        · rw [Set.indicator_of_mem hz, h1]
        · rw [Set.indicator_of_notMem hz]
      rw [h1, h2]
  calc ∫ y in S, F y = integralWith A hne.some Φ g := by rw [hgI, hSint]
    _ ≤ integralWith A hne.some Φ h := hle
    _ = mInt A Φ h := by
      unfold mInt
      rw [dite_eq_left hne]
    _ ≤ _ := hB

end GlobalTheory.CompanionTheory.Metric.LocTail
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.snc_adapted_atlas_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas e X) (Ab Bb : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A Ab pr) (L : LocPot Z) (s : Z → Z → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Z), IsPotential Ab L → IsSection Ab L s → IsSNC Ab L s m W → (∀ x, logNormSec L s x ≤ 0) → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) → IsPotential A (L.pullback pr hp.1) ∧ IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) ∧ IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) ∧ ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | exact GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.singular_potential_log_growth_psh : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : LocPot X) (u : X → ℝ) (C₁ : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → (∀ y ∉ bdry s, |u y| ≤ C₁ * Real.log (rW L s y)) → ∃ C₅, IsSingWeight A L s th u C₅ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.isSingWeight_of_logGrowth | exact GlobalTheory.CompanionTheory.Ar.PB.isSingWeight_of_logGrowth | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.isSingWeight_of_logGrowth <;> assumption)
end
