module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleNefPlusAmple
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle047
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle045
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle002
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

namespace ModelGenericPoint

variable {O : Type} [CommRing O] {K : Type} {ι : K → Type} (P : Ideal (NumbersDVR.MRing ι O))

def genPt : (Σ k, ι k) → FractionRing (NumbersDVR.MRing ι O ⧸ P) :=
  fun p => algebraMap (NumbersDVR.MRing ι O ⧸ P) _ (Ideal.Quotient.mk P (X p))

theorem aeval_genPt (g : NumbersDVR.MRing ι O) :
    aeval (genPt P) g = algebraMap (NumbersDVR.MRing ι O ⧸ P)
      (FractionRing (NumbersDVR.MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) := by
  have h : (aeval (genPt P) : NumbersDVR.MRing ι O →ₐ[O] FractionRing (NumbersDVR.MRing ι O ⧸ P)) =
      (IsScalarTower.toAlgHom O (NumbersDVR.MRing ι O ⧸ P)
        (FractionRing (NumbersDVR.MRing ι O ⧸ P))).comp (Ideal.Quotient.mkₐ O P) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [genPt]
  rw [h]
  rfl

theorem aeval_genPt_eq_zero (g : NumbersDVR.MRing ι O) : aeval (genPt P) g = 0 ↔ g ∈ P := by
  rw [aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

theorem genPt_ne_zero (p : Σ k, ι k) : genPt P p ≠ 0 ↔ (X p : NumbersDVR.MRing ι O) ∉ P := by
  rw [Ne, ← aeval_genPt_eq_zero, aeval_X]

theorem mIdealOver_genPt [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [P.IsPrime]
    (hP : NumbersDVR.IsMultiHomogIdeal P) : mIdealOver O (genPt P) = P := by
  ext f
  constructor
  · intro hf
    have hc : ∀ b : K → ℕ, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f ∈ P := by
      intro b
      rw [← aeval_genPt_eq_zero, ← coeff_mConeMapOver, RingHom.mem_ker.mp hf, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    exact Ideal.sum_mem _ fun b _ => hc b
  · intro hf
    refine RingHom.mem_ker.mpr ?_
    ext m
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    have h := coeff_mConeMapOver (S := O) (genPt P) (⇑m) f
    rw [Finsupp.equivFunOnFinite_symm_coe] at h
    rw [h, aeval_genPt_eq_zero]
    exact hP f hf _

end ModelGenericPoint


end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def RealiseRestrict.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
      ∀ (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
        IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀ → mIdealOver F y ≤ mIdealOver F y' →
        ∀ hxy : (∀ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) i ≠ 0 → x i ≠ 0),
          ∃ (Q' : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm)) (r : Ω → K'),
            Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r ∧ BundleRealises y' k₀ Q' β

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

universe u w

section Scale

variable {k : Type u} [Field k] {K' : Type w} [Field K'] [Algebra k K'] {N : ℕ} {y : Fin (N + 1) → K'}

def scaleBundle (P : Kleiman.LineBundle k y) (μ : K') (hμ : μ ≠ 0) : Kleiman.LineBundle k y where
  sub I := Submodule.span (Kleiman.chartRing k y I) {μ} * P.sub I
  mono I J h z hz := by
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact Submodule.mem_span_singleton_mul.mpr ⟨w, P.mono I J h w hw, rfl⟩
  mem_iff I J h z := by
    simp only [Submodule.mem_span_singleton_mul]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, ha, haw⟩ := (P.mem_iff I J h w).mp hw
      refine ⟨a, ha, (a : K') • w, haw, ?_⟩
      simp only [smul_eq_mul]; ring
    · rintro ⟨a, ha, w, hw, hwz⟩
      refine ⟨μ⁻¹ * z, (P.mem_iff I J h _).mpr ⟨a, ha, ?_⟩, by field_simp⟩
      rw [smul_eq_mul] at hwz ⊢
      rw [show (a : K') * (μ⁻¹ * z) = w by
        rw [mul_left_comm, ← hwz, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]]
      exact hw
  fg I := (Submodule.fg_span_singleton μ).mul (P.fg I)
  invertible I := by
    obtain ⟨M, hM⟩ := P.invertible I
    refine ⟨Submodule.span (Kleiman.chartRing k y I) {μ⁻¹} * M, ?_⟩
    rw [mul_mul_mul_comm, hM, Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hμ,
      mul_one, ← Submodule.one_eq_span]

theorem restrictData_scale {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {Q : Kleiman.SubSystem k x Ω} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {P : Kleiman.LineBundle k y} {r : Ω → K'}
    (hr : Kleiman.RestrictData Q hxy P.toSubSystem r) (μ : K') (hμ : μ ≠ 0) :
    Kleiman.RestrictData Q hxy (scaleBundle P μ hμ).toSubSystem (fun q => μ * r q) := by
  constructor
  · intro I q hq
    exact Submodule.mem_span_singleton_mul.mpr ⟨r q, hr.mem I q hq, rfl⟩
  · intro I q hq q' hq'
    simp only [hr.add I q hq q' hq', mul_add]
  · intro I q hq f s e hs hf hse
    simp only [hr.smul I q hq f s e hs hf hse]
    ring
  · intro I
    change _ = Submodule.span _ {μ} * P.sub I
    rw [← hr.span I, Submodule.span_mul_span, Set.singleton_mul, Set.image_image]

end Scale

section GraphEq

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {N m : ℕ}

abbrev baseRename : Kleiman.Poly k N →ₐ[k] MvPolynomial (Σ c, graphIdx N m c) k :=
  rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)

theorem mConeMapOver_baseRename (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {g : Kleiman.Poly k N} {e : ℕ}
    (hg : g.IsHomogeneous e) :
    mConeMapOver k (graphVec x s) (baseRename g) = C (aeval x g) * X baseBlock ^ e := by
  have h1 := DFunLike.congr_fun (mConeMapOver_graph_comp_base (S := k) x s) g
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1
  rw [h1, Kleiman.cone_of_isHomogeneous x hg, AlgHom.restrictScalars_apply, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.algebraMap_eq]

theorem mConeMapOver_graphEq (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {f h : Kleiman.Poly k N} {e : ℕ}
    (hf : f.IsHomogeneous e) (hh : h.IsHomogeneous e) (b l : Fin m) :
    mConeMapOver k (graphVec x s) (X ⟨Sum.inr (), b⟩ * baseRename h - X ⟨Sum.inr (), l⟩ * baseRename f) =
      C (s b * aeval x h - s l * aeval x f) * (X (Sum.inr ()) * X baseBlock ^ e) := by
  rw [map_sub, map_mul, map_mul, mConeMapOver_baseRename x s hh, mConeMapOver_baseRename x s hf]
  simp only [mConeMapOver, aeval_X, graphVec_inr, map_sub, map_mul]
  ring

theorem graphEq_of_le {K' : Type} [Field K'] [Algebra k K'] {x : Fin (N + 1) → Ω} {s : Fin m → Ω}
    {x' : Fin (N + 1) → K'} {s' : Fin m → K'}
    (hle : mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s')) {f h : Kleiman.Poly k N} {e : ℕ}
    (hf : f.IsHomogeneous e) (hh : h.IsHomogeneous e) (b l : Fin m)
    (hx : s b * aeval x h = s l * aeval x f) : s' b * aeval x' h = s' l * aeval x' f := by
  have hmem : X ⟨Sum.inr (), b⟩ * baseRename h - X ⟨Sum.inr (), l⟩ * baseRename f ∈
      mIdealOver k (graphVec x s) := by
    change _ ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    rw [mConeMapOver_graphEq x s hf hh, hx, sub_self, map_zero, zero_mul]
  have h0 := hle hmem
  change _ ∈ RingHom.ker _ at h0
  rw [RingHom.mem_ker] at h0
  change mConeMapOver k (graphVec x' s') _ = 0 at h0
  rw [mConeMapOver_graphEq x' s' hf hh, mul_eq_zero, C_eq_zero, sub_eq_zero] at h0
  exact h0.resolve_right (mul_ne_zero (X_ne_zero _) (pow_ne_zero _ (X_ne_zero _)))

end GraphEq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem GraphClosed.full : GraphClosed.Statement.{u, w} := GraphClosed.proof
theorem VeryAmplePow.full : VeryAmplePow.Statement.{u, w} := VeryAmplePow.proof

theorem SectionExists.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) : SectionExists.Statement.{u, w} :=
  SectionExists.proof (SectionCount.assembled hTop hF hT hH hR) VeryAmplePow.full
    (LeadingCoeffPos.proof_of_cut hR hPos)

theorem VeryAmpleNefPlusAmple.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    VeryAmpleNefPlusAmple.Statement.{u, w} :=
  VeryAmpleNefPlusAmple.proof Generated.full (SectionExists.assembled hTop hF hT hH hR hPos)
    (StepThree.assembled hL hG) GraphClosed.full hPt

theorem NefProductNonneg.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    NefProductNonneg.Statement.{u, w} :=
  NefProductNonneg.proof (VeryAmpleNefPlusAmple.assembled hTop hF hT hH hR hPos hL hG hPt) hR

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

theorem segreFibresNef_of_map (hA : SegreLiftComap.Statement) (hB : SegreLiftPrime.Statement)
    (hC : SegreLiftRelDim.Statement) (hN : SegreLiftIntNum.Statement)
    (hD : SegreFibreIdeal.Statement) (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (F : Type) [Field F] (φ : O →+* F) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (β : K → ℤ) :
    IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal F ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ))
                              (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
      IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal F ((mIdealOver O y).map (MvPolynomial.map φ)) β := by
  obtain ⟨hrel, hle, hlift⟩ := hD O Ω F φ K ι y
  constructor
  · intro h W hW hPW hdim
    have hpos := h (segreLift ι F W) (hB F K ι W hW) (hlift W hPW)
      (by rw [hC F K ι W hW]; exact hdim)
    rwa [hN F K ι W hW β] at hpos
  · intro h W' hW' hPW' hdim
    obtain ⟨hWp, heq⟩ := hA F K ι W' hW' fun g hg => hPW' (hrel hg)
    have hPW : (mIdealOver O y).map (MvPolynomial.map φ) ≤ W'.comap (segreIncl ι F) :=
      hle.trans (Ideal.comap_mono hPW')
    have hdimW : relDim (W'.comap (segreIncl ι F)) = ((1 : ℕ) : WithBot (WithTop ℤ)) := by
      rw [← hC F K ι _ hWp, ← heq]
      exact hdim
    have hpos := h _ hWp hPW hdimW
    rw [heq, hN F K ι _ hWp β]
    exact hpos

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

theorem SegreRealise.proof (hB : SegreBase.Statement) (hT : SegreTwist.Statement) (hD : SegreDim.Statement)
    (hNf : SegreNef.Statement) (hNm : SegreNum.Statement) (hBd : BundleOfDeg.Statement)
    (hMD : ModelDimEq.Statement) (hMN : ModelNefEq.Statement) (hMNum : ModelNumEq.Statement) :
    SegreRealise.Statement := by
  classical
  intro F _ K _ _ ι _ Ω _ _ y d μs hy hd
  have : ∀ a, Nonempty (ι a) := fun a => ⟨(hy a).choose⟩
  have hcard : 0 < Fintype.card (∀ a, ι a) := Fintype.card_pos
  let N := Fintype.card (∀ a, ι a) - 1
  let eqv : (∀ a, ι a) ≃ Fin (N + 1) := Fintype.equivFinOfCardEq (by omega)
  have hbase : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F (segreJoin y) (Sum.inl ()) := (hB F K ι Ω y hy).1
  choose Ms hMs using fun j =>
    hBd F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j))
  have hsub : Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm)
      (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm)) d :=
    (hMD F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase d).2 (by rw [hD F K ι Ω y hy]; exact hd)
  refine ⟨N, eqv, IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm, Ms, fun i => ?_, hsub,
    fun j c => ?_, fun j => ?_, ?_⟩
  · show ∏ a, y ⟨a, eqv.symm (eqv i) a⟩ = ∏ a, y ⟨a, i a⟩
    rw [Equiv.symm_apply_apply]
  · exact (hMs j c).trans (hT F K ι Ω y hy (μs j) c)
  · exact (hMN F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase _ (Ms j) (hMs j)).trans (hNf F K ι Ω y hy (μs j))
  · exact (hMNum F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase d (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j)) Ms
      hMs hsub).trans (hNm F K ι Ω y hy d μs)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem ModelDimEq.full : ModelDimEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod d
  obtain ⟨hnz, hsame⟩ := hmod
  choose c hc using hnz
  obtain ⟨c', hc', htr⟩ := exists_trdeg_chartRing_eq y _ hsame c hc
  have hy := trdeg_quotient_mIdealOver (F := F) y c hc
  have hx := trdeg_quotient_mIdealOver (F := F) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c' hc'
  rw [← htr, Fintype.card_unit] at hx

  have _ : (mIdealOver F y).IsPrime := RingHom.ker_isPrime _
  have _ : (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))).IsPrime :=
    RingHom.ker_isPrime _
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)
  rw [hy] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = ((t + Fintype.card K : ℕ) : ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]
    simp
  have dimx : ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) =
      ((t + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← ReindexDim.proof F (ι k₀) Ω (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) N e,
      GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hx, ht]
    simp
  have hrel : relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ)) := by
    unfold relDim
    rw [dimy]
    have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
        ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
        (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
    rw [e₁, Nat.cast_add, add_sub_cancel_right]
    rfl
  rw [hrel]
  constructor
  · intro h
    have h' := h.dim
    rw [dimx] at h'
    have htd : t + 1 = d + 1 := by exact_mod_cast h'
    rw [show t = d by omega]
  · intro h
    have htd : t = d := by exact_mod_cast h
    refine ⟨inferInstance, fun p hp n => Kleiman.homogeneousComponent_mem_primeOf _ hp n, le_rfl,
      ⟨e (c k₀), ?_⟩, by rw [dimx, htd]⟩
    rw [Kleiman.mem_primeOf_of_isHomogeneous _ (isHomogeneous_X F _), aeval_X]
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hc k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem isMultiProjPrime_baseComap (F : Type) [Field F] {K : Type} [DecidableEq K] {ι : K → Type} (k₀ : K)
    {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {W : Ideal (NumbersDVR.MRing ι F)} (hW : NumbersDVR.IsMultiProjPrime W) :
    NumbersDVR.IsMultiProjPrime (baseComap F k₀ e W) := by
  refine FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := fun _ : Unit => k₀)
    (g := fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) (fun _ => rfl)
    (fun _ _ _ => Subsingleton.elim _ _) ?_ ?_ hW
  · rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, EmbeddingLike.apply_eq_iff_eq] at h
    rw [h]
  · rintro ⟨k, i⟩ ⟨⟨⟩, hk⟩
    obtain rfl : k₀ = k := hk
    exact ⟨⟨(), e i⟩, by simp⟩

theorem mIdealOver_le_baseComap (F : Type) [Field F] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {x : Fin (N + 1) → Ω}
    (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) {W : Ideal (NumbersDVR.MRing ι F)}
    (hW : mIdealOver F y ≤ W) : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ baseComap F k₀ e W := by
  subst hx
  intro f hf
  rw [baseComap, Ideal.mem_comap]
  apply hW
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := Ω) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have hf' : mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) f = 0 := hf
  have h1 := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hf', map_zero] at h1
  exact h1

theorem ModelCurves.proof (hdim : ModelCurvesDim.Statement) (hlift : ModelCurvesLift.Statement) :
    ModelCurves.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy d
  refine ⟨fun W hW hyW hd => ⟨isMultiProjPrime_baseComap F k₀ e hW,
    mIdealOver_le_baseComap F y k₀ e hx hyW, ?_⟩, fun P hP hxP hd => ?_⟩
  · rw [hdim F K ι Ω y k₀ N e hy W hW hyW, hd]
  · obtain ⟨W, hW, hyW, rfl⟩ := hlift F K ι Ω y k₀ N e x hx hy P hP hxP
    exact ⟨W, hW, hyW, by rw [← hdim F K ι Ω y k₀ N e hy W hW hyW, hd], rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
