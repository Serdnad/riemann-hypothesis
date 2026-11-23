module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle075
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

theorem EuclideanSectionsPower.proof (hL : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) :
    EuclideanSectionsPower.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hc
  obtain ⟨μ, m, hμ, hcon, hZ, hm, hdeg⟩ := hP K ι Ω y D A P0 II hD hII har hb hA hc
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, hnorm⟩ :=
    hL K ι Ω y D A har hb hA.semipos.1.continuousOn μ hμ hcon hZ
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, m, hm, fun ε hε => ?_⟩
  filter_upwards [hdeg ε hε] with q hq
  intro _ _
  exact hq (r (m * q)) (φ (m * q)) (hinj _) (hnorm _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGraphDeg

theorem isMultiHomog_blockForms {K : Type} [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {κ : Type}
    (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (q : Σ k, GlobalTheory κ k) :
    IsMultiHomog (blockForms k₀ M q) (blockDeg k₀ 1) := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  by_cases hk : k = k₀
  · subst hk
    simp [blockDeg, Finsupp.single_apply]
  · simp [blockDeg, hk, Sigma.ext_iff]

theorem x'_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} [Fintype K₂]
    {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}
    (G : GenFibre (inrV (ι := ι) (ι₂ := ι₂)) (graphIdeal P g)) (k : K) (i : ι k)
    (hi : (X ⟨k, i⟩ : MRing ι) ∉ P) : G.x' ⟨Sum.inl k, i⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl k, i⟩ : MRing (Sum.elim ι ι₂)) ∈ graphIdeal P g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  exact hi (Ideal.Quotient.eq_zero_iff_mem.1 (MvPolynomial.C_eq_zero.1 h1))

end BlockGraphDeg


open BlockGraphDeg in
theorem BlockGraphDeg.proof (hGr : GraphStatement) (hImg : BlockGraphImage.Statement)
    (hEx : GenFibreExistsStatement) (hDim : FibreDimStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hCR : Inter.ChartRankAdjoin.Statement) (hRat : BlockGraphFibreRatio.Statement) :
    BlockGraphDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hy hB hx hI
  have hImage := hImg K ι Ω κ y k₀ M N x hI
  have hIm : IsArithVar (imageZ (inrV (ι := ι) (ι₂ := GlobalTheory κ))
      (graphIdeal (mCoordIdeal y) (blockForms k₀ M))) (D + 1) := by
    rw [hImage]
    exact hx

  have hnv : ∀ u : Unit, ∃ j, blockForms k₀ M ⟨u, j⟩ ∉ mCoordIdeal y := by
    intro u
    obtain ⟨j, hj⟩ := hIm.2.1.2.2 u
    refine ⟨j, fun hm => hj ?_⟩
    rw [imageZ, Ideal.mem_comap]
    change rename inrV (X ⟨u, j⟩) ∈ _
    rw [rename_X, graphIdeal, RingHom.mem_ker, inrV, graphMap, eval₂Hom_X']
    change C (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨u, j⟩)) * X u = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero, zero_mul]
  have hΓ := (hGr K ι Unit (GlobalTheory κ) (mCoordIdeal y) (D + 1) (blockForms k₀ M) (fun _ => blockDeg k₀ 1) hy
    (isMultiHomog_blockForms k₀ M) hnv).1
  obtain ⟨G⟩ := hEx Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) isBlockMap_inr hΓ
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr)
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (GlobalTheory κ) (K ⊕ Unit) (Sum.elim ι (GlobalTheory κ)) Sum.inr inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm

  choose c hc using hy.2.1.2.2
  let ch : (k : FibreBlock (Sum.inr : Unit → K ⊕ Unit)) → fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k := fun
    | ⟨Sum.inl k, _⟩ => c k
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(k | u), h⟩
    · exact x'_ne_zero G k (c k) (hc k)
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := hCR (FibreBlock (Sum.inr : Unit → K ⊕ Unit)) (fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr) G.Φ G.Φ'
    (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → K ⊕ Unit),
      fibreIdx (Sum.elim ι (GlobalTheory κ)) Sum.inr k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(k | u), h⟩, i⟩, rfl⟩
    · exact IntermediateField.mem_bot.2 (hRat D K ι Ω κ y k₀ M N x hy hB hI G k i (c k) (x'_ne_zero G k (c k) (hc k)))
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreRelLift

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (ℓ : ℕ)

def ratio (p : Σ k, ι k) : chartRingZ y c :=
  ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩

def dehom : MRing ι →ₐ[ℤ] chartRingZ y c := aeval (ratio y c)

theorem coe_dehom (f : MRing ι) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y f) := by
  show ((chartRingZ y c).val.toRingHom.comp (dehom y c).toRingHom) f =
    ((aeval (fun k => (y ⟨k, c k⟩)⁻¹) : MvPolynomial K Ω →ₐ[Ω] Ω).toRingHom.comp (mConeMap y).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp
  · simp [dehom, ratio, mConeMap, div_eq_mul_inv]

theorem coe_dehom_of_homog {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    ((dehom y c f : chartRingZ y c) : Ω) = aeval y f * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
  rw [coe_dehom, ProjLine.mConeMap_eq_of_isMultiHomog y hf, map_mul, aeval_C, map_prod]
  simp only [map_pow, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

theorem dehom_eq_zero {f : MRing ι} (hf : f ∈ mCoordIdeal y) : dehom y c f = 0 := by
  have h0 : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  apply Subtype.ext
  rw [coe_dehom, h0]
  simp

abbrev ChartQ := chartRingZ y c ⧸ Ideal.span {((ℓ : ℕ) : chartRingZ y c)}

theorem natCast_chartQ : ((ℓ : ℕ) : ChartQ y c ℓ) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})) ℓ]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

def dehomMod : MRingOver (ZMod ℓ) ι →+* ChartQ y c ℓ :=
  eval₂Hom (ZMod.castHom (ringChar.dvd (natCast_chartQ y c ℓ)) (ChartQ y c ℓ))
    (fun p => Ideal.Quotient.mk _ (ratio y c p))

theorem dehomMod_map (f : MRing ι) :
    dehomMod y c ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) f) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) (dehom y c f) := by
  show ((dehomMod y c ℓ).comp (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))) f =
    ((Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})).comp (dehom y c).toRingHom) f
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)) f
  · simp [dehomMod]
  · simp [dehomMod, dehom]

theorem idealOver_le_ker : GenOnFibres.idealOver y (ZMod ℓ) ≤ RingHom.ker (dehomMod y c ℓ) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  rw [Ideal.mem_comap, RingHom.mem_ker, dehomMod_map, dehom_eq_zero y c hf, map_zero]

def dehomQuot : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ) →+* ChartQ y c ℓ :=
  Ideal.Quotient.lift _ (dehomMod y c ℓ) fun _ hf => RingHom.mem_ker.mp (idealOver_le_ker y c ℓ hf)

theorem dehomQuot_smul (r : MRingOver (ZMod ℓ) ι) (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) :
    dehomQuot y c ℓ (r • m) = dehomMod y c ℓ r * dehomQuot y c ℓ m := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [GenOnFibres.smul_mk, dehomQuot, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, map_mul]

theorem dehomMod_cellMon (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, i = c k)
    {t : MRingOver (ZMod ℓ) ι} (ht : t ∈ KH.cellMon (ZMod ℓ) I) : dehomMod y c ℓ t = 1 := by
  have hle : KH.cellMon (ZMod ℓ) I ≤ (⊥ : Submonoid (ChartQ y c ℓ)).comap (dehomMod y c ℓ).toMonoidHom := by
    unfold KH.cellMon
    refine Submonoid.closure_le.mpr ?_
    rintro f ⟨k, i, hi, rfl⟩
    obtain rfl := hI k i hi
    have h1 : ratio y c ⟨k, c k⟩ = 1 := Subtype.ext (by simp [ratio, div_self (hc k)])
    rw [SetLike.mem_coe, Submonoid.mem_comap, Submonoid.mem_bot]
    simp [dehomMod, h1]
  exact Submonoid.mem_bot.mp (hle ht)

variable {y c ℓ}

def dehomLocFun (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (x : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) : ChartQ y c ℓ :=
  x.liftOn (fun p => dehomQuot y c ℓ p.1) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    have h := congrArg (dehomQuot y c ℓ) hu
    simp only [Submonoid.smul_def, dehomQuot_smul, hT _ u.2, hT _ s.2, hT _ s'.2, one_mul] at h
    exact h)

theorem dehomLocFun_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLocFun T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m := by
  unfold dehomLocFun
  rw [LocalizedModule.liftOn_mk]

def dehomLoc (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1) :
    LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) →+* ChartQ y c ℓ where
  toFun := dehomLocFun T hT
  map_one' := by
    rw [show (1 : LocalizedModule T (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))) =
      LocalizedModule.mk 1 1 by rw [OreLocalization.one_def], dehomLocFun_mk, map_one]
  map_mul' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_mul_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk, map_mul]
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, dehomLocFun_mk, map_zero]
  map_add' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, dehomLocFun_mk, dehomLocFun_mk, dehomLocFun_mk,
        (dehomQuot y c ℓ).map_add,
        Submonoid.smul_def, Submonoid.smul_def, dehomQuot_smul, dehomQuot_smul, hT _ s.2, hT _ s'.2,
        one_mul, one_mul]

theorem dehomLoc_mk (T : Submonoid (MRingOver (ZMod ℓ) ι)) (hT : ∀ t ∈ T, dehomMod y c ℓ t = 1)
    (m : MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ)) (t : T) :
    dehomLoc T hT (LocalizedModule.mk m t) = dehomQuot y c ℓ m :=
  dehomLocFun_mk T hT m t

end FibreRelLift


open FibreRelLift in
theorem FibreRelLift.proof : FibreRelLift.Statement := by
  intro K _ _ ι _ _ Ω _ y ℓ a r s J u hs hc _ hrel
  set c := GenOnFibres.cellChart J with hcdef
  have hI : ∀ k, ∀ i ∈ J.1 k, i = c k := by
    intro k i hi
    have h1 : (J.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
    exact Finset.card_le_one.mp (by omega) i hi (c k) (GenOnFibres.cellChart_mem J k)
  have hT : ∀ t ∈ KH.cellMon (ZMod ℓ) J.1, dehomMod y c ℓ t = 1 := fun t ht =>
    dehomMod_cellMon y c ℓ hc hI ht
  have hw : ∀ j, s j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := fun j => by
    simpa using hs j c hc
  have hz : ∀ j, dehomLoc _ hT (GenOnFibres.secCoch y (ZMod ℓ) (s j) a J) =
      Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)}) ⟨_, hw j⟩ := by
    intro j
    obtain ⟨e, F, ⟨d, hF, hd, hv⟩, h, he⟩ := GenOnFibres.secCoch_spec (S := ZMod ℓ) (hs j) J hc
    rw [he, dehomLoc_mk, dehomQuot, Ideal.Quotient.lift_mk, dehomMod_map]
    congr 1
    apply Subtype.ext
    rw [coe_dehom_of_homog y c hF, hv, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hc k)]
    congr 1
    have := hd k
    omega
  have h1 := congrArg (dehomLoc _ hT) hrel
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one] at h1
  simp only [map_mul, hz] at h1
  choose b hb using fun j => Ideal.Quotient.mk_surjective (dehomLoc _ hT (u j))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← hb, ← map_mul, ← map_sum] at h1
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {((ℓ : ℕ) : chartRingZ y c)})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨q, hq⟩ := h1
  refine ⟨fun j => (b j : Ω), -(q : Ω), fun j => (b j).2, neg_mem q.2, ?_⟩
  have h2 := congrArg (fun x : chartRingZ y c => (x : Ω)) hq
  push_cast at h2
  linear_combination (-1 : Ω) * h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory

theorem TensorPowerL2Degree.proof (hDat : PowerBlockDatum.Statement) (hTop : PowerBlockTop.Statement)
    (hChi : BlockChiCovolume.Statement) (hHS : TheoremHSMBlock.Statement) : TensorPowerL2Degree.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD1 hII har hb hA hc
  classical
  obtain ⟨m, N, v, d, μ, hm, hdy, hk, hv, hgen, hmet, hlat, hμ, hnull, hZ, hnorm⟩ :=
    hDat K ι Ω y D A P0 hD1 har hb hA hc
  have htop : II (Option K) (addIdx ι N) (mCoordIdeal d.y) (D + 1) (fun _ => d.A) =
      (m : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => A) := by
    rw [hdy]
    refine hTop K ι Ω y D A m N v d.A II hII har hA.semipos.1 hm hv hgen (by rw [d.deg, hk]) d.semipos.1 ?_
    rw [← hdy]
    exact hmet
  obtain ⟨hdef, -⟩ := hHS D (Option K) (addIdx ι N) Ω II d hII
  refine ⟨μ, m, hμ, hnull, hZ, hm, fun ε hε => ?_⟩
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hmpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast hm) _
  have hc' : 0 < ε * (m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  filter_upwards [hdef.bound hc', hlat] with q hq hl
  intro r ψ hψ hiso _ _
  have hcov := hChi D (Option K) (addIdx ι N) Ω d q (chartLat y A.a (m * q)) (by rw [hk]; exact hl) r ψ hψ
    (fun s f hf hs => by
      rw [hk] at hf
      rw [hiso, ← hs]
      exact hnorm q f hf)
  rw [hcov]
  rw [htop] at hq
  simp only [hsDefect, pw, Real.norm_eq_abs] at hq
  have hq' := (abs_le.mp hq).2
  rw [abs_of_nonneg (by positivity)] at hq'
  push_cast
  rw [mul_pow]
  have key : (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
      ((m : ℝ) ^ (D + 1) * (q : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      (m : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => A) * (q : ℝ) ^ (D + 1) /
          ((D + 1).factorial : ℝ) +
        ε * (m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) * (q : ℝ) ^ (D + 1) := by
    ring
  rw [key]
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SecCochReduce.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (p : ℕ) (a : K → ℤ),
    ∀ s ∈ chartLat y a 1,
      FibreReduction.redCoch y p 0 (GenOnFibres.secCoch y ℤ s a) = GenOnFibres.secCoch y (ZMod p) s a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
