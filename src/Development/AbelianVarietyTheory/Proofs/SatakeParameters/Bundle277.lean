module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.AlgebraicWeights.InertDatumExists
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle298
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle253
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle233
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle252
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle244
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumExist

open scoped TensorProduct

theorem isCMExt (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
    fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩

theorem mem_tensInt_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    x ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (Formalism.UG.Ov F v) ↔
      Algebra.TensorProduct.comm F E (v.adicCompletion F) x ∈ GlobalTheory.AdelicU.intLoc F E v := by
  constructor
  · intro hx
    have hle : Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (Formalism.UG.Ov F v) ≤
        (GlobalTheory.AdelicU.intLoc F E v).comap (Algebra.TensorProduct.comm F E (v.adicCompletion F)).toRingHom := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · show Algebra.TensorProduct.comm F E _ (((a : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ GlobalTheory.AdelicU.intLoc F E v
        rw [Algebra.TensorProduct.comm_tmul]
        exact GlobalTheory.AdelicU.tmul_mem_intLoc (one_mem _) a
      · show Algebra.TensorProduct.comm F E _ ((1 : E) ⊗ₜ[F] y) ∈ GlobalTheory.AdelicU.intLoc F E v
        rw [Algebra.TensorProduct.comm_tmul]
        have := GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) hy (1 : 𝓞 E)
        simpa using this
    exact hle hx
  · intro hx
    have h := GlobalTheory.AdelicU.intLoc_induction
      (p := fun y => (Algebra.TensorProduct.comm F E (v.adicCompletion F)).symm y ∈
        Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (Formalism.UG.Ov F v))
      (fun a ha z => by
        have e1 : (Algebra.TensorProduct.comm F E (v.adicCompletion F)).symm (a ⊗ₜ[F] (z : E)) =
            ((z : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] a) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rfl
        rw [e1]
        exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨(z : E), z, rfl⟩, rfl⟩))
          (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)))
      (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
      (fun y hy => by rw [map_neg]; exact neg_mem hy) hx
    simpa using h

theorem exists_inertDatum : ∀ (D : D7) (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))),
    (∀ s : SplitPlace D.host.E, s.v ≠ v) → ∃ w : HeightOneSpectrum (𝓞 D.host.E), NG.OverPl w v ∧
      ¬ IsSplitPl D.host w ∧ Nonempty (InertDatum D.host.E n v w) := by
  intro D n v hv
  classical
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, fun h0 => v.ne_bot (by
    rw [hQv.over, h0]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _))⟩
  have hov : NG.OverPl w v := hQv.over.symm
  have hunder : w.under (𝓞 (maximalRealSubfield D.host.E)) = v := HeightOneSpectrum.ext hov
  have key : ∀ x ∈ w.asIdeal, IsCMField.ringOfIntegersComplexConj D.host.E x ∈ w.asIdeal := by
    intro x hx
    by_contra hc
    have hspl : IsSplitPl D.host w := ⟨x, hx, fun y hy hym => hc (by
      have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := by
        apply RingOfIntegers.ext
        rw [hy, IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.SplitPlaceOver.host_conj_eq']
      simpa [this] using hym)⟩
    obtain ⟨s, ϖ, hs, hϖ⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hspl
    apply hv s
    apply HeightOneSpectrum.ext
    rw [← s.w_under, ← hov]
    ext a
    have ha : D.host.conj ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) := by
      rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
      exact congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ((IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩)
    exact (hs _ _ ha.symm).symm
  have hnsp : ¬ IsSplitPl D.host w := by
    rintro ⟨x, hx, hy⟩
    exact hy _ (by rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.SplitPlaceOver.host_conj_eq']) (key x hx)
  have hnsa : ¬ GlobalTheory.UnitaryBC.IsSplitAt w := by
    rintro ⟨u, hne, hu⟩
    apply hne
    apply HeightOneSpectrum.ext
    apply u.isMaximal.eq_of_le w.isPrime.ne_top
    intro x hx
    by_contra hxw
    have hfix : IsCMField.ringOfIntegersComplexConj D.host.E (x * IsCMField.ringOfIntegersComplexConj D.host.E x) =
        x * IsCMField.ringOfIntegersComplexConj D.host.E x := by
      apply RingOfIntegers.ext
      simp [IsCMField.coe_ringOfIntegersComplexConj, mul_comm]
    obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
    have hcom := congrArg HeightOneSpectrum.asIdeal hu
    change u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) at hcom
    have hp : a ∈ u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      change algebraMap _ _ a ∈ u.asIdeal
      rw [ha]; exact u.asIdeal.mul_mem_right _ hx
    rw [hcom] at hp
    change algebraMap _ _ a ∈ w.asIdeal at hp
    rw [ha] at hp
    rcases w.isPrime.mem_or_mem hp with h | h
    · exact hxw h
    · apply hxw
      have hh := key _ h
      have he : IsCMField.ringOfIntegersComplexConj D.host.E (IsCMField.ringOfIntegersComplexConj D.host.E x) = x := by
        apply RingOfIntegers.ext
        simp [IsCMField.coe_ringOfIntegersComplexConj]
      rwa [he] at hh
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield D.host.E) D.host.E v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w (GlobalTheory.DefiniteBC.host_unramified D.host w) hnsa
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj D.host.E).toAlgHom hw hunder
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (isCMExt D.host.E) hw hc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov D.host.E w = Formalism.UG.intL (w.adicCompletion D.host.E) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield D.host.E) D.host.E
    (v.adicCompletion (maximalRealSubfield D.host.E))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨w, hov, hnsp, ⟨⟨e, c, ϖ, k, ?_, hU, ?_, ?_, ?_⟩⟩⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj D.host.E).toAlgHom _ x)) =
      c (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

end GlobalTheory.InertDatumExist

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaPrimeHecke

open Formalism.L2.Host _root_.Formalism.L2.Col

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : HChar L) (Q : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt Q) (k : Lˣ) (hk : Q.valuation L (k : L) = WithZero.exp (-1 : ℤ)) :
    χ.locK Q k = χ.val Q := by
  have h1 : Valued.v ((atFin Q k : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    rw [← hk]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : L)
  have h2 : Valued.v ((atFin Q (unif Q) : (Q.adicCompletion L)ˣ) : Q.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec Q
  have h3 : IsUnitAt Q (atFin Q k * (atFin Q (unif Q))⁻¹) := by
    show Valued.v _ = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h1, h2, mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h4 := hu _ h3
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4

theorem exists_unif {L : Type} [Field L] [NumberField L] (Q : HeightOneSpectrum (𝓞 L)) :
    ∃ ϖ : 𝓞 L, ϖ ∈ Q.asIdeal ∧ ϖ ∉ Q.asIdeal ^ 2 ∧ Q.valuation L (ϖ : L) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨ϖ, h⟩ := Q.intValuation_exists_uniformizer
  refine ⟨ϖ, ?_, ?_, ?_⟩
  · rw [← Q.intValuation_lt_one_iff_mem, h, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · rw [← Q.intValuation_le_pow_iff_mem, h, WithZero.exp_le_exp]; norm_num
  · rw [← h]; exact Q.valuation_of_algebraMap ϖ

theorem poly_id (q r t : ℕ) (u v : ℂ) (a : ℕ → ℂ) :
    heckePolyOf (r + t) q (fun k => ∑ j ∈ Finset.range (r + 1),
      (if j ≤ k then (q : ℂ) ^ ((r - j) * (k - j)) * (gaussBin q t (k - j) : ℂ) * u⁻¹ ^ k * v ^ j else 0) * a j) =
    (heckePolyOf r q a).comp (C (u⁻¹ * v) * X) * blockPoly (u⁻¹ * (q : ℂ) ^ r) q t := by
  have key := GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv.2 ℂ q r t (fun j => if j ≤ r then a j else 0) u⁻¹ (u⁻¹ * v)
    (fun j hj => if_neg (by omega))
  have h1 : heckePolyOf r q (fun j => if j ≤ r then a j else 0) = heckePolyOf r q a := by
    unfold heckePolyOf
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [if_pos (show j ≤ r by simpa [Nat.lt_succ_iff] using hj)]
  rw [h1] at key
  rw [← key]
  congr 1
  funext k
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_congr (by ext j; simp [Nat.lt_succ_iff, and_comm]) fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using (Finset.mem_filter.1 hj).1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left, pow_add, mul_pow]
  ring

variable {D : D7}

theorem not_isConjPl {P : Pl D.host.E} (h : _root_.Formalism.DivisionValues.conjPl P ≠ P) : ¬ Formalism.IndefR.Lev.IsConjPl P P := by
  intro hc
  apply h
  refine HeightOneSpectrum.ext ((_root_.Formalism.DivisionValues.conjPl P).isMaximal.eq_of_le P.isPrime.ne_top ?_)
  refine Ideal.map_le_iff_le_comap.2 fun c hcP => ?_
  obtain ⟨c', hc', he⟩ := hc c hcP
  have : Formalism.DivisionValues.cO D.host.E c = c' := RingOfIntegers.ext he.symm
  rw [Ideal.mem_comap, this]
  exact hc'

theorem unrPl_mul_inv {P : Pl D.host.E} {a b : (AE D)ˣ →* Circle} (ha : UnrPl P a) (hb : UnrPl P b) : UnrPl P (a * b⁻¹) := by
  intro e f h x h1 h2 h3
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha e f h x h1 h2 h3, hb e f h x h1 h2 h3, inv_one, mul_one]

theorem consts (μ η ηa q s : ℂ) (hμ : μ ≠ 0) (hη : η ≠ 0) (hs : s ≠ 0) (hq : s * s = q) (he : ηa = η * s⁻¹) (r t : ℕ)
    (hr : Odd r) (ht : Odd t) :
    (μ * η⁻¹ * s ^ r)⁻¹ * (μ * s ^ (r + t)) = ηa * q ^ ((t + 1) / 2) ∧
      (μ * η⁻¹ * s ^ r)⁻¹ * q ^ r = μ⁻¹ * ηa * q ^ ((r + 1) / 2) := by
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := ht
  rw [show (2 * a + 1 + 1) / 2 = a + 1 by omega, show (2 * b + 1 + 1) / 2 = b + 1 by omega, he, ← hq]
  constructor
  · field_simp
    ring
  · field_simp
    ring



theorem transfer_and_heckePoly : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ (Vc D i).rank → MatchW R i t (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) (splitC (Wc D i).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf (Vc D i).rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Wc D i).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Wc D i).rank (A.q P) a).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) * ((A.fam.L i t).blockProd P).map D.what₂.embLL := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hc hS i t P
  obtain ⟨hQ0, hG, -, hF⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hc.lev
  obtain ⟨hgood, hsplit, hq⟩ := hF hc.fam t P P.2
  obtain ⟨hunη, hunμ⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hc.lev t _ hgood
  obtain ⟨gramR, c0R, c0L, tie⟩ := hc.fam.tie
  obtain ⟨-, hAr, hAt⟩ := tie.ranks
  have hP0 : (P : Pl0) ∈ A.ok A.μ0 := by
    have h := (tie.ok t P).1 P.2
    rw [tie.ok, hQ0]
    simp only [Finset.coe_empty, Set.union_empty]
    exact ⟨h.1, fun h' => h.2.1 (Or.inl h'), fun Q hQ => h.2.2 Q (Or.inl hQ)⟩
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (not_isConjPl hsplit)
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ3⟩ := exists_unif (R.pl P)
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ3
    exact WithZero.exp_ne_zero hϖ3.symm
  have hpl : Formalism.L2.JoinChr.IsPlIdem D e (R.pl P) := by
    obtain ⟨⟨h1, h2, v, ε, h3, h4⟩, h5⟩ := he
    exact ⟨h1, ⟨v, ε, h3, Or.inl ⟨h2, h4⟩⟩, h5⟩
  let x : (AE D)ˣ := Formalism.L2.JoinChr.locU hpl.1 (Units.mk0 _ hϖ0)
  have hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (Units.mk0 _ hϖ0 : D.host.Eˣ) := rfl
  have hx' : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
    rw [hx, Formalism.L2.JoinChr.locE, Units.val_mk0]
    ring
  have hun1 := hunμ ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  obtain ⟨hfix, hM⟩ := GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace R.ψ _ _ _ _ _ (R.pl P) (hc.thP.ωP i t) hsplit hun1 (unrPl_mul_inv hun1 hunη)
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hV : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [hW]
    exact D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hM' := (hM e ϖ x D.R.t he hϖ1 hϖ2 hx').2 hV
  refine ⟨_, fun k hk => GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke R F hc hS i t _ hgood hfix _ _ (hM' k hk), fun a => ?_⟩

  have hu0 : (R.C.mu0 i).UnrAt (R.pl P) := by
    refine (R.C.isMu0 i).unr _ fun k hk => (hG t _ hgood).1 ?_
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk
    · exact Ideal.mul_mem_left _ _ hk
  have huξ : (R.xiH t).UnrAt (R.pl P) := by
    by_contra h
    rcases (hc.lev.Q_ram t _).1 h with h | ⟨PP, h1, h2⟩
    · exact (hgood _ (Or.inr h)).1 rfl
    · exact (hgood _ (Or.inr h1)).2 h2
  have hη : ((R.eta x : Circle) : ℂ) = (R.C.eta.val (R.pl P) : ℂˣ) := by
    rw [hc.lev.eta.2 _ e hpl _ x hx, locK_eq_val _ _ (R.C.isEta.unr _) _ hϖ3]
  have hμ : ((R.toLevCh.mu t ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (A.muVal i t P : D.what₂.LL) := by
    rw [hc.fam.muVal i t P P.2, HChar.val_mul, Units.val_mul, ← locK_eq_val _ _ hu0 (Units.mk0 _ hϖ0) hϖ3,
      ← locK_eq_val _ _ huξ (Units.mk0 _ hϖ0) hϖ3, ← (hc.lev.mu0 i).2 _ e hpl _ x hx, ← (hc.lev.xi t).2 _ e hpl _ x hx,
      ← Circle.coe_mul]
    rfl
  have hN : (0 : ℝ) < (Ideal.absNorm (R.pl P).asIdeal : ℕ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  have hs0 : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hN).ne'
  have hss : ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ) = (Ideal.absNorm (R.pl P).asIdeal : ℕ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le, Complex.ofReal_natCast]
  have hηa : D.what₂.embLL (A.etaVal P : D.what₂.LL) =
      ((R.eta x : Circle) : ℂ) * ((Real.sqrt (Ideal.absNorm (R.pl P).asIdeal : ℕ) : ℝ) : ℂ)⁻¹ := by
    rw [hc.fam.etaVal P hP0, hη, etaAlg, HChar.valTw, Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow hN.le,
      Complex.ofReal_natCast]
  have hr : Odd (Wc D i).rank := by
    rw [hW]
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
  obtain ⟨c1, c2⟩ := consts _ _ _ _ _ (Circle.coe_ne_zero (R.toLevCh.mu t ((i : ℕ) + 1) x)) (Circle.coe_ne_zero (R.eta x))
    hs0 hss hηa _ _ hr D.R.t_odd
  have hB : ((A.fam.L i t).blockProd P).map D.what₂.embLL =
      blockPoly (D.what₂.embLL (firstValA (A.muVal i t) A.etaVal A.q A.r P)) (A.q P) A.t := by
    rw [← map_blockPoly]
    simp [BlockDat.blockProd, FamIn.fam, liftDat]
  rw [hB, firstValA, map_mul D.what₂.embLL, map_mul D.what₂.embLL, Units.val_inv_eq_inv_val, map_inv₀, map_pow D.what₂.embLL, map_natCast D.what₂.embLL, ← hμ,
    hAr, hAt, hq, ← hW,
    ← c1, ← c2]
  simp only [Lift.chrTh, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [hV]
  exact poly_id _ _ _ _ _ a

end GlobalTheory.ThetaPrimeHecke
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem leftSide_odd_grp {M : Type} [CommGroup M] (u e d d' e' : M) (n : ℕ) (c s w : ℤ) (hu : u = e' * d'⁻¹) (he : e * e = 1) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  subst hu
  apply Additive.ofMul.injective
  have he' : Additive.ofMul e + Additive.ofMul e = 0 := by rw [← ofMul_mul, he]; rfl
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv]
  linear_combination (norm := module) (c - w) • he'

theorem leftSide_odd (u e d d' e' : ℂ) (n : ℕ) (c s w : ℤ) (hd : d ≠ 0) (hd' : d' ≠ 0) (he : e * e = 1) (he' : e' * e' = 1)
    (hu : u = e' * d'⁻¹) :
    (u ^ ((n : ℤ) - 1) * e * d) ^ ((n : ℤ) * c - s) * (u ^ (c - s) * (u ^ n * e * d) ^ (c - (n : ℤ) * c + s)) * u ^ (w - c) * d ^ (-w)
      = (e * e') ^ w * d' ^ (-w) * (e * d⁻¹) ^ (w - c) := by
  have he0 : e ≠ 0 := left_ne_zero_of_mul_eq_one he
  have he0' : e' ≠ 0 := left_ne_zero_of_mul_eq_one he'
  have h := leftSide_odd_grp (Units.mk0 e' he0' * (Units.mk0 d' hd')⁻¹) (Units.mk0 e he0) (Units.mk0 d hd) (Units.mk0 d' hd')
    (Units.mk0 e' he0') n c s w rfl (Units.ext (by simpa using he))
  have h2 := congrArg Units.val h
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0] at h2
  subst hu
  exact h2

theorem leftSide_sgRev_sq (n : ℕ) : sgRev n * sgRev n = 1 := by
  unfold sgRev
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem leftSide_det_zT_odd {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = sgRev n * ((f τ).det)⁻¹ := by
  unfold zT
  rw [if_pos h]
  have := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) ((f τ)⁻¹).transpose
  rw [show (⇑(Fin.revPerm : Equiv.Perm (Fin n))) = Fin.rev from rfl] at this
  rw [this, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rfl

theorem leftSide_zT_even {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (h : ¬ IsOddPos (pos.symm τ).2) :
    zT X D pos f τ = f τ := by
  unfold zT; rw [if_neg h]

end GlobalTheory.TwV.DelA
end

namespace GlobalTheory.TwV.DelA

theorem leftSide_at_point : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G * numD X Kc j) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = evD X D pos ι hN d f' (denD X Kc j) * ι (sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hG d f' hf' hdf
  have hodd := GlobalTheory.T.modelPolynomial_oddDegree_of_realisesFramePoly X D pos Kc ι j hN ν hν Q hQ Gc G hR hG
  have hsub := GlobalTheory.T.substituted_value_at_complex_point_oddBlocks X D pos Kc ι j hN Gc G hG hodd d f' hf' hdf
  have hnum := GlobalTheory.T.numerator_div_denominator_at_complex_point X D pos Kc ι j hN d f' hf' hdf
  have hex := GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j
  have hnn := (GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν).2.2.2.2
  have hR' := hR ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩
  have hR2 := (ev1_eq_prod_det_pow_mul_valZ X D pos j (rkS X D hN) Gc ⟨dfr X D hN d f', fun τ => (hdf τ).isUnit⟩).symm.trans hR'
  clear hR'
  simp only at hR2
  rw [map_mul, hsub, hnum]
  have gen : ∀ (x y z : ℂ) (E : Kc), ι x * (E * ι y) * ι z = E * ι (x * y * z) := by
    intro x y z E; simp only [map_mul]; ring
  rw [gen]
  congr 2
  have hW : (∏ τ, (dfr X D hN d f' τ).det ^ (-(wT X D pos j τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdf τ)
  have key : ∀ A V B P' S W' q Pj Wf : ℂ, Wf ≠ 0 → A * B * P' * Wf = S * W' * Pj → Pj * V = Wf * q →
      A * V * B * P' = S * W' * q := by
    intro A V B P' S W' q Pj Wf hWf hK hP
    apply mul_right_cancel₀ hWf
    linear_combination V * hK + S * W' * hP
  refine key _ _ _ _ _ _ _ _ _ hW ?_ hR2
  unfold sgO
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨h1, h2⟩ := hex τ
  by_cases ho : IsOddPos (pos.symm τ).2
  · simp only [if_pos ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_det_zT_odd X D pos f' τ ho, leftSide_det_zT_odd X D pos (dfr X D hN d f') τ ho]
    exact leftSide_odd _ _ _ _ _ _ _ _ _ (hdf τ) (hf' τ) (leftSide_sgRev_sq _) (leftSide_sgRev_sq _) rfl
  · simp only [if_neg ho] at h1 h2 ⊢
    rw [h1, h2, leftSide_zT_even X D pos f' τ ho, leftSide_zT_even X D pos (dfr X D hN d f') τ ho, ← zpow_natCast,
      Int.toNat_of_nonneg (hnn τ), zpow_sub₀ (hdf τ)]
    simp only [zpow_neg]
    ring

end GlobalTheory.TwV.DelA
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_polynomials_weight_realised_next_level : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) {n : ℕ} (h : (X.Pj (j + 1)).m + 1 = n) (ν : D.what₂.Tau → Fin n → ℕ), (∀ τ r, (ν τ r : ℤ) ≤ cT1 X D pos j τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ R, Realises X D pos (j + 1) h (wT X D pos j) Q R := by
  first | exact @GlobalTheory.TwV.DelA.realises_of_wtPol | exact GlobalTheory.TwV.DelA.realises_of_wtPol | (intros; apply GlobalTheory.TwV.DelA.realises_of_wtPol <;> assumption)
end
