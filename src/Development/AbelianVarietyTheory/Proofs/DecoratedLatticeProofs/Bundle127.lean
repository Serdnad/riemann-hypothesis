module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle336
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.HaarCoord

theorem measurePreserving_skew_add {A B : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [μ.IsAddLeftInvariant] {f : B → A} (hf : Measurable f) :
    MeasurePreserving (fun p : A × B => (f p.2 + p.1, p.2)) (μ.prod ν) (μ.prod ν) := by
  have h : MeasurePreserving (fun p : B × A => (id p.1, f p.1 + p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun b a => f b + a)
      ((hf.comp measurable_fst).add measurable_snd) (Filter.Eventually.of_forall fun b => map_add_left_eq_self μ (f b))
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

theorem isMulRightInvariant_map {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X) (e : X ≃ᵐ G)
    (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e p * e q) : (P.map e).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have hg : (fun x : G => x * g) = e ∘ T ∘ e.symm := by
    funext x
    simp only [Function.comp, hTe, e.apply_symm_apply]
  rw [hg]
  have h1 : MeasurePreserving e P (P.map e) := ⟨e.measurable, rfl⟩
  exact (h1.comp (hT.comp (h1.symm e))).map_eq

theorem coord_mul {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (c c' : skewA D ρ) (b b' : Mx D ρ V₀.rank)
    (u u' : GL (Fin ρ) (AE D)) :
    d.nC ((skewConj u.1 c' + cComm V₀ b (u.1 ⬝ b')) + c) * (d.nB (u.1 ⬝ b' + b) * d.levi (u * u')) =
      d.nC c * (d.nB b * d.levi u) * (d.nC c' * (d.nB b' * d.levi u')) := by
  have h1 : d.levi u * (d.nC c' * (d.nB b' * d.levi u')) =
      d.nC (skewConj u.1 c') * (d.nB (u.1 ⬝ b') * d.levi (u * u')) := by
    rw [← mul_assoc, d.levi_mul_nC, mul_assoc, ← mul_assoc (d.levi u), d.levi_mul_nB, mul_assoc, map_mul]
  rw [mul_assoc, mul_assoc, h1, ← mul_assoc (d.nB b), ← d.nC_mul_nB, mul_assoc, ← mul_assoc (d.nB b), d.nB_mul_nB,
    ← d.nC_mul_nB, add_comm _ c, add_comm _ b, d.nC_add, d.nC_add]
  simp only [mul_assoc]

theorem measurableAdd₂_addSubgroup {A : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] (H : AddSubgroup A) :
    MeasurableAdd₂ H :=
  ⟨Measurable.subtype_mk ((measurable_subtype_coe.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd))⟩

theorem measurePreserving_triple {A B U : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [AddGroup B]
    [MeasurableSpace B] [MeasurableAdd₂ B] [Mul U] [MeasurableSpace U] [MeasurableMul U]
    (l : Measure A) (μ : Measure B) (ν : Measure U) [SFinite l] [SFinite μ] [SFinite ν] [l.IsAddLeftInvariant]
    [μ.IsAddLeftInvariant] [ν.IsMulRightInvariant] {f : B × U → A} (hf : Measurable f) {g : U → B} (hg : Measurable g)
    (u' : U) :
    MeasurePreserving (fun p : A × (B × U) => (f p.2 + p.1, (g p.2.2 + p.2.1, p.2.2 * u')))
      (l.prod (μ.prod ν)) (l.prod (μ.prod ν)) := by
  have T1 := measurePreserving_skew_add l (μ.prod ν) hf
  have T2 := (MeasurePreserving.id l).prod (measurePreserving_skew_add μ ν hg)
  have T3 := (MeasurePreserving.id l).prod ((MeasurePreserving.id μ).prod (measurePreserving_mul_right ν u'))
  exact T3.comp (T2.comp T1)

theorem continuous_UX_val (D : D7) (ρ : ℕ) : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_UX_mul {D : D7} {ρ n : ℕ} (b' : Mx D ρ n) : Continuous fun u : UX D ρ => (u.1.1 ⬝ b' : Mx D ρ n) :=
  (continuous_UX_val D ρ).matrix_mul continuous_const

theorem continuous_skewConj {D : D7} {ρ : ℕ} (c' : skewA D ρ) : Continuous fun a : Mx D ρ ρ => skewConj a c' := by
  have h1 : Continuous fun a : Mx D ρ ρ => (a ⬝ c'.1 : Mx D ρ ρ) := continuous_id.matrix_mul continuous_const
  have h2 : Continuous fun a : Mx D ρ ρ => (a ⬝ c'.1 ⬝ adj a : Mx D ρ ρ) := h1.matrix_mul continuous_adj
  exact Continuous.subtype_mk h2 _

theorem continuous_cComm {D : D7} (V₀ : HSp D) (ρ : ℕ) :
    Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => cComm V₀ x.1 x.2 := by
  have := (lattice_Mx D ρ ρ).1
  have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
  have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
  have h1 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => (x.2 ⬝ plus V₀ x.1 : Mx D ρ ρ) :=
    continuous_snd.matrix_mul (hp.comp continuous_fst)
  have h2 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => (x.1 ⬝ plus V₀ x.2 : Mx D ρ ρ) :=
    continuous_fst.matrix_mul (hp.comp continuous_snd)
  have h3 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank =>
      (half D • (x.2 ⬝ plus V₀ x.1 - x.1 ⬝ plus V₀ x.2) : Mx D ρ ρ) := (h1.sub h2).const_smul (half D)
  exact Continuous.subtype_mk h3 _


theorem continuous_shift {D : D7} (V₀ : HSp D) (ρ : ℕ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) :
    Continuous fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' + cComm V₀ y.1 (y.2.1.1 ⬝ b') := by
  have := (lattice_Mx D ρ ρ).1
  have h1 : Continuous fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' :=
    (continuous_skewConj c').comp (f := fun y : Mx D ρ V₀.rank × UX D ρ => y.2.1.1)
      ((continuous_UX_val D ρ).comp continuous_snd)
  have h2 : Continuous fun y : Mx D ρ V₀.rank × UX D ρ => cComm V₀ y.1 (y.2.1.1 ⬝ b') :=
    (continuous_cComm V₀ ρ).comp (f := fun y : Mx D ρ V₀.rank × UX D ρ => (y.1, (y.2.1.1 ⬝ b' : Mx D ρ V₀.rank)))
      (continuous_fst.prodMk ((continuous_UX_mul b').comp continuous_snd))
  exact h1.add h2


theorem measurable_shift {D : D7} (V₀ : HSp D) (ρ : ℕ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) :
    Measurable fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' + cComm V₀ y.1 (y.2.1.1 ⬝ b') := by
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  exact (continuous_shift V₀ ρ c' b').measurable




theorem isMulRightInvariant_map_coord : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → ((lC.prod (vb.μ.prod vU.ν)).map e).IsMulRightInvariant := by
  intro D V V₀ ρ d vb vU e he lC hC hS
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D ρ ρ
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := vb.covol.1
  have := vU.unit.1
  have : vU.ν.IsMulRightInvariant := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ vU.unit
  have : SFinite vb.μ := inferInstance
  have hSFiniteU : SFinite vU.ν := by
    letI : LocallyCompactSpace (UX D ρ) := u1
    letI : SecondCountableTopology (UX D ρ) := u2
    letI : vU.ν.IsHaarMeasure := vU.unit.1
    exact @MeasureTheory.instSFiniteOfSigmaFinite _ _ vU.ν (Measure.IsHaarMeasure.sigmaFinite vU.ν)
  have : MeasurableAdd₂ (Mx D ρ ρ) := inferInstance
  have : MeasurableAdd₂ (skewA D ρ) := measurableAdd₂_addSubgroup _
  have : MeasurableAdd₂ (Mx D ρ V₀.rank) := inferInstance
  have : MeasurableMul (UX D ρ) := inferInstance
  refine isMulRightInvariant_map _ e ?_
  rintro ⟨c', b', u'⟩
  refine ⟨_, measurePreserving_triple lC vb.μ vU.ν (measurable_shift V₀ ρ c' b') (continuous_UX_mul b').measurable u', ?_⟩
  rintro ⟨c, b, u⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, he, he, he]
  exact coord_mul d c c' b b' u.1 u'.1

end GlobalTheory.Unf.HaarCoord
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.LinkExist

theorem star_smul_vec {D : D7} {n : ℕ} (k : D.host.E) (v : Fin n → D.host.E) : star (k • v) = star k • star v := by
  funext i
  simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']

theorem norm_smul_vec {D : D7} (L' : HSp D) (k : D.host.E) (v : Fin L'.rank → D.host.E) :
    star (k • v) ⬝ᵥ L'.gram *ᵥ (k • v) = star k * k * (star v ⬝ᵥ L'.gram *ᵥ v) := by
  rw [star_smul_vec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem link_of_norm : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (c : D.host.E), IsLineVec L' ζ' → star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = c * star c * (star ζ' ⬝ᵥ L'.gram *ᵥ ζ') → IsLineVec L' ((c / D.host.xi0) • ζ') ∧ Nonempty (Link B L' ((c / D.host.xi0) • ζ')) := by
  intro D ρ B L' ζ' c hl hn
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hN := B.line.2
  rw [hn] at hN
  have hc : c ≠ 0 := fun h => hN (by simp [h])
  have hv : star ζ' ⬝ᵥ L'.gram *ᵥ ζ' ≠ 0 := fun h => hN (by simp [h])
  have hk : c / D.host.xi0 ≠ 0 := div_ne_zero hc hxi
  have hsk : star (c / D.host.xi0) ≠ 0 := star_ne_zero.2 hk
  set x := (c / D.host.xi0) • ζ' with hx
  have hnx : star x ⬝ᵥ L'.gram *ᵥ x = star (c / D.host.xi0) * (c / D.host.xi0) * (star ζ' ⬝ᵥ L'.gram *ᵥ ζ') :=
    norm_smul_vec L' _ ζ'
  have hn0 : star x ⬝ᵥ L'.gram *ᵥ x ≠ 0 := by
    rw [hnx]; exact mul_ne_zero (mul_ne_zero hsk hk) hv
  refine ⟨⟨hl.1, hn0⟩, ⟨{ τ := (-(star x ⬝ᵥ L'.gram *ᵥ x)⁻¹) • vecMulVec B.ζ (star x ᵥ* L'.gram), map := ?_, norm := ?_ }⟩⟩
  · rw [Matrix.smul_mulVec, vecMulVec_mulVec, ← Matrix.dotProduct_mulVec, op_smul_eq_smul, smul_smul, neg_mul, inv_mul_cancel₀ hn0, neg_one_smul]
  · rw [hn, hnx]
    have hsx : star D.host.xi0 ≠ 0 := star_ne_zero.2 hxi
    rw [star_div₀]
    field_simp

end GlobalTheory.Unf.LinkExist
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open scoped Pointwise

namespace GlobalTheory.Unf

theorem vol_fund_lt_top {D : D7} {V : HSp D} (hc : CoCpt V) (v : Vol V) : v.μ v.𝓕 < ⊤ := by
  obtain ⟨_, _, _, _, _, _, hΓc⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := v.haar
  obtain ⟨K, hKc, hKcov⟩ := hc
  have hcover : v.𝓕 ⊆ ⋃ g : GQ V, (g • K) := by
    intro h _
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
    simp [Subgroup.smul_def]
  have hle : v.μ v.𝓕 ≤ v.μ K := by
    calc v.μ v.𝓕 = v.μ ((⋃ g : GQ V, (g • K)) ∩ v.𝓕) := by rw [Set.inter_eq_right.2 hcover]
      _ = v.μ (⋃ g : GQ V, (g • K ∩ v.𝓕)) := by rw [Set.iUnion_inter]
      _ ≤ ∑' g : GQ V, v.μ (g • K ∩ v.𝓕) := measure_iUnion_le _
      _ = v.μ K := (v.fund.measure_eq_tsum K).symm
  exact hle.trans_lt hKc.measure_lt_top

theorem jac_bound (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ) (hK : Continuous K)
    (hinv : ∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) (h : GA D J.W) :
    ∃ C, ∀ (n : flagN J.d) (h' : GA D J.W₀), ‖K (n.1 * J.d.emb0 h' * h)‖ ≤ C := by
  have hcont := J.d.continuous_embed
  obtain ⟨-, -, -, -, hnorm, -, -⟩ := GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d
  obtain ⟨⟨Kn, hKn, hcov⟩, -⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D J.W ρ J.d.e (isIsoSub_e J.d)
  obtain ⟨K₀, hK₀, hcov₀⟩ := J.cpt
  obtain ⟨-, -, -, -, htop, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  let f : flagN J.d × GA D J.W₀ → GA D J.W := fun p => p.1.1 * J.d.emb0 p.2 * h
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_fst).mul (hcont.comp continuous_snd)).mul continuous_const
  have hS : IsCompact (f '' (Kn ×ˢ K₀)) := (hKn.prod hK₀).image hf
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hK.continuousOn
  refine ⟨C, fun n h' => ?_⟩
  obtain ⟨γ₀, hγ₀, hk₀⟩ := hcov₀ h'
  have hemb : J.d.emb0 γ₀ ∈ GQ J.W := J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hγ₀
  let n' : flagN J.d := ⟨J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹, hnorm n.1 n.2 γ₀⟩
  obtain ⟨γ, hγ, k, hk, hn'⟩ := hcov n'
  have hδ : (J.d.emb0 γ₀)⁻¹ * γ.1 ∈ GQ J.W ⊓ jacGrp J.d :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hemb) (Subgroup.mem_subgroupOf.1 hγ),
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (MonoidHom.mem_range.2 ⟨γ₀, rfl⟩)))
        (Subgroup.mem_sup_left γ.2)⟩
  have h1 : γ.1 * k.1 = J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹ := (congrArg Subtype.val hn').symm
  have heq : n.1 * J.d.emb0 h' * h = ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * J.d.emb0 (γ₀ * h') * h) := by
    rw [map_mul, show ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * (J.d.emb0 γ₀ * J.d.emb0 h') * h) =
      (J.d.emb0 γ₀)⁻¹ * (γ.1 * k.1) * J.d.emb0 γ₀ * J.d.emb0 h' * h by simp only [mul_assoc], h1]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [heq, hinv _ hδ]
  exact hC _ ⟨(k, γ₀ * h'), ⟨hk, hk₀⟩, rfl⟩

theorem jac_absConv : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K →
    (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) → ∀ h,
      AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h) := by
  intro D ρ J K hK hinv h
  obtain ⟨C, hC⟩ := jac_bound D ρ J K hK hinv h
  have hcont := J.d.continuous_embed
  obtain ⟨-, h2W, -, hbW, htW, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨-, h20, -, hb0, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  have hμ : J.v0.μ J.v0.𝓕 < ⊤ := vol_fund_lt_top J.cpt J.v0
  have hν : J.vN.ν J.vN.𝓝 < ⊤ := by rw [J.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2 hμ.ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  unfold AbsConv
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => hC p.2 p.1)
  exact (hK.comp (((continuous_subtype_val.comp continuous_snd).mul (hcont.comp continuous_fst)).mul
    continuous_const)).aestronglyMeasurable

end GlobalTheory.Unf

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilPairing

theorem thPair_om_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ (v : VolM D T.rank S.rank) p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → thPair v.μ v.𝓕 (om p f) (om p f') = thPair v.μ v.𝓕 f f' := by
  intro D ψ S T χ χ' om hW v p f f' hf hf'
  obtain ⟨hμ, h𝓕, -⟩ := v.covol
  have h𝓕' : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := h𝓕
  exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hW.std S T v.μ v.𝓕 hμ h𝓕' (om p) (fun g hg => hW.om_pres p g hg)
    (fun g hg => hW.om_unit v.μ v.𝓕 hμ h𝓕' p g hg) f f' hf hf'

end GlobalTheory.WeilPairing

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf.CoCptOf

theorem coCpt_of_mul {D : D7} {V : HSp D}
    (h : ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, ∃ k ∈ K, g = γ * k) : CoCpt V := by
  obtain ⟨K, hK, h⟩ := h
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

theorem coCpt_of_isAniso_or_posDef :
    ∀ (D : D7) (V : HSp D), (IsAniso V → CoCpt V) ∧ ((∀ τ, (gramAt D V τ).PosDef) → CoCpt V) :=
  fun D V => ⟨fun h => coCpt_of_mul (GlobalTheory.Mem.AnisoQuotient.exists_compact D V h),
    fun h => coCpt_of_mul (GlobalTheory.definite_unitary_cocompact V h)⟩

end GlobalTheory.Unf.CoCptOf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_definiteQuotient_eq_classSum : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E), J = V.gram.reindex (finCongr hn) (finCongr hn) → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (cl : Type) (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → V.SigOK → (∀ τ, (gramAt D V τ).PosDef) → ∀ [Fintype cl] (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ h : cl → GA D V, (∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (yc c).1.1) → ∃ (vol : ℝ) (ν : Measure (GinfC V)), 0 < vol ∧ ν.IsHaarMeasure ∧ ν Set.univ = 1 ∧ ∀ Φ : GA D V → ℂ, Continuous Φ → (∀ γ ∈ GQ V, ∀ x, Φ (γ * x) = Φ x) → (∀ k ∈ GfC V, (∃ κ : S.U, κ.1.1 = finM V hn k) → ∀ x, Φ (x * k) = Φ x) → ∫ x in 𝓕, Φ x ∂μ = (vol : ℂ) * ∑ c, ((Nat.card {γ : GQ V // ∃ κ : S.U, finM V hn γ.1 * (yc c).1.1 = (yc c).1.1 * κ.1.1} : ℕ) : ℂ)⁻¹ * ∫ k, Φ (h c * k.1) ∂ν := by
  first | exact @GlobalTheory.ClassSumLevel.integral_eq_classSum | exact GlobalTheory.ClassSumLevel.integral_eq_classSum | (intros; apply GlobalTheory.ClassSumLevel.integral_eq_classSum <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.trueColumnWeight_spread_le_two_mul_scale : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → ∀ (u : B.Word) (j : ℕ), j ≤ B.R.m → ∀ τ, ((B.wts.lamTrue u j τ).spread : ℝ) ≤ 2 * L.sc.a := by
  first | exact @GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le | exact GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le | (intros; apply GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.fockPartitionRows_numericDatum_mem_Icc : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), ∀ j ∈ (numDatumOfParameters D L).lifts, ∀ z, ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D L).nu (codeRec L u) j z i ∧ (((numDatumOfParameters D L).nu (codeRec L u) j z i : ℚ) : ℝ) ≤ 3 * L.sc.a := by
  first | exact @GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem | exact GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem | (intros; apply GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem PM_map {r : ℕ} {B : Type} [CommRing B] (f : AE D →+* B) (M : Matrix (Fin r) (Fin r) (AE D)) :
    (PM M).map f = f (eps D) • M.map f + f (1 - eps D) • (1 : Matrix (Fin r) (Fin r) B) := by
  ext i j
  simp only [PM, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add (f := _), map_mul]
  split_ifs <;> simp

theorem cT_PM {r : ℕ} (M : Matrix (Fin r) (Fin r) (AE D)) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) =
      eps D • cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M + (1 - eps D) • (1 : Matrix (Fin r) (Fin r) (AE D)) := by
  unfold cT
  rw [PM_map, RingHom.map_sub, RingHom.map_one, sig_eps, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_one]

theorem PM_unit {r : ℕ} (J M : Matrix (Fin r) (Fin r) (AE D))
    (hM : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * J * M = J) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) * J * PM M = J := by
  rw [cT_PM, PM]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    eps_mul_self, one_sub_mul_self, eps_mul_one_sub, mul_comm (1 - eps D) (eps D), zero_smul, add_zero, zero_add, hM]
  rw [← add_smul, add_sub_cancel, one_smul]

def PGL (D : D7) (r : ℕ) : GL (Fin r) (AE D) →* GL (Fin r) (AE D) where
  toFun g := ⟨PM g.1, PM (g⁻¹).1, by rw [← PM_mul, Units.mul_inv, PM_one], by rw [← PM_mul, Units.inv_mul, PM_one]⟩
  map_one' := Units.ext PM_one
  map_mul' a b := Units.ext (PM_mul a.1 b.1)

theorem PGL_mem (V : HSp D) (g : GL (Fin V.rank) (AE D)) (hg : g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) :
    PGL D V.rank g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
  PM_unit _ g.1 hg

def pf (V : HSp D) (h : GA D V) : GA D V :=
  (⟨PGL D V.rank (matHom V h), PGL_mem V (matHom V h) (Subtype.property (h : ↥(HR (AF D.host.F) D.sp.cm.sig V.gram)))⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem mt_pf (V : HSp D) (h : GA D V) : Formalism.L2.Theta.mt V (pf V h) = PM (Formalism.L2.Theta.mt V h) := rfl

theorem pf_one (V : HSp D) : pf V 1 = 1 := by
  apply Subtype.ext
  show PGL D V.rank (matHom V 1) = 1
  rw [map_one, map_one]

theorem pf_fin (V : HSp D) (h : GA D V) : pf V h ∈ GfC V := by
  show infHom V (pf V h) = 1
  apply Units.ext
  show (Formalism.L2.Theta.mt V (pf V h)).map (infPart D) = 1
  rw [mt_pf, PM_map, infPart_eps, RingHom.map_sub, RingHom.map_one, infPart_eps, sub_zero, zero_smul, zero_add, one_smul]

theorem finM_pf (V : HSp D) (h : GA D V) : finM V rfl (pf V h) = finM V rfl h := by
  rw [finM_rfl, finM_rfl, mt_pf, PM_map, toEAf_eps, RingHom.map_sub, RingHom.map_one, toEAf_eps, sub_self, zero_smul, add_zero, one_smul]

theorem continuous_pf (V : HSp D) : Continuous (pf V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hm : Continuous fun h : GA D V => Formalism.L2.Theta.mt V h :=
    Units.continuous_val.comp continuous_subtype_val
  have hP : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) (AE D) => PM M :=
    (continuous_const_smul _).add continuous_const
  refine Continuous.subtype_mk (f := fun h => PGL D V.rank (matHom V h)) (Units.continuous_iff.2 ⟨hP.comp hm, ?_⟩) _
  have e : (fun h : GA D V => ((PGL D V.rank (matHom V h))⁻¹ : GL (Fin V.rank) (AE D)).val) =
      fun h => PM (Formalism.L2.Theta.mt V h⁻¹) := by
    funext h
    rw [← map_inv, ← map_inv]; rfl
  rw [e]
  exact hP.comp (hm.comp continuous_inv)

end GlobalTheory.AdForm.RdLaw
end
end
