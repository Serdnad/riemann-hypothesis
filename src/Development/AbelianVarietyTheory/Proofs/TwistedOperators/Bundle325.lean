module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle288
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle205
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockSource
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct

namespace GlobalTheory.FinZeta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {V : HSp D} {ν : Measure (GA D V)} {𝓕 : Set (GA D V)}

private theorem zero_one_mem_gammaSet_one (f : bddAut V) : Continuous (f : GA D V → ℂ) ∧
    (∀ γ ∈ GQ V, ∀ g, (f : GA D V → ℂ) (γ * g) = (f : GA D V → ℂ) g) ∧
    ∃ C : ℝ, ∀ g, ‖(f : GA D V → ℂ) g‖ ≤ C := f.2

private theorem integrableOn_fundamentalDomain_of_bounded {E : Type} [NormedAddCommGroup E] (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) {φ : GA D V → E} (hφ : Continuous φ) (C : ℝ)
    (hC : ∀ g, ‖φ g‖ ≤ C) : IntegrableOn φ 𝓕 ν := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.1
  haveI := hT.2.2.2.1
  exact Measure.integrableOn_of_bounded
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕).ne hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

theorem integrableOn_mul_conj_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f f₂ : bddAut V) :
    IntegrableOn (fun g => (f : GA D V → ℂ) g * starRingEnd ℂ ((f₂ : GA D V → ℂ) g)) 𝓕 ν := by
  obtain ⟨hc, -, C, hC⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨hc₂, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
  refine integrableOn_fundamentalDomain_of_bounded hν h𝓕 (hc.mul (Complex.continuous_conj.comp hc₂)) (C * C₂) fun g => ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC g) (hC₂ g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

theorem exists_form_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ, ∀ f f₂, B f f₂ = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f f₂ : bddAut V => l2 ν 𝓕 (f : GA D V → ℂ) f₂) ?_ ?_ ?_ ?_, fun f f₂ => rfl⟩
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a c) (integrableOn_mul_conj_bddAut hν h𝓕 b c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a b) (integrableOn_mul_conj_bddAut hν h𝓕 a c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring

theorem petersson_self_re_pos_of_ne_zero (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f : bddAut V) (hf : f ≠ 0) :
    0 < (l2 ν 𝓕 (f : GA D V → ℂ) f).re := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  obtain ⟨hc, hi, C, hC⟩ := zero_one_mem_gammaSet_one f
  have key : l2 ν 𝓕 (f : GA D V → ℂ) f =
      ((∫ x in 𝓕, Complex.normSq ((f : GA D V → ℂ) x) ∂ν : ℝ) : ℂ) := by
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Complex.mul_conj]
    exact integral_ofReal
  rw [key, Complex.ofReal_re]
  have hint : IntegrableOn (fun x => Complex.normSq ((f : GA D V → ℂ) x)) 𝓕 ν :=
    integrableOn_fundamentalDomain_of_bounded hν h𝓕 (Complex.continuous_normSq.comp hc) (C * C) fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hC g) (hC g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _) hint]
  set U : Set (GA D V) := {x | (f : GA D V → ℂ) x ≠ 0} with hUdef
  have hsupp : Function.support (fun x => Complex.normSq ((f : GA D V → ℂ) x)) = U := by
    ext x
    simp [U, Complex.normSq_eq_zero]
  rw [hsupp]
  have hU : IsOpen U := isOpen_ne_fun hc continuous_const
  have hne : U.Nonempty := by
    by_contra hE
    rw [Set.not_nonempty_iff_eq_empty] at hE
    apply hf
    apply Subtype.ext
    funext x
    by_contra hx
    have hx' : x ∈ U := hx
    rw [hE] at hx'
    exact hx'
  refine pos_iff_ne_zero.2 fun h0 => (hU.measure_pos ν hne).ne' ?_
  have hsub : U ⊆ {x | ¬ ∃ γ : GQ V, γ • x ∈ 𝓕} ∪
      ⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) := by
    intro x hx
    by_cases hx' : ∃ γ : GQ V, γ • x ∈ 𝓕
    · obtain ⟨γ, hγ⟩ := hx'
      refine Or.inr (Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩)
      show (f : GA D V → ℂ) ((γ : GA D V) * x) ≠ 0
      rw [hi γ γ.2]
      exact hx
    · exact Or.inl hx'
  refine measure_mono_null hsub (measure_union_null (ae_iff.1 h𝓕.ae_covers) ?_)
  refine measure_iUnion_null fun γ => ?_
  rw [measure_preimage_mul]
  exact h0

theorem petersson_bounded_automorphic_right_translation_invariant (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (g : GA D V) (f f₂ : bddAut V) :
    l2 ν 𝓕 (bddRep V g f : GA D V → ℂ) (bddRep V g f₂ : GA D V → ℂ) = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V ν hν).1
  obtain ⟨-, hi, -⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨-, hi₂, -⟩ := zero_one_mem_gammaSet_one f₂
  rw [coe_bddRep, coe_bddRep]
  simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
  exact GlobalTheory.setIntegral_fundamentalDomain_mul_right h𝓕 g
    (fun x => (f : GA D V → ℂ) x * starRingEnd ℂ ((f₂ : GA D V → ℂ) x))
    fun γ hγ x => by simp only [hi γ hγ, hi₂ γ hγ]

end

theorem bddRep_unitarisable_and_bounded : ∀ (D : D7) (V : HSp D), IsUnitarisable (bddRep V) ∧ ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∀ f₂ : bddAut V, ∃ ℓ : bddAut V →ₗ[ℂ] ℂ, (∀ f : bddAut V, ℓ f = l2 ν 𝓕 (f : GA D V → ℂ) f₂) ∧ ∀ f : bddAut V, ∃ C : ℝ, ∀ g, ‖ℓ (bddRep V g f)‖ ≤ C := by
  intro D V
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  refine ⟨?_, fun ν 𝓕 hν h𝓕 f₂ => ?_⟩
  · have hH : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
    obtain ⟨𝓕, h𝓕⟩ :=
      (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V Measure.haar hH).2
    obtain ⟨B, hB⟩ := exists_form_bddAut hH h𝓕
    unfold IsUnitarisable
    refine ⟨B, fun v w => ?_, fun v hv => ?_, fun g v w => ?_⟩
    · rw [hB, hB]
      simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet]
      rw [← integral_conj]
      congr 1
      funext x
      rw [map_mul, Complex.conj_conj, mul_comm]
    · rw [hB]
      exact petersson_self_re_pos_of_ne_zero hH h𝓕 v hv
    · rw [hB, hB]
      exact petersson_bounded_automorphic_right_translation_invariant hH h𝓕 g v w
  · obtain ⟨B, hB⟩ := exists_form_bddAut hν h𝓕
    refine ⟨{ toFun := fun f => B f f₂, map_add' := fun a b => by simp, map_smul' := fun c a => by simp },
      fun f => hB f f₂, fun f => ?_⟩
    obtain ⟨-, -, C, hC⟩ := zero_one_mem_gammaSet_one f
    obtain ⟨-, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
    have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕
    refine ⟨C * C₂ * (ν 𝓕).toReal, fun g => ?_⟩
    show ‖B (bddRep V g f) f₂‖ ≤ _
    rw [hB, coe_bddRep]
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x _ => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

end GlobalTheory.FinZeta

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

theorem levelCharacter_on_stabilizer_eq_prod_residue_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ ψ : ∀ P : Pl D.host.E, AddChar (kP P) ℂ, (∀ PP ∈ R.Pg, ψ PP ≠ 1 ∧ ψ (GlobalTheory.IdemSupport.cP PP) ≠ 1) ∧ ∀ κ : GA D (Yc D 0), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → X.chi2 ((iotaX X h).toMulEquiv κ).2 = ∏ PP ∈ R.Pg, ψ PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) * ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG
  obtain ⟨hg, hcov⟩ := GlobalTheory.T.typePlaces_over_norm_and_cover_with_conjugates R hL
  obtain ⟨ψ, hψ, hprod⟩ := GlobalTheory.T.conjInstanceCharacter_eq_prod_residueField_addChars X h R.Pg hg hcov (GlobalTheory.T.levelPlaces_not_isConjPlace_realDat R F hL hG)
  refine ⟨ψ, hψ, fun κ hκ => ?_⟩
  obtain ⟨hi, he⟩ := GlobalTheory.T.otherInstanceCharacter_eq_conjInstancePsiValue_integral X h κ hκ
  rw [he, hprod _ hi]

end GlobalTheory.SeeConjChar
end

section

noncomputable section

open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift.TensorFormProof

open GlobalTheory.Chain.IoLift

variable {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]

theorem contr_tmul (ι : V →ₗ[ℂ] H) (y : V) (a : A) (v : V) :
    contr ι y (a ⊗ₜ[ℂ] v) = ⟪ι y, ι v⟫_ℂ • a := by
  unfold contr
  rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.comp_apply, innerₛₗ_apply_apply]
  exact TensorProduct.rid_tmul _ _

theorem dual_contr (ι : V →ₗ[ℂ] H) (y : V) (l : A →ₗ[ℂ] ℂ) (t : A ⊗[ℂ] V) :
    l (contr ι y t) = ⟪ι y, ι (TensorProduct.lid ℂ V (LinearMap.rTensor V l t))⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [contr_tmul, map_smul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, inner_smul_right,
      smul_eq_mul, mul_comm]
  | add s u hs hu => simp only [map_add (f := _), inner_add_right, hs, hu]

theorem eq_zero_of_contr (ι : V →ₗ[ℂ] H) (hι : Function.Injective ι) (t : A ⊗[ℂ] V)
    (h : ∀ y, contr ι y t = 0) : t = 0 := by

  have hl : ∀ l : A →ₗ[ℂ] ℂ, LinearMap.rTensor V l t = 0 := by
    intro l
    set w := TensorProduct.lid ℂ V (LinearMap.rTensor V l t) with hw
    have h0 : ⟪ι w, ι w⟫_ℂ = 0 := by
      have := dual_contr ι w l t
      rw [h w, map_zero] at this
      exact this.symm
    have hw0 : w = 0 := hι ((inner_self_eq_zero.mp h0).trans (map_zero ι).symm)
    rw [hw] at hw0
    exact (LinearEquiv.map_eq_zero_iff _).mp hw0

  let e := (Module.Basis.ofVectorSpace ℂ A).repr
  have hs : TensorProduct.finsuppScalarLeft ℂ V _ (LinearMap.rTensor V e.toLinearMap t) = 0 := by
    ext i
    rw [TensorProduct.finsuppScalarLeft_apply, ← LinearMap.rTensor_comp_apply, hl, map_zero]
    rfl
  have h2 : LinearMap.rTensor V e.toLinearMap t = 0 := (LinearEquiv.map_eq_zero_iff _).mp hs
  have h3 := congrArg (LinearMap.rTensor V e.symm.toLinearMap) h2
  rwa [← LinearMap.rTensor_comp_apply, LinearEquiv.symm_comp, LinearMap.rTensor_id_apply, map_zero] at h3

theorem exists_tensor (ι : V →ₗ[ℂ] H) (β : V →ₛₗ[starRingEnd ℂ] A) (E : Submodule ℂ V) [FiniteDimensional ℂ E]
    (h : ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → β y = 0) : ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = β y := by

  set F : Submodule ℂ H := E.map ι with hF
  haveI : FiniteDimensional ℂ F := by rw [hF]; infer_instance
  let b := stdOrthonormalBasis ℂ F
  have hpre : ∀ k, ∃ e : V, e ∈ E ∧ ι e = (b k : H) := fun k => Submodule.mem_map.mp (b k).2
  choose e heE he using hpre
  refine ⟨∑ k, β (e k) ⊗ₜ[ℂ] e k, fun y => ?_⟩

  rw [map_sum]
  simp only [contr_tmul, he]

  set z : V := ∑ k, ⟪(b k : H), ι y⟫_ℂ • e k with hz
  have hperp : ∀ x ∈ E, ⟪ι (y - z), ι x⟫_ℂ = 0 := by
    intro x hx
    have hxF : ι x ∈ F := Submodule.mem_map_of_mem hx
    have hx' : ι x = ∑ j, ⟪(b j : H), ι x⟫_ℂ • (b j : H) := by
      have := congrArg Subtype.val (b.sum_repr' ⟨ι x, hxF⟩)
      simpa [Submodule.coe_inner] using this.symm
    have key : ⟪ι y, ι x⟫_ℂ = ∑ j, ⟪ι y, (b j : H)⟫_ℂ * ⟪(b j : H), ι x⟫_ℂ := by
      conv_lhs => rw [hx']
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right, mul_comm]

    simp only [hz, map_sub, map_sum, map_smul, he, inner_sub_left, sum_inner, inner_smul_left, inner_conj_symm]
    rw [key, sub_self]
  have hyz := h (y - z) hperp
  rw [map_sub, sub_eq_zero] at hyz

  rw [hyz, hz, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, inner_conj_symm]

theorem tensorForm : TensorForm := by
  intro U A V H _ _ _ _ _ _ _ _ ι hι
  have sep : ∀ s u : A ⊗[ℂ] V, (∀ y, contr ι y s = contr ι y u) → s = u := fun s u hsu =>
    sub_eq_zero.mp (eq_zero_of_contr ι hι _ fun y => by rw [map_sub, hsu, sub_self])
  refine ⟨fun t ht => eq_zero_of_contr ι hι t ht, fun B hB => ?_⟩
  have hex : ∀ P, ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = B P y := by
    intro P
    obtain ⟨E, hE, hk⟩ := hB P
    exact exists_tensor ι (B P) E hk
  choose g hg using hex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sep _ _ fun y => by simp [hg]
           map_smul' := fun c P => sep _ _ fun y => by simp [hg] }, hg⟩

end GlobalTheory.Chain.IoLift.TensorFormProof

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift


open Formalism.REAL in
theorem kMean_translate {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {n : ℕ}
    (c : Fin n → KG (M.ε τ) → ℂ) (hc : IsCoefFam c) (w : M.H τ) (i : Fin n) (k₀ : KG (M.ε τ)) :
    ∃ d : Fin n → ℂ, M.σ τ (toMK k₀) (kMean M τ (c i) w) = ∑ j, d j • kMean M τ (c j) w := by
  have hds := M.ds τ
  have : CompleteSpace (M.H τ) := hds.1
  obtain ⟨⟨-, hmul⟩, -, hcont⟩ := hds.2.2.1
  have hmem : ∀ k : KG (M.ε τ), toMK k ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun k => (k : UJ (M.ε τ)).2
  have hcK : Continuous fun k : KG (M.ε τ) => M.σ τ (toMK k) w :=
    (hcont w).comp_continuous (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)) hmem
  have hint : ∀ j, Integrable (fun k => c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j =>
    ((hc.1 j).smul hcK).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have hm : ∀ k : KG (M.ε τ), M.σ τ (toMK (k₀ * k)) = (M.σ τ (toMK k₀)).comp (M.σ τ (toMK k)) :=
    fun k => hmul _ (hmem k₀) _ (hmem k)
  obtain ⟨d, hd⟩ := hc.2 k₀⁻¹ i
  refine ⟨d, ?_⟩
  unfold kMean
  calc M.σ τ (toMK k₀) (∫ k, c i k • M.σ τ (toMK k) w ∂muK (M.ε τ))
      = ∫ k, M.σ τ (toMK k₀) (c i k • M.σ τ (toMK k) w) ∂muK (M.ε τ) :=
        (ContinuousLinearMap.integral_comp_comm _ (hint i)).symm
    _ = ∫ k, (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) (k₀ * k) ∂muK (M.ε τ) := by
        congr 1
        funext k
        simp only [map_smul, inv_mul_cancel_left]
        rw [hm]
        rfl
    _ = ∫ k, c i (k₀⁻¹ * k) • M.σ τ (toMK k) w ∂muK (M.ε τ) :=
        integral_mul_left_eq_self (μ := muK (M.ε τ)) (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) k₀
    _ = ∑ j, d j • ∫ k, c j k • M.σ τ (toMK k) w ∂muK (M.ε τ) := by
        simp only [hd, Finset.sum_smul, mul_smul]
        have hs : ∀ j ∈ (Finset.univ : Finset (Fin n)),
            Integrable (fun k => d j • c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j _ => (hint j).smul (d j)
        rw [integral_finsetSum _ hs]
        simp only [integral_smul]

theorem kMean_mem_kFin_of_coefFam : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (n : ℕ) (c : Fin n → Formalism.REAL.KG (M.ε τ) → ℂ), IsCoefFam c → ∀ (w : M.H τ) (i : Fin n),
    kMean M τ (c i) w ∈ kFin M τ := by
  intro D V S M τ n c hc w i
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin
  rw [GlobalTheory.KFiniteVectors.mem_kFiniteVectors]
  refine ⟨Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _), Submodule.subset_span ⟨i, rfl⟩, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k₀, rfl⟩ := hg
  have hle : Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w) ≤
      (Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)).comap
        (M.σ τ (Formalism.REAL.toMK k₀) : M.H τ →ₗ[ℂ] M.H τ) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd⟩ := kMean_translate M τ c hc w j k₀
    change M.σ τ (Formalism.REAL.toMK k₀) (kMean M τ (c j) w) ∈ Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)
    rw [hd]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  exact hle hx

end GlobalTheory.Chain.IoLift
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin)
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LowerMembers

theorem pairing_eq_zero : ∀ (X : ProvA), Formalism.MainNotions.SchurIrreducible.admQ5 X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → ∀ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de → (∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → ∀ i : ℕ, 1 ≤ i → i ≤ al.length + be.length → i ≤ ga.length + de.length → ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (e : Ix (al.length + be.length - i) (ga.length + de.length - i) ≃ Fin V.rank) (e' : Ix (al.length + de.length + t) (ga.length + be.length) ≃ Fin W.rank) (m' : ℤ) (aS : ℚ) (U' : M'.H τ ≃ₗᵢ⋆[ℂ] (X.ds _ _ (lamA' t al be ga de)).U.H) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) (b : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] ℂ), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat (M'.ε τ) e' → (m' : ℚ) = 2 * aS → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches (X.ds _ _ (lamA' t al be ga de)) M' τ (GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat e') m' U' → GlobalTheory.Chain.IoLift.IsKAct M' τ a' → (∀ Y ∈ lieAt W τ, ∀ P y, b (locT ε (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y + b P (a' Y y) = 0) → b = 0 := by
  intro X h5 hAR t al be ga de hd hbig i hi hip hiq D V W S' M' τ ε e e' m' aS U' a' b he he' hm' h₂ ha hb
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ ε (M'.ε τ) e e' he he'
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm ((X.ds _ _ (lamA' t al be ga de)).ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : (X.ds _ _ (lamA' t al be ga de)).HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm ((X.ds _ _ (lamA' t al be ga de)).ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = (X.ds _ _ (lamA' t al be ga de)).ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  let B' : Pol _ _ _ _ →ₗ[ℂ] (X.ds _ _ (lamA' t al be ga de)).HK.V →ₛₗ[starRingEnd ℂ] ℂ :=
    { toFun := fun P => (b (κ.symm P)).comp j
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  have hB' : ∀ P v, B' (κ P) v = b P (j v) := fun P v => by simp [B']
  have h0 : B' = 0 := GlobalTheory.T.no_invariant_pairing_smaller_fock_source X h5 hAR t al be ga de hd hbig i hi hip hiq B' (fun Y hY P y => by
    obtain ⟨P, rfl⟩ := κ.surjective P
    have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
    have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
    have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j ((X.ds _ _ (lamA' t al be ga de)).HK.act Y y) -
        ((aS : ℂ) * Y.trace) • j y := by
      have h7 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
          j ((X.ds _ _ (lamA' t al be ga de)).HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
        refine Subtype.ext (U'.injective ?_)
        rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
      rw [h7, map_add (f := _), LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
        sub_eq_add_neg, ← neg_smul]
      congr 2
      ring
    have h := hb _ hY' P (j y)
    rw [h6, fr_toFrame, trace_toFrame, h4] at h
    rw [← hκ.2, hB', hB', ← h]
    simp [plainMat])
  refine LinearMap.ext fun P => LinearMap.ext fun z => ?_
  obtain ⟨v, rfl⟩ := hsurj z
  rw [← hB', h0]
  rfl

end GlobalTheory.LowerMembers

end
end
