module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle401
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
import GroundTheory.GlobalFields.Adele.Topology
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle406
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle411
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

@[expose] public section

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

open GroundTheory.Automorphic.AutomorphicForm


omit [_root_.NumberField.IsTotallyComplex E] in
theorem unipGL_eq_unip {r : ℕ} (X : UPos a r → Ad E) :
    (unipGL X : GL (Fin a) (Ad E)) = unip X :=
  Units.ext rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isAddHaarMeasure_unipMeasure (r : ℕ) : (unipMeasure E a r).IsAddHaarMeasure := by
  infer_instance

theorem ctFun_resQ_eq_zero {φ : GA E a → ℂ} (hφ : φ ∈ cuspCont E a) {r : ℕ} (h0 : 0 < r) (h1 : r < a)
    (y : normOneGL (K := E) (n := a)) : ctFun r (resQ φ) y = 0 := by
  obtain ⟨-, hl, -, hc⟩ := mem_cuspCont.1 hφ
  have h := hc r h0 h1 (unipMeasure E a r) (unipFundamentalDomain E a r)
    (isAddHaarMeasure_unipMeasure r) isAddFundamentalDomain_unipFundamentalDomain (y : GA E a)
  unfold ctFun
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)) h
  exact (resQ_mk hl _).trans (congrArg φ (congrArg (· * (y : GA E a)) (unipGL_eq_unip X)))

theorem toLp_restrict_mem_cuspidalL2 (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (φ : GA E a → ℂ) (hφ : φ ∈ cuspCont E a)
    (h : MemLp (resQ φ) 2 (RightCosetSpace.quotientMeasure (rationalGLOne (K := E) (n := a)) ν)) :
    h.toLp (resQ φ) ∈ cuspidalL2 ν := by
  intro r h0 h1
  filter_upwards [ae_ctFun_congr ν r h.coeFn_toLp] with y hy
  exact hy.trans (ctFun_resQ_eq_zero hφ h0 h1 y)

end GlobalTheory.CompanionTheory.CuspTransfer
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem tst_conj_Kinf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) {β : Lie E a → ℂ} (hβ : ConjInv β) (k : Kinf E a) (y : GA E a) :
    tst U β ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k))) = tst U β y := by
  have e : ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k)))⁻¹ =
      (infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k) := by group
  have hf : GeneralLinearGroup.map (pFin E) ((infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k)) =
      GeneralLinearGroup.map (pFin E) y⁻¹ := by
    simp only [map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]
  have hi : GeneralLinearGroup.map (pInf E) ((infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k)) =
      (Unitary.toUnits k)⁻¹ * GeneralLinearGroup.map (pInf E) y⁻¹ * Unitary.toUnits k := by
    rw [map_mul, map_mul, map_inv, pInf_infGL]
  have hc := hβ k⁻¹ (toL (GeneralLinearGroup.map (pInf E) y⁻¹).val)
  have hv : toL ((k⁻¹ : Kinf E a).1 * Matrix.of (toL (GeneralLinearGroup.map (pInf E) y⁻¹).val) * star (k⁻¹ : Kinf E a).1) =
      toL ((Unitary.toUnits k)⁻¹ * GeneralLinearGroup.map (pInf E) y⁻¹ * Unitary.toUnits k).val := by
    have h1 : ((Unitary.toUnits k)⁻¹ : GL (Fin a) (Cinf E)).val = (k⁻¹ : Kinf E a).1 := by
      rw [← map_inv]; rfl
    have h2 : star (k⁻¹ : Kinf E a).1 = k.1 := by
      change star (star k.1) = k.1
      exact star_star _
    rw [h2, Units.val_mul, Units.val_mul, h1]
    rfl
  unfold tst ker
  rw [e, hf, hi, ← hv, hc]

theorem convR_tst_cpt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ), ConjInv β → ∀ (F : L2 (latticeGL E a) μ) (k : Kinf E a) (x : GA E a), convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)) x = convR μ (tst U β) (lift (latticeGL E a) F) (x * infGL E a (Unitary.toUnits k)) := by
  intro E _ _ _ a μ _ _ U β hβ F k x
  have h1 : ∀ᵐ y ∂μ, lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F) (x * y) =
      lift (latticeGL E a) F (x * y * infGL E a (Unitary.toUnits k)) :=
    (measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (lift_R (infGL E a (Unitary.toUnits k)) F)
  simp only [AutomorphicL2Unitary.convR]
  rw [← integral_mul_left_eq_self
      (fun y => tst U β y * lift (latticeGL E a) F (x * infGL E a (Unitary.toUnits k) * y)) (infGL E a (Unitary.toUnits k))⁻¹,
    ← integral_mul_right_eq_self
      (fun y => tst U β ((infGL E a (Unitary.toUnits k))⁻¹ * y) *
        lift (latticeGL E a) F (x * infGL E a (Unitary.toUnits k) * ((infGL E a (Unitary.toUnits k))⁻¹ * y)))
      (infGL E a (Unitary.toUnits k))]
  refine integral_congr_ae (h1.mono fun y hy => ?_)
  have e : x * infGL E a (Unitary.toUnits k) * ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k))) =
      x * y * infGL E a (Unitary.toUnits k) := by group
  simp only [tst_conj_Kinf U hβ k y, e, hy]

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem tst_finGL_inv_mul {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (u : GL (Fin a) (Af E)) (hu : u ∈ U)
    (y : GA E a) : tst U β ((finGL E a u)⁻¹ * y) = tst U β y := by
  have hinv : ((finGL E a u)⁻¹ * y)⁻¹ = y⁻¹ * finGL E a u := by
    rw [_root_.mul_inv_rev, inv_inv]
  have hfin : GeneralLinearGroup.map (pFin E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pFin E) y⁻¹ * u := by
    rw [map_mul, pFin_finGL]
  have hinf : GeneralLinearGroup.map (pInf E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pInf E) y⁻¹ := by
    rw [map_mul, pInf_finGL, mul_one]
  unfold tst ker
  rw [hinv, hfin, hinf]
  by_cases hm : GeneralLinearGroup.map (pFin E) y⁻¹ ∈ U
  · rw [if_pos (U.mul_mem hm hu), if_pos hm]
  · rw [if_neg (fun h => hm (by simpa using U.mul_mem h (U.inv_mem hu))), if_neg hm]

theorem convR_tst_mul_finGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ)
    (u : GL (Fin a) (Af E)) (hu : u ∈ U) (x : GA E a) :
    convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  unfold convR
  have h := integral_mul_left_eq_self (μ := μ)
    (fun y => tst U β ((finGL E a u)⁻¹ * y) * Fl (x * y)) (finGL E a u)
  simp only [inv_mul_cancel_left] at h
  simp only [tst_finGL_inv_mul U β u hu] at h
  simpa only [mul_assoc] using h

theorem convR_tst_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (u : GL (Fin a) (Af E)), u ∈ U → ∀ x : GA E a, convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  intro E _ _ _ a μ _ _ U β Fl u hu x
  exact convR_tst_mul_finGL E a μ U β Fl u hu x

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.RedInEx

section Abstract

variable {A : Type} [CommRing A] {I : Ideal A} {γ : DividedPowers I} {l s : ℕ}

theorem one_eq (γ : DividedPowers I) : pdP γ 1 = I := by
  refine le_antisymm (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_one_le γ) fun x hx => ?_
  have h := GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ 1 hx
  rwa [γ.dpow_one hx] at h

theorem mem_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x ∈ I) : x ∈ I := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf 1 ((l : A) ^ N * x) (by
      rw [one_eq]
      rwa [pow_succ', mul_assoc] at h)
    rwa [one_eq] at this

theorem eq_zero_of_pow_mul (hb : TFBase γ l s) (N : ℕ) (x : A) (h : (l : A) ^ N * x = 0) : x = 0 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih ?_
    have := hb.tf s ((l : A) ^ N * x) (by
      rw [hb.nil]
      rw [pow_succ', mul_assoc] at h
      exact h)
    rw [hb.nil] at this
    exact this

theorem mem_of_fact_mul (hb : TFBase γ l s) (k : ℕ) (x : A) (h : (k.factorial : A) * x ∈ I) : x ∈ I := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  refine mem_of_pow_mul hb N x ?_
  rw [← hu, mul_comm _ u, mul_assoc]
  exact Ideal.mul_mem_left _ _ h

theorem eq_of_fact_mul (hb : TFBase γ l s) (k : ℕ) {x y : A} (h : (k.factorial : A) * x = (k.factorial : A) * y) :
    x = y := by
  obtain ⟨N, u, hu⟩ := hb.dv _ k.factorial_ne_zero
  rw [← sub_eq_zero]
  refine eq_zero_of_pow_mul hb N _ ?_
  rw [← hu, mul_comm _ u, mul_assoc, mul_sub, h, sub_self, mul_zero]

theorem dpow_congr (hb : TFBase γ l s) {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (h : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) x = Ideal.Quotient.mk _ y) (k : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) (γ.dpow k x) = Ideal.Quotient.mk _ (γ.dpow k y) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  have haI : a ∈ I := mem_of_pow_mul hb n a (by rw [mul_comm, ha]; exact sub_mem hx hy)
  have hc : (l : A) ^ n * a ∈ I := Ideal.mul_mem_left _ _ haI
  have e : x = y + (l : A) ^ n * a := by rw [mul_comm, ha]; ring

  rw [e, γ.dpow_add hy hc, map_sum, Finset.sum_eq_single (k, 0)]
  · rw [γ.dpow_zero hc, mul_one]
  · rintro ⟨i, j⟩ hij hne
    have hj : j ≠ 0 := by
      rintro rfl
      have : i = k := by simpa using hij
      exact hne (by rw [this])
    change Ideal.Quotient.mk _ (γ.dpow i y * γ.dpow j ((l : A) ^ n * a)) = 0
    rw [γ.dpow_mul haI, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (by
      rw [pow_succ]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · intro h0
    exact absurd (by simp) h0

end Abstract

section Concrete

open PAlg

variable {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A]

def e0 (l : ℕ) [Fact l.Prime] : Acris0 l ≃+* (base l).Acr0 :=
  RingEquiv.ofBijective (base l).cris0 (RL.base_acr (base l) isBase_base).1.1

def lam0 (lam : Acris l →+* A) : (base l).Acr0 →+* A :=
  (lam.comp (algebraMap (Acris0 l) (Acris l))).comp (e0 l).symm.toRingHom

theorem lam0_cris0_eq_lam_of (lam : Acris l →+* A) (y : Acris0 l) :
    lam0 lam ((base l).cris0 y) = lam (AdicCompletion.of _ _ y) := by
  have h : (e0 l).symm ((base l).cris0 y) = y := (e0 l).symm_apply_apply y
  change lam (algebraMap (Acris0 l) (Acris l) ((e0 l).symm ((base l).cris0 y))) = _
  rw [h]
  rfl

theorem lam0_algebraMap_sW_eq_lam_algebraMap (lam : Acris l →+* A) (w : Ainf l) :
    lam0 lam (algebraMap (base l).W (base l).Acr0 ((base l).sW w)) = lam (algebraMap (Ainf l) (Acris l) w) := by
  have h : algebraMap (base l).W (base l).Acr0 ((base l).sW w) = (base l).cris0 (algebraMap (Ainf l) (Acris0 l) w) :=
    Subtype.ext (awayW_algebraMap (base l).s w).symm
  rw [h, lam0_cris0_eq_lam_of, AdicCompletion.algebraMap_apply]

def rho (lam : Acris l →+* A) (n : ℕ) : (base l).Acr n →+* A ⧸ Ideal.span {(l : A) ^ n} :=
  ((base l).cris n).liftOfSurjective ((RL.base_acr (base l) isBase_base).2 n).1
    ⟨(Ideal.Quotient.mk _).comp lam, fun x hx => by
      rw [((RL.base_acr (base l) isBase_base).2 n).2] at hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      have hz : Ideal.Quotient.mk (Ideal.span {(l : A) ^ n}) ((l : A) ^ n) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_mul, map_pow, map_natCast, hz, mul_zero]⟩

theorem rho_cris (lam : Acris l →+* A) (n : ℕ) (c : Acris l) :
    rho lam n ((base l).cris n c) = Ideal.Quotient.mk _ (lam c) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ c

theorem rho_mk (lam : Acris l →+* A) (n : ℕ) (y : (base l).Acr0) :
    rho lam n ((base l).mkAcr n y) = Ideal.Quotient.mk _ (lam0 lam y) := by
  obtain ⟨y, rfl⟩ := (e0 l).surjective y
  change rho lam n ((base l).mkAcr n ((base l).cris0 y)) = Ideal.Quotient.mk _ (lam0 lam ((base l).cris0 y))
  rw [← cris_of, rho_cris, lam0_cris0_eq_lam_of]

variable {I : Ideal A} {γ : DividedPowers I} {s : ℕ}

theorem lam0_mem_of_mem_fil0_one (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) :
    lam0 lam x ∈ I := by
  have : (base l).Fil0 1 ≤ I.comap (lam0 lam) := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    refine mem_of_fact_mul hb k _ ?_
    rw [← map_natCast (lam0 lam), ← map_mul, (RL.filtration_multiplicative (base l)).2.2.1 k, map_pow]
    refine Ideal.pow_mem_of_mem _ ?_ _ hk
    rw [show (base l).xi = (base l).sW (xi0 l) from rfl, lam0_algebraMap_sW_eq_lam_algebraMap]
    exact hξ
  exact this hx

theorem lam0_dpow (hb : TFBase γ l s) (lam : Acris l →+* A)
    (hξ : lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I) {x z : (base l).Acr0} (hx : x ∈ (base l).Fil0 1) (k : ℕ)
    (hz : (k.factorial : (base l).Acr0) * z = x ^ k) : lam0 lam z = γ.dpow k (lam0 lam x) := by
  refine eq_of_fact_mul hb k ?_
  rw [γ.factorial_mul_dpow_eq_pow (lam0_mem_of_mem_fil0_one hb lam hξ hx), ← map_natCast (lam0 lam), ← map_mul, hz, map_pow]

theorem exists_unit_one_add_generator (x : (base l).Acr0) (hx : x ∈ (base l).Fil0 1) (k : ℕ) :
    ∃ z : (base l).Acr0, (k.factorial : (base l).Acr0) * z = x ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨1, by simp⟩
  · obtain ⟨z, -, hz⟩ := (RL.pdi (base l)).1 x hx k hk
    exact ⟨z, hz⟩

end Concrete

theorem redIn_ex : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {A : Type} [CommRing A] [Algebra (OK l K) A]
    {I : Ideal A} (γ : DividedPowers I) (s : ℕ) (lam : Acris l →+* A), TFBase γ l s →
    lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ I →
    (∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w) ∈ I) →
    ∀ n : ℕ, ∃ d : RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) γ l n,
      ∀ c, d.ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (lam c) := by
  intro l _ K A _ _ I γ s lam hb hξ hO n
  have hfil : ∀ x ∈ (PAlg.base l).Fil n 1, ∃ x₀ ∈ (PAlg.base l).Fil0 1, (PAlg.base l).mkAcr n x₀ = x := by
    intro x hx
    rw [((PAlg.base l).isPd_pdFil n).1] at hx
    exact (Ideal.mem_map_iff_of_surjective _ ((PAlg.base l).mkAcr_surjective n)).1 hx
  refine ⟨{ hl := (Fact.out : l.Prime).ne_zero, ρ := rho lam n, mem := ?_, dp := ?_, hκ := ?_ }, rho_cris lam n⟩
  · intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    exact ⟨lam0 lam x₀, lam0_mem_of_mem_fil0_one hb lam hξ hx₀, rho_mk lam n x₀⟩
  · intro k x hx y hy e
    obtain ⟨x₀, hx₀, rfl⟩ := hfil x hx
    obtain ⟨z, hz⟩ := exists_unit_one_add_generator x₀ hx₀ k
    have e1 : (B.DD false (PAlg.base l) n).dpow k ((PAlg.base l).mkAcr n x₀) = (PAlg.base l).mkAcr n z :=
      ((PAlg.base l).isPd_pdFil n).2 k x₀ z hx₀ hz
    rw [e1, rho_mk, lam0_dpow hb lam hξ hx₀ k hz]
    rw [rho_mk] at e
    exact dpow_congr hb (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) hy e k
  · intro a r h
    obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l (okToOC l K a)
    have h1 : B.κb (okToOC l K) false n a = Ideal.Quotient.mk _ ((PAlg.base l).toAcr n ((PAlg.base l).sW w)) := by
      change B.uJ false (PAlg.base l) n ((PAlg.base l).oC (okToOC l K a)) = _
      rw [← hw, PAlg.oC_theta0, B.uJ_th]
    rw [h1] at h
    have h2 : r - (PAlg.base l).toAcr n ((PAlg.base l).sW w) ∈ (PAlg.base l).Fil n 1 :=
      Ideal.Quotient.eq.1 h.symm
    obtain ⟨x₀, hx₀, e⟩ := hfil _ h2
    have h3 : rho lam n r = Ideal.Quotient.mk _ (lam (algebraMap (Ainf l) (Acris l) w) + lam0 lam x₀) := by
      rw [map_add (f := _), ← rho_mk, e, ← PAlg.cris_algebraMap, ← rho_cris, PAlg.cris_algebraMap, map_sub, add_sub_cancel]
    refine ⟨lam0 lam x₀ - (algebraMap (OK l K) A a - lam (algebraMap (Ainf l) (Acris l) w)),
      sub_mem (lam0_mem_of_mem_fil0_one hb lam hξ hx₀) (hO a w hw), ?_⟩
    rw [h3]
    congr 1
    ring

end GlobalTheory.CompanionTheory.RedInEx
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupBeta
open CrystallineSemistableComparison.CH
universe w u v u' v'

theorem pull_cup {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w} R) (m : Mor (modF A) (modF A') (RingHom.id R))
    (hm : ∀ T (x y : A.obj (m.G.obj T)), m.τ T ((mulP A).μ _ x y) = (mulP A').μ T (m.τ T x) (m.τ T y))
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    m.pull n ((mulP A).cup h x y) = (mulP A').cup h (m.pull p x) (m.pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat hm h x y

theorem beta_cup {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ}
    (h : i + j = m) (x : Hc F κ k n i) (y : Hc F κ k n j) :
    β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) =
      (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y) :=
  pull_cup (OcA F κ k n) (AcrEl (F.pt κ) n) (βMor F κ k n) (fun _ _ _ => rfl) h x y

end GlobalTheory.CompanionTheory.CupBeta
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rcalc : RCalc := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ f hf
    exact ⟨fun X => Rd_contDiffOn X hf, fun X Y g hg => Rd_bracket X Y hf hg, fun s m X g hg => Rd_gel X s m hf hg,
      fun s m x hx g hg => ⟨gel_left s m hx hf hg, gel_right s m hx hf hg⟩⟩
  · intro E f hf s m
    exact gel_mem_CE E hf s m
  · intro _ _ μ _ V _ _ _ f hf hc X
    exact ibp n μ V f hf hc X

end GlobalTheory.CompanionTheory.RCalc
end
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegreeBasis

theorem degBasis_of_degBasisG : DegBasisG → DegBasis := by
  intro h E _ _ _ n k x M hM
  rw [← degG_eq x M]
  exact h E n (Fin k) x M hM

end GlobalTheory.CompanionTheory.DegreeBasis
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.sign_cone_weight_translation : ∀ m : ℕ, (∀ y : (Fin m → SignType) → ℝ, Measurable (gam y)) ∧ (∀ (y : (Fin m → SignType) → ℝ) a b, gam (fun e => y e + sdot e b) (a + b) = gam y a) ∧ ∀ (y y' : (Fin m → SignType) → ℝ) e s t a, (∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') → gam (Function.update y e s) a - gam (Function.update y e t) a = gam (Function.update y' e s) a - gam (Function.update y' e t) a := by
  first | exact @GlobalTheory.CompanionTheory.ChainSum.chainSum_rest | exact GlobalTheory.CompanionTheory.ChainSum.chainSum_rest | (intros; apply GlobalTheory.CompanionTheory.ChainSum.chainSum_rest <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.only_isotropic_subspaces : OnlyStable → DegPairing → SizeBasic → OnlyIsotropic := by
  first | exact @GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of | exact GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of | (intros; apply GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.only_stable_subspaces : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  first | exact @GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | exact GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | (intros; apply GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of <;> assumption)
end
