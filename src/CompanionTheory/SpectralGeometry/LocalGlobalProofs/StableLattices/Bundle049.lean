module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle053
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle064
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle092
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle019
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.Development
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.CasimirDS

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem qdet_smooth (hC : PI.DSInfCharCap.DSInfCharCap) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (hR : R.IsDS ε mu) (Q : Mx k r)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub) (hQ : IsUnit Q) (hE : R.IsE Q E)
    (Y : ℂ) (w : R.smSub) :
    Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  have hK : PI.KFinSmooth := CompanionTheory.D.gk.admitted.k_finite_smooth
  obtain ⟨hmu, Q0, hQ0, hDS⟩ := id hR
  have hU0 : IsUnit Q0 := hQ0.1.1
  obtain ⟨E0, hE0, hgl⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR Q0 hU0
  obtain ⟨hsm, hd⟩ := GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport k r ε R Q0 hQ0
  obtain ⟨-, hexp, -⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q0 E0 hU0 hE0
  have hdQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hdQ0 : IsUnit Q0.det := (Matrix.isUnit_iff_isUnit_det Q0).1 hU0
  have hEE : E = Formalism.FourierDecayAlt.Q.Econj E0 (Q0 * Q⁻¹) (Q * Q0⁻¹) := by
    funext a b
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [hE a b v, hexp]
    have h1 : Q0 * (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * Q0⁻¹ =
        (Q0 * Q⁻¹) * Matrix.single a b (1 : ℂ) * (Q * Q0⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [h1]
    simp only [GlobalTheory.CapelliSmooth.entry_conj, Formalism.FourierDecayAlt.Q.Econj, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have h2 : (Q * Q0⁻¹) * (Q0 * Q⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ0, Matrix.mul_nonsing_inv _ hdQ]
  have h3 : (Q0 * Q⁻¹) * (Q * Q0⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ, Matrix.mul_nonsing_inv _ hdQ0]
  rw [hEE, covariant_det_of_lin covariant_linear _ _ E0 _ _ hgl h2 h3]
  apply Subtype.ext
  have h4 := GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator _ ε R.H (fun g => R.σ (Q0⁻¹ * g * Q0)) R.smSub E0
    (fun a b v => by rw [hd, hE0 a b v]; rfl) (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w
  rw [← h4, hC _ ε mu R.H _ hmu hDS w (hsm w w.2) Y]
  rfl

theorem dC_coe (U : URep k r) (Y : Mx k r) (v : U.R.smSub) : (U.dC Y v : U.R.H) = U.R.dC Y v := by
  have h1 := U.dsig_coe (X := reH k r Y) (GlobalTheory.ComplexifiedAction.lie_re Y) v
  have h2 := U.dsig_coe (X := imH k r Y) (GlobalTheory.ComplexifiedAction.lie_im Y) v
  simp only [URep.dC, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, h1, h2]
  rfl

theorem isE_one (U : URep k r) : U.R.IsE 1 (fun a b => U.dC (Matrix.single a b 1)) := by
  intro a b v
  rw [dC_coe, inv_one, Matrix.one_mul, Matrix.mul_one]

theorem cas_smooth (hC : PI.DSInfCharCap.DSInfCharCap) {ε : Fin (2 * r + k + 1) → Bool}
    {μ : Fin (2 * r + k + 1) → ℝ} (U : URep k r) (hk : 1 ≤ k) (hU : U.R.IsDS ε μ) (w : U.R.smSub) :
    (∑ a, ∑ b, U.dC (Matrix.single a b 1) * U.dC (Matrix.single b a 1)) w = (casG μ : ℂ) • w :=
  GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue U.R.smSub (2 * r + k + 1) (fun a b => U.dC (Matrix.single a b 1)) μ (by omega)
    (GlobalTheory.T.derivedAction_expand_matrixUnits CompanionTheory.D.gk.admitted.k_finite_smooth k r ε μ U.R hU 1 _ isUnit_one (isE_one U)).1
    (qdet_smooth hC k r ε μ U.R hU 1 _ isUnit_one (isE_one U)) w

theorem triv_dC (Y : Mx k r) : (triv k r).dC Y = 0 := by
  have h : ∀ X : Mx k r, (triv k r).dR X = 0 := by
    intro X
    funext c d
    simp [FRep.dR]
  simp [FRep.dC, h]

theorem L_one (U : URep k r) (Y : Mx k r) (x : M (one U)) (c : Unit) : L (one U) Y x c = U.dC Y (x c) := by
  have h : (one U).1.dC Y = 0 := triv_dC Y
  simp [L, h, dOp, mAct]

theorem casDS : CasDS := by
  intro hC k r ε μ U hk hU F
  constructor
  · refine LinearMap.ext fun x => funext fun c => ?_
    exact cas_smooth hC U hk hU (x c)
  · refine LinearMap.ext fun x => funext fun c => ?_
    have h := cas_smooth hC U hk hU (x c)
    simp only [LinearMap.sum_apply, Module.End.mul_apply] at h
    simp only [cas, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, L_one]
    exact h

end GlobalTheory.CompanionTheory.CasimirDS

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgIso

open CompanionTheory.RgExh
open Formalism.REAL (GlRel qdet qminor Tm KHighest IsWeight)
open CompanionTheory.D.LK (LocFin IsMin)
open CompanionTheory.D.DSIC (KStab)

variable {n : ℕ}

theorem iso_refl (X : GMod n) : Iso X X := by
  exact ⟨LinearEquiv.refl ℂ X.V, fun a b x => rfl⟩

theorem intertwine_symm {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x))
    (a b : Fin n) (y : Y.V) : e.symm (Y.E a b y) = X.E a b (e.symm y) := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem iso_symm {X Y : GMod n} : Iso X Y → Iso Y X := by
  rintro ⟨e, he⟩
  exact ⟨e.symm, intertwine_symm e he⟩

theorem iso_trans {X Y Z : GMod n} : Iso X Y → Iso Y Z → Iso X Z := by
  rintro ⟨e, he⟩ ⟨f, hf⟩
  exact ⟨e.trans f, fun a b x => by rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he, hf]⟩

def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ V →+* Module.End ℂ W where
  toFun f := e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' f g := by ext; simp
  map_zero' := by ext; simp
  map_add' f g := by ext; simp

theorem cj_apply {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (f : Module.End ℂ V) (w : W) : cj e f w = e (f (e.symm w)) := rfl

theorem cj_smul_one {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (c : ℂ) : cj e (c • (1 : Module.End ℂ V)) = c • (1 : Module.End ℂ W) := by
  refine LinearMap.ext fun w => ?_
  rw [cj_apply]
  simp

theorem cj_algebraMap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (c : ℂ) : cj e (algebraMap ℂ (Module.End ℂ V) c) = algebraMap ℂ (Module.End ℂ W) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, cj_smul_one]

theorem cj_E {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (a b : Fin n) :
    cj e (X.E a b) = Y.E a b := by
  refine LinearMap.ext fun w => ?_
  rw [cj_apply, he, LinearEquiv.apply_symm_apply]

theorem cj_Tm {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (u : ℂ)
    (a b : Fin n) : cj e (Tm X.E u a b) = Tm Y.E u a b := by
  unfold Formalism.REAL.Tm
  rw [map_add (f := _), cj_E e he]
  split_ifs
  · rw [cj_algebraMap]
  · rw [map_zero]

theorem cj_qdet {X Y : GMod n} (e : X.V ≃ₗ[ℂ] Y.V) (he : ∀ a b x, e (X.E a b x) = Y.E a b (e x)) (u : ℂ) :
    cj e (qdet X.E u) = qdet Y.E u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor

  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, cj_Tm e he]

theorem scalChar_of_iso {X Y : GMod n} (h : Iso X Y) (χ : Fin n → ℂ) (hX : ScalChar X χ) : ScalChar Y χ := by
  obtain ⟨e, he⟩ := h
  intro t
  rw [← cj_qdet e he, hX t, cj_smul_one]

theorem hasChar_of_iso {X Y : GMod n} (h : Iso X Y) (χ : Fin n → ℂ) (hX : HasChar X χ) : HasChar Y χ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨k, hk⟩ := hX
  refine ⟨k, fun t => ?_⟩
  rw [← cj_qdet e he, ← cj_smul_one e, ← map_sub, ← map_pow, hk t, map_zero]

theorem isSimple_of_iso {X Y : GMod n} (h : Iso X Y) (hX : IsSimple X) : IsSimple Y := by
  obtain ⟨e, he⟩ := h
  refine ⟨?_, fun S hS => ?_⟩
  · haveI := hX.1
    exact e.symm.toEquiv.nontrivial
  · have hS' : ∀ a b, ∀ x ∈ S.comap (e : X.V →ₗ[ℂ] Y.V), X.E a b x ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by
      intro a b x hx
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
      rw [he]
      exact hS a b _ hx
    rcases hX.2 _ hS' with h0 | h1
    · left
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      have hy' : e.symm y ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by simpa using hy
      rw [h0, Submodule.mem_bot] at hy'
      simpa using hy'
    · right
      rw [eq_top_iff]
      intro y _
      have hy' : e.symm y ∈ S.comap (e : X.V →ₗ[ℂ] Y.V) := by
        rw [h1]
        trivial
      simpa using hy'

theorem locFin_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (hX : LocFin ε X.E) : LocFin ε Y.E := by
  obtain ⟨e, he⟩ := h
  intro y
  obtain ⟨S, hfd, hst, hx⟩ := hX (e.symm y)
  refine ⟨S.map (e : X.V →ₗ[ℂ] Y.V), ?_, ?_, ?_⟩
  · haveI := hfd
    exact Module.Finite.map S _
  · intro a b hab v hv
    obtain ⟨x, hxS, rfl⟩ := Submodule.mem_map.mp hv
    have hm := Submodule.mem_map_of_mem (f := (e : X.V →ₗ[ℂ] Y.V)) (hst a b hab x hxS)
    simpa [he] using hm
  · exact ⟨e.symm y, hx, by simp⟩

theorem isWeight_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (he : ∀ a b x, e (E a b x) = F a b (e x)) {μ : Fin n → ℝ} {x : V} (h : IsWeight E μ x) :
    IsWeight F μ (e x) := by
  intro a
  rw [← he, h a, map_smul]

theorem kHighest_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (he : ∀ a b x, e (E a b x) = F a b (e x)) {μ : Fin n → ℝ} {x : V} (h : KHighest ε E μ x) :
    KHighest ε F μ (e x) := by
  exact ⟨isWeight_of_intertwine e E F he h.1, fun a b hab hε => by rw [← he, h.2 a b hab hε, map_zero]⟩

theorem intWt_of_iso {X Y : GMod n} (h : Iso X Y) (hX : IntWt X) : IntWt Y := by
  obtain ⟨e, he⟩ := h
  intro μ y hy hw
  have hx : e.symm y ≠ 0 := by simpa using hy
  exact hX μ (e.symm y) hx (isWeight_of_intertwine e.symm Y.E X.E (fun a b z => intertwine_symm e he a b z) hw)

theorem algDS_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ)
    (hX : AlgDS ε X s mu) : AlgDS ε Y s mu := by
  obtain ⟨e, he⟩ := h
  obtain ⟨h1, h2, h3, v, hv, hk⟩ := hX
  refine ⟨h1, h2, ?_, e v, by simpa using hv,
    kHighest_of_intertwine e _ (fun a b => X.E (s a) (s b)) (fun a b => Y.E (s a) (s b))
      (fun a b x => he (s a) (s b) x) hk⟩
  intro μ y hy hky
  exact h3 μ (e.symm y) (by simpa using hy)
    (kHighest_of_intertwine e.symm _ (fun a b => Y.E (s a) (s b)) (fun a b => X.E (s a) (s b))
      (fun a b z => intertwine_symm e he (s a) (s b) z) hky)

theorem coneDS_of_iso {X Y : GMod n} (ε : Fin n → Bool) (h : Iso X Y) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ)
    (hX : CompanionTheory.RgExh.Fin.ConeDS ε X s mu) : CompanionTheory.RgExh.Fin.ConeDS ε Y s mu := by
  obtain ⟨e, he⟩ := h
  intro ν y hy hky
  exact hX ν (e.symm y) (by simpa using hy)
    (kHighest_of_intertwine e.symm _ (fun a b => Y.E (s a) (s b)) (fun a b => X.E (s a) (s b))
      (fun a b z => intertwine_symm e he (s a) (s b) z) hky)

theorem isoFacts : CompanionTheory.RgExh.Fin.IsoFacts := by
  intro n ε X Y Z
  exact ⟨iso_refl X, iso_symm, iso_trans, fun h => ⟨isSimple_of_iso h, isSimple_of_iso (iso_symm h)⟩,
    fun h χ => ⟨scalChar_of_iso h χ, scalChar_of_iso (iso_symm h) χ⟩,
    fun h χ => ⟨hasChar_of_iso h χ, hasChar_of_iso (iso_symm h) χ⟩,
    fun h => ⟨locFin_of_iso ε h, locFin_of_iso ε (iso_symm h)⟩,
    fun h => ⟨intWt_of_iso h, intWt_of_iso (iso_symm h)⟩,
    fun h s mu => ⟨algDS_of_iso ε h s mu, algDS_of_iso ε (iso_symm h) s mu⟩,
    fun h s mu => ⟨coneDS_of_iso ε h s mu, coneDS_of_iso ε (iso_symm h) s mu⟩⟩

end GlobalTheory.CompanionTheory.RgIso
end
end

section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh CompanionTheory.RgExh.Fin
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.LK (IsKMod LocFin IsMin)

variable {n : ℕ}

theorem hasChar_path (hS : StepChar) (ss : List (Fin n)) :
    ∀ (X : GMod n) (χ : Fin n → ℂ), HasChar X χ → HasChar (path X χ ss) (pathEnd χ ss) := by
  induction ss with
  | nil => intro X χ h; exact h
  | cons s ss ih => intro X χ h; exact ih _ _ (hS n X χ s h)

theorem hasChar_of_scalChar {X : GMod n} {χ : Fin n → ℂ} (h : ScalChar X χ) : HasChar X χ :=
  ⟨1, fun Y => by rw [pow_one, h Y, sub_self]⟩

theorem capelliPoly_eq_of_perm {χ χ₂ : Fin n → ℂ} (τ τ₂ : Equiv.Perm (Fin n)) (h : ∀ a, χ (τ a) = χ₂ (τ₂ a)) :
    Formalism.QuantumDeterminants.capP χ = Formalism.QuantumDeterminants.capP χ₂ := by
  funext Y
  delta Formalism.QuantumDeterminants.capP
  rw [← Equiv.prod_comp τ (fun s => Y + χ s), ← Equiv.prod_comp τ₂ (fun s => Y + χ₂ s)]
  exact Finset.prod_congr rfl fun a _ => by rw [h a]

def EndOf (ε : Fin n → Bool) (M : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n))
    (d : Equiv.Perm (Fin n) × (Fin n → ℝ)) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : GlRel E), IsUnitary ε E ∧ LocFin ε E ∧ IsSimple ⟨V, E, hE⟩ ∧ AlgDS ε ⟨V, E, hE⟩ d.1 d.2 ∧
      Iso (path M χ ss) ⟨V, E, hE⟩

theorem iso_of_ends (hH : Hecke) (hI : IsoFacts) (hU : AlgUniq) {ε : Fin n → Bool} {M M' : GMod n}
    {χ : Fin n → ℂ} {ss : List (Fin n)} {d : Equiv.Perm (Fin n) × (Fin n → ℝ)}
    (hg : GoodPath χ ss) (hM : IsSimple M) (hM' : IsSimple M') (hc : HasChar M χ) (hc' : HasChar M' χ)
    (hs : ScalChar (path M χ ss) (pathEnd χ ss)) (e : EndOf ε M χ ss d) (e' : EndOf ε M' χ ss d) :
    Iso M M' := by
  obtain ⟨V, i1, i2, E, hE, u, l, sm, a, iso⟩ := e
  obtain ⟨V', j1, j2, E', hE', u', l', sm', a', iso'⟩ := e'
  have h := hU n ε V V' E E' hE hE' d.1 d.2 u u' l l' sm sm' a a'
  have h1 := (hI n ε (path M χ ss) ⟨V, E, hE⟩ ⟨V', E', hE'⟩).2.2.1 iso h
  have h2 := (hI n ε (path M' χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.1 iso'
  have h3 := (hI n ε (path M χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.2.1 h1 h2
  exact (hH n M χ ss hg hM hc hs).2.2 M' hM' hc' h3

theorem finish : StartMod → PathFin → PathExists → PathEndNat → SimpleDistinct → ScalarCharacterOfL2Embedding → UnitarizableOfL2Embedding →
    IsoFacts → CharOfAlgDS → AlgUniq → DataUniq → DSOfArr → DSOfData → KModOf → ArrCount → Finish := by
  intro hSM hPF hPE hPN hSD hSc hUn hI hCh hU hDU hDA hDD hKM hAC hS hH hDec hFR n ε H _ _ σ hσ
  obtain ⟨hcpl, hnt, hur, hir, hsq⟩ := id hσ
  haveI := hcpl
  obtain ⟨D, E, hK⟩ := hKM n ε H σ hur hir
  obtain ⟨hsim, ⟨χ, hχ⟩, hiw⟩ := hSM n ε H σ hur hir hnt D E hK
  obtain ⟨B, hB⟩ := hDec n
  obtain ⟨C, δ, hδ, hP⟩ := hPE n χ B
  obtain ⟨N₀, hN₀⟩ := hFR n C δ hδ
  obtain ⟨ss, N, hN, hg, hfar, hall, hgap, hbd⟩ := hP N₀
  have key : ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (D' : Submodule ℂ H')
      (E' : Fin n → Fin n → Module.End ℂ D') (hK' : IsKMod ε σ' D' E'), GlobalTheory.Dec.IsSqIntIrr ε σ' →
      IsSimple ⟨D', E', hK'.gl⟩ → ScalChar ⟨D', E', hK'.gl⟩ χ → IntWt ⟨D', E', hK'.gl⟩ →
      SimplePath χ ss ∧ ScalChar (path ⟨D', E', hK'.gl⟩ χ ss) (pathEnd χ ss) ∧
        ∃ d : Equiv.Perm (Fin n) × (Fin n → ℝ), EndOf ε ⟨D', E', hK'.gl⟩ χ ss d ∧
          Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
          ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = pathEnd χ ss (τ a) := by
    intro H' _ _ _ σ' D' E' hK' hs' hsm' hsc' hiw'
    obtain ⟨_, _, ur, ir, sq⟩ := id hs'
    have hcX := hasChar_of_scalChar hsc'
    have hL := hB ε H' σ' D' E' hK' χ ss ur ir sq hcX hg hfar
    have hce := hasChar_path hS ss _ χ hcX
    have hse := hSc n ε _ _ hL hce
    obtain ⟨sp, sm, -⟩ := hH n _ χ ss hg hsm' hcX hse
    obtain ⟨V, i1, i2, EV, hEV, hun, iso⟩ := hUn n ε _ hL sm
    have facts := hI n ε (path ⟨D', E', hK'.gl⟩ χ ss) ⟨V, EV, hEV⟩ ⟨V, EV, hEV⟩
    have smV : IsSimple ⟨V, EV, hEV⟩ := (facts.2.2.2.1 iso).1 sm
    have scV : ScalChar ⟨V, EV, hEV⟩ (pathEnd χ ss) := (facts.2.2.2.2.1 iso _).1 hse
    have lfV : LocFin ε EV := (facts.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).1 hK'.locFin)
    have iwV : IntWt ⟨V, EV, hEV⟩ := (facts.2.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).2 hiw')
    obtain ⟨s', mu', hAlg⟩ := hN₀ ε V EV hEV (pathEnd χ ss) N smV.1 hun lfV iwV scV hN hgap hbd
    obtain ⟨τ, hτ⟩ := hCh n ε V EV hEV (pathEnd χ ss) s' mu' hun lfV scV hAlg
    exact ⟨sp, hse, (s', mu'), ⟨V, i1, i2, EV, hEV, hun, lfV, smV, hAlg, iso⟩, hAlg.1, hAlg.2.1, τ, hτ⟩
  obtain ⟨sp, hse, d₀, e₀, hc₀, ho₀, τ₀, hτ₀⟩ := key H σ D E hK hσ hsim hχ hiw
  have hend : ∀ a, pathEnd χ ss a = ((d₀.2 (τ₀.symm a) : ℝ) : ℂ) := fun a => by
    rw [hτ₀, Equiv.apply_symm_apply]
  have hinj' : Function.Injective (pathEnd χ ss) := fun a b h => by
    rw [hend, hend] at h
    exact τ₀.symm.injective (hc₀.1.injective (Complex.ofReal_injective h))
  have hr' : ∀ a, (pathEnd χ ss a).im = 0 ∧ ∃ m : ℤ, (pathEnd χ ss a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    rw [hend]
    exact ⟨Complex.ofReal_im _, by simpa using hc₀.2 (τ₀.symm a)⟩
  obtain ⟨m, hm, -⟩ := hPN n χ ss
  have hχa : ∀ a, χ a = pathEnd χ ss a - (m a : ℂ) := fun a => by
    rw [hm]; simp
  have hr : ∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    obtain ⟨h1, k, h2⟩ := hr' a
    refine ⟨by rw [hχa]; simp [h1], k - m a, ?_⟩
    rw [hχa]
    simp only [Complex.sub_re, Complex.natCast_re]
    push_cast
    linarith
  have hinj := hSD n χ ss sp hall
  obtain ⟨A, A', hcard, hA, hA'⟩ := hAC n ε χ (pathEnd χ ss) hinj hinj' hr hr'
  have per : ∀ d : Equiv.Perm (Fin n) × (Fin n → ℝ), ∃ (M : GMod n) (e : Equiv.Perm (Fin n) × (Fin n → ℝ)),
      d ∈ A → e ∈ A' ∧ IsSimple M ∧ HasChar M χ ∧ ScalChar (path M χ ss) (pathEnd χ ss) ∧
        EndOf ε M χ ss e ∧ AlgDS ε M d.1 d.2 ∧ ConeDS ε M d.1 d.2 := by
    intro d
    by_cases hd : d ∈ A
    · obtain ⟨hhc, hord, τ, hτ⟩ := (hA d).1 hd
      obtain ⟨H', i1, i2, i3, σ', hsi, hall'⟩ := hDA n ε d.1 d.2 hhc hord
      obtain ⟨_, hnt', ur', ir', _⟩ := id hsi
      obtain ⟨D', E', hK'⟩ := hKM n ε H' σ' ur' ir'
      obtain ⟨s1, ⟨χd, hχd⟩, iw⟩ := hSM n ε H' σ' ur' ir' hnt' D' E' hK'
      obtain ⟨hAlg, hCone⟩ := hall' D' E' hK'
      obtain ⟨τ', hτ'⟩ := hCh n ε D' E' hK'.gl χd d.1 d.2 hK'.unit hK'.locFin hχd hAlg
      have hcap : Formalism.QuantumDeterminants.capP χd = Formalism.QuantumDeterminants.capP χ :=
        capelliPoly_eq_of_perm τ' τ fun a => by rw [← hτ', ← hτ]
      have hsc : ScalChar ⟨D', E', hK'.gl⟩ χ := fun Y => by rw [hχd Y, hcap]
      obtain ⟨-, hse', e, he, hce, hoe, τe, hτe⟩ := key H' σ' D' E' hK' hsi s1 hsc iw
      exact ⟨⟨D', E', hK'.gl⟩, e, fun _ => ⟨(hA' e).2 ⟨hce, hoe, τe, hτe⟩, s1, hasChar_of_scalChar hsc, hse', he,
        hAlg, hCone⟩⟩
    · exact ⟨triv n, d, fun h => absurd h hd⟩
  haveI : Nonempty (GMod n) := ⟨triv n⟩
  choose! M e hMe using per
  have hmaps : Set.MapsTo e (A : Set _) (A' : Set _) := fun d hd => (hMe d hd).1
  have hinjA : Set.InjOn e (A : Set _) := by
    intro d₁ h₁ d₂ h₂ heq
    obtain ⟨-, s1, c1, p1, n1, a1, k1⟩ := hMe d₁ h₁
    obtain ⟨-, s2, c2, p2, n2, a2, k2⟩ := hMe d₂ h₂
    rw [← heq] at n2
    have hiso := iso_of_ends hH hI hU hg s1 s2 c1 c2 p1 n1 n2
    have a2' : AlgDS ε (M d₁) d₂.1 d₂.2 :=
      ((hI n ε (M d₁) (M d₂) (M d₁)).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
    obtain ⟨q1, q2⟩ := hDU n ε (M d₁) _ _ _ _ a1 k1 a2'
    exact Prod.ext q1 q2
  have hsurj := Finset.surjOn_of_injOn_of_card_le e hmaps hinjA hcard.symm.le
  obtain ⟨d, hd, hde⟩ := hsurj ((hA' d₀).2 ⟨hc₀, ho₀, τ₀, hτ₀⟩)
  obtain ⟨-, s2, c2, p2, n2, a2, -⟩ := hMe d hd
  rw [hde] at n2
  have hiso := iso_of_ends hH hI hU hg hsim s2 (hasChar_of_scalChar hχ) c2 hse e₀ n2
  have aX : AlgDS ε ⟨D, E, hK.gl⟩ d.1 d.2 :=
    ((hI n ε ⟨D, E, hK.gl⟩ (M d) ⟨D, E, hK.gl⟩).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
  obtain ⟨hhc, hord, -⟩ := (hA d).1 hd
  exact ⟨d.1, d.2, hhc, hord, hDD n ε H σ D E hK d.1 d.2 hσ aX⟩

end GlobalTheory.CompanionTheory.RgExhFin
end
end
