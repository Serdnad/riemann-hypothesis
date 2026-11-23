module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle016
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle069
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle073
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle068
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle044
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle037
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle028
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle072
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle063
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle060
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle079
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt

@[expose] public section

section

noncomputable section

namespace GlobalTheory.FiniteOrderRule

open Formalism.L2.Pj

theorem eq_zero_of_forall_algHom {K R Ω : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R]
    [Algebra.FiniteType K R] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (x : R)
    (h : ∀ φ : R →ₐ[K] Ω, φ x = 0) : x = 0 := by
  have hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hb : (⊥ : Ideal R).jacobson = ⊥ := hJ.out (Ideal.isRadical_bot)
  rw [← Ideal.mem_bot, ← hb, Ideal.jacobson, Ideal.mem_sInf]
  rintro J ⟨-, hM⟩
  letI := Ideal.Quotient.field J
  haveI : Module.Finite K (R ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ J)
  let ψ : (R ⧸ J) →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have h0 := h (ψ.comp (Ideal.Quotient.mkₐ K J))
  have h1 : Ideal.Quotient.mk J x = 0 := by
    apply ψ.toRingHom.injective
    rw [map_zero]
    exact h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

theorem pow_eq_one_of_complex {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (hW : EvalWD pts mapR)
    (hB : ∀ (S : Type) [CommRing S] [Algebra K S] (T : Type) [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
      (y : pts S), ∃ z : pts T, mapR φ y z)
    (σ : K →+* ℂ) (f : Rules pts) (hf : IsNatural pts mapR f) (k : ℕ)
    (h : ∀ y : pts (CAt σ), evalAt pts mapR f y ^ k = 1) (p : TRing K) (y : pts p.R) : f p y ^ k = 1 := by
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  rw [← sub_eq_zero]
  letI : Algebra K ℂ := σ.toAlgebra
  refine eq_zero_of_forall_algHom (K := K) (Ω := ℂ) _ ?_
  intro φ
  let φ' : p.R →ₐ[K] CAt σ := φ
  obtain ⟨z, hz⟩ := hB p.R (CAt σ) φ' y
  have hT : FromTest pts mapR z := ⟨p, φ', y, hz⟩
  have h0 := h z
  unfold evalAt at h0
  rw [dite_eq_left hT, ← hW f hf (CAt σ) p _ φ' _ y _ z hz hT.choose_spec.choose_spec.choose_spec] at h0
  show φ' _ = 0
  rw [map_sub, map_pow, h0, map_one, sub_self]

theorem evalAt_pow_eq_one {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (f : Rules pts) (k : ℕ) (h : ∀ (p : TRing K) (y : pts p.R), f p y ^ k = 1)
    {S : Type} [CommRing S] [Algebra K S] (y : pts S) (hT : FromTest pts mapR y) :
    evalAt pts mapR f y ^ k = 1 := by
  unfold evalAt
  rw [dite_eq_left hT, ← map_pow, h, map_one]

end GlobalTheory.FiniteOrderRule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem GlobalTheory.FiniteOrderRule.unitC_of_cmp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false → UnitC d := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet hC A y
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hk : Nat.card Cls ≠ 0 := Nat.card_pos.ne'
  have h1 := GlobalTheory.FiniteOrderRule.pow_eq_one_of_complex (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) (GlobalTheory.Frames.algebraic_laws hS E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw d.l₂ d.Xo₂ d.c₂ S T φ y)
    d.c₂.F.val.toRingHom d.cδ hC.1.1 (Nat.card Cls) (fun z => by
      have h2 := hC.2 z
      unfold evR at h2
      rw [h2, if_neg Bool.false_ne_true, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one,
        Units.val_one, map_one])
  have h3 := @GlobalTheory.FiniteOrderRule.evalAt_pow_eq_one d.c₂.F _ (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) d.cδ (Nat.card Cls) h1 ℂ _ A y
    (@GlobalTheory.Frames.allTest_of_secBaseChange hS E _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ _ inferInstance A y)
  exact Complex.norm_eq_one_of_pow_eq_one h3 hk

end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem covAut_eF {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F) (a : c.F) :
    covAut d ta (d.eF a) = d.eF (ta a) := by
  show d.eF (ta (d.eF.symm (d.eF a))) = _
  rw [AlgEquiv.symm_apply_apply]

theorem thLa_conj (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F)
    (h₂ : Fixes d.c₂ (covAut d ta)) [StarRing (𝓞 E)] (hN : IsNab d.Xo₂ d.c₂ d.nab₂) (u : c.F) (hu : u ≠ 0)
    (w w' : (Fin n → LevQ Dw d.l₂) → c.F) (hw : ∀ q, ta (w q) = u * w' q) (La : GenLat E n) (N : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (k : Type) [CommRing k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k) (v : Tw (covAut d ta) k)
    (hv : thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) La N
      (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) (twPt h₂ y₂) v) :
    thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w' q)) La N
      (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (MvPolynomial.map (ta : c.F →+* c.F) P)) y₂
      (algebraMap d.c₂.F k (d.eF u⁻¹) * v.val) := by
  have h1 := GlobalTheory.T.shortSeriesValue_twisted_eq_conjugate_value hC E H Dw d.l₂ d.Xo₂ d.c₂ (covAut d ta) h₂ d.nab₂ hN n a _
    ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP) _ La 1 N k y₂ v hv
  have h3 := (GlobalTheory.T.level_fourier_transform_aut_and_homogeneous E H Dw d.l₂ d.Xo₂ d.c₂ n).2.2 d.nab₂ _ La _ (d.eF u⁻¹) N _ k y₂ _ h1
  have e1 : (fun q => d.eF u⁻¹ * covAut d ta (d.eF (w q))) = fun q => d.eF (w' q) := by
    funext q
    rw [covAut_eF, hw, ← map_mul, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  have e2 : MvPolynomial.map (covAut d ta : d.c₂.F →+* d.c₂.F) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
      MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (MvPolynomial.map (ta : c.F →+* c.F) P) := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun g => MvPolynomial.map g P) (RingHom.ext fun a => covAut_eF d ta a)
  rw [e1, e2, map_one] at h3
  exact h3

theorem isThClsD_galRul : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ (n : ℕ) (d : DeltaDat Xo c n) (h₂ : Fixes d.c₂ (covAut d ta)), (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → ∀ (cx : Rul d.Xo₂ d.c₂) (ka u : c.F), ka ≠ 0 → u ≠ 0 → (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ (galRul h₂ d.cδ) y₂ = algebraMap d.c₂.F k (d.eF ka) * evR d.Xo₂ d.c₂ cx y₂) → ∀ (Cl : Type) [Fintype Cl] (w w' : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (a : (E →+* ℂ) × ℕ → ℕ), (∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → (∀ k q, ta (w k q) = u * w' k q) → ∀ x x' : Cl → Vs, (∀ k, io (x' k) = MvPolynomial.map (ta : c.F →+* c.F) (io (x k))) → ∀ (m : ℕ), ∀ f ∈ sec Xo c a m, IsThClsD Xo c d w La Nc gam vol ep io x f → (ka * u)⁻¹ • galRul h f ∈ sec Xo c a m ∧ IsThClsD Xo c { d with cδ := cx } w' La Nc gam (ta vol) (fun k => ta (ep k)) io x' ((ka * u)⁻¹ • galRul h f) := by
  intro hC E _ _ _ H Dw l Xo c ta h n d h₂ hN hδ cx ka u hka hu hcx Cl _ w w' La Nc gam vol ep Vs _ _ io a hio hw
    x x' hx m f hf hT
  obtain ⟨_, hN⟩ := hN
  obtain ⟨hs, hv⟩ := (GlobalTheory.T.conjugateSection_values_semilinear E H Dw l Xo c ta h).1 a m f hf
  have hv₂ := ((GlobalTheory.T.conjugateSection_values_semilinear E H Dw d.l₂ d.Xo₂ d.c₂ (covAut d ta) h₂).1 0 0 d.cδ hδ).2
  refine ⟨Submodule.smul_mem _ _ hs, ?_⟩
  intro k _ _ A A₂ hk y y₂ hy
  letI A₂' : Algebra d.c₂.F k := A₂
  have hk' : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := hk
  obtain ⟨vc, hvc, he⟩ := @hT k _ _ (inferInstance : Algebra c.F (Tw ta k))
    (inferInstance : Algebra d.c₂.F (Tw (covAut d ta) k))
    (fun a => by
      show algebraMap d.c₂.F k (covAut d ta (d.eF a)) = algebraMap c.F k (ta a)
      rw [covAut_eF, hk'])
    (twPt h y) (twPt h₂ y₂) hy
  refine ⟨fun cl => algebraMap d.c₂.F k (d.eF u⁻¹) * vc cl, fun cl => ?_, ?_⟩
  · rw [hx]
    exact thLa_conj hC d ta h₂ hN u hu (w cl) (w' cl) (hw cl) (La cl) (Nc cl) a _ (hio _) k y₂ (vc cl) (hvc cl)
  · have e0 : evR Xo c ((ka * u)⁻¹ • galRul h f) y = algebraMap c.F k (ka * u)⁻¹ * evR Xo c (galRul h f) y :=
      evalAt_smul _ _ _ _ y
    have he' : evR Xo c (galRul h f) y = evR d.Xo₂ d.c₂ (galRul h₂ d.cδ) y₂ *
        ∑ cl, algebraMap c.F k (ta (vol * ((gam cl : c.F))⁻¹ * ep cl)) * vc cl := by
      rw [hv k y, hv₂ k y₂]
      exact he
    show _ = evR d.Xo₂ d.c₂ cx y₂ * _
    rw [e0, he', hcx k y₂, hk', hk']
    have hka' : algebraMap c.F k ka ≠ 0 := (map_ne_zero _).2 hka
    simp only [map_mul, map_inv₀, map_natCast, mul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun cl _ => ?_
    field_simp

end GlobalTheory.GalTw
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaForm

private theorem frMap_id_self {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have eid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 (Sp S) := Spec.map_id _
  have did : spMap (dualMap (AlgHom.id c.F S).toRingHom) = 𝟙 _ := by
    have : dualMap (AlgHom.id c.F S).toRingHom = RingHom.id _ :=
      RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [this]
    exact Spec.map_id _
  refine ⟨by rw [eid, Category.id_comp], fun τ i => by rw [did, Category.id_comp], 𝟙 _, by simp,
    by rw [eid]; simp, ?_⟩
  intro i h
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx y.x).presheaf.map_id]
    rfl
  rw [e, CommRingCat.hom_id, RingHom.id_apply]

theorem exists_small_coeff_etaValAt_ne_zero : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → 1 < R → ∀ [Fintype (LatMod Dw R)] (n : ℕ) (x₀ : Fin n → Dw.La) (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (Nc : ℕ) (y : Fin Nc → FrPt Xo c K), ∃ cf : (Fin n → LatMod Dw R) → ℕ, (∀ j, cf j ≤ Nc * Nat.card (LevGrp Dw (R ^ 4))) ∧ ∀ k v, EtaValAt Xo c R (fun j => (cf j : ℤ)) (shiftFam R x₀) (y k) v → v ≠ 0 := by
  intro hL E _ _ _ H Dw l Xo c R hodd hR _ n x₀ K _ _ _ Nc y
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  haveI : Finite (LevGrp Dw (R ^ 4)) := (GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R hR).1
  letI : Fintype (LevGrp Dw (R ^ 4)) := Fintype.ofFinite _
  have hlev := GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (by positivity)
  choose ev hev using fun k => hlev.2.2.2 K (y k).x
  have hpow : ∀ k q, ev k q ^ ((R ^ 2) ^ 2) = 1 := by
    intro k q
    have h := (hlev.2.1 K K (RingHom.id K) (y k).x (y k).x (𝟙 _)
      (by rw [Over.id_left]; exact (Spec.map_id _).symm) (ev k) (hev k)).2 q
    rwa [← pow_mul]
  choose w hw using fun k q =>
    ((GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hodd.pow).1 K (y k) (ev k q) (hpow k q)).exists
  obtain ⟨cf, hcf, hne⟩ := exists_sum_natCast_smul_apply_ne_zero (K := K)
    (V := Fin Nc × LevGrp Dw (R ^ 4) → K) (W := fun _ : Fin Nc × LevGrp Dw (R ^ 4) => K)
    (fun a => LinearMap.proj a)
    (fun (j : Fin n → LatMod Dw R) a => ∏ b, w a.1 (a.2 (shiftFam R x₀ j b)))
    (fun a => by
      obtain ⟨u, hu⟩ := GlobalTheory.exists_shift_nullVal_ne_zero hL E H Dw l Xo c R hodd hR K (y a.1) (ev a.1) (w a.1) (hev a.1) (hw a.1)
        n x₀ a.2
      refine ⟨u, ?_⟩
      rw [LinearMap.proj_apply]
      exact Finset.prod_ne_zero_iff.2 fun b _ => hu b)
  refine ⟨cf, fun j => ?_, fun k v hv => ?_⟩
  · have := hcf j
    rwa [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card] at this
  · have h0 : EtaValAt Xo c R (fun j => (cf j : ℤ)) (shiftFam R x₀) (y k)
        (etaExpr (R ^ 4) (fun j => (cf j : ℤ)) (shiftFam R x₀) (w k)) :=
      ⟨K, inferInstance, inferInstance, AlgHom.id c.F K, y k, ev k, w k,
        RingHom.FaithfullyFlat.of_bijective Function.bijective_id, frMap_id_self (y k), hev k, hw k, rfl⟩
    have hu := ((GlobalTheory.EtaForm.etaValAt_existsUnique_natural hL E H Dw l Xo c R hodd _ n (fun j => (cf j : ℤ)) (shiftFam R x₀)).1 K (y k)).unique
      hv h0
    rw [hu, etaExpr, finprod_eq_prod_of_fintype]
    refine Finset.prod_ne_zero_iff.2 fun g _ => ?_
    have := hne (k, g)
    simpa [Finset.sum_apply] using this

end GlobalTheory.EtaForm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm.ScalarWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem finite_aut (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LevGrp Dw k) := by
  haveI : Finite (LatMod Dw k) := by
    haveI := Dw.fin
    haveI : Module.Finite ℤ (LatMod Dw k) := Module.Finite.trans (𝓞 E) _
    refine Module.finite_of_fg_torsion (M := LatMod Dw k) fun x => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
    change (k : ℤ) • Submodule.mkQ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) x = 0
    rw [natCast_zsmul, ← map_nsmul]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  exact Finite.of_injective (fun g : LevGrp Dw k => (g : LatMod Dw k → LatMod Dw k)) DFunLike.coe_injective

theorem etaExpr_scale {S : Type} [CommRing S] {k : ℕ} (hk : 0 < k) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) (t : S) :
    etaExpr k cf x (fun q => t * w q) = t ^ (n * Nat.card (LevGrp Dw k)) * etaExpr k cf x w := by
  haveI := finite_aut Dw hk
  haveI := Fintype.ofFinite (LevGrp Dw k)
  unfold etaExpr
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, pow_mul,
    ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem frBor_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

theorem exists_level_of_eq {k : ℕ} {S : Type} [CommRing S] {x₀ x₁ : Sp S ⟶ Xo.X} (h : x₁ = x₀)
    {ev : LatMod Dw k → (ptO Xo x₀ ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x₀ ev) :
    ∃ ev' : LatMod Dw k → (ptO Xo x₁ ⟶ Xo.univ.t.G), IsFullLev Xo k x₁ ev' ∧ ∀ q, (ev' q).left = (ev q).left := by
  subst h
  exact ⟨ev, hev, fun _ => rfl⟩

theorem etaValAt_frBor (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ}
    {x : J → Fin n → LatMod Dw (R ^ 4)} {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ}
    {y y' : FrPt Xo c S} (h : FrBor t y y') {v : S} (hv : EtaValAt Xo c R cf x y v) :
    EtaValAt Xo c R cf x y' ((t none : S) ^ (n * Nat.card (LevGrp Dw (R ^ 4))) * v) := by
  obtain ⟨S', _, _, φ, z, ev, w, hφ, hz, hev, hw, hv⟩ := hv
  obtain ⟨z', hz'⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S S' φ y'
  have hb := frBor_baseChange φ h hz hz'
  obtain ⟨ev', hev', he⟩ := exists_level_of_eq hb.1 hev
  refine ⟨S', _, _, φ, z', ev', fun q => φ (t none) * w q, hφ, hz', hev', fun q => ?_, ?_⟩
  · exact (GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).2.2 S' z z' _ hb (ev q) (ev' q) (he q) (w q) (hw q)
  · rw [etaExpr_scale (pow_pos hR.pos _), map_mul, map_pow, hv]

end GlobalTheory.EtaForm.ScalarWeight

namespace GlobalTheory.EtaForm

theorem isEtaRule_existsUnique_mem_sec : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4)), (∃! f, IsEtaRule Xo c R cf x f) ∧ ∀ f, IsEtaRule Xo c R cf x f → f ∈ sec Xo c 0 (n * Nat.card (LevGrp Dw (R ^ 4))) := by
  intro hL E _ _ _ H Dw l Xo c R hR J _ n cf x
  obtain ⟨hex, hnat⟩ := GlobalTheory.EtaForm.etaValAt_existsUnique_natural hL E H Dw l Xo c R hR J n cf x
  refine ⟨⟨fun p y => (hex p.R y).exists.choose, fun p y => (hex p.R y).exists.choose_spec, fun f hf => ?_⟩,
    fun f hf => ⟨fun p q φ y z h => ?_, fun p t y y' h => ?_⟩⟩
  · funext p y
    exact (hex p.R y).unique (hf p y) (hex p.R y).exists.choose_spec
  · exact (hnat p.R q.R φ y z h _ _ (hf p y) (hf q z)).symm
  · rw [(hex p.R y').unique (hf p y') (ScalarWeight.etaValAt_frBor hL hR h (hf p y))]
    congr 1
    simp [wchar, ex, Fintype.prod_option]

end GlobalTheory.EtaForm
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem GlobalTheory.Shares.exists_anFacts_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (N : ℕ) (ka wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (CR c : ℝ), addL wF wL Tn = ka → Nonempty (ArchAt h j w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → TieMaxCuspSt h j CR Tn c ka → ∃ (R : Rdg (recPlusN h j hj n)) (t : Idx D j N → ℂ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t ∧ AnFacts R w t ka wF Tn (WeightFamilies.MggK n.base CR Tn c j ka) xs := by
  intro D T h j hj n N ka wL wF w Tn CR c hka hA hOn hM hTie
  subst hka
  obtain ⟨A⟩ := hA
  obtain ⟨R, e, hR⟩ := GlobalTheory.T.exists_base_embedding_reading_forms D T h j hj n
  obtain ⟨t, ht, ⟨Fl⟩⟩ := GlobalTheory.T.exists_algIndependent_coeffs_flatDatum D T h j hj N wL wF w Tn _ A
  classical
  let ι : Type := Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ
  have : Fintype ι := inferInstance
  let en : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let xs : Fin (Fintype.card ι) → R.Y := fun q =>
    e.symm ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩
  have hxs : ∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩ :=
    fun q => e.apply_symm_apply _
  have h1 := GlobalTheory.T.points_interpolation_genericSections D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn
  refine ⟨R, t, _, xs, ?_, h1.1, h1.2,
    GlobalTheory.T.cuspForm_vanishing_at_points_mul_pow_mem_span D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn,
    GlobalTheory.T.leadingProducts_independent_modulo_deepProducts D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    GlobalTheory.T.archimedean_flat_decomposition_indexing D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    GlobalTheory.T.finrank_lower_bound_cuspForm_vanishing_low_coeff D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs CR c rfl hM,
    GlobalTheory.T.cuspForm_vanishing_low_coeff_mem_leading_add_deep_span D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn CR c rfl ?_⟩
  · intro Q hQ
    have hσ : R.σ = T.σ₀ := RingHom.ext hR.1
    rw [hσ]
    exact ht Q hQ
  · exact fun F hF => (hTie F).1 hF
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC

theorem frOver_isLev_ddBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (d : DeltaDat Xo c n), (∀ (k : Type) [CommRing k] [Algebra c.F k] [Algebra c'.F k] [Algebra d.c₂.F k] [A₂ : Algebra (covCoeff hle d).F k] (h : AlgOver c c' hle k) (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k) (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (y : FrPt Xo c' k), @FrOver E _ _ _ H Dw l Xo c' n (ddBC hle d) k _ _ A₂ y₂ y ↔ FrOver d (y₂.res (le_covCoeff hle d) h₂) (y.res hle h)) ∧ (d.IsLev → (ddBC hle d).IsLev) := by
  intro E _ _ _ H Dw l Xo c c' hle n d
  refine ⟨fun k _ _ _ _ _ _ _ _ _ => Iff.rfl, ?_⟩
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hB := (GlobalTheory.T.ruleBaseChange_section_values_semilinear E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d)).1 0 0 d.cδ h8
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, hB.1, ?_⟩
  · intro k _ _ A A₂ hA y
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI B : Algebra c.F k := @resAlg E _ _ _ H l c c' hle k _ A
    letI B₂ : Algebra d.c₂.F k := @resAlg E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ A₂'
    have h : @AlgOver E _ _ _ H l c c' hle k _ B A := fun _ => rfl
    have h₂ : @AlgOver E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ B₂ A₂' := fun _ => rfl
    obtain ⟨z, hz⟩ := @h7 k _ _ B B₂ (fun a => hA (incF c c' hle a)) (@FrPt.res E _ _ _ H Dw l c c' hle Xo k _ B A h y)
    exact ⟨@FrPt.ext E _ _ _ H Dw d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) d.Xo₂ k _ B₂ A₂' h₂ z, hz⟩
  · intro k _ _ A₂ y₂
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI B₂ : Algebra d.c₂.F k := @resAlg E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ A₂'
    have h₂ : @AlgOver E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ B₂ A₂' := fun _ => rfl
    intro h0
    exact @h9 k _ _ B₂ _ ((@hB.2 k _ B₂ A₂' h₂ y₂).symm.trans h0)

end GlobalTheory.FieldBC
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.short_theta_value_linear_in_polynomial : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, Q i ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (u : Fin m → S), ShortValAt Xo c nab w Λ β N (∑ i, cf i • Q i) y v → (∀ i, ShortValAt Xo c nab w Λ β N (Q i) y (u i)) → v = ∑ i, algebraMap c.F S (cf i) * u i := by
  first | exact @GlobalTheory.shortThetaValue_linear | exact GlobalTheory.shortThetaValue_linear | (intros; apply GlobalTheory.shortThetaValue_linear <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.theta_rules_linear_and_level_congruence : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (x : Fin n → Dw.La) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) (g : Fin m → Rul Xo c), (∀ i, Q i ∈ harmA c a n) → (∑ i, cf i • Q i) ∈ harmA c a n → IsThRule Xo c nab x (∑ i, cf i • Q i) f → (∀ i, IsThRule Xo c nab x (Q i) (g i)) → f = ∑ i, cf i • g i) ∧ ∀ (x x' : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), (∀ b, x b - x' b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → IsThRule Xo c nab x P f → IsThRule Xo c nab x' P f := by
  first | exact @GlobalTheory.ThetaRule.isThRule_linear_and_congr | exact GlobalTheory.ThetaRule.isThRule_linear_and_congr | (intros; apply GlobalTheory.ThetaRule.isThRule_linear_and_congr <;> assumption)
end
