module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle025
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle329
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwich
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

theorem GlobalTheory.WeilVacuum.smooth_flow : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ T : ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ, (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ A : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) →
    A 0 = LinearMap.id →
    (∀ (t : ℝ) (p q : V) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β p q ⇑f →
      ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f)) →
    (∀ f x, Continuous fun t => T t f x) →
    ∀ J₀ : (V × V) →ₗ[ℝ] (V × V), (∀ w, J₀ (J₀ w) = -w) →
    ∀ f₀ : SchwartzMap V ℂ, (∀ w x, GlobalTheory.GaussLine.dHeis β (J₀ w) ⇑f₀ x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑f₀ x) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => T p.1 f₀ p.2) ∧
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ) (c : ℂ), ∀ x,
      HasDerivAt (fun t => T t f₀ x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ) * f₀ x + c * f₀ x) 0 := by
  intro V _ _ _ _ _ μ _ β hβ T hadd h0 hunit A hAc hAadd hA0 hint hcont J₀ hJ₀ f₀ hf₀
  by_cases hz : f₀ = 0
  · subst hz
    have hT0 : ∀ t, T t 0 = 0 := fun t => map_zero _
    refine ⟨?_, 0, Fin.elim0, Fin.elim0, Fin.elim0, 0, fun x => ?_⟩
    · simp only [hT0, SchwartzMap.zero_apply]; exact contDiff_const
    · simp only [hT0, SchwartzMap.zero_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_mul, add_zero]
      exact hasDerivAt_const _ _
  have hAsm := GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear A hAc hAadd hA0
  have hinv : ∀ t w, A t (A (-t) w) = w := by
    intro t w
    have := congrArg (fun L => L w) (hAadd t (-t))
    simp only [add_neg_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this
    exact this.symm
  have hinv' : ∀ t w, A (-t) (A t w) = w := by
    intro t w
    have := congrArg (fun L => L w) (hAadd (-t) t)
    simp only [neg_add_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this
    exact this.symm
  set J : ℝ → (V × V) →ₗ[ℝ] (V × V) := fun t => (A t).comp (J₀.comp (A (-t))) with hJdef
  have hJapp : ∀ t w, J t w = A t (J₀ (A (-t) w)) := fun t w => rfl
  have hJsm : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w := by
    intro w
    have e : (fun t => J t w) = fun t => (LinearMap.toContinuousLinearMap (A t))
        ((LinearMap.toContinuousLinearMap J₀) ((LinearMap.toContinuousLinearMap (A (-t))) w)) := by
      funext t; simp [hJapp]
    rw [e]
    exact hAsm.clm_apply ((LinearMap.toContinuousLinearMap J₀).contDiff.comp
      ((hAsm.comp contDiff_neg).clm_apply contDiff_const))
  have hJsq : ∀ t w, J t (J t w) = -w := by
    intro t w; simp only [hJapp, hinv', hJ₀, map_neg, hinv]
  have hFock : ∀ t w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑(T t f₀) x =
      Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑(T t f₀) x := by
    intro t w x
    set u := A (-t) w
    obtain ⟨g1, hg1⟩ := GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative β (J₀ u) f₀
    obtain ⟨g2, hg2⟩ := GlobalTheory.T.exists_schwartz_heisenbergOperatorDerivative β u f₀
    have hg12 : g1 = Complex.I • g2 := by
      ext y; rw [SchwartzMap.smul_apply, hg1, hg2, hf₀, smul_eq_mul]
    have hI : ∀ w₁ : V × V, ∀ (s : ℝ) (f g : SchwartzMap V ℂ),
        ⇑g = GlobalTheory.GaussLine.heisFun β (s • w₁).1 (s • w₁).2 ⇑f →
        ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (s • A t w₁).1 (s • A t w₁).2 ⇑(T t f) := by
      intro w₁ s f g h
      have := hint t (s • w₁).1 (s • w₁).2 f g h
      rwa [Prod.mk.eta, map_smul] at this
    have h1 := GlobalTheory.T.heisenberg_equivariant_isometry μ β (T t) (hunit t) (J₀ u) (A t (J₀ u)) (hI _) f₀ g1 hg1 x
    have h2 := GlobalTheory.T.heisenberg_equivariant_isometry μ β (T t) (hunit t) u (A t u) (hI _) f₀ g2 hg2 x
    have hu : A t u = w := hinv t w
    rw [hu] at h2
    rw [hJapp, ← h1, ← h2, hg12, map_smul, SchwartzMap.smul_apply, smul_eq_mul]
  have hne : ∀ t, T t f₀ ≠ 0 := by
    intro t h
    apply hz
    have := hadd (-t) t f₀
    rw [neg_add_cancel, h0, h, map_zero] at this
    exact this
  obtain ⟨M, hMs, hMj, hMdec, hMuniq, n, qs, qs', cs, hMder⟩ :=
    GlobalTheory.T.fockVacua_smooth_family_complexGaussians β hβ J hJsm hJsq (fun t => ⟨T t f₀, hne t, hFock t⟩)
  set cc : ℝ → ℂ := fun t => T t f₀ 0 with hccdef
  have hrep : ∀ t x, T t f₀ x = cc t * Complex.exp (M t x x) := fun t x => hMuniq t (T t f₀) (hFock t) x
  obtain ⟨hK, hKne⟩ := GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag μ M hMs hMdec
  set K : ℝ → ℝ → ℂ := fun u v => ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M v x x)) ∂μ with hKdef
  have hexp : ∀ u v, ∫ x, T u f₀ x * starRingEnd ℂ (T v f₀ x) ∂μ = cc u * starRingEnd ℂ (cc v) * K u v := by
    intro u v
    simp_rw [hrep, map_mul]
    rw [hKdef, ← integral_const_mul]
    congr 1; funext x; ring
  have hpol := fun s => GlobalTheory.T.schwartz_isometry_inner_product_eq μ (T s) (hunit s)
  have eq1 : ∀ s t, cc (s + t) * starRingEnd ℂ (cc s) * K (s + t) s = cc t * starRingEnd ℂ (cc 0) * K t 0 := by
    intro s t
    have := hpol s (T t f₀) (T 0 f₀)
    rw [← hadd, ← hadd, add_zero] at this
    rw [← hexp, ← hexp, this]
  have eq2 : ∀ s, cc s * starRingEnd ℂ (cc s) * K s s = cc 0 * starRingEnd ℂ (cc 0) * K 0 0 := by
    intro s
    have := hpol s f₀ f₀
    rw [← hexp, ← hexp, this, h0]
  have hc0 : cc 0 ≠ 0 := by
    intro h; apply hz; ext x
    rw [← h0 f₀, hrep, h, zero_mul, SchwartzMap.zero_apply]
  have hcs : ∀ s, cc s ≠ 0 := by
    intro s h
    have := eq2 s
    rw [h, zero_mul, zero_mul] at this
    exact mul_ne_zero (mul_ne_zero hc0 ((map_ne_zero _).2 hc0)) (hKne 0) this.symm
  have hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2 := hK.continuous
  set U : Set (ℝ × ℝ) := {p | K (p.1 + p.2) p.1 ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun (hKc.comp ((continuous_fst.add continuous_snd).prodMk continuous_fst)) continuous_const
  have hU0 : ∀ s, (s, 0) ∈ U := by intro s; simp only [hUdef, Set.mem_setOf_eq, add_zero]; exact hKne s
  set E : ℝ → ℝ → ℂ := fun s t => K s s * K t 0 / (cc 0 * K 0 0 * K (s + t) s) with hEdef
  have hEsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U := by
    have k1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.1 p.1) := hK.comp (contDiff_fst.prodMk contDiff_fst)
    have k2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.2 0) := hK.comp (contDiff_snd.prodMk contDiff_const)
    have k3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K (p.1 + p.2) p.1) :=
      hK.comp ((contDiff_fst.add contDiff_snd).prodMk contDiff_fst)
    have hinvd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (cc 0 * K 0 0 * K (p.1 + p.2) p.1)⁻¹) U :=
      ((contDiff_const.mul k3).contDiffOn).inv (fun p hp => mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)
    have := (k1.mul k2).contDiffOn.mul hinvd
    simpa only [hEdef, div_eq_mul_inv] using this
  have hfe : ∀ p ∈ U, cc (p.1 + p.2) = cc p.1 * cc p.2 * E p.1 p.2 := by
    rintro ⟨s, t⟩ hp
    simp only [hUdef, Set.mem_setOf_eq] at hp
    simp only [hEdef]
    have hd : starRingEnd ℂ (cc 0) ≠ 0 := (map_ne_zero _).2 hc0
    rw [mul_div_assoc', eq_div_iff (mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)]
    apply mul_left_cancel₀ hd
    linear_combination (-(cc (s + t) * K (s + t) s)) * eq2 s + (cc s * K s s) * eq1 s t
  have hccc : Continuous cc := by
    have := hcont f₀ 0
    exact this
  have hcsm := GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect cc E U hccc hc0 hUo hU0 hEsm hfe
  have hfun : (fun p : ℝ × V => T p.1 f₀ p.2) = fun p => cc p.1 * Complex.exp (M p.1 p.2 p.2) := by
    funext p; exact hrep p.1 p.2
  refine ⟨?_, n, qs, qs', cs, deriv cc 0 / cc 0, fun x => ?_⟩
  · rw [hfun]; exact (hcsm.comp contDiff_fst).mul hMj.cexp
  · have hft : (fun t => T t f₀ x) = fun t => cc t * Complex.exp (M t x x) := by funext t; exact hrep t x
    rw [hft]
    have hdc : HasDerivAt cc (deriv cc 0) 0 := ((hcsm.differentiable (by simp)) 0).hasDerivAt
    refine (hdc.mul (hMder x).cexp).congr_deriv ?_
    have hf0x : f₀ x = cc 0 * Complex.exp (M 0 x x) := by rw [← hrep 0 x, h0]
    rw [hf0x, ← Finset.sum_mul]
    field_simp
    ring

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rational_complement_isotropic_sandwich : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) ∧ (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ z : Mx D 1 k, (∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.cplx V W B c)) = 1) ↔ z ∈ GlobalTheory.MixModel.ratMx D 1 k) := by
  first | exact @GlobalTheory.IsoCompl.ratCompl | exact GlobalTheory.IsoCompl.ratCompl | (intros; apply GlobalTheory.IsoCompl.ratCompl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TransportedLine

variable {D : D7}

theorem exp_mem_UH_of_lie {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit H.det) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * H + H * X = 0) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : (t • X)ᴴ = H * (-(t • X)) * H⁻¹ := by
    have h1 : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Xᴴ = -(H * X) * H⁻¹ := by rw [← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * H * NormedSpace.exp (t • X) = H
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem gramAt_det_isUnit (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
  rw [this]
  exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit

variable (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e)

def toUXHom : GA D X →* GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := GlobalTheory.TripleRead.toUX X e hJ
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    show (mt X 1).submatrix e e = 1
    simp [Formalism.L2.Theta.mt]
  map_mul' a b := by
    refine Subtype.ext (Units.ext ?_)
    show (mt X (a * b)).submatrix e e = (mt X a).submatrix e e * (mt X b).submatrix e e
    simp [Formalism.L2.Theta.mt, Matrix.submatrix_mul_equiv]

theorem continuous_toUX : Continuous (GlobalTheory.TripleRead.toUX X e hJ) := by
  have hm : Continuous fun g : GA D X => (matHom X g) := continuous_subtype_val
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · have hv : Continuous fun g : GA D X =>
        (matHom X g).1 := Units.continuous_val.comp hm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (e j)).comp ((continuous_apply (e i)).comp hv)
  · have hv : Continuous fun g : GA D X =>
        ((matHom X g)⁻¹).1 := Units.continuous_coe_inv.comp hm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    refine ((continuous_apply (e j)).comp ((continuous_apply (e i)).comp hv)).congr fun g => ?_
    show ((matHom X g)⁻¹).1 (e i) (e j) = (mt X g⁻¹) (e i) (e j)
    simp [Formalism.L2.Theta.mt]

def finIncl (F : Type) [Field F] [NumberField F] : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F →ₗ[F] AF F where
  toFun a := ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  map_add' a b := by
    show ((0, a + b) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + ((0, b) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp
  map_smul' c a := by
    show ((0, c • a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = c • ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp

theorem smul_eq_zero_of_snd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : AF F ⊗[F] E) (hx : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x = 0) (u : AF F)
    (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F u = 0) : u • x = 0 := by
  let e : AF F := ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  have h1 : (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 = 0 :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have hu' : u = u * e := by
    refine Prod.ext ?_ ?_
    · show (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 = (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 * 0
      rw [mul_zero]; exact h1
    · show (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).2 = (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).2 * 1
      rw [mul_one]
  have key : ∀ y : AF F ⊗[F] E,
      e • y = (finIncl F).rTensor E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      show ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a) =
        ((0, (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a).2) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
      refine Prod.ext ?_ ?_
      · exact zero_mul _
      · exact one_mul _
    | add y z hy hz => rw [smul_add, hy, hz, map_add (f := _), map_add (f := _)]
  rw [hu', mul_smul, key, hx, map_zero, smul_zero]

theorem toUX_mem_UAt (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    {g : GA D X} (hg : g ∈ GinfC X) :
    GlobalTheory.TripleRead.toUX X e hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Z (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have h1 : (finHom X g).val = 1 := by rw [show finHom X g = 1 from hg]; rfl
  have hM : ∀ a b, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.L2.Theta.mt X g - 1) a b) = 0 := by
    intro a b
    have e2 := congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 ((congrArg id e2).trans ?_)
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.TripleRead.toUX X e hJ g) - 1 = (Formalism.L2.Theta.mt X g - 1).submatrix e e := by
    show (Formalism.L2.Theta.mt X g).submatrix e e - 1 = _
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  rw [hr]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, Matrix.submatrix_apply]
  exact smul_eq_zero_of_snd _ _ _ (hM _ _) u hu

theorem continuous_exp_smul {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • Y) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end GlobalTheory.TransportedLine

namespace GlobalTheory.TransportedLine

theorem exists_line_toUX_oneP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e) (τ : D.what₂.Tau),
    ∀ Y ∈ lieAt X τ, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Z,
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e hJ (oneP θ X τ Y t) := by
  intro D θ hθ X k e Z hJ τ Y hY
  have hU : ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D X τ) :=
    exp_mem_UH_of_lie (gramAt_det_isUnit X τ) hY
  let φ : Multiplicative ℝ →* GA D X :=
    { toFun := fun t => oneP θ X τ Y (Multiplicative.toAdd t)
      map_one' := by
        show atTau θ X τ (NormedSpace.exp ((0 : ℝ) • Y)) = 1
        rw [zero_smul, NormedSpace.exp_zero]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ X τ
      map_mul' := fun s t => by
        show atTau θ X τ (NormedSpace.exp ((Multiplicative.toAdd s + Multiplicative.toAdd t) • Y)) =
          atTau θ X τ (NormedSpace.exp (Multiplicative.toAdd s • Y)) * atTau θ X τ (NormedSpace.exp (Multiplicative.toAdd t • Y))
        rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
        exact GlobalTheory.PointAtPlaceHom.atTau_mul hθ X τ (hU _) (hU _) }
  refine ⟨(toUXHom X e hJ).comp φ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · have hc : Continuous fun t : ℝ => oneP θ X τ Y t :=
      (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ X τ).comp_continuous (continuous_exp_smul Y) hU
    exact (continuous_toUX X e hJ).comp (hc.comp continuous_toAdd)
  · exact toUX_mem_UAt X e Z hJ (GlobalTheory.PointAtPlaceHom.atTau_mem X τ _)

end GlobalTheory.TransportedLine

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly

variable {D : D7}

theorem toUX_one (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) : GlobalTheory.TripleRead.toUX X e hJ 1 = 1 := by
  apply Subtype.ext; apply Units.ext
  show (GlobalTheory.TripleRead.toUX X e hJ 1).1.1 = 1
  rw [GlobalTheory.TripleRead.toUX_val]
  simp [Formalism.L2.Theta.mt]


end GlobalTheory.TripleAssembly
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DarbImageRevB

variable {D : D7}

theorem incM_mul {m : ℕ} (G H : Matrix (Fin m) (Fin m) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D := D) (G * H) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM H :=
  Matrix.map_mul

theorem incM_one {m : ℕ} : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D := D) (1 : Matrix (Fin m) (Fin m) D.host.E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def crd {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d) :
    Matrix (Fin m) (Fin k) (AE D) ≃+ Matrix (Fin d) (Fin m) (AE D) where
  toFun u := HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)
  invFun x := GlobalTheory.TripleRead.ptO G e x
  left_inv u := by
    simp only [GlobalTheory.TripleRead.ptO]
    rw [Matrix.mul_assoc, ← incM_mul, Matrix.mul_nonsing_inv _ hG, incM_one, Matrix.mul_one]
    ext i j
    simp
  right_inv x := by
    have e1 : ((GlobalTheory.TripleRead.ptO G e x)ᵀ.submatrix e.symm id) = HMul.hMul x (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹) := by
      ext i j
      simp [GlobalTheory.TripleRead.ptO]
    simp only [e1]
    rw [Matrix.mul_assoc, ← incM_mul, Matrix.nonsing_inv_mul _ hG, incM_one, Matrix.mul_one]
  map_add' u v := by
    rw [← Matrix.add_mul]
    rfl

end GlobalTheory.DarbImageRevB

end
end
