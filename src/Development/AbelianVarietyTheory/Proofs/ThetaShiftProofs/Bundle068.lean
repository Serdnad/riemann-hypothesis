module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormCmArcCoefficientFunctionalLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle067
import Mathlib.Algebra.MvPolynomial.Funext
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_coeff_ne_zero_of_fourierJacobi_arcDatum : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c (em.comp (algebraMap c.F K₁)) r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → _root_.Formalism.L2.PjFree.GoodEmb c (em.comp (algebraMap c.F K₁)) → _root_.Formalism.L2.PjFree.IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → Comparison₂ Uw d.a em s.ξ k ξ' x → ∀ F ∈ sec Xo c a' n, (∀ k', (U.X k').IsBddSec (laU U a' n k') (_root_.Formalism.L2.PjFree.rdU U F k')) → (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (_root_.Formalism.L2.PjFree.rdU U F k) x ≠ 0 → ∃ mo : ArcLt Dw →₀ ℕ, cfOf d.yF mo d.jj F ≠ 0 := by
  first | exact @GlobalTheory.DerivativeDetermination.exists_cfOf_ne_zero | exact GlobalTheory.DerivativeDetermination.exists_cfOf_ne_zero | (intros; apply GlobalTheory.DerivativeDetermination.exists_cfOf_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcKill

theorem eq_zero_of_eval_off {σ : Type} {P Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0)
    (h : ∀ x, MvPolynomial.eval x Q ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have : P * Q = 0 := MvPolynomial.funext fun x => by
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x Q = 0
    · rw [hx, mul_zero]
    · rw [h x hx, zero_mul]
  exact (mul_eq_zero.1 this).resolve_right hQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem coeff_eq_zero_of_invBl (S : Finset (ArcLt Dw →₀ ℕ)) (f : (ArcLt Dw →₀ ℕ) → ℂ)
    (h : ∀ x : ArcLt Dw → ℂ, InvBl x → ∑ mo ∈ S, f mo * ∏ v ∈ mo.support, x v ^ mo v = 0) : ∀ mo ∈ S, f mo = 0 := by
  classical
  let Q : MvPolynomial (ArcLt Dw) ℂ := ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)).det
  have hQe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x Q ≠ 0 ↔ InvBl x := fun x => by
    rw [map_prod, Finset.prod_ne_zero_iff]
    refine forall_congr' fun τ => ?_
    have : (MvPolynomial.eval x).mapMatrix (Matrix.of fun i k : Fin (Dw.mult τ) =>
        (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)) =
        Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩ := by
      ext i k : 2
      simp
    rw [RingHom.map_det, this]
    simp
  have hone : InvBl (Dw := Dw) fun v => (1 : Matrix (Fin (Dw.mult v.1)) (Fin (Dw.mult v.1)) ℂ) v.2.1 v.2.2 :=
    fun τ => (Matrix.det_one (n := Fin (Dw.mult τ)) (R := ℂ)).trans_ne one_ne_zero
  have hQ : Q ≠ 0 := fun h0 => (hQe _).2 hone (by rw [h0, map_zero])
  have hP : ∑ mo ∈ S, MvPolynomial.monomial mo (f mo) = 0 := eq_zero_of_eval_off hQ fun x hx => by

    rw [map_sum, ← h x ((hQe x).1 hx)]
    exact Finset.sum_congr rfl fun mo _ => MvPolynomial.eval_monomial
  intro mo hmo
  have := congrArg (AddMonoidAlgebra.coeff · mo) hP
  rw [MvPolynomial.coeff_sum] at this
  simpa [MvPolynomial.coeff_monomial, hmo] using this

theorem cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (em : K₁ →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c (em.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Fam n' La c₁ d → Formalism.L2.PjFree.GoodEmb c (em.comp (algebraMap c.F K₁)) → Formalism.L2.PjFree.IsUnf U → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, (∀ k, rdU U F k ∈ (U.X k).SSgt (laU U a' n k) c₁) → cfOf d.yF d.μ d.jj F = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ em r U a' n hfam hgood hunf hdom htv F hF hS
  obtain ⟨⟨hover, -, hpush⟩, ⟨s⟩⟩ := hfam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hmain⟩ := GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5
    E H Dw l Xo c K₁ d em r U s.ξ s.ν₀ a' n (hK.ev E H Dw l Xo c) hgood hunf hover s.tan hpush s.rk s.ξ_ne s.beta
    hdom htv
  have hν : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    have h1 := TraceFormIndependence.trace_re (U.X k) s.ν₀
    have h2 := s.tr
    rw [h1, ← Finset.mul_sum] at h2
    linarith
  have h0 : ∀ x, InvBl x → ajAt d em F x = 0 := fun x hx => by
    have := hmain F hF (hS k).1.1 x hx
    rw [(hS k).2 ξ' hiso _ hν _ (hfr x hx), mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_right (zpow_ne_zero _ hu)
  unfold cfOf
  by_cases hmo : d.μ ∈ (arcNum (evR Xo c F d.yF)).support
  · exact (map_eq_zero em).1 (coeff_eq_zero_of_invBl _
      (fun mo => em (((arcNum (evR Xo c F d.yF)).coeff mo).coeff d.jj)) h0 _ hmo)
  · rw [MvPolynomial.notMem_support_iff.1 hmo]
    rfl

end GlobalTheory.ArcKill
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

namespace GlobalTheory.ArcKill

theorem sum_cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c (ι.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (La c₁ : ℝ), Formalism.L2.PjFree.GoodEmb c (ι.comp (algebraMap c.F K₁)) → Formalism.L2.PjFree.IsUnf U → Fam n' La c₁ d → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c) (f : ∀ k : U.Comp, Frame (U.X k).Ψ r → ℂ), (∀ i, F i ∈ sec Xo c a' n) → (∀ i k, (U.X k).IsBddSec (laU U a' n k) (rdU U (F i) k)) → (∀ k, f k ∈ (U.X k).SSgt (laU U a' n k) c₁) → (∀ k, ∀ x ∈ (U.X k).dom, f k x = ∑ i, a i * rdU U (F i) k x) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d ι r U a' n n' La c₁ hG hU hFam hDom hT m a F f hF hB hf hfe
  obtain ⟨⟨hob, -, hpush⟩, ⟨s⟩⟩ := hFam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hid⟩ :=
    GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5 E H Dw l Xo c K₁ d ι r U s.ξ s.ν₀ a' n
      (hK.ev E H Dw l Xo c) hG hU hob s.tan hpush s.rk s.ξ_ne s.beta hDom hT
  refine GlobalTheory.T.coeff_eq_zero_of_vanish_on_invertibleLetterBlocks E H Dw l Xo c K₁ d ι m a F fun x hx => ?_
  have hlin := GlobalTheory.T.fourierJacobi_coeff_linear_bounded_sections E r (U.X k) (laU U a' n k) m a (fun i => rdU U (F i) k) (f k) (fun i => hB i k)
    (hfe k) ξ' hiso (fun τ => (τ.1 s.ν₀).re) (fr x) (hfr x hx)
  have htr : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    rw [GlobalTheory.sum_re_cmType_eq_half_trace E r (U.X k) s.ν₀]
    exact s.tr
  have h0 := (hf k).2 ξ' hiso (fun τ => (τ.1 s.ν₀).re) htr (fr x) (hfr x hx)
  have hz : u₁ ^ d.jj ≠ 0 := zpow_ne_zero _ hu
  refine (mul_eq_zero.mp ?_).resolve_right hz
  rw [h0] at hlin
  rw [Finset.sum_mul]
  have : ∀ i, a i * ajAt d ι (F i) x * u₁ ^ d.jj =
      κ x * (a i * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U (F i) k) (fr x)) := by
    intro i
    rw [mul_assoc, hid (F i) (hF i) (hB i k) x hx]
    ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, ← hlin, mul_zero]

end GlobalTheory.ArcKill
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.norm_cmArcCoefficientFunctional_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c (em.comp (algebraMap c.F K₁)) r) (xi S : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → 1 ≤ La → Formalism.L2.PjFree.GoodEmb c (em.comp (algebraMap c.F K₁)) → Formalism.L2.PjFree.IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = xi) → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, 0 ≤ S → (∀ k, ∀ y ∈ (U.X k).dom, Formalism.L2.PjFree.lieFac Dw xi a' * (U.X k).pnorm (laU U a' n k) (rdU U F k) y ≤ S) → ‖em (cfOf d.yF d.μ d.jj F)‖ * (s.valLine d.μ n).n em ≤ S * Real.exp (4 * Real.pi + GlobalTheory.ArcCM.archP E r La c₁ * ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n)) := by
  first | exact @GlobalTheory.ArchCM.norm_cfOf_le | exact GlobalTheory.ArchCM.norm_cfOf_le | (intros; apply GlobalTheory.ArchCM.norm_cfOf_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_cmArcData_at_splitIsotropicPoint : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : _root_.Formalism.L2.PjFree.Unf Xo c c.F.val.toRingHom r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La₀ La c₁ : ℝ) (lam : Fin (r - 2) → Fin r → E) (n' : ℕ) (ν₀ : E), _root_.Formalism.L2.PjFree.IsUnf U → l.A = 1 → 3 ≤ r → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La₀ (hX ▸ x) lam → La₀ ^ 2 ≤ La ^ 2 → 0 < n' → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (em : K₁ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (s : CMIn a e th jj n' La c₁), em.comp (algebraMap c.F K₁) = c.F.val.toRingHom ∧ s.ν₀ = ν₀ ∧ Comparison₂ Uw a em s.ξ k ξ' x := by
  first | exact @GlobalTheory.ArcCM.Exist.exists_cmIn_tie | exact GlobalTheory.ArcCM.Exist.exists_cmIn_tie | (intros; apply GlobalTheory.ArcCM.Exist.exists_cmIn_tie <;> assumption)
end
