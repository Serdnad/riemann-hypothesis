module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def TestRd (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ),
    ∃ (k : (U σ).Comp) (x : ((U σ).X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n,
      cvalR σ (ψ (f p y)) = u * rdU (U σ) f k x.1

def BCEx (σ : c.F →+* ℂ) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ), ∃ z : FrPt Xo c (CAt σ), FrMap ψ y z

def WtC (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)),
    FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) : Frame Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frInv {Ψ : Finset (E →+* ℂ)} (b : Frame Ψ r) (τ : Ψ) : mat (frInv b) τ = (mat b τ)⁻¹ := rfl

theorem mat_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

theorem eq_zero_of_orbit (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, P (lact γ x) = X.χ la γ * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hz : rmul (lact γ x) b ∈ X.dom) (h0 : P (rmul (lact γ x) b) = 0) : P x = 0 := by
  have hbinv : frInv b ∈ Bor X.Ψ r := by
    intro τ
    obtain ⟨hdet, htri⟩ := hb τ
    have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 hdet
    refine ⟨?_, ?_⟩
    · rw [mat_frInv]
      exact (Matrix.isUnit_nonsing_inv_det_iff.2 hu).ne_zero
    · intro i j hij
      haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu
      have hBT : (mat b τ).BlockTriangular id := fun i' j' h' => htri i' j' h'
      exact Matrix.blockTriangular_inv_of_blockTriangular hBT hij
  have hrm : rmul (rmul (lact γ x) b) (frInv b) = lact γ x := by
    funext τ
    show mat (rmul (lact γ x) b) τ * mat (frInv b) τ = mat (lact γ x) τ
    rw [mat_rmul, mat_frInv, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hb τ).1), Matrix.mul_one]
  have h1 : P (lact γ x) = 0 := by
    have h2 := hB _ hz (frInv b) hbinv
    rw [hrm, h0, mul_zero] at h2
    exact h2
  rw [hΓ γ hγ x hx] at h1
  obtain ⟨n, hn, hχ⟩ := X.χ_fin la
  have hne : X.χ la γ ≠ 0 := by
    intro h
    have h3 := hχ γ hγ
    rw [h, zero_pow hn.ne'] at h3
    exact zero_ne_one h3
  exact (mul_eq_zero.1 h1).resolve_left hne

theorem eqv_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X}
    (hP : P ∈ holSub X la) :
    (∀ k, ∀ x ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, P k (rmul x b) = bchar (la k) b * P k x) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x) := by
  replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    have hQ' : IsHolCusp X la Q := hQ
    exact ⟨fun k x hx b hb => (hQ' k).1.1.2.1 x hx b hb, fun k γ hγ x hx => (hQ' k).1.1.2.2 γ hγ x hx⟩
  | zero => exact ⟨fun k x _ b _ => by simp, fun k γ _ x _ => by simp⟩
  | add Q R _ _ hQ hR =>
    refine ⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩
    · simp only [Pi.add_apply]
      rw [hQ.1 k x hx b hb, hR.1 k x hx b hb]
      ring
    · simp only [Pi.add_apply]
      rw [hQ.2 k γ hγ x hx, hR.2 k γ hγ x hx]
      ring
  | smul a Q _ hQ =>
    refine ⟨fun k x hx b hb => ?_, fun k γ hγ x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hQ.1 k x hx b hb]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hQ.2 k γ hγ x hx]
      ring

variable {D : D7} {Comp : Type} {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
  (mu : GA D V → ℂ)

def AdelAut : Prop :=
  ∀ (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X), IsHolCusp X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P)

def QuotSupp : Prop :=
  ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → onQ V φ =ᵐ[muQ1 V] 0 → ∀ g, φ g = 0

variable {V dict mu}

theorem adelAut_holSub (h : AdelAut V dict mu) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  replace hP : P ∈ Submodule.span ℂ {Q | IsHolCusp X la Q} := hP
  induction hP using Submodule.span_induction with
  | mem Q hQ => exact h la Q hQ
  | zero =>
    refine ⟨fun γ _ g => ?_, ?_⟩
    · simp only [map_zero, Pi.zero_apply]
    · rw [map_zero]
      exact continuous_const
  | add Q R _ _ hQ hR =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · simp only [map_add (f := _), Pi.add_apply, hQ.1 γ hγ g, hR.1 γ hγ g]
    · rw [map_add (f := _)]
      exact hQ.2.add hR.2
  | smul a Q _ hQ =>
    refine ⟨fun γ hγ g => ?_, ?_⟩
    · simp only [map_smul, Pi.smul_apply, hQ.1 γ hγ g]
    · rw [map_smul]
      exact hQ.2.const_smul a

theorem onQ_eq_lift (φ : GA D V → ℂ) (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) :
    onQ V φ = Quotient.lift φ (fun a b hab => by
      have h' : b * a⁻¹ ∈ GQ V := QuotientGroup.rightRel_apply.1 hab
      have := hL _ h' a
      rw [inv_mul_cancel_right] at this
      exact this.symm) := by
  funext q
  exact congrArg (Quotient.lift φ _) (Quotient.out_eq q)

theorem adelMeas_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ}
    (h : AdelAut V dict mu) : AdelMeas U σ V dict mu := by
  intro la P hP
  obtain ⟨hL, hc⟩ := h la P hP
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [onQ_eq_lift _ hL]
  refine Measurable.aestronglyMeasurable ?_
  exact measurable_from_quotient.2 hc.measurable

theorem aeDom_of_aut {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hQ : QuotSupp V) (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) :
    AeDom U σ V dict mu := by
  intro la P hP h0 k x hx
  have hA' := adelAut_holSub hA la hP
  have hz : ∀ g, adel V dict mu P g = 0 := hQ _ hA'.2 hA'.1 h0
  obtain ⟨-, -, -, hdom, hsurj, -⟩ := hd
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hsurj k x hx
  have hm : mu g ≠ 0 := by
    intro h
    have h1 := hmu.2.1 g
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have h1 : mu g * P (dict g).1 (dict g).2 = 0 := hz g
  have h2 : P (dict g).1 (dict g).2 = 0 := (mul_eq_zero.1 h1).resolve_left hm
  have h3 := hdom g
  rw [hg] at h2 h3
  have hE := eqv_holSub (U σ).X la hP
  exact eq_zero_of_orbit ((U σ).X k) (la k) (P k) (hE.1 k) (hE.2 k) hx hγ hb h3 h2

end Adelic

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Models

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adel_leftInv_of_inv {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hm : MuUnit V dict mu)
    (hP : ∀ g, ∀ γ' ∈ (X (dict g).1).Γ, P (dict g).1 (lact γ' (dict g).2) = P (dict g).1 (dict g).2) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g := by
  intro γ hγ g
  obtain ⟨γ', hγ', he⟩ := hd γ hγ g
  show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
  rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
  exact congrArg (mu g * ·) (hP g γ' hγ')

theorem adel_leftInv_of_chi {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g :=
  adel_leftInv_of_inv V dict mu P hd hm fun g γ' hγ' => by
    rw [hΓ _ γ' hγ' _ (hdom g), hχ _ γ' hγ', one_mul]

end Models

section Readings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def RdInvG (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom,
    rdU U f k (lact γ x) = rdU U f k x

def SecGen (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ k, ∃ b m, Dom b m ∧
    (∃ f ∈ sec Xo c b m, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0) ∧
    (∃ f ∈ sec Xo c (a + b) (n + m), ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0)

variable (U : Unf Xo c σ r)

theorem rdU_lact (hU : IsUnf U) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n) {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (k : U.Comp) :
    ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, rdU U f k (lact γ x) = (U.X k).χ (laU U a n k) γ * rdU U f k x :=
  (hU.2.2.2.2.1 a n hdn f hf k).2.2

variable {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ)
  (Kf : Subgroup (GA D V)) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)

theorem rdU_leftInv (hU : IsUnf U) (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1) {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu (rdU U f) (γ * g) = adel V dict mu (rdU U f) g :=
  adel_leftInv_of_chi V dict mu (laU U a n) (rdU U f) hd.1 hd.2.2.2.1 hm (rdU_lact U hU hdn hf) hχ

end Readings

namespace Core

variable {D : D7} (T : Core D)

end Core

end Formalism.L2.Pj
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def BadPin (bad q1 d cond : ℕ) : Prop := 2 ∣ bad ∧ q1 ∣ bad ∧ d ∣ bad ∧ cond ∣ bad

section Reps

variable {n : ℕ} {Tup : Type} (Cl' : Tup → Type)

def RepsCov (dδ : Tup → DeltaDat Xo c n) (bad : Tup → ℕ) (Lh : ∀ t, Cl' t → Submodule (𝓞 E) (Fin n → E))
    (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ) (gam : ∀ t, Cl' t → ℕ) : Prop :=
  ∀ t, RepsOK (l := (dδ t).l₂) (bad t) (La t) (Nc t) (gam t) ∧ LatPin (Lh t) (La t)

end Reps

section Io

variable {n : ℕ} {Ix : Type} [Fintype Ix] (emb : Ix → E →+* c.F) (lam : Ix → DomWeight n)

abbrev VVc : Type := ↥(Formalism.L2.DIV.VV c.F lam)


open Classical in
def rhoM (ga : Matrix (Fin n) (Fin n) E) : VVc c lam →ₗ[c.F] VVc c lam :=
  if h : IsUnit ga.det then Formalism.L2.DIV.rhoVr emb lam (Matrix.nonsingInvUnit ga h) else 0

def nab0M : Submodule (𝓞 c.F) (VVc c lam) := Formalism.L2.DIV.nabAtr emb lam (stdLat E n)

def hwOK (hw : VVc c lam) : Prop :=
  (hw : Formalism.L2.DIV.Pol c.F Ix n) = Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal c.F n (lam τ)

def IoLFRec (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam) : Prop :=
  hwOK c lam hw ∧ ∃ cga : Matrix (Fin n) (Fin n) E → c.F,
    IoLF c a io (rhoM c emb lam) cga (nab0M c emb lam) hw (pG (Dw := Dw) c a n)

end Io

section Dat

variable {n : ℕ}

variable {Tup : Type} (Cl' : Tup → Type)

def WPin (dδ : Tup → DeltaDat Xo c n) (φ : ∀ t, (Fin n → LevQc Dw (dδ t).l₂) → c.F)
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) : Prop :=
  ∀ t (k : Cl' t) (q : Fin n → LevQ Dw (dδ t).l₂),
    (dδ t).eF (w t k q) = phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q

def CovPin (dδ : Tup → DeltaDat Xo c n) : Prop :=
  ∀ t, (dδ t).IsLev ∧ (dδ t).l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab (dδ t).Xo₂ (dδ t).c₂ (dδ t).nab₂

end Dat

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open scoped ComplexConjugate

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem not_isIso_of_p0_zero (X : Data E r) (h0 : X.p0 = 0) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, hh, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (X.cmType τ).2 h⟩
  obtain ⟨P, hP, hG⟩ := X.signature ⟨τ, hτ⟩
  set v : Fin r → ℂ := fun a => τ (ξ a) with hv
  set w : Fin r → ℂ := P⁻¹.mulVec v with hw
  have hPw : P.mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have h1 : hermC τ X.Gm v v = 0 := by
    have := congrArg τ hh
    rw [map_zero] at this
    rw [← this]

    simp only [hermC, herm, map_sum, map_mul, hv, cc, IsCMField.complexEmbedding_complexConj]
  have h2 : hermC τ X.Gm v v = ∑ a, ∑ b, w a * gram τ X.Gm P a b * conj (w b) := by
    have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
        ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := fun f =>
      calc ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ x, ∑ a, ∑ y, ∑ b, f x y a b :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ y, ∑ b, f x y a b := Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ b, ∑ y, f x y a b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have L : ∀ x y, P.mulVec w x * τ (X.Gm x y) * conj (P.mulVec w y) =
        ∑ a, ∑ b, w a * (P x a * τ (X.Gm x y) * conj (P y b)) * conj (w b) := by
      intro x y
      simp only [Matrix.mulVec, dotProduct]

      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]; ring
    rw [← hPw]
    simp only [hermC, L, gram, col, Matrix.of_apply]
    rw [sw]
    simp only [Finset.mul_sum, Finset.sum_mul]
  have h3 : ∑ a, Complex.normSq (w a) = 0 := by
    rw [h2, hG] at h1
    have : ∑ a, (Complex.normSq (w a) : ℂ) = 0 := by
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ hb.symm]) (by simp)]
      simp [sgn, h0, Complex.mul_conj]
    exact_mod_cast this
  have h4 : w = 0 := funext fun a => Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg _).mp h3 a (Finset.mem_univ a))
  apply hne
  funext a
  have : v a = 0 := by rw [← hPw, h4, Matrix.mulVec_zero]; rfl
  exact (map_eq_zero τ).mp this

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

theorem dom_zero : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩

end

variable {D : D7} {T : Core D}

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions

def DatDom (D : D7) (j : ℕ) (hI : DatInt D j) : Prop := DomFor D j (efW D j hI)

def datumOfRecord (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) (hP : FactPrincipalDatum)
    (hd : DatDom D j (datInt_of hP D j)) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum (hostOfRecord D) :=
  datumOf D j (datInt_of hP D j)
    { unimod := efW_unimod_of hP D j _, rank := latW_rank D j hj, dom := hd }

end Formalism.L2.Pj
end
end
