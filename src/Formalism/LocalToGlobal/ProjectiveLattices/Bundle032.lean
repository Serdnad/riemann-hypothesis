module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle030
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle073
public import Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_injective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab c σ) := by
  intro τ₁ τ₂ h
  ext a
  have := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective this)

theorem relab_rt_iff (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt <;> assumption

variable {σ : c.F →+* ℂ}



open Classical in
def nCol (U : Unf Xo c σ r) (n : ℕ) (k : U.Comp) (j : Fin r) : ℝ :=
  if (U.X k).p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℝ) else -((n / 2 : ℕ) : ℝ)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


open Classical in
theorem rdU_mul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (f g : Rul Xo c) : rdU U (f * g) = rdU U f * rdU U g := by
  funext k x
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c (f * g) (U.un k ⟨x, h⟩)) else 0) =
    (if h : x ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x, h⟩)) else 0) *
      (if h : x ∈ (U.X k).dom then toC (evR Xo c g (U.un k ⟨x, h⟩)) else 0)
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨x, h⟩)
  · simp

theorem laU_add {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (hn : Even n)
    (hn' : Even n') (k : U.Comp) : laU U (a + a') (n + n') k = laU U a n k + laU U a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  have h1 : (m + m) / 2 = m := by omega
  have h2 : (m' + m') / 2 = m' := by omega
  have h3 : (m + m + (m' + m')) / 2 = m + m' := by omega
  funext τ j
  simp only [laU, Pi.add_apply, h1, h2, h3]
  split_ifs <;> push_cast <;> ring

theorem holSub_mul (hM : SiegelSpaceAlgebra (E := E)) {Comp : Type} {X : Comp → Data E r} {la la' : ∀ k, Wt (X k).Ψ r}
    {P Q : FDSec X} (hP : P ∈ holSub X la) (hQ : Q ∈ holSub X la') : P * Q ∈ holSub X (la + la') := by
  first | exact UpperTheory.Reformulated.B.Qe28.holSub_mul .. | (apply UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe28.holSub_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q hP hQ | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q hP | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P Q | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' P | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la la' | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X la | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp X | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM Comp | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r hM | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› r | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E ‹_› | exact @UpperTheory.Reformulated.B.Qe28.holSub_mul E

theorem cusp_mul_of_M5 (hM : SiegelSpaceAlgebra (E := E)) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : CuspMul Xo c U := by
  intro a a' n n' f g hd hd' hf hg
  rw [mem_cusp] at hf hg ⊢
  refine ⟨mulC_mem_sec Xo c a a' n n' hf.1 hg.1, fun σ hσ => ?_⟩
  have hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n' :=
    funext fun k => laU_add (U σ) a a' n n' hd.2 hd'.2 k
  show rdU (U σ) (f * g) ∈ holSub (U σ).X (laU (U σ) (a + a') (n + n'))
  rw [rdU_mul, hla]
  exact holSub_mul hM (hf.2 σ hσ) (hg.2 σ hσ)

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

section Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem supE_add_le (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  unfold supE
  refine iSup_le fun p => ?_
  have h1 : (X p.1).pnorm (la p.1) ((P + Q) p.1) p.2 ≤
      (X p.1).pnorm (la p.1) (P p.1) p.2 + (X p.1).pnorm (la p.1) (Q p.1) p.2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  calc ENNReal.ofReal ((X p.1).pnorm (la p.1) ((P + Q) p.1) p.2)
      ≤ ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2) +
          ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2) :=
        (ENNReal.ofReal_le_ofReal h1).trans ENNReal.ofReal_add_le
    _ ≤ (⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) +
          ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2) :=
        add_le_add (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p)
          (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2)) p)

theorem supE_smul (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  show ‖a * P p.1 p.2‖ * _ = ‖a‖ * (‖P p.1 p.2‖ * _)
  rw [norm_mul]
  ring

theorem supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  unfold holSub at h
  induction h using Submodule.span_induction with
  | mem P hP =>
    have hb : ∀ c, ∃ C : ℝ, ∀ x ∈ (X c).dom, (X c).pnorm (la c) (P c) x ≤ C := fun c => (hP c).1.2
    choose C hC using hb
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ c, |C c|))
      (iSup_le fun p => ENNReal.ofReal_le_ofReal ?_)
    calc (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ C p.1 := hC p.1 p.2 p.2.2
      _ ≤ |C p.1| := le_abs_self _
      _ ≤ ∑ c, |C c| := Finset.single_le_sum (fun c _ => abs_nonneg (C c)) (Finset.mem_univ _)
  | zero =>
    refine ne_top_of_le_ne_top ENNReal.zero_ne_top (iSup_le fun p => ?_)
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm]
  | add P Q _ _ hP hQ =>
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hP, hQ⟩) (supE_add_le X la P Q)
  | smul a P _ hP =>
    rw [supE_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP

end Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)


open Classical in
def goodOf (σ : c.F →+* ℂ) : c.F →+* ℂ := if GoodEmb c σ then σ else (starRingEnd ℂ).comp σ

theorem norm_goodOf (σ : c.F →+* ℂ) (x : c.F) : ‖goodOf c σ x‖ = ‖σ x‖ := by
  unfold goodOf
  split_ifs <;> simp

theorem goodEmb_goodOf (σ : c.F →+* ℂ) : GoodEmb c (goodOf c σ) := by
  unfold goodOf
  split_ifs with h
  · exact h
  · unfold GoodEmb at h ⊢
    set β := (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ with hβ
    have hβsq : β ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, hβ, ← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
    have hneg : β = -H.rt0 := by
      have hm : (β - H.rt0) * (β + H.rt0) = 0 := by
        rw [show (β - H.rt0) * (β + H.rt0) = β ^ 2 - H.rt0 ^ 2 by ring, hβsq, sub_self]
      rcases mul_eq_zero.mp hm with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) h
      · exact eq_neg_of_add_eq_zero_left h1
    have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h3 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h2 h3
    have hre : H.rt0.re = 0 := by
      rcases mul_eq_zero.mp (show H.rt0.re * H.rt0.im = 0 by nlinarith) with h4 | h4
      · exact h4
      · rw [h4] at h2
        exfalso
        nlinarith [mul_self_nonneg H.rt0.re]
    show starRingEnd ℂ β = H.rt0
    rw [hneg, map_neg]
    apply Complex.ext <;> simp [hre]

theorem IsNormOn.of_goodOf {C : Submodule c.F (Rul Xo c)} {σ : c.F →+* ℂ} {N : Rul Xo c → ℝ}
    (h : IsNormOn C (goodOf c σ) N) : IsNormOn C σ N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simpa only [norm_goodOf] using h1, by simpa only [norm_goodOf] using h2,
    by simpa only [norm_goodOf] using h3, by simpa only [norm_goodOf] using h4⟩

def lieFac (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFac_pos (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : 0 < lieFac Dw x a := Real.exp_pos _

def supC (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  lieFac Dw x a * supN (U σ).X (laU (U σ) a n) (rdU (U σ) f)

def SupDef : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) = 0 → f = 0

variable {Xo c U}

theorem supE_cusp_ne_top {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := Submodule.mem_iInf _ |>.mp h1 σ
  have h3 := Submodule.mem_iInf _ |>.mp h2 hσ
  exact supE_ne_top (U σ).X (laU (U σ) a n) (Submodule.mem_comap.mp h3)

theorem isNormOn_supC (x : ℝ) (h : SupDef Xo c U) {a n} (hd : Dom a n) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) :
    IsNormOn (cusp Xo c U a n) σ (supC Xo c U x σ a n) := by
  constructor
  · intro f _
    exact mul_nonneg (lieFac_pos _ _ _).le (supN_nonneg _ _ _)
  · intro f hf h0
    exact h a n hd σ hσ f hf ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne')
  · intro y f _
    unfold supC supN
    rw [map_smulₛₗ, supE_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    ring
  · intro f hf g hg
    unfold supC supN
    rw [← mul_add, map_add (f := _), ← ENNReal.toReal_add (supE_cusp_ne_top hσ hf) (supE_cusp_ne_top hσ hg)]
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ?_ (supE_add_le _ _ _ _)) (lieFac_pos _ _ _).le
    exact ENNReal.add_ne_top.mpr ⟨supE_cusp_ne_top hσ hf, supE_cusp_ne_top hσ hg⟩

variable (U)

-- Prefer the same-scalar submodule instance when elaborating the L² constructions.
attribute [local instance 2000] Submodule.module

def rdC (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n →ₛₗ[σ] FDSec (U σ).X :=
  (rdU (U σ)).comp (cusp Xo c U a n).subtype

variable {D : D7} (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)

def CuspL2 : Prop := ∀ a n, Dom a n → JMemL2 V σ (rdC U σ a n) dict mu


open Classical in
def l2C (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : JMemL2 V σ (rdC U σ a n) dict mu) (f : Rul Xo c) : ℝ :=
  if hf : f ∈ cusp Xo c U a n then
    lieFac Dw x a * l2NormAlt V σ (rdC U σ a n) dict mu h ⟨f, hf⟩ else 0

def L2DefiniteCuspForms (h : CuspL2 U σ V dict mu) : Prop :=
  ∀ a n (hd : Dom a n), L2Definite V σ (rdC U σ a n) dict mu (h a n hd)

variable {U σ V dict mu}

theorem isNormOn_l2C (x₀ : ℝ) {h : CuspL2 U σ V dict mu} (h1 : L2DefiniteCuspForms U σ V dict mu h) {a n} (hd : Dom a n) :
    IsNormOn (cusp Xo c U a n) σ (l2C U σ V dict mu x₀ a n (h a n hd)) := by
  constructor
  · intro f hf
    rw [l2C, dite_eq_left hf]; exact mul_nonneg (lieFac_pos _ _ _).le (l2Norm_nonneg_bis _ _ _ _ _ _ _)
  · intro f hf h0
    rw [l2C, dite_eq_left hf] at h0
    exact congrArg Subtype.val (h1 a n hd ⟨f, hf⟩ ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne'))
  · intro x f hf
    rw [l2C, l2C, dite_eq_left hf, dite_eq_left (Submodule.smul_mem _ x hf)]
    have := l2Norm_smul_alt V σ (rdC U σ a n) dict mu (h a n hd) x ⟨f, hf⟩
    exact (congrArg (lieFac Dw x₀ a * ·) this).trans (by ring)
  · intro f hf g hg
    rw [l2C, l2C, l2C, dite_eq_left hf, dite_eq_left hg, dite_eq_left (Submodule.add_mem _ hf hg), ← mul_add]
    exact mul_le_mul_of_nonneg_left (L2Norm_add_le V σ (rdC U σ a n) dict mu (h a n hd) ⟨f, hf⟩ ⟨g, hg⟩)
      (lieFac_pos _ _ _).le

theorem l2C_le_supC (x : ℝ) (hσ : GoodEmb c σ) {a n} (h : JMemL2 V σ (rdC U σ a n) dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom) (hm : MuUnit V dict mu) :
    ∀ f ∈ cusp Xo c U a n, l2C U σ V dict mu x a n h f ≤ supC Xo c U x σ a n f := by
  intro f hf
  unfold l2C supC
  rw [dite_eq_left hf]
  refine mul_le_mul_of_nonneg_left ?_ (lieFac_pos Dw x a).le
  exact L2Norm_le_sup_norm (V := V) (la := laU (U σ) a n) (rd := rdC U σ a n) (dict := dict) (mu := mu) (h := h)
    (hd := hd) (hm := hm) (f := ⟨f, hf⟩) (hfin := supE_cusp_ne_top hσ hf)

theorem rdC_continuousOn (hU : IsUnf (U σ)) {a n} (hd : Dom a n) (f : cusp Xo c U a n) (k : (U σ).Comp) :
    ContinuousOn (rdC U σ a n f k) ((U σ).X k).dom := by
  obtain ⟨-, -, -, -, hsec, -⟩ := hU
  have hf : (f : Rul Xo c) ∈ sec Xo c a n := (Submodule.mem_inf.mp f.2).1
  exact (hsec a n hd f hf k).1.continuousOn

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

lemma weight_add_shift {e k : ℕ} {w' : WeightFamilies.Wt D j} (hw : wadd wF w' = wsmul e wL) :
    wadd (addL wF wL k) w' = addL (wt0 D j) wL (k + e) := by
  have h1 := congrArg WeightFamilies.Wt.aP hw
  have h2 := congrArg WeightFamilies.Wt.aM hw
  have h3 := congrArg WeightFamilies.Wt.n hw
  simp only [wadd, wsmul] at h1 h2 h3
  unfold addL wadd wsmul wt0 wscalar
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i
    have := congrFun (congrFun h1 τ) i
    linarith
  · funext τ i
    have := congrFun (congrFun h2 τ) i
    linarith
  · linarith

variable (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (g0 : B.Cusp j wF)

lemma product_cusp_forms_mem_weight {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL) :
    emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ) ∈
      Vw (xplus X E hM) la G.N (addL (wt0 D j) wL e) := by
  have := mul_mem_Vw (xplus X E hM) la G.N (emb_mem_Vw (xplus X E hM) la G.N wF g0)
    (emb_mem_Vw (xplus X E hM) la G.N w' θ)
  have hw' : addL (wt0 D j) wL e = wadd wF w' := by rw [hw]; exact zero_weight_add _
  rw [hw']
  exact this

def u0 {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL) :
    ↥(Frac0 (xplus X E hM) la G.w) :=
  ⟨frac (xplus X E hM) la G.w e (emb (xplus X E hM) la G.N (X.inc wF g0) * emb (xplus X E hM) la G.N (X.inc w' θ)),
    Algebra.subset_adjoin (frac_mem_Hfr _ _ _ (product_cusp_forms_mem_weight G la g0 θ hw))⟩

lemma top_span_mem {z : ↥(Frac0 (xplus X E hM) la G.w)} (hz : z ∈ Jid (xplus X E hM) la G.w) :
    (⟨z, Algebra.mem_top⟩ : ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w))) ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        (⟨sfr (xplus X E hM) la G.w i.succ, Algebra.mem_top⟩ :
          ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w)))) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Ideal.subset_span ⟨i, rfl⟩
  | zero => exact Ideal.zero_mem _
  | add a b _ _ ha hb => exact Ideal.add_mem _ ha hb
  | smul a b _ hb =>
    have : (⟨a • b, Algebra.mem_top⟩ :
        ↥(⊤ : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w))) =
        ⟨a, Algebra.mem_top⟩ * ⟨b, Algebra.mem_top⟩ := rfl
    rw [this]
    exact Ideal.mul_mem_left _ _ hb

theorem curveModel_of_fr
    (hfd : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))
    (hred : IsReduced (OsK (xplus X E hM) la G.w))
    {e : ℕ} {w' : WeightFamilies.Wt D j} (θ : B.Cusp j w') (hw : wadd wF w' = wsmul e wL)
    (hu0 : IsUnit (toOsK (xplus X E hM) la G.w (u0 G la g0 θ hw)))
    (hinj : ∀ b : ↥(Frac0 (xplus X E hM) la G.w),
      (b : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0)) = 0 →
        b = 0) :
    Nonempty (CurveModel G la g0) := by
  obtain ⟨v, hv⟩ := hu0
  obtain ⟨c, hc⟩ := toOsK_surjective (xplus X E hM) la G.w (↑v⁻¹)
  set A : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w) := ⊤ with hA
  have hJh : c * u0 G la g0 θ hw - 1 ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_sub, map_mul, map_one, hc, ← hv, Units.inv_mul, sub_self]

  have hspan : Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, Algebra.mem_top⟩ : ↥A)) =
      (Jid (xplus X E hM) la G.w).map (Subalgebra.topEquiv (R := Kp (xplus X E hM) la G.N)).symm := by
    rw [Jid, Ideal.map_span, ← Set.range_comp]
    rfl
  let qe := Ideal.quotientEquivAlg (R₁ := Kp (xplus X E hM) la G.N) (Jid (xplus X E hM) la G.w) _
    (Subalgebra.topEquiv (R := Kp (xplus X E hM) la G.N) (A := ↥(Frac0 (xplus X E hM) la G.w))).symm hspan
  have hfd' : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥(Frac0 (xplus X E hM) la G.w) ⧸ Jid (xplus X E hM) la G.w) :=
    hfd
  have hred' : IsReduced (↥(Frac0 (xplus X E hM) la G.w) ⧸ Jid (xplus X E hM) la G.w) := hred
  refine ⟨{ A' := A
            sA := fun _ => Algebra.mem_top
            h := ⟨c * u0 G la g0 θ hw, Algebra.mem_top⟩
            h_one := ?_
            fin := ?_
            red := ?_
            loc := fun b => ⟨0, ⟨b, Algebra.mem_top⟩, by rw [pow_zero, one_mul]⟩
            base_form_injective := ?_
            base_form_local := ?_ }⟩
  · have := top_span_mem G la hJh
    convert this using 1
  · exact LinearEquiv.finiteDimensional qe.toLinearEquiv
  · exact isReduced_of_injective qe.symm.toRingEquiv.toRingHom qe.symm.injective
  · intro a₁ a₂ h12
    apply Subtype.ext
    have h0 : (((a₁ : ↥(Frac0 (xplus X E hM) la G.w)) - (a₂ : ↥(Frac0 (xplus X E hM) la G.w)) :
        ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
          (emb (xplus X E hM) la G.N (X.inc wF g0)) = 0 := by
      rw [Subalgebra.coe_sub, sub_mul, sub_eq_zero]
      exact h12
    exact sub_eq_zero.1 (hinj _ h0)
  · intro x
    obtain ⟨k, g, hg, hx⟩ := (mem_Hfr (xplus X E hM) la G.w).1 ((mem_HK (xplus X E hM) la G.w).1 x.2)
    have hgθ : g * emb (xplus X E hM) la G.N (X.inc w' θ) ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL (k + e)) := by
      rw [← weight_add_shift (k := k) hw]
      exact mul_mem_Vw _ _ _ hg (emb_mem_Vw _ _ _ w' θ)
    let b : ↥(Frac0 (xplus X E hM) la G.w) :=
      ⟨frac (xplus X E hM) la G.w (k + e) (g * emb (xplus X E hM) la G.N (X.inc w' θ)),
        Algebra.subset_adjoin (frac_mem_Hfr _ _ _ hgθ)⟩
    refine ⟨1, ⟨c * b, Algebra.mem_top⟩, ?_⟩
    show ((c * u0 G la g0 θ hw : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) ^ 1 *
        (x : Lw (xplus X E hM) la G.w) =
      ((c * b : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) *
        algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0))
    rw [pow_one, Subalgebra.coe_mul, Subalgebra.coe_mul, hx, ← frac_zero, mul_assoc, mul_assoc]
    congr 1
    show frac _ _ _ e _ * frac _ _ _ k g = frac _ _ _ (k + e) _ * frac _ _ _ 0 _
    rw [frac_mul, frac_mul, add_zero, add_comm e k]
    congr 1
    ring

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def LiftModelSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF) (T : ℕ),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    Nonempty (LiftModel G la y (fun ζ => (hw ζ).toSecPt) g0 T)

end Formalism.L2.Pj
end
end
