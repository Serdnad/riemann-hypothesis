module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle439
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WhitBump

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem continuous_psiInf : Continuous (psiInf (E := E)) := by
  have hs : Continuous (fun z : Cinf E => sInf E z) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact continuous_subtype_val.comp ((GroundTheory.Global.continuous_adelicChar (K := E)).comp hs)

theorem psiInf_zero : psiInf (0 : Cinf E) = 1 := by
  simp [psiInf, map_zero]

variable {E} {n : ℕ}

theorem continuous_sdM_of : Continuous fun x : Lie E n => sdM (Matrix.of x) := by
  unfold sdM
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_apply j).comp (continuous_apply i)

theorem sdM_one : sdM (1 : Matrix (Fin n) (Fin n) (Cinf E)) = 0 := by
  unfold sdM
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
  have hj' := (Finset.mem_filter.1 hj).2
  exact Matrix.one_apply_ne fun e => by subst e; omega

theorem continuous_toL_nu : Continuous fun t : Vp E n => toL (nu t) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun t : Vp E n => nu t i j
  by_cases hij : i < j
  · simp only [nu, Matrix.of_apply, dif_pos hij]
    exact continuous_apply _
  · simp only [nu, Matrix.of_apply, dif_neg hij]
    exact continuous_const

theorem nu_zero : nu (0 : Vp E n) = 1 := by
  ext i j
  by_cases hij : i < j
  · simp [nu, hij, Matrix.one_apply, hij.ne]
  · simp [nu, hij, Matrix.one_apply]

theorem exists_bumpInf_oneL_ne_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) :
    ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧
      bumpInf f (oneL E n) ≠ 0 := by
  classical
  set h : Lie E n → ℝ := fun x => (psiInf (-sdM (Matrix.of x))).re with hh
  have hc : Continuous h :=
    Complex.continuous_re.comp ((continuous_psiInf E).comp continuous_sdM_of.neg)
  have hof : Matrix.of (oneL E n) = 1 := Matrix.of.apply_symm_apply _
  have h1 : h (oneL E n) = 1 := by
    simp only [hh, hof, sdM_one, neg_zero, psiInf_zero, Complex.one_re]
  have hU : {x | 0 < h x} ∩ invSet E n ∈ nhds (oneL E n) :=
    Filter.inter_mem ((isOpen_lt continuous_const hc).mem_nhds (by simp [h1]))
      (isOpen_invSet.mem_nhds (by change IsUnit (Matrix.of (oneL E n)); rw [hof]; exact isUnit_one))
  obtain ⟨f, hfs, hfc, hfd, hfr, hf1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  refine ⟨f, hfd, hfc, hfs.trans Set.inter_subset_right, ?_⟩
  set φ : Vp E n → Lie E n := fun t => toL (nu t) with hφ
  have hφc : Continuous φ := continuous_toL_nu
  set ψ : Lie E n → Vp E n := fun x p => x p.1.1 p.1.2 with hψ
  have hψc : Continuous ψ := continuous_pi fun p => (continuous_apply p.1.2).comp (continuous_apply p.1.1)
  have hψφ : ∀ t, ψ (φ t) = t := fun t => by
    funext p
    change nu t p.1.1 p.1.2 = t p
    simp [nu, p.2]
  have hfφ : HasCompactSupport (fun t => f (φ t)) := by
    refine HasCompactSupport.intro ((hfc.isCompact).image hψc) fun t ht => ?_
    by_contra hne
    exact ht ⟨φ t, subset_tsupport _ hne, hψφ t⟩
  have hsd : ∀ t, sdM (nu t) = sdM (Matrix.of (φ t)) := fun t => by
    rw [hφ]; simp only [toL, Equiv.apply_symm_apply]
  have hb : bumpInf f (oneL E n) = ∫ t : Vp E n, (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t))) := by
    rw [bumpInf, hof]
    simp only [Matrix.mul_one, hsd]
    rfl
  set G : Vp E n → ℂ := fun t => (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t))) with hG
  have hGc : Continuous G :=
    (Complex.continuous_ofReal.comp (hfd.continuous.comp hφc)).mul
      ((continuous_psiInf E).comp (continuous_sdM_of.neg.comp hφc))
  have hGs : HasCompactSupport G := (hfφ.comp_left Complex.ofReal_zero).mul_right
  have hint : Integrable G := hGc.integrable_of_hasCompactSupport hGs
  have hre : (∫ t, G t).re = ∫ t, f (φ t) * h (φ t) := by
    have := (Complex.reCLM.integral_comp_comm hint).symm
    simp only [Complex.reCLM_apply] at this
    rw [this]
    congr 1
    funext t
    simp [hG, hh, Complex.re_ofReal_mul]
  haveI : (volume : Measure (InfinitePlace E → ℂ)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  haveI : (volume : Measure (Vp E n)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  have hpos : 0 < ∫ t, f (φ t) * h (φ t) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Vp E n))
      ((hfd.continuous.comp hφc).mul (hc.comp hφc)) hfφ.mul_right (fun t => ?_) ?_
    · have h0 : 0 ≤ f (φ t) := (hfr ⟨φ t, rfl⟩).1
      by_cases hz : f (φ t) = 0
      · simp [hz]
      · exact mul_nonneg h0 (hfs (subset_tsupport _ hz)).1.le
    · have : φ 0 = oneL E n := by rw [hφ]; simp only [nu_zero]
      simp [this, hf1, h1]
  intro h0
  rw [hb] at h0
  rw [h0, Complex.zero_re] at hre
  linarith

end GlobalTheory.WhitBump
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.EqCovol.FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cc_cc' (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

lemma herm_sub_left' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (u v y : Fin r → E) :
    herm G (u - v) y = herm G u y - herm G v y := by
  simp [herm, sub_mul, Finset.sum_sub_distrib]

lemma herm_sub_right' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x u v : Fin r → E) :
    herm G x (u - v) = herm G x u - herm G x v := by
  simp [herm, cc, mul_sub, Finset.sum_sub_distrib]

lemma herm_smul_left'' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (u y : Fin r → E) :
    herm G (c • u) y = c * herm G u y := by
  simp [herm, Finset.mul_sum, mul_assoc]

lemma herm_smul_right'' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x v : Fin r → E) :
    herm G x (c • v) = cc c * herm G x v := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, cc, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma oe_smul {r : ℕ} (c : 𝓞 E) (y : Fin r → E) : c • y = (c : E) • y := by
  ext i; rfl

end GlobalTheory.EqCovol.FullLevel


open GlobalTheory.EqCovol.FullLevel in
theorem GlobalTheory.EqCovol.mem_iff_congr_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (l : Level H) (r : ℕ) (Y : Data E r), GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsSelfDualTr Y →
    ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧ ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ,
      (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M' • y := by
  intro E _ _ _ H l r Y hL hS γ
  have hM0 : (l.M : E) ≠ 0 := by
    have : l.M ≠ 0 := by have := l.three_le; omega
    exact_mod_cast this
  have hA0 : (l.A : E) ≠ 0 := by exact_mod_cast l.A_pos.ne'
  constructor
  · intro hγ
    obtain ⟨hU, hM, hA⟩ := (hL γ).1 hγ
    obtain ⟨-, hMinv, -⟩ := (hL γ⁻¹).1 (Y.Γ.inv_mem hγ)
    set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
    set gi : Matrix (Fin r) (Fin r) E := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hgi
    have hggi : ∀ v, g.mulVec (gi.mulVec v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, hg, hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hunit : ∀ u v, herm Y.Gm (g.mulVec u) v = herm Y.Gm u (gi.mulVec v) := by
      intro u v
      have := hU.1 u (gi.mulVec v)
      rwa [hggi] at this
    have hcop : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.coprime]; exact Submodule.mem_top
    obtain ⟨b', hb', b, hb, hsum⟩ := Submodule.mem_sup.1 hcop
    have hsumE : (b' : E) + (b : E) = 1 := by exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hsum

    have key : ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, g.mulVec x - x = l.M • y := by
      intro x hx
      obtain ⟨y1, hy1, e1⟩ := hM (b • x) (Submodule.smul_mem_smul hb hx)
      set z : Fin r → E := (l.M : E)⁻¹ • ((b' : E) • (g.mulVec x - x)) with hz
      have hzmem : z ∈ Y.Λ := by
        refine (hS z).2 fun y hy => ?_
        have hc : H.bar b' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hb'
        obtain ⟨w, hw, ew⟩ := hMinv (H.bar b' • y) (Submodule.smul_mem_smul hc hy)
        have hbarE : ((H.bar b' : 𝓞 E) : E) = cc (b' : E) := H.bar_eq b'
        rw [oe_smul, hbarE, ← Nat.cast_smul_eq_nsmul E] at ew
        have h1 : herm Y.Gm z y = herm Y.Gm x w := by
          have h2 := congrArg (herm Y.Gm x) ew
          rw [herm_sub_right', ← hunit, herm_smul_right'', herm_smul_right'', herm_smul_right'',
            cc_cc', cc, map_natCast] at h2
          rw [hz, herm_smul_left'', herm_smul_left'', herm_sub_left']
          field_simp
          linear_combination h2
        obtain ⟨n, hn⟩ := (hS x).1 hx w hw
        exact ⟨n, by rw [h1, hn]⟩
      refine ⟨z + y1, Y.Λ.add_mem hzmem hy1, ?_⟩
      rw [oe_smul, Matrix.mulVec_smul] at e1
      rw [smul_add, ← e1, ← Nat.cast_smul_eq_nsmul E, hz, smul_smul,
        mul_inv_cancel₀ hM0, one_smul, ← smul_sub, ← add_smul, hsumE, one_smul]
    refine ⟨hU, fun x hx => ?_⟩
    obtain ⟨y, hy, ey⟩ := key x hx
    obtain ⟨y', hy', ey'⟩ := hA x hx
    refine ⟨Nat.gcdA l.M l.A • y' + Nat.gcdB l.M l.A • y,
      Y.Λ.add_mem (Y.Λ.toAddSubgroup.zsmul_mem hy' _) (Y.Λ.toAddSubgroup.zsmul_mem hy _), ?_⟩
    set t := g.mulVec x - x with ht
    rw [← Nat.cast_smul_eq_nsmul E] at ey ey'
    have hy1 : y = (l.M : E)⁻¹ • t := by rw [ey, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    have hy2 : y' = (l.A : E)⁻¹ • t := by rw [ey', smul_smul, inv_mul_cancel₀ hA0, one_smul]
    have hG : ((Nat.gcd l.M l.A : ℕ) : E) = (l.M : E) * (Nat.gcdA l.M l.A : E) + (l.A : E) * (Nat.gcdB l.M l.A : E) := by
      have := congrArg (Int.cast : ℤ → E) (Nat.gcd_eq_gcd_ab l.M l.A)
      push_cast at this
      exact this
    have hGL : ((Nat.gcd l.M l.A : ℕ) : E) * (l.M' : E) = (l.M : E) * (l.A : E) := by
      unfold Level.M'
      exact_mod_cast Nat.gcd_mul_lcm l.M l.A
    rw [← Nat.cast_smul_eq_nsmul E, ← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, hy1, hy2,
      smul_smul, smul_smul, ← add_smul, smul_smul]
    conv_lhs => rw [← one_smul E t]
    congr 1
    field_simp
    linear_combination hGL.symm + (l.M' : E) * hG
  · rintro ⟨hU, h⟩
    refine (hL γ).2 ⟨hU, fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := h x (Submodule.smul_le_right hx)
      obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      exact ⟨k • y, Y.Λ.toAddSubmonoid.nsmul_mem hy k, by rw [e, hk, mul_smul]⟩
    · obtain ⟨y, hy, e⟩ := h x hx
      obtain ⟨k, hk⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
      exact ⟨k • y, Y.Λ.toAddSubmonoid.nsmul_mem hy k, by rw [e, hk, mul_smul]⟩
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E _

theorem exists_twist (l : Level H) (L : ℤ) (hL : (l.A : ℤ) ∣ L - 1) :
    ∃ u w c : 𝓞 E, c ∈ l.Mb ∧ u = 1 + (l.A : 𝓞 E) * c ∧
      H.bar u * u = (L : 𝓞 E) + (l.M' : 𝓞 E) * w := by
  obtain ⟨q, hq⟩ := hL
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.1 h1
  have hbn : H.bar n ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hn
  have hbm : H.bar m ∈ l.Mb := by
    obtain ⟨m0, hm0, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hm
    simpa [bar_bar] using hm0
  have hbar1 : H.bar n + H.bar m = 1 := by rw [← map_add (f := _), hnm, map_one]
  have hxN : H.bar n - m ∈ l.Mb := by
    have e : H.bar n - m = n - H.bar m := by linear_combination hbar1 - hnm
    rw [e]; exact sub_mem hn hbm
  have hxN' : H.bar n - m ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := sub_mem hbn hm
  have hx : H.bar n - m ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have e : H.bar n - m = n * (H.bar n - m) + (H.bar n - m) * m := by
      linear_combination -(H.bar n - m) * hnm
    rw [e]
    exact add_mem (Ideal.mul_mem_mul hn hxN') (Ideal.mul_mem_mul hxN hm)
  have hnn : n * H.bar n ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_mem_mul hn hbn
  rw [l.prod] at hx hnn
  obtain ⟨y1, hy1⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨y2, hy2⟩ := Ideal.mem_span_singleton'.1 hnn
  have hg : ((l.M : ℕ) : 𝓞 E) * l.A = (l.M' : 𝓞 E) * (Nat.gcd l.M l.A : ℕ) := by
    have := Nat.gcd_mul_lcm l.M l.A
    unfold Level.M'
    exact_mod_cast (by rw [mul_comm (Nat.lcm _ _), this] : l.M * l.A = Nat.lcm l.M l.A * Nat.gcd l.M l.A)
  have hq' : (L : 𝓞 E) - 1 = (l.A : 𝓞 E) * q := by exact_mod_cast hq
  refine ⟨1 + ((L : 𝓞 E) - 1) * n, (Nat.gcd l.M l.A : 𝓞 E) * q * (y1 + ((L : 𝓞 E) - 1) * y2),
    (q : 𝓞 E) * n, Ideal.mul_mem_left _ _ hn, ?_, ?_⟩
  · rw [hq']; ring
  · have hb : H.bar (1 + ((L : 𝓞 E) - 1) * n) = 1 + ((L : 𝓞 E) - 1) * H.bar n := by
      simp [map_add (f := _), map_mul, map_sub, map_one, map_intCast]
    rw [hb]
    linear_combination ((L : 𝓞 E) - 1) * hnm - ((L : 𝓞 E) - 1) * hy1 - ((L : 𝓞 E) - 1) ^ 2 * hy2
      + (l.M : 𝓞 E) * (y1 + ((L : 𝓞 E) - 1) * y2) * hq' + (q : 𝓞 E) * (y1 + ((L : 𝓞 E) - 1) * y2) * hg

theorem smul_mem_M (l : Level H) {D : Datum H} {c : 𝓞 E} (hc : c ∈ l.Mb) {a : D.La}
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ y : D.La, c • a = l.M • y := by
  refine Submodule.smul_induction_on ha ?_ ?_
  · intro r hr t _
    have : c * r ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := l.prod ▸ Ideal.mul_mem_mul hc hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨s • t, by rw [← mul_smul, ← hs, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]⟩
  · rintro x y ⟨x', hx'⟩ ⟨y', hy'⟩
    exact ⟨x' + y', by rw [smul_add, hx', hy', smul_add]⟩

theorem exists_sympLevel_of_tate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)
    {z : kˣ}, IsPrimitiveRoot z l.M' → z ^ (l.M' / l.A) = I.ζ l.A →
    ∃ ev : D.La → Q, IsSympLevel D act e l.M' z ev ∧ Induces l (I.ev l.A) (I.ev l.M) ev := by
  intro E _ _ _ H D l k _ Q _ act e I z hz hzA
  have hM' := M'_pos l
  haveI : NeZero l.M' := ⟨hM'.ne'⟩
  have hζ := I.ζ_prim l.M' hM'
  obtain ⟨L, -, hcop, hL⟩ := (hζ.isPrimitiveRoot_iff').1 hz
  obtain ⟨d, hd⟩ := A_dvd_M' l
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
  have hdiv : l.M' / l.A = d := by rw [hd, Nat.mul_div_cancel_left _ l.A_pos]
  have hζA : I.ζ l.M' ^ d = I.ζ l.A := by
    have := I.ζ_pow l.A d l.A_pos hd0; rwa [← hd] at this
  have hAL : (l.A : ℤ) ∣ (L : ℤ) - 1 := by
    have e1 : I.ζ l.M' ^ (L * d) = I.ζ l.M' ^ d := by
      rw [pow_mul, hL, ← hdiv, hzA, hdiv, hζA]
    have h2 : I.ζ l.M' ^ (((L : ℤ) - 1) * d) = 1 := by
      rw [sub_mul, one_mul, zpow_sub, show ((L : ℤ) * d) = ((L * d : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, zpow_natCast, e1, mul_inv_cancel]
    have h3 := (hζ.zpow_eq_one_iff_dvd _).1 h2
    rw [hd] at h3; push_cast at h3
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hd0.ne')).1 h3
  obtain ⟨a', b', hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨u, w, c, hc, hu, hw⟩ := exists_twist l L hAL
  set v : 𝓞 E := (a' : 𝓞 E) * H.bar u with hv
  have hvu : v * u = 1 + (l.M' : 𝓞 E) * ((a' : 𝓞 E) * w - b') := by
    have hab' : (a' : 𝓞 E) * (L : ℤ) + (b' : 𝓞 E) * ((l.M' : ℕ) : ℤ) = 1 := by exact_mod_cast hab
    push_cast at hab'
    rw [hv, mul_assoc, hw]
    push_cast
    linear_combination hab'
  have key : ∀ a : D.La, v • u • a = a + l.M' • (((a' : 𝓞 E) * w - b') • a) := by
    intro a; rw [← mul_smul, hvu, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul]
  have key' : ∀ a : D.La, u • v • a = a + l.M' • (((a' : 𝓞 E) * w - b') • a) := by
    intro a; rw [smul_comm]; exact key a
  have hcong : ∀ a b : D.La, I.ev l.M' (a + l.M' • b) = I.ev l.M' a := by
    intro a b; rw [I.add, (I.ker _ hM' _).2 ⟨b, rfl⟩, mul_one]
  have hEF : ∀ a b : D.La, D.EF (u • a) (u • b) = L * D.EF a b + l.M' * D.EF a (w • b) := by
    intro a b
    rw [D.adj, ← mul_smul, hw, add_smul, mul_smul, Nat.cast_smul_eq_nsmul]
    simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul, map_add (f := _), map_zsmul, map_nsmul, smul_eq_mul, nsmul_eq_mul]
  refine ⟨fun a => I.ev l.M' (u • a), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a b; simp only [smul_add, I.add]
  · intro c a; try simp only
    rw [smul_comm, I.lin]
  · intro a; try simp only
    rw [I.ker _ hM']
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨v • b - ((a' : 𝓞 E) * w - b') • a, ?_⟩
      have h := congrArg (v • ·) hb
      change v • u • a = v • (l.M' • b) at h
      rw [key, smul_comm v l.M' b] at h
      rw [smul_sub, ← h]; abel
    · rintro ⟨b, rfl⟩; exact ⟨u • b, smul_comm _ _ _⟩
  · intro x; rw [I.onto _ hM']
    constructor
    · rintro ⟨a0, rfl⟩; exact ⟨v • a0, by simp only [key', hcong]⟩
    · rintro ⟨a, rfl⟩; exact ⟨u • a, rfl⟩
  · intro a b
    have h := I.isom _ hM' (u • a) (u • b)
    convert h using 1
    rw [hEF, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hL, hζ.pow_eq_one, one_zpow, mul_one]
  · intro a
    have htow : I.ev l.M' (u • a) ^ d = I.ev l.A (u • a) := by
      have := I.tower l.A d l.A_pos hd0 (u • a); rwa [← hd] at this
    try simp only
    rw [hdiv, htow, hu, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul, I.add,
      (I.ker _ l.A_pos _).2 ⟨_, rfl⟩, mul_one]
  · intro a ha
    obtain ⟨dM, hdM⟩ := M_dvd_M' l
    have hMp : 0 < l.M := by have := l.three_le; omega
    have hdM0 : 0 < dM := Nat.pos_of_ne_zero (by rintro rfl; simp at hdM; omega)
    have hdivM : l.M' / l.M = dM := by rw [hdM, Nat.mul_div_cancel_left _ hMp]
    have htow : I.ev l.M' (u • a) ^ dM = I.ev l.M (u • a) := by
      have := I.tower l.M dM hMp hdM0 (u • a); rwa [← hdM] at this
    obtain ⟨y, hy⟩ := smul_mem_M l hc ha
    try simp only
    rw [hdivM, htow, hu, add_smul, one_smul, mul_smul, hy, Nat.cast_smul_eq_nsmul, smul_comm, I.add,
      (I.ker _ hMp _).2 ⟨_, rfl⟩, mul_one]

end GlobalTheory.FullLevel
end
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.vacuum_coef_sq : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → GlobalTheory.IsSiegel (-(Q * P⁻¹)) → ∀ c : ℂ, c ^ 2 * P.det = 1 → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (GlobalTheory.Published.Metaplectic.holPart s).det = (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 := by
  intro l _ _ s P Q hP hQ hdet hS c hc
  set K := (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  set J := (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  have h1 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (-(Q * P⁻¹)) c hS
  have hSI : GlobalTheory.IsSiegel ((I • (1 : Matrix l l ℂ))) := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.IsSymm]
    · have : ((I • (1 : Matrix l l ℂ)).map Complex.im) = 1 := by
        ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
      rw [this]; exact Matrix.PosDef.one
  have h2 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (I • (1 : Matrix l l ℂ)) 1 hSI
  have hJ : (∫ x : l → ℝ, (1:ℂ) * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (I • (1 : Matrix l l ℂ)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) = J := by
    congr 1; ext x
    congr 2
    rw [one_mul]; congr 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [dotProduct, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [← mul_assoc, mul_assoc _ I I, I_mul_I]; ring
  rw [hJ] at h2
  have hdet2 : (1 - I • (I • (1 : Matrix l l ℂ))).det = 2 ^ Fintype.card l := by
    have : (1 - I • (I • (1 : Matrix l l ℂ))) = (2:ℂ) • (1 : Matrix l l ℂ) := by
      rw [smul_smul, I_mul_I]; ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]; norm_num
    rw [this, det_smul, det_one, mul_one]
  rw [hdet2, one_pow] at h2
  have hprod : (1 - I • (-(Q * P⁻¹))) * P = (2:ℂ) • GlobalTheory.Published.Metaplectic.holPart s := by
    have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
    rw [sub_mul, one_mul, smul_mul_assoc, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, hP, hQ, GlobalTheory.Published.Metaplectic.holPart]
    push_cast
    ring_nf; rw [I_sq]; ring
  have h3 : K ^ 2 * ((2:ℂ) ^ Fintype.card l * (GlobalTheory.Published.Metaplectic.holPart s).det) = 1 := by
    rw [← det_smul, ← hprod, det_mul, ← mul_assoc, h1, hc]
  have h2ne : (2:ℂ) ^ Fintype.card l ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h2ne
  linear_combination h3 - h2
end
