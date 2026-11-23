module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle036
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle002

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

def NoCommonZeroSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → 4 * DF w + 4 ≤ T.Q.l.M →
    (∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}) →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom,
      ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def LieFacAddSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (x : ℝ)
    (a a' : (E →+* ℂ) × ℕ → ℕ), lieFac Dw x (a + a') = lieFac Dw x a * lieFac Dw x a'

def PnormMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r)
    (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r), x ∈ X.dom →
      X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x

def SupCMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (σ : c.F →+* ℂ)
    (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), GoodEmb c σ → Even n → Even n' →
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ → supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) ≠ ⊤ →
      supC Xo c U x σ (a + a') (n + n') (f * g) ≤ supC Xo c U x σ a n f * supC Xo c U x σ a' n' g

def RecSubMulSt : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul (recPJ h j hj)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def NZDOfCompSt : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ →
    (∀ k, ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) (F.1 : T.R j) k x ≠ 0) →
    (recPJ h j hj).NonZeroComp w F

def NoBaseSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
    D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → DF w + 2 ≤ qq D →
    (∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}) →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k,
      ∃ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (f : T.R j),
        P ∈ harmA T.Q.c (wtA w) w.n ∧
        (∀ σ' : T.Q.c.F →+* ℂ, Real.log (∑ m ∈ P.support, ‖σ' (P.coeff m)‖) ≤ 140 * D.R.r * large₂.sc.L * absA w) ∧
        IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f ∧ ∃ x' ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) f k x' ≠ 0

def ThetaWeightBounds : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (j : ℕ) (hj : InR D j)
    (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    Formalism.MainNotions.Gaps.FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 →
    (∀ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 →
      D.R.r ≤ w2.n ∧ LastPos (T.Q.Dw j) (wtA w2) ∧ DF w2 + 2 ≤ qq D) ∧
    (j < D.R.m → ∀ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW →
      D.R.r ≤ w1.n ∧ LastPos (T.Q.Dw j) (wtA w1) ∧ DF w1 + 2 ≤ qq D)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def SupAtUnitSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w,
      0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) →
      ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
        (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧
        supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤
          2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧
        0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 44 * large₂.sc.L

def CuspTieSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    LastPos (T.Q.Dw j) (wtA w) →
    ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f → f ∈ T.C j w

structure XExt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) where
  k0 : ℝ
  minWeight_pos : 0 < k0
  k0_le : k0 ≤ 2
  ξ0_abs : ∀ τ : X.Ψ, ‖τ.1 X.ξ0‖ = k0 / 2
  EF_int : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ k : ℤ, EFf X.ξ0 X.Gm x y = k
  EF_perf : ∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y
  L' : Submodule (𝓞 E) (Fin r → E)
  L'_fg : L'.FG
  L'_int : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)
  L'_dual : ∀ x, (∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)) → x ∈ L'
  NA : ℕ
  NC : ℕ
  NA_pos : 0 < NA
  NC_pos : 0 < NC
  NA_sub : ∀ x ∈ X.Λ, (NA : E) • x ∈ L'
  NC_sub : ∀ x ∈ L', (NC : E) • x ∈ X.Λ
  g : ℕ
  g_pos : 0 < g
  cong : ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ →
    (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ

def XExt.toX {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} (e : XExt X) :
    DataX E r :=
  ⟨X, e.k0, e.minWeight_pos, e.k0_le, e.ξ0_abs, e.EF_int, e.EF_perf, e.L', e.L'_fg, e.L'_int, e.L'_dual, e.NA, e.NC,
    e.NA_pos, e.NC_pos, e.NA_sub, e.NC_sub, e.g, e.g_pos, e.cong⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


open Classical in
theorem rdU_apply_dom {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f : Rul Xo c) (k : U.Comp) (x : (U.X k).dom) : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := by
  show (if h : x.1 ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0) = _
  rw [dite_eq_left x.2]

theorem rel_of_frames {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hU3 : ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (U.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) y)
    (hT : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x))
    (hF : WtField Xo c) {m : ℕ} (fs : Fin m → Rul Xo c) (hfs : ∀ i, fs i ∈ sec Xo c a n) (g : Fin m → ℂ)
    (hrel : ∀ k (x : (U.X k).dom), ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) = 0)
    (z : FrPt Xo c (CAt σ)) (hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z) :
    ∑ i, g i * toC (evR Xo c (fs i) z) = 0 := by
  obtain ⟨k, x, t, hbor⟩ := hU3 z
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hv : ∀ i, evR Xo c (fs i) z = wchar (ex Dw a n) t * evR Xo c (fs i) (U.un k x) :=
    fun i => hF a n (fs i) (hfs i) (CAt σ) t _ z (hT k x) hz hbor
  calc ∑ i, g i * toC (evR Xo c (fs i) z)
      = ∑ i, g i * (toC (wchar (ex Dw a n) t) * toC (evR Xo c (fs i) (U.un k x))) :=
        Finset.sum_congr rfl fun i _ => by rw [hv i]; rfl
    _ = toC (wchar (ex Dw a n) t) * ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hrel k x, mul_zero]

end Frames

theorem jInjRd_of_wt {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hA : BCEx (T.Q.Xo j) T.Q.c T.σ₀) (hF : WtField (T.Q.Xo j) T.Q.c) :
    JInjRd T j a n := by
  intro m b hb
  have hU : IsUnf (T.U j T.σ₀) := hM.unf j hj T.σ₀ T.good_σ₀
  set_option synthInstance.maxHeartbeats 200000 in
  have hb' := hb.map' (cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype (Submodule.ker_subtype _)
  have hfs : ∀ i, (⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i ∈ sec (T.Q.Xo j) T.Q.c a n :=
    fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (b i).2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ k (x : ((T.U j T.σ₀).X k).dom),
      ∑ i, g i * toC (evR (T.Q.Xo j) T.Q.c ((⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i)
        ((T.U j T.σ₀).un k x)) = 0 := by
    intro k x
    have h := congrFun (congrFun hg k) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← rdU_apply_dom (T.U j T.σ₀) _ k x]; rfl
  have hall := rel_of_frames (T.U j T.σ₀) hU.2.2.1 (hM.unTest j hj T.σ₀ T.good_σ₀) hF _ hfs g hrel
  let _ : Algebra T.Q.c.F ℂ := T.σ₀.toAlgebra
  have hc := indep_of_complex (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S)
    (fun φ y z => FrMap φ y z) (hM.evalWD j hj) (fun p φ y => hA p y φ)
    _ (fun i => (hfs i).1) hb' g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
