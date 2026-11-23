module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Basic
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.RCLike.Extend

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tors_push {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : U ⟶ S') (b : U ⟶ S) (hb : a ≫ f = b) :
    ∃ π : (Over.mk a ⟶ G') →* (Over.mk b ⟶ G), Function.Bijective π ∧ ∀ x, (π x).left = x.left ≫ φ := by
  subst hb
  have hw : ∀ x : Over.mk a ⟶ G', (x.left ≫ φ) ≫ G.hom = a ≫ f := by
    intro x
    have hx : x.left ≫ G'.hom = a := Over.w x
    rw [Category.assoc, h.1.w, ← Category.assoc, hx]
  let F : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (hw x)
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun x => rfl
  have hmul : ∀ x y, F (x * y) = F x * F y := by
    intro x y
    apply Over.OverMorphism.ext
    rw [hF]
    exact (h.2 (Over.mk a) x y (F x) (F y) (hF x) (hF y)).symm
  refine ⟨MonoidHom.mk' F hmul, ⟨?_, ?_⟩, hF⟩
  · intro x y hxy
    apply Over.OverMorphism.ext
    have e1 : (F x).left = (F y).left := congrArg (fun g => Over.Hom.left g) hxy
    rw [hF, hF] at e1
    apply h.1.hom_ext e1
    rw [Over.w x, Over.w y]
  · intro g
    have hg : g.left ≫ G.hom = a ≫ f := Over.w g
    refine ⟨Over.homMk (h.1.lift g.left a hg) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    show (h.1.lift g.left a hg) ≫ φ = g.left
    exact h.1.lift_fst _ _ _

theorem tors_iff {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T) {X : Scheme.{0}}
    {x : Sp R ⟶ X} {G : Over X} [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} (N : ℕ)
    (h : IsGrpPullback G₀ G x ψ) (i₀ : Γ.G.left ⟶ G₀.left) (hi : i₀ ≫ G₀.hom = Γ.G.hom) :
    Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ ↔ Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  have cancel : ∀ {W : Scheme.{0}} (u v : W ⟶ G₀.left), u ≫ ψ = v ≫ ψ → u ≫ G₀.hom = v ≫ G₀.hom → u = v :=
    fun u v e1 e2 => h.1.hom_ext e1 e2
  have base : ∀ (Y : Over (Sp R)) (y : Y ⟶ Γ.G), (y.left ≫ i₀) ≫ G₀.hom = Y.hom := by
    intro Y y
    rw [Category.assoc, hi]
    exact Over.w y
  have pushY : ∀ (Y : Over (Sp R)), ∃ π : (Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀) →* (Over.mk (Y.hom ≫ x) ⟶ G),
      Function.Bijective π ∧ ∀ g, (π g).left = g.left ≫ ψ := by
    intro Y
    exact tors_push h (Y.hom ≫ 𝟙 _) (Y.hom ≫ x) (by simp)
  have w1 : ∀ (Y : Over (Sp R)) (g : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀), g.left ≫ G₀.hom = Y.hom := by
    intro Y g
    have := Over.w g
    simpa using this
  constructor
  · intro t
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h.1.w, ← Category.assoc, hi]
    · intro Y y z y₀ z₀ hy hz
      obtain ⟨π, -, hπ⟩ := pushY Y
      let y₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀ := Over.homMk (y.left ≫ i₀) (by simpa using base Y y)
      let z₁ : Over.mk (Y.hom ≫ 𝟙 _) ⟶ G₀ := Over.homMk (z.left ≫ i₀) (by simpa using base Y z)
      have ey : π y₁ = y₀ := by
        apply Over.OverMorphism.ext
        rw [hπ, hy]
        show (y.left ≫ i₀) ≫ ψ = _
        rw [Category.assoc]
      have ez : π z₁ = z₀ := by
        apply Over.OverMorphism.ext
        rw [hπ, hz]
        show (z.left ≫ i₀) ≫ ψ = _
        rw [Category.assoc]
      rw [← ey, ← ez, ← map_mul, hπ, t.mul Y y z y₁ z₁ rfl rfl, Category.assoc]
    · intro Y y z e
      apply t.inj Y y z
      apply cancel
      · simpa only [Category.assoc] using e
      · rw [base Y y, base Y z]
    · intro Y g
      obtain ⟨π, ⟨hinj, hsurj⟩, hπ⟩ := pushY Y
      obtain ⟨g₁, rfl⟩ := hsurj g
      rw [← map_pow, ← map_one π, hinj.eq_iff, t.kernel Y g₁, hπ]
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y, by rw [← hy, Category.assoc]⟩
      · rintro ⟨y, hy⟩
        refine ⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩
        rw [base Y y, w1 Y g₁]
  · intro t
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hi, Category.comp_id]
    · intro Y y z y₀ z₀ hy hz
      obtain ⟨π, -, hπ⟩ := pushY Y
      have m := t.mul Y y z (π y₀) (π z₀) (by rw [hπ, hy, Category.assoc]) (by rw [hπ, hz, Category.assoc])
      rw [← map_mul, hπ] at m
      apply cancel
      · rw [m, Category.assoc]
      · rw [w1 Y, base Y]
    · intro Y y z e
      apply t.inj Y y z
      simp only [← Category.assoc, e]
    · intro Y g₁
      obtain ⟨π, ⟨hinj, -⟩, hπ⟩ := pushY Y
      rw [← hinj.eq_iff, map_pow, map_one, t.kernel Y (π g₁), hπ]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨y, cancel _ _ (by rw [Category.assoc, hy]) ?_⟩
        rw [base Y y, w1 Y g₁]
      · rintro ⟨y, hy⟩
        exact ⟨y, by rw [← hy, Category.assoc]⟩

theorem isTorsionAlong_iff_of_isGrpPullback : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (N : ℕ), IsGrpPullback G₀ G x ψ → (∀ i : Γ.G.left ⟶ G.left, Γ.IsTorsionAlong G x N i → ∃ i₀ : Γ.G.left ⟶ G₀.left, i₀ ≫ ψ = i ∧ Γ.IsTorsionAlong G₀ (𝟙 _) N i₀) ∧ ∀ i₀ : Γ.G.left ⟶ G₀.left, Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ → Γ.IsTorsionAlong G x N (i₀ ≫ ψ) := by
  intro R _ _ T _ Γ X x G _ G₀ _ ψ N h
  refine ⟨?_, ?_⟩
  · intro i t
    have w : i ≫ G.hom = Γ.G.hom ≫ x := t.isOver
    refine ⟨h.1.lift i Γ.G.hom w, h.1.lift_fst _ _ _, ?_⟩
    have e := (tors_iff Γ N h (h.1.lift i Γ.G.hom w) (h.1.lift_snd _ _ _)).2
    rw [h.1.lift_fst] at e
    exact e t
  · intro i₀ t
    have hi : i₀ ≫ G₀.hom = Γ.G.hom := by
      have := t.isOver
      simpa using this
    exact (tors_iff Γ N h i₀ hi).1 t

end PositivityTheory.UnitarySelfGeneration
end

section

namespace PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts

open ReciprocityTheory.AnForm Filter Topology Set Metric Complex

theorem exists_re_of_levi_zero {e : ℕ} {d : (Fin e → ℂ) → ℝ} {c : Fin e → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ContDiffOn ℝ 2 d (ball c r)) (h0 : ∀ z ∈ ball c r, ∀ w, levi d z w = 0) :
    ∃ G : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ G (ball c r) ∧ ∀ z ∈ ball c r, d z = (G z).re := by
  have hUo : IsOpen (ball c r) := isOpen_ball
  let J : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) := Complex.I • ContinuousLinearMap.id ℝ (Fin e → ℂ)
  let P : ((Fin e → ℂ) →L[ℝ] ℝ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin e → ℂ) (Fin e → ℂ) ℝ).flip J
  have hP : ∀ (L : (Fin e → ℂ) →L[ℝ] ℝ) (w : Fin e → ℂ), P L w = L (Complex.I • w) := fun L w => rfl
  let ω : (Fin e → ℂ) → (Fin e → ℂ) →L[ℝ] ℝ := fun z => -P (fderiv ℝ d z)
  have hC : ∀ a ∈ ball c r, ContDiffAt ℝ 2 d a := fun a ha => hd.contDiffAt (hUo.mem_nhds ha)
  have hω : ∀ a ∈ ball c r, HasFDerivAt ω (-(P.comp (fderiv ℝ (fderiv ℝ d) a))) a := by
    intro a ha
    have h1 : HasFDerivAt (fderiv ℝ d) (fderiv ℝ (fderiv ℝ d) a) a :=
      (((hC a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    exact (P.hasFDerivAt.comp a h1).neg
  have hωd : DifferentiableOn ℝ ω (ball c r) := fun a ha =>
    (hω a ha).differentiableAt.differentiableWithinAt
  have hsymm : ∀ a ∈ ball c r, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x := by
    intro a ha x y
    rw [(hω a ha).fderiv]
    have hS : IsSymmSndFDerivAt ℝ d a := (hC a ha).isSymmSndFDerivAt (by simp)
    have hL : ∀ w, fderiv ℝ (fderiv ℝ d) a w w
        + fderiv ℝ (fderiv ℝ d) a (Complex.I • w) (Complex.I • w) = 0 := by
      intro w
      have h := h0 a ha w
      simp only [levi] at h
      linarith
    have hB : ∀ u v, fderiv ℝ (fderiv ℝ d) a u v
        + fderiv ℝ (fderiv ℝ d) a (Complex.I • u) (Complex.I • v) = 0 := by
      intro u v
      have h1 := hL (u + v)
      have h2 := hL u
      have h3 := hL v
      simp only [smul_add, map_add (f := _), ContinuousLinearMap.add_apply] at h1
      have e1 := hS u v
      have e2 := hS (Complex.I • u) (Complex.I • v)
      linarith
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, hP]
    have k1 := hB x (Complex.I • y)
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at k1
    have k2 := hS (Complex.I • x) y
    linarith
  obtain ⟨v, hv⟩ := (convex_ball c r).exists_forall_hasFDerivAt_of_fderiv_symmetric hUo hωd hsymm
  refine ⟨fun z => (d z : ℂ) + (v z : ℂ) * Complex.I, ?_, ?_⟩
  · have hO := ReciprocityTheory.AnForm.Osgood.osgood
    unfold ReciprocityTheory.AnForm.Osgood.OsgoodStatement at hO
    apply hO e _ _ hUo
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hdz : HasFDerivAt d (fderiv ℝ d z) z :=
      ((hC z hz).differentiableAt (by norm_num)).hasFDerivAt
    have hG : HasFDerivAt (fun z => (d z : ℂ) + (v z : ℂ) * Complex.I)
        (Complex.ofRealCLM.comp (fderiv ℝ d z) + Complex.I • Complex.ofRealCLM.comp (ω z)) z :=
      (Complex.ofRealCLM.hasFDerivAt.comp z hdz).add
        ((Complex.ofRealCLM.hasFDerivAt.comp z (hv z hz)).mul_const Complex.I)
    rw [differentiableAt_iff_restrictScalars ℝ hG.differentiableAt]
    refine ⟨StrongDual.extendRCLike (fderiv ℝ d z), ?_⟩
    rw [hG.fderiv]
    ext w
    simp [StrongDual.extendRCLike_apply, ω, hP]
    ring
  · intro z _
    simp

end PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts
end

section

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem xi_den (E : Type) [Field E] [NumberField E] : ∃ c : 𝓞 E, c ≠ 0 ∧ ∀ η : E,
    (∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (η * a) = z) → ∃ b : 𝓞 E, (b : E) = c * η := by
  obtain ⟨c, hc, h⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)).prop
  refine ⟨c, nonZeroDivisors.ne_zero hc, fun η hη => ?_⟩
  have hm : η ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨z, hz⟩ := hη b
    exact ⟨z, hz.symm⟩
  obtain ⟨b, hb⟩ := h η hm
  exact ⟨b, by rw [Algebra.smul_def] at hb; exact hb⟩

theorem xi_rep (E : Type) [Field E] [NumberField E] (lam : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ η : E, ∀ a : 𝓞 E, Algebra.trace ℚ E (η * a) = lam a := by
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ fun i => (lam (RingOfIntegers.basis E i) : ℚ)
  refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm f, fun a => ?_⟩
  rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  have h : (f.restrictScalars ℤ).comp (IsScalarTower.toAlgHom ℤ (𝓞 E) E).toLinearMap
      = (Algebra.linearMap ℤ ℚ).comp lam := by
    refine (RingOfIntegers.basis E).ext fun i => ?_
    show f (algebraMap (𝓞 E) E (RingOfIntegers.basis E i)) = _
    rw [← integralBasis_apply]
    exact (integralBasis E).constr_basis ℚ _ i
  exact LinearMap.congr_fun h a

theorem tw_g_xi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : ℕ, p.Prime → ∃ ξ : E, IsCMField.complexConj E ξ = -ξ ∧ (∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (ξ * a) = z) ∧ ∀ lam : 𝓞 E →ₗ[ℤ] ℤ, ∃ (m : ℤ) (b : 𝓞 E), ¬ (p : ℤ) ∣ m ∧ ∀ a : 𝓞 E, ((m * lam a : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * b * a) := by
  intro E _ _ _ bar hbar hun p hp
  obtain ⟨c0, hc0, hden⟩ := xi_den E
  have hbb := bar_bar bar hbar
  have htr : ∀ x : E, Algebra.trace ℚ E (IsCMField.complexConj E x) = Algebra.trace ℚ E x := fun x =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
  set c : 𝓞 E := c0 * bar c0 with hc
  have hc' : c ≠ 0 := mul_ne_zero hc0 (by simpa using hc0)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc'
  have hcb : IsCMField.complexConj E (c : E) = c := by
    rw [← hbar, hc, map_mul, hbb, mul_comm]
  let I : Ideal (𝓞 E) :=
    { carrier := {y | ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E ((y : E) / c * a) = z}
      add_mem' := fun {x y} hx hy a => by
        obtain ⟨z, hz⟩ := hx a
        obtain ⟨w, hw⟩ := hy a
        exact ⟨z + w, by push_cast; rw [add_div, add_mul, map_add (f := _), hz, hw]⟩
      zero_mem' := fun a => ⟨0, by simp⟩
      smul_mem' := fun r y hy a => by
        obtain ⟨z, hz⟩ := hy (r * a)
        refine ⟨z, ?_⟩
        rw [← hz]
        congr 1
        rw [smul_eq_mul]
        push_cast
        ring }
  have hmem : ∀ y : 𝓞 E, y ∈ I ↔ ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E ((y : E) / c * a) = z :=
    fun _ => Iff.rfl
  have hI0 : I ≠ ⊥ := by
    intro h
    have : c ∈ I := (hmem c).2 fun a => ⟨Algebra.trace ℤ (𝓞 E) a, by
      rw [div_self hcE, one_mul, Algebra.coe_trace_int]⟩
    rw [h] at this
    exact hc' this
  have hI : ∀ y ∈ I, bar y ∈ I := by
    intro y hy
    refine (hmem _).2 fun a => ?_
    obtain ⟨z, hz⟩ := (hmem y).1 hy (bar a)
    refine ⟨z, ?_⟩
    rw [← hz, ← htr ((y : E) / c * _), map_mul (IsCMField.complexConj E), map_div₀, hcb, ← hbar, ← hbar, hbb]
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨x, hxI, hx⟩ := anti_ded bar hbb I hI0 hI (tw_g_diff E bar hbar hun) (p : 𝓞 E) hp0
  have hxI' : x - bar x ∈ I := sub_mem hxI (hI x hxI)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {x - bar x} := Ideal.dvd_span_singleton.2 hxI'
  have hm : ∃ m : ℤ, ¬ (p : ℤ) ∣ m ∧ (m : 𝓞 E) ∈ J := by
    by_contra hne
    push Not at hne
    have : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
    obtain ⟨Q, hJQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E)
      (Ideal.span {(p : ℤ)}) J (by
        intro m hm
        rw [Ideal.mem_span_singleton]
        by_contra h
        exact hne m h (by simpa using hm))
    have hpQ : (p : 𝓞 E) ∈ Q := by
      have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
        change (p : ℤ) ∈ Ideal.under ℤ Q
        rw [hQp]
        exact Ideal.mem_span_singleton_self _
      simpa using this
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact hp0 hpQ
    refine hx Q (hQ.isMaximal hQ0) hpQ ?_
    have : x - bar x ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self _
    rw [mul_comm Q]
    exact Ideal.mul_mono_right hJQ this
  obtain ⟨m, hmp, hmJ⟩ := hm
  refine ⟨((x - bar x : 𝓞 E) : E) / c, ?_, (hmem _).1 hxI', fun lam => ?_⟩
  · rw [map_div₀, hcb, ← hbar, map_sub, hbb]
    push_cast
    ring
  · obtain ⟨η, hη⟩ := xi_rep E lam
    obtain ⟨b, hb⟩ := hden η fun a => ⟨lam a, hη a⟩
    have hy : ((bar c0 * b : 𝓞 E) : E) / c = η := by
      rw [div_eq_iff hcE, hc]
      have e1 : ((bar c0 * b : 𝓞 E) : E) = (bar c0 : 𝓞 E) * (b : E) := rfl
      have e2 : ((c0 * bar c0 : 𝓞 E) : E) = (c0 : E) * (bar c0 : 𝓞 E) := rfl
      rw [e1, e2, hb]
      ring
    have hyI : bar c0 * b ∈ I := (hmem _).2 fun a => ⟨lam a, by rw [hy, hη]⟩
    have h2 : bar c0 * b * m ∈ Ideal.span {x - bar x} := hJ ▸ Ideal.mul_mem_mul hyI hmJ
    obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton.1 h2
    refine ⟨m, β, hmp, fun a => ?_⟩
    have h3 : ((x - bar x : 𝓞 E) : E) / c * β * a = (m : ℚ) • (η * a) := by
      have h4 : ((bar c0 * b : 𝓞 E) : E) * m = ((x - bar x : 𝓞 E) : E) * β := by
        have := congrArg (algebraMap (𝓞 E) E) hβ
        rw [map_mul _ (bar c0 * b), map_intCast, map_mul _ _ β] at this
        exact this
      rw [← hy, Int.cast_smul_eq_zsmul, zsmul_eq_mul, div_mul_eq_mul_div, ← h4]
      ring
    rw [h3, map_smul, hη]
    simp

end PositivityTheory.UnitarySelfGeneration
end
