module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
theorem _root_.GlobalTheory.T.exists_commGrpObj_weierstrassScheme : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ (η[schemeOver W].left = zero W ∧ (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q) (hT : IsUnimodularSol (W.map ρ) T), (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧ Proportional T (diagXYZ (W.map ρ).toProjective P Q)) → ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP → y.left = ptHom W ρ Q hQ → (lift x y ≫ μ[schemeOver W]).left = ptHom W ρ T hT) ∧ (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P), ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P), ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN)) := by
  first | exact @GlobalTheory.exists_grpObj_weierstrass | exact GlobalTheory.exists_grpObj_weierstrass | (intros; apply GlobalTheory.exists_grpObj_weierstrass <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

theorem _root_.GlobalTheory.T.thetaPolynomial_lower_bound_of_thetaLine_degree : (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi)) → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.thetaLine_lower_bound_of_degree | exact GlobalTheory.thetaLine_lower_bound_of_degree | (intros; apply GlobalTheory.thetaLine_lower_bound_of_degree <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open PureTypeVector in
theorem hermForm_principal_dim_one :
  ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ) (L : PeriodPair) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), g = 1 → w ≠ 0 → (∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ) → Hm.IsHermitian → 0 < (hermForm Hm w w).re → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∀ z z' : ℂ, hermForm Hm (z • w) (z' • w) = z * starRingEnd ℂ z' / (|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) := by
  intro g Λ w L Hm Ef hg hw hΛ hH hpos hEf hbij z z'
  subst hg
  set H := hermForm Hm w w with hHdef
  have hHim : H.im = 0 := hermForm_self_im hH w
  have hHreal : H = (H.re : ℂ) := Complex.ext (by simp) (by simp [hHim])
  have hsm : ∀ u v : ℂ, hermForm Hm (u • w) (v • w) = u * starRingEnd ℂ v * H :=
    fun u v => hermForm_smul_smul Hm u v w w
  set D := (L.ω₁ * starRingEnd ℂ L.ω₂).im with hD
  have hw0 : w 0 ≠ 0 := by
    intro h
    apply hw
    funext i
    rw [Subsingleton.elim i 0]
    simpa using h
  have hcoord : ∀ x : Λ, ∃ m n : ℤ, (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w := by
    intro x
    have hx : (x : Fin 1 → ℂ) = (x.1 0 / w 0) • w := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [div_mul_cancel₀ _ hw0]
    have hmem : (x.1 0 / w 0) ∈ L.lattice := (hΛ _).2 (by rw [← hx]; exact x.2)
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 hmem
    exact ⟨m, n, by rw [hmn]; exact hx⟩
  have him : ∀ m n m' n' : ℤ,
      (((m : ℂ) * L.ω₁ + n * L.ω₂) * starRingEnd ℂ ((m' : ℂ) * L.ω₁ + n' * L.ω₂)).im
        = ((m * n' - n * m' : ℤ) : ℝ) * D := by
    intro m n m' n'
    simp only [hD, map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
    push_cast
    ring
  have hEfc : ∀ (x y : Λ) (m n m' n' : ℤ),
      (x : Fin 1 → ℂ) = ((m : ℂ) * L.ω₁ + n * L.ω₂) • w →
      (y : Fin 1 → ℂ) = ((m' : ℂ) * L.ω₁ + n' * L.ω₂) • w →
      (Ef x y : ℝ) = ((m * n' - n * m' : ℤ) : ℝ) * (H.re * D) := by
    intro x y m n m' n' hx hy
    rw [hEf, hx, hy, hsm, Complex.mul_im, hHim, him]
    ring
  have ha : L.ω₁ • w ∈ Λ := (hΛ _).1 L.ω₁_mem_lattice
  have hb : L.ω₂ • w ∈ Λ := (hΛ _).1 L.ω₂_mem_lattice
  let a : Λ := ⟨L.ω₁ • w, ha⟩
  let b : Λ := ⟨L.ω₂ • w, hb⟩
  have ea : (a : Fin 1 → ℂ) = (((1 : ℤ) : ℂ) * L.ω₁ + ((0 : ℤ) : ℂ) * L.ω₂) • w := by
    show L.ω₁ • w = _
    simp
  have eb : (b : Fin 1 → ℂ) = (((0 : ℤ) : ℂ) * L.ω₁ + ((1 : ℤ) : ℂ) * L.ω₂) • w := by
    show L.ω₂ • w = _
    simp
  set k := Ef a b with hkdef
  have hk : (k : ℝ) = H.re * D := by
    rw [hEfc a b 1 0 0 1 ea eb]
    norm_num
  have hdvd : ∀ x y : Λ, k ∣ Ef x y := by
    intro x y
    obtain ⟨m, n, hx⟩ := hcoord x
    obtain ⟨m', n', hy⟩ := hcoord y
    refine ⟨m * n' - n * m', ?_⟩
    have h := hEfc x y m n m' n' hx hy
    rw [← hk, mul_comm] at h
    exact_mod_cast h
  have hba : Ef b a = -k := by
    have h := hEfc b a 0 1 1 0 eb ea
    rw [← hk] at h
    have h' : ((Ef b a : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by
      rw [h]
      push_cast
      ring
    exact_mod_cast h'
  have hk0 : k ≠ 0 := by
    intro hk0
    have hEa : Ef a = Ef 0 := by
      apply LinearMap.ext
      intro y
      rw [map_zero, LinearMap.zero_apply]
      obtain ⟨c, hc⟩ := hdvd a y
      rw [hc, hk0, zero_mul]
    have ha0 : a = 0 := hbij.1 hEa
    have h0 : L.ω₁ • w = 0 := congrArg Subtype.val ha0
    rcases smul_eq_zero.1 h0 with h | h
    · exact L.indep.ne_zero 0 (by simpa using h)
    · exact hw h
  let f : Λ →ₗ[ℤ] ℤ :=
    { toFun := fun y => Ef y a / k
      map_add' := fun y y' => by
        simp only [map_add (f := _), LinearMap.add_apply]
        exact Int.add_ediv_of_dvd_left (hdvd y a)
      map_smul' := fun c y => by
        simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hdvd y a) }
  obtain ⟨x, hx⟩ := hbij.2 f
  have hxb : Ef x b = -1 := by
    rw [hx]
    show Ef b a / k = -1
    rw [hba, Int.neg_ediv_of_dvd (dvd_refl k), Int.ediv_self hk0]
  have hunit : k = 1 ∨ k = -1 := by
    have h := hdvd x b
    rw [hxb] at h
    exact Int.isUnit_iff.1 (isUnit_of_dvd_one (dvd_neg.1 h))
  have hHre : H.re * |D| = 1 := by
    have hpos' : 0 < H.re := hpos
    rcases hunit with h | h
    · have h1 : H.re * D = 1 := by rw [← hk, h]; norm_num
      have hD0 : 0 < D := by nlinarith
      rw [abs_of_pos hD0]
      exact h1
    · have h1 : H.re * D = -1 := by rw [← hk, h]; norm_num
      have hD0 : D < 0 := by nlinarith
      rw [abs_of_neg hD0]
      linarith
  have hDabs : |D| ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hHre
    exact zero_ne_one hHre
  have hr : H.re = 1 / |D| := by
    rw [eq_div_iff hDabs]
    exact hHre
  rw [hsm, hHreal, hr, Complex.ofReal_div, Complex.ofReal_one]
  ring

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.existsUnique_linearLift_of_holomorphic_abelianVariety : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g m : ℕ) (u : HolUnif A L g),
  (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
  ∀ G : (Fin m → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ z w, G (z + w) = G z * G w) →
  IsHolTo (Set.univ : Set (Fin m → ℂ)) (fun z => (G z).left) →
  ∃! F : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = G z := by
  first | exact @GlobalTheory.existsUnique_linear_lift_of_isHolTo | exact GlobalTheory.existsUnique_linear_lift_of_isHolTo | (intros; apply GlobalTheory.existsUnique_linear_lift_of_isHolTo <;> assumption)
end
