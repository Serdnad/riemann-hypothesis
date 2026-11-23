module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle139
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle144
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle142
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MaximalTorusInFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle002
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc

private theorem coeff_mul_eq_zero_of_order_two_of_degree_le_two {σ k : Type} [CommRing k] (j : ℕ) (q a : MvPolynomial σ k)
    (ha : ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff a e = 0) :
    ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff (q * a) e = 0 := by
  classical
  intro e he
  rw [MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h2 : x.2.degree ≤ e.degree := by
    rw [← hx, map_add (f := _)]; exact Nat.le_add_left _ _
  rw [ha x.2 (lt_of_le_of_lt h2 he), mul_zero]

private theorem coeff_eq_zero_of_mem_span_X_pow_of_degree_lt {σ k : Type} [CommRing k] :
    ∀ (j : ℕ) (P : MvPolynomial σ k), P ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ j →
      ∀ e : σ →₀ ℕ, e.degree < j → AddMonoidAlgebra.coeff P e = 0 := by
  classical
  intro j
  induction j with
  | zero => intro P _ e he; exact absurd he (Nat.not_lt_zero _)
  | succ j ih =>
    let K : Ideal (MvPolynomial σ k) :=
      { carrier := {P | ∀ e : σ →₀ ℕ, e.degree < j + 1 → AddMonoidAlgebra.coeff P e = 0}
        add_mem' := fun {a b} ha hb e he => by rw [MvPolynomial.coeff_add, ha e he, hb e he, add_zero]
        zero_mem' := fun e _ => by simp
        smul_mem' := fun c a ha => coeff_mul_eq_zero_of_order_two_of_degree_le_two (j + 1) c a ha }
    have hle : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ (j + 1) ≤ K := by
      rw [pow_succ, Ideal.mul_le]
      intro r hr s hs
      refine Submodule.span_induction (p := fun s _ => r * s ∈ K) ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨i, rfl⟩
        show ∀ e : σ →₀ ℕ, e.degree < j + 1 → AddMonoidAlgebra.coeff (r * MvPolynomial.X i) e = 0
        intro e he
        rw [MvPolynomial.coeff_mul]
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [MvPolynomial.coeff_X']
        split_ifs with hxi
        · have hx1 : x.1.degree + 1 = e.degree := by
            rw [← hx, map_add (f := _), ← hxi, Finsupp.degree_single]
          rw [ih r hr x.1 (by omega), zero_mul]
        · rw [mul_zero]
      · rw [mul_zero]; exact K.zero_mem
      · intro a b _ _ ha hb; rw [mul_add]; exact K.add_mem ha hb
      · intro c a _ ha; rw [smul_eq_mul, mul_left_comm]; exact K.mul_mem_left c ha
    exact fun P hP => hle hP

theorem pderiv_eq_zero_of_jet_pow_sub : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d : ℕ) (F f : MvPowerSeries (Fin 1 × Fin d) k), (∀ q, MvPowerSeries.pderiv (R := k) q f = 0) → (∀ m, ∃ v : Jet k (Fin 1 × Fin d) m, psJet m F = v ^ p - psJet m f) → ∀ q, MvPowerSeries.pderiv (R := k) q F = 0 := by
  intro k _ p _ _ d F f hf hF q
  classical
  ext e
  obtain ⟨v, hv⟩ := hF (e.degree + 1)
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hmem : psTrunc (e.degree + 1) F + psTrunc (e.degree + 1) f - P ^ p ∈
      orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), map_pow]
    have h1 : psJet (e.degree + 1) F =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) F) := rfl
    have h2 : psJet (e.degree + 1) f =
        Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (e.degree + 1 + 1)) (psTrunc (e.degree + 1) f) := rfl
    rw [← h1, ← h2, hv]; ring
  have hdeg : (e + Finsupp.single q 1).degree < e.degree + 1 + 1 := by
    rw [map_add (f := _), Finsupp.degree_single]; omega
  have hz := coeff_eq_zero_of_mem_span_X_pow_of_degree_lt (e.degree + 1 + 1) _ hmem (e + Finsupp.single q 1) hdeg
  have hbd : ∀ i, (e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i ≤ (e + Finsupp.single q 1).degree := by
    intro i
    exact Finsupp.le_degree i _
  have hin : e + Finsupp.single q 1 ∈ degLE (e.degree + 1) := by
    simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · refine ⟨fun i => ⟨(e + Finsupp.single q 1 : Fin 1 × Fin d →₀ ℕ) i, ?_⟩, ?_⟩
      · have := hbd i
        rw [map_add (f := _), Finsupp.degree_single] at this
        omega
      · ext i; simp
    · show (e + Finsupp.single q 1).degree ≤ e.degree + 1
      rw [map_add (f := _), Finsupp.degree_single]
  have htr : ∀ g : MvPowerSeries (Fin 1 × Fin d) k,
      AddMonoidAlgebra.coeff (psTrunc (e.degree + 1) g) (e + Finsupp.single q 1) =
        MvPowerSeries.coeff (e + Finsupp.single q 1) g := by
    intro g
    simp [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hin]
  have hpow : MvPowerSeries.pderiv (R := k) q ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k) = 0 := by
    rw [MvPolynomial.coe_pow, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have hG : MvPowerSeries.pderiv (R := k) q F = MvPowerSeries.pderiv (R := k) q
      (F + f - ((P ^ p : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries (Fin 1 × Fin d) k)) := by
    rw [map_sub, map_add (f := _), hf q, hpow, add_zero, sub_zero]
  rw [hG, MvPowerSeries.coeff_pderiv, map_zero, map_sub, map_add (f := _), MvPolynomial.coeff_coe, ← htr F, ← htr f,
    ← MvPolynomial.coeff_add, ← MvPolynomial.coeff_sub, hz, zero_mul]

end GlobalTheory.CompanionTheory.Ar.Coc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem gs_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (y : Y) (hy : y ∈ V)
    (a : Γ(X, U)) : gs (𝟙 Y) y V ((f.appLE U V e).hom a) = gs f y U a := by
  have hf : f y ∈ U := e hy
  have key := Y.presheaf.germ_res_apply (homOfLE e) y hy ((f.app U).hom a)
  unfold gs
  rw [dite_eq_left hf]
  split_ifs with h1
  · exact key
  · exact absurd hy h1

theorem gm_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (z : Sp B) :
    gm (spMap f) z ⊤ (unitΓ u) = gm (𝟙 _) z ⊤ (unitΓ (Units.map (f : A →* B) u)) := by
  have key := congrArg (fun g => (CommRingCat.Hom.hom g) (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  unfold gm
  rw [dite_eq_left (show (spMap f) z ∈ (⊤ : (Sp A).Opens) from trivial)]
  rw [dite_eq_left (show (𝟙 (Sp B)) z ∈ (⊤ : (Sp B).Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, pullU, unitΓ, toΓ, MonoidHom.coe_coe, Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]
  erw [key]
  rfl

theorem val_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u c) r z J = gm r z ⊤ u * val c r z J := by
  have hz : r z ∈ t.PP.L.wchart φ (fun k => J (r ≫ φ k)) := by
    show r z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k)))
    refine Set.mem_iInter.2 fun k => ?_
    have := hJ (r ≫ φ k)
    simpa [Scheme.Hom.comp_apply] using this
  unfold val scaleGenG
  erw [map_mul, gm_res r z _ hz]

theorem val_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (genPowG t φ ε c n) r z J = val c r z J ^ n :=
  map_pow _ _ _

theorem jet_left_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {k : Type} [Field k] (x : Sp k ⟶ X0) {κ : Type} {n : ℕ} (j₀ : t.PP.L.ι)
    (hj₀ : ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀) (ψ : overAt x (Jet k κ n) ⟶ t.G)
    (h : homAt x (jetAug : Jet k κ n →ₐ[k] k) ≫ ψ = 1) (q : Sp (Jet k κ n)) : ψ.left q ∈ t.PP.L.U j₀ := by
  have hsurj : Function.Surjective (jetAug : Jet k κ n →ₐ[k] k).toRingHom :=
    fun c => ⟨algebraMap k _ c, (jetAug : Jet k κ n →ₐ[k] k).commutes c⟩
  have hnil : ∀ a : Jet k κ n, jetAug a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff P = 0 := by
      have : jetAug (Ideal.Quotient.mk _ P : Jet k κ n) = MvPolynomial.aeval (fun _ : κ => (0 : k)) P := rfl
      rw [this] at ha
      simpa [MvPolynomial.aeval_zero'] using ha
    have hP : P ∈ orig k κ := by
      have : P ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set κ)) := by
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        by_contra hc
        push_neg at hc
        have hm0 : m = 0 := by ext i; exact hc i (Set.mem_univ i)
        subst hm0
        rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq] at hm
        exact hm h0
      simpa [orig, Set.image_univ] using this
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hP _
  have hrange := range_comap_of_surjective _ _ hsurj
  have huniv : PrimeSpectrum.zeroLocus (RingHom.ker (jetAug : Jet k κ n →ₐ[k] k).toRingHom : Set (Jet k κ n)) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro a ha
    exact mem_nilradical.2 (hnil a (RingHom.mem_ker.1 ha))
  obtain ⟨p, hp⟩ : q ∈ Set.range (PrimeSpectrum.comap (jetAug : Jet k κ n →ₐ[k] k).toRingHom) := by
    rw [hrange, huniv]; trivial
  have hl := congrArg (fun g => Over.Hom.left g) h
  simp only [Over.comp_left] at hl
  have hq : ψ.left q = (1 : overAt x k ⟶ t.G).left p := by
    rw [← hl, ← hp]
    rfl
  rw [hq]
  exact hj₀ (show p ∈ (⊤ : (Sp k).Opens) from trivial)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.holomorphic_disc_ratio_growth : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc | exact GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.isArithVar_of_block_algebraic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι' k) → Ω) (d : ℕ), IsBlockMap κ v → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsArithVar (mCoordIdeal (y ∘ v)) d → (∀ t ∈ blockFnField y, IsAlgebraic (blockFnField (y ∘ v)) t) → IsArithVar (mCoordIdeal y) d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image | exact GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

theorem _root_.GlobalTheory.T.exists_unique_rational_statement : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | exact GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ReciprocityTheory.ChartRestriction.G.AI.I2

theorem vertical_holds : VerticalStatement := GroundTheory.Heights₂.Heights.Inter.InductiveIntersectionFormula.proof

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem resBridgeStatement_holds : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.resBridge

end GlobalTheory.CompanionTheory.Ar.Link
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.MaxTorus

theorem kernel_eq_of_rank_le : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ :=
  @PositivityTheory.Xgn.maximal_torus_in_fibre

end GlobalTheory.CompanionTheory.Ar.MaxTorus
end
