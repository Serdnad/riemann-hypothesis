module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartStandardSmooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle175
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle173
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle121
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.exists_projective_coord_model : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (Ab : Set X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → SncPts ξ e {p | Char0 ξ p ∧ p.1 ∉ Ab} → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (g : M.X ⟶ X), Nonempty K ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ g (RingHom.id Ω) ∧ Flat.NormalCpt M.ξ ∧ SncPts M.ξ e {p | Char0 M.ξ p ∧ g p.1 ∉ Ab} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model | exact GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem injective_ringOfIntegers_toComplex {F : Type} [Field F] [NumberField F] (g : 𝓞 F →+* ℂ) :
    Function.Injective g := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  have h : Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker g) = RingHom.ker (g.comp (algebraMap ℤ (𝓞 F))) :=
    RingHom.comap_ker _ _
  change Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker g) = ⊥
  rw [h, (RingHom.injective_iff_ker_eq_bot _).1]
  have e : g.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [e]
  exact Int.cast_injective

theorem exists_comp_eq_of_ringOfIntegers {F : Type} [Field F] [NumberField F] (g : 𝓞 F →+* ℂ) :
    ∃ g' : F →+* ℂ, g'.comp (algebraMap (𝓞 F) F) = g :=
  ⟨IsFractionRing.lift (injective_ringOfIntegers_toComplex g), by
    ext a
    simp⟩

theorem exists_spMap_of_ringOfIntegers {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} (s : X ⟶ Sp (𝓞 F))
    (u : Sp ℂ ⟶ X) : ∃ g' : F →+* ℂ, u ≫ s = spMap g' ≫ spMap (algebraMap (𝓞 F) F) := by
  obtain ⟨g', hg'⟩ := exists_comp_eq_of_ringOfIntegers (Spec.preimage (u ≫ s)).hom
  refine ⟨g', ?_⟩
  rw [← spMap_comp, hg']
  exact (Spec.map_preimage (u ≫ s)).symm

theorem polarisedAt_of_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type)
    [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → HodgeMetric.PolarisedAt 𝔐.t z := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z hz
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hsub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have h₁ : (z ≫ 𝔐.f) p ∈ abLocus Y.t.G := by
    have := (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (z p)).2 hz
    simpa using this

  obtain ⟨g', hg'⟩ := exists_spMap_of_ringOfIntegers Y.s (z ≫ 𝔐.f)
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift (z ≫ 𝔐.f) (spMap g') hg'
  have hw : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _

  have h₂ : w p ∈ Set.range Y.jQ := by
    rw [← Y.ab_gen]
    show (pullback.fst Y.s _) (w p) ∈ abLocus Y.t.G
    have : (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (w p) = (z ≫ 𝔐.f) p := by
      rw [← hw]; simp
    rw [this]; exact h₁
  have h₃ : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q p]
  haveI := Y.jQ_open
  let v : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w h₃
  have hv : v ≫ Y.jQ ≫ pullback.fst _ _ = z ≫ 𝔐.f := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hw]

  obtain ⟨t', ⟨m₁⟩⟩ := exists_sab z 𝔐.t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m m₁
  have cancel : ∀ (q : Sp ℂ ⟶ Y.X) (_ : q = v ≫ Y.jQ ≫ pullback.fst _ _) (_ : SABMap t' Y.t q),
      Nonempty (SABMap t' Y.oF.t v) := by
    intro q hq n; subst hq
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ hv.symm n
  obtain ⟨w₂, g₂, -⟩ := m₃.lin
  obtain ⟨am, -⟩ := amplePt _ _ v _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB t'.PP.isLB ⟨w₂, g₂⟩ Y.oF.ample Y.oF.ktriv
  exact ⟨t', m₁, MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper, am⟩

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.exists_exp_chart_standard_smooth : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom →
  ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (ρ : R), IsAffineOpen V ∧ φ ρ ≠ 0 ∧ (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V).IsStandardSmooth ∧
    (∀ θ : R →+* ℂ, θ ρ ≠ 0 → ⊤ ≤ (1 : Over.mk (spMap θ) ⟶ G).left ⁻¹ᵁ V ∧ (∀ c, valAt' (1 : Over.mk (spMap θ) ⟶ G).left V (t c) = 0) ∧
      ∀ a c, TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V (t c)) = if a = c then 1 else 0) ∧
    ∀ f : Γ(G.left, V), ∃ (u : R) (k : ℕ), ∀ θ : R →+* ℂ, θ ρ ≠ 0 → valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * θ ρ ^ k = θ u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords | exact GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.hodge_comp_descent_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → GenPull Fl₀ Fl i hd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.GP.genPull_of_frames | exact GlobalTheory.CompanionTheory.Ar.Chg.GP.genPull_of_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.GP.genPull_of_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section Pow1

variable {k : Type} [Field k] {d : ℕ}

theorem aeval_firstOrder {B A : Type} [CommRing B] [Algebra k B] [CommRing A] [Algebra k A]
    (τ : B →ₐ[k] A) (ε : A) (hε : ε * ε = 0) (c : Fin d → k) (z : Fin d → B)
    (P : MvPolynomial (Fin 2 × Fin d) k) :
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then algebraMap k A (c q.2) * ε else τ (z q.2)) P =
      τ (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2) P) +
      ε * ∑ i, algebraMap k A (c i) * τ (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2)
        (MvPolynomial.pderiv ((0 : Fin 2), i) P)) := by
  set θ : MvPolynomial (Fin 2 × Fin d) k →ₐ[k] B :=
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2) with hθ
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simp only [map_add (f := _), hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P q hP =>
    obtain ⟨a, j⟩ := q
    rw [map_mul, hP, MvPolynomial.aeval_X]
    by_cases ha : a = 0
    · subst ha
      have key : ∀ i, τ (θ (MvPolynomial.pderiv ((0 : Fin 2), i) (P * MvPolynomial.X ((0 : Fin 2), j)))) =
          if j = i then τ (θ P) else 0 := by
        intro i
        have hX : θ (MvPolynomial.X ((0 : Fin 2), j)) = 0 := by simp [hθ]
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, hX, zero_mul, add_zero,
          MvPolynomial.pderiv_X]
        by_cases hij : j = i
        · subst hij; simp
        · simp [Pi.single_apply, hij, Ne.symm hij]
      simp only [key, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hX : θ (P * MvPolynomial.X ((0 : Fin 2), j)) = 0 := by simp [hθ]
      rw [hX, map_zero, zero_add]
      linear_combination (algebraMap k A (c j) * ∑ i, algebraMap k A (c i) * τ (θ (MvPolynomial.pderiv ((0 : Fin 2), i) P))) * hε
    · have key : ∀ i, θ (MvPolynomial.pderiv ((0 : Fin 2), i) (P * MvPolynomial.X (a, j))) =
          θ (MvPolynomial.pderiv ((0 : Fin 2), i) P) * z j := by
        intro i
        have h0 : MvPolynomial.pderiv ((0 : Fin 2), i) (MvPolynomial.X (a, j) : MvPolynomial (Fin 2 × Fin d) k) = 0 := by
          rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg]
          intro h; exact ha (congrArg Prod.fst h)
        rw [Derivation.leibniz, h0, smul_zero, zero_add, smul_eq_mul, map_mul, mul_comm]
        simp [hθ, ha]
      have hX : θ (P * MvPolynomial.X (a, j)) = θ P * z j := by simp [hθ, ha]
      simp only [key, hX, ha, if_false, map_mul, Finset.mul_sum, Finset.sum_mul, add_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

theorem mk_psTrunc_of_le {κ : Type} [Fintype κ] [DecidableEq κ] {m N : ℕ} (hN : m ≤ N)
    (f : MvPowerSeries κ k) :
    Ideal.Quotient.mk (orig k κ ^ (m + 1)) (psTrunc N f) = psJet m f := by
  rw [psJet, Ideal.Quotient.eq]
  refine GermD.mem_orig_pow_of fun e he => ?_
  by_contra hlt
  push Not at hlt
  apply MvPolynomial.mem_support_iff.mp he
  rw [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc _ _ _ (by omega), GermFun.coeff_psTrunc _ _ _ (by omega), sub_self]

theorem mk_pderiv_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] {m N : ℕ} (hN : m + 1 ≤ N)
    (f : MvPowerSeries κ k) (q : κ) :
    Ideal.Quotient.mk (orig k κ ^ (m + 1)) (MvPolynomial.pderiv q (psTrunc N f)) =
      psJet m (MvPowerSeries.pderiv (R := k) q f) := by
  rw [psJet, Ideal.Quotient.eq]
  refine GermD.mem_orig_pow_of fun e he => ?_
  by_contra hlt
  push Not at hlt
  apply MvPolynomial.mem_support_iff.mp he
  have hd : (e + Finsupp.single q 1).degree = e.degree + 1 := by simp
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_pderiv, GermFun.coeff_psTrunc _ _ _ (by omega),
    GermFun.coeff_psTrunc _ _ _ (by omega), MvPowerSeries.coeff_pderiv, sub_self]

theorem aeval_axis_eq_psJet (m : ℕ) (P : MvPolynomial (Fin 2 × Fin d) k) (h : Germ.PS k 2 d)
    (hP : Ideal.Quotient.mk (orig k (Fin 2 × Fin d) ^ (m + 1)) P = psJet m h) :
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : Jet k (Fin 1 × Fin d) m)
      else Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2))) P =
      psJet m (Germ.ev (n := 1) ![0, Germ.pt k d 0] h) := by
  have ha : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) q.1 q.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a <;> simp [Germ.pt]
  rw [Germ.ev, FBIdJet.psJet_subst m _ ha, ← hP, GermD.jetMap_mk]
  have e : (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : Jet k (Fin 1 × Fin d) m)
      else Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2))) : MvPolynomial (Fin 2 × Fin d) k →ₐ[k] _) =
      (Ideal.Quotient.mkₐ k _).comp (MvPolynomial.aeval fun q : Fin 2 × Fin d =>
        psTrunc m ((![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) q.1 q.2)) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    obtain ⟨a, j⟩ := q
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X]
    show _ = psJet m _
    fin_cases a
    · simp [psJet, psTrunc]
    · have : (![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) 1 j =
          ((MvPolynomial.X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries _ k) := by
        simp [Germ.pt]
      simp only [Fin.mk_one, this, ExpGF.psJet_coe]
      simp
  rw [e]
  rfl

theorem psJet_sum_C_mul {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (u : Fin d → k)
    (h : Fin d → MvPowerSeries κ k) :
    psJet m (∑ i, MvPowerSeries.C (u i) * h i) = ∑ i, algebraMap k (Jet k κ m) (u i) * psJet m (h i) := by
  have hadd : ∀ f g : MvPowerSeries κ k, psJet m (f + g) = psJet m f + psJet m g := fun f g => by
    simp [psJet, psTrunc, Finset.sum_add_distrib]
  have hzero : psJet m (0 : MvPowerSeries κ k) = 0 := by simp [psJet, psTrunc]
  have hC : ∀ c : k, psJet m (MvPowerSeries.C c : MvPowerSeries κ k) = algebraMap k (Jet k κ m) c := fun c => by
    have : (MvPowerSeries.C c : MvPowerSeries κ k) = ((MvPolynomial.C c : MvPolynomial κ k) : MvPowerSeries κ k) := by simp
    rw [this, ExpGF.psJet_coe]
    rfl
  let L : MvPowerSeries κ k →+ Jet k κ m := ⟨⟨psJet m, hzero⟩, hadd⟩
  have := map_sum L (fun i => MvPowerSeries.C (u i) * h i) Finset.univ
  refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
  show psJet m _ = _
  rw [FBIdJet.psJet_mul, hC]

theorem jq_psJet_ptPow (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d m : ℕ) (w : Fin d → k)
    (g : Germ.PS k 2 d) (hg : AxOne g) :
    jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) =
      1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer g fun i => w i ^ p)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set B := Jet k (Fin 1 × Fin d) m with hB
  set A := Jet B Unit p with hA
  have hε : dQ B p ^ p * dQ B p ^ p = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (by omega) (dQ_pow B p)
  have ha : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) q.1 q.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    · simp [ptPow, hp]
    · simp [Germ.pt]
  have hjq : ∀ Q : MvPolynomial (Fin 2 × Fin d) k, jq w p m (Ideal.Quotient.mk _ Q) =
      MvPolynomial.aeval (fun q : Fin 2 × Fin d =>
        if q.1 = 0 then algebraMap k A (w q.2) * dQ B p
        else inR (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) Q := fun Q => rfl
  have step : jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) =
      MvPolynomial.aeval (fun q : Fin 2 × Fin d =>
        if q.1 = 0 then algebraMap k A (w q.2 ^ p) * dQ B p ^ p
        else inR (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) (psTrunc (p + m + 1) g) := by
    rw [Germ.ev, FBIdJet.psJet_subst _ _ ha, psJet, GermD.jetMap_mk, hjq, MvPolynomial.comp_aeval_apply]
    congr 2
    funext q
    obtain ⟨a, j⟩ := q
    rw [← hjq]
    show jq w p m (psJet _ _) = _
    fin_cases a
    · have : (![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) 0 j =
          ((MvPolynomial.X ((0 : Fin 2), j) ^ p : MvPolynomial (Fin 2 × Fin d) k) : MvPowerSeries _ k) := by
        simp [ptPow]
      simp only [Fin.zero_eta, this, ExpGF.psJet_coe, hjq]
      simp [mul_pow]
    · have : (![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) 1 j =
          ((MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin d) k) : MvPowerSeries _ k) := by
        simp [Germ.pt]
      simp only [Fin.mk_one, this, ExpGF.psJet_coe, hjq]
      simp
  rw [step, aeval_firstOrder (inR (k := k) B p) (dQ B p ^ p) hε (fun i => w i ^ p)
    (fun j => Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) (psTrunc (p + m + 1) g)]
  rw [aeval_axis_eq_psJet m _ g (mk_psTrunc_of_le (by omega) g), hg.1, FBIdJet.psJet_one, map_one]
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dSer, psJet_sum_C_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_axis_eq_psJet m _ _ (mk_pderiv_psTrunc (by omega) g _), map_mul]
  rw [← IsScalarTower.algebraMap_apply]
  rfl

end Pow1

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagModel

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem pull_map (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (φ : E →ₗ[Ω] E') :
    (L.map φ).pull ξ' f (AddMonoidHom.id E') = (L.pull ξ' f (AddMonoidHom.id E)).map φ := by
  funext p'
  simp only [Lat.pull, Lat.map, Submodule.map_span]
  congr 1
  ext e'
  constructor
  · rintro ⟨h, e, he, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 he
    exact ⟨u, ⟨h, u, hu, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨h, v, hv, huv⟩, rfl⟩
    exact ⟨h, φ v, Submodule.mem_map.2 ⟨v, hv, rfl⟩, congrArg φ huv⟩

theorem pull_vb {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {f : X' ⟶ X} (hd : Dominates ξ' ξ f (RingHom.id Ω)) : (L.pull ξ' f (AddMonoidHom.id E)).IsVB g W := by
  intro p' _
  obtain ⟨h, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ _ _ hd p'
  obtain ⟨U, hU, b, hW, hb⟩ := hL ⟨f p'.1, h⟩ (Set.mem_univ _)
  refine ⟨f ⁻¹ᵁ U, hU, b, hW, fun q' _ hq' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ _ _ hd q'
  obtain ⟨hli, hsp⟩ := hb ⟨f q'.1, hq⟩ (Set.mem_univ _) hq'
  refine ⟨hli, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro e' ⟨h', e, he, he'⟩
    have he2 : e ∈ Submodule.span (regAt ξ ⟨f q'.1, hq⟩) (Set.range b) := hsp ▸ he
    have hee : e' = e := he'
    rw [hee]
    clear he he' hee
    induction he2 using Submodule.span_induction with
    | mem u hu => exact Submodule.subset_span hu
    | zero => exact Submodule.zero_mem _
    | add u v _ _ hu hv => exact Submodule.add_mem _ hu hv
    | smul c u _ hu => exact Submodule.smul_mem _ (⟨c.1, hreg c.1 c.2⟩ : regAt ξ' q') hu
  · refine Submodule.span_mono ?_
    intro e he
    exact ⟨hq, e, hsp ▸ Submodule.subset_span he, rfl⟩

theorem coh_map {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) (φ : E →ₗ[Ω] E') :
    (L.map φ).IsCohOn Set.univ := by
  intro p hp
  obtain ⟨U, hU, b, -, hb⟩ := hL p hp
  refine ⟨U, hU, g, φ ∘ b, fun q hq hqU => ?_⟩
  simp only [Lat.map]
  rw [(hb q hq hqU).2, Submodule.map_span, Set.range_comp]
  rfl

theorem span_map {L : Lat ξ E} {g : ℕ} {W : Submodule Ω E} (hL : L.IsVB g W) (φ : E →ₗ[Ω] E') (p : Cpt ξ) :
    Submodule.span Ω ((L.map φ) p : Set E') = W.map φ := by
  obtain ⟨U, hU, b, hW, hb⟩ := hL p (Set.mem_univ p)
  simp only [Lat.map]
  rw [(hb p (Set.mem_univ p) hU).2, Submodule.map_span, Submodule.span_span_of_tower, ← hW, Submodule.map_span]
  rfl

theorem flagStep_min {r : ℕ} (b₀ : Fin r → E) (n : ℕ) : flagStep Ω b₀ (min n r) = flagStep Ω b₀ n := by
  unfold flagStep
  congr 2
  ext k
  have := k.2
  simp only [Set.mem_setOf_eq]
  omega

theorem flagStep_le {r : ℕ} {b₀ : Fin r → E} {W : Submodule Ω E} (h : ∀ k, b₀ k ∈ W) (n : ℕ) :
    flagStep Ω b₀ n ≤ W := by
  unfold flagStep
  rw [Submodule.span_le]
  rintro _ ⟨k, -, rfl⟩
  exact h k

theorem flagModel : FlagModelStatement := by
  intro o _ _ Ω _ _ κ _ x M A _ κa _ w S _ E _ _ L g r W b₀ hw hL hb hbW
  obtain ⟨p₀⟩ : Nonempty (Cpt M.ξ) := ⟨⟨genPt M.ξ, specializes_rfl⟩⟩
  haveI hfin : ∀ σ, FiniteDimensional Ω (W σ) := fun σ => by
    obtain ⟨U, -, b, hW, -⟩ := hL σ p₀ (Set.mem_univ _)
    rw [← hW]
    exact FiniteDimensional.span_of_finite Ω (Set.finite_range b)
  obtain ⟨κ', hκ', y, M', f, hdom, hnorm, hchart, hvb, hat⟩ :=
    GlobalTheory.T.flag_model_common_refinement o Ω κ x M A κa w (Σ σ, Fin (r σ + 1))
      (fun q => E ⧸ flagStep Ω (b₀ q.1) q.2)
      (fun q => (L q.1).map (flagStep Ω (b₀ q.1) q.2).mkQ)
      (fun q => (W q.1).map (flagStep Ω (b₀ q.1) q.2).mkQ) hw
      (fun q => coh_map (hL q.1) _) (fun q p => span_map (hL q.1) _ p)
  have hpull : ∀ σ, ((L σ).pull M'.ξ f (AddMonoidHom.id E)).IsVBOn Set.univ (g σ) (W σ) :=
    fun σ => pull_vb (hL σ) hdom
  have hquot : ∀ σ (n : ℕ), ∃ s W', (((L σ).pull M'.ξ f (AddMonoidHom.id E)).map
      (flagStep Ω (b₀ σ) n).mkQ).IsVBOn Set.univ s W' := fun σ n => by
    rw [← flagStep_min]
    have h := hvb ⟨σ, ⟨min n (r σ), Nat.lt_succ_of_le (min_le_right _ _)⟩⟩
    rw [pull_map] at h
    exact ⟨_, _, h⟩
  refine ⟨κ', hκ', y, M', f, hdom, hnorm, hchart, fun σ => ?_, fun σ n p' => ?_, fun p hp hfr => ?_⟩
  · exact GlobalTheory.T.lattice_flag_vector_bundle _ _ _ _ _ _ _ _ _ _ (hb σ) (hbW σ) (hpull σ) (hquot σ)
  · obtain ⟨s, W', h⟩ := hquot σ n
    exact (GlobalTheory.T.lattice_sub_quotient_split _ _ _ _ _ _ _ _ _ _ _ (flagStep_le (hbW σ) n) (hpull σ) h).2 p' (Set.mem_univ _)
  · exact hat p hp fun q => hfr q.1 q.2

end GlobalTheory.CompanionTheory.Ar.FlagModel
end
end
