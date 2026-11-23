module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle456
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle463
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

theorem linearIndependent_mulVec_unit {E : Type} [Field E] {M n : ℕ} (A : GL (Fin M) E)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ z : Fin M → E,
        ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ ((A : Matrix (Fin M) (Fin M) E) *ᵥ z) = z := by
      intro z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      simp
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem linearIndependent_gact_unitary {F E : Type} [Field F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (gact σ g X) :=
  linearIndependent_mulVec_unit (g : GL (Fin M) E) hX

theorem gact_inv_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : gact σ w⁻¹ (e0 E M) = e0 E M := by
  conv_lhs => rw [← hw]
  exact gact_inv_gact σ w _

theorem gact_zero_of_first {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (w : UJ (σ : E →+* E) (hypOne J))
    {X : Fin (n + 1) → Fin (M + 2) → E} (hX : X 0 = e0 E M 0) :
    gact σ w X 0 = gact σ w (e0 E M) 0 := by
  change ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ X 0 =
    ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ e0 E M 0
  rw [hX]

theorem gact_mem_framesOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) {X : Fin (n + 1) → Fin (M + 2) → E}
    (hX : X ∈ framesOne σ J n) : gact σ w X ∈ framesOne σ J n := by
  refine ⟨⟨linearIndependent_gact_unitary σ w hX.1.1, ?_⟩, ?_⟩
  · rw [gramE_gact]; exact hX.1.2
  · rw [gact_zero_of_first σ w hX.2, hw]

def framesOneEquiv {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (n : ℕ) {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : framesOne σ J n ≃ framesOne σ J n where
  toFun X := ⟨gact σ w X.1, gact_mem_framesOne σ hw X.2⟩
  invFun X := ⟨gact σ w⁻¹ X.1, gact_mem_framesOne σ (gact_inv_e0 σ hw) X.2⟩
  left_inv X := Subtype.ext (gact_inv_gact σ w X.1)
  right_inv X := Subtype.ext (gact_gact_inv σ w X.1)

theorem tsum_gact_framesOne (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (w : UJ (σ : E →+* E) (hypOne J))
    (hw : gact σ w (e0 E M) = e0 E M) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞) :
    ∑' X : framesOne σ J n, f (gact σ w X.1) = ∑' X : framesOne σ J n, f X.1 :=
  (framesOneEquiv σ n hw).tsum_eq (fun X => f X.1)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem linearIndependent_gact {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E}
    (hX : LinearIndependent E X) : LinearIndependent E (gact σ g X) := by
  have hker : LinearMap.ker
      (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y h => ?_
    have h1 : gact σ g (fun _ : Fin 1 => x) = gact σ g (fun _ : Fin 1 => y) :=
      funext fun _ => h
    have h2 := congrArg (gact σ g⁻¹) h1
    rw [gact_inv_gact, gact_inv_gact] at h2
    exact congrFun h2 0
  have h3 : gact σ g X =
      (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) ∘ X := by
    funext a
    rfl
  rw [h3]
  exact hX.map' (Matrix.mulVecLin ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) hker

theorem gact_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J)
    {T : Matrix (Fin n) (Fin n) E} {X : Fin n → Fin M → E} (hX : X ∈ framesE σ J T) :
    gact σ g X ∈ framesE σ J T :=
  ⟨linearIndependent_gact σ g hX.1, (gramE_gact σ g X).trans hX.2⟩

theorem tsum_framesOne : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (rr : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → UJ (σ : E →+* E) (hypOne J)), (∀ q, gact σ (rr q) q.1 = e0 E M) → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E), f X.1 = ∑' q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E), ∑' X : framesOne σ J n, f (gact σ (rr q)⁻¹ X.1) := by
  intro F E _ _ _ σ M J n rr hrr f
  have hrow : ∀ (q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))
      (X : framesOne σ J n), gact σ (rr q)⁻¹ X.1 0 = q.1 0 := by
    intro q X
    have h := congrArg (gact σ (rr q)⁻¹) (hrr q)
    rw [gact_inv_gact] at h
    have h0 := congrFun h 0
    have hX : X.1 0 = e0 E M 0 := X.2.2
    change ((((rr q)⁻¹ : UJ (σ : E →+* E) (hypOne J)) : GL (Fin (M + 2)) E) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ X.1 0 = q.1 0
    rw [hX, h0]
    rfl
  let m : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) × framesOne σ J n →
      framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) :=
    fun p => ⟨gact σ (rr p.1)⁻¹ p.2.1, gact_mem_framesE σ _ p.2.2.1⟩
  have hinj : Function.Injective m := by
    rintro ⟨q, X⟩ ⟨q', X'⟩ h
    have h1 : gact σ (rr q)⁻¹ X.1 = gact σ (rr q')⁻¹ X'.1 := congrArg Subtype.val h
    have hq : q = q' := by
      apply Subtype.ext
      funext a
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      rw [← hrow q X, ← hrow q' X', h1]
    subst hq
    have h2 := congrArg (gact σ (rr q)) h1
    rw [gact_gact_inv, gact_gact_inv] at h2
    exact Prod.ext rfl (Subtype.ext h2)
  have hsurj : Function.Surjective m := by
    rintro ⟨Y, hY⟩
    have hq : (fun _ : Fin 1 => Y 0) ∈
        framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
      refine ⟨hY.1.comp (fun _ : Fin 1 => (0 : Fin (n + 1)))
        (Function.injective_of_subsingleton _), ?_⟩
      funext a b
      exact congrFun (congrFun hY.2 0) 0
    let q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := ⟨_, hq⟩
    have hX : gact σ (rr q) Y ∈ framesOne σ J n :=
      ⟨gact_mem_framesE σ _ hY, congrFun (hrr q) 0⟩
    exact ⟨(q, ⟨_, hX⟩), Subtype.ext (gact_inv_gact σ (rr q) Y)⟩
  let e := Equiv.ofBijective m ⟨hinj, hsurj⟩
  rw [← e.tsum_eq (fun Y => f Y.1), ENNReal.tsum_prod']
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

section Torus

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_torus_of_homog {s : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring

private theorem ratio_cancel {a b F G H : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * F / (b * G) / (a / b * H) = F / G / H := by
  by_cases hG : G = 0
  · simp [hG]
  by_cases hH : H = 0
  · simp [hH]
  field_simp

theorem logNormRat_torus {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {A : HermLine ι} {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι}
    (h : IsRatSectionOn P A f g) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNormRat A f g (fun p => c p.1 * z p) = logNormRat A f g z := by
  obtain ⟨α, β, hf, hg, -, -, hd⟩ := h
  have hne : ∀ (a : K → ℕ), ‖∏ k, c k ^ a k‖ ≠ 0 := fun a =>
    norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  have hab : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ α k‖ / ‖∏ k, c k ^ β k‖ := by
    rw [norm_prod, norm_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hd k, zpow_sub₀ (norm_ne_zero_iff.2 (hc k)), norm_pow, norm_pow, zpow_natCast, zpow_natCast]
  unfold logNormRat
  rw [eval_torus_of_homog hf, eval_torus_of_homog hg, A.smul c z hc, norm_mul, norm_mul, hab,
    ratio_cancel (hne α) (hne β)]

end Torus

theorem sheetDensity_eq_of_isSheet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (P : Ideal (Pol n)) (D : ℕ) (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D)
    (B A : HermLine (Bk n)) (f g : Pol n), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (D + 1) → IsGoodProj P Ψ → IsSmoothHerm B →
    IsRatSectionOn P A f g → ∀ᵐ v : Fin D → ℂ, ∀ w γ, IsSheet P Ψ v w γ →
      sheetDensity P Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w =
        logNormRat A f g (γ v) * maDensity (fun _ y' => Real.log (B.h (γ y'))) v := by
  intro m n P D Ψ B A f g hP hΨ hB hA
  let A' : HermLine (Bk n) := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine 1
  have hA1 : ∀ z, ReciprocityTheory.ChartRestriction.G.Geo.logNorm A' 1 z = 1 := fun z => by
    simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight, Real.exp_neg]
  have hAs : IsSmoothHerm A' := contDiffOn_const
  have hs : ReciprocityTheory.ChartRestriction.G.Geo.IsSectionOn P A' 1 := by
    refine ⟨0, fun k => by simp [A', ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight], fun d hd k => ?_, fun h => ?_⟩
    · rw [MvPolynomial.support_one, Finset.mem_singleton] at hd
      subst hd
      simp
    · exact hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  filter_upwards [ReciprocityTheory.ChartRestriction.G.Geo.sheetIndep (Fin (m + 1)) (Bk n) P D Ψ (fun _ => B) A' 1 hP hΨ (fun _ => hB) hAs hs]
    with v hind w γ hγ
  have hex : ∃ γ, IsSheet P Ψ v w γ := ⟨γ, hγ⟩
  have hc := hex.choose_spec
  have h1 := hind w _ γ hc hγ
  simp only [hA1, one_mul] at h1
  have hval : logNormRat A f g (hex.choose v) = logNormRat A f g (γ v) := by
    obtain ⟨c, hcne, hcz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.sameOrbit_of_segre hγ.2.self_of_nhds.2.1.1 1 one_ne_zero
      (by rw [one_smul, hc.1, hγ.1])
    rw [hcz]
    exact logNormRat_torus hA hcne _
  unfold sheetDensity
  rw [dite_eq_left hex, hval]
  exact congrArg (logNormRat A f g (γ v) * ·) h1

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem log_eq_of_frame {a ρ F G Pa Pb φ h : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hF : 0 < F) (hG : 0 < G)
    (hPa : 0 < Pa) (hPb : 0 < Pb) (hh : h = Pa / Pb * a * Real.exp (φ / 2))
    (e : a * ρ * (G / Pb) = F / Pa) : Real.log ρ - φ / 2 = Real.log (F / G / h) := by
  have hE := Real.exp_pos (φ / 2)
  have key : F / G / h = ρ / Real.exp (φ / 2) := by
    have hF' : F = a * ρ * (G / Pb) * Pa := by
      rw [e]
      field_simp
    rw [hh, hF']
    field_simp
  rw [key, Real.log_div hρ.ne' hE.ne', Real.log_exp]

theorem value_of_ne_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : GlobalTheory.HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
    ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z →
      eval z (map (Int.castRingHom ℂ) f) ≠ 0 → eval z (map (Int.castRingHom ℂ) g) ≠ 0 →
      y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) ∧
      GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r y = logNormRat A f g z := by
  intro m n M A X _ i _ r hr f g hfg hrat y z hz hf0 hg0
  obtain ⟨α, β, hf, hg, -, -, hdeg⟩ := hfg
  obtain ⟨u, hu, hcl⟩ := hrat
  obtain ⟨w, hw⟩ : ∃ w, w = PtsOver.map i rfl _ y := ⟨_, rfl⟩
  have hz' : IsUnder w z := hw ▸ hz
  have hwb := mem_pick (M.φ σ₀).isLB w
  obtain ⟨b, hb⟩ : ∃ b, b = pick (M.φ σ₀).isLB w := ⟨_, rfl⟩
  rw [← hb] at hwb
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, Bk n k, c = fun k => ptChart (w.1 (IsLocalRing.closedPoint ℂ)) k := ⟨_, rfl⟩
  have hwc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => hc ▸ mem_ptChart _ k)
  have hwbc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) := mem_ptsIn_inf.2 ⟨hwb, hwc⟩
  have pre : ∀ V : (MP ℤ m n).Opens, w ∈ ptsIn (mpStr ℤ m n) σ₀ V → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ V) := by
    intro V hV
    subst hw
    exact CxPts.mem_ptsIn.2 (CxPts.mem_ptsIn.1 hV)
  have hyc := pre _ hwc
  have hybc := pre _ hwbc
  have hyb := pre _ hwb
  have hgc : genericPoint X ∈ i ⁻¹ᵁ mchart c := gen_mem (CxPts.mem_ptsIn.1 hyc)
  have hgb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c) := gen_mem (CxPts.mem_ptsIn.1 hybc)
  have e := hcl b c hgc hgb
  have hne : ∀ a : Fin (m + 1) → ℕ, ∏ k, z ⟨k, c k⟩ ^ a k ≠ 0 := fun a =>
    Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
  have val : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      ratVal (fnAt i c hgc s) y = eval z (map (Int.castRingHom ℂ) s) / ∏ k, z ⟨k, c k⟩ ^ a k := by
    intro s a hs
    refine (ratVal_fnOf hyc hgc _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
    exact ev_dehomog_of_isUnder m n c s a hs w z hz' hwc
  have unit : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      eval z (map (Int.castRingHom ℂ) s) ≠ 0 → UnitAt (under y) (fnAt i c hgc s) := by
    intro s a hs h0
    refine (unitAt_fnOf_iff (CxPts.mem_ptsIn.1 hyc) hgc _).2 (CxPts.mem_ptsIn.1 ((mem_ptsIn_basicOpen hyc _).2 ?_))
    rw [← ratVal_fnOf hyc hgc]
    change ratVal (fnAt i c hgc s) y ≠ 0
    rw [val s a hs]
    exact div_ne_zero h0 (hne a)
  have hF := unit f α hf hf0
  have hG := unit g β hg hg0
  have hU : UnitAt (under y) (fnOf _ hgb (i.app _ (u b c).val)) := by
    obtain ⟨v, hv⟩ := (u b c).isUnit.map (i.app (M.B.U b ⊓ mchart c)).hom
    have hv' : (v : Γ(X, i ⁻¹ᵁ (M.B.U b ⊓ mchart c))) = i.app _ (u b c).val := hv
    rw [← hv']
    exact unitAt_fnOf (CxPts.mem_ptsIn.1 hybc) hgb v
  have hR : UnitAt (under y) (r fun _ => b : X.functionField) := by
    have e' : (r fun _ => b : X.functionField) =
        fnAt i c hgc f * (fnOf _ hgb (i.app _ (u b c).val) * fnAt i c hgc g)⁻¹ := by
      rw [← e]
      have h1 := hU.ne_zero
      have h2 := hG.ne_zero
      field_simp
    rw [e']
    exact hF.mul (hU.mul hG).inv
  have hxb : under y ∈ (M.restr i).B.U (fun _ => b) := by
    refine Set.mem_iInter.2 fun _ => ?_
    subst hw
    exact CxPts.mem_ptsIn.1 hwb
  have hyb' : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).B.U (fun _ => b)) := CxPts.mem_ptsIn.2 hxb
  have ho : y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) :=
    mem_offSupp.2 fun hs =>
      ((presents_divOfRatSec (M.restr i).isLB hr).isEqn (fun _ => b) _ hxb).mem_supp_iff.1 hs hR
  refine ⟨ho, ?_⟩
  have hφ : ((M.restr i).φ σ₀).φ (fun _ => b) y = (M.φ σ₀).φ b w := by
    rw [hw]
    exact GlobalTheory.Weight.pull_φ (M.φ σ₀) i rfl _ y
  have hvU : ratVal (fnOf _ hgb (i.app _ (u b c).val)) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) (u b c : Γ(MP ℤ m n, M.B.U b ⊓ mchart c)) w := by
    refine (ratVal_fnOf hybc hgb _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
  have ev' := congrArg (ratVal · y) e
  simp only at ev'
  rw [ratVal_mul (hU.mul hR).regAt hG.regAt, ratVal_mul hU.regAt hR.regAt, hvU, val g β hg, val f α hf] at ev'
  have hP : ∀ a : Fin (m + 1) → ℕ, 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := fun a => by
    have := norm_pos_iff.2 (hne a)
    simpa only [norm_prod, norm_pow] using this
  have hh := hu.2.2 b c w z hz' hwbc
  have hzp : ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ α k) / ∏ k, ‖z ⟨k, c k⟩‖ ^ β k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 : ‖z ⟨k, c k⟩‖ ≠ 0 := norm_ne_zero_iff.2 ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
    rw [← hdeg k, zpow_sub₀ h0, zpow_natCast, zpow_natCast]
  rw [hzp] at hh
  rw [logNorm_eq _ hr ho hyb', hφ, logNormRat]
  have evn := congrArg norm ev'
  simp only [norm_mul, norm_div, norm_prod, norm_pow] at evn
  exact log_eq_of_frame (norm_pos_iff.2 (ev_ne_zero hwbc (u b c).isUnit)) (norm_pos_iff.2 (ratVal_ne_zero hR))
    (norm_pos_iff.2 hf0) (norm_pos_iff.2 hg0) (hP α) (hP β) hh evn

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCountG

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ}

def muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a =>
  2 * lam a + (((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ))

theorem wtR_muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : wtR (muZ lam lev) = muQ lam lev := by
  funext a
  simp only [wtR, muZ, muQ, rhoU]
  push_cast
  ring

theorem wtR_injective : Function.Injective (wtR : (Fin n → ℤ) → Fin n → ℝ) := fun x y h => by
  funext a
  have := congrFun h a
  simpa [wtR] using this


open Classical in
def harmZ (lam : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  ((univ : Finset (Fin n → Fin n)).filter fun lev => IsLev lam fun a => (lev a : ℕ)).image
    fun lev => muZ lam fun a => (lev a : ℕ)

open Classical in
theorem harmSet_eq (lam : Fin n → ℤ) : harmSet lam = (harmZ lam).image wtR := by
  unfold harmSet harmZ
  rw [Finset.image_image]
  refine Finset.image_congr fun lev _ => ?_
  exact (wtR_muZ lam _).symm

def hwOf {M : Type*} [AddCommGroup M] [Module ℂ M] (G : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) :
    Submodule ℂ M where
  carrier := {v | Formalism.REAL.KHighest (fun _ => true) G μ v}
  add_mem' {x y} hx hy := ⟨fun a => by rw [map_add (f := _), hx.1 a, hy.1 a, smul_add],
    fun a b hab he => by rw [map_add (f := _), hx.2 a b hab he, hy.2 a b hab he, add_zero]⟩
  zero_mem' := ⟨fun a => by simp, fun a b _ _ => by simp⟩
  smul_mem' c x hx := ⟨fun a => by rw [map_smul, hx.1 a, smul_comm],
    fun a b hab he => by rw [map_smul, hx.2 a b hab he, smul_zero]⟩

def IsDualFam (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) : Prop :=
  Formalism.REAL.GlRel G ∧ ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
    (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ ξ : E.V →L[ℂ] ℂ,
      HasDerivAt (fun t : ℝ => ξ ∘L E.ρ (γ t)⁻¹) (∑ a, ∑ b, X a b • G a b ξ) 0

end GlobalTheory.CompanionTheory.RealCountG
end
end
