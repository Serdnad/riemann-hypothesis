module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.CptConst

theorem exists_eq_algX {F : Type} [Field F] {X Z : Scheme.{0}} (p : X ⟶ Sp F) [IsIntegral X] [UniversallyClosed p]
    (g : Z ⟶ X) [GeometricallyIntegral (g ≫ p)] (f : Γ(X, ⊤)) : ∃ a : F, f = algX p ⊤ a := by
  have : IsIntegral Z := GeometricallyIntegral.isIntegral_of_subsingleton (g ≫ p)
  have hal : ∀ {W : Scheme.{0}} (q : W ⟶ Sp F),
      algX q ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ q.appTop).hom := by
    intro W q
    have : q.appLE ⊤ ⊤ le_top = q.appTop := q.appLE_eq_app
    rw [← this]
    rfl
  have hint : (algX p ⊤).IsIntegral := by
    rw [hal]
    let G := (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop
    have : G.hom.IsIntegral := by
      apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
      exact isIntegral_appTop_of_universallyClosed p
    exact this
  have hcomp : g.appTop.hom.comp (algX p ⊤) = algX (g ≫ p) ⊤ := by
    rw [hal, hal, Scheme.Hom.comp_appTop]
    rfl
  letI := (isField_of_universallyClosed F p).toField
  let φ : Γ(X, ⊤) →+* Z.functionField := (GlobalTheory.Cartier.fnOf ⊤ trivial).comp g.appTop.hom
  have hφ : φ.comp (algX p ⊤) = GlobalTheory.Cartier.constFn (g ≫ p) := by
    rw [RingHom.comp_assoc, hcomp]
    rfl
  obtain ⟨P, hP, hPf⟩ := hint f
  obtain ⟨a, ha⟩ := GlobalTheory.GeomIntConst.mem_range_constFn F Z (g ≫ p) (φ f) ⟨P, hP.ne_zero, by
    rw [← hφ, ← Polynomial.hom_eval₂, hPf, map_zero]⟩
  refine ⟨a, φ.injective ?_⟩
  rw [← ha, ← hφ]
  rfl

theorem exists_eq_constFn_compactOf :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (V : (gen Y).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → (V : Set (gen Y)) = compactOf Y U → ∀ f : Γ(gen Y, V), ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (genStr Y) V a := by
  intro E _ _ _ H D l Xo c O _ β Y U V hn _ hU hV f
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have hgi : GeometricallyIntegral (U.ι ≫ toF Xo c) := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral U.toScheme := GeometricallyIntegral.isIntegral_of_subsingleton (U.ι ≫ toF Xo c)
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsReduced (gen Y) := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_genStr Y
  have hUirr : IsIrreducible (U : Set (Xo.XF c)) :=
    isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace U.toScheme))
  have hirr : IsIrreducible (V : Set (gen Y)) :=
    hV ▸ (hUirr.image _ Y.jQ.continuous.continuousOn).closure
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, hV]
    exact isClosed_closure)
  have hr : Set.range (U.ι ≫ Y.jQ) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hV]
    exact subset_closure ⟨x.1, x.2, rfl⟩
  let g : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (U.ι ≫ Y.jQ) hr
  have hg : g ≫ V.ι ≫ genStr Y = U.ι ≫ toF Xo c := by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc]
    exact congrArg (U.ι ≫ ·) Y.jQ_over
  have : GeometricallyIntegral (g ≫ V.ι ≫ genStr Y) := hg ▸ hgi
  have hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun x _ => x.2
  obtain ⟨a, ha⟩ := exists_eq_algX (V.ι ≫ genStr Y) g ((V.ι.appLE V ⊤ hle).hom f)
  refine ⟨a, ?_⟩
  have hiso : IsIso (V.ι.appLE V ⊤ hle) := by
    rw [Scheme.Opens.ι_appLE]
    have : V.ι ''ᵁ ⊤ = V := V.ι_image_top
    have : IsIso (homOfLE (x := V.ι ''ᵁ ⊤) (y := V) this.le) := ⟨homOfLE this.ge, rfl, rfl⟩
    exact Functor.map_isIso _ (homOfLE (x := V.ι ''ᵁ ⊤) (y := V) V.ι_image_top.le).op
  refine (ConcreteCategory.bijective_of_isIso (V.ι.appLE V ⊤ hle)).1 (ha.trans ?_)
  have := Scheme.Hom.appLE_comp_appLE V.ι (genStr Y) ⊤ V ⊤ (fun _ _ => trivial) hle
  exact (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) this).symm

end GlobalTheory.CptConst
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem _root_.GlobalTheory.T.isSec_reading_decreasing_integer_exponents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), Nonempty (KeySec Xo c) → GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ G : WTZ E, Even G.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)) → ∀ f ∈ secZ Xo c (exZ Dw G), ∀ k, (U.X k).IsSec (modelWt U G k) (rdU U f k) := by
  first | exact @GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU | exact GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU | (intros; apply GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU <;> assumption)
end

section

open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory

theorem transport_cong {N r : ℕ} (e : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (x y : Fin r → ℤ)
    (h : ∀ i, ((x i : ℤ) : ZMod N) = y i) : ∀ i, ((e x i : ℤ) : ZMod N) = e y i := by
  have hd : ∀ i, (N : ℤ) ∣ x i - y i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i).symm
  choose w hw using hd
  have hxy : x - y = (N : ℤ) • w := by ext i; simp [hw i]
  have he : e x - e y = (N : ℤ) • e w := by rw [← map_sub, hxy, map_smul]
  intro i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have := congrFun he i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨-(e w i), by linarith⟩

theorem transport_minimisers : ∀ (O : Type) [CommRing O] (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] (n N : ℕ) [NeZero N] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((ebY (μ cl) i : ℤ) : ZMod N) = cl i) → ∃ σ : Equiv.Perm (Fin n → ZMod N), (∀ cl i, ((ebX (f.symm (μ (σ cl))) i : ℤ) : ZMod N) = cl i) ∧ ∀ b : LinearMap.BilinForm ℤ Y, (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → pull f.toLinearMap b (f.symm (μ (σ cl))) (f.symm (μ (σ cl))) ≤ pull f.toLinearMap b α α := by
  intro O _ X Y _ _ _ _ n N _ ebX ebY f μ hμ
  let A : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    ebY.toLinearMap ∘ₗ f.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ ebX.symm.toLinearMap
  let B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    ebX.toLinearMap ∘ₗ f.symm.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ ebY.symm.toLinearMap
  have hA : ∀ x, A x = ebY (f (ebX.symm x)) := fun x => rfl
  have hB : ∀ x, B x = ebX (f.symm (ebY.symm x)) := fun x => rfl
  have hBA : ∀ x, B (A x) = x := fun x => by simp [hA, hB]
  have hAB : ∀ x, A (B x) = x := fun x => by simp [hA, hB]
  have key : ∀ (F G : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)), (∀ x, G (F x) = x) → ∀ c i,
      ((G (ebY (μ (fun i => ((F (ebY (μ c)) i : ℤ) : ZMod N)))) i : ℤ) : ZMod N) = c i := by
    intro F G hGF c i
    rw [transport_cong G _ (F (ebY (μ c))) (fun j => hμ _ j) i, hGF, hμ]
  let σ : Equiv.Perm (Fin n → ZMod N) :=
    { toFun := fun c i => ((A (ebY (μ c)) i : ℤ) : ZMod N)
      invFun := fun c i => ((B (ebY (μ c)) i : ℤ) : ZMod N)
      left_inv := fun c => by funext i; exact key A B hBA c i
      right_inv := fun c => by funext i; exact key B A hAB c i }
  refine ⟨σ, fun c i => ?_, ?_⟩
  · have := key A B hBA c i
    rw [hB, LinearEquiv.symm_apply_apply] at this
    exact this
  · intro b hmin c α hα
    simp only [pull_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    apply hmin (σ c) (f α)
    intro i
    have h1 : ebY (f α) = A (ebX α) := by rw [hA, LinearEquiv.symm_apply_apply]
    rw [h1]
    exact transport_cong A (ebX α) (ebY (μ c)) (fun j => (hα j).trans (hμ c j).symm) i

end GlobalTheory
end

section

open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.PolFan

theorem evalZ_eq_of_nsmul_eq_sum {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {φ : InvFun O} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn γ) {b : LinearMap.BilinForm ℤ X} {k : ℕ}
    (hk : 0 < k) {cf : Fin m → ℕ} (he : k • b = ∑ j, cf j • γ j) :
    φ.evalZ b = ∑ j, ((cf j : ℝ) / k) * φ.evalZ (γ j) := by
  rw [← (linearOn_iff φ γ).1 h _ (fun j => by positivity), ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun x y => ?_
  have h1 := LinearMap.congr_fun₂ he x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h1
  have h2 : (k : ℝ) * b x y = ∑ j, (cf j : ℝ) * γ j x y := by exact_mod_cast h1
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show ∑ j, (cf j : ℝ) / k * (γ j x y : ℝ) = (∑ j, (cf j : ℝ) * γ j x y) / k by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring, ← h2]
  field_simp

theorem cones_eq_min_linear : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) →
    ∃ (Nℓ : ℕ) (ℓ : Fin p → LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ), 0 < Nℓ ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) →
      (∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j) →
      (∀ i, (Nℓ : ℝ) * φ.evalZ b' ≤ ℓ i b') ∧ ∃ i, (Nℓ : ℝ) * φ.evalZ b' = ℓ i b' := by
  intro O _ bar φ Y _ _ _ p m γ hγ
  have hs : ∀ i, IsStrict bar φ (γ i) := fun i => (hγ i).strict
  unfold IsStrict at hs
  choose N ℓ hN h1 h2 h3 using hs
  refine ⟨∏ i, N i, fun i => ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℤ) • ℓ i,
    Finset.prod_pos fun i _ => hN i, ?_⟩
  rintro b' hb hp ⟨i, k, cf, hk, he⟩
  have key : ∀ i, ((∏ j, N j : ℕ) : ℝ) = ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℝ) * N i := fun i => by
    rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have eq : ∀ i, (N i : ℝ) * φ.evalZ b' ≤ ℓ i b' := fun i => h2 i b' hb hp
  refine ⟨fun i' => ?_, i, ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i', mul_assoc]
    exact mul_le_mul_of_nonneg_left (eq i') (by positivity)
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i, mul_assoc]
    congr 1
    have hev := evalZ_eq_of_nsmul_eq_sum (hγ i).linear hk he
    have hl : (k : ℤ) * ℓ i b' = ∑ j, (cf j : ℤ) * ℓ i (γ i j) := by
      have := congrArg (ℓ i) he

      simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    have hl' : (k : ℝ) * ℓ i b' = ∑ j, (cf j : ℝ) * ℓ i (γ i j) := by exact_mod_cast hl
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [hev, Finset.mul_sum, show (ℓ i b' : ℝ) = (∑ j, (cf j : ℝ) * ℓ i (γ i j)) / k by
      rw [← hl']; field_simp, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 i j]
    field_simp

end GlobalTheory.PolFan
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.mem_basicOpen_of_sub_one_mem_baseIdealSheaf : ∀ (R : Type) [CommRing R] (I : Ideal R) (Z : Scheme.{0}) (p : Z ⟶ Spec (CommRingCat.of R)) (V : Z.Opens) (hV : IsAffineOpen V) (r : Γ(Z, V)) (z : Z), z ∈ V → I ≤ (p z).asIdeal → r - 1 ∈ (baseIdeal p I).ideal ⟨V, hV⟩ → z ∈ Z.basicOpen r := by
  first | exact @GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal | exact GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal | (intros; apply GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem ker_specMap_quotientMk (R : Type) [CommRing R] (J : Ideal R) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker =
      baseIdeal (𝟙 (Spec (CommRingCat.of R))) J := by
  rw [Scheme.ker_of_isAffine, baseIdeal]
  congr 1
  have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have h1' : ∀ y, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop.hom y) =
        Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := fun y => by
    rw [← CommRingCat.comp_apply, h1, CommRingCat.comp_apply]
    rfl
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  have hc : ∀ r : R, cst (𝟙 (Spec (CommRingCat.of R))) ⊤ r =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    intro r
    simp [cst, rs]
  ext x
  rw [RingHom.mem_ker, ← map_eq_zero_iff _ hinj, h1']
  constructor
  · intro hx
    have hm := Ideal.mem_map_of_mem (cst (𝟙 (Spec (CommRingCat.of R))) ⊤)
      (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    rwa [hc, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at hm
  · intro hx
    have hle : J.map (cst (𝟙 (Spec (CommRingCat.of R))) ⊤) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom) := by
      refine Ideal.map_le_iff_le_comap.2 fun j hj => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hc, RingHom.comp_apply, ← CommRingCat.comp_apply,
        Iso.inv_hom_id, CommRingCat.id_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hj
    exact hle hx

theorem baseChange_quotient : ∀ (R : Type) [CommRing R] (J : Ideal R) (W Y : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ W) (q : Y ⟶ Spec (CommRingCat.of (R ⧸ J))),
    IsPullback b q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) →
      IsClosedImmersion b ∧ b.ker = baseIdeal f J ∧ ∀ V : W.Opens, IsAffineOpen V →
        Function.Surjective (b.app V).hom ∧ RingHom.ker (b.app V).hom = J.map (cst f V) := by
  intro R _ J W Y f b q h
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have e : h.isoPullback.hom ≫ pullback.fst _ _ = b := h.isoPullback_hom_fst
  haveI hb : IsClosedImmersion b := by
    rw [← e]
    infer_instance
  have hk : b.ker = baseIdeal f J := by
    rw [← e, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ker_specMap_quotientMk, (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1, Category.comp_id]
  refine ⟨hb, hk, fun V hV => ⟨b.app_surjective V hV, ?_⟩⟩
  rw [← Scheme.Hom.ker_apply b ⟨V, hV⟩, hk, baseIdeal_ideal]

end GlobalTheory.FormalAlg
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → Function.Bijective (cmp1 (str A)) := by
  first | exact @GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian | exact GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian | (intros; apply GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_closedSubscheme : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (a : W.IdealSheafData), Alg (a.subschemeι ≫ f) I →
    ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) →
    ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T (fun e => t e ⊔ a) := by
  intro R _ I W f a hA t ht hp
  set ι := a.subschemeι with hι
  have hbase : ∀ J : Ideal R, (baseIdeal f J).comap ι = baseIdeal (ι ≫ f) J :=
    fun J => GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1 R W a.subscheme f ι J
  have hms := GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion a.subscheme W ι inferInstance
  let s : ℕ → a.subscheme.IdealSheafData := fun e => (t e).comap ι
  have hs : IsSystem (ι ≫ f) I s := fun e => by
    simp only [s]
    rw [ht e, Scheme.IdealSheafData.comap_sup, hbase]
  have hsp : ∀ e, IsProper ((s e).subschemeι ≫ ι ≫ f) := fun e => by
    have H : t e ≤ (s e).map ι := Scheme.IdealSheafData.le_map_comap _ _
    rw [← Category.assoc, ← Scheme.IdealSheafData.subschemeMap_subschemeι (s e) (t e) ι H,
      Category.assoc]
    haveI := hp e
    haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H) := by
      haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H ≫
          (t e).subschemeι) := by
        rw [Scheme.IdealSheafData.subschemeMap_subschemeι]; infer_instance
      exact IsClosedImmersion.of_comp_isClosedImmersion _ (t e).subschemeι
    infer_instance
  obtain ⟨T₀, hT₀p, hT₀r⟩ := hA s hs hsp
  refine ⟨T₀.map ι, ?_, fun e => ?_⟩
  · let g := T₀.subschemeι ≫ ι
    have hk : (T₀.map ι).subschemeι.ker = g.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; rfl
    haveI := IsClosedImmersion.isIso_lift _ _ hk
    have hfac : (T₀.map ι).subschemeι =
        inv (IsClosedImmersion.lift (T₀.map ι).subschemeι g hk.le) ≫ g := by
      rw [IsIso.eq_inv_comp, IsClosedImmersion.lift_fac]
    rw [hfac, Category.assoc]
    haveI : IsProper (g ≫ f) := by simpa [g, Category.assoc] using hT₀p
    infer_instance
  · calc T₀.map ι ⊔ baseIdeal f (I ^ (e + 1))
        = (T₀ ⊔ (baseIdeal f (I ^ (e + 1))).comap ι).map ι := (hms T₀ _).1.symm
      _ = (s e).map ι := by rw [hbase, hT₀r e]
      _ = ((⊥ : a.subscheme.IdealSheafData) ⊔ (t e).comap ι).map ι := by rw [bot_sup_eq]
      _ = t e ⊔ a := by
        rw [(hms ⊥ (t e)).1, Scheme.IdealSheafData.map_bot, hι,
          Scheme.IdealSheafData.ker_subschemeι, sup_comm]

end GlobalTheory.FormalAlg
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem fibre_subsingleton_of_isClosedImmersion_restrict :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z)
      (p : Z ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) →
      ∀ z : Z, I ≤ (p z).asIdeal → (⇑φ ⁻¹' {z}).Subsingleton := by
  intro R _ I X Z φ p hci z hz
  have hmem : ∀ x : X, φ x = z → x ∈ Set.range ((baseIdeal p I).comap φ).subschemeι := by
    intro x hx
    rw [Scheme.IdealSheafData.range_subschemeι, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1 R Z X p φ I]
    show x ∈ (baseIdeal (φ ≫ p) I).support
    refine (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.2.2 R X (φ ≫ p) I x).mpr ?_
    have e : (φ ≫ p) x = p (φ x) := by simp
    rw [e, hx]
    exact hz
  intro x hx x' hx'
  obtain ⟨y, rfl⟩ := hmem x hx
  obtain ⟨y', rfl⟩ := hmem x' hx'
  have hinj := (((baseIdeal p I).comap φ).subschemeι ≫ φ).isClosedEmbedding.injective
  have : y = y' := hinj (by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    have e : ∀ w, (((baseIdeal p I).comap φ).subschemeι ≫ φ) w = φ (((baseIdeal p I).comap φ).subschemeι w) := fun w => by simp
    rw [e, e, hx, hx'])
  rw [this]

end GlobalTheory.FormalAlg
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem ratRes_locRing_of_isClosed_of_isProjOver : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ x : X,
    IsClosed ({x} : Set X) → RatRes (Cartier.constFn p) (locRing x) := by
  intro X _ p hP x hx
  haveI : LocallyOfFiniteType p := GlobalTheory.isProjOver_locallyOfFiniteType ℂ X p hP
  exact ratRes_locRing_of_isClosed X p x hx

end GlobalTheory.FieldPair
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_harmonicPolynomial_localDepth_between : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (D.host.E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ A B : ℝ, NuBetween Xo la (gap Dw a) A B → ∃ P₁ ∈ harmA (Dw := Dw) c a n, PolyBetween Xo la P₁ A B := by
  first | exact @GlobalTheory.RefSum.GlobalPoly.exists_polyBetween | exact GlobalTheory.RefSum.GlobalPoly.exists_polyBetween | (intros; apply GlobalTheory.RefSum.GlobalPoly.exists_polyBetween <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.dbarCohomologousEvenForms_algebra_closed : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) , DbarCoh A 1 1 ∧ (∀ w : A.Pt → Ev n, A.IsForm (fld A w) → A.dbar (fld A w) = 0 → DbarCoh A w w) ∧ ∀ (c : ℂ) (w w' z z' : A.Pt → Ev n), DbarCoh A w w' → DbarCoh A z z' → DbarCoh A (c • w) (c • w') ∧ DbarCoh A (w + z) (w' + z') ∧ DbarCoh A (w * z) (w' * z') := by
  first | exact @GlobalTheory.ChernCalc.dbarCoh_algebra | exact GlobalTheory.ChernCalc.dbarCoh_algebra | (intros; apply GlobalTheory.ChernCalc.dbarCoh_algebra <;> assumption)
end
