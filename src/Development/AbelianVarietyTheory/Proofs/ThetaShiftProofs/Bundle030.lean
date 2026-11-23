module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemRealSpanPeriodsOfCharacterKernel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle022
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle023
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanAlg

open ConstTerm

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {R₀ : Type} [CommRing R₀] [IsDomain R₀] {D₀ : Out.DegPre R₀} {S₀ : Type} [CommRing S₀] {σ₀ : Sp S₀ ⟶ Sp R₀}
    (κ : R →+* S) (ρ : S₀ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ)))
    (g₀ : Out.GtPt D₀ (Over.mk σ₀)) {α : D.toPre.X} {α₀ : D₀.X}
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (k : Fin 4 → D₀.P.L.ι)
    (hj : FormalValue.CohCharts g α jM jf jt)
    (cg : ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) :
    valR (A := S) g.b.left _ (w.s (fun _ => k 2, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (valR (A := S₀) g₀.b.left (LB.wchart D₀.P.L (D₀.famφB α₀) ![k 2, k 0, k 1, k 3])
        (s₀.f ![k 2, k 0, k 1, k 3]) *
        valR (A := S₀) (𝟙 _) (LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) ((g₀.s α₀).s k).val) := by
  have hφ : ∀ i, FormalValue.coordφ g α i ≫ φ =
      spMap ρ ≫ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) := hg.1
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have hq₀ := comp_famφB D₀ g₀.b α₀
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have hk : ∀ i, ⊤ ≤ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) ⁻¹ᵁ D₀.P.L.U (k i) :=
    fun i => cg.trans (LB.wchart_le _ _ _ i)
  have ek : ![k 2, k 0, k 1, k 3] = fun i => k (![2, 0, 1, 3] i) := by
    funext i; fin_cases i <;> rfl
  rw [ek]
  subst ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have cf : ⊤ ≤ (show Sp S₀ ⟶ _ from g₀.b.left) ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) :=
    fun z hz => Set.mem_iInter.2 fun i =>
      (congrArg (fun q => q z ∈ D₀.P.L.U (k (![2, 0, 1, 3] i))) (hq₀ i)).mpr (hk _ hz)
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      (FormalValue.valR_spMap ρ (show Sp S₀ ⟶ _ from g₀.b.left) _ cf _)
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    (valR_pullGen ρ (g₀.s α₀) k cg))
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₅] at e₁
  rw [map_mul, ← _root_.mul_assoc (κ r)]
  refine Eq.trans ?_ (congrArg (· * _) e₁)
  exact (congrArg (_ * ·) (_root_.mul_left_comm _ _ _)).trans
    ((_root_.mul_assoc _ _ _).symm.trans (_root_.mul_assoc _ _ _).symm)

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (j : ℕ) (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) (jM : W.P.D.toPre.P.L.ι) (jf jt : Fin 4 → W.P.D.toPre.P.L.ι) (jt₀ : Fin 4 → a.D₀.P.L.ι), TanRel W ν g₁ → IsConstMul W j x s₀ f r → FormalValue.CohCharts g₁ (W.e x) jM jf jt → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀ → valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ (W.w.s (fun _ => jt₀ 2, jM)).val ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e x) jt) = TrivSqZeroExt.inl r * constEps (valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB x) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀) ((ν.s x).s jt₀).val) := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν g₁ j x s₀ f r jM jf jt jt₀ hg hf hj hc
  have := isLocalRing_dual ℂ⟦X⟧
  exact core (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) constEps W.w g₁ ν (hg x) s₀ f r (fun p => hf _ p _) jM jf jt jt₀
    hj hc

end GlobalTheory.ConstTanAlg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

theorem _root_.GlobalTheory.T.exists_constantTorusExtension_tangentRel : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)), ∃ g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧), TanRel W ν g₁ := by
  first | exact @GlobalTheory.ConstTan.exists_tanRel | exact GlobalTheory.ConstTan.exists_tanRel | (intros; apply GlobalTheory.ConstTan.exists_tanRel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_entire_unit_appellHumbert_frame_ratio : ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (X : Scheme.{0}) (L : LB X) (L' : LB A'.left), L.IsLB → L'.IsLB → ∀ (φ : A'.left ⟶ X) (w : LB.Iso L' (L.pull φ)), w.IsGen → ∀ (g g' : ℕ) (u : HolUnif A' L' g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∀ (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, (u.ex (F z)).left ≫ φ = e z) → ∀ (fr : L.ι → (Fin g → ℂ) → ℂ) (th : L.Sec) (θ : (Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j}) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → valAt' (e z) (L.U j) (th.f j) = θ z * fr j z) → ∃ ρ : (Fin g → ℂ) → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ (la : Fin g → ℂ) (l : u.Λ), F la = l → ∀ z, θ (z + la) * ρ (z + la) = χ l * Complex.exp (Real.pi * hermForm Hm (F z) l + Real.pi / 2 * hermForm Hm l l) * (θ z * ρ z) := by
  first | exact @GlobalTheory.FrameCompare.exists_entire_unit_automorphy | exact GlobalTheory.FrameCompare.exists_entire_unit_automorphy | (intros; apply GlobalTheory.FrameCompare.exists_entire_unit_automorphy <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.mem_realSpan_periods_of_character_kernel : ∀ (g n : ℕ) (S : Finset (Fin g)) (h τ : Matrix (Fin g) (Fin g) ℂ) (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (ℓ : Fin g → (Fin g → ℂ) →ₗ[ℂ] ℂ), 0 < n → (τ.map Complex.im).PosDef → (∀ k, h.mulVec (p (Pi.single (.inl k) 1)) = Pi.single k 1 ∧ h.mulVec (p (Pi.single (.inr k) 1)) = τ.mulVec (Pi.single k 1)) → (∀ k ∈ S, ∀ k' ∈ S, ∀ s : ℂ, Complex.exp (ℓ k (s • p (Pi.single (.inl k') 1))) = eTwoPi (n * s * if k' = k then 1 else 0)) → (∀ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) → ∀ k ∈ S, Complex.exp (ℓ k (p u)) = 1) → ∀ z : Fin g → ℂ, (∀ k ∈ S, ℓ k z = 0) → z ∈ Submodule.span ℝ {q | ∃ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) ∧ q = p u} := by
  first | exact @GlobalTheory.PeriodSpan.mem_span_periods | exact GlobalTheory.PeriodSpan.mem_span_periods | (intros; apply GlobalTheory.PeriodSpan.mem_span_periods <;> assumption)
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.Special

theorem exists_lift {Z Z' : Scheme.{0}} (x : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    ∃ x' : Z' ⟶ W.toScheme, x' ≫ W.ι = x := by
  refine ⟨IsOpenImmersion.lift W.ι x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h (x := p) trivial

theorem le_comp {Z Z' Z'' : Scheme.{0}} (g : Z'' ⟶ Z') (x : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    ⊤ ≤ (g ≫ x) ⁻¹ᵁ W := fun p _ => h (x := g p) trivial

theorem le_powOver {S Z' : Scheme.{0}} (G : Over S) (L : LB G.left) (U : S.Opens) (N : ℕ)
    (x : Z' ⟶ (G.hom ⁻¹ᵁ U).toScheme) (j : L.ι) (h : ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ (Out.powOver G L U N).U (fun _ => j) :=
  fun p _ => Set.mem_iInter.2 fun _ => h (x := p) trivial

theorem exists_chart {Z : Scheme.{0}} {K : Type} [Field K] (L : LB Z) (hL : L.IsLB) (x : Sp K ⟶ Z) :
    ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  have h : x (default : PrimeSpectrum K) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨j, fun p _ => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact hj

theorem exists_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (hL : L.IsLB)
    {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (y : Sp R ⟶ S) (x : Sp K ⟶ G.left) (hx : x ≫ G.hom = spMap f ≫ y) (τ : L.ι → K) (hτ : IsFrm L x τ)
    (U : S.Opens) (hU : IsAffineOpen U) (hyU : ⊤ ≤ y ⁻¹ᵁ U) {n : ℕ} (b : Fin n → LB.Sec (Out.powOver G L U 4))
    (hb : AmpleSpan.EmbedsBy (G.hom ∣_ U) b) (cf : Fin n → R) (hcf : ∃ i, IsUnit (cf i))
    (hv : ∀ i (x' : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (j : L.ι), x' ≫ (G.hom ⁻¹ᵁ U).ι = x → ⊤ ≤ x ⁻¹ᵁ L.U j →
      valR x' ((Out.powOver G L U 4).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * τ j ^ 4)
    (U' : S.Opens) (hyU' : ⊤ ≤ y ⁻¹ᵁ U') (b' : LB.Sec (Out.powOver G L U' 5)) (cf' : R) (hcf' : IsUnit cf')
    (hv' : ∀ (x' : Sp K ⟶ (G.hom ⁻¹ᵁ U').toScheme) (j : L.ι), x' ≫ (G.hom ⁻¹ᵁ U').ι = x → ⊤ ≤ x ⁻¹ᵁ L.U j →
      valR x' ((Out.powOver G L U' 5).U (fun _ => j)) (b'.f (fun _ => j)) = f cf' * τ j ^ 5) :
    ∃ (z : Sp R ⟶ G.left) (σ : L.ι → R), z ≫ G.hom = y ∧ spMap f ≫ z = x ∧ IsFrm L z σ ∧
      ∀ j, ⊤ ≤ z ⁻¹ᵁ L.U j → f (σ j) = τ j := by
  classical
  have hxU : ⊤ ≤ x ⁻¹ᵁ (G.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hx]
    exact le_comp _ _ _ hyU
  obtain ⟨x₁, hx₁⟩ := exists_lift x _ hxU
  obtain ⟨j₀, hj₀⟩ := exists_chart L hL x
  obtain ⟨u₀, hu₀⟩ := (hτ.1 j₀ hj₀).pow 4
  obtain ⟨z₁, ⟨hz₁, hz₂, hz₃⟩, -⟩ := GlobalTheory.T.existsUnique_lift_coords_localSubring S G L U 4 n b R K f y x₁ cf j₀ u₀ hL hU hb hf hyU
    (by rw [← Category.assoc, hx₁, hx]) (by rw [hx₁]; exact hj₀)
    (fun i => by rw [hu₀]; exact hv i x₁ j₀ hx₁ hj₀) hcf
  have hz : spMap f ≫ z₁ ≫ (G.hom ⁻¹ᵁ U).ι = x := by rw [← Category.assoc, hz₂, hx₁]
  have hzy : (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ≫ G.hom = y := by rw [Category.assoc, hz₁]
  have hzU' : ⊤ ≤ (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ (G.hom ⁻¹ᵁ U') := by
    rw [← Scheme.Hom.comp_preimage, hzy]
    exact hyU'
  obtain ⟨z₂, hz₄⟩ := exists_lift _ _ hzU'
  have key : ∀ j, ⊤ ≤ (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ r : R, IsUnit r ∧ f r = τ j := by
    intro j hj
    have hxj : ⊤ ≤ x ⁻¹ᵁ L.U j := by rw [← hz]; exact le_comp _ _ _ hj
    obtain ⟨u, hu⟩ := hz₃ j hj
    obtain ⟨i, hi⟩ := hcf
    have h4 : f u = τ j ^ 4 := by
      have e := hv i x₁ j hx₁ hxj
      rw [← hz₂, HolHom.valR_spMap _ _ _ (le_powOver G L U 4 z₁ j hj), hu, map_mul] at e
      exact mul_left_cancel₀ (hi.map f).ne_zero e
    have e := hv' (spMap f ≫ z₂) j (by rw [Category.assoc, hz₄, hz]) hxj
    rw [HolHom.valR_spMap _ _ _ (le_powOver G L U' 5 z₂ j (by rw [hz₄]; exact hj))] at e
    obtain ⟨c, rfl⟩ := hcf'
    set a := valR z₂ ((Out.powOver G L U' 5).U (fun _ => j)) (b'.f (fun _ => j))
    have hc : f (↑c⁻¹ : R) * f c = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hu' : f (↑u⁻¹ : R) * f u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hr : f (↑c⁻¹ * ↑u⁻¹ * a) = τ j := by
      rw [map_mul, map_mul, e]
      rw [h4] at hu'
      linear_combination (f (↑u⁻¹ : R) * τ j ^ 5) * hc + τ j * hu'
    refine ⟨_, ?_, hr⟩
    have : (↑c⁻¹ * ↑u⁻¹ * a) ^ 4 = (u : R) := hf (by rw [map_pow, hr, h4])
    exact (isUnit_pow_iff (by norm_num : 4 ≠ 0)).1 (this ▸ u.isUnit)
  choose! σ hσ using key
  refine ⟨z₁ ≫ (G.hom ⁻¹ᵁ U).ι, σ, hzy, hz, ⟨fun j hj => (hσ j hj).1, fun j j' hj => hf ?_⟩,
    fun j hj => (hσ j hj).2⟩
  have h1 := hj.trans (Scheme.Hom.preimage_mono _ (inf_le_left : L.U j ⊓ L.U j' ≤ _))
  have h2 := hj.trans (Scheme.Hom.preimage_mono _ (inf_le_right : L.U j ⊓ L.U j' ≤ _))
  rw [map_mul, (hσ j h1).2, (hσ j' h2).2, ← HolHom.valR_spMap _ _ _ hj, hz]
  exact hτ.2 j j' (by rw [← hz]; exact le_comp _ _ _ hj)

theorem germs_local (Γ : Germs) (w : ℂ) : IsLocalRing (Γ.R w) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : Γ.ev w a = 0
    · exact Or.inr (Γ.unit w _ (by rw [map_sub, h, map_one, sub_zero]; exact one_ne_zero))
    · exact Or.inl (Γ.unit w _ h)

theorem specPts_nonempty : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (k : Type) [CommRing k] (s₀ : S ⟶ Sp k) [LocallyOfFiniteType s₀] (b₀ : k →+* ℂ), y ≫ s₀ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp b₀) → AnFin A → Φ.Rational → Nonempty (SpecPts Φ Γ) := by
  intro h1 h2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ k _ s₀ _ b₀ hy hA hΦ
  classical
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_projCoords_convergent_coefficients h1 h2 E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨C'⟩ := GlobalTheory.T.nonempty_projCoords_convergent_coefficients h1 h2 E H D l B bb S s o A y Φ hA hΦ 5 (by norm_num)
  haveI := o.proper
  obtain ⟨x₀, hx₀⟩ := hΦ.1 0
  have hy₀ : spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫ x₀ ≫ o.t.G.hom = y := by
    rw [← Category.assoc, hx₀]
    exact Over.w (Φ.x 0)
  set y₀ := x₀ ≫ o.t.G.hom
  have hin : ∀ U : S.Opens, ⊤ ≤ y ⁻¹ᵁ U → ⊤ ≤ y₀ ⁻¹ᵁ U := by
    intro U hU p _
    rw [← hy₀] at hU
    obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  have hs₀ : y₀ ≫ s₀ = spMap ((algebraMap ℂ Conv.convLaurent).comp b₀) := by
    refine HolHom.point_ext (isAffineOpen_top _) le_top le_top fun g => Subtype.ext ?_
    have e1 := HolHom.valR_spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (y₀ ≫ s₀) ⊤ le_top g
    have e2 := HolHom.valR_spMap (algebraMap Conv.convLaurent ℂ⸨X⸩)
      (spMap ((algebraMap ℂ Conv.convLaurent).comp b₀)) ⊤ le_top g
    rw [← Category.assoc, hy₀, hy] at e1
    rw [← spMap_comp] at e2
    exact e1.symm.trans e2
  obtain ⟨T₁, hT₁, y₁, hy₁U, hy₁, -⟩ :=
    Conv.exists_halfRing_point s₀ b₀ y₀ hs₀ C.aff (hin _ C.mem) (max C.T C'.T)
  obtain ⟨T, hT, hU'⟩ := Conv.exists_le_preimage_inclusion y₁ (U := C'.U) (by rw [hy₁]; exact hin _ C'.mem)
  set yT := spMap (Subalgebra.inclusion (Conv.halfRing_mono hT) : Conv.halfRing T₁ →+* Conv.halfRing T) ≫ y₁ with hyT
  have hU : ⊤ ≤ yT ⁻¹ᵁ C.U := le_comp _ _ _ hy₁U
  have hgen : spMap (Conv.halfRing T).val.toRingHom ≫ yT = y := by
    rw [← hy₀, ← hy₁, hyT, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    rfl
  have hC : C.T ≤ T := ((le_max_left _ _).trans hT₁).trans hT
  have hC' : C'.T ≤ T := ((le_max_right _ _).trans hT₁).trans hT
  have key : ∀ (w : ℂ) (hw : T < w.im) (v : A.V), ∃ (z : Sp (Γ.R w) ⟶ o.t.G.left) (σ : o.t.PP.L.ι → Γ.R w),
      z ≫ o.t.G.hom = spMap (Subalgebra.inclusion (Γ.le T w hw)).toRingHom ≫ yT ∧
      spMap (Γ.R w).val.toRingHom ≫ z = (Φ.x v).left ∧ IsFrm o.t.PP.L z σ ∧
      ∀ j, ⊤ ≤ z ⁻¹ᵁ o.t.PP.L.U j → (Γ.R w).val.toRingHom (σ j) = Φ.τ v j := by
    intro w hw v
    haveI := germs_local Γ w
    have hw₁ := hC.trans_lt hw
    have hw₂ := hC'.trans_lt hw
    obtain ⟨i, hi⟩ := C.bpf w hw₁ v
    obtain ⟨i', hi'⟩ := C'.bpf w hw₂ v
    refine exists_ext o.t.G o.t.PP.L o.t.PP.isLB (Γ.R w).val.toRingHom Subtype.val_injective _ (Φ.x v).left ?_
      (Φ.τ v) (Φ.frm v) C.U C.aff (le_comp _ _ _ hU) C.b C.emb
      (fun i => Subalgebra.inclusion (Γ.le _ w hw₁) (C.cf i v)) ⟨i, Γ.unit w _ (by rw [Γ.ev_eq]; exact hi)⟩
      (fun i x' j => C.val i v x' j) C'.U (le_comp _ _ _ hU') (C'.b i')
      (Subalgebra.inclusion (Γ.le _ w hw₂) (C'.cf i' v)) (Γ.unit w _ (by rw [Γ.ev_eq]; exact hi'))
      (fun x' j => C'.val i' v x' j)
    rw [← Category.assoc, ← spMap_comp]
    exact (Over.w (Φ.x v)).trans hgen.symm
  choose z σ hz1 hz2 hz3 hz4 using key
  have hpi : ∀ (w : ℂ) (hw : T < w.im) (v : A.V),
      (spMap (Γ.ev w).toRingHom ≫ z w hw v) ≫ o.t.G.hom = Conv.halfCurve yT w := by
    intro w hw v
    rw [Category.assoc, hz1, ← Category.assoc, ← spMap_comp, Conv.halfCurve_eq yT hw]
    congr 2
    exact RingHom.ext fun r => Γ.ev_eq T w hw r
  exact ⟨{
    T := T
    yT := yT
    yT_gen := hgen
    xt := fun w hw v => Over.homMk (z w hw v) (hz1 w hw v)
    xt_gen := hz2
    τt := fun w v => if hw : T < w.im then σ w hw v else fun _ => 1
    τt_frm := fun w hw v => by rw [dite_eq_left hw]; exact hz3 w hw v
    τt_gen := fun w hw v j hj => by rw [dite_eq_left hw]; exact hz4 w hw v j hj
    yw := Conv.halfCurve yT
    yw_eq := fun w hw => Conv.halfCurve_eq yT hw
    pi := fun w v => if hw : T < w.im then Over.homMk (spMap (Γ.ev w).toRingHom ≫ z w hw v) (hpi w hw v) else 1
    pi_eq := fun w hw v => by rw [dite_eq_left hw]; rfl }⟩

end GlobalTheory.ArcPts.Special
end
end
