module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle116
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedNormalisation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle067
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle104
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle122
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ContentZeroAtSmallPrimes
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCondPf
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle025
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle121
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle124
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

theorem _root_.GlobalTheory.T.markedLattice_isometry_double_coset_move : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (X X' : Data D.host.E r) (A A' : Datum H) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (h γ κ : GA D V), ModelW V hr X → ModelW V hr X' → (∀ a b, ((A.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → (∀ a b, ((A'.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → D.host.E) (φ' b))) → γ ∈ GQ V → latGHat V κ = latGHat V 1 → (∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s a)) + l.M • w) → Marked V hr io l X.Λ (fun a => (φ (t a) : Fin r → D.host.E)) h → Marked V hr io l X'.Λ (fun a => (φ' (t' a) : Fin r → D.host.E)) (γ * h * κ) → ∃ gam : A.La ≃ₗ[𝓞 D.host.E] A'.La, (∀ a b, A'.EF (gam a) (gam b) = A.EF a b) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ x, gam (t (s a)) = t' a + l.M • x := by
  first | exact @GlobalTheory.ShortMoveIso.marked_isometry | exact GlobalTheory.ShortMoveIso.marked_isometry | (intros; apply GlobalTheory.ShortMoveIso.marked_isometry <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGenerators

open TorusExt

attribute [local instance] gtGroup

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem exists_lift (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) (a : O) (N k : ℕ)
    (haa : a * star a = (N : O)) (u v : O) (huv : u * N + v * k = 1) (p : QkPt D F k) :
    ∃ (p' : QkPt D F k) (p₁ : QkPt D F (k * N)), QkPt.Equiv D F p p' ∧ GtAct oa a p₁.g p'.g ∧
      p₁.y = star a • p'.y ∧ ∀ b : O, QkPt.Equiv D F (qkZero hB F k) (qkSmul hB hG oa b p) →
        QkPt.Equiv D F (qkZero hB F (k * N)) (qkSmul hB hG oa b p₁) := by
  letI := gtModule hG oa F
  have hs : ∀ (c : O) (g : GtPtF D F), gtSmul hG oa c g = c • g := fun _ _ => rfl
  have hι : ∀ (c : O) (y : D.X), iota hB F (c • y) = c • iota hB F y := iota_smul hG oa hB
  have hp : (k : O) • p.g = iota hB F p.y := by rw [Nat.cast_smul_eq_nsmul]; exact qk_nsmul hB p
  have e : u * N = 1 + k * -v := by linear_combination huv
  refine ⟨qkSmul hB hG oa (u * N) p, qkMk hB (star a • (u * N) • p.y) ((u * star a) • p.g) ?_, ?_, ?_, rfl, ?_⟩
  · rw [hι, hι, ← hp, ← Nat.cast_smul_eq_nsmul O, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · refine (equiv_iff hB _ _).2 ⟨(-v) • p.y, ?_, ?_⟩
    · show (u * N) • p.y = p.y + k • (-v) • p.y
      rw [e, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul]
    · show (u * N) • p.g = p.g + iota hB F ((-v) • p.y)
      rw [hι, ← hp, e, add_smul, one_smul, mul_comm, mul_smul]
  · refine (gtAct_iff_eq_gtSmul hG oa _ _ _).2 ?_
    show (u * N) • p.g = a • (u * star a) • p.g
    rw [smul_smul, ← haa]
    congr 1
    ring
  · intro b hb
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 hb
    have hy' : b • p.y = (k : O) • z := by
      rw [Nat.cast_smul_eq_nsmul]; exact hy.trans (zero_add _)
    have hg' : b • p.g = iota hB F z := hg.trans (zero_add _)
    refine (equiv_iff hB _ _).2 ⟨(u * star a) • z, ?_, ?_⟩
    · show b • star a • (u * N) • p.y = 0 + (k * N) • (u * star a) • z
      rw [zero_add, smul_comm b, smul_comm b, hy', ← Nat.cast_smul_eq_nsmul O, smul_smul, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    · show b • (u * star a) • p.g = 0 + iota hB F ((u * star a) • z)
      rw [zero_add, smul_comm b, hg', hι]

theorem killed_iff (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) {k : ℕ} {G : Type} [Group G]
    (f : QkPt D F k → G) (act : O → G → G) (h₁ : ∀ p p', f p = f p' ↔ QkPt.Equiv D F p p')
    (h₂ : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p')
    (h₃ : ∀ a p p', QkAct oa a p p' → f p' = act a (f p)) (b : O) (p : QkPt D F k) :
    act b (f p) = 1 ↔ QkPt.Equiv D F (qkZero hB F k) (qkSmul hB hG oa b p) := by
  have z : f (qkZero hB F k) = 1 := by
    have e : qkAdd hB (qkZero hB F k) (qkZero hB F k) = qkZero hB F k := qk_ext (add_zero _) (add_zero _)
    have := h₂ _ _ _ (qkAdd_qkAdd hB (qkZero hB F k) (qkZero hB F k))
    rw [e] at this
    exact left_eq_mul.1 this
  rw [← h₁, z, h₃ b p _ (qkAct_qkSmul hB hG oa b p), eq_comm]

end Points

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem exists_operator (hL : Laws) (oa : D.toPre.OAct O) (w0 : O) (hw0 : TraceFormTwistIso D.toPre oa w0) (a : O) (N k : ℕ)
    (hN : 1 ≤ N) (hk : 1 ≤ k) (haa : a * star a = (N : O))
    (π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N)) (hπ : Function.Injective π)
    (hπ' : ∀ s s', PullAl D F oa a k N s s' ↔ s' = π s) (θ : Fam D.toPre F k) (hθ : θ ≠ 0)
    (p p' : QkPt D.toPre F k) (p₀ p₁ p₂ : QkPt D.toPre F (k * N)) (he : QkPt.Equiv D.toPre F p p')
    (hg : GtAct oa a p₁.g p'.g) (hy : p₁.y = star a • p'.y) (hy₂ : p₂.y = p₀.y + p₁.y) (hg₂ : p₀.g.IsAdd p₁.g p₂.g)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (w₀ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₀.g.b) (DegPre.lineε (k * N)))) (hw₀ : w₀.IsGen)
    (ζ ζ₀ : F) (hζ : FinOrd D F k p w ζ) (hζ₀ : FinOrd D F (k * N) p₀ w₀ ζ₀) :
    ∃ w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε (k * N))), w₂.IsGen ∧
      FinOrd D F (k * N) p₂ w₂ (ζ₀ * ζ) ∧ ∀ s t t', PhiRel D.toPre F k p w s t →
        PhiRel D.toPre F (k * N) p₀ w₀ (π t) t' → PhiRel D.toPre F (k * N) p₂ w₂ (π s) t' := by
  have hkN : 1 ≤ k * N := Nat.mul_pos hk hN
  obtain ⟨w', hw', h'⟩ := phiRel_of_qkEquiv hL V D F k hk p p' he w hw
  obtain ⟨w₁, hw₁, h₁⟩ := ThetaPull.phiRel_pullAl hL V D F O oa w0 hw0 a N k hN hk haa p' p₁ hg hy w' hw'
  obtain ⟨w₂, hw₂, h₂⟩ := phi_mul hL V D F (k * N) hkN p₀ p₁ p₂ hy₂ hg₂ w₀ w₁ hw₀ hw₁
  have hc : ∀ s t, PhiRel D.toPre F k p w s t → PhiRel D.toPre F (k * N) p₁ w₁ (π s) (π t) := fun s t h =>
    h₁ s t _ _ ((h' s t).1 h) ((hπ' _ _).2 rfl) ((hπ' _ _).2 rfl)
  refine ⟨w₂, hw₂, ?_, fun s t t' h h₀ => h₂ _ _ _ (hc s t h) h₀⟩
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V _ D F k hk p w hw
  obtain ⟨Φ₁, hΦ₁⟩ := phiFun_of hL V _ D F (k * N) hkN p₁ w₁ hw₁
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p w ζ Φ hΦ).1 hζ
  have hn : ∀ (n : ℕ) (s : Fam D.toPre F k), ((ζ • Φ₁ : Module.End F (Fam D.toPre F (k * N))) ^ n) (π s) =
      π (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ n) s) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih, LinearMap.smul_apply,
        LinearMap.smul_apply, map_smul π, (hΦ₁ _ _).1 (hc s _ ((hΦ _ _).2 rfl))]
  obtain ⟨c₁, c₂⟩ := finOrd_criteria hL V D F (k * N) hkN
  refine c₂ p₀ p₁ p₂ hy₂ hg₂ w₀ w₁ w₂ hw₀ hw₁ hw₂ h₂ ζ₀ ζ hζ₀
    (c₁ p₁ w₁ hw₁ ζ Φ₁ hΦ₁ (π θ) M (fun h => hθ (hπ (h.trans (map_zero π).symm))) hM ?_)
  exact (hn M θ).trans (by rw [hU]; rfl)

end GlobalTheory.ThetaGenerators

namespace GlobalTheory


open ThetaGenerators TorusExt in
theorem operator_on_pullback_eq_sum : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → letI := H.starRing; ∀ (a a' : 𝓞 E) (N N' : ℕ), 1 ≤ N → 1 ≤ N' → Nat.Coprime N N' → a * star a = (N : 𝓞 E) → a' * star a' = (N' : 𝓞 E) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (θ' s : Fam P.D.toPre F (1 * N')) (θ₂ s₂ t₀ h : Fam P.D.toPre F (1 * N' * N)), θ' ≠ 0 → PullAl P.D F P.oD a (1 * N') N θ' θ₂ → PullAl P.D F P.oD a (1 * N') N s s₂ → ∀ (m : ℕ) (c : Fin m → F) (p : Fin m → QkPt P.D.toPre F (1 * N')) (x : Fin m → (TFK (R := V) F ⟶ P.A.A)) (w : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p i).g.b) (DegPre.lineε (1 * N')))) (ζ : Fin m → F) (tt : Fin m → Fam P.D.toPre F (1 * N')), ((∀ i, P.ToA F (1 * N') (p i) (x i)) ∧ (∀ i, x i ≫ P.oA.act (star (a')) = 1) ∧ (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd P.D F (1 * N') (p i) (w i) (ζ i)) ∧ (∀ i, ∃ t' : Fam P.D.toPre F (1 * N'), PhiRel P.D.toPre F (1 * N') (p i) (w i) θ' t' ∧ Fam.IsSmul P.D.toPre F (ζ i) t' (tt i)) ∧ s = ∑ i, c i • tt i) → ∀ (p₀ : QkPt P.D.toPre F (1 * N' * N)) (x₀ : TFK (R := V) F ⟶ P.A.A) (w₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₀.g.b) (DegPre.lineε (1 * N' * N)))) (ζ₀ : F), P.ToA F (1 * N' * N) p₀ x₀ → x₀ ≫ P.oA.act (star a) = 1 → w₀.IsGen → ζ₀ ≠ 0 → FinOrd P.D F (1 * N' * N) p₀ w₀ ζ₀ → PhiRel P.D.toPre F (1 * N' * N) p₀ w₀ s₂ t₀ → Fam.IsSmul P.D.toPre F ζ₀ t₀ h → ∃ (p₂ : Fin m → QkPt P.D.toPre F (1 * N' * N)) (x₂ : Fin m → (TFK (R := V) F ⟶ P.A.A)) (w₂ : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₂ i).g.b) (DegPre.lineε (1 * N' * N)))) (ζ₂ : Fin m → F) (t₂ : Fin m → Fam P.D.toPre F (1 * N' * N)), (∀ i, P.ToA F (1 * N' * N) (p₂ i) (x₂ i)) ∧ (∀ i, x₂ i ≫ P.oA.act (star (a' * a)) = 1) ∧ (∀ i, (w₂ i).IsGen ∧ ζ₂ i ≠ 0 ∧ FinOrd P.D F (1 * N' * N) (p₂ i) (w₂ i) (ζ₂ i)) ∧ (∀ i, ∃ t' : Fam P.D.toPre F (1 * N' * N), PhiRel P.D.toPre F (1 * N' * N) (p₂ i) (w₂ i) θ₂ t' ∧ Fam.IsSmul P.D.toPre F (ζ₂ i) t' (t₂ i)) ∧ h = ∑ i, c i • t₂ i := by
  intro hL E _ _ _ H V _ _ _ t P hT
  letI := H.starRing
  intro a a' N N' hN hN' hco haa _ F _ _ _ θ' s θ₂ s₂ t₀ h hθ hθ₂ hs₂ m c p x w ζ tt ⟨hx, hxa, hw, htt, hs⟩
    p₀ x₀ w₀ ζ₀ hx₀ hxa₀ hw₀ hζ₀ hf₀ ht₀ hh
  have hG := hL.globalFns
  have hB := P.D.tau_bimult
  have hk : 1 ≤ 1 * N' := by omega
  have hkN : 1 ≤ 1 * N' * N := Nat.mul_pos hk hN
  obtain ⟨u, v, huv⟩ : IsCoprime (N : 𝓞 E) ((1 * N' : ℕ) : 𝓞 E) := by
    rw [_root_.one_mul]; exact hco.cast
  obtain ⟨π, hπ, hπ'⟩ := PullLin.exists_pull_linearMap hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a N (1 * N') hN hk haa
  obtain rfl := (hπ' _ _).1 hθ₂
  obtain rfl := (hπ' _ _).1 hs₂
  obtain ⟨f, f₀, -, f₁, f₂, f₃, -⟩ := hT F (1 * N') hk
  obtain ⟨g, g₀, -, g₁, g₂, g₃, -⟩ := hT F (1 * N' * N) hkN
  obtain ⟨Φ₀, hΦ₀⟩ := phiFun_of hL V _ P.D F (1 * N' * N) hkN p₀ w₀ hw₀
  choose p' p₁ he hg hy hb using fun i => exists_lift hG hB P.oD a N (1 * N') haa u v huv (p i)
  choose w₂ hw₂ hf₂ hΦ₂ using fun i => exists_operator hL P.oD H.w0 P.w0 a N (1 * N') hN hk haa π hπ hπ' θ' hθ
    (p i) (p' i) p₀ (p₁ i) (qkAdd hB p₀ (p₁ i)) (he i) (hg i) (hy i) rfl ((isAdd_iff_eq _ _ _).2 rfl)
    (w i) (hw i).1 w₀ hw₀ (ζ i) ζ₀ (hw i).2.2 hf₀
  choose t' ht' htt' using htt
  refine ⟨fun i => qkAdd hB p₀ (p₁ i), fun i => g (qkAdd hB p₀ (p₁ i)), w₂, fun i => ζ₀ * ζ i,
    fun i => (ζ₀ * ζ i) • Φ₀ (π (t' i)), fun i => (g₀ _ _).2 rfl, fun i => ?_,
    fun i => ⟨hw₂ i, mul_ne_zero hζ₀ (hw i).2.1, hf₂ i⟩,
    fun i => ⟨_, hΦ₂ i _ _ _ (ht' i) ((hΦ₀ _ _).2 rfl), (DVR.isSmul_iff _ _ _).2 rfl⟩, ?_⟩
  · have k₁ : g (p₁ i) ≫ P.oA.act (star a') = 1 :=
      (killed_iff hG hB P.oD g (fun b y => y ≫ P.oA.act b) g₁ g₂ g₃ (star a') (p₁ i)).2 (hb i _
        ((killed_iff hG hB P.oD f (fun b y => y ≫ P.oA.act b) f₁ f₂ f₃ (star a') (p i)).1
          ((f₀ _ _).1 (hx i) ▸ hxa i)))
    have := P.oA.hom (star (a' * a))
    have := P.oA.hom (star a')
    have := P.oA.hom (star a)
    have e₀ : x₀ ≫ P.oA.act (star (a' * a)) = 1 := by
      rw [star_mul', P.oA.map_mul, ← Category.assoc, hxa₀, MonObj.one_comp]
    have e₁ : g (p₁ i) ≫ P.oA.act (star (a' * a)) = 1 := by
      rw [star_mul, P.oA.map_mul, ← Category.assoc, k₁, MonObj.one_comp]
    show g (qkAdd hB p₀ (p₁ i)) ≫ P.oA.act (star (a' * a)) = 1
    rw [g₂ _ _ _ (qkAdd_qkAdd hB p₀ (p₁ i)), ← (g₀ _ _).1 hx₀, MonObj.mul_comp, e₀, e₁, _root_.mul_one]

  · rw [(DVR.isSmul_iff _ _ _).1 hh, (hΦ₀ _ _).1 ht₀, hs, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(DVR.isSmul_iff _ _ _).1 (htt' i), map_smul, map_smul, map_smul, map_smul, smul_comm, smul_smul ζ₀]

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem _root_.GlobalTheory.T.hostField_two_conjugate_places_over_two : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), H.d = D.host.d → ∀ (p : ℕ) [Fact p.Prime], p ∈ D.host.small → UpperTheory.Depth.SplitAt H.d p ∧ UpperTheory.Depth.SplitPlaces p H D.R.f (D.host.vdH p) ∧ 0 ≤ D.host.vdH p ∧ D.host.vdH p ≤ vd2 D := by
  first | exact @GlobalTheory.CharDepth.twoPlaces_host | exact GlobalTheory.CharDepth.twoPlaces_host | (intros; apply GlobalTheory.CharDepth.twoPlaces_host <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besType_continuous_blockW (k r : ℕ) : Continuous (PI.UpqRep.blockW k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold PI.UpqRep.blockW
  split_ifs
  · exact continuous_apply_apply _ _
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem besType_hcParam : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → Q.IsType k r z π u → ∃ u₀, PI.UpqRep.IsHCTypeW k r z u₀ π := by
  intro k r Wp _ _ _ z π u hz hT hπ
  obtain ⟨g, hg, hin, honto⟩ := GlobalTheory.T.exists_frame_conj_unitaryBlock_eq_unitaryComplement k r z hz hT
  obtain ⟨hnt, ⟨h1, hmul⟩, hcont, hnorm, hirr, -⟩ := hπ
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hg.1
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hg.1
  have hc : Continuous (fun x : Matrix (Fin k) (Fin k) ℂ => g * PI.UpqRep.blockW k r x * g⁻¹) :=
    (continuous_const.matrix_mul (besType_continuous_blockW k r)).matrix_mul continuous_const
  haveI := hnt
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.exists_highestWeight_irreducible_unitaryRep_U k Wp (fun x => π (g * PI.UpqRep.blockW k r x * g⁻¹))
    (by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show π (g * PI.UpqRep.blockW k r 1 * g⁻¹) = 1
        rw [PI.HwUniqW.blockW_one, Matrix.mul_one, hgg]
        exact h1
      · intro x hx y hy
        have e : g * PI.UpqRep.blockW k r (x * y) * g⁻¹ =
            g * PI.UpqRep.blockW k r x * g⁻¹ * (g * PI.UpqRep.blockW k r y * g⁻¹) := by
          rw [← PI.HwUniqW.blockW_mul]
          calc g * (PI.UpqRep.blockW k r x * PI.UpqRep.blockW k r y) * g⁻¹
              = g * PI.UpqRep.blockW k r x * (g⁻¹ * g) * PI.UpqRep.blockW k r y * g⁻¹ := by
                rw [hgg', Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Matrix.mul_assoc]
        show π (g * PI.UpqRep.blockW k r (x * y) * g⁻¹) = _
        rw [e]
        exact hmul _ (hin x hx) _ (hin y hy)
      · intro x hx v
        exact hnorm _ (hin x hx) v
      · intro v
        have h2 : ContinuousOn (fun x : Matrix (Fin k) (Fin k) ℂ => π (g * PI.UpqRep.blockW k r x * g⁻¹))
            (PI.UpqRep.UJset (PI.UpqRep.allPos k)) :=
          hcont.comp hc.continuousOn (fun x hx => hin x hx)
        exact h2.clm_apply continuousOn_const)
    (by
      intro S hS
      refine hirr S ?_
      intro h hh v hv
      obtain ⟨x, hx, rfl⟩ := honto h hh
      exact hS x hx v hv)
  exact ⟨u₀, g, hg, hu₀⟩

end GlobalTheory
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

noncomputable section

namespace GlobalTheory

theorem intertwiner_exp_of_intertwiner {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂]
    (T : V₁ →ₗ[ℂ] V₂) {A₁ : V₁ →L[ℂ] V₁} {A₂ : V₂ →L[ℂ] V₂} (h : ∀ v, T (A₁ v) = A₂ (T v)) (v : V₁) :
    T (NormedSpace.exp A₁ v) = NormedSpace.exp A₂ (T v) := by
  have : CompleteSpace V₁ := FiniteDimensional.complete ℂ V₁
  have : CompleteSpace V₂ := FiniteDimensional.complete ℂ V₂
  have hp : ∀ n : ℕ, ∀ v, T ((A₁ ^ n) v) = (A₂ ^ n) (T v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih, h]
  have h1 := ((LinearMap.toContinuousLinearMap T).comp (ContinuousLinearMap.apply ℂ V₁ v)).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A₁)
  have h2 := (ContinuousLinearMap.apply ℂ V₂ (T v)).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A₂)
  refine h1.unique (h2.congr_fun ?_)
  intro n
  show T (((n.factorial : ℂ)⁻¹) • (A₁ ^ n) v) = ((n.factorial : ℂ)⁻¹) • (A₂ ^ n) (T v)
  rw [map_smul, hp]

theorem intertwiner_dOp_of_EB {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁]
    {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π₁ : Mx k r → (V₁ →L[ℂ] V₁)} {π₂ : Mx k r → (V₂ →L[ℂ] V₂)} (T : V₁ →ₗ[ℂ] V₂)
    {B : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0)
    (h₁ : IsRepW k r z π₁) (h₂ : IsRepW k r z π₂) (hB : IsFrameOf k r [z] B)
    (hT : ∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v)) {X : Mx k r} (hX : InLieW k r z X) :
    ∀ v, T (dOp π₁ X v) = dOp π₂ X (T v) := by
  have hE := elementary_lie_elements
  let Gd : Mx k r → Prop := fun Z => InGlW k r z Z ∧ ∀ v, T (ecOp π₁ Z v) = ecOp π₂ Z (T v)
  have gadd : ∀ Z Z', Gd Z → Gd Z' → Gd (Z + Z') := by
    intro Z Z' h h'
    have e₁ := (hE V₁ k r z π₁ h₁ Z Z' h.1 h'.1).1
    have e₂ := (hE V₂ k r z π₂ h₂ Z Z' h.1 h'.1).1
    refine ⟨e₁.1, fun v => ?_⟩
    rw [e₁.2, e₂.2, _root_.add_apply, _root_.add_apply, map_add (f := _), h.2, h'.2]
  have gsmul : ∀ (c : ℂ) Z, Gd Z → Gd (c • Z) := by
    intro c Z h
    have e₁ := (hE V₁ k r z π₁ h₁ Z Z h.1 h.1).2.1 c
    have e₂ := (hE V₂ k r z π₂ h₂ Z Z h.1 h.1).2.1 c
    refine ⟨e₁.1, fun v => ?_⟩
    rw [e₁.2, e₂.2, _root_.smul_apply, _root_.smul_apply, map_smul, h.2]
  have g0 : Gd 0 := by
    refine ⟨SkewHermitianParts.inGl_zero z, fun v => ?_⟩
    have e₁ := ((hE V₁ k r z π₁ h₁ 0 0 (SkewHermitianParts.inGl_zero z) (SkewHermitianParts.inGl_zero z)).2.1 0).2
    have e₂ := ((hE V₂ k r z π₂ h₂ 0 0 (SkewHermitianParts.inGl_zero z) (SkewHermitianParts.inGl_zero z)).2.1 0).2
    rw [zero_smul, zero_smul] at e₁ e₂
    rw [e₁, e₂]
    simp
  have gu : ∀ a b, Gd (unitB (Hpk k r) B a b) := fun a b => ⟨frame_lie hB a b, fun v => hT a b v⟩
  have hsum : Gd (∑ a, ∑ b, herm (Hpk k r) (X *ᵥ B b) (B a) • unitB (Hpk k r) B a b) :=
    Finset.sum_induction _ Gd gadd g0 fun a _ =>
      Finset.sum_induction _ Gd gadd g0 fun b _ => gsmul _ _ (gu a b)
  rw [← SkewHermitianParts.lie_expand hz hzz hB hX] at hsum
  have e₁ : ecOp π₁ X = dOp π₁ X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hX.1.1, SkewHermitianParts.hpart2_skew hX.1.1, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  have e₂ : ecOp π₂ X = dOp π₂ X := by
    unfold ecOp
    rw [SkewHermitianParts.hpart1_skew hX.1.1, SkewHermitianParts.hpart2_skew hX.1.1, SkewHermitianParts.dOp_zero, smul_zero, add_zero]
  rw [← e₁, ← e₂]
  exact hsum.2

theorem intertwiner_group_of_EB : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (T : V₁ →ₗ[ℂ] V₂) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π₁ → IsRepW k r z π₂ → IsFrameOf k r [z] B → (∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v)) → ∀ h ∈ UWset k r z, ∀ v, T (π₁ h v) = π₂ h (T v) := by
  intro V₁ _ _ _ V₂ _ _ _ k r z π₁ π₂ T B hz hTz h₁ h₂ hB hT h hh
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    rw [Qx8.herm_self']
    intro h0
    rw [neg_eq_zero, Complex.ofReal_eq_zero] at h0
    exact hTz.ne' h0
  refine (exp_generates k r z hz hTz (fun h => h ∈ UWset k r z ∧ ∀ v, T (π₁ h v) = π₂ h (T v))
    ⟨Qx8.uw_one z, fun v => ?_⟩ ?_ h hh).2
  · rw [h₁.1.1, h₂.1.1]
    rfl
  · intro X g hX hg
    have e0 : NormedSpace.exp X ∈ UWset k r z := by
      have := exp_uw hX 1
      simpa using this
    have e₁ : π₁ (NormedSpace.exp X) = NormedSpace.exp (dOp π₁ X) := by
      have := representation_exp V₁ k r z π₁ h₁ X hX 1
      simpa using this
    have e₂ : π₂ (NormedSpace.exp X) = NormedSpace.exp (dOp π₂ X) := by
      have := representation_exp V₂ k r z π₂ h₂ X hX 1
      simpa using this
    refine ⟨SkewHermitianParts.uw_mul e0 hg.1, fun v => ?_⟩
    rw [h₁.1.2 _ e0 _ hg.1, h₂.1.2 _ e0 _ hg.1, e₁, e₂]
    show T (NormedSpace.exp (dOp π₁ X) (π₁ g v)) = NormedSpace.exp (dOp π₂ X) (π₂ g (T v))
    rw [intertwiner_exp_of_intertwiner T (intertwiner_dOp_of_EB T hz hzz h₁ h₂ hB hT hX), hg.2]

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem leafDepthTwo_of_unscaled_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs) (Nd : NumDatum), (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O → ContentEqualsDatumContent N Nd ι → TiePrimes O Nd → (∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∈ O.sm → ∀ j, ∃ B : ℝ, O.T * B ≤ O.sC j ∧ nuWAt (Xo := Xo (ι j)) (c := c) Dd la (ι j) ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal)) → LeafDepth2 N O := by
  intro E _ _ _ H l Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N Nd hE hσ hT hpr hsp hPg tF tP hB
  have hT0 : (0 : ℝ) ≤ O.T := by rw [hT]; positivity
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), plc v ∈ O.sm →
      (1 ≤ DepthTie.e1 c v ∧ 1 ≤ DepthTie.e2 c v ∧ ramw v = (DepthTie.e1 c v : ℤ) * (DepthTie.e2 c v : ℤ) ∧
        ∀ j, (O.E v j : ℤ) ≤ (DepthTie.e1 c v : ℤ) *
          ⌈(DepthTie.e2 c v : ℝ) * O.T * (DepthTie.nuT Xo c Dd ι v j + if plc v ∈ O.Bad then 1 else 0)⌉) →
      O.e0 v j ≤ O.sC j + O.T + 1 := by
    intro v j hv ⟨he1, he2, hram, hEv⟩
    have hbad : plc v ∈ O.Bad := by simp [OnObj.Bad, hv]
    have hEj := hEv j
    rw [if_pos hbad] at hEj
    have hR := rounding_condition_holds (DepthTie.e1 c v) (DepthTie.e2 c v) (O.T * (DepthTie.nuT Xo c Dd ι v j + 1))
      (O.E v j) he1 he2 (by rw [← mul_assoc]; exact hEj)
    have hramR : (ramw v : ℝ) = (DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ) := by simp [hram]
    have he2R : (1 : ℝ) ≤ DepthTie.e2 c v := by exact_mod_cast he2
    have hinv : 1 / (DepthTie.e2 c v : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact he2R
    have hs1 := GlobalTheory.RunDepth.sprime_nonneg_two E H l Dw Xo c Dd K Bs Df S P oc O ι hT hpr hσ hsp hPg v hv j
    obtain ⟨B, hTB, hν⟩ := hB (placeBelow (K := c.F) v) (by rw [DepthTie.resChar_below (F := c.F) v]; exact hv) j
    have hW : DepthTie.nuWT Xo c Dd ι v j ≤ B := by
      have h0 : (0 : EReal) ≤ nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j) := le_max_left _ _
      have ht := EReal.toReal_le_toReal hν (ne_bot_of_le_ne_bot EReal.zero_ne_bot h0) (EReal.coe_ne_top _)
      rw [EReal.toReal_coe] at ht
      unfold DepthTie.nuWT
      rw [div_le_iff₀ (by linarith), mul_comm]
      exact ht
    have hTW := mul_le_mul_of_nonneg_left hW hT0
    have he0 : O.e0 v j = (O.E v j : ℝ) / ((DepthTie.e1 c v : ℝ) * (DepthTie.e2 c v : ℝ)) -
        (vw v (O.σ v j) : ℝ) / (ramw v : ℝ) := by
      unfold OnObj.e0
      rw [sub_div, hramR]
    unfold DepthTie.s1T DepthTie.sWT at hs1
    rw [he0]
    nlinarith
  intro w hw h2 j
  obtain ⟨h1, h1'⟩ := DepthTie.tieE Xo c Dd O ι hE hT hpr w hw
  exact ⟨key w j h2 h1, key (conjPl w) j (by rw [plc_conjPl]; exact h2) h1', content_zero_at_small_primes N O Nd ι hPg tF tP w h2 j⟩

end GlobalTheory.RunDepth
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem _root_.GlobalTheory.T.kappaRows_entries_le_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ τ : D.what₂.Tau, (∀ i, i.1 < D.R.k - 1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ wj D j τ + L.Sc) ∧ (∀ i, D.R.k - 1 ≤ i.1 → ((kaR Tp hK j).aP τ i : ℝ) ≤ L.etaSz) ∧ ∀ i, ((kaR Tp hK j).aM τ i : ℝ) ≤ L.etaSz := by
  first | exact @GlobalTheory.WeightRows.kappa_entries_le | exact GlobalTheory.WeightRows.kappa_entries_le | (intros; apply GlobalTheory.WeightRows.kappa_entries_le <;> assumption)
end
