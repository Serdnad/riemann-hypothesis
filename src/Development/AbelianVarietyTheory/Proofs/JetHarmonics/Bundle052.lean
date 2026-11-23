module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle049
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.IncomingBounds.Bundle001
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalToGlobal.CharacterGerms.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle053
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle009
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenSpread

theorem gs_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {l : ℕ}
    (a : Fin l → Γ(X, U)) : gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem exists_defect_sum {O : Type} [CommRing O] {Y G H : Scheme.{0}} (m s : Y ⟶ G) (p : Y ⟶ H)
    (π : H ⟶ Spec (CommRingCat.of O)) (V : G.Opens) {l : ℕ} (c : Fin l → O) (t : Fin l → Γ(G, V))
    (u : Γ(H, ⊤)) : ∃ f : Γ(Y, m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V), ∀ (Z : Scheme.{0}) (g : Z ⟶ Y) (z : Z),
      g z ∈ m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V → gs g z (m ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V) f =
        ∑ i, constVal ((g ≫ p) ≫ π) z (c i) * gs (g ≫ m) z V (t i) -
          gs (g ≫ p) z ⊤ u * ∑ i, constVal ((g ≫ p) ≫ π) z (c i) * gs (g ≫ s) z V (t i) := by
  choose f hf using fun i => EigenAll.exists_defect m s p V (t i) u
  refine ⟨∑ i, resTop _ (scal (p ≫ π) (c i)) * f i, fun Z g z hz => ?_⟩
  rw [gs_sum g z _ hz, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul g z _ hz, FieldBaseChange.gs_const _ g z _ hz, hf i Z g z hz, Category.assoc]
  ring

end GlobalTheory.EigenSpread

namespace GlobalTheory

theorem fn_eigen_equation_of_forall_geometric_point :
    ∀ (V O F : Type) [CommRing V] [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (β : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G], Flat G.hom → ∀ (Z : Over (Spec (CommRingCat.of O))), IsFinite Z.hom → Flat Z.hom → IsReduced (Pdiv.specO O F ⊗ Z).left → ∀ (jZ : Z.left ⟶ G.left), jZ ≫ G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom β) → ∀ (U : G.left.Opens) (l : ℕ) (c : Fin l → O) (s : Fin l → Γ(G.left, U)) (k : Γ(Z.left, ⊤)), (∀ (T : Over (Spec (CommRingCat.of V))) (e : T.left ⟶ Spec (CommRingCat.of F)) (c₀ : Pdiv.specO O F ⟶ Z) (r g : T ⟶ G), g.left = (e ≫ c₀.left) ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal e z (algebraMap O F (c i)) * gs (r * g).left z U (s i) = gs (e ≫ c₀.left) z ⊤ k * ∑ i, constVal e z (algebraMap O F (c i)) * gs r.left z U (s i)) → ∀ (T : Over (Spec (CommRingCat.of V))) (q : T.left ⟶ Z.left) (r g : T ⟶ G), g.left = q ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal (q ≫ Z.hom) z (c i) * gs (r * g).left z U (s i) = gs q z ⊤ k * ∑ i, constVal (q ≫ Z.hom) z (c i) * gs r.left z U (s i) := by
  intro V O F _ _ _ _ _ hinj β G _ hG Z hfin hflat hred jZ hj U l c s k hyp
  let Y : Over (Spec (CommRingCat.of O)) :=
    Over.mk (pullback.snd G.hom (Spec.map (CommRingCat.ofHom β)))
  have hY : Flat Y.hom := inferInstanceAs (Flat (pullback.snd G.hom (Spec.map (CommRingCat.ofHom β))))
  let p : (Z ⊗ Y).left ⟶ Z.left := pullback.fst Z.hom Y.hom
  let PV : Over (Spec (CommRingCat.of V)) := Over.mk (p ≫ Z.hom ≫ Spec.map (CommRingCat.ofHom β))
  let r₀ : PV ⟶ G := Over.homMk (pullback.snd Z.hom Y.hom ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom β))) (by
    change _ = pullback.fst Z.hom Y.hom ≫ Z.hom ≫ _
    rw [Category.assoc, pullback.condition, pullback.condition_assoc]
    rfl)
  let g₀ : PV ⟶ G := Over.homMk (p ≫ jZ) (by
    change _ = p ≫ Z.hom ≫ _
    rw [Category.assoc, hj])
  obtain ⟨f, hf⟩ := EigenSpread.exists_defect_sum (Y := (Z ⊗ Y).left) (r₀ * g₀).left r₀.left p Z.hom U c s k
  have h0 : f = 0 := by
    refine section_eq_zero_of_forall_geometric_point O F hinj Z Y hfin hflat hred hY _ f fun c₀ => ?_
    refine fn_ext fun x hx => ?_
    rw [EigenAll.gs_zero, gs_pull (𝟙 _) (c₀ ▷ Y).left x _ hx, Category.id_comp, hf _ _ x hx, sub_eq_zero]
    let ρ : Over.mk ((c₀ ▷ Y).left ≫ PV.hom) ⟶ PV := Over.homMk (c₀ ▷ Y).left rfl
    let e : (Pdiv.specO O F ⊗ Y).left ⟶ Spec (CommRingCat.of F) := pullback.fst (Pdiv.specO O F).hom Y.hom
    have e₁ : (c₀ ▷ Y).left ≫ p = e ≫ c₀.left := Over.whiskerRight_left_fst c₀
    have e₂ : (e ≫ c₀.left) ≫ Z.hom = e ≫ Spec.map (CommRingCat.ofHom (algebraMap O F)) := by
      rw [Category.assoc, Over.w c₀]
      rfl
    have e₃ : (ρ ≫ r₀ * ρ ≫ g₀).left = (c₀ ▷ Y).left ≫ (r₀ * g₀).left := by
      rw [← MonObj.comp_mul]
      rfl
    have := hyp _ e c₀ (ρ ≫ r₀) (ρ ≫ g₀) (by rw [← e₁, Category.assoc]; rfl) x hx.2 (by rw [e₃]; exact hx.1)
    rw [e₃] at this
    rw [e₁, e₂]
    simp only [FieldBaseChange.constVal_specMap]
    exact this
  intro T q r g hg z hr hrg
  have hT : T.hom = q ≫ Z.hom ≫ Spec.map (CommRingCat.ofHom β) := by
    rw [← Over.w g, hg, Category.assoc, hj]
  let a : T.left ⟶ (Z ⊗ Y).left := pullback.lift q
    (pullback.lift r.left (q ≫ Z.hom) (by rw [Over.w r, hT, Category.assoc]))
    (pullback.lift_snd _ _ _).symm
  have e₁ : a ≫ p = q := pullback.lift_fst _ _ _
  let ρ : T ⟶ PV := Over.homMk a (by
    change a ≫ p ≫ _ = _
    rw [← Category.assoc, e₁, hT])
  have e₂ : a ≫ r₀.left = r.left := by
    change a ≫ pullback.snd Z.hom Y.hom ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom β)) = _
    rw [← Category.assoc, pullback.lift_snd, pullback.lift_fst]
  have e₃ : ρ ≫ r₀ = r := Over.OverMorphism.ext e₂
  have e₄ : ρ ≫ g₀ = g := Over.OverMorphism.ext (by
    change a ≫ p ≫ jZ = _
    rw [← Category.assoc, e₁, hg])
  have e₅ : a ≫ (r₀ * g₀).left = (r * g).left := by
    rw [← e₃, ← e₄, ← MonObj.comp_mul]
    rfl
  rw [← e₅] at hrg
  rw [← e₂] at hr
  have := hf _ a z ⟨hrg, hr⟩
  rw [h0, EigenAll.gs_zero, e₁, e₂, e₅] at this
  exact sub_eq_zero.1 this.symm

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.decayThresholds_of_spectralGapCondition : ∀ (k r : ℕ) (h : ℝ), GapOK k r h → JF.TransportedAlt k r (aOf r h - 1) 0 ∧ B.AB k r ≤ aOf r h - 1 ∧ AG k r < (aOf r h - 1) / 2 ∧ 0 < aOf r h - 1 := by
  first | exact @GlobalTheory.thresholds_of_gapOK | exact GlobalTheory.thresholds_of_gapOK | (intros; apply GlobalTheory.thresholds_of_gapOK <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exp_mem_unipotent_and_hasDerivAt_character : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r), Formalism.QuantumDeterminants.inWb k r z → PI.UpqRep.InLieHpk k r X → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → X i j = 0) → (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.Nset k r) ∧ HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X))) (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) 0 := by
  first | exact @GlobalTheory.UnipotentExp.exp_mem_and_deriv | exact GlobalTheory.UnipotentExp.exp_mem_and_deriv | (intros; apply GlobalTheory.UnipotentExp.exp_mem_and_deriv <;> assumption)
end

section

open Formalism.IncomingBounds

namespace GlobalTheory.FlowProgrammeFacts

variable {l d : ℕ} [NeZero d]

lemma succ_mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ}
    (hx : IsFlow l d D x) : ((l : ℝ) + 1) * flowVal d x ≤ ∑ a, D a := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) * flowVal d x ≤ ∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
    unfold flowVal
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd (Finset.mem_filter.1 hi).2 (by decide)
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)
  have h2 : ∑ a : ZMod d, ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i = flowVal d x := by
    unfold flowVal
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)
  have h3 := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hx.2 a
  rw [Finset.sum_add_distrib, h2] at h3
  linarith

lemma rho_mul_le_Fnum (hl : 2 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    Formalism.IncomingBounds.rho l * ∑ a, D a ≤ Fnum l d D := by
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hp : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hm : maxFlow l d D ≤ (∑ a, D a) / ((l : ℝ) + 1) :=
    GlobalTheory.FlowScaling.maxFlow_le hD fun x hx => by
      rw [le_div_iff₀ hp, mul_comm]
      exact succ_mul_flowVal_le (by omega) hx
  have hq : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have e : Formalism.IncomingBounds.gam l * ∑ a, D a - (∑ a, D a) / ((l : ℝ) + 1)
      = Formalism.IncomingBounds.rho l * ∑ a, D a := by
    unfold Formalism.IncomingBounds.gam Formalism.IncomingBounds.rho
    field_simp
    ring
  unfold Fnum
  linarith

theorem main : ∀ (l d : ℕ) [NeZero d] (D : ZMod d → ℝ), 2 ≤ l → (∀ a, 0 ≤ D a) →
    Formalism.IncomingBounds.rho l * ∑ a, D a ≤ Fnum l d D ∧
    (∀ t : ℝ, 0 ≤ t → Fnum l d (fun a => t * D a) = t * Fnum l d D) ∧
    Formalism.BasicNotions.lpF l d D = Fnum l d D ∧
    ∀ i₀ : ℕ, ∃ x : ZMod d → ℕ → ℝ, IsFlow l d D x ∧ (∀ a i, i₀ ≤ i → x a i = 0) ∧
      Formalism.IncomingBounds.gam l * ∑ a, D a - flowVal d x ≤
        Fnum l d D + ((l : ℝ) ^ i₀)⁻¹ * ∑ a, D a := by
  intro l d _ D hl hD
  refine ⟨rho_mul_le_Fnum hl hD, fun t ht => ?_, GlobalTheory.LevelsOrbits.lpF_eq l d D, fun i₀ => ?_⟩
  · unfold Fnum
    rw [GlobalTheory.FlowScaling.maxFlow_mul (by omega) ht hD, ← Finset.mul_sum]
    ring
  · obtain ⟨x, ⟨hx, hx0⟩, hmax⟩ := GlobalTheory.BasicFlow.low_optimum l d hl D hD i₀
    have hm : maxFlow l d D ≤ flowVal d x + (∑ a, D a) / (l : ℝ) ^ i₀ :=
      GlobalTheory.FlowScaling.maxFlow_le hD fun z hz => by
        obtain ⟨z', h1, h2, h3⟩ := GlobalTheory.BasicFlow.truncate l d hl D i₀ z hz
        linarith [hmax z' h1 h2]
    refine ⟨x, hx, fun a i h => hx0 a i (Or.inl h), ?_⟩
    rw [div_eq_inv_mul] at hm
    unfold Fnum
    linarith

end GlobalTheory.FlowProgrammeFacts
end

section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.GoodPlan

theorem blockBd_le {l n m i y I S : ℕ} {x : ℝ} (hl : 5 ≤ l) (hn : 1 ≤ n)
    (hi : x ≠ 0 → i < I) (h1 : (n : ℝ) * y ≤ x) (h2 : x - n * y ≤ n * S) :
    blockBd l n m i y ≤ n * gam l * ((l : ℝ) ^ i * y) + n * gam l * y - x +
      (if x ≠ 0 then (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) else 0) +
      2 * (I : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y) := by
  have hL := GlobalTheory.OrbitPlan.logTerm_nonneg hl hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  by_cases hx : x = 0
  · have : (y : ℝ) = 0 := by nlinarith
    have hy : y = 0 := by exact_mod_cast this
    simp [blockBd, hy, hx]
  rw [if_pos hx]
  by_cases hy : y = 0
  · subst hy
    simp only [blockBd, if_true, Nat.cast_zero, mul_zero, sub_zero] at h2 ⊢
    linarith
  have hiI : (i : ℝ) + 1 ≤ I := by exact_mod_cast hi hx
  have hp : (1 : ℝ) ≤ (l : ℝ) ^ i := one_le_pow₀ (by linarith)
  have e : ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1) ≤
      2 * (I : ℝ) * m / ((l : ℝ) - 1) * ((l : ℝ) ^ i * y) := by
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (by linarith)
    have : ((i : ℝ) + 1) * ((l : ℝ) ^ i + 1) ≤ I * (2 * (l : ℝ) ^ i) :=
      mul_le_mul hiI (by linarith) (by positivity) (by positivity)
    have hmy : (0 : ℝ) ≤ m * y := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this hmy]
  simp only [blockBd, bdP, hy, if_false]
  linarith

theorem exists_plan : ∀ (l d : ℕ) [NeZero d], 5 ≤ l → ∀ (n m k S : ℕ), 1 ≤ n → 1 ≤ k → ∀ (W : ZMod d → ℕ) (Ws : ZMod d → ℝ) (Good : ZMod d → ℕ → Set ℕ),
  (∀ a, 0 ≤ Ws a ∧ Ws a ≤ W a) → (∀ a, ∀ i ∈ oddLevels d, i < i0 k l → Windows S (Good a i)) →
  ∃ p : Plan l d W, (∀ a i, i0 k l ≤ i → p.y a i = 0) ∧ (∀ a i, p.y a i ≠ 0 → p.y a i ∈ Good a i) ∧
    p.bound n m ≤ Fnum l d (fun a => (n : ℝ) * Ws a) + thl k l * n * (∑ a, Ws a) + n * gam l * (∑ a, ((W a : ℝ) - Ws a)) +
      m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) + 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) + d * (i0 k l : ℝ) * (n * ((S : ℝ) + Real.logb l n + 1)) := by
  intro l d _ hl n m k S hn hk W Ws Good hW hG
  classical
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hW0 : (0 : ZMod d → ℝ) ≤ fun a => (n : ℝ) * Ws a := fun a => mul_nonneg hn0.le (hW a).1
  obtain ⟨ys, hflow, hsupp, hcard, hval⟩ :=
    GlobalTheory.BasicFlow.dropLevelsBasic l d (by omega) (fun a => (n : ℝ) * Ws a) hW0 (i0 k l)
  obtain ⟨-, h3, -, hthl⟩ := GlobalTheory.LevelsOrbits.thlEq k l hk (by omega)
  have hex : ∀ a i, ∃ y : ℕ, (y ≠ 0 → y ∈ Good a i) ∧ (n : ℝ) * y ≤ ys a i ∧
      ys a i - n * y ≤ n * (S : ℝ) := by
    intro a i
    by_cases hc : i ∈ oddLevels d ∧ i < i0 k l
    · obtain ⟨y, hy, h1, h2⟩ := GlobalTheory.OrbitPlan.exists_good (hG a i hc.1 hc.2)
        (div_nonneg (hflow.1 a i) hn0.le)
      rw [le_div_iff₀ hn0] at h1
      rw [sub_le_iff_le_add, div_le_iff₀ hn0] at h2
      exact ⟨y, fun _ => hy, by linarith, by linarith⟩
    · have : ys a i = 0 := hsupp a i (by
        by_cases h : i ∈ oddLevels d
        · left; by_contra h'; exact hc ⟨h, by omega⟩
        · right; exact h)
      refine ⟨0, fun h => absurd rfl h, by simp [this], ?_⟩
      simp only [this, Nat.cast_zero, mul_zero, sub_zero]; positivity
  choose y hyG hyle hyge using hex
  have hy0 : ∀ a i, ys a i = 0 → y a i = 0 := by
    intro a i h
    have h1 := hyle a i
    rw [h] at h1
    have h2 : (0 : ℝ) ≤ y a i := Nat.cast_nonneg _
    have : (y a i : ℝ) = 0 := by nlinarith
    exact_mod_cast this
  have hleR : ∀ a, (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ Ws a := by
    intro a
    refine le_of_mul_le_mul_left (le_trans ?_ (hflow.2 a)) hn0
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => hyle _ i)
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hyle a i) (by positivity)
  have hle : ∀ a, (∑ i ∈ oddLevels d, l ^ i * y a i) +
      (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) ≤ W a := by
    intro a
    exact_mod_cast (hleR a).trans (hW a).2
  let p : Plan l d W :=
    { y := y
      u := fun a => W a - ((∑ i ∈ oddLevels d, l ^ i * y a i) +
        (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i))
      supp := fun a i hi => hy0 a i (hsupp a i (Or.inr hi))
      bal := fun a => by have := hle a; omega }
  refine ⟨p, fun a i hi => hy0 a i (hsupp a i (Or.inl hi)), hyG, ?_⟩
  have hbal : ∀ a, (W a : ℝ) = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + (p.u a : ℝ) := by
    intro a
    have := p.bal a
    exact_mod_cast this
  set L : ℝ := (n : ℝ) * ((S : ℝ) + Real.logb l n + 1) with hL
  have hL0 : 0 ≤ L := by
    have := GlobalTheory.OrbitPlan.logTerm_nonneg hl hn
    have : (0 : ℝ) ≤ n * S := by positivity
    rw [hL]; linarith
  have hshift : (∑ a, ∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) =
      ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ) := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a i => (y a i : ℝ))]
    exact Finset.sum_congr rfl fun i _ =>
      Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => (y a i : ℝ))
  set A : ℝ := ∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i with hA
  set B : ℝ := ∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ) with hB
  set U : ℝ := ∑ a, (p.u a : ℝ) with hU
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hsum : (∑ a, (W a : ℝ)) = A + B + U := by
    rw [Finset.sum_congr rfl fun a _ => hbal a, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hshift]
  have hAB : A + B ≤ ∑ a, Ws a := by
    have := Finset.sum_le_sum (s := Finset.univ) fun a _ => hleR a
    rwa [Finset.sum_add_distrib, hshift] at this
  have e1 : (∑ a, ∑ i ∈ oddLevels d, (if ys a i ≠ 0 then L else 0)) ≤ d * (i0 k l : ℝ) * L := by
    rw [← Finset.sum_product' (f := fun a i => if ys a i ≠ 0 then L else 0), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hL0
    exact_mod_cast hcard.trans (Nat.le_mul_of_pos_right _ (by omega))
  set c : ℝ := 2 * (i0 k l : ℝ) * m / ((l : ℝ) - 1) with hc
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hc0 : 0 ≤ c := by positivity
  have e2 : (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) ≤
      n * gam l * A + n * gam l * B - flowVal d ys +
        (∑ a, ∑ i ∈ oddLevels d, (if ys a i ≠ 0 then L else 0)) + c * A := by
    refine le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ =>
      blockBd_le (I := i0 k l) (m := m) hl hn
        (fun h => by by_contra h'; exact h (hsupp a i (Or.inl (by omega))))
        (hyle a i) (hyge a i)) (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, flowVal]
    rfl
  have e3 : (∑ a, chBd l n m (p.u a)) = n * gam l * U + m / ((l : ℝ) - 1) * U := by
    simp only [chBd, ← Finset.sum_mul]; ring
  have e4 : m / ((l : ℝ) - 1) * U ≤ m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e5 : c * A ≤ 2 * (i0 k l : ℝ) * m * (∑ a, Ws a) / ((l : ℝ) - 1) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) hc0
  rw [← Finset.mul_sum, ← inv_mul_eq_div, ← hthl] at hval
  unfold Plan.bound Fnum
  rw [e3, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) + _ ≤ _
  rw [hsum] at e4 ⊢
  nlinarith

end GlobalTheory.GoodPlan
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem valuation_blockPoly_ge : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Ty : Type) [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) (β : (Σ τ : Ty, Fin (r τ)) → Fin n), Function.Injective β → ∀ (a : Ty → ℕ → ℕ), Crude.Dom r a → ∀ (yv : Letter Ty r n → O) (x : Ty → NNReal), (∀ τ, x τ ≤ 1) → (∀ τ (i : Fin (r τ)), x τ ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => yv ⟨τ, Fin.castLE i.isLt a, β ⟨τ, Fin.castLE i.isLt b⟩⟩).det)) → (∏ τ, x τ ^ (a τ 0) ≤ v (algebraMap O C (MvPolynomial.eval yv (Crude.crP r n O β a)))) ∧ ∀ mo ∈ (Crude.crP r n O β a).support, ∀ ℓ, mo ℓ ≠ 0 → ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2 := by
  intro C _ v O _ _ _ Ty _ _ r n β _ a ha yv x hx hmin
  refine ⟨?_, fun mo hmo ℓ hℓ => ?_⟩
  · unfold Crude.crP
    rw [map_prod, map_prod, map_prod]
    refine Finset.prod_le_prod' fun τ _ => ?_
    rw [map_prod, map_prod, map_prod]
    have h1 : x τ ^ (a τ 0) ≤ ∏ kk : Fin (r τ), x τ ^ Crude.crExp r a τ kk := by
      rw [Finset.prod_pow_eq_pow_sum]
      refine pow_le_pow_of_le_one zero_le (hx τ) ?_
      rcases Nat.eq_zero_or_pos (r τ) with h0 | h0
      · haveI : IsEmpty (Fin (r τ)) := by rw [h0]; infer_instance
        simp
      · have := Crude.crExpSum a ha τ ⟨0, h0⟩
        simp only [Nat.zero_lt_succ, if_true] at this
        exact this.le
    refine h1.trans (Finset.prod_le_prod' fun kk _ => ?_)
    rw [map_pow, map_pow, map_pow]
    refine pow_le_pow_left₀ zero_le ?_ _
    have h2 : MvPolynomial.eval yv (Crude.crMinor r n O β τ kk).det =
        (Matrix.of fun a b : Fin (kk.val + 1) =>
          yv ⟨τ, Fin.castLE kk.isLt a, β ⟨τ, Fin.castLE kk.isLt b⟩⟩).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [Crude.crMinor, RingHom.mapMatrix_apply]
    rw [h2]
    exact hmin τ kk
  · exact MvPolynomial.mem_supported.1 (Crude.crP_mem_supported O β a)
      ((MvPolynomial.mem_vars_iff_mem_support ℓ).2 ⟨mo, hmo, Finsupp.mem_support_iff.2 hℓ⟩)

end GlobalTheory.CharDepth
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.levelCoverDatum_similitude_adjoint_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  first | exact @GlobalTheory.DatumCoverAdjoint.datum_adjoint | exact GlobalTheory.DatumCoverAdjoint.datum_adjoint | (intros; apply GlobalTheory.DatumCoverAdjoint.datum_adjoint <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem expandsG_bijective_of_dvr : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ σ' : U.SecGF F k, ∃! s : Fam D.toPre F k, U.ExpandsG F k σ' s) ∧ ∀ s : Fam D.toPre F k, ∃! σ' : U.SecGF F k, U.ExpandsG F k σ' s :=
  fun hL _ _ _ _ _ _ _ _ _ _ _ _ _ U F _ _ k hk =>
    FieldBaseChange.expandsG_bijective U.toUnifPre F hL.globalFns hk (U.expand k hk)

end GlobalTheory
end
