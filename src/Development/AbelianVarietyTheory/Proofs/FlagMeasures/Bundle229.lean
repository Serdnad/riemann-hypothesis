module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LeadMinorEMulUpper
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle227
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Counterexamples.TransversalityLocal.FramePairFixatorUnitaryAndFixesFrame
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JordanExponentsMaximalHermitianLatticeBadPrime
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermIntegralNearOneBound
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007

@[expose] public section

section

universe u_1

namespace GlobalTheory.LowerUnipotentMul

open Matrix

theorem isLoUni_mul {R : Type*} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (hl : Formalism.MainNotions.S.IsLoUni l) (hl' : Formalism.MainNotions.S.IsLoUni l') : Formalism.MainNotions.S.IsLoUni (l * l') := by
  apply PI.TermAttrConst.UnitaryGroupMassFormula.isLoUni_mul <;> assumption

theorem main : ∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R},
    Formalism.MainNotions.S.IsLoUni l → Formalism.MainNotions.S.IsLoUni l' → Formalism.MainNotions.S.IsLoUni (l * l') :=
  fun hl hl' => isLoUni_mul hl hl'

end GlobalTheory.LowerUnipotentMul
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.families_have_largeGap_of_numericalHypotheses : (∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → IsFamG lam q0 R) ∧ ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg ↔ SetupG lam u b bv ga h q0 z π μW μN μG νq R lb dg := by
  first | exact @GlobalTheory.GapSetup.families_gap | exact GlobalTheory.GapSetup.families_gap | (intros; apply GlobalTheory.GapSetup.families_gap <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec

namespace GlobalTheory.AutBall

theorem pow_bound (s t R : ℝ) (m f : ℕ) (hs : 1 ≤ s) (ht : 0 < t) (ht1 : t ≤ 1 / 2) (hR : 0 ≤ R) (hf : 0 < f) :
    (1 + 2 * s * Real.exp (R / f) / (t * t)) ^ (2 * (m * f)) ≤
      (3 * s / t ^ 2) ^ (2 * (m * f)) * Real.exp (2 * (m : ℝ) * R) := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hE : 1 ≤ Real.exp (R / f) := Real.one_le_exp (div_nonneg hR hf'.le)
  have htt : 0 < t * t := mul_pos ht ht
  have h1 : 1 ≤ s * Real.exp (R / f) / (t * t) := by
    rw [le_div_iff₀ htt]; nlinarith
  have h2 : 1 + 2 * s * Real.exp (R / f) / (t * t) ≤ 3 * s / t ^ 2 * Real.exp (R / f) := by
    have e1 : 2 * s * Real.exp (R / f) / (t * t) = 2 * (s * Real.exp (R / f) / (t * t)) := by ring
    have e2 : 3 * s / t ^ 2 * Real.exp (R / f) = 3 * (s * Real.exp (R / f) / (t * t)) := by ring
    rw [e1, e2]; linarith
  have h3 : Real.exp (2 * (m : ℝ) * R) = Real.exp (R / f) ^ (2 * (m * f)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [h3, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h2 _

theorem autBallCount : GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.AutBallCount := by
  intro I hn x r hr
  obtain ⟨hfin, hle⟩ := GlobalTheory.RationalCount.count_le I x x r hn hr
  have hsub : GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.ballSet I x r ⊆
      {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * x).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * x).1 v)) ≤ r v} := by
    rintro a ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun v => le_trans ?_ (h3 v)⟩
    obtain ⟨h0, -, -, h4, -⟩ :=
      (GlobalTheory.Count.Cartan.cartan_distances I.n (I.ε v)).2.1 ((x⁻¹ * a * x).1 v) ((x⁻¹ * a * x).1 v) hn
    have h5 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    exact (le_mul_of_one_le_left h0 h5).trans h4
  refine ⟨hfin.subset hsub, ?_⟩
  have hc := Set.ncard_le_ncard hsub hfin
  have hf : 0 < I.f := Module.finrank_pos (R := ℚ) (M := I.F)
  have hs : 1 ≤ Real.sqrt (I.n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hb := pow_bound (Real.sqrt (I.n : ℝ)) (tau1 I x) (∑ v, r v) (I.n ^ 2) I.f hs
    (GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x) (min_le_left _ _) (Finset.sum_nonneg fun v _ => hr v) hf
  refine (Nat.cast_le.mpr hc).trans (hle.trans (hb.trans (le_of_eq ?_)))
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.bigA
  push_cast
  rfl

end GlobalTheory.AutBall
end

section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.torus_normaliser_bessel : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (c : ℂ) (μW μN μG νq : Measure (Mt k r)) (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), t ∈ GG k r → (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) → (∀ h ∈ UWset k r z, t * h = h * t) → (∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) → SideG k r z π u μW μN μG νq → SideG k r z π u μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) μG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) ∧ ∀ (R : Rep k r), Formalism.MainNotions.S.IsURepOn (GG k r) R.σ → (∀ B : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B ↔ IsBes R z π (fun v => B (R.σ t v))) ∧ ∀ l₁ : R.H → Wp, IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁ → ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  first | exact @GlobalTheory.BesselMove.bessel_move | exact GlobalTheory.BesselMove.bessel_move | (intros; apply GlobalTheory.BesselMove.bessel_move <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, cmp l s *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) = (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) ∧ ∀ g ∈ GG k r, ∑ J, ‖(cmp l g⁻¹ *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) J‖ ^ 2 = ∏ a : Fin l, lenA k r z g (Fin.castLE hl a) ^ 2 := by
  first | exact @GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length | exact GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length | (intros; apply GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.cwCont_integral_comm_alt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (κ : X → Mx k r) (p : X → ℂ), Continuous κ → (∀ x, κ x ∈ GG k r) → Continuous p → ∀ v ∈ R.sm, (∫ x, p x • R.σ (κ x) v ∂μ) ∈ R.sm → Bm (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, p x • Bm (R.σ (κ x) v) ∂μ := by
  first | exact @GlobalTheory.cwCont_integral_comm | exact GlobalTheory.cwCont_integral_comm | (intros; apply GlobalTheory.cwCont_integral_comm <;> assumption)
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.exists_irr_pairs_char_prod_eq_sum : ∀ (G₁ G₂ : Type) [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] (Φ : G₁ × G₂ → ℂ), IsChar Φ → ∃ L : List ((G₁ → ℂ) × (G₂ → ℂ)), (∀ p ∈ L, IsIrr p.1 ∧ IsIrr p.2) ∧ ∀ x y, Φ (x, y) = (L.map fun p => p.1 x * p.2 y).sum := by
  first | exact @GlobalTheory.GLm.ProdChar.exists_list_prod | exact GlobalTheory.GLm.ProdChar.exists_list_prod | (intros; apply GlobalTheory.GLm.ProdChar.exists_list_prod <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.MoveTerm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) : x ∈ img g Λ ↔ g.symm x ∈ Λ := by
  unfold img
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g.symm x, h, by simp⟩

theorem map_mem_span_range {R : Type} [Semiring R] [Module R V] (φ : V →ₗ[R] V) {ι : Type} (v : ι → V)
    {x : V} (hx : x ∈ Submodule.span R (Set.range v)) :
    φ x ∈ Submodule.span R (Set.range fun a => φ (v a)) := by
  have := Submodule.apply_mem_span_image_of_mem_span φ hx
  rwa [← Set.range_comp] at this

variable (H : HermSp M V)

theorem h_symm {g : V ≃ₗ[E] V} (hg : IsUnitary H g) (x y : V) : H.h (g.symm x) (g.symm y) = H.h x y := by
  rw [← hg]; simp

theorem isSelfDual_img {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {Λ : Submodule M.L.O V}
    (h : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨hfg, hspan, hdual⟩ := h
  refine ⟨hfg.map _, ?_, fun x => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have h1 : g.symm x ∈ Submodule.span E (Λ : Set V) := by rw [hspan]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span (g : V →ₗ[E] V) h1
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_img g Λ _).2 (by simpa using hy)
  · rw [mem_img, hdual (g.symm x)]
    constructor
    · intro h y hy
      have := h _ ((mem_img g Λ y).1 hy)
      rwa [h_symm H hg] at this
    · intro h y hy
      have := h (g y) ((mem_img g Λ _).2 (by simpa using hy))
      rw [← hg (g.symm x) y, LinearEquiv.apply_symm_apply]; exact this

theorem prim_img (g : V ≃ₗ[E] V) {Λ : Submodule M.L.O V} {ι : Type} {v : ι → V}
    (h : H.Prim Λ v) : H.Prim (img g Λ) (fun a => g (v a)) := by
  obtain ⟨hmem, hli, hsat⟩ := h
  refine ⟨fun a => (mem_img g Λ _).2 (by simpa using hmem a), ?_, fun x hx hxs => ?_⟩
  · exact hli.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)
  · have h1 : g.symm x ∈ Submodule.span E (Set.range v) := by
      have := map_mem_span_range (g.symm : V →ₗ[E] V) _ hxs
      simpa using this
    have h2 := hsat _ ((mem_img g Λ x).1 hx) h1
    have h3 := map_mem_span_range ((g : V →ₗ[E] V).restrictScalars M.L.O) _ h2
    simpa using h3

theorem isFrame_img {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {Λ : Submodule M.L.O V} {r : ℕ}
    {f : Fin (r + 1) → V} {T : F} (h : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun a => g (f a)) T := by
  obtain ⟨hp, hiso, hz, hT, hT0⟩ := h
  refine ⟨prim_img H g hp, fun a b hab => ?_, ?_, hT, hT0⟩
  · rw [hg]; exact hiso a b hab
  · rw [hg]; exact hz

theorem smulLat_img (g : V ≃ₗ[E] V) (c : E) {Λ : Submodule M.L.O V} {y : V}
    (hy : y ∈ H.smulLat c Λ) : g y ∈ H.smulLat c (img g Λ) := by
  unfold HermSp.smulLat at hy ⊢
  have := Submodule.apply_mem_span_image_of_mem_span ((g : V →ₗ[E] V).restrictScalars M.L.O) hy
  refine Submodule.span_mono ?_ (by simpa using this)
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨g w, (mem_img g Λ _).2 (by simpa using hw), by simp⟩

theorem zhat_move {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Zhat (fun a => g (f a)) (fun b => g (f' b)) = H.Zhat f f' := by
  ext a b
  exact hg _ _

theorem isTerm_move {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r) (hg : IsUnitary H g) (ht : H.IsTerm t) :
    H.IsTerm (GlobalTheory.LocOver.move g t) := by
  obtain ⟨hSD, hF, hF', hU, hG, hsplit⟩ := ht
  have hD : ∀ l, H.Dl (GlobalTheory.LocOver.move g t).f (GlobalTheory.LocOver.move g t).f' l = H.Dl t.f t.f' l := by
    intro l
    unfold HermSp.Dl
    rw [show (GlobalTheory.LocOver.move g t).f = fun a => g (t.f a) from rfl,
      show (GlobalTheory.LocOver.move g t).f' = fun a => g (t.f' a) from rfl, zhat_move H hg]
  refine ⟨isSelfDual_img H hg hSD, isFrame_img H hg hF, isFrame_img H hg hF', ?_, ?_, fun gs hgs => ?_⟩
  · rw [hD]; exact hU
  · unfold HermSp.Gdet
    rw [hD, hD]
    exact hG
  · obtain ⟨h1, h2, h3⟩ := hsplit gs hgs
    refine ⟨h1, h2, fun b => ?_⟩
    show g (t.f' b) - g (t.f b) ∈ H.smulLat _ (img g t.abelian₂)
    rw [← map_sub]
    exact smulLat_img H g _ (h3 b)

end GlobalTheory.LocOver.MoveTerm

theorem GlobalTheory.LocOver.isTerm_move_of_unitary : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Term V M r), IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) :=
  fun H _ g t hg ht => GlobalTheory.LocOver.MoveTerm.isTerm_move H g t hg ht
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver

theorem orbit_reps_over : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V]
    [Module E V] (H : HermSp M V) (r : ℕ), ∀ P : FPair H r, Equivalence (Datum.Rel (P := P)) ∧ Nonempty (Reps P) ∧
    ∀ (d d' : Datum P) (t : Term V M r), Datum.Rel d d' → Over P d t → Over P d' t := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r P
  have he := GlobalTheory.NonGenericLocalCheck.rel_equiv P
  refine ⟨he, GlobalTheory.NonGenericLocalCheck.reps_nonempty P, ?_⟩
  rintro d d' t hdd' ⟨g, hg, d'', h1, h2⟩
  exact ⟨g, hg, d'', he.trans (he.symm hdd') h1, h2⟩

end GlobalTheory.LocOver
end

section

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

theorem _root_.GlobalTheory.T.jordan_exponents_maximal_hermitian_lattice_bad_prime : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ P ∈ badP h M, ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ M (P.comap (algebraMap (𝓞 F) (𝓞 K))) b a → ∃ i, vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a i) = 1 ∧ ∀ j, j ≠ i → vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a j) = 0 := by
  first | exact @GlobalTheory.MaxLatExpo.main | exact GlobalTheory.MaxLatExpo.main | (intros; apply GlobalTheory.MaxLatExpo.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFrames_reference_subgroups_relIndex_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  first | exact @GlobalTheory.RefVol.main | exact GlobalTheory.RefVol.main | (intros; apply GlobalTheory.RefVol.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.term_integral_near_one_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → |(cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u)).re * (S.q : ℝ) ^ S.a - 1| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ (cint (S.refU J Λ) (ind fun u => u ∈ S.refU J Λ ∧ S.InZ u ∧ ¬ S.NoLeak Λ u)).re * (S.q : ℝ) ^ S.a ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ∀ y : S.V, (∃ u ∈ S.refU J Λ, L.psi0 (S.h y u) ≠ 1) → ‖cint (S.refU J Λ) (fun u => ind (fun u => u ∈ S.refU J Λ ∧ S.InZ u) u * L.psi0 (S.h y u))‖ * (S.q : ℝ) ^ S.a ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.FibU.shares | exact GlobalTheory.HL.FibU.shares | (intros; apply GlobalTheory.HL.FibU.shares <;> assumption)
end
