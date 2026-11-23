module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LatSumSB

open GlobalTheory.WeilM GlobalTheory.ThetaTrCont

theorem summable_sb_mul_decay : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∀ (a : κ → FiniteAdeleRing (𝓞 F) F), ∃ M : ℕ, ∀ c : κ → mixedEmbedding.mixedSpace F,
      Summable fun ξ : κ → F => ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + a i)‖ *
        ((1 + ‖((fun i => mixedEmbedding F (ξ i)) + c : κ → mixedEmbedding.mixedSpace F)‖) ^ M)⁻¹ := by
  intro F _ _ κ _ g hg a
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hK : IsCompact ((fun z => z - a) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := exists_nat_mul_integral_of_isCompact F hK
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, fun c => ?_⟩
  set M := Module.finrank ℤ (denomLattice F κ N) + 1
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine mul_eq_zero_of_left ?_ _
    rw [norm_eq_zero]
    by_contra h0
    apply hξ
    have hy : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ (fun z => z - a) '' tsupport g :=
      ⟨_, subset_tsupport _ h0, by funext i; simp⟩
    refine ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy'⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hKN _ hy i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy'
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_norm_bounded
      ((((summable_one_add_norm_inv (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj).mul_left
        ((1 + ‖c‖) ^ M)).mul_left B) fun ξ => ?_
    set z : κ → mixedEmbedding.mixedSpace F := fun i => mixedEmbedding F (ξ.1 i)
    have hz : ‖(j ξ : denomLattice F κ N)‖ = ‖z‖ := rfl
    simp only [Function.comp_apply, hz]
    have hpos1 : 0 < (1 + ‖z + c‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hpos2 : 0 < (1 + ‖z‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hw : ((1 + ‖z + c‖) ^ M)⁻¹ ≤ (1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos2, ← div_eq_inv_mul, div_le_iff₀ hpos1, ← mul_pow, mul_comm (1 + ‖c‖)]
      exact pow_le_pow_left₀ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)).le (one_add_norm_le z c) M
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (inv_nonneg.2 hpos1.le)]
    calc ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i) + a i)‖ * ((1 + ‖z + c‖) ^ M)⁻¹
        ≤ B * ((1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹) :=
          mul_le_mul (hB _) hw (inv_nonneg.2 hpos1.le) ((norm_nonneg _).trans (hB 0))
      _ = _ := rfl

end GlobalTheory.LatSumSB
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.ample_lineBundle_top_selfIntersection_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) → ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  first | exact @GlobalTheory.AmplePos.topSelf_pos | exact GlobalTheory.AmplePos.topSelf_pos | (intros; apply GlobalTheory.AmplePos.topSelf_pos <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.global_sections_polynomial_growth : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 0 ≤ C * (m + 1) ^ d := by
  first | exact @GlobalTheory.exists_hdim_twist_lbPow_zero_le | exact GlobalTheory.exists_hdim_twist_lbPow_zero_le | (intros; apply GlobalTheory.exists_hdim_twist_lbPow_zero_le <;> assumption)
end

section

set_option autoImplicit false

namespace GlobalTheory.HSShort.FormRatio

open MvPolynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Adelic GlobalTheory.Points GlobalTheory.Twist

theorem exists_forms_of_mem_closure {F K : Type} [Field F] [Field K] {N : ℕ} (φ : F →+* K) (c : Fin N → K) {r : K}
    (hr : r ∈ Subfield.closure (Set.range φ ∪ {r | ∃ i j, r = c i / c j})) :
    ∃ (d : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ eval₂ φ c Q ≠ 0 ∧
      r * eval₂ φ c Q = eval₂ φ c P := by
  have h0 : ∃ (d : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ eval₂ φ c Q ≠ 0 ∧
      0 * eval₂ φ c Q = eval₂ φ c P :=
    ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
  induction hr using Subfield.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨i, j, rfl⟩
    · exact ⟨0, C a, 1, isHomogeneous_C _ _, isHomogeneous_one _ _, by simp, by simp⟩
    · by_cases hj : c j = 0
      · rwa [hj, div_zero]
      · exact ⟨1, X i, X j, isHomogeneous_X _ _, isHomogeneous_X _ _, by simpa using hj, by simp [hj]⟩
  | one => exact ⟨0, 1, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    obtain ⟨e, P', Q', hP', hQ', h1', h2'⟩ := hy
    refine ⟨d + e, P * Q' + Q * P', Q * Q', (hP.mul hQ').add (hQ.mul hP'), hQ.mul hQ', ?_, ?_⟩
    · rw [eval₂_mul]; exact mul_ne_zero h1 h1'
    · rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h2, ← h2']; ring
  | neg x _ hx =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    exact ⟨d, -P, Q, hP.neg, hQ, h1, by rw [eval₂_neg, ← h2, neg_mul]⟩
  | inv x _ hx =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    by_cases hx0 : x = 0
    · rwa [hx0, inv_zero]
    · refine ⟨d, Q, P, hQ, hP, h2 ▸ mul_ne_zero hx0 h1, ?_⟩
      rw [← h2, inv_mul_cancel_left₀ hx0]
  | mul x y _ _ hx hy =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    obtain ⟨e, P', Q', hP', hQ', h1', h2'⟩ := hy
    refine ⟨d + e, P * P', Q * Q', hP.mul hP', hQ.mul hQ', ?_, ?_⟩
    · rw [eval₂_mul]; exact mul_ne_zero h1 h1'
    · rw [eval₂_mul, eval₂_mul, ← h2, ← h2']; ring

theorem eq_zero_of_valR_generic {Y : Scheme.{0}} [IsReduced Y] {η : Y} (hη : IsGenericPoint η Set.univ)
    {U : Y.Opens} (f : Γ(Y, U)) (h : valR (resPt η) U f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro y hy
  have h1 : ptOf (resPt η) ∈ Y.basicOpen f := by
    rw [ptOf_resPt]
    exact (hη.mem_open_set_iff (Y.basicOpen f).isOpen).2 ⟨y, trivial, hy⟩
  exact ((valR_ne_zero_iff _ (Y.basicOpen_le f h1) f).2 h1 h).elim

theorem exists_forms (F : Type) [Field F] (S : LinSys F) (hS : S.IsVariety) (_ : S.BasePointFree)
    (hb : S.Birational) (W : S.Y.Opens) (a : Γ(S.Y, W)) :
    ∃ (d : ℕ) (P Q : MvPolynomial (Fin S.N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ Q ∉ S.imageIdeal ∧
      (a ≠ 0 → P ∉ S.imageIdeal) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), ptOf x.1 ∈ W →
        valR x.1 W a * aeval (S.coords x.1) Q = aeval (S.coords x.1) P := by
  have := hS.isIntegral
  obtain ⟨η, hη, hr⟩ := hb
  obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := exists_forms_of_mem_closure (S.baseHom (resPt η)) (S.coords (resPt η))
    (r := valR (resPt η) W a) (hr.ge (Subfield.mem_top _))
  refine ⟨d, P, Q, hP, hQ, fun h => h1 (S.eval₂_coords_eq_zero _ h), fun ha h => ?_, fun K _ _ x hx => ?_⟩
  · rw [S.eval₂_coords_eq_zero _ h] at h2
    exact ha (eq_zero_of_valR_generic hη a ((mul_eq_zero.1 h2).resolve_right h1))
  · set j := S.chartAt (ptOf x.1)
    have hxV : ptOf x.1 ∈ W ⊓ S.L.U j := ⟨hx, S.mem_chartAt _⟩
    have hηV : ptOf (resPt η) ∈ W ⊓ S.L.U j := by
      rw [ptOf_resPt]
      exact (hη.mem_open_set_iff (W ⊓ S.L.U j).isOpen).2 ⟨_, trivial, hxV⟩
    let f : Γ(S.Y, W ⊓ S.L.U j) :=
      (S.Y.presheaf.map (homOfLE inf_le_left).op).hom a *
        (S.Y.presheaf.map (homOfLE inf_le_right).op).hom (zfun (S.form hQ) j) +
        -(S.Y.presheaf.map (homOfLE inf_le_right).op).hom (zfun (S.form hP) j)
    have hf : ∀ {Ω : Type} [Field Ω] (z : Sp Ω ⟶ S.Y), ptOf z ∈ W ⊓ S.L.U j → valR z _ f =
        valR z W a * valR z _ (zfun (S.form hQ) j) - valR z _ (zfun (S.form hP) j) := fun z hz => by
      have h := (le_iff_ptOf_mem z _).2 hz
      rw [valR_add z _ h, valR_neg z _ h, valR_mul z _ h, valR_res z _ h, valR_res z _ h, valR_res z _ h,
        sub_eq_add_neg]
    have hf0 : f = 0 := by
      obtain ⟨c, -, -, hc⟩ := S.exists_frame_change (resPt η) j hηV.2
      refine eq_zero_of_valR_generic hη f ?_
      rw [hf _ hηV, hc, hc, S.powVal_form, S.powVal_form, ← h2]
      ring
    have h3 := hf x.1 hxV
    rw [hf0, valR_zero _ _ ((le_iff_ptOf_mem _ _).2 hxV), eq_comm, sub_eq_zero] at h3
    have e : ∀ {g : MvPolynomial (Fin S.N) F} (hg : g.IsHomogeneous d),
        valR x.1 _ (zfun (S.form hg) j) = aeval (S.coords x.1) g := fun hg =>
      (S.powVal_form x.1 hg).trans (by rw [LinSys.baseHom_ptOver, aeval_def])
    rwa [e, e] at h3

end GlobalTheory.HSShort.FormRatio
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_smooth_lift_abelian_scheme_square_zero : FormSt → PrimitiveExtendedDegTwoVanish → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∃ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) ∧ Smooth X.hom := by
  first | exact @GlobalTheory.Obs.exists_smooth_lift_of_abelian | exact GlobalTheory.Obs.exists_smooth_lift_of_abelian | (intros; apply GlobalTheory.Obs.exists_smooth_lift_of_abelian <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic


theorem _root_.GlobalTheory.T.integrableOn_cartanDoubleCoset_shellIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) → ∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ := by
  first | exact @GlobalTheory.ShellInt.integrableOn_shell | exact GlobalTheory.ShellInt.integrableOn_shell | (intros; apply GlobalTheory.ShellInt.integrableOn_shell <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic


theorem _root_.GlobalTheory.T.cartanDoubleCoset_finite_disjoint_leftCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (a : ℕ) (n : Fin a → ℤ), ∃ t : Finset (GL (Fin a) k), (∀ x ∈ t, x ∈ KO k (Fin a)) ∧
      shellSet ϖ n = ⋃ x ∈ t, {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)} ∧
      (t : Set (GL (Fin a) k)).PairwiseDisjoint
        (fun x => {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)}) := by
  first | exact @GlobalTheory.ShellCosets.shell_cosets | exact GlobalTheory.ShellCosets.shell_cosets | (intros; apply GlobalTheory.ShellCosets.shell_cosets <;> assumption)
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.OrbReindex

theorem mem_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t : Aˣ)
    (L : Submodule O A) (y : A) :
    y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L := by
  unfold GlobalTheory.UnitLemma.mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [LinearMap.mulLeft_apply, Units.inv_mul_cancel_left] using hx
  · intro h
    exact ⟨_, h, by simp [LinearMap.mulLeft_apply, Units.mul_inv_cancel_left]⟩

theorem stabLat_mulLat_unit {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (t : Aˣ)
    (L : Submodule O A) :
    GlobalTheory.UnitLemma.stabLat O (GlobalTheory.UnitLemma.mulLat O (t : A) L) = GlobalTheory.UnitLemma.stabLat O L := by
  ext s
  change (∀ y, y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L ↔ (s : A) * y ∈ GlobalTheory.UnitLemma.mulLat O (t : A) L) ↔
    (∀ y, y ∈ L ↔ (s : A) * y ∈ L)
  simp only [mem_mulLat_unit]
  constructor
  · intro h y
    have e : ((t⁻¹ : Aˣ) : A) * ((s : A) * ((t : A) * y)) = (s : A) * y := by
      rw [mul_left_comm, Units.inv_mul_cancel_left]
    have := h ((t : A) * y)
    rwa [Units.inv_mul_cancel_left, e] at this
  · intro h y
    rw [h (((t⁻¹ : Aˣ) : A) * y), mul_left_comm]

theorem cast_finsum_rat {α : Type*} (u : α → ℚ) : ((∑ᶠ a, u a : ℚ) : ℂ) = ∑ᶠ a, ((u a : ℚ) : ℂ) := by
  by_cases h : (Function.support u).Finite
  · simpa using map_finsum (Rat.castHom ℂ) h
  · have h' : ¬ (Function.support (fun a => ((u a : ℚ) : ℂ))).Finite := by
      have : Function.support (fun a => ((u a : ℚ) : ℂ)) = Function.support u := by
        ext a; simp
      rwa [this]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

end GlobalTheory.OrbReindex

namespace GlobalTheory.OrbReindex
open GlobalTheory.UnitLemma

theorem finsum_ite_subtype {α : Type*} (p : α → Prop) (c : α → ℂ) :
    (∑ᶠ q, if p q then c q else 0) = ∑ᶠ s : {q // p q}, c s.1 := by
  rw [finsum_subtype_eq_finsum_cond]
  simp only [finsum_eq_if]

theorem twOrb_eq_orbSum : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) (f : G → ℂ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (X : Set (Submodule O A)) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ L ∈ X, ∃ g, M g = L) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ g : G, avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) = if M g ∈ X then 1 else 0) → (∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb)) → twOrb (MonoidHom.id G) Kg δ f = ((GlobalTheory.UnitLemma.orbSum O Tb X fun _ => 1 : ℚ) : ℂ) := by
  intro G _ _ Kg δ f O A _ _ _ Tb X M τ hK hinj hsurj hT hTs havg hidx

  have hX : ∀ h ∈ twCent (MonoidHom.id G) δ, ∀ g : G, (M (h * g) ∈ X ↔ M g ∈ X) := by
    intro h hh g
    have hc : h * δ = δ * h := hh
    have hc' : h⁻¹ * δ * h = δ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    have e : avg (fun k : Kg => f ((h * g * k)⁻¹ * δ * (MonoidHom.id G) (h * g * k))) =
        avg (fun k : Kg => f ((g * k)⁻¹ * δ * (MonoidHom.id G) (g * k))) := by
      congr 1
      funext k
      congr 1
      simp only [MonoidHom.id_apply]
      calc (h * g * (k : G))⁻¹ * δ * (h * g * k) = (g * (k : G))⁻¹ * (h⁻¹ * δ * h) * (g * k) := by group
        _ = _ := by rw [hc']
    have := (havg (h * g)).symm.trans (e.trans (havg g))
    by_cases a : M (h * g) ∈ X <;> by_cases b : M g ∈ X <;> simp_all
  let r : X → X → Prop := fun L L' => ∃ t ∈ Tb, (L' : Submodule O A) = mulLat O (t : A) (L : Submodule O A)
  have hw : ∀ L L' : X, Relation.EqvGen r L L' → stabLat O L.1 = stabLat O L'.1 := by
    intro L L' h
    induction h with
    | rel a b hab =>
      obtain ⟨t, -, ht⟩ := hab
      rw [ht, stabLat_mulLat_unit]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  let φ : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} → Orb O Tb X := fun q => Quot.mk r ⟨M (Quotient.out q.1), q.2⟩
  let ψ : Orb O Tb X → DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) :=
    Quot.lift (fun L : X => DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj L.1 L.2))) (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨t, ht, hLL⟩
      obtain ⟨h, hh, rfl⟩ := hTs t ht
      have hg := Classical.choose_spec (hsurj L hL)
      have hg' := Classical.choose_spec (hsurj L' hL')
      set g := Classical.choose (hsurj L hL)
      set g' := Classical.choose (hsurj L' hL')
      have hMM : M (h * g) = M g' := by
        rw [(hT h hh).2, hg, hg']
        exact hLL.symm
      have hk := hinj _ _ hMM
      show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g = DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g'
      rw [DoubleCoset.eq]
      exact ⟨h, hh, _, hk, by group⟩)
  have hleft : ∀ q : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, ψ (φ q) = q.1 := by
    intro q
    show DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg (Classical.choose (hsurj (M (Quotient.out q.1)) q.2)) = q.1
    have hg := Classical.choose_spec (hsurj (M (Quotient.out q.1)) q.2)
    set g := Classical.choose (hsurj (M (Quotient.out q.1)) q.2)
    have hk := hinj _ _ hg.symm
    rw [← DoubleCoset.out_eq' q.1, DoubleCoset.eq]
    exact ⟨1, (twCent (MonoidHom.id G) δ).one_mem, _, Kg.inv_mem hk, by group⟩
  have hinjφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    rw [← hleft a, ← hleft b, hab]
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨L, hL⟩
    obtain ⟨g, rfl⟩ := hsurj L hL
    obtain ⟨h, hh, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id G) δ) Kg g
    have hM : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) = mulLat O (τ h : A) (M g) := by
      rw [hout, hK _ _ hk, (hT h hh).2]
    have hmem : M (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g)) ∈ X := by
      rw [hout, hK _ _ hk, hX h hh]
      exact hL
    refine ⟨⟨DoubleCoset.mk (twCent (MonoidHom.id G) δ) Kg g, hmem⟩, ?_⟩
    exact (Quot.sound ⟨τ h, (hT h hh).1, hM⟩).symm
  let e : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X} ≃ Orb O Tb X := Equiv.ofBijective φ ⟨hinjφ, hsurjφ⟩

  have hwt : ∀ s : {q : DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (Kg : Set G) // M (Quotient.out q) ∈ X}, stabLat O (Quot.out (e s)).1 = stabLat O (M (Quotient.out s.1)) := by
    intro s
    have h1 : Quot.mk r (Quot.out (φ s)) = φ s := Quot.out_eq _
    exact hw _ _ (Quot.eqvGen_exact h1)
  unfold twOrb orbSum
  simp only [havg, hidx]
  rw [cast_finsum_rat, ← finsum_comp_equiv e]
  simp only [hwt, one_mul, mul_ite, mul_one, mul_zero]
  simp only [Rat.cast_natCast]
  exact finsum_ite_subtype _ _

end GlobalTheory.OrbReindex
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.charpoly_coeff_det_inv_valuation_bounded_of_isCompact_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ γ : WithZero (Multiplicative ℤ), ∀ y ∈ C, (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ γ := by
  first | exact @GlobalTheory.BCT.charpoly_det_bounded_of_isCompact | exact GlobalTheory.BCT.charpoly_det_bounded_of_isCompact | (intros; apply GlobalTheory.BCT.charpoly_det_bounded_of_isCompact <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.absHalf_conjugatePlace_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ x : E, absHalf u (algebraMap E (u.adicCompletion E) x) = absHalf w (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) := by
  first | exact @GlobalTheory.BCT.AbsHalfConj.absHalf_conjPl | exact GlobalTheory.BCT.AbsHalfConj.absHalf_conjPl | (intros; apply GlobalTheory.BCT.AbsHalfConj.absHalf_conjPl <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  first | exact @GlobalTheory.ConjSelfRecip.ell_coeff_conj | exact GlobalTheory.ConjSelfRecip.ell_coeff_conj | (intros; apply GlobalTheory.ConjSelfRecip.ell_coeff_conj <;> assumption)
end

section

open Filter GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.mem_compactPart_centralizer_iff_local : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (KH : ∀ i, Subgroup (H i)) (T : Subgroup G) (TH : ∀ i, Subgroup (H i)), (∀ i, Continuous (p i)) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ a ∈ TH i, ∀ b ∈ TH i, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ x ∈ T ∧ ∀ i, p i x ∈ cptPart (TH i) := by
  first | exact @GlobalTheory.BCT.mem_cptPart_iff_local | exact GlobalTheory.BCT.mem_cptPart_iff_local | (intros; apply GlobalTheory.BCT.mem_cptPart_iff_local <;> assumption)
end
