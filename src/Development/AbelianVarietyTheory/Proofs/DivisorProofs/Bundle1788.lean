module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1754
import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ConjComb

theorem normSq_nonneg (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (La : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    0 ≤ TaylorLogMetric.normSq D T La G := by
  unfold TaylorLogMetric.normSq
  simp only [MeasureTheory.average_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 MeasureTheory.measureReal_nonneg) (MeasureTheory.integral_nonneg fun z => by positivity)

theorem supConst_nonneg (D : D7) (a b : ℕ) : 0 ≤ supConst D a b := by
  have h : 0 ≤ D.host.rdE := by
    exact Real.rpow_nonneg (by positivity) _
  unfold supConst
  positivity

theorem sq_sum_le {k : ℕ} (c f : Fin k → ℂ) (n B : ℝ) (hB : 0 ≤ B) (hc : ∑ i, ‖c i‖ ≤ n) (hf : ∀ i, ‖f i‖ ^ 2 ≤ B) :
    ‖∑ i, c i * f i‖ ^ 2 ≤ n ^ 2 * B := by
  have h1 : ‖∑ i, c i * f i‖ ≤ n * √B := by
    calc ‖∑ i, c i * f i‖ ≤ ∑ i, ‖c i * f i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * √B := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (hf i)) (norm_nonneg _)
      _ = (∑ i, ‖c i‖) * √B := (Finset.sum_mul _ _ _).symm
      _ ≤ n * √B := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
  calc ‖∑ i, c i * f i‖ ^ 2 ≤ (n * √B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = n ^ 2 * B := by rw [mul_pow, Real.sq_sqrt hB]

theorem conj_pres : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ (F₀ F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ), StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F₀ → Pres D (TaylorLogMetric.tor0 D cc dl) L L' F₀ F n → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ F ∧ TaylorLogMetric.CoefIn D F TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D F α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ n ^ 2 * (supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F₀) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl)))) := by
  intro D cc dl t0 hC ht a b L L' hL hL' hev F₀ F n hF₀ hP ρ
  obtain ⟨k, r, y, hr, hy, hn, rfl⟩ := hP
  have h := fun i => GlobalTheory.T.conj_torsion_translate_vacuum_entire_gaussian_growth D cc dl t0 hC ht a b L L' hL hL' hev F₀ hF₀ (y i) (hy i) ρ
  choose h1 h2 F' h3 h4 h5 using h
  have hc : GlobalTheory.ThetaConj.CjF D TaylorLogMetric.Qbar ρ (fun z => ∑ i, r i * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) (y i) F₀ z)
      (fun z => ∑ i, StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (r i) * F' i z) :=
    GlobalTheory.ThetaConj.CjF.sum Finset.univ fun i _ =>
      GlobalTheory.ThetaConj.CjF.mul ⟨h1 i, h3 i, fun α => ⟨h2 i α, h4 i α⟩⟩ (hr i)
  refine ⟨hc.1, fun α => (hc.2.2 α).1, _, hc.2.1, fun α => (hc.2.2 α).2, fun z => ?_⟩
  exact sq_sum_le _ _ n _
    (mul_nonneg (mul_nonneg (supConst_nonneg D a b) (normSq_nonneg _ _ _ _)) (Real.exp_pos _).le) (hn ρ) fun i => h5 i z

end GlobalTheory.ConjComb
end

section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem pairVr_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] (emb : ι → E →+* K) {n : ℕ}
    (lam : ι → DomWeight n) :
    pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) = pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) := by
  have e : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    rw [gramKd, Matrix.map_one _ (map_zero _) (map_one _), inv_one, Matrix.transpose_one]
  rw [← e]
  rfl

theorem gram_posSemidef_and_sqAt : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (emb : ι → E →+* K) (n : ℕ) (lam : ι → DomWeight n) (σ : K →+* ℂ), ((Matrix.of fun i j => pairVr emb lam 1 (bVV K lam i) (bVV K lam j)).map σ).PosSemidef ∧ ∀ x : Formalism.L2.DIV.VV K lam, (∑ i, ∑ j, starRingEnd ℂ ((InfinitePlace.mk σ).embedding ((bVV K lam).repr x i)) * (InfinitePlace.mk σ).embedding (pairVr emb lam 1 (bVV K lam i) (bVV K lam j)) * (InfinitePlace.mk σ).embedding ((bVV K lam).repr x j)).re = sqAt σ lam x := by
  intro E K _ _ _ _ _ ι _ emb n lam σ
  rw [pairVr_one_eq]
  refine ⟨?_, fun x => ?_⟩
  · simp only [GlobalTheory.PeriodClassSum.pairK_one_basis]
    exact (GlobalTheory.PeriodClassSum.gramB_posDef lam σ).posSemidef
  · unfold sqAt
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, ← Complex.conj_re]

      simp only [map_sum, map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

end GlobalTheory.ColNorms
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_ring_eventually : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (κ : Type) (b : Module.Basis κ ℚ A),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b 1 ∧
      ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (exact GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_mul_eventually  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem isIntB_one_mul_cofinite : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type) (b : Module.Basis κ ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      IsIntB v b 1 ∧ ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) :=
  isIntB_one_mul_eventually

end GlobalTheory.AdicSpan
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.fixed_unit_eq_norm_almost_all_places : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  first | (exact @GlobalTheory.LocNorm.unit_fixed_is_norm) | (exact GlobalTheory.LocNorm.unit_fixed_is_norm) | (intros; apply GlobalTheory.LocNorm.unit_fixed_is_norm  <;> assumption)
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_iff_exists_integral_multiple : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ z : L,
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral) | (exact GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_tmul_iff_exists_isIntegral  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.almost_all_places_basis_integral : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (κ : Type) (ℓ : Module.Basis κ ℚ L) (κ' : Type) (b : Module.Basis κ' ℚ C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      IsIntB v b (∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)) ↔ ∀ i, IsIntB v ℓ (β i) := by
  first | (exact @GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (exact GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually) | (intros; apply GlobalTheory.AdicSpan.LeftBasis.isIntB_sum_leftBasis_iff_eventually  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem _root_.GlobalTheory.T.integralFrame_span_completed_eigenLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) ∧ ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  first | exact @GlobalTheory.PtDeg.intFrame_span_eigLat | exact GlobalTheory.PtDeg.intFrame_span_eigLat | (intros; apply GlobalTheory.PtDeg.intFrame_span_eigLat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary : ∀ (D : D7) [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (x y : UA D.host.E n), x ∈ locU n P → y ∈ locU n P →
    HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
    ∃ k₁ ∈ KP (D := D) n P, ∃ k₂ ∈ KP (D := D) n P, y = k₁ * x * k₂ := by
  first | exact @GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | exact GlobalTheory.LocalCartan.doubleCoset_of_hasDiv | (intros; apply GlobalTheory.LocalCartan.doubleCoset_of_hasDiv <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJForm

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem isEqv_integral (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ) (hν : IsSmU ν) (hz : (n : ℝ) - 1 < z.re) :
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ =>
      ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  refine ⟨fun φ hφ φ' hφ' => ?_, fun c φ hφ => ?_, fun g₁ g₂ φ hφ => ?_⟩
  · dsimp only
    rw [← integral_add (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ hφ) (GlobalTheory.T.integrable_zeta_integral_matrix_schwartz k n ν z hν hz φ' hφ')]
    congr 1; funext g; simp only [Pi.add_apply]; ring
  · dsimp only
    rw [← integral_const_mul]; congr 1; funext g; simp only [Pi.smul_apply, smul_eq_mul]; ring
  · set F : GL (Fin n) k → ℂ := fun g => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z with hF
    set d := gdet g₁ * gdet g₂ with hd'
    have hd : (ν d : ℂ) * apow d z ≠ 0 := mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
    have key : ∀ g : GL (Fin n) k, φ (g₁.val * g.val * g₂.val) * (ν (gdet g) : ℂ) * apow (gdet g) z
        = ((ν d : ℂ) * apow d z)⁻¹ * F (g₁ * (g * g₂)) := by
      intro g
      have e : gdet (g₁ * (g * g₂)) = gdet g * d := by
        rw [gdet_mul, gdet_mul, hd', mul_left_comm]
      have ha := apow_ne_zero d z
      have hn : (ν d : ℂ) ≠ 0 := Units.ne_zero _
      simp only [hF, e, map_mul, Units.val_mul, apow_mul, Matrix.mul_assoc]
      field_simp
    simp_rw [key]
    rw [integral_const_mul]
    have h1 : ∫ g, F (g₁ * (g * g₂)) ∂(haarVol (KO k (Fin n))) = ∫ g, F g ∂(haarVol (KO k (Fin n))) := by
      have h2 := integral_mul_right_eq_self (μ := haarVol (KO k (Fin n))) (fun g => F (g₁ * g)) g₂
      exact h2.trans (integral_mul_left_eq_self (μ := haarVol (KO k (Fin n))) F g₁)
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

theorem exists_integral_ne_zero (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ) (hν : IsSmU ν) :
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k),
      ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (GL (Fin n) k) := borel_GL
  have : MeasurableMul (GL (Fin n) k) := inferInstance
  have : (haarVol (KO k (Fin n))).IsHaarMeasure := isHaarMeasure_haarVol_KO
  set H : Subgroup (GL (Fin n) k) := KO k (Fin n) ⊓ (ν.comp Matrix.GeneralLinearGroup.det).ker with hH
  have hHo : IsOpen (H : Set (GL (Fin n) k)) := by
    rw [hH, Subgroup.coe_inf]
    exact isOpen_KO.inter (hν.1.preimage Matrix.GeneralLinearGroup.continuous_det)
  have hHc : IsCompact (H : Set (GL (Fin n) k)) :=
    isCompact_KO.of_isClosed_subset (H.isClosed_of_isOpen hHo) fun x hx => hx.1
  have hemb : Topology.IsOpenEmbedding (fun g : GL (Fin n) k => g.val) := by
    refine { toIsEmbedding := isEmbedding_val_GL, isOpen_range := ?_ }
    have e : Set.range (fun g : GL (Fin n) k => g.val) = {A | A.det ≠ 0} := by
      ext A
      refine ⟨?_, fun h => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A h, rfl⟩⟩
      rintro ⟨g, rfl⟩
      exact g.det_ne_zero
    rw [e]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  set S : Set (Matrix (Fin n) (Fin n) k) := (fun g : GL (Fin n) k => g.val) '' H with hS
  have hSc : IsCompact S := hHc.image Units.continuous_val
  have hSo : IsClopen S := ⟨hSc.isClosed, hemb.isOpenMap _ hHo⟩
  refine ⟨S.indicator 1, ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hSo).isLocallyConstant,
    HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩, ?_⟩
  have hfun : (fun g : GL (Fin n) k => S.indicator 1 g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) =
      (H : Set (GL (Fin n) k)).indicator (fun _ => (1 : ℂ)) := by
    funext g
    by_cases hg : g ∈ H
    · have h1 : g.val ∈ S := ⟨g, hg, rfl⟩
      have h2 : ν (gdet g) = 1 := hg.2
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show g ∈ (H : Set _) from hg), h2,
        apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg.1)]
      simp
    · have h1 : g.val ∉ S := by
        rintro ⟨g', hg', e⟩
        exact hg (Units.ext e ▸ hg')
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show g ∉ (H : Set _) from hg)]
      simp
  simp only [hfun]
  have hI := integral_indicator_const (μ := haarVol (KO k (Fin n))) (1 : ℂ) hHo.measurableSet
  have hpos := hHo.measure_pos (haarVol (KO k (Fin n))) ⟨1, H.one_mem⟩
  have hfin := hHc.measure_lt_top (μ := haarVol (KO k (Fin n)))
  erw [hI]
  rw [Complex.real_smul, mul_one, Complex.ofReal_ne_zero, measureReal_def]
  exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

theorem isEqv_integral_and_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ => ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 :=
  fun _ _ _ _ _ _ _ n ν z hν hz => ⟨isEqv_integral n ν z hν hz, exists_integral_ne_zero n ν z hν⟩

end GlobalTheory.GJForm
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerTw

theorem isSplitAt_iff_cPl_ne_and_cPl_cPl :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
      (IsSplitAt w ↔ GlobalTheory.EulerTw.cPl E w ≠ w) ∧ GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) = w := by
  intro E _ _ _ w
  refine ⟨⟨fun h => (GlobalTheory.SplitPts.over_split h).1, fun h => ?_⟩, GlobalTheory.SplitPts.conjSrc_conjSrc_cm w⟩
  by_contra hs
  exact h (GlobalTheory.LocInj.conjSrc_eq_of_not_split hs)

end GlobalTheory.EulerTw
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def thAt (u : Pl E) : GLw n (cPl E u) →* GLw n u :=
  (MulAut.conj (PhiU n (u.adicCompletion E))).toMonoidHom.comp
    ((invT n (u.adicCompletion E)).comp (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)))

theorem thAt_apply (u : Pl E) (h : GLw n (cPl E u)) (i j : Fin n) :
    (thAt u h).val i j =
      (-1) ^ ((i : ℕ) + j) * conjLoc (IsCMField.complexConj E).toRingEquiv u ((h⁻¹).val j.rev i.rev) :=
  GlobalTheory.ThetaPull.phi_mul_apply _ i j

theorem map_thF (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n g) = thAt u (GeneralLinearGroup.map (pLoc E (cPl E u)) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (conjFin (IsCMField.complexConj E).toRingEquiv) g i j
  change pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j) = _
  rw [h, thAt_apply, map_mul, map_pow, map_neg, map_one, pLoc_conjFin]
  rfl

theorem mem_KGL_of_thAt (u : Pl E) (k : GLw n (cPl E u)) (hk : thAt u k ∈ GlobalTheory.LFun.KGL u (n := n)) :
    k ∈ GlobalTheory.LFun.KGL (cPl E u) (n := n) := by
  have hv : ∀ (h : GLw n (cPl E u)) (i j : Fin n),
      Valued.v ((thAt u h).val i j) = Valued.v ((h⁻¹).val j.rev i.rev) := by
    intro h i j
    rw [thAt_apply, Valuation.map_mul, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow, one_mul]
    exact (conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 _
  rw [GlobLev.mem_KGL_iff_val] at hk ⊢
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := h2 j.rev i.rev
    rw [← map_inv, hv, inv_inv, Fin.rev_rev, Fin.rev_rev] at this
    exact this
  · have := h1 j.rev i.rev
    rwa [hv, Fin.rev_rev, Fin.rev_rev] at this

end GlobalTheory.EulerTw.IntRead

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

end GlobalTheory.EulerTw.IntRead
end
end
