module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeanSquareNormalizedThetaTwoTorsion
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumRpowZerosLe
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle060
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.unitaryQuotientIntegral_prod_over_places : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  first | exact @GlobalTheory.RealQuotProd.quot_integral_prod | exact GlobalTheory.RealQuotProd.quot_integral_prod | (intros; apply GlobalTheory.RealQuotProd.quot_integral_prod <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation

theorem normTheta0 : GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic.NormTheta0 := GlobalTheory.ThetaNullNormSquares.normTheta0

end GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation
end
end

section

open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_isQuotientMeasure_of_bruhat : ∀ (T T' : Type) [Group T] [MeasurableSpace T] [MeasurableMul₂ T] [Group T'] [MeasurableSpace T'] [MeasurableMul T'] [MeasurableInv T'] (j : T' →* T), Measurable j → ∀ (m : Measure T) [SFinite m] [m.IsMulLeftInvariant] (m' : Measure T') [SFinite m'] [m'.IsMulRightInvariant] [m'.IsInvInvariant] (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∃ ν, IsQuotientMeasure j m' m ν := by
  first | exact @GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction | exact GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction | (intros; apply GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction <;> assumption)
end

section

open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_unfoldingKernel_levelSubgroup_bruhat_alt : ∀ (G G' T T' : Type) [Group G] [Group G'] [Group T] [Group T'] [MeasurableSpace G] [MeasurableSpace G'] [MeasurableSpace T] [MeasurableSpace T'] [MeasurableMul G'] [MeasurableMul T] [MeasurableInv T'] (μ : Measure G) (μ' : Measure G') [μ'.IsMulLeftInvariant] (m : Measure T) (m' : Measure T') [m'.IsInvInvariant] (K : Subgroup G) (K' : Subgroup G'), MeasurableSet (K : Set G) → MeasurableSet (K' : Set G') → ∀ (φ : G' →* G) (ψ : G →* T) (ψ' : G' →* T') (j : T' →* T), Measurable ψ → Measurable ψ' → Measurable j → (∀ g, φ g ∈ K ↔ g ∈ K') → (∀ g, ψ (φ g) = j (ψ' g)) → (μ.restrict K).map ψ = m → (μ'.restrict K').map ψ' = m' → ∀ (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∀ (f : T → ℝ≥0∞), Measurable f → (∀ s t, f (j s * t) = f t) → ∀ ν, IsQuotientMeasure j m' m ν → ∃ u : G → ℝ≥0∞, Measurable u ∧ ∫⁻ h, u h ∂μ = ∫⁻ c, f (Quotient.out c) ∂ν ∧ ∀ h, ∫⁻ g, u ((φ g)⁻¹ * h) ∂μ' = {h | ∃ g, (φ g)⁻¹ * h ∈ K}.indicator 1 h * f (ψ h) := by
  first | exact @GlobalTheory.exists_unfoldingKernel_levelSubgroup_bruhat | exact GlobalTheory.exists_unfoldingKernel_levelSubgroup_bruhat | (intros; apply GlobalTheory.exists_unfoldingKernel_levelSubgroup_bruhat <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem localAtT_of_overAt (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) (H : OverPlaceIntegralForm.OverAt L N v hv) :
    ∃ s, SplittingProjection.LocalAtT L N v hv s := by
  obtain ⟨P, Pb, s, hs, hfac, hker, ⟨iso⟩, hP, hPb, ⟨hle, -, hU⟩, b, φ, e, hfr, hbij, hφ, hrow, -⟩ := H
  have hs' : SplittingProjection.IsSplitting sp.cm.sig v s := ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
  have hpart1 : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N) =
      SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v (SplittingProjection.dualLb L)) :=
    SetLike.coe_injective ((coe_partOf_prP hs' _).trans (hP.trans (coe_partOf_prP hs' _).symm))
  have hpart2 : SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v N) =
      SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v L.Lb) :=
    SetLike.coe_injective ((coe_partOf_prPbar hs' _).trans (hPb.trans (coe_partOf_prPbar hs' _).symm))
  have hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b :=
    (isFrame_iff _ _).2 ((coe_partOf_prP hs' _).trans hfr)
  have huniq : ∀ g' : GL (Fin R.k) (v.adicCompletion F),
      ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (SplittingProjection.prP s) g.1 = g' :=
    existsUnique_upts sp.cm.sig sp.gram0 sp.baseGram_isHermitian (gram_matrix_det_unit sp) _ s hs'.2.1
  have hlev : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (SplittingProjection.prP s) g * b ∈
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    intro g hg
    refine ⟨fun h => hbij.mapsTo h, fun h => ?_⟩
    obtain ⟨g', hg', hgg⟩ := hbij.surjOn h
    have h1 : bc (SplittingProjection.prP s) g' = bc (SplittingProjection.prP s) g :=
      mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g' * b =
        b⁻¹ * bc (SplittingProjection.prP s) g * b from hgg))
    have h2 : (⟨g', hg'.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g, hg⟩ :=
      (huniq (bc (SplittingProjection.prP s) g)).unique h1 rfl
    have h3 : g' = g := congrArg Subtype.val h2
    exact h3 ▸ hg'
  have hstab : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔
        bc (SplittingProjection.prP s) g ∈ stabGL (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) :=
    fun g hg => (hlev g hg).trans (hb.mem_stabGL_iff _).symm
  obtain ⟨f, hf⟩ := hb.exists_fun φ
  let ε : L.fM v hv ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F) := e
  have hfe : ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L))
      (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)),
      (∀ i, y.1 i = SplittingProjection.prP s (x.1 i)) → f y = ε (L.fT v hv x) := by
    intro x y hxy
    obtain ⟨z, hz⟩ := hb.exists_coord y
    exact (hf y z hz).trans (hrow x z ((funext hxy).symm.trans hz)).symm
  have hlift : ∀ y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N),
      ∃ x : SplittingProjection.locLat v (SplittingProjection.dualLb L), ∀ i, y.1 i = SplittingProjection.prP s (x.1 i) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (mem_partOf _ (sur_prP hs') _ y.1).1 (hpart1.le y.2)
    exact ⟨⟨x, hx⟩, fun i => (congrFun hxy i).symm⟩
  have hf0 : f ≠ 0 := (hf.ne_zero_iff hb).2 hφ
  have hsm : ∀ (a : intV E v) (a' : v.adicCompletionIntegers F),
      (a' : v.adicCompletion F) = SplittingProjection.prP s a →
      ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L))
      (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)),
      (∀ i, y.1 i = SplittingProjection.prP s (x.1 i)) → f (a' • y) = ε (L.fT v hv (a • x)) := by
    intro a a' ha x y hxy
    refine hfe _ _ fun i => ?_
    show (a' : v.adicCompletion F) * y.1 i = SplittingProjection.prP s ((a : E ⊗[F] v.adicCompletion F) * x.1 i)
    rw [map_mul, ha, hxy]
  refine ⟨s, hs', fun x hx => hfac x (funext hx), ?_, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩,
    f, ε, ?_, hfe, hf0, ?_, ?_, ?_⟩
  · rw [← (map_primes hs).1, ← (map_primes hs).2]
    exact ⟨iso⟩
  · intro a a' ha m
    obtain ⟨y, hy⟩ := surjective_of_ne_zero hf0 (ε m)
    obtain ⟨x, hx⟩ := hlift y
    have hm : m = L.fT v hv x := ε.injective (hy.symm.trans (hfe x y hx))
    rw [← hy, ← map_smul, hsm a a' ha x y hx, hm, (L.fT v hv).map_smul]
  · intro y
    obtain ⟨x, hx⟩ := hlift y
    rw [hsm (A.T : intV E v) (A.T : v.adicCompletionIntegers F) (by simp) x y hx, L.fT_T, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := hlift y
    rw [hfe x y hx, map_eq_zero_iff _ ε.injective, hker x, ← SetLike.mem_coe, coe_partOf_prP hs',
      show y.1 = OverPlaceIntegralForm.pr₁ s x.1 from funext hx]
  · intro g
    rw [hU, Subgroup.mem_inf]
    refine and_congr_right fun hg => ?_
    exact mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε
      (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)

theorem overAt_of_localAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (hN : N ≤ SplittingProjection.dualLb L)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal)
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (H : SplittingProjection.LocalAtT L N v hv s) : OverPlaceIntegralForm.OverAt L N v hv := by
  obtain ⟨hs', hfac, ⟨iso⟩, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩, f, ε, -, hfe, hf0, -, hker,
    hU⟩ := H
  replace hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b := hb
  obtain ⟨P, Pb, hs⟩ := exists_primes sp.cm.deg2 hs'
  obtain ⟨φ, hf⟩ := hb.exists_row f
  have hle : OverPlaceIntegralForm.latV v N ≤ OverPlaceIntegralForm.latV v (OverPlaceIntegralForm.baseDual L) :=
    Submodule.span_mono (Set.image_mono hN)
  have hmem : ∀ x : SplittingProjection.locLat v (SplittingProjection.dualLb L),
      OverPlaceIntegralForm.pr₁ s x.1 ∈ SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N) := fun x => by
    rw [hpart1]
    exact Submodule.subset_span ⟨x.1, x.2, rfl⟩
  refine ⟨P, Pb, s, hs, fun x hx => hfac x (congrFun hx), ?_, ?_, ?_, ?_, ⟨hle, ?_, ?_⟩, b, φ, ε,
    ?_, ⟨?_, ?_, ?_⟩, (hf.ne_zero_iff hb).1 hf0, ?_, ?_⟩
  · intro x
    rw [← coe_partOf_prP hs', SetLike.mem_coe, ← map_eq_zero_iff _ ε.injective,
      ← hfe x ⟨_, hmem x⟩ (fun _ => rfl)]
    exact hker _
  · rw [(map_primes hs).1, (map_primes hs).2]
    exact ⟨iso⟩
  · rw [← coe_partOf_prP hs', ← coe_partOf_prP hs', hpart1]
  · rw [← coe_partOf_prPbar hs', ← coe_partOf_prPbar hs', hpart2]
  · intro h0
    apply hf0
    ext y
    obtain ⟨x, hx, hxy⟩ := (mem_partOf _ (sur_prP hs') _ y.1).1 y.2
    have h1 := hfe (Submodule.inclusion hle ⟨x, hx⟩) y (fun i => (congrFun hxy i).symm)
    have h2 : L.fT v hv (Submodule.inclusion hle ⟨x, hx⟩) = 0 := LinearMap.congr_fun h0 ⟨x, hx⟩
    rw [h1, h2, map_zero, LinearMap.zero_apply]
  · ext g
    rw [hU, Subgroup.mem_inf]
    refine and_congr_right fun hg => ?_
    exact (mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε
      (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)).symm
  · exact (coe_partOf_prP hs' _).symm.trans ((isFrame_iff _ _).1 hb)
  · exact fun g hg => (hlev g hg.1).1 hg
  · intro g hg g' hg' hgg
    have h1 : bc (SplittingProjection.prP s) g = bc (SplittingProjection.prP s) g' :=
      mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g * b =
        b⁻¹ * bc (SplittingProjection.prP s) g' * b from hgg))
    have h2 : (⟨g, hg.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g', hg'.1⟩ :=
      (huniq (bc (SplittingProjection.prP s) g')).unique h1 rfl
    exact congrArg Subtype.val h2
  · intro u hu
    obtain ⟨g, hg, -⟩ := huniq (b * u * b⁻¹)
    have h1 : b⁻¹ * bc (SplittingProjection.prP s) g.1 * b = u := by rw [hg]; group
    exact ⟨g.1, (hlev g.1 g.2).2 (h1 ▸ hu), h1⟩
  · intro x y hxy
    exact (hfe x ⟨_, hmem x⟩ (fun _ => rfl)).symm.trans (hf _ y hxy)
  · intro g hg
    refine (hU g).trans (Iff.trans ⟨fun h => h.2, fun h => ⟨(hstab g hg).2 h.1, h⟩⟩ ?_)
    exact hf.mem_stabFun_iff hb _

theorem isOverLattice_iff (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) :
    OverPlaceIntegralForm.IsOverLattice L N ↔
      (SplittingProjection.IsOverLattice L N ∧
        (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal),
          ∃ φ, SplittingProjection.LocalAtT L N v h φ) ∧
        (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
        L.U ≤ levelAfL sp.cm.sig sp.gram0 N) := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨⟨h1, h2, h3, h4, fun x hx => Submodule.subset_span (h5 hx), h6⟩,
      fun v hv => localAtT_of_overAt L N v hv (h7 v hv), fun v => ?_, h8⟩
    by_cases hv : (A.T : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨P, Pb, s, -, -, -, -, -, -, ⟨hle, -, hU⟩, -⟩ := h7 v hv
      rw [hU]; exact inf_le_left
    · have : levelVL sp.cm.sig sp.gram0 v N = levelVL sp.cm.sig sp.gram0 v L.Lb :=
        congrArg (level _ _) (h6 v hv)
      rw [this]; exact L.Uloc_lev v
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, -, h8⟩
    refine ⟨h1, h2, h3, h4, fun y hy x hx => ?_, h6, fun v hv => ?_, h8⟩
    · rw [← h3] at hy
      exact hy x (h4 hx)
    · obtain ⟨s, hs⟩ := h7 v hv
      exact overAt_of_localAtT L N h5 v hv s hs

theorem overLatticeAt_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    OverPlaceIntegralForm.OverLatticeAt D Lv u ↔
      (letI := D.host.cmStar
       Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → SplittingProjection.HasOverLattice (Lv u)) := by
  letI := D.host.cmStar
  exact imp_congr_right fun _ => and_congr_right fun _ =>
    exists_congr fun N => isOverLattice_iff (Lv u) N

theorem overLattice_iff_selfDualOverBase : OverPlaceIntegralForm.OverLattice ↔ SplittingProjection.SelfDualOverBase :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => overLatticeAt_iff D Lv u

end GlobalTheory.OverCompare

end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SelfDualFrame

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing
open GlobalTheory.SelfDualGenus

def sw (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E) ≃+* LocAlg v :=
  (Algebra.TensorProduct.comm (maximalRealSubfield E) E
    (v.adicCompletion (maximalRealSubfield E))).toRingEquiv

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem mem_intV_iff (z : E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    z ∈ intV E v ↔ sw v z ∈ locOrder v := by
  constructor
  · intro hz
    refine (Subring.closure_le
      (t := (locOrder v).toSubring.comap (sw v).toRingHom)).2 ?_ hz
    rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact locEmb_mem_locOrder v x
    · exact (locOrder v).algebraMap_mem ⟨a.1, a.2⟩
  · intro hz
    have key : ∀ y ∈ locOrder v, (sw v).symm y ∈ intV E v := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        exact Subring.subset_closure (Or.inl ⟨⟨a, a, rfl⟩, rfl⟩)
      | algebraMap r => exact Subring.subset_closure (Or.inr ⟨⟨r.1, r.2⟩, rfl⟩)
      | add x y _ _ hx hy =>
        rw [map_add (sw v).symm]
        exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    simpa using key _ hz

theorem mem_latS_iff {r : ℕ} (N : Submodule (𝓞 E) (Fin r → E))
    (x : Fin r → E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    x ∈ latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) (intV E v) N ↔
      (fun i => sw v (x i)) ∈ locLattice v N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp only [Pi.zero_apply, map_zero]; exact (locLattice v N).zero_mem
    | add x y _ _ hx hy =>
      have := add_mem hx hy
      convert this using 1
      funext i
      exact map_add (sw v) (x i) (y i)
    | smul c x _ hx =>
      have := smul_mem_locLattice v ((mem_intV_iff v _).1 c.2) hx
      convert this using 1
      funext i
      exact map_mul (sw v) _ _
  · intro hx
    have key : ∀ y ∈ locLattice v N, (fun i => (sw v).symm (y i)) ∈
        latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))
          (intV E v) N := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have := add_mem hx hy
        convert this using 1
        funext i
        exact map_add (sw v).symm (x i) (y i)
      | smul c x _ hx =>
        have hc : (sw v).symm (algebraMap _ (LocAlg v) c) ∈ intV E v :=
          (mem_intV_iff v _).2 (by simpa using (locOrder v).algebraMap_mem c)
        have := Submodule.smul_mem _ (⟨_, hc⟩ : intV E v) hx
        convert this using 1
        funext i
        rw [Pi.smul_apply, Algebra.smul_def]
        exact map_mul (sw v).symm _ _
    simpa using key _ hx

theorem sw_sigR (hc : CMData (maximalRealSubfield E) E)
    (z : E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)) :
    sw v (Formalism.UG.sigR hc.sig (v.adicCompletion (maximalRealSubfield E)) z) = locConj v (sw v z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e => rfl

theorem unramified (hc : CMData (maximalRealSubfield E) E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem exists_frame_cm (hc : CMData (maximalRealSubfield E) E) {r : ℕ}
    (J : Matrix (Fin r) (Fin r) E) (hJ : IsHerm (hc.sig : E →+* E) J) (hd : IsUnit J.det)
    (N : Submodule (𝓞 E) (Fin r → E))
    (hN : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex.IsSelfDualLat (hc.sig : E →+* E) J N) :
    ∃ b : GL (Fin r) (E ⊗[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E)),
      cT (Formalism.UG.sigR hc.sig (v.adicCompletion (maximalRealSubfield E))) b.1 *
        J.map (inclE (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))) *
          b.1 = 1 ∧
      ∀ x, x ∈ latS (F := maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E))
        (intV E v) N ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV E v := by
  have := unramified hc
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (Jᵀ a b) = Jᵀ b a :=
    fun a b => congrFun (congrFun hJ a) b
  have hd' : Jᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact hd.ne_zero
  have hh : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y = hform (hc.sig : E →+* E) J y x := by
    intro x y
    unfold ReciprocityTheory.ChartRestriction.G.FD.herm hform
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change x j * J i j * ReciprocityTheory.ChartRestriction.G.FD.cc (y i) = ReciprocityTheory.ChartRestriction.G.FD.cc (y i) * J i j * x j
    ring
  have hint : ∀ a : E, a ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ a := by
    intro a
    constructor
    · rintro ⟨b, rfl⟩; exact b.isIntegral_coe
    · intro h; exact ⟨⟨a, h⟩, rfl⟩
  have hsd : ∀ x, x ∈ N ↔ ∀ y ∈ N, IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y) := by
    intro x
    have : x ∈ dualSet (hc.sig : E →+* E) J N ↔ x ∈ N := by rw [hN.2.2]; rfl
    rw [← this]
    simp only [hh, ← hint]
    rfl
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame hG hd'
    ⟨Module.Finite.iff_fg.1 hN.1, hN.2.1⟩ hsd v
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    Matrix.transpose_one] at h3
  have hb : ∀ g : GL (Fin r) (LocAlg v), (bc (sw v).symm.toRingHom g).1.map (sw v) = g.1 := by
    intro g
    ext i j
    exact (sw v).apply_symm_apply _
  refine ⟨bc (sw v).symm.toRingHom h, ?_, fun x => ?_⟩
  · apply Matrix.map_injective (f := (sw v).toRingHom) (sw v).injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← h3]
    congr 1
    · congr 1
      ext i j
      exact (sw_sigR v hc _).trans (congrArg (locConj v) ((sw v).apply_symm_apply _))
    · exact hb h
  · rw [mem_latS_iff, h2, ← map_inv]
    refine forall_congr' fun i => ?_
    rw [mem_intV_iff, ← hb h⁻¹]
    have := RingHom.map_mulVec (sw v).toRingHom (bc (sw v).symm.toRingHom h⁻¹).1 x i
    exact Iff.of_eq (congrArg (· ∈ locOrder v) this.symm)

end CM

theorem exists_frame : ∀ (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E))
    (v : HeightOneSpectrum (𝓞 D.host.F)),
    letI := D.host.cmStar
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualStabiliserIndex.IsSelfDualLat
      (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N →
    ∃ b : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F),
      cT (Formalism.UG.sigR D.sp.cm.sig (v.adicCompletion D.host.F)) b.1 *
        D.sp.gram0.map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * b.1 = 1 ∧
      ∀ x, x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) N ↔
        ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ intV D.host.E v := by
  intro D N v hN
  letI := D.host.cmStar
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  exact exists_frame_cm v D.sp.cm D.sp.gram0 D.sp.baseGram_isHermitian
    (GlobalTheory.OverCompare.gram_matrix_det_unit D.sp) N hN

end GlobalTheory.SelfDualFrame
end
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.exists_sum_characters_finsum_zeros_rpow_re_sub_one_le : ∃ A C η₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < η₀ ∧ ∀ (q : ℕ) [NeZero q] (T u η : ℝ), 2 ≤ T → ((q : ℝ) * T) ^ A ≤ u → 0 ≤ η → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤ C * (u ^ (-η / 2) + u ^ (-η₀)) := by
  first | exact @GlobalTheory.Lin.ZeroSum.sum_rpow_zeros_le | exact GlobalTheory.Lin.ZeroSum.sum_rpow_zeros_le | (intros; apply GlobalTheory.Lin.ZeroSum.sum_rpow_zeros_le <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), W.SigOK → (GlobalTheory.NegSpace.neg W).SigOK := by
  first | exact @GlobalTheory.NegSpace.sigOK_neg | exact GlobalTheory.NegSpace.sigOK_neg | (intros; apply GlobalTheory.NegSpace.sigOK_neg <;> assumption)
end
