module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Bundle001
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle015
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle053
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddBlockAnisotropic
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle064
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle010
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle068
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle066
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle052
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle060
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle700
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

theorem swMeasC_succ (hB : BaseOne) (hI : IsomC) (hS : ScaleC) (hSt : StepC) (hN : NotRepC) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ J → PositivityTheory.PfSWUS.HMass.IsAnisoH σ J →
    ∀ (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → SWMeasC σ J T hT := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro J hJ _ T hT hd
    exact hB F E σ hσ J hJ T hT hd
  | succ n ih =>
    intro J hJ ha T hT hd
    obtain ⟨t, x, ht, hx⟩ := GlobalTheory.CompanionTheory.SW.HermRep.exists_repr F E σ hσ (n + 1) T ⟨hT, hd⟩
    obtain ⟨g, T₁, hT₁, hb, -⟩ :=
      GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ (n + 1) T ⟨hT, hd⟩ t x ht hx
    obtain ⟨hdet, hblk, -, -⟩ := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hσ (n + 1) T₁ t
    have hT' := hblk hT₁.1
    have htE : algebraMap F E t ≠ 0 := by
      simpa using ht
    have hd' : (blockOne (algebraMap F E t) T₁).det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero htE hT₁.2
    refine hS F E σ hσ (n + 2) J hJ (n + 2) T hT hd g _ hT' hb ?_
    by_cases hrep : ∃ y : Fin (n + 2) → E, hE σ J y y = algebraMap F E t
    · obtain ⟨y, hy⟩ := hrep
      obtain ⟨g', J₁, hJ₁, hb', -⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hσ (n + 1) J hJ t y ht hy
      have ha' : PositivityTheory.PfSWUS.HMass.IsAnisoH σ (blockOne (algebraMap F E t) J₁) := by
        rw [hb']
        exact PositivityTheory.PfSWUS.HMass.isAnisoH_of_isometry σ J g' ha
      refine hI F E σ hσ (n + 2) J hJ g' _ hb' (n + 2) _ hT' hd' ?_
      exact hSt F E σ hσ (n + 1) J₁ hJ₁ (by omega) t ht ha' T₁ hT₁.1 hT₁.2 hT'
        (ih J₁ hJ₁ (PositivityTheory.PfSWUS.HMass.isAnisoH_of_block σ _ J₁ ha') T₁ hT₁.1 hT₁.2)
    · exact hN F E σ hσ (n + 1) J hJ (by omega) ha t ht T₁ hT₁.1 hT₁.2 hT' (fun y hy => hrep ⟨y, hy⟩)

theorem swMeasCAll_of (hB : BaseOne) (hI : IsomC) (hS : ScaleC) (hSt : StepC) (hN : NotRepC) : SWMeasCAll := by
  intro F E _ _ _ _ _ σ hσ M hM J hJ ha T hT hd
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  exact swMeasC_succ hB hI hS hSt hN F E σ hσ n J hJ ha T hT hd

end PositivityTheory.SiegelWeilFormula.Densx

end
end

section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

def halfLam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : ℝ≥0 := by
  classical
  exact if h : ∃ Λ : ℂ, IsLamLim F E Λ then Real.toNNReal (h.choose.re / 2) else 0

theorem halfLam_spec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Λ : ℂ)
    (hΛ : IsLamLim F E Λ) : ((halfLam F E : ℝ) : ℂ) = Λ / 2 := by
  classical
  have h : ∃ Λ : ℂ, IsLamLim F E Λ := ⟨Λ, hΛ⟩
  have he : h.choose = Λ := lamLim_unique h.choose_spec hΛ
  obtain ⟨h1, h2⟩ := lamLim_real hΛ
  rw [halfLam, dite_eq_left h, he, Real.coe_toNNReal _ (by linarith)]
  conv_rhs => rw [h1]
  push_cast
  ring

theorem notRepC_of (hE1 : PositivityTheory.PfSWUS.HMass.OneVecBinary) (hM : MassCAll) : NotRepC := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM1 hA t ht T hT hdet hT' hne
  intro d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf m hminf hm
  refine ⟨halfLam F E, ?_, fun Λ hΛ => halfLam_spec Λ hΛ⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hLinf : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v : HeightOneSpectrum (𝓞 F), IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  have haarOf : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
      [BorelSpace R], IsLocR R → ∀ lam' : Measure R, lam'.IsAddHaarMeasure →
      (∀ n' M' : ℕ, (coordW R b lam' n' M').IsAddHaarMeasure) ∧
        ∀ n' : ℕ, (coordHerm R σ b lam' n').IsAddHaarMeasure := by
    intro R _ _ _ _ _ hLoc lam' hl
    obtain ⟨_, _, _, _, -⟩ := hLoc
    exact (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam' hl).2
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun _ _ => σ.commutes t
  have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
  have hdet1 : T1.det ≠ 0 := by
    rw [Matrix.det_fin_one]; exact htE
  have hsw := PositivityTheory.PfSWUS.HMass.one_vec_sw hE1 F E σ hCM (M + 1) J hJ (by omega) (Or.inr hA) T1 hT1 hdet1
  obtain ⟨minf1, hminf1⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM (M + 1) J hJ (Ainf F) hLinf 1 _ _
    ((haarOf _ hLinf laminf hinf.1).1 1 (M + 1)) ((haarOf _ hLinf laminf hinf.1).2 1)
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m' : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E),
      IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 (M + 1)) (coordHerm (Fv F v) σ b (lam v) 1) m' :=
    fun v => GlobalTheory.T.exists_gram_fiber_measures F E σ hCM (M + 1) J hJ (Fv F v) (hLv v) 1 _ _
      ((haarOf _ (hLv v) (lam v) (hv v).1).1 1 (M + 1)) ((haarOf _ (hLv v) (lam v) (hv v).1).2 1)
  choose m1 hm1 using hex
  have hEul := hsw d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf1 m1 hminf1 hm1
  have hS1 : {X : Fin 1 → Fin (M + 1) → E | gramE σ J X = T1} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    exact hne (X 0) (congrFun (congrFun hX 0) 0)
  have hS : {X : Fin (M + 1) → Fin (M + 1) → E | gramE σ J X = blockOne (algebraMap F E t) T} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    apply hne (X 0)
    simpa [gramE, blockOne] using congrFun (congrFun hX 0) 0
  have hz := ((GlobalTheory.T.euler_product_measure_zero F E σ hCM d b 1 (M + 1) _ 1 _ _).1 hEul
    (SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS1))
  have hvan : minf (hermOf (Ainf F) σ (blockOne (algebraMap F E t) T) hT') = 0 ∨
      ∃ v, cfac E v • m v (hermOf (Fv F v) σ (blockOne (algebraMap F E t) T) hT') = 0 := by
    rcases hz with h | h | ⟨v, h⟩
    · exact absurd h one_ne_zero
    · exact Or.inl (SwEmpty.fibre_zero_of_one σ hCM J hJ (Ainf F) hLinf b laminf hinf.1 t ht T hT' T1 rfl hT1
        minf1 minf hminf1 hminf h)
    · refine Or.inr ⟨v, ?_⟩
      rw [SwEmpty.fibre_zero_of_one σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hv v).1 t ht T hT' T1 rfl hT1
        (m1 v) (m v) (hm1 v) (hm v) h, smul_zero]
  have hdetB : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [((GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M T t).1)]
    exact mul_ne_zero htE hdet
  obtain ⟨hfin, hsum⟩ := hM F E σ hCM (M + 1) (by omega) J hJ (blockOne (algebraMap F E t) T) hT' hdetB d b lam
    (fun v => hv v) m hm
  rw [SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS]
  exact (GlobalTheory.T.euler_product_measure_zero F E σ hCM d b (M + 1) (M + 1) 0 (halfLam F E) _ _).2.2 hfin hsum hvan

end PositivityTheory.SiegelWeilFormula.Densx

end
end

section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

theorem smul_indicator_mass {α : Type} [MeasurableSpace α] {β : Type} (k : ℝ≥0) (μ : Measure α) (A B : Set α)
    (L : Set β) (y : β) (h : μ A = L.indicator (fun _ => μ B) y) :
    (k • μ) A = L.indicator (fun _ => (k • μ) B) y := by
  by_cases hy : y ∈ L
  · rw [Set.indicator_of_mem hy] at h ⊢
    rw [Measure.smul_apply, Measure.smul_apply, h]
  · rw [Set.indicator_of_notMem hy] at h ⊢
    rw [Measure.smul_apply, h, smul_zero]

theorem stepC_of (hE1 : PositivityTheory.PfSWUS.HMass.OneVecBinary) (hM : MassCAll) : StepC := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM1 t ht hA T hT hdet hT' hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hta : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨hdetb, hhermb, -, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩
  have hdet' : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [(GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M T t).1]; exact mul_ne_zero hta hdet

  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁
  obtain ⟨m'inf, hm'inf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Ainf F) hLi b laminf hinf.1 M
  choose m' hm' using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hlam v).1 M
  obtain ⟨c₀, hE', hc₀⟩ := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf m' hm'inf hm'
  refine ⟨c₀, ?_, hc₀⟩

  obtain ⟨m₁inf, hm₁inf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1
  choose m₁ hm₁ using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1

  obtain ⟨cinf, c, hc, hcinf, hcv⟩ := GlobalTheory.T.scalar_multiplication_euler_product F E σ hCM (algebraMap F E t) hta
  have hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) =
      cinf • coordK (Ainf F) b laminf := by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLi
    exact hcinf _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1).1
  have hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      c v • coordK (Fv F v) b (lam v) := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    exact hcv v _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1
  obtain ⟨-, -, -, -, -, -, -, S₃, hS₃⟩ := GlobalTheory.T.unit_product_closure_properties F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩

  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun a b => by simp [T1]
  have hdet1 : T1.det ≠ 0 := by rw [Matrix.det_fin_one]; exact hta
  have hE₁ := PositivityTheory.PfSWUS.HMass.one_vec_sw hE1 F E σ hCM (M + 1) _ hJ' (by omega) (Or.inr hA) T1 hT1 hdet1
    d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 m₁inf m₁ hm₁inf hm₁
  obtain ⟨β, hβ1, -, hβ2⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hCM T1 hT1
  have hβ : β = t := (algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm
  rw [hβ] at hβ2
  simp only [hβ2] at hE₁
  obtain ⟨-, hsum₁, S₁, hS₁⟩ := hE₁
  have hsum' := hE'.2.1
  have hgood := hM F E σ hCM (M + 1) (by omega) _ hJ' _ hT' hdet' d b lam hlam m hm
  refine ⟨hgood.1, hgood.2, ?_⟩
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.CompanionTheory.SW.StepC.theta_hypothesis_c F E σ hCM M J hJ t ht M d b _ _ _ _ hE'
  have hG := GlobalTheory.T.local_density_block_one_eventually F E σ hCM M J hJ t ht M T hT hdet hT' d b
  have hSG := GlobalTheory.T.local_measures_orthogonal_sum_almost_all_places F E σ hCM M J hJ t ht M T hT hdet d b
  refine ⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset,
    fun S hS φinf φ hφinf hφ => ?_⟩
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inl (Or.inr hx))
  have hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inr hx)
  obtain ⟨hc1, hc2⟩ := hS₃ S hS3
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht M T hT hdet hT' (Ainf F) hLi d b
    laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf
  choose Ψ₀ hΨm₀ hΨ1₀ hΨ2₀ using fun v => GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht M T hT hdet hT' (Fv F v) (hLv v) d b
    (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (fun y => (cfac E v : ℝ≥0∞) * φ v y)
    ((hφ v).const_mul _)

  have hΨ1 : ∀ v, ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J),
      Ψ₀ v (actW (Fv F v) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) =
        ∫⁻ X, φ v (actW (Fv F v) σ _ g (consTup X)) ∂(cfac E v • m' v (hermOf (Fv F v) σ T hT)) := by
    intro v g
    rw [hΨ1₀ v g, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, lintegral_const_mul']
    exact ENNReal.coe_ne_top
  have hΨ2 : ∀ v, ∫⁻ X, φ v X ∂(cfac E v • m v (hermOf (Fv F v) σ _ hT')) =
      (c v : ℝ≥0∞) ^ M * ∫⁻ y, Ψ₀ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    intro v
    rw [← hΨ2₀ v, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, lintegral_const_mul']
    exact ENNReal.coe_ne_top
  have hHv : ∀ v, (coordW (Fv F v) b (lam v) M M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) M).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact ⟨hh.2.1 M M, hh.2.2 M⟩
  have hHyp := hS₂ S hS2 φinf φ Ψinf Ψ₀ hφinf hφ hΨinf1 hΨ1 (fun v hv g =>
    smul_indicator_mass _ _ _ _ _ _ (GlobalTheory.CompanionTheory.SW.Step.of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g))
  set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, ((cfac E v.1 • m' v.1 (hermOf (Fv F v.1) σ T hT)) (latV b v.1)).toReal) with hτ'
  have hPm : Measurable (pureL b S Ψinf Ψ₀) := GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b 1 (M + 1) S Ψinf Ψ₀ hΨinfm hΨm₀
  have hth := GlobalTheory.T.lintegral_thetaMeas_block_one_eq_rank_one F E σ hCM M J hJ t ht M T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ)
    (fun y => ((c₀ : ℝ≥0∞) * τ') * pureL b S Ψinf Ψ₀ y) (GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (M + 1) (M + 1) S φinf φ hφinf hφ)
    (hPm.const_mul _) hHyp
  have hone := hS₁ S hS1 Ψinf Ψ₀ hΨinfm hΨm₀
  rw [hth, lintegral_const_mul _ hPm]
  have hone' : ∫⁻ X, pureL b S Ψinf Ψ₀ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _ := hone
  rw [hone']
  have hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) *
      ∏ v ∈ S, ∫⁻ X, φ v X ∂(cfac E v • m v (hermOf (Fv F v) σ _ hT')) =
      (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ₀ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    have hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hc2
    rw [hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) ^ M * ((∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ₀ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))) := by rw [mul_pow]; ring
      _ = _ := by rw [hone2, one_pow, one_mul]
  have htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, ((cfac E v.1 • m v.1 (hermOf (Fv F v.1) σ _ hT')) (latV b v.1)).toReal) =
      τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) := by
    have hA := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => ((cfac E v.1 • m' v.1 (hermOf (Fv F v.1) σ T hT)) (latV b v.1)).toReal)
      (hsum'.subtype _)
    have hB := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)
      (hsum₁.subtype _)
    have hcong : ∀ v : {v // v ∉ S}, ((cfac E v.1 • m v.1 (hermOf (Fv F v.1) σ _ hT')) (latV b v.1)).toReal =
        ((cfac E v.1 • m' v.1 (hermOf (Fv F v.1) σ T hT)) (latV b v.1)).toReal *
          (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal := fun v => by
      rw [Measure.smul_apply, Measure.smul_apply, GlobalTheory.CompanionTheory.SW.Step.of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]
      simp [ENNReal.toReal_mul, ENNReal.smul_def, mul_assoc]
    rw [tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]
  rw [hprod, htail]
  simp only [ENNReal.coe_one, one_mul]
  ring

end PositivityTheory.SiegelWeilFormula.Densx

end
end
