module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle064
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBlockInvertibleCriterion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle660
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle663
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle693
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle317
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle694
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle696
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

theorem _root_.GlobalTheory.T.irreducible_subquotient_cuspidal_permutation : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l N : ℕ} (x : Fin l → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N) (hxc : ∀ a, (x a).IsCusp) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr x hx)), ∃ (e : Equiv.Perm (Fin l)) (he : ∑ a, (x (e a)).1 = N), 1 ≤ jm (fun a => x (e a)) he π := by
  first | exact @GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm | exact GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm | (intros; apply GlobalTheory.CompanionTheory.SegNcjm.exists_perm_one_le_jm <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem compact_finite_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → (∀ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C → m' (hermOf R σ T hT) C < ⊤) → ∀ C : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E), IsCompact C → m (hermOf R σ _ hT') C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ t ht n T hT hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc hfin C hC
  obtain ⟨b1, b2, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hcm M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨b2 hJ.1, by rw [b1]; exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2⟩
  have hR' := hR
  obtain ⟨_, _, _, _, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have := hB n M
  have := hB 1 (M + 1)
  have := hB (n + 1) (M + 1)
  obtain ⟨hTG, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm _ _ hJ' R
  obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam hlam
  have e0 : gramR R σ (blockOne (algebraMap F E t) J) (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    funext a a'
    simp only [gramR, hR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform, JR, blockOne, Fin.sum_univ_succ, hermScal, Fin.cons_zero, Fin.cons_succ,
      map_one, map_zero, one_mul, mul_one, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Matrix.map_apply,
      Matrix.of_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes t
  obtain ⟨s, sm, s1, s2⟩ := GlobalTheory.T.rank_one_gram_measurable_section F E σ hcm _ _ hJ' R hR (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) (by
    rw [e0, Matrix.det_unique]
    exact (ht.isUnit.map (algebraMap F R)).map (algebraMap R (R ⊗[F] E)))
  rw [e0] at s1 s2
  have hCm : MeasurableSet C := hC.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.scalar_extension_fibre_measure F E σ hcm M J hJ t ht n T hT hT' R hR d b lam hlam m m₁ m' hm hm₁ hm' c hc
    (C.indicator 1) (measurable_one.indicator hCm)
  rw [lintegral_indicator_one hCm] at hint
  have hc' : Continuous (consTup : (Fin n → Fin M → R ⊗[F] E) → _) := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun i => ?_) i
    exacts [continuous_const, continuous_const, continuous_const, continuous_apply_apply a i]

  let p : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin 1 → Fin (M + 1) → R ⊗[F] E) := fun X _ => X 0
  have hpc : Continuous p := continuous_pi fun _ => continuous_apply 0
  have hC₁ : IsCompact (p '' C) := hC.image hpc
  obtain ⟨C', hC', hs⟩ := s2 _ hC₁

  let r : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) := fun Y a i => Y a.succ i.succ
  have hrc : Continuous r := continuous_pi fun a => continuous_pi fun i => continuous_apply_apply a.succ i.succ
  have hD : IsCompact ((fun q : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      actW R σ _ q.1⁻¹ q.2) '' (C' ×ˢ C)) :=
    (hC'.prod hC).image ((hact (n + 1)).1.comp (continuous_fst.inv.prodMk continuous_snd))
  obtain ⟨K, hK, hKsub⟩ : ∃ K : Set (Fin n → Fin M → R ⊗[F] E), IsCompact K ∧
      ∀ h ∈ C', ∀ X, actW R σ _ h (consTup X) ∈ C → X ∈ K := by
    refine ⟨_, hD.image hrc, fun h hh X hX => ⟨consTup X, ⟨(h, _), ⟨hh, hX⟩, ?_⟩, rfl⟩⟩
    show actW R σ _ h⁻¹ (actW R σ _ h (consTup X)) = consTup X
    rw [← (hact _).2.2.1, inv_mul_cancel, (hact _).2.1]
  have hKf := hfin K hK
  have hfirst : ∀ (h : HA R σ (blockOne (algebraMap F E t) J)) (X : Fin n → Fin M → R ⊗[F] E),
      p (actW R σ _ h (consTup X)) = actW R σ _ h (fun _ : Fin 1 => Fin.cons 1 fun _ => 0) := fun h X => rfl
  have hae : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    refine measure_mono_null ?_ (hm₁.1 (hermScal R σ (algebraMap F R t)))
    intro y hy hy'
    exact hy hy'.1
  have hbound : ∀ᵐ y ∂(m₁ (hermScal R σ (algebraMap F R t))),
      Ψ y ≤ (p '' C).indicator (fun _ => m' (hermOf R σ T hT) K) y := by
    filter_upwards [hae] with y hy
    have hy' := s1 y hy
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => actW R σ _ (s y) (consTup X) :=
      ((hact _).1.comp (continuous_const.prodMk hc')).measurable
    have hΨy : Ψ y = m' (hermOf R σ T hT) {X | actW R σ _ (s y) (consTup X) ∈ C} := by
      have h1 := hΨ (s y)
      rw [hy'] at h1
      rw [h1]
      have h2 : (fun X : Fin n → Fin M → R ⊗[F] E =>
          C.indicator (1 : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (actW R σ _ (s y) (consTup X))) =
          {X | actW R σ _ (s y) (consTup X) ∈ C}.indicator 1 := by
        funext X
        simp [Set.indicator]
      rw [h2]
      exact lintegral_indicator_one (hmeas hCm)
    by_cases hyC : y ∈ p '' C
    · rw [Set.indicator_of_mem hyC, hΨy]
      exact measure_mono fun X hX => hKsub _ (hs y hyC hy) X hX
    · have hempty : {X | actW R σ _ (s y) (consTup X) ∈ C} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun X hX => hyC ⟨_, hX, ?_⟩
        rw [hfirst, hy']
      rw [hΨy, hempty, measure_empty]
      exact bot_le
  have hloc := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm _ _ hJ' R hR 1 _ _ _ (k1 1 (M + 1)) (k2 1) hm₁
    (hermScal R σ (algebraMap F R t))).1
  have hΨf : ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) < ⊤ := by
    refine (lintegral_mono_ae hbound).trans_lt ?_
    rw [lintegral_indicator_const hC₁.measurableSet]
    exact ENNReal.mul_lt_top hKf hC₁.measure_lt_top
  rw [hint]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hΨf

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis


theorem _root_.GlobalTheory.T.rows_of_weyl_heisenberg_product : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K),
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.LowerRows.lower_rows | exact GlobalTheory.CompanionTheory.ZUnf.LowerRows.lower_rows | (intros; apply GlobalTheory.CompanionTheory.ZUnf.LowerRows.lower_rows <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis


theorem _root_.GlobalTheory.T.unitary_cell_block_normal_form : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit x.det → IsUnitary σ (blk4 0 1 (-1) 0) x → LinearMap.ker ((lowerC x).mulVecLin ∘ₗ zinc hn) = ⊥ →
    ∃ (T₀ : Matrix (Fin n) (Fin n) K) (a₁ b₁ Z : Matrix (Fin ρ) (Fin ρ) K) (a₂ b₂ X Y : Matrix (Fin ρ) (Fin p) K)
      (a₃ b₃ W : Matrix (Fin p) (Fin ρ) K) (a₄ b₄ c' d' : Matrix (Fin p) (Fin p) K),
      IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')) ∧
      IsUnit (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')).det ∧
      lowerC x = T₀ * bl hn (-1) X 0 c' ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T₀ * bl hn Z Y W d' := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.rowReduce_lowerC | exact GlobalTheory.CompanionTheory.ZUnf.rowReduce_lowerC | (intros; apply GlobalTheory.CompanionTheory.ZUnf.rowReduce_lowerC <;> assumption)
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis


theorem _root_.GlobalTheory.T.unitary_block_invertible_criterion : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a₁ b₁ Z : Matrix (Fin ρ) (Fin ρ) K) (a₂ b₂ X Y : Matrix (Fin ρ) (Fin p) K)
      (a₃ b₃ W : Matrix (Fin p) (Fin ρ) K) (a₄ b₄ c' d' : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')) →
    IsUnit (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')).det →
    ∃ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      IsUnit (blk4 (a₄ + a₃ * X) (b₄ + a₃ * Y) c' d').det ∧ IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (a₄ + a₃ * X) (b₄ + a₃ * Y) c' d') ∧
      cT σ ζ = ζ ∧ bl hn (-1) X 0 c' = T * rowC hn η (a₄ + a₃ * X) c' ∧ bl hn Z Y W d' = T * rowD hn σ ζ η (b₄ + a₃ * Y) d' := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.NormalRow.normal_form | exact GlobalTheory.CompanionTheory.ZUnf.NormalRow.normal_form | (intros; apply GlobalTheory.CompanionTheory.ZUnf.NormalRow.normal_form <;> assumption)
end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology
noncomputable section

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem decay_step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) {Ω : Set (GAd σ J)} (hΩ : IsCompact Ω)
    (hΩP : Ω ⊆ minParOne σ J X) {c : ℝ} (hc : 0 < c) {U : Subgroup (GAd σ J)} (hU : IsOpen (U : Set (GAd σ J))) (A e m : ℕ)
    (hm : ∀ ψ, Good σ J U A ψ → ∀ Cm : Set (GAd σ J), IsCompact Cm → ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ‖ψ (p * a * k)‖ * rbar t ^ m ≤ B * rbar t ^ e)
    (ψ : GAd σ J → ℂ) (hψ : Good σ J U A ψ) (Cm : Set (GAd σ J)) (hCm : IsCompact Cm) :
    ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm,
      ‖ψ (p * a * k)‖ * rbar t ^ (m + 1) ≤ B * rbar t ^ e := by
  obtain ⟨q, b, Ω₀, Cv, δ₁, hb, hΩ₀, hδ₁, hCv, hmv⟩ := GlobalTheory.T.siegel_set_uniform_smooth_bound F E σ h n J hJ
  have hCm' : IsCompact ((fun x : GAd σ J × GAd σ J => x.1 * x.2) '' (Cm ×ˢ Ω₀)) :=
    (hCm.prod hΩ₀).image (by fun_prop)
  choose B hB using fun i => hm _ (GlobalTheory.T.good_function_line_derivative F E σ h n J hJ U A ψ (b i) hψ (hb i)) _ hCm'
  obtain ⟨B₀, hB₀⟩ := hm ψ hψ Cm hCm
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.siegel_domain_open_subgroup_bound F E σ h n J hJ r X Y hW Ω Cm c U hΩ hΩP hCm hc hU
  set R₀ := max 1 (M / δ₁) with hR₀
  have hR1 : 1 ≤ R₀ := le_max_left _ _
  have hSum : 0 ≤ ∑ i, |B i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨R₀ * |B₀| + Cv * M * ∑ i, |B i|, fun p hp t ht a ha k hk => ?_⟩
  have hR := one_le_rbar t
  have hRpos : 0 < rbar t := by linarith
  have hRe : 0 < rbar t ^ e := pow_pos hRpos e
  have hRm : 0 < rbar t ^ m := pow_pos hRpos m
  have hT : 0 ≤ Cv * M * ∑ i, |B i| := mul_nonneg (mul_nonneg hCv hM0) hSum
  by_cases hcase : rbar t ≤ R₀
  · calc ‖ψ (p * a * k)‖ * rbar t ^ (m + 1) = rbar t * (‖ψ (p * a * k)‖ * rbar t ^ m) := by ring
      _ ≤ R₀ * (|B₀| * rbar t ^ e) := by
          refine mul_le_mul hcase ((hB₀ p hp t ht a ha k hk).trans ?_) (by positivity) (by linarith)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hRe.le
      _ ≤ _ := by
          rw [← mul_assoc, add_mul]
          exact le_add_of_nonneg_right (mul_nonneg hT hRe.le)
  · push Not at hcase
    have hne : rbar t ≠ 1 := fun e' => by
      rw [e'] at hcase; linarith
    obtain ⟨s, hs⟩ := (rbar_eq t).resolve_left hne
    have hδ : M / rbar t ≤ δ₁ := by
      rw [div_le_iff₀ hRpos]
      have h1 : M / δ₁ ≤ R₀ := le_max_right _ _
      rw [div_le_iff₀ hδ₁] at h1
      nlinarith
    set g := p * a * k with hg
    set cc : Fin q → ℝ := fun i => |B i| * rbar t ^ e / rbar t ^ m with hcc
    have hcc' : ∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ cc i := fun i x hx => by
      have := hB i p hp t ht a ha (k * x) ⟨(k, x), ⟨hk, hx⟩, rfl⟩
      rw [show p * a * (k * x) = g * x by rw [hg, mul_assoc (p * a)]] at this
      rw [hcc, le_div_iff₀ hRm]
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hRe.le)
    have hvar : ‖ψ g‖ ≤ Cv * (M / rbar t) * ∑ i, cc i := by
      refine GlobalTheory.T.cuspidal_constant_term_small F E σ h n J hJ ψ hψ.left hψ.cont hψ.cusp _ (pre X s) (Nat.succ_pos _)
        (GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ _) g _ fun m' hm' => ?_
      obtain ⟨γ, hγ, u, κ, hu, hκU, hκf, e'⟩ := hM p hp t ht a ha k hk s m' hm'
      rw [← hs] at hu
      have : ψ (m' * g) = ψ (g * u) := by
        rw [hg, e', hψ.level κ hκU hκf, mul_assoc γ, hψ.left γ hγ]
      rw [this]
      exact hmv ψ hψ.smooth g u _ (div_nonneg hM0 hRpos.le) hδ hu cc hcc'
    have hsum : ∑ i, cc i = (∑ i, |B i|) * rbar t ^ e / rbar t ^ m := by
      rw [hcc, Finset.sum_mul, Finset.sum_div]
    calc ‖ψ g‖ * rbar t ^ (m + 1) ≤ (Cv * (M / rbar t) * ∑ i, cc i) * rbar t ^ (m + 1) :=
          mul_le_mul_of_nonneg_right hvar (pow_pos hRpos _).le
      _ = (Cv * M * ∑ i, |B i|) * rbar t ^ e := by
          rw [hsum, pow_succ]
          field_simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hRe.le
          exact le_add_of_nonneg_left (by positivity)

theorem rapid_decrease : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ), IsCompact (K : Set (GAd σ J)) → IsCompact Ω → Ω ⊆ minParOne σ J X → 0 < c → ∀ φ : GAd σ J → ℂ, IsSmoothModerate σ J φ → IsCuspidal σ J φ → ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ siegelSet σ J X Y Ω c K, ‖φ g‖ * (height σ J g : ℝ) ^ N ≤ C := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K Ω c hK hΩ hΩP hc φ hs hcu N
  obtain ⟨U, hU, hlev⟩ := hs.level
  obtain ⟨A, hA⟩ := hs.growth
  have hG : Good σ J U A φ := ⟨hs.left, hlev, hs.cont, hs.smooth, hA, hcu⟩
  obtain ⟨b, hb⟩ := GlobalTheory.T.height_bound_siegel_torus F E σ h n J hJ r X Y hW c hc
  set e := b * A with he
  have hbase : ∀ ψ, Good σ J U A ψ → ∀ Cm : Set (GAd σ J), IsCompact Cm → ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ‖ψ (p * a * k)‖ * rbar t ^ 0 ≤ B * rbar t ^ e := fun ψ hψ Cm hCm => by
    obtain ⟨H, hH0, hH⟩ := hb Ω Cm hΩ hCm
    obtain ⟨C, hC⟩ := hψ.growth [] (by simp)
    refine ⟨|C| * H ^ A, fun p hp t ht a ha k hk => ?_⟩
    have h1 := hC (p * a * k)
    have h2 := hH p hp t ht a ha k hk
    have h3 : (0 : ℝ) ≤ (height σ J (p * a * k) : ℝ) := NNReal.coe_nonneg _
    simp only [List.foldr_nil] at h1
    rw [pow_zero, mul_one, he, pow_mul, mul_assoc |C|, ← mul_pow]
    exact h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg h3 _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 A) (abs_nonneg _)))
  have hall : ∀ m : ℕ, ∀ ψ, Good σ J U A ψ → ∀ Cm : Set (GAd σ J), IsCompact Cm → ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ‖ψ (p * a * k)‖ * rbar t ^ m ≤ B * rbar t ^ e := fun m => by
    induction m with
    | zero => exact hbase
    | succ m ih => exact fun ψ hψ Cm hCm => decay_step h hJ hW hΩ hΩP hc hU A e m ih ψ hψ Cm hCm
  obtain ⟨B, hB⟩ := hall (b * N + e) φ hG _ hK
  obtain ⟨H, hH0, hH⟩ := hb Ω K hΩ hK
  refine ⟨|B| * H ^ N, ?_⟩
  rintro _ ⟨p, hp, t, ht, a, ha, k, hk, rfl⟩
  have hR := one_le_rbar t
  have hRpos : 0 < rbar t := by linarith
  have h1 := hB p hp t ht a ha k hk
  have h2 := hH p hp t ht a ha k hk
  have h3 : (0 : ℝ) ≤ (height σ J (p * a * k) : ℝ) := NNReal.coe_nonneg _
  have h4 : ‖φ (p * a * k)‖ * rbar t ^ (b * N) ≤ |B| := by
    rw [pow_add, ← mul_assoc] at h1
    have h5 := h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos hRpos e).le)
    exact le_of_mul_le_mul_right h5 (pow_pos hRpos e)
  calc ‖φ (p * a * k)‖ * (height σ J (p * a * k) : ℝ) ^ N ≤ ‖φ (p * a * k)‖ * (H * rbar t ^ b) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 N) (norm_nonneg _)
    _ = (‖φ (p * a * k)‖ * rbar t ^ (b * N)) * H ^ N := by rw [mul_pow, pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 (pow_nonneg hH0 _)

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem orbFin_of_latBound : LatBound → OrbFin := by
  intro hL D θ hθ W m hm x₀ hx N hN
  obtain ⟨C, hC⟩ := hL D θ hθ W W.rank N hN
  have hB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨-, g2, g3, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hfd : IsFundamentalDomain (GQ W) (stdDom (GQ W)) m := isFundamentalDomain_stdDom _ m
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W m _ hm hfd
  have hcnt : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  have hNc : Continuous N :=
    (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ W.rank W.rank N
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ W.rank W.rank N hN)).1
  have hfm : Measurable fun h : GA D W => ‖N (ww W x₀ h)‖ₑ :=
    (hNc.comp (continuous_ww x₀)).enorm.measurable

  classical
  have hu : ∀ γ : GQ W, ∃ u : GL (Fin W.rank) D.host.E, mt W γ.1 = rat u.1 := fun γ => by
    obtain ⟨u, -, hu⟩ := γ.2
    exact ⟨u, (congrArg Units.val hu).symm⟩
  choose u hu using hu
  have hxu : IsUnit x₀.det := isUnit_iff_ne_zero.2 hx
  have hrk : ∀ γ : GQ W, ((u γ).1 * x₀).rank = W.rank := fun γ => by
    have h1 : IsUnit ((u γ).1 * x₀) := by
      refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (u γ).isUnit).mul hxu
    simpa using Matrix.rank_of_isUnit _ h1
  let e : GQ W → {x : Matrix (Fin W.rank) (Fin W.rank) D.host.E // x.rank = W.rank} :=
    fun γ => ⟨(u γ).1 * x₀, hrk γ⟩
  have he : Function.Injective e := fun γ γ' h => by
    have h1 : (u γ).1 * x₀ = (u γ').1 * x₀ := congrArg Subtype.val h
    have h2 : (u γ).1 = (u γ').1 := by
      have hxi : x₀ * x₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
      calc (u γ).1 = (u γ).1 * x₀ * x₀⁻¹ := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
        _ = (u γ').1 * x₀ * x₀⁻¹ := by rw [h1]
        _ = (u γ').1 := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
    exact Subtype.ext (GlobalTheory.MixModel.mt_injective W (by rw [hu, hu, h2]))
  have hterm : ∀ (γ : GQ W) (h : GA D W), ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ = ‖N (mm (mt W h⁻¹) (rat (e γ).1))‖ₑ := fun γ h => by
    have h1 : (γ⁻¹ • h)⁻¹ = h⁻¹ * γ.1 := by
      change ((γ.1)⁻¹ * h)⁻¹ = _
      rw [mul_inv_rev, inv_inv]
    have h2 : mt W (h⁻¹ * γ.1) = mt W h⁻¹ * mt W γ.1 := rfl
    have h3 : ww W x₀ (γ⁻¹ • h) = mm (mt W h⁻¹) (rat (e γ).1) := by
      simp only [ww, e]
      rw [h1, h2, hu, rat_mul]
      exact Matrix.mul_assoc _ _ _
    rw [h3]
  rw [hfd.lintegral_eq_tsum']
  rw [← lintegral_tsum fun γ => ?_]
  · calc ∫⁻ h in stdDom (GQ W), ∑' γ : GQ W, ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ ∂m
        ≤ ∫⁻ _ in stdDom (GQ W), (C : ℝ≥0∞) ∂m := lintegral_mono fun h => by
          simp only [hterm]
          exact (ENNReal.tsum_comp_le_tsum_of_injective he
            (fun x => ‖N (mm (mt W h⁻¹) (rat x.1))‖ₑ)).trans (hC h)
      _ = C * m (stdDom (GQ W)) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin
  · exact (hfm.comp (measurable_const_smul γ⁻¹)).aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

theorem _root_.GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (x : Fin h → IrrGL (k := k)) (W : List (IrrGL (k := k))) (b : Fin h → Fin W.length → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (W.get j).1) (c : Fin W.length → Fin h), (∀ i j, b i j = if c j = i then (W.get j).1 else 0) → jhMult (piTensor fun j => (W.get j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = ∏ i, jmL (sub W c i) (x i).rep := by
  first | exact @GlobalTheory.CompanionTheory.FineProdCell.jhMult_cell_colour | exact GlobalTheory.CompanionTheory.FineProdCell.jhMult_cell_colour | (intros; apply GlobalTheory.CompanionTheory.FineProdCell.jhMult_cell_colour <;> assumption)
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm


theorem _root_.GlobalTheory.T.torus_element_levi_embedding : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (t : ℝ),
  aT E (r + s) r t = GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s (aT E r r t, 1) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.LevAt.aT_eq_lev | exact GlobalTheory.CompanionTheory.Conc.LevAt.aT_eq_lev | (intros; apply GlobalTheory.CompanionTheory.Conc.LevAt.aT_eq_lev <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.unitary_adelic_iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) ∧ ∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame | exact GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_compact_iwasawa_of_frame <;> assumption)
end
