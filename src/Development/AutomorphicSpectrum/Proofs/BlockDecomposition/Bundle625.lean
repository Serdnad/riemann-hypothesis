module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle616
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle008
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonrepresentedSignatureObstruction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle606
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle610
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle609
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle611
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle612
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
public import Mathlib.MeasureTheory.Group.ModularCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle381
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoordDnApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle613
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle614
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle617
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProduct
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.compact_finite_rational_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (𝒞 : Set (GFin σ J)), IsCompact 𝒞 → ∀ {ι : Type} [Fintype ι] (A : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E), ∃ d : ℕ, 0 < d ∧ ∀ δ : GRat σ J, projFin σ J (ratEmb σ J δ) ∈ 𝒞 → ∀ u v, IsIntegral ℤ ((d : E) * (A * δ.1.1 * B) u v) := by
  first | exact @GlobalTheory.CompanionTheory.CFin.bounded_denominators | exact GlobalTheory.CompanionTheory.CFin.bounded_denominators | (intros; apply GlobalTheory.CompanionTheory.CFin.bounded_denominators <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal


theorem _root_.GlobalTheory.T.rational_points_eq_embedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J), g ∈ ratPts σ J → ∃ η : GRat σ J, g = ratEmb σ J η := by
  first | exact @GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts | exact GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts | (intros; apply GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.coordinate_form_symmetric_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), (coordForm σ b n).IsSymm ∧ (coordForm σ b n).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.free_cell_open_independent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ n : ℕ, IsOpen (freeCell (R ⊗[F] E) M n) ∧ (∀ X ∈ freeCell (R ⊗[F] E) M n, LinearIndependent (R ⊗[F] E) X) ∧ (∀ X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → gramR R σ (hypOne J) X = 0 → IsUnit (X 0 0) → X ∈ freeCell (R ⊗[F] E) M n) ∧ (∀ (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → LinearIndependent (R ⊗[F] E) Y → chartS R σ J x a s Y ∈ freeCell (R ⊗[F] E) M n) ∧ Measurable (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell.freeCell_props | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell.freeCell_props | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell.freeCell_props <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.nonrepresented_signature_obstruction : ∀ (D : D7) (r : ℕ) (V : HSp D), 2 * r < V.rank → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → ∃ (ρ : D.what₂.Tau) (ε : ℝ) (S : Submodule ℂ (Fin r → ℂ)), (ε = 1 ∨ ε = -1) ∧ GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.NonnegOn ε (β.1.map (tauE D ρ)) S ∧ ∀ T : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (gramAt D V ρ) T → Module.finrank ℂ T < Module.finrank ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem IsInt.mul {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s t : Type} [Fintype s]
    {M : Matrix r s (w.adicCompletion E)} {N : Matrix s t (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) :
    IsInt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact (Ov E w).sum_mem fun l _ => (Ov E w).mul_mem (hM i l) (hN l j)

theorem tj_blk (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E)
    (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    Tj ℂ n (Ov E w) ϖ k (blk h w m X) =
      if IsInt w m.1.val ∧ IsInt w m.2.val ∧ IsInt w (m.1.val * X) ∧ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧
        IsInt w (ϖ • (X * (m.2⁻¹).val)) ∧ ordL m.1.val.det + ordL m.2.val.det = (k : ℤ) then 1 else 0 := by
  rw [GlobalTheory.T.hecke_indicator_formula E w n k ϖ hϖ hk]
  refine if_congr ?_ rfl rfl
  rw [GlobalTheory.T.block_integral_iff E n a b h w m X, GlobalTheory.T.block_inverse_integral_iff E n a b h w ϖ m X, GlobalTheory.T.block_det_order_add E n a b h w m X]
  tauto

theorem hint_lat (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E)
    (hϖ : IsUnifV E w ϖ) (i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) (m : GLw a w × GLw b w)
    (i1 : IsInt w m.1.val) (j2 : IsInt w (ϖ • (m.2⁻¹).val))
    (t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0) (t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0) :
    hint (intMat a b w) (fun X => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧
        IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0) = (qV E w : ℂ) ^ (i * (b - j)) := by
  have hle : intSub a b w ≤ latM ϖ m := fun X hX => by
    refine ⟨i1.mul hX, ?_⟩
    have e : ϖ • (X * (m.2⁻¹).val) = X * (ϖ • (m.2⁻¹).val) := (Matrix.mul_smul _ _ _).symm
    rw [e]
    exact IsInt.mul hX j2
  have := GlobalTheory.T.lattice_indicator_integral_index E a b w (latM ϖ m) hle
  rw [GlobalTheory.T.lattice_index_eq_diagonal E a b w ϖ hϖ i j hi hj m t1 t2, GlobalTheory.T.diagonal_lattice_index_pow E a b w ϖ hϖ i j hi hj] at this
  rw [Nat.cast_pow] at this
  have e2 : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      if IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0) =
      fun X => if Multiplicative.toAdd X ∈ latM ϖ m then (1 : ℂ) else 0 :=
    funext fun X => if_congr Iff.rfl rfl rfl
  rw [e2]
  exact this

theorem coef_eq (q : ℕ) (hq : q ≠ 0) (c : ℂˣ) (a b i j : ℕ) (hj : j ≤ b) :
    (c : ℂ) ^ (i * b + j * a) * ((q : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) * (q : ℂ) ^ (i * (b - j))) = coef q c a b i j := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [coef]
  congr 1
  rw [← Complex.cpow_natCast (q : ℂ), ← Complex.cpow_add _ _ hq']
  congr 1
  push_cast [Nat.cast_sub hj]
  ring

theorem hint_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  unfold hint
  rw [finsum_zero, mul_zero]


theorem ct_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (c : ℂˣ)
    (ϖ : w.adicCompletion E) (hw : IsSplitAt w) (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) (m : GLw a w × GLw b w) :
    ctT h w (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c) ϖ k m =
      ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) := by
  rw [GlobalTheory.T.constant_term_hecke_formula E n a b h w _ ϖ hw hϖ k m]
  by_cases hP : ∃ p ∈ pairs a b k, Tj ℂ a (Ov E w) ϖ p.1 m.1 ≠ 0 ∧ Tj ℂ b (Ov E w) ϖ p.2 m.2 ≠ 0
  · obtain ⟨⟨i, j⟩, hp, h1, h2⟩ := hP
    obtain ⟨hij, hi, hj⟩ : i + j = k ∧ i ≤ a ∧ j ≤ b := by
      exact mem_pairs.1 hp
    simp only at h1 h2
    have c1 := GlobalTheory.T.hecke_indicator_formula E w a i ϖ hϖ hi m.1
    have c2 := GlobalTheory.T.hecke_indicator_formula E w b j ϖ hϖ hj m.2
    rw [c1] at h1
    rw [c2] at h2
    obtain ⟨i1, i2, i3⟩ : IsInt w m.1.val ∧ IsInt w (ϖ • (m.1⁻¹).val) ∧ ordL m.1.val.det = (i : ℤ) := by
      by_contra hc; exact h1 (if_neg hc)
    obtain ⟨j1, j2, j3⟩ : IsInt w m.2.val ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ ordL m.2.val.det = (j : ℤ) := by
      by_contra hc; exact h2 (if_neg hc)
    have hfun : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) =
        fun X => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧
          IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0 := by
      funext X
      rw [tj_blk E n a b h w ϖ hϖ k hk m]
      have e : ordL m.1.val.det + ordL m.2.val.det = (k : ℤ) := by rw [i3, j3, ← hij]; push_cast; rfl
      by_cases hX : IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val))
      · rw [if_pos ⟨i1, j1, hX.1, i2, j2, hX.2, e⟩, if_pos hX]
      · rw [if_neg fun hc => hX ⟨hc.2.2.1, hc.2.2.2.2.2.1⟩, if_neg hX]
    have u1 : Tj ℂ a (Ov E w) ϖ i m.1 = 1 := by rw [c1, if_pos ⟨i1, i2, i3⟩]
    have u2 : Tj ℂ b (Ov E w) ϖ j m.2 = 1 := by rw [c2, if_pos ⟨j1, j2, j3⟩]
    have t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 := by rw [u1]; exact one_ne_zero
    have t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 := by rw [u2]; exact one_ne_zero
    rw [hfun, hint_lat E a b w ϖ hϖ i j hi hj m i1 j2 t1 t2, GlobalTheory.T.unramified_character_block_value E a b w c i j m i3 j3, GlobalTheory.T.modulus_half_block_value E a b w i j m i3 j3,
      coef_eq _ (qV_ne_zero w) c a b i j hj, Finset.sum_eq_single_of_mem (⟨i, j⟩ : ℕ × ℕ) hp]
    · simp [u1, u2]
    · rintro ⟨i', j'⟩ hp' hne
      obtain ⟨hij', hi', hj'⟩ : i' + j' = k ∧ i' ≤ a ∧ j' ≤ b := by
        exact mem_pairs.1 hp'
      have : i' ≠ i := fun e => hne (by subst e; congr; omega)
      have u : Tj ℂ a (Ov E w) ϖ i' m.1 = 0 := by
        rw [GlobalTheory.T.hecke_indicator_formula E w a i' ϖ hϖ hi' m.1, if_neg]
        rintro ⟨-, -, e⟩
        exact this (by rw [i3] at e; exact_mod_cast e.symm)
      simp [u]
  · push_neg at hP
    have hz : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) = fun _ => 0 := by
      funext X
      rw [tj_blk E n a b h w ϖ hϖ k hk m, if_neg]
      rintro ⟨i1, j1, -, i2, j2, -, e⟩
      obtain ⟨i, hi, i3⟩ := GlobalTheory.T.det_order_bounded_hecke_support E w a ϖ hϖ m.1 i1 i2
      obtain ⟨j, hj, j3⟩ := GlobalTheory.T.det_order_bounded_hecke_support E w b ϖ hϖ m.2 j1 j2
      have hp : (⟨i, j⟩ : ℕ × ℕ) ∈ pairs a b k := by
        have : i + j = k := by rw [i3, j3] at e; exact_mod_cast e
        exact mem_pairs.2 ⟨this, hi, hj⟩
      have t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 := by
        rw [GlobalTheory.T.hecke_indicator_formula E w a i ϖ hϖ hi m.1, if_pos ⟨i1, i2, i3⟩]; exact one_ne_zero
      have t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 := by
        rw [GlobalTheory.T.hecke_indicator_formula E w b j ϖ hϖ hj m.2, if_pos ⟨j1, j2, j3⟩]; exact one_ne_zero
      exact t2 (hP (i, j) hp t1)
    have hs : ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      by_cases t1 : Tj ℂ a (Ov E w) ϖ p.1 m.1 = 0
      · simp [t1]
      · simp [hP p hp t1]
    rw [hz, hs, hint_zero, mul_zero, mul_zero]

theorem ctSat : CtSat := by
  intro E _ _ _ n a b h w ν c V _ _ ρ x Ba Bb hw hν hs ϖ hϖ k hk
  subst hν
  have hF : ctT h w (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c) ϖ k = fun m =>
      ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) :=
    funext fun m => ct_eq E n a b h w c ϖ hw hϖ k hk m
  rw [hF, GlobalTheory.T.hecke_vector_linear_combination E a b w ϖ hϖ, GlobalTheory.T.satake_eigenvalue_pair_decomposition _ n a b c Ba Bb (qV_ne_zero w) h hs.2.1 hs.2.2.1 k hk, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨-, hi, hj⟩ : p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by
    exact mem_pairs.1 hp
  rw [hs.2.2.2 ϖ hϖ p.1 hi p.2 hj, smul_smul]

end GlobalTheory.CompanionTheory.CtS
end
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def levPair : GA D W × GL (Fin t) (AE D) →* levM d where
  toFun p := ⟨⟨d.emb0 p.1 * d.levi p.2, mul_mem (GlobalTheory.GodementSectionReduction.wittCoreEmbedding_mem_isotropicStabilizer d _) (GlobalTheory.RegSW.levi_mem d _)⟩, p.1, p.2, rfl⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' p q := Subtype.ext (Subtype.ext (by
    show d.emb0 (p.1 * q.1) * d.levi (p.2 * q.2) = d.emb0 p.1 * d.levi p.2 * (d.emb0 q.1 * d.levi q.2)
    rw [map_mul, map_mul]
    calc d.emb0 p.1 * d.emb0 q.1 * (d.levi p.2 * d.levi q.2)
        = d.emb0 p.1 * (d.emb0 q.1 * d.levi p.2) * d.levi q.2 := by group
      _ = d.emb0 p.1 * (d.levi p.2 * d.emb0 q.1) * d.levi q.2 := by rw [d.wittHyperbolic_anisotropic_commute_levi]
      _ = _ := by group))

theorem coe_levPair (p : GA D W × GL (Fin t) (AE D)) :
    (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) = d.emb0 p.1 * d.levi p.2 := rfl

theorem mt_eq_of_levPair (p : GA D W × GL (Fin t) (AE D)) :
    d.p0 ⬝ (mt B (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.j0) = mt W p.1 := by
  rw [coe_levPair, mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul]

theorem onX_levPair (p : GA D W × GL (Fin t) (AE D)) :
    GlobalTheory.RegSW.onX d ((levPair d p : levM d) : GlobalTheory.RegSW.stab d) = p.2 := by
  have h : mt B (((levPair d p : levM d) : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.jX = d.jX ⬝ p.2.1 := by
    rw [coe_levPair, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  exact Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d _)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)

theorem levPair_bijective : Function.Bijective (levPair d) := by
  constructor
  · intro p q h
    refine Prod.ext (mt_injective W ?_) ?_
    · rw [← mt_eq_of_levPair d p, ← mt_eq_of_levPair d q, h]
    · rw [← onX_levPair d p, ← onX_levPair d q, h]
  · rintro ⟨⟨q, hq⟩, g, a, e⟩
    exact ⟨(g, a), Subtype.ext (Subtype.ext e.symm)⟩

def levEquiv : (GA D W × GL (Fin t) (AE D)) ≃* levM d := MulEquiv.ofBijective (levPair d) (levPair_bijective d)

theorem continuous_levEquiv : Continuous (levEquiv d) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have h : Continuous fun p : GA D W × GL (Fin t) (AE D) => d.emb0 p.1 * d.levi p.2 :=
    (d.continuous_embed.comp continuous_fst).mul (d.continuous_levi.comp continuous_snd)
  exact (h.subtype_mk _).subtype_mk _

theorem continuous_levEquiv_symm : Continuous (levEquiv d).symm := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hv : Continuous fun m : levM d => ((m : GlobalTheory.RegSW.stab d) : GA D B) :=
    continuous_subtype_val.comp continuous_subtype_val
  refine Continuous.prodMk (continuous_of_mt W ?_) ?_
  · have hc : Continuous fun m : levM d => d.p0 ⬝ (mt B ((m : GlobalTheory.RegSW.stab d) : GA D B) ⬝ d.j0) :=
      continuous_const.matrix_mul (((continuous_mt B).comp hv).matrix_mul continuous_const)
    refine hc.congr fun m => ?_
    have := mt_eq_of_levPair d ((levEquiv d).symm m)
    rwa [show levPair d ((levEquiv d).symm m) = m from (levEquiv d).apply_symm_apply m] at this
  · refine ((GlobalTheory.RegSW.continuous_onX d).comp continuous_subtype_val).congr fun m => ?_
    have := onX_levPair d ((levEquiv d).symm m)
    rwa [show levPair d ((levEquiv d).symm m) = m from (levEquiv d).apply_symm_apply m] at this

end GlobalTheory.CompanionTheory.QKAvg

theorem GlobalTheory.CompanionTheory.QKAvg.exists_haar_of_prod {G₁ G₂ M : Type} [Group G₁] [Group G₂] [Group M] [TopologicalSpace G₁]
    [TopologicalSpace G₂] [TopologicalSpace M] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [IsTopologicalGroup M]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂] [SecondCountableTopology G₁] [SecondCountableTopology G₂]
    [T2Space G₂] [MeasurableSpace G₁] [BorelSpace G₁] [MeasurableSpace M] [BorelSpace M]
    (e : (G₁ × G₂) ≃* M) (he : Continuous e) (he' : Continuous e.symm)
    (h₁ : ∀ μ : Measure G₁, μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (h₂ : ∀ a : G₂, Measure.modularCharacterFun a = 1) :
    ∃ νM : Measure M, νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  borelize G₂
  haveI hr1 : (Measure.haar : Measure G₁).IsMulRightInvariant := h₁ _ inferInstance
  haveI hr2 : (Measure.haar : Measure G₂).IsMulRightInvariant := GlobalTheory.ParAvg.isMulRightInvariant_of_modular _ h₂
  obtain ⟨ν, hνH, hνR⟩ : ∃ ν : Measure (G₁ × G₂), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant :=
    ⟨(Measure.haar : Measure G₁).prod Measure.haar, inferInstance, inferInstance⟩
  refine ⟨Measure.map e ν, MulEquiv.isHaarMeasure_map ν e he he', ⟨fun m => ?_⟩⟩
  obtain ⟨p, rfl⟩ := e.surjective m
  rw [Measure.map_map (measurable_mul_const _) he.measurable]
  have h : (fun x => x * e p) ∘ e = e ∘ fun x => x * p := by
    funext x; simp [map_mul]
  rw [h, ← Measure.map_map he.measurable (measurable_mul_const _), map_mul_right_eq_self]



theorem GlobalTheory.CompanionTheory.QKAvg.top_GL (D : D7) (t : ℕ) : LocallyCompactSpace (GL (Fin t) (AE D)) ∧
    SecondCountableTopology (GL (Fin t) (AE D)) ∧ T2Space (GL (Fin t) (AE D)) := by
  obtain ⟨-, m2, m3, m4, -⟩ := lattice_Mx D t t
  haveI : LocallyCompactSpace (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : T2Space (Mx D t t)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.t2Space
  haveI : T1Space (Mx D t t) := @T2Space.t1Space _ _ m4
  exact ⟨(Units.isClosedEmbedding_embedProduct (α := Mx D t t)).locallyCompactSpace,
    (Units.isEmbedding_embedProduct (M := Mx D t t)).secondCountableTopology,
    (Units.isEmbedding_embedProduct (M := Mx D t t)).t2Space⟩

theorem GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (levM d)],
    ∃ νM : Measure (levM d), νM.IsHaarMeasure ∧ νM.IsMulRightInvariant := by
  intro D B W t d _
  obtain ⟨g1, g2, g3, g4, g5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨l1, l2, l3⟩ := GlobalTheory.CompanionTheory.QKAvg.top_GL D t
  exact GlobalTheory.CompanionTheory.QKAvg.exists_haar_of_prod (levEquiv d) (continuous_levEquiv d) (continuous_levEquiv_symm d)
    (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D W) (GlobalTheory.T.modularCharacter_adelic_GL_eq_one D t)
end
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.absDet_unipotent_radical_eq_one : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), ∀ n ∈ radN d, GlobalTheory.RegSW.absDet d n = 1 := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.absDet_radN | exact GlobalTheory.CompanionTheory.QKAvg.absDet_radN | (intros; apply GlobalTheory.CompanionTheory.QKAvg.absDet_radN <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isClosed_unipotent_radical_stabilizer : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), IsClosed (radN d : Set (GlobalTheory.RegSW.stab d)) := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.isClosed_radN | exact GlobalTheory.CompanionTheory.QKAvg.isClosed_radN | (intros; apply GlobalTheory.CompanionTheory.QKAvg.isClosed_radN <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_radical_inf_levi_trivial : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), ∀ x, x ∈ radN d → x ∈ levM d → x = 1 := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM | exact GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM | (intros; apply GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_radical_stabilizer_property : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), IsClosed (levM d : Set (GlobalTheory.RegSW.stab d)) := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.isClosed_levM | exact GlobalTheory.CompanionTheory.QKAvg.isClosed_levM | (intros; apply GlobalTheory.CompanionTheory.QKAvg.isClosed_levM <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_radical_haar_from_product : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] (κ : Measure (skewA D t)) (β : Measure (Mx D t W.rank)), κ.IsAddHaarMeasure → β.IsAddHaarMeasure → ∃ Ψ : (skewA D t × Mx D t W.rank) ≃ₜ radN d, (∀ p, (((Ψ p : GlobalTheory.RegSW.stab d) : GA D B)) = d.nC p.1 * d.nB p.2) ∧ ((κ.prod β).map Ψ).IsHaarMeasure ∧ ((κ.prod β).map Ψ).IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord | exact GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord | (intros; apply GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord <;> assumption)
end
