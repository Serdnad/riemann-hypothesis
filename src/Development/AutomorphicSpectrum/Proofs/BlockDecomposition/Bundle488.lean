module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle457
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle458
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle460
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core


theorem _root_.GlobalTheory.T.pairing_on_rational_tuple_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψf : Af F → ℂ) (c : hermE σ n) (c₀ : Fin n) (i₀ : Fin M) (x : Af F ⊗[F] E) (s : ℕ)
      (ρ : Fin M → Fin n → 𝓞 E),
    pairB σ J ψf (hermIn (Af F) σ n c) (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ) =
      ψf (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle.pair_single | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle.pair_single | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle.pair_single <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField


theorem _root_.GlobalTheory.T.hermitian_finite_adeles_dense_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField


theorem _root_.GlobalTheory.T.summable_periodic_bound_by_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Λ : AddSubgroup (hermE σ n)) (t : F), t ≠ 0 → ∀ τ : ℕ, 0 < τ →
    (∀ c ∈ hermO σ n, ((τ : F) / t) • c ∈ Λ) →
    ∀ g : hermE σ n → ℝ, (∀ c, 0 ≤ g c) → (∀ c, ∀ l ∈ Λ, g (c + l) = g c) →
    ∀ C s : ℝ, (∀ c, g c ≤ C * (delta (t • c).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ Λ => g (Quotient.out x)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.summable_quot_of_le_delta_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.summable_quot_of_le_delta_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.summable_quot_of_le_delta_rpow <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField


theorem _root_.GlobalTheory.T.scaled_integral_hermitian_in_open_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.chart_gram_first_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 0 = hR R σ (hypOne J) (x 0) (x 0) ∧ (∀ j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 j.succ = s 0 j) ∧ ∀ i j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) i.succ j.succ = gramR R σ J Y i j + (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j - hR R σ (hypOne J) (x 0) (x 0) * (sigR R σ (a 0 i) * a 0 j)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS | exact GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.unitary_moving_unit_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (x : Fin (M + 2) → R ⊗[F] E), IsUnit (x 0) → ∃ g : HA R σ (hypOne J), ∀ v : Fin (M + 2) → R ⊗[F] E, ((HA.mat R σ (hypOne J) g : GL (Fin (M + 2)) (R ⊗[F] E)) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary | exact GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary <;> assumption)
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapStable

theorem qdet_mem {a : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (X : Fin a → Fin a → A)
    (h : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

def blockM {R : Type} [CommRing R] {r s : ℕ} (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    Matrix (Fin (r + s)) (Fin (r + s)) R :=
  Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (fromBlocks A 0 0 B)

theorem val_lev {R : Type} [CommRing R] {r s : ℕ} (g : GL (Fin r) R × GL (Fin s) R) :
    (lev R r s g).val = blockM g.1.val g.2.val :=
  GlobalTheory.SmGL.val_emb₂ R _ g

theorem blockM_map {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    (blockM A B).map p = blockM (A.map p) (B.map p) := by
  ext i j
  simp only [blockM, Matrix.map_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem map_lev {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (g : GL (Fin r) R × GL (Fin s) R) :
    Matrix.GeneralLinearGroup.map p (lev R r s g) =
      lev S r s (Matrix.GeneralLinearGroup.map p g.1, Matrix.GeneralLinearGroup.map p g.2) := by
  apply Units.ext
  change (lev R r s g).val.map p = (lev S r s _).val
  rw [val_lev, val_lev, blockM_map]
  rfl

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem infGL_lev (y : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)) :
    infGL E (r + s) (lev (Cinf E) r s y) = lev (Ad E) r s (infGL E r y.1, infGL E s y.2) := by
  refine ga_ext ?_ ?_
  · rw [map_lev]; simp
  · rw [map_lev]; simp only [pFin_infGL, pFin_infGL]; exact (map_one _).symm

theorem blockM_add {R : Type} [CommRing R] {r s : ℕ} (A A' : Matrix (Fin r) (Fin r) R)
    (B B' : Matrix (Fin s) (Fin s) R) : blockM A B + blockM A' B' = blockM (A + A') (B + B') := by
  ext i j
  simp only [blockM, Matrix.add_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem blockM_smul {R : Type} [CommRing R] {r s : ℕ} (t : ℝ) [Module ℝ R] (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin s) (Fin s) R) : t • blockM A B = blockM (t • A) (t • B) := by
  ext i j
  simp only [blockM, Matrix.smul_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem one_add_smul_blockM (t : ℝ) (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    1 + t • blockM X₁ X₂ = blockM (1 + t • X₁) (1 + t • X₂) := by
  have h1 : (1 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) = blockM 1 1 := by
    simp [blockM, fromBlocks_one]
  rw [h1, blockM_smul, blockM_add]

theorem lieD_block {F : Sm E (r + s)} (hF : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0)
    (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) (m : GA E r × GA E s) :
    lieD (toL (blockM X₁ X₂)) F.1 (lev (Ad E) r s m) = 0 := by
  set g := lev (Ad E) r s m with hg
  set X : Lie E (r + s) := toL (blockM X₁ X₂) with hX
  let c : ℝ → Lie E (r + s) := fun t => oneL E (r + s) + t • X
  have hc : HasDerivAt c X 0 :=
    (((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul ℝ X)
  have h0 : c 0 = oneL E (r + s) := by simp [c]
  have hd : HasFDerivAt (chart F.1 g) (fderiv ℝ (chart F.1 g) (oneL E (r + s))) (c 0) := by
    rw [h0]; exact (differentiableAt_chart F.2 g).hasFDerivAt
  have h2 := hd.comp_hasDerivAt (0 : ℝ) hc
  have ev : ∀ (n : ℕ) (Y : Lie E n), ∀ᶠ t : ℝ in 𝓝 0, oneL E n + t • Y ∈ invSet E n := by
    intro n Y
    have hcont : Continuous fun t : ℝ => oneL E n + t • Y := by fun_prop
    refine hcont.continuousAt.eventually_mem (isOpen_invSet.mem_nhds ?_)
    simp only [zero_smul, add_zero]
    change IsUnit (Matrix.of (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) (Cinf E))))
    rw [Equiv.apply_symm_apply]
    exact isUnit_one
  have hz : (chart F.1 g ∘ c) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ev r (toL X₁), ev s (toL X₂)] with t h1 h2
    obtain ⟨u₁, hu₁⟩ := h1
    obtain ⟨u₂, hu₂⟩ := h2
    have e : c t = toL (lev (Cinf E) r s (u₁, u₂)).val := by
      rw [val_lev]
      change c t = toL (blockM u₁.val u₂.val)
      rw [hu₁, hu₂]
      exact one_add_smul_blockM t X₁ X₂
    rw [Function.comp_apply, e, chart_val, infGL_lev, hg, ← map_mul]
    exact hF _
  exact h2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)


variable (E r s) in
def vanAlg : Subalgebra ℂ (Module.End ℂ (Sm E (r + s))) where
  carrier := {z | ∀ F : Sm E (r + s), (∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
    ∀ m : GA E r × GA E s, (z F).1 (lev (Ad E) r s m) = 0}
  mul_mem' hx hy F hF := hx _ (hy F hF)
  add_mem' {x y} hx hy F hF m := by
    change (x F).1 _ + (y F).1 _ = 0
    rw [hx F hF m, hy F hF m, add_zero]
  algebraMap_mem' c F hF m := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hF m, smul_zero]

theorem Eop_mem_of {a : ℕ} (S : Subalgebra ℂ (Module.End ℂ (Sm E a))) (τ : E →+* ℂ) (p q : Fin a)
    (h : ∀ x, lieS E a p q x ∈ S) : Eop τ p q ∈ S :=
  S.smul_mem (S.sub_mem (h _) (S.smul_mem (h _) _)) _

theorem lie_block_mem (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    lie E (r + s) (toL (blockM X₁ X₂)) ∈ vanAlg E r s :=
  fun _ hF m => lieD_block hF X₁ X₂ m

theorem single_castAdd (i j : Fin r) (x : Cinf E) :
    Matrix.single (Fin.castAdd s i) (Fin.castAdd s j) x = blockM (Matrix.single i j x) (0 : Matrix (Fin s) (Fin s) (Cinf E)) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hc, hc]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

theorem single_natAdd (i j : Fin s) (x : Cinf E) :
    Matrix.single (Fin.natAdd r i) (Fin.natAdd r j) x = blockM (0 : Matrix (Fin r) (Fin r) (Cinf E)) (Matrix.single i j x) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hn, hn]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

theorem capR_mem (τ : E →+* ℂ) (u : ℂ) : capR r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_castAdd]; exact lie_block_mem _ _) _

theorem capS_mem (τ : E →+* ℂ) (u : ℂ) : capS r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_natAdd]; exact lie_block_mem _ _) _


variable (E) in
def nInvAlg (a r : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E a)) where
  carrier := {z | ∀ ψ : Sm E a, (∀ (x : BlockIx a r → Ad E) (g : GA E a), ψ.1 (unip x * g) = ψ.1 g) →
    ∀ (x : BlockIx a r → Ad E) (g : GA E a), (z ψ).1 (unip x * g) = (z ψ).1 g}
  mul_mem' hx hy ψ hψ := hx _ (hy ψ hψ)
  add_mem' {x y} hx hy ψ hψ v g := by
    change (x ψ).1 _ + (y ψ).1 _ = (x ψ).1 _ + (y ψ).1 _
    rw [hx ψ hψ v g, hy ψ hψ v g]
  algebraMap_mem' c ψ hψ v g := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hψ v g]

theorem lie_mem_nInvAlg (a r : ℕ) (X : Lie E a) : lie E a X ∈ nInvAlg E a r := by
  intro ψ hψ v g
  have e : chart ψ.1 (unip v * g) = chart ψ.1 g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, hψ v]
    · rfl
  simp only [GlobalTheory.CuspRep.lie_apply, lieD, e]

theorem cap_mem_nInvAlg (a r : ℕ) (τ : E →+* ℂ) (u : ℂ) : cap (a := a) τ u ∈ nInvAlg E a r :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => lie_mem_nInvAlg a r _) _

theorem capStable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (F : Sm E (r + s)) :
    ((∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
      (∀ m : GA E r × GA E s, (capR r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
        ∀ m : GA E r × GA E s, (capS r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
    ((∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
      ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)),
        (cap (a := r + s) τ u F).1 (unip x * g) = (cap (a := r + s) τ u F).1 g) :=
  ⟨fun hF => ⟨capR_mem τ u F hF, capS_mem τ u F hF⟩, fun hF => cap_mem_nInvAlg (r + s) r τ u F hF⟩

end GlobalTheory.CompanionTheory.CTFin.CapStable

end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory


theorem _root_.GlobalTheory.T.hermRep_twisted_bundle_exists : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (c : Fin m) (t : ℤ), Nonempty (LBIso M.B (twB m n c t)) → ∃ A : Geo.HermLine (Bk n), IsHermRep M A ∧ A.a = Pi.single c.succ 1 + t • Pi.single 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB | exact GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB | (intros; apply GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB <;> assumption)
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.Orbit

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_mem_blockChart (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) :
    ∃ i, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) :=
  ⟨ptChart _ k, GlobalTheory.CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩

theorem exists_ne_zero_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (k : Fin (m + 1)) : ∃ i, z ⟨k, i⟩ ≠ 0 :=
  (exists_mem_blockChart w k).imp fun i hi => (h k i).1.1 hi

theorem sameOrbit_of_isUnder {w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀} {z z' : (Σ k, Bk n k) → ℂ}
    (h : IsUnder w z) (h' : IsUnder w z') : SameOrbit z z' := by
  choose c hc using exists_mem_blockChart w
  refine ⟨fun k => z ⟨k, c k⟩ / z' ⟨k, c k⟩,
    fun k => div_ne_zero ((h k _).1.1 (hc k)) ((h' k _).1.1 (hc k)), ?_⟩
  funext ⟨k, j⟩
  have e := ((h k (c k)).2 j (hc k)).symm.trans ((h' k (c k)).2 j (hc k))
  have a := (h k _).1.1 (hc k)
  have b := (h' k _).1.1 (hc k)
  rw [div_eq_div_iff a b] at e
  show z ⟨k, j⟩ = z ⟨k, c k⟩ / z' ⟨k, c k⟩ * z' ⟨k, j⟩
  rw [div_mul_eq_mul_div, eq_div_iff b]
  linear_combination e

theorem eq_iff_sameOrbit (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y y' : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ)
    (h : IsUnder (PtsOver.map i rfl _ y) z) (h' : IsUnder (PtsOver.map i rfl _ y') z') :
    y = y' ↔ SameOrbit z z' := by
  constructor
  · rintro rfl
    exact sameOrbit_of_isUnder h h'
  · intro ho
    have e := (Under.existsUnique_isUnder m n z (exists_ne_zero_of_isUnder h)).unique h
      (isUnder_of_sameOrbit m n _ z' z h' ho)
    exact Subtype.ext ((cancel_mono i).1 (congrArg Subtype.val e))

end GlobalTheory.CompanionTheory.MixZ.Orbit
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem _root_.GlobalTheory.T.isUnder_of_same_orbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder w z → SameOrbit z' z → IsUnder w z' := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Orbit.isUnder_of_sameOrbit | exact GlobalTheory.CompanionTheory.MixZ.Orbit.isUnder_of_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.MixZ.Orbit.isUnder_of_sameOrbit <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.lattice_sum_shift_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s),
    ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 (y₁ + rat p₀) (y₂ + rat q₀) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂ := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat | exact GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Period.tsum_cellTerm_add_rat <;> assumption)
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.idempotents_coarsen_to_lower_level : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (r : ℕ → t.A), (∀ m, r (m + 1) ^ l = r m) →
  ∀ {m n : ℕ} (h : m ≤ n) (e : ZMod (l ^ n) → t.A), CompleteOrthogonalIdempotents e →
  (∀ c, t.sharp (e c) * (t.sharp (r n) - t.sharp (t.s (ε.e n)) ^ c.val) = 0) →
  CompleteOrthogonalIdempotents (fun c : ZMod (l ^ m) => ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') ∧
  ∀ c : ZMod (l ^ m), t.sharp (∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') * (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.coi_descend | exact GlobalTheory.CompanionTheory.ContUniv.coi_descend | (intros; apply GlobalTheory.CompanionTheory.ContUniv.coi_descend <;> assumption)
end
