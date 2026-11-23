module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle252
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle481
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle647
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle654
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle576
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle655
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle648
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFibreFreeExtension
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle499
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WSum

theorem integrable_schwartzA_haar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n))
    [μ.IsAddHaarMeasure] (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n → Integrable φ μ := by
  intro D θ hθ m n μ _ φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    haveI : IsModuleTopology (Af D.host.F) (GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (GlobalTheory.RegSch.IkSchwartz.AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
    haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
    obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
    haveI : LocallyCompactSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isClosedEmbedding.locallyCompactSpace
    haveI : SecondCountableTopology (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.secondCountableTopology
    haveI : T2Space (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isEmbedding.t2Space
    letI : MeasurableSpace (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := borel _
    haveI : BorelSpace (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
    haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
    haveI := (GlobalTheory.TowerRestrict.lattice_Mx D m n).1
    obtain ⟨e, he⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ m n
    let μr : Measure (D.what₂.Tau → Fin m → Fin n → ℂ) := Measure.addHaar
    let ν : Measure (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := Measure.addHaar
    obtain ⟨c, hc⟩ := GlobalTheory.PartialIntegral.exists_integral_split e μ μr ν
    have h := (hc f g (f.integrable) (hg.1.continuous.integrable_of_hasCompactSupport hg.2)).1
    simpa only [he] using h
  | zero => exact integrable_zero _ _ _
  | add φ ψ _ _ h1 h2 => exact h1.add h2
  | smul c φ _ h => exact h.smul c

end GlobalTheory.CompanionTheory.WSum

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.CuspRep
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem v_thetaGL_apply (w : Pl E) (a : ℕ) (g : GLw a w) (i j : Fin a) :
    Valued.v ((thetaGL a (cj w) g).val i j) = Valued.v ((g⁻¹).val j.rev i.rev) := by
  rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, GlobalTheory.PrincCong.v_cj, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]

theorem thetaGL_mem_KGL (w : Pl E) (a : ℕ) {k : GLw a w} (hk : k ∈ GlobalTheory.LFun.KGL w (n := a)) :
    thetaGL a (cj w) k ∈ GlobalTheory.LFun.KGL w (n := a) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff w a k).1 hk
  refine (GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff w a _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [v_thetaGL_apply]
    exact h2 _ _
  · rw [← map_inv, v_thetaGL_apply, inv_inv]
    exact h1 _ _

theorem thetaGL_mem_iwGL (w : Pl E) (a : ℕ) {k : GLw a w} (hk : k ∈ iwGL a w) :
    thetaGL a (cj w) k ∈ iwGL a w := by
  obtain ⟨h1, h2, -⟩ := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a k).1).1 hk
  obtain ⟨-, -, h3⟩ := ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a k⁻¹).1).1 (inv_mem hk)
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w a _).1).2 ⟨fun i j => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [v_thetaGL_apply]
    exact h2 _ _
  · rw [← map_inv, v_thetaGL_apply, inv_inv]
    exact h1 _ _
  · rw [v_thetaGL_apply]
    exact h3 _ _ (Fin.rev_lt_rev.2 hij)

theorem isCompact_support_dcos (w : Pl E) (a : ℕ) (t : GLw a w) :
    IsCompact {g : GLw a w | dcos a w t g ≠ 0} := by
  have hI : IsCompact (iwGL a w : Set (GLw a w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin a)
  have hS : IsCompact ((fun p : GLw a w × GLw a w => p.1 * t * p.2) ''
      ((iwGL a w : Set (GLw a w)) ×ˢ (iwGL a w : Set (GLw a w)))) :=
    (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  convert hS using 1
  ext g
  simp only [Set.mem_setOf_eq, dcos, Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists]
  constructor
  · intro h
    by_contra hn
    refine h (if_neg ?_)
    rintro ⟨x, hx, y, hy, rfl⟩
    exact hn ⟨x, y, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    rw [if_pos ⟨x, hx, y, hy, rfl⟩]
    exact one_ne_zero

end GlobalTheory.CompanionTheory.IwFacts
end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology


theorem _root_.GlobalTheory.T.cuspidal_constant_term_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g) → Continuous φ → IsCuspidal σ J φ → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), 0 < k → GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ (g : GAd σ J) (e : ℝ), (∀ m ∈ unipRad σ J Cc, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.norm_le_of_unipRad_variation | exact GlobalTheory.CompanionTheory.RapidDecay.norm_le_of_unipRad_variation | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.norm_le_of_unipRad_variation <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology


theorem _root_.GlobalTheory.T.unipotent_radical_compact_fundamental_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ W ∈ 𝓝 (1 : GFin σ J), ∃ Q : Set (GAd σ J), IsCompact Q ∧ ∀ m ∈ unipRad σ J Cc, ∃ γ ∈ ratPts σ J, ∃ q ∈ Q, q ∈ unipRad σ J Cc ∧ projFin σ J q ∈ W ∧ m = γ * q := by
  first | exact @GlobalTheory.CompanionTheory.StrongUnip.strong_approx_unipRad | exact GlobalTheory.CompanionTheory.StrongUnip.strong_approx_unipRad | (intros; apply GlobalTheory.CompanionTheory.StrongUnip.strong_approx_unipRad <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwUFacts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_cj (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

end GlobalTheory.CompanionTheory.IwUFacts
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.PRep
open GlobalTheory.CuspRep Formalism.BasicNotions
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.InvDoubleCoset

section Generic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def wJ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) : GL (Fin n) L :=
  ⟨antiJ L n, antiJ L n, GlobalTheory.UnitarySwap.antiJ_mul_self, GlobalTheory.UnitarySwap.antiJ_mul_self⟩

theorem cT_antiJ (σ : L →+* L) : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, antiJ]
  by_cases h : i.val + j.val + 1 = n
  · rw [if_pos h, if_pos (by omega)]; simp
  · rw [if_neg h, if_neg (by omega)]; simp

theorem wJ_mem_GU (σ : L →+* L) : wJ L n ∈ GU σ n := by
  change cT σ (antiJ L n) * antiJ L n * antiJ L n = antiJ L n
  rw [cT_antiJ, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]

theorem wJ_mem_GLint (O : Subring L) : wJ L n ∈ GLint (Fin n) O := by
  have h : ∀ i j, antiJ L n i j ∈ O := fun i j => by
    simp only [antiJ]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  exact GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨h, h⟩

theorem wJ_conj_diag {σ : L →+* L} {ϖ : L} (hϖ : σ ϖ = ϖ) (d : Fin n → ℤ) (t : GU σ n)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) : wJ L n * t.1 * wJ L n = (t.1)⁻¹ := by
  have h0 : cT σ t.1.1 * antiJ L n * t.1.1 = antiJ L n := t.2
  have hc : cT σ t.1.1 = t.1.1 := by
    rw [ht]
    ext i j
    by_cases h : i = j
    · subst h
      simp [cT, map_zpow₀, hϖ]
    · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [hc] at h0
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  change antiJ L n * t.1.1 * antiJ L n * t.1.1 = 1
  calc antiJ L n * t.1.1 * antiJ L n * t.1.1 = antiJ L n * (t.1.1 * antiJ L n * t.1.1) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h0, GlobalTheory.UnitarySwap.antiJ_mul_self]

end Generic

theorem inv_mem_doubleCoset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (g : UL n w),
      ∃ k₁ ∈ KL n w, ∃ k₂ ∈ KL n w, g⁻¹ = k₁ * g * k₂ := by
  intro E _ _ _ hU w hw n g
  obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hUI (B := 1) (one_mem _) (cT_one _)
  have hb' : cT (cj w) b.val * b.val = antiJ _ n := by simpa using hb
  have hconj : ∀ x : GLw n w, b * x * b⁻¹ ∈ UL n w ↔ x ∈ UJ (cj w) (antiJ _ n) := fun x => by
    rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.conj_mem_UJ_one_iff _ b x hb'
  have hback : b⁻¹ * g.1 * b ∈ UJ (cj w) (antiJ _ n) :=
    (hconj _).1 (by rw [show b * (b⁻¹ * g.1 * b) * b⁻¹ = g.1 by group]; exact g.2)
  have hbi := (GlobalTheory.LFun.KGL w (n := n)).inv_mem hbK
  have hO : Ov E w = intL (w.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  have hKU : ∀ k ∈ KU (cj w) n, (k.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) := fun k hk => by
    have h : k.1 ∈ intPts (intL (w.adicCompletion E)).subtype (GU (cj w) n) := Subgroup.mem_subgroupOf.1 hk
    show k.1 ∈ (bc (Ov E w).subtype).range
    rw [hO]
    exact (Subgroup.mem_inf.1 h).2
  obtain ⟨d, t, ht, k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.ChainOnto.CayleyVac.exists_cartanU hUI ⟨_, hback⟩
  have e' : b⁻¹ * g.1 * b = k₁.1 * t.1 * k₂.1 := congrArg Subtype.val e
  have hinv : (t.1)⁻¹ = wJ _ n * t.1 * wJ _ n := (wJ_conj_diag hUI.2.2.1 d t ht).symm

  set c : GLw n w := (k₂.1 : GLw n w)⁻¹ * wJ _ n * (k₁.1 : GLw n w)⁻¹ with hc
  have hcU : c ∈ UJ (cj w) (antiJ _ n) :=
    mul_mem (mul_mem (inv_mem k₂.2) (wJ_mem_GU _)) (inv_mem k₁.2)
  have hcK : c ∈ GlobalTheory.LFun.KGL w (n := n) :=
    mul_mem (mul_mem (inv_mem (hKU k₂ hk₂)) (wJ_mem_GLint _)) (inv_mem (hKU k₁ hk₁))
  have hx : b * c * b⁻¹ ∈ UL n w := (hconj _).2 hcU
  have hxK : (⟨b * c * b⁻¹, hx⟩ : UL n w) ∈ KL n w :=
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK hcK) hbi)
  refine ⟨_, hxK, _, hxK, Subtype.ext ?_⟩
  show (g.1)⁻¹ = b * c * b⁻¹ * g.1 * (b * c * b⁻¹)
  have hg : g.1 = b * (k₁.1 * t.1 * k₂.1) * b⁻¹ := by
    rw [← e']
    group
  have hti : (k₁.1 * t.1 * k₂.1 : GLw n w)⁻¹ = c * (k₁.1 * t.1 * k₂.1) * c := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hinv, hc]
    group
  calc (g.1)⁻¹ = b * (k₁.1 * t.1 * k₂.1 : GLw n w)⁻¹ * b⁻¹ := by
        rw [hg]
        group
    _ = b * c * b⁻¹ * g.1 * (b * c * b⁻¹) := by
        rw [hti, hg]
        group

end GlobalTheory.CompanionTheory.InvDoubleCoset
end
end

section

open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.ChartSymm

theorem continuous_mat {D : D7} {n : ℕ} : Continuous (mat : G D n → Mx D (n + n) (n + n)) := by
  unfold GlobalTheory.StdUnn.mat
  exact Continuous.comp' Units.continuous_val continuous_induced_dom

private theorem gram_conjTranspose_eq_self {D : D7} (S : HSp D) :
    (Formalism.BasicNotions.HSpace.gram S).conjTranspose = Formalism.BasicNotions.HSpace.gram S := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Formalism.BasicNotions.HSpace.gram]
  exact S.herm.eq (S.frame j) (S.frame i)

private theorem fromRows_gram_mul_fromCols_eq_one_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : D.host.E)
    (hμ : μ ≠ 0) :
    Matrix.fromRows (d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S)
        (μ⁻¹ • (d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S)) *
      Matrix.fromCols d.e (μ • d.e') = 1 := by
  have h1 : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 1 := d.e'e
  have h0 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 0 := d.ee
  have h0' : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 0 := d.e'e'
  have h2 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 1 := by
    have h := congrArg Matrix.conjTranspose h1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose_eq_self,
      Matrix.conjTranspose_one] at h
    rw [Matrix.mul_assoc]
    exact h
  rw [Matrix.fromRows_mul_fromCols]
  simp only [Matrix.mul_smul, Matrix.smul_mul, h1, h0, h0', h2, smul_zero, smul_smul,
    inv_mul_cancel₀ hμ, mul_inv_cancel₀ hμ, one_smul, Matrix.fromBlocks_one]

theorem continuous_symm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ (κ : GA D (dblSp A) ≃* G D A.rank), IsChart A μ κ →
    Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hL : ((Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id) * Tm A μ = 1 := by
    show _ * (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e')).submatrix id finSumFinEquiv.symm = 1
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, fromRows_gram_mul_fromCols_eq_one_of_hypDec _ μ hμ.1,
      Matrix.submatrix_one_equiv]
  have hR := mul_eq_one_comm.mp hL
  set L := (Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id with hLdef
  have hTP : rat (Tm A μ) * rat L = (1 : Mx D (A.rank + A.rank) (A.rank + A.rank)) := by
    show (incA D).mapMatrix (Tm A μ) * (incA D).mapMatrix L = 1
    rw [← map_mul, hR, map_one]
  have key : ∀ h : G D A.rank, mt (dblSp A) (κ.symm h) = rat (Tm A μ) * mat h * rat L := by
    intro h
    have e := hκ (κ.symm h)
    rw [MulEquiv.apply_symm_apply] at e
    calc mt (dblSp A) (κ.symm h) = mt (dblSp A) (κ.symm h) * (rat (Tm A μ) * rat L) := by
          rw [hTP, Matrix.mul_one]
      _ = (mt (dblSp A) (κ.symm h) * rat (Tm A μ)) * rat L := by rw [Matrix.mul_assoc]
      _ = rat (Tm A μ) * mat h * rat L := by rw [← e]
  have hind : Topology.IsInducing (fun g : GA D (dblSp A) => matHom (dblSp A) g) := ⟨rfl⟩
  have hmi : Continuous (fun h : G D A.rank => mat h⁻¹) := by
    unfold GlobalTheory.StdUnn.mat
    simp only [map_inv]
    exact Units.continuous_coe_inv.comp continuous_induced_dom
  rw [hind.continuous_iff, Units.continuous_iff]
  constructor
  · have hf : (Units.val ∘ (fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) =
        fun h => rat (Tm A μ) * mat h * rat L := by
      funext h
      exact key h
    rw [hf]
    exact (continuous_const.matrix_mul continuous_mat).matrix_mul continuous_const
  · have hf : (fun h : G D A.rank => (((fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) h)⁻¹.val) =
        fun h => rat (Tm A μ) * mat h⁻¹ * rat L := by
      funext h
      simp only [Function.comp_apply]
      rw [← map_inv (matHom (dblSp A)), ← map_inv κ.symm]
      exact key h⁻¹
    rw [hf]
    exact (continuous_const.matrix_mul hmi).matrix_mul continuous_const

end GlobalTheory.CompanionTheory.ChartSymm
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

theorem contra_contra_of_equiv {G V W U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} {υ : Representation ℂ G U}
    (E₁ : (contra σ).Equiv τ) (E₂ : (contra τ).Equiv υ) (E₃ : υ.Equiv σ) :
    Nonempty ((contra (contra σ)).Equiv σ) :=
  ⟨((GlobalTheory.ContraRefl.contraEquiv E₁).symm.trans E₂).trans E₃⟩

theorem prodIrr_equiv_of_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : y = x)
    (hy : ∑ a, (y a).1 = N) (hx : ∑ a, (x a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr x hx)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem contra_contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Nonempty ((contra (contra (prodIrr x hd))).Equiv (prodIrr x hd)) := by
  intro k _ _ _ _ hA h N x hd
  refine Exists.elim (contra_prodIrr hA x hd) fun hd₁ H₁ => H₁.elim fun E₁ => ?_
  refine Exists.elim (contra_prodIrr hA (fun a => Zc.dualCl (x a)) hd₁) fun hd₂ H₂ => H₂.elim fun E₂ => ?_
  refine (prodIrr_equiv_of_eq (funext fun a => GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA (x a)) hd₂ hd).elim fun E₃ => ?_
  exact contra_contra_of_equiv E₁ E₂ E₃

end GlobalTheory.CompanionTheory.ContraProd

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.generic_subquotient_iff_whittaker_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ A B : Subrepresentation ρ, B ≤ A → (IsGenericFor ψ (subQuot A B) ↔ ¬ A.toSubmodule ≤ B.toSubmodule ⊔ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff | exact GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff | (intros; apply GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

theorem _root_.GlobalTheory.T.twisted_kernel_sup_distributes_subreps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ≤ X.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ⊔ Y.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le | exact GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le | (intros; apply GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.hyperbolic_fibre_free_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → (∀ X, 0 ≤ φ X) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m 0) = ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (φ (chartS R σ J x a 0 Y)) ∂(m' 0) ∂(coordW R b lam 1 n) ∂(m₁ 0) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero <;> assumption)
end
