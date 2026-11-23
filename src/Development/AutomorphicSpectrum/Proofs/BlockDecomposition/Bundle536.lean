module

public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle506
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle008
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle057
import Formalism.LocalRingCardinality.DataHost
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Mathlib.Topology.UniformSpace.Uniformizable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle490
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle039
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

namespace GlobalTheory.CompanionTheory.CTFin.IwaAd

theorem map_unip {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {a r : ℕ} (x : BlockIx a r → R) :
    GeneralLinearGroup.map f (unip x) = unip (fun p => f (x p)) := by
  apply Units.ext
  ext i j
  change f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM (fun p => f (x p)) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add (f := _)]
  split_ifs <;> simp

theorem map_lev {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r s : ℕ)
    (m : GL (Fin r) R × GL (Fin s) R) :
    GeneralLinearGroup.map f (lev R r s m) =
      lev S r s (GeneralLinearGroup.map f m.1, GeneralLinearGroup.map f m.2) := by
  apply Units.ext
  ext i j
  change f (((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) i j) = ((lev S r s _ : GL (Fin (r + s)) S) : Matrix _ _ S) i j
  have val_emb (T : Type) [CommRing T] (g : GL (Fin r) T × GL (Fin s) T) :
      (GlobalTheory.SmGL.emb₂ T (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) g : Matrix _ _ T) =
        Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
          (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb,
        GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two, Matrix.blockDiagonal'_apply]
  rw [lev, lev, val_emb, val_emb]
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp

theorem exists_finset_cover (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Subgroup (GL (Fin n) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin n) (Af E)))) :
    ∃ T : Finset (GL (Fin n) (Af E)), ∀ c ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n,
      ∃ t ∈ T, ∃ l ∈ L, c = t * l := by
  obtain ⟨T, hT⟩ := (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).elim_finite_subcover
    (fun t : GL (Fin n) (Af E) => (fun z => t⁻¹ * z) ⁻¹' (L : Set (GL (Fin n) (Af E))))
    (fun t => hL.preimage (continuous_const.mul continuous_id))
    (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [L.one_mem]⟩)
  refine ⟨T, fun c hc => ?_⟩
  obtain ⟨t, ht, hl⟩ := Set.mem_iUnion₂.1 (hT hc)
  exact ⟨t, ht, t⁻¹ * c, hl, by group⟩

theorem iwasawa_finite_cosets : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∃ T : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GA E (r + s), ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E)) (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ T ∧ l ∈ L ∧ g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  intro E _ _ _ r s L hL
  obtain ⟨T, hT⟩ := exists_finset_cover E (r + s) L hL
  refine ⟨T, fun g => ?_⟩
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) g)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) g)
  obtain ⟨t, ht, l, hl, rfl⟩ := hT c hc
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add (f := _), show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add (f := _), show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), t, k, l, ht, hl, ga_ext ?_ ?_⟩
  · simp only [map_mul, map_unip, map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [map_mul, map_unip, map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf, mul_assoc, mul_assoc, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.IwaAd
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

namespace GlobalTheory.CompanionTheory.UnfoldFam

open GlobalTheory.CompanionTheory.UnfoldAbs

theorem unfold_fam : ∀ {A X Y U : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] [Countable U] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : U → A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1)
    (Um : X → ℝ) (_ : Summable Um) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (_ : ∀ b, ∃ l : Λ, ∀ q, ‖F q b‖ ≤ Um (τ l q))
    (e : Λ × U → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l l' : Λ) u, τ l' (e (l, u)) = e (l' + l, u))
    (_ : ∀ (l : Λ) u b, F (e (l, u)) b = F0 u ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    (∀ u, Integrable (F0 u) lam ∧ ∫ b, ‖F0 u b‖ ∂lam ≤ ∑' l : Λ, Um (e (l, u))) ∧
    HasSum (fun u => ∫ b, F0 u b * ch b ∂lam) (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) := by
  intro A X Y U _ _ _ lam _ Λ _ 𝓖 h𝓖 h1 _ _ c y0 F F0 ch hF hch hnorm hmul hΛ Um hUm τ hτ hcτ hbd
    e he hfib hτe hF0 hν
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by simp [h1]⟩

  have hUm0 : ∀ q, 0 ≤ Um q := by
    intro q
    obtain ⟨l, hl⟩ := hbd 0
    have := hl ((τ l).symm q)
    rw [Equiv.apply_symm_apply] at this
    exact (norm_nonneg _).trans this

  have hb : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ ∑' q, Um q := by
    intro b
    obtain ⟨l, hl⟩ := hbd b
    have hs : Summable (fun q => Um (τ l q)) := (τ l).summable_iff.mpr hUm
    have hs1 : Summable (fun q => ‖F q b‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hl hs
    refine ⟨hs1, ?_⟩
    calc ∑' q, ‖F q b‖ ≤ ∑' q, Um (τ l q) := hs1.tsum_le_tsum hl hs
      _ = ∑' q, Um q := (τ l).tsum_eq Um
  have hsub : ∀ {Z : Type} (j : Z → X), Function.Injective j → ∀ b,
      Summable (fun z => ‖F (j z) b‖) ∧ ∑' z, ‖F (j z) b‖ ≤ ∑' q, Um q := by
    intro Z j hj b
    refine ⟨(hb b).1.comp_injective hj, ?_⟩
    exact (tsum_comp_le_tsum_of_inj (hb b).1 (fun _ => norm_nonneg _) hj).trans (hb b).2
  have key : ∀ {Z : Type} [Countable Z] (j : Z → X), Function.Injective j →
      HasSum (fun z => ∫ b in 𝓖, F (j z) b * ch b ∂lam)
        (∫ b in 𝓖, (∑' z, F (j z) b) * ch b ∂lam) := by
    intro Z _ j hj
    have := hasSum_integral_of_norm_bound (lam.restrict 𝓖) (fun z b => F (j z) b * ch b)
      (fun z => ((hF (j z)).mul hch).restrict) (∑' q, Um q) (fun b => by
        simpa [hnorm] using hsub j hj b)
    simpa only [tsum_mul_right] using this

  have heu : ∀ u, Function.Injective (fun l : Λ => e (l, u)) := fun u a b h =>
    (Prod.mk.inj (he h)).1
  have hF0e : ∀ u, F0 u = F (e (0, u)) := by
    intro u
    funext b
    have := hF0 0 u b
    simpa using this.symm
  have hm0 : ∀ u, AEStronglyMeasurable (F0 u) lam := fun u => hF0e u ▸ hF (e (0, u))
  have hSs : ∀ u, Summable (fun l : Λ => Um (e (l, u))) := fun u => hUm.comp_injective (heu u)
  have hS0 : ∀ u, 0 ≤ ∑' l : Λ, Um (e (l, u)) := fun u => tsum_nonneg fun _ => hUm0 _
  have horb : ∀ u b, Summable (fun l : Λ => ‖F0 u ((l : A) + b)‖) ∧
      ∑' l : Λ, ‖F0 u ((l : A) + b)‖ ≤ ∑' l : Λ, Um (e (l, u)) := by
    intro u b
    obtain ⟨l0, hl0⟩ := hbd b
    have hle : ∀ l : Λ, ‖F0 u ((l : A) + b)‖ ≤ Um (e (l0 + l, u)) := by
      intro l
      rw [← hF0 l u b, ← hτe l l0 u]
      exact hl0 _
    have hs : Summable (fun l : Λ => Um (e (l0 + l, u))) :=
      (Equiv.addLeft l0).summable_iff.mpr (hSs u)
    have hs1 : Summable (fun l : Λ => ‖F0 u ((l : A) + b)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
    refine ⟨hs1, ?_⟩
    calc ∑' l : Λ, ‖F0 u ((l : A) + b)‖ ≤ ∑' l : Λ, Um (e (l0 + l, u)) :=
          hs1.tsum_le_tsum hle hs
      _ = ∑' l : Λ, Um (e (l, u)) :=
          (Equiv.addLeft l0).tsum_eq (fun l : Λ => Um (e (l, u)))
  have hint0 : ∀ u, Integrable (F0 u) lam := fun u =>
    integrable_of_lattice_bound lam Λ 𝓖 h𝓖 h1 (F0 u) (hm0 u) _ (horb u)
  have hnb : ∀ u, ∫ b, ‖F0 u b‖ ∂lam ≤ ∑' l : Λ, Um (e (l, u)) := by
    intro u
    rw [integral_norm_eq_lintegral_enorm (hm0 u)]
    refine ENNReal.toReal_le_of_le_ofReal (hS0 u) ?_
    have ee : ∫⁻ b, ‖F0 u b‖ₑ ∂lam = ∑' l : Λ, ∫⁻ b in 𝓖, ‖F0 u ((l : A) + b)‖ₑ ∂lam :=
      h𝓖.lintegral_eq_tsum'' _
    have hmeas : ∀ l : Λ, AEMeasurable (fun b => ‖F0 u ((l : A) + b)‖ₑ) (lam.restrict 𝓖) :=
      fun l => (((hm0 u).comp_measurePreserving
        (measurePreserving_add_left lam (l : A))).enorm).restrict
    rw [ee, ← lintegral_tsum hmeas]
    calc ∫⁻ b in 𝓖, ∑' l : Λ, ‖F0 u ((l : A) + b)‖ₑ ∂lam
        ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal (∑' l : Λ, Um (e (l, u))) ∂lam := by
          refine lintegral_mono (fun b => ?_)
          simp_rw [← ofReal_norm_eq_enorm]
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (horb u b).1]
          exact ENNReal.ofReal_le_ofReal (horb u b).2
      _ = ENNReal.ofReal (∑' l : Λ, Um (e (l, u))) := by simp [h1]
  refine ⟨fun u => ⟨hint0 u, hnb u⟩, ?_⟩

  have hT := key (Z := X) id Function.injective_id
  simp only [id] at hT
  have hsig := (Equiv.sigmaFiberEquiv c).hasSum_iff.mpr hT
  have hg : HasSum (fun y => ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam)
      (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) :=
    hsig.sigma (fun y => key (Z := {x // c x = y}) Subtype.val Subtype.val_injective)

  have hzero : ∀ y, y ≠ y0 → ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam = 0 := by
    intro y hy
    obtain ⟨ν, hν1, hνq⟩ := hν y hy
    refine setIntegral_eq_zero_of_translate lam Λ 𝓖 h𝓖 _ ν (ch ν) hν1 (fun l b => ?_) (fun b => ?_)
    · have hs : ∑' z : {x // c x = y}, F z ((l : A) + b) = ∑' z : {x // c x = y}, F z b := by
        calc ∑' z : {x // c x = y}, F z ((l : A) + b)
            = ∑' z : {x // c x = y}, F (τ l z) b := tsum_congr fun z => hτ l z b
          _ = ∑' z : {x // c x = y}, F z b :=
            ((τ l).subtypeEquiv (p := fun x => c x = y) (q := fun x => c x = y)
              (fun a => by rw [hcτ])).tsum_eq (fun z : {x // c x = y} => F z b)
      rw [hs, hmul, hΛ, one_mul]
    · have hs : ∑' z : {x // c x = y}, F z (ν + b) = ∑' z : {x // c x = y}, F z b :=
        tsum_congr fun z => hνq z z.2 b
      rw [hs, hmul]
      ring
  have hT' := hg.unique (hasSum_single y0 (fun y hy => hzero y hy))
  rw [hT']

  let ee : Λ × U ≃ {x // c x = y0} := Equiv.ofBijective
    (fun p => ⟨e p, (hfib _).2 ⟨p, rfl⟩⟩)
    ⟨fun a b h => he (congrArg Subtype.val h), fun q => by
      obtain ⟨p, hp⟩ := (hfib q).1 q.2
      exact ⟨p, Subtype.ext hp⟩⟩
  have hsum : ∀ b, ∑' z : {x // c x = y0}, F z b = ∑' p : Λ × U, F (e p) b := fun b =>
    (ee.tsum_eq (fun z => F z b)).symm
  simp_rw [hsum]
  have hK := key e he
  have hK' : HasSum (fun p : U × Λ => ∫ b in 𝓖, F (e (p.2, p.1)) b * ch b ∂lam)
      (∫ b in 𝓖, (∑' p : Λ × U, F (e p) b) * ch b ∂lam) :=
    (Equiv.prodComm U Λ).hasSum_iff.mpr hK
  refine hK'.prod_fiberwise (fun u => ?_)
  have hs := hK'.summable.prod_factor u
  have hint1 : Integrable (fun b => F0 u b * ch b) lam :=
    (hint0 u).mono ((hint0 u).aestronglyMeasurable.mul hch) (ae_of_all _ fun b => by simp [hnorm])
  have hval : ∫ b, F0 u b * ch b ∂lam = ∑' l : Λ, ∫ b in 𝓖, F (e (l, u)) b * ch b ∂lam := by
    rw [h𝓖.integral_eq_tsum'' _ hint1]
    refine tsum_congr fun l => ?_
    refine integral_congr_ae (ae_of_all _ fun b => ?_)
    change F0 u ((l : A) + b) * ch ((l : A) + b) = F (e (l, u)) b * ch b
    rw [hF0, hmul, hΛ, one_mul]
  rw [hval]
  exact hs.hasSum

end GlobalTheory.CompanionTheory.UnfoldFam
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rank_residue_le_rank_generic : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L] [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O), (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  first | exact @GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map | exact GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map | (intros; apply GlobalTheory.CompanionTheory.Jp.rank_residue_map_le_rank_fraction_map <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.TorCent

theorem finite_roots_of_unity (M : Type) [Field M] [NumberField M] :
    {ζ : M | ∃ k : ℕ, 0 < k ∧ ζ ^ k = 1}.Finite := by
  refine (NumberField.Embeddings.finite_of_norm_le M ℂ 1).subset ?_
  rintro ζ ⟨k, hk, h⟩
  refine ⟨IsIntegral.of_pow hk (by rw [h]; exact isIntegral_one), fun φ => ?_⟩
  have h1 : (φ ζ) ^ k = 1 := by rw [← map_pow, h, map_one]
  exact (Complex.norm_eq_one_of_pow_eq_one h1 hk.ne').le

theorem exists_distinct_roots {M : Type} [Field M] {n : ℕ} (A : Matrix (Fin n) (Fin n) M)
    (hs : A.charpoly.Separable) (hsp : A.charpoly.Splits) :
    ∃ z : Fin n → M, Function.Injective z ∧ A.charpoly = ∏ a, (X - C (z a)) := by
  have hnd : A.charpoly.roots.Nodup := nodup_roots hs
  have hcard := splits_iff_card_roots.1 hsp
  have hdeg : A.charpoly.natDegree = n := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  set s := A.charpoly.roots.toFinset with hs_def
  have hsc : Fintype.card s = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard, hdeg]
  let e := Fintype.equivFinOfCardEq hsc
  refine ⟨fun a => ((e.symm a : s) : M), Subtype.val_injective.comp e.symm.injective, ?_⟩
  rw [Equiv.prod_comp e.symm (fun r : s => X - C (r : M)), Finset.prod_coe_sort s (fun r => X - C r),
    Finset.prod_eq_multiset_prod, hs_def, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd,
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _) hcard]

theorem eq_diagonal_of_commute {M : Type} [Field M] {n : ℕ} {z : Fin n → M}
    (hz : Function.Injective z) {F : Matrix (Fin n) (Fin n) M}
    (h : F * diagonal z = diagonal z * F) : F = diagonal fun i => F i i := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · have h1 := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at h1
    rw [diagonal_apply_ne _ hij]
    have h2 : F i j * (z j - z i) = 0 := by rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 fun e => hij (hz e.symm))

theorem finite_torsion_centralizer : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (N : GL (Fin n) E), N.val.charpoly.Separable →
  {g : GL (Fin n) E | g * N = N * g ∧ IsOfFinOrder g}.Finite := by
  intro E _ _ n N hsep
  let M := N.val.charpoly.SplittingField
  haveI : NumberField M := NumberField.of_module_finite E M
  let f : E →+* M := algebraMap E M
  let A : Matrix (Fin n) (Fin n) M := N.val.map f
  have hA : A.charpoly = N.val.charpoly.map f := charpoly_map _ _
  have hs : A.charpoly.Separable := by rw [hA]; exact hsep.map
  have hsp : A.charpoly.Splits := by rw [hA]; exact SplittingField.splits _
  obtain ⟨z, hz, hprod⟩ := exists_distinct_roots A hs hsp
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := A) (N := diagonal z) hs
    (by rw [charpoly_diagonal, hprod])
  let B : Matrix (Fin n) (Fin n) M := x.val
  let Bi : Matrix (Fin n) (Fin n) M := (x⁻¹).val
  have hBB : B * Bi = 1 := by simp [B, Bi]
  have hBB' : Bi * B = 1 := by simp [B, Bi]
  have hx' : diagonal z * B = B * A := hx
  have hx2 : Bi * diagonal z = A * Bi := by
    calc Bi * diagonal z = Bi * (diagonal z * B) * Bi := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one]
      _ = A * Bi := by rw [hx', ← Matrix.mul_assoc, hBB', Matrix.one_mul]
  let F : GL (Fin n) E → Matrix (Fin n) (Fin n) M := fun g => B * g.val.map f * Bi
  have hFc : ∀ g : GL (Fin n) E, g * N = N * g → F g * diagonal z = diagonal z * F g := by
    intro g hg
    have h1 : g.val * N.val = N.val * g.val := congrArg Units.val hg
    have h2 : g.val.map f * A = A * g.val.map f := by
      simp only [A]
      rw [← Matrix.map_mul, ← Matrix.map_mul, h1]
    simp only [F]
    calc B * g.val.map f * Bi * diagonal z = B * (g.val.map f * A) * Bi := by
          rw [Matrix.mul_assoc, hx2, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = diagonal z * (B * g.val.map f * Bi) := by
          rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hx', Matrix.mul_assoc, Matrix.mul_assoc,
            Matrix.mul_assoc, Matrix.mul_assoc]
  have hFpow : ∀ (g : GL (Fin n) E) (k : ℕ), F g ^ k = F (g ^ k) := by
    intro g k
    induction k with
    | zero => simp [F, hBB, Matrix.map_one, Matrix.mul_one]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [F, Units.val_mul]
      rw [Matrix.map_mul]
      calc B * (g ^ k).val.map f * Bi * (B * g.val.map f * Bi)
          = B * (g ^ k).val.map f * (Bi * B) * g.val.map f * Bi := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hBB', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  let φ : GL (Fin n) E → Fin n → M := fun g i => F g i i
  have hfin := Set.Finite.pi' fun _ : Fin n => finite_roots_of_unity M
  refine Set.Finite.of_injOn (f := φ) ?_ ?_ hfin
  · rintro g ⟨hg, ho⟩ i
    obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 ho
    refine ⟨k, hk, ?_⟩
    have h1 : F g ^ k = 1 := by
      rw [hFpow, hgk]; simp [F, hBB, Matrix.map_one]
    rw [eq_diagonal_of_commute hz (hFc g hg), diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa [φ] using h2
  · rintro g ⟨hg, -⟩ g' ⟨hg', -⟩ e
    have h1 : F g = F g' := by
      rw [eq_diagonal_of_commute hz (hFc g hg), eq_diagonal_of_commute hz (hFc g' hg')]
      exact congrArg diagonal e
    have h2 : g.val.map f = g'.val.map f := by
      have h3 : Bi * F g * B = Bi * F g' * B := by rw [h1]
      have h4 : ∀ Y : Matrix (Fin n) (Fin n) M, Bi * (B * Y * Bi) * B = Y := fun Y => by
        calc Bi * (B * Y * Bi) * B = (Bi * B) * Y * (Bi * B) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [hBB', Matrix.one_mul, Matrix.mul_one]
      simpa only [F, h4] using h3
    refine Units.ext ?_
    ext i j
    exact f.injective (congrFun (congrFun h2 i) j)

end GlobalTheory.CompanionTheory.TorCent
end
