module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle101
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle442
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle436
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.VertGen

private theorem pullForm_X_eq_pullRatio {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace ℤ N) (W : Y.Opens)
    (i : Fin (N + 1)) (hi : W ≤ (Opens.map φ.base).obj (GlobalTheory.ProjSpace.chart ℤ N i)) (l : Fin (N + 1))
    (h : (MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℤ).IsHomogeneous 1) :
    GlobalTheory.ProjBlowup.pullForm φ W i hi 1 (MvPolynomial.X l) h = GlobalTheory.ProjSpace.pullRatio φ W i hi l := by
  unfold GlobalTheory.ProjBlowup.pullForm GlobalTheory.ProjSpace.pullRatio GlobalTheory.ProjSpace.formOn GlobalTheory.ProjSpace.ratio
    GlobalTheory.ProjSpace.ratioOn
  congr 1
  congr 1
  exact pow_one _

theorem genericPoint_mem_nonzeroLocus : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (k : Fin (m + 1)) (l : Bk n k), (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f (genericPoint Z)) → genericPoint Z ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) := by
  intro m n Z _ f _ k l hX
  have hxj := GlobalTheory.CompanionTheory.MPDict.mem_ptChart (f (genericPoint Z)) k
  have hne : GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩ ≠ 0 := by
    intro h0
    apply hX
    show (MvPolynomial.X ⟨k, l⟩ : Pol n) ∈
      RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z))))
    rw [RingHom.mem_ker]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, h0]
  let j : (pullO (f ≫ prB n k) 1).ι := (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k : Fin (n k + 1))
  have hξ : genericPoint Z ∈ (pullO (f ≫ prB n k) 1).U j := hxj
  apply GlobalTheory.basicOpen_le_nonzeroLocus _ j
  refine (Scheme.evaluation_ne_zero_iff_mem_basicOpen Z (genericPoint Z) hξ _).mp ?_
  dsimp only [GlobalTheory.ProjBlowup.pullFormSec]
  have hle : (pullO (f ≫ prB n k) 1).U j ≤
      (Opens.map (f ≫ prB n k).base).obj (GlobalTheory.ProjSpace.chart ℤ (n k) (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k)) :=
    le_rfl
  have e := pullForm_X_eq_pullRatio (f ≫ prB n k) ((pullO (f ≫ prB n k) 1).U j)
    (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hle l (isHomogeneous_X ℤ l)
  have key := GlobalTheory.CompanionTheory.MPDict.FnDeg.eval_pullRatio_comp f (prB n k) (genericPoint Z)
    (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hxj l
  have h2 : (CommRingCat.Hom.hom (Scheme.Hom.residueFieldMap f (genericPoint Z)))
      (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩) ≠ 0 := (map_ne_zero _).mpr hne
  convert h2 using 1
  refine Eq.trans ?_ key.symm
  exact congrArg (ConcreteCategory.hom (Z.evaluation _ (genericPoint Z) hξ)) e

end GlobalTheory.CompanionTheory.MixZ.VertGen
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspFinDeriv

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def cExp (t : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))

theorem splitCentre_eq_infGL (t : ℝ) : GlobalTheory.UnitaryBC.splitCentre E a t = infGL E a (cExp E a t) := rfl

theorem cExp_zero : cExp E a 0 = 1 := by
  have h1 : (GlobalTheory.CuspRep.expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU]
  unfold cExp
  rw [h1, map_one]

theorem hasDerivAt_cExp : HasDerivAt (fun t => toL (cExp E a t).val) (oneL E a) 0 := by
  unfold cExp GlobalTheory.CuspRep.toL GlobalTheory.CuspRep.oneL
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro v
  simp [GlobalTheory.CuspRep.expU, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    have h := (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    simp only [Complex.ofReal_zero, Complex.exp_zero] at h
    simpa using h
  · simpa [hij] using hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem hasDerivAt_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ),
    HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  intro E _ _ _ a φ g s
  have hφ := φ.2
  unfold GlobalTheory.CuspRep.Sm at hφ
  have hc := hφ (g * GlobalTheory.UnitaryBC.splitCentre E a s)
  have hopen : IsOpen (GlobalTheory.CuspRep.invSet E a) := by
    unfold GlobalTheory.CuspRep.invSet
    have hdet : Continuous fun x : GlobalTheory.CuspRep.Lie E a => (Matrix.of x).det :=
      (continuous_id.comp continuous_id).matrix_det
    have h3 := Units.isOpen.preimage hdet
    simpa [Matrix.isUnit_iff_isUnit_det] using h3
  have hmem : GlobalTheory.CuspRep.oneL E a ∈ GlobalTheory.CuspRep.invSet E a := by
    unfold GlobalTheory.CuspRep.invSet GlobalTheory.CuspRep.oneL GlobalTheory.CuspRep.toL
    change IsUnit (1 : Matrix (Fin a) (Fin a) (Cinf E))
    exact isUnit_one
  have hdiff : DifferentiableAt ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (GlobalTheory.CuspRep.oneL E a) :=
    (hc.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)
  have hγ0 : GlobalTheory.CuspRep.toL (cExp E a 0).val = GlobalTheory.CuspRep.oneL E a := by
    rw [cExp_zero]
    rfl
  have hl : HasFDerivAt (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a))
      (GlobalTheory.CuspRep.toL (cExp E a 0).val) := by
    rw [hγ0]
    exact hdiff.hasFDerivAt
  have hcomp := hl.comp_hasDerivAt (0 : ℝ) (hasDerivAt_cExp E a)
  have hadd : ∀ s t : ℝ, GlobalTheory.UnitaryBC.splitCentre E a (s + t) =
      GlobalTheory.UnitaryBC.splitCentre E a s * GlobalTheory.UnitaryBC.splitCentre E a t := by
    intro s t
    rw [splitCentre_eq_infGL, splitCentre_eq_infGL, splitCentre_eq_infGL, ← map_mul]
    congr 1
    unfold cExp
    rw [← map_mul]
    congr 1
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU, Complex.exp_add]
  have hval : ∀ t : ℝ, GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)
      (GlobalTheory.CuspRep.toL (cExp E a t).val) = (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := by
    intro t
    unfold GlobalTheory.CuspRep.chart GlobalTheory.CuspRep.toL
    have hu : IsUnit (Matrix.of (Matrix.of.symm (cExp E a t).val)) := by
      change IsUnit (cExp E a t).val
      exact (cExp E a t).isUnit
    rw [dite_eq_left hu]
    have hunit : hu.unit = cExp E a t := Units.ext (by rfl)
    rw [hunit, ← splitCentre_eq_infGL, hadd, mul_assoc]
  have hF : HasDerivAt (fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a)
        (GlobalTheory.CuspRep.oneL E a)) (s - s) := by
    rw [sub_self]
    have h5 : (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s) ∘ fun t => GlobalTheory.CuspRep.toL (cExp E a t).val) =
        fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := funext hval
    rw [← h5]
    exact hcomp
  have hF2 := HasDerivAt.comp_sub_const s s hF
  have h6 : (fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + (x - s)))) =
      fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a x) := by
    funext x
    rw [show s + (x - s) = x by ring]
  rw [h6] at hF2
  exact hF2

end GlobalTheory.CompanionTheory.CuspFinDeriv

end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

theorem _root_.GlobalTheory.T.compact_conjugate_rational_entries_bounded : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g₀ : GA E a)
    (Q : Set (GA E a)), IsCompact Q → ∀ n₀ : ℕ, ∃ (Qf : Set (Af E)) (C : ℝ), IsCompact Qf ∧ 0 ≤ C ∧
      ∀ (y : GL (Fin a) (Cinf E)) (γ : GL (Fin a) E) (n : ℤ), |n| ≤ n₀ →
        (g₀ * infGL E a y)⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * (g₀ * infGL E a y) ∈ Q →
        ∀ i j, algebraMap E (Af E) (γ.val i j) ∈ Qf ∧ ∀ w : InfinitePlace E, w (γ.val i j) ≤ C * height y ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GrowthEntries.entries_bound | exact GlobalTheory.CompanionTheory.GrowthEntries.entries_bound | (intros; apply GlobalTheory.CompanionTheory.GrowthEntries.entries_bound <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Orth

variable {D : D7}

theorem trA_incA_eq (e : D.host.E) :
    trA (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  have h : LinearMap.mulLeft (AF D.host.F) (incA D e) =
      LinearMap.baseChange (AF D.host.F) (LinearMap.mulLeft D.host.F e) := by
    ext b
    simp [TensorProduct.AlgebraTensorModule.curry_apply, incA, inclR, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
  simp only [trA, Algebra.trace_apply]
  change LinearMap.trace _ _ (LinearMap.mulLeft (AF D.host.F) (incA D e)) =
    algebraMap _ _ (LinearMap.trace _ _ (LinearMap.mulLeft D.host.F e))
  rw [h, LinearMap.trace_baseChange]

theorem trA_smul_half (x : AF D.host.F) :
    trA (x • half D) = x := by
  have hE := D.host.toHostAx.der.finrank_E
  have hF := D.host.toHostAx.der.finrank_F
  have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
  have htow := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [hF] at hpos htow
    rw [hE] at htow
    have h4 : 2 * D.R.ord * Module.finrank D.host.F D.host.E = 2 * D.R.ord * 2 := by
      rw [htow]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  have hhalf : trA (half D) = 1 := by
    rw [half, trA_incA_eq]
    have : (1 / 2 : D.host.E) = algebraMap D.host.F D.host.E (1 / 2) := by
      rw [map_div₀, map_one, map_ofNat]
    rw [this, Algebra.trace_algebraMap, h2]
    norm_num
  have hlin : trA (x • half D) = x * trA (half D) := by
    simp only [trA, map_smul, smul_eq_mul]
  rw [hlin, hhalf, mul_one]

theorem inner_rat_eq (V : HSp D) {s : ℕ} (q : Matrix (Fin V.rank) (Fin s) D.host.E) (y : Mx D V.rank s) :
    GlobalTheory.StdUnn.inner V (rat q) y = rat (qᴴ * V.gram) ⬝ y := by
  simp only [GlobalTheory.StdUnn.inner]
  rw [← rat_conjTranspose, gA, ← Matrix.mul_assoc, ← rat_mul]

theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {s : ℕ} (x y u : Mx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x (y + u)))) =
      ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x y))) * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V x u))) := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.trace_add, trA, map_add (f := _), AddChar.map_add_eq_mul]

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) {γ : Mx D V.rank s} (hγ : γ ∈ ratMx D V.rank s) :
    ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) γ))) = 1 := by
  obtain ⟨g, rfl⟩ := mem_ratMx.mp hγ
  have htr : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E), Matrix.trace (rat M) = incA D (Matrix.trace M) := by
    intro n M

    simp [rat, Matrix.trace, map_sum]
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) * rat g))) = 1
  rw [← rat_mul, htr, trA_incA_eq]
  exact hψ.2.2.1 _

theorem exists_chi_ne_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    {q : Matrix (Fin V.rank) (Fin s) D.host.E} (hq : q ≠ 0) :
    ∃ u : Mx D V.rank s, ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) u))) ≠ 1 := by
  obtain ⟨x, hx⟩ := hψ.2.2.2
  have hM : qᴴ * V.gram ≠ 0 := by
    intro h
    apply hq
    have h1 : qᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right V.gram qᴴ (gram_isUnit_det V), h, Matrix.zero_mul]
    simpa using congrArg Matrix.conjTranspose h1
  obtain ⟨i, j, hij⟩ : ∃ i j, (qᴴ * V.gram) i j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hM (Matrix.ext hne)
  have key : ∀ (A : Mx D s V.rank) (c : AE D), Matrix.trace (A * Matrix.single j i c) = A i j * c := by
    intro A c
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  refine ⟨Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D)), ?_⟩
  rw [inner_rat_eq]
  change ψ (trA (Matrix.trace (rat (qᴴ * V.gram) *
      Matrix.single j i (incA D ((qᴴ * V.gram) i j)⁻¹ * (x • half D))))) ≠ 1
  rw [key, show rat (qᴴ * V.gram) i j = incA D ((qᴴ * V.gram) i j) from rfl, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ hij, map_one, one_mul, trA_smul_half]
  exact hx

theorem orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (s : ℕ)
    (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)), IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ q : Matrix (Fin V.rank) (Fin s) D.host.E,
      (q = 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 1) ∧
      (q ≠ 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 0) := by
  intro D ψ hψ V s μs 𝓕s hcov q
  constructor
  · rintro rfl
    have h0 : ∀ y : Mx D V.rank s, ψ (trA (Matrix.trace (inner V (rat (0 : Matrix (Fin V.rank) (Fin s) D.host.E)) y))) = 1 := by
      intro y
      simp [GlobalTheory.StdUnn.inner, rat_zero, adj_zero, trA]
    simp_rw [h0]
    rw [MeasureTheory.setIntegral_const]
    simp [Measure.real, hcov.2.2]
  · intro hq
    obtain ⟨u, hu⟩ := exists_chi_ne_one hψ V hq
    set φ : Mx D V.rank s → ℂ := fun y => ψ (trA (Matrix.trace (inner V (rat q) y))) with hφ
    have hper : ∀ γ ∈ ratMx D V.rank s, ∀ a, φ (γ + a) = φ a := by
      intro γ hγ a
      simp only [hφ]
      rw [chi_add, chi_rat hψ V q hγ, one_mul]
    have h1 := covolOne_integral_add hcov φ hper u
    have h2 : ∀ a, φ (a + u) = φ u * φ a := by
      intro a
      simp only [hφ]
      rw [chi_add, mul_comm]
    simp only [h2] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    have h3 : (φ u - 1) * ∫ y in 𝓕s, φ y ∂μs = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hu
    · exact h

end GlobalTheory.CompanionTheory.EisUnfold.Orth

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_group_le_of_generators_mem : ∀ (D : D7) (n : ℕ) (S : Subgroup (G D n)),
  (∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S) →
  (∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S) →
  (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S) → GF D n ≤ S := by
  first | exact @GlobalTheory.CompanionTheory.RatGen.GF_le_of_levi_unip_weyl | exact GlobalTheory.CompanionTheory.RatGen.GF_le_of_levi_unip_weyl | (intros; apply GlobalTheory.CompanionTheory.RatGen.GF_le_of_levi_unip_weyl <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem hypOne_mul_hypOne_of_mul_eq_one {K : Type} [Field K] {M : ℕ} {A B : Matrix (Fin M) (Fin M) K}
    (h : A * B = 1) : hypOne A * hypOne B = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, Matrix.one_apply,
      ← Matrix.mul_apply, h, Fin.ext_iff]

theorem isHermND_hypOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : IsHermND σ (hypOne J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    all_goals first
      | exact hJ.1 i j
      | simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
          hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one]
  · have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
    have h1 : hypOne J * hypOne J⁻¹ = 1 :=
      hypOne_mul_hypOne_of_mul_eq_one (Matrix.mul_nonsing_inv J hu)
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2

theorem e0_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  refine ⟨linearIndependent_unique_iff.2 ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [e0] at this
  · ext a b
    simp [gramE, hE, hform, e0, Fin.sum_univ_succ, hypOne_zero_zero]

theorem hypOne_isHermND_and_e0_mem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (_hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) :
    IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) :=
  ⟨isHermND_hypOne σ hJ, e0_mem_framesE σ J⟩

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.laplacian_casimir_relation : ∀ (n : ℕ) (E : KMod n), RCalc → OmFormula → ∃ Q : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g) := by
  first | exact @GlobalTheory.CompanionTheory.FcSmooth.lap_sec | exact GlobalTheory.CompanionTheory.FcSmooth.lap_sec | (intros; apply GlobalTheory.CompanionTheory.FcSmooth.lap_sec <;> assumption)
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.laplacian_power_casimir_bound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (Q : E.V →L[ℂ] E.V), LgFacts → Unimod → RCalc → ClsFacts →
    (∀ f ∈ CE E, ∀ g ∈ GLs n, GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g)) →
    ∀ j : ℕ, ∃ C : ℝ, ∀ f : Mat n → E.V, Sob μ f → IsSec E f →
      ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ ≤ C * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ := by
  first | exact @GlobalTheory.CompanionTheory.LapSec.sectionBound | exact GlobalTheory.CompanionTheory.LapSec.sectionBound | (intros; apply GlobalTheory.CompanionTheory.LapSec.sectionBound <;> assumption)
end
