module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle451
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle450
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle453
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle010
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

theorem _root_.GlobalTheory.T.archimedean_rank_one_free_of_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ X : Fin 1 → Fin M → Ainf F ⊗[F] E, (∀ w, xw e b X w ≠ 0) → LinearIndependent (Ainf F ⊗[F] E) X := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec.linearIndependent_of_xw_ne_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec.linearIndependent_of_xw_ne_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec.linearIndependent_of_xw_ne_zero <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF.Tails

theorem linearIndependent_tails {K : Type} [CommRing K] {M n : ℕ} {Y : Fin (n + 1) → Fin (M + 1) → K}
    (hY : LinearIndependent K Y) (h0 : ∀ i : Fin M, Y 0 i.succ = 0) :
    LinearIndependent K (fun (j : Fin n) (i : Fin M) => Y j.succ i.succ) := by
  have hfree := Fintype.linearIndependent_iff.1 hY

  have hnzd : ∀ b : K, b * Y 0 0 = 0 → b = 0 := by
    intro b hb
    have hsum : ∑ i, (Pi.single 0 b : Fin (n + 1) → K) i • Y i = 0 := by
      rw [Finset.sum_eq_single_of_mem (0 : Fin (n + 1)) (Finset.mem_univ _)
        (fun i _ hi => by simp [Pi.single_eq_of_ne hi])]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hb
      · simp [h0 i]
    simpa using hfree _ hsum 0
  refine Fintype.linearIndependent_iff.2 fun w hw j => ?_
  have hw' : ∀ i : Fin M, ∑ j, w j * Y j.succ i.succ = 0 := by
    intro i
    have := congrFun hw i
    simpa [Finset.sum_apply] using this
  set r : K := ∑ j, w j * Y j.succ 0 with hr
  have hsum : ∑ i, (Fin.cons (-r) (fun j => Y 0 0 * w j) : Fin (n + 1) → K) i • Y i = 0 := by
    rw [Fin.sum_univ_succ]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        Pi.zero_apply]
      have h1 : ∑ j, Y 0 0 * w j * Y j.succ 0 = r * Y 0 0 := by
        rw [hr, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [h1]
      ring
    · simp only [Fin.cons_zero, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        Pi.zero_apply, h0 i, mul_zero, zero_add]
      have : ∑ j, Y 0 0 * w j * Y j.succ i.succ = Y 0 0 * ∑ j, w j * Y j.succ i.succ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hw' i, mul_zero]
  have hj := hfree _ hsum j.succ
  rw [Fin.cons_succ] at hj
  exact hnzd _ (by rw [mul_comm]; exact hj)

theorem exists_compact_tails (K : Type) [CommRing K] [TopologicalSpace K] [T2Space K] (M n : ℕ)
    (Q : Set (Fin (n + 1) → Fin (M + 1) → K)) (hQ : IsCompact Q)
    (hfree : ∀ Y ∈ Q, LinearIndependent K Y) :
    ∃ C : Set (Fin n → Fin M → K), IsCompact C ∧ (∀ X ∈ C, LinearIndependent K X) ∧
      ∀ (A : K) (c : Fin n → K) (X : Fin n → Fin M → K), vec A c X ∈ Q → X ∈ C := by
  let tl : (Fin (n + 1) → Fin (M + 1) → K) → Fin n → Fin M → K := fun Y j i => Y j.succ i.succ
  have htl : Continuous tl :=
    continuous_pi fun j => continuous_pi fun i => (continuous_apply i.succ).comp (continuous_apply j.succ)
  have hclosed : IsClosed {Y : Fin (n + 1) → Fin (M + 1) → K | ∀ i : Fin M, Y 0 i.succ = 0} := by
    have : {Y : Fin (n + 1) → Fin (M + 1) → K | ∀ i : Fin M, Y 0 i.succ = 0} =
        ⋂ i : Fin M, {Y | Y 0 i.succ = 0} := by
      ext Y
      simp
    rw [this]
    exact isClosed_iInter fun i =>
      isClosed_eq ((continuous_apply i.succ).comp (continuous_apply 0)) continuous_const
  refine ⟨tl '' (Q ∩ {Y | ∀ i : Fin M, Y 0 i.succ = 0}), (hQ.inter_right hclosed).image htl, ?_, ?_⟩
  · rintro _ ⟨Y, ⟨hYQ, h0⟩, rfl⟩
    exact linearIndependent_tails (hfree Y hYQ) h0
  · intro A c X h
    exact ⟨vec A c X, ⟨h, fun i => by simp [vec]⟩, by funext j i; simp [tl, vec]⟩

end GlobalTheory.CompanionTheory.SW.StageF.Tails
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree

variable {K : Type} [CommRing K] {M n : ℕ}

theorem sum_vec_zero (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) 0
      = g 0 * α + ∑ j : Fin n, g j.succ * c j := by
  rw [Finset.sum_apply, Fin.sum_univ_succ]
  simp [vec]

theorem sum_vec_succ (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K)
    (i : Fin M) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) i.succ
      = (∑ j : Fin n, g j.succ • X j) i := by
  rw [Finset.sum_apply, Fin.sum_univ_succ, Finset.sum_apply]
  simp [vec]

theorem linearIndependent_vec_iff (K : Type) [CommRing K] (M n : ℕ) (α : K) (hα : IsUnit α)
    (c : Fin n → K) (X : Fin n → Fin M → K) :
    LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h w hw j
    obtain ⟨β, hβ⟩ := hα.exists_left_inv
    have key := h (Fin.cons (-(∑ j : Fin n, w j * c j) * β) w) (by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [sum_vec_zero]
        simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply]
        rw [mul_assoc, hβ]
        ring
      · rw [sum_vec_succ]
        simp only [Fin.cons_succ, Pi.zero_apply]
        rw [hw]
        rfl) j.succ
    simpa using key
  · intro h w hw
    have hs : ∀ j : Fin n, w j.succ = 0 := by
      refine h (fun j => w j.succ) ?_
      funext i
      have := congrFun hw i.succ
      rwa [sum_vec_succ] at this
    have h0 : w 0 = 0 := by
      have := congrFun hw 0
      rw [sum_vec_zero] at this
      simp only [hs, zero_mul, Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
      exact (hα.mul_left_eq_zero).1 this
    intro a
    refine Fin.cases h0 hs a

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

theorem constTerm_unip_left : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a),
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
      (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ →
    ∀ (y : BlockIx a r → Ad E) (g : GA E a),
      ∫ x in 𝓕, φ.1 (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  intro E _ _ _ a r φ hl _ _ _ μ 𝓕 hμ h𝓕 y g
  haveI := countable_ratN (E := E) (a := a) r
  have hper : ∀ n ∈ ratN E a r, ∀ x, φ.1 (unip (n + x) * g) = φ.1 (unip x * g) := by
    rintro _ ⟨q, rfl⟩ x
    rw [unip_add, mul_assoc]
    exact (congrArg (fun u => φ.1 (u * _)) (unip_algebraMap q)).trans (hl _ _)
  have h := Formalism.IndefR.Tow.fd_setIntegral_add h𝓕 (f := fun x => φ.1 (unip x * g)) hper y
  simpa only [unip_add, mul_assoc] using h

end GlobalTheory.CompanionTheory.CTFin
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

theorem _root_.GlobalTheory.T.smooth_weight_pullback_chart_formula : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (c : GlobalTheory.AlgChart q σ D) (j : Fin A.n) (u : Fin D → ℂ),
      u ∈ (A.chart j).target → F ((A.chart j).symm u) ∈ c.e.source →
      AnalyticAt ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u ∧
      locDens A (fun _ => φ.locPot.pullback F hF) j u =
        ‖LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (F ((A.chart j).symm u)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq | exact GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq | (intros; apply GlobalTheory.CompanionTheory.MixZ.PullDens.locDens_pullback_eq <;> assumption)
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

theorem _root_.GlobalTheory.T.smooth_weight_pullback_is_potential : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → IsPotential A (φ.locPot.pullback F hF) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.isPotential_pullback_locPot | exact GlobalTheory.CompanionTheory.MixZ.isPotential_pullback_locPot | (intros; apply GlobalTheory.CompanionTheory.MixZ.isPotential_pullback_locPot <;> assumption)
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
open Set Filter Topology

namespace GlobalTheory.CompanionTheory.MixZ

theorem lintegral_logNorm_locDens_lt_top : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B C : LB X} (φ : GlobalTheory.Weight q σ B) (_ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (_ : ψ.IsCInf)
      (g : GlobalTheory.CxPts q σ → ℝ) (S Z : Set (GlobalTheory.CxPts q σ)) {N : ℕ} (W : Fin N → X.Opens) (b : Fin N → C.ι)
      (a d : ∀ l, Γ(X, W l)),
    (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) → (∀ l, W l ≤ C.U (b l)) →
    (∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ S → y ∉ Z →
      g y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2) →
    IsOpen S → ContinuousOn g S → MeasurableSet Z →
    ∀ (j : Fin A.n) (K : Set (Fin D → ℂ)), K ⊆ (A.chart j).target → IsCompact K →
      ∫⁻ u in K \ (F ∘ (A.chart j).symm) ⁻¹' Z, S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤ := by
  intro k _ X q σ D T _ A F hF hol B C φ hφ ψ hψ g S Z N W b a d hcov hWb hg hSo hgc hZ j K hKt hKc
  have hGc : ContinuousOn (F ∘ (A.chart j).symm) (A.chart j).target :=
    hF.comp_continuousOn (A.chart j).continuousOn_symm
  have hdc : ContinuousOn (locDens A (fun _ => φ.locPot.pullback F hF) j) (A.chart j).target :=
    locDensCont A _ (fun _ => isPotential_pullback_locPot A F hF hol φ hφ) j
  refine hKc.induction_on (p := fun s => ∫⁻ u in s \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤) ?_ ?_ ?_ ?_
  · simp
  · intro s t hst ht
    exact (lintegral_mono_set (diff_subset_diff_left hst)).trans_lt ht
  · intro s t hs ht
    rw [union_diff_distrib]
    exact (lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)
  intro u0 hu0
  obtain ⟨l, hl⟩ := hcov (F ((A.chart j).symm u0))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l))) :=
    (A.chart j).isOpen_inter_preimage_symm ((isOpen_ptsIn _).preimage hF)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 ⟨hKt hu0, hl⟩
  set V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l)) with hV
  set Bl := Metric.closedBall u0 (r / 2) with hBl
  have hBV : Bl ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact Bl := isCompact_closedBall _ _
  have hBm : MeasurableSet Bl := Metric.isClosed_closedBall.measurableSet
  have hBt : Bl ⊆ (A.chart j).target := hBV.trans inter_subset_left
  refine ⟨Bl, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  have hla : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (a l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (a l) j u hu)).integrableOn_compact_subset hBV hBc
  have hld : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (d l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (d l) j u hu)).integrableOn_compact_subset hBV hBc
  have hψc : ContinuousOn (fun u => ψ.φ (b l) (F ((A.chart j).symm u))) Bl := by
    intro u hu
    have hc : ContinuousAt (ψ.φ (b l)) (F ((A.chart j).symm u)) :=
      (hψ (b l) _ (ptsIn_mono (hWb l) (hBV hu).2)).continuousAt
    exact ContinuousAt.comp_continuousWithinAt (f := F ∘ (A.chart j).symm) hc
      ((hGc u (hBt hu)).mono hBt)
  have hlψ : IntegrableOn (fun u => |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hψc.abs.div_const 2).integrableOn_compact hBc
  have hh : IntegrableOn (fun u => |Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
      |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
      |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hla.abs.add hld.abs).add hlψ
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn (hdc.mono hBt)
  have hYm : MeasurableSet (Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z) := by
    have hc : Continuous (fun u : Bl => (F ∘ (A.chart j).symm) u.1) :=
      continuousOn_iff_continuous_restrict.1 (hGc.mono hBt)
    have h1 : MeasurableSet (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) :=
      hBm.subtype_image (hc.measurable hZ)
    have h2 : Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z =
        Bl \ (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) := by
      ext u
      constructor
      · rintro ⟨hu, hn⟩
        refine ⟨hu, ?_⟩
        rintro ⟨v, hv, rfl⟩
        exact hn hv
      · rintro ⟨hu, hn⟩
        exact ⟨hu, fun hz => hn ⟨⟨u, hu⟩, hz, rfl⟩⟩
    rw [h2]
    exact hBm.diff h1
  have hpt : ∀ u ∈ Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| ≤
      ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
        |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
        |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M := by
    rintro u ⟨huB, huZ⟩
    by_cases hS : F ((A.chart j).symm u) ∈ S
    · rw [indicator_of_mem hS]
      refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_)
      · rw [← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hg l _ (hBV huB).2 hS huZ, Real.norm_eq_abs]
        have h1 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖ -
          Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
          (ψ.φ (b l) (F ((A.chart j).symm u)) / 2)
        have h2 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖)
          (Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
        rw [abs_div, abs_two] at h1
        linarith
      · simpa using hM u huB
    · rw [indicator_of_notMem hS, zero_mul]
      exact zero_le
  calc ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
          ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|
      ≤ ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        setLIntegral_mono' hYm hpt
    _ ≤ ∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        lintegral_mono_set diff_subset
    _ = (∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2)) * ENNReal.ofReal M :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top hh.lintegral_lt_top ENNReal.ofReal_lt_top

end GlobalTheory.CompanionTheory.MixZ
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwEntries

variable {E : Type} [Field E] [NumberField E]

theorem rel_le_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem rel_lt_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).lt_one_iff_lt_one

theorem mem_KGL_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, h2 i j⟩,
      hi ?_, hi ?_⟩, Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem mem_KO_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) ↔
      (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) →
      ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (rel_le_one_iff w _).1 (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    let O := ValuativeRel.valuation (w.adicCompletion E) |>.integer
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, (rel_le_one_iff w _).2 (h1 i j)⟩,
      Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, (rel_le_one_iff w _).2 (h2 i j)⟩, hi ?_, hi ?_⟩,
      Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem iwGL_KGL_entries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (g : GLw n w), (g ∈ iwGL n w ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (g.val i j) < 1) ∧ (g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  intro E _ _ _ w n g
  refine ⟨?_, mem_KGL_iff w n g⟩
  show g ∈ GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n) ↔ _
  rw [GlobalTheory.SmGL.mem_iwahori, mem_KO_iff, and_assoc]
  exact and_congr_right' (and_congr_right' (forall₃_congr fun i j _ => rel_lt_one_iff w _))

end GlobalTheory.CompanionTheory.IwEntries
end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

theorem _root_.GlobalTheory.T.split_centre_derivative_lie_action : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ), HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  first | exact @GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre | exact GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre | (intros; apply GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre <;> assumption)
end
