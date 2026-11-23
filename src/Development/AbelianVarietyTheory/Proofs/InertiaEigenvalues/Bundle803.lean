module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle030
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle175
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOpenSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle791
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle792
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle793
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle794
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem kerAbs_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, KerAbs D := by
  intro hP D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ
  have hfinV := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V νV 𝓗 hS.haarV hS.fdV
  refine ⟨hfinV.ne, fun f hf φ hφ hc => ?_⟩
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := GlobalTheory.Size.isTheta_iff_level.1 hf
  obtain ⟨μ', 𝓕', hμ'⟩ := GlobalTheory.Size.exists_isCovolOne V W
  obtain ⟨C, hC0, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  have hb := (hC χV χW om hS.weil μ' 𝓕' hμ' f hl).2
  set s := (GlobalTheory.Size.sobO ψ θ μ' 𝓕' d f).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact V (fun τ => hS.posDef (tauE D τ))
  obtain ⟨M₀, hM₀⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  set M := max M₀ 1 with hMdef
  have hM : ∀ c ∈ K, GlobalTheory.Grow.height V c ≤ M := fun c hc => (hM₀ c hc).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := zero_le_one.trans (le_max_right _ _)

  have hunif : ∀ h g, ‖thetaKO om h g f‖ ≤ C * s * M ^ A * GlobalTheory.Grow.height W g ^ A := by
    intro h g
    obtain ⟨γ, hγ, c, hc', rfl⟩ := hcov h
    rw [GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hS.weil hf g γ hγ c]
    calc ‖thetaKO om c g f‖ ≤ C * s * (GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g) ^ A := hb c g
      _ = C * s * GlobalTheory.Grow.height V c ^ A * GlobalTheory.Grow.height W g ^ A := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (GlobalTheory.Grow.height_pos V c).le (hM c hc') A) (mul_nonneg hC0 hs0))
            (pow_nonneg (GlobalTheory.Grow.height_pos W g).le A)
  have hR := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc
  obtain ⟨B0, hB0⟩ := hR.decay A
  have hq : ∀ h g, ‖star (thetaKO om h g f)‖ ≤ C * s * M ^ A * 2 ^ A * GlobalTheory.Grow.quotHeight W g ^ A := by
    intro h g
    rw [norm_star]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO om h g f)
      (GlobalTheory.Chain.LiftConv.thetaKO_left hS.weil hf h) (hunif h) g
  have hfinW := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W νW 𝓖 hS.haarW hS.fdW
  refine ⟨C * s * M ^ A * 2 ^ A * B0 * νW.real 𝓖, fun h => ⟨?_, ?_⟩⟩
  · exact hR.integrableOn_mul_of_le hS.haarW hS.fdW
      (GlobalTheory.Chain.LiftConv.thetaKO_continuous hS.weil hf h).star.aestronglyMeasurable (hq h)
  · refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const hfinW fun g _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have h1 := hq h g
    rw [norm_star] at h1
    have hK0 : 0 ≤ C * s * M ^ A * 2 ^ A := by positivity
    calc ‖thetaKO om h g f‖ * ‖φ g‖ ≤ C * s * M ^ A * 2 ^ A * GlobalTheory.Grow.quotHeight W g ^ A * ‖φ g‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * s * M ^ A * 2 ^ A * (‖φ g‖ * GlobalTheory.Grow.quotHeight W g ^ A) := by ring
      _ ≤ C * s * M ^ A * 2 ^ A * B0 := mul_le_mul_of_nonneg_left (hB0 g) hK0

end GlobalTheory.RawLift

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.locations_distinguished_by_generics : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  first | exact @GlobalTheory.CoefDuty.sameLoc_iff_heckeCong | exact GlobalTheory.CoefDuty.sameLoc_iff_heckeCong | (intros; apply GlobalTheory.CoefDuty.sameLoc_iff_heckeCong <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.side_eigen_frobenius : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tp.tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w), ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) = c v k := by
  first | exact @GlobalTheory.EigOnto.main | exact GlobalTheory.EigOnto.main | (intros; apply GlobalTheory.EigOnto.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Pointwise

namespace GlobalTheory.ConjTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem symm_alg (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (x : E) :
    c.symm (algebraMap E Ω x) = algebraMap E Ω (τ.symm x) := by
  rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]

def conjG (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) :
    G E Ω →* G E Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := c.symm.trans (g.toRingEquiv.trans c)) (fun x => by
    simp only [RingEquiv.trans_apply, symm_alg c τ hτ, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, hτ, RingEquiv.apply_symm_apply])
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp

theorem conjG_apply (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g y = c (g (c.symm y)) := rfl

theorem conjG_apply_c (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g (c y) = c (g y) := by
  rw [conjG_apply, RingEquiv.symm_apply_apply]

theorem conjG_conjG_symm (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) : conjG c τ hτ (conjG c.symm τ.symm (symm_alg c τ hτ) g) = g := by
  ext y; simp [conjG_apply]

theorem conjG_continuous [Algebra.IsAlgebraic E Ω] (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) : Continuous (conjG c τ hτ) := by
  classical
  apply continuous_of_continuousAt_one (conjG c τ hτ)
  rw [ContinuousAt, map_one]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨S, hS, hSU⟩ := hU
  let b := Module.finBasis E S
  let s : Finset Ω := Finset.univ.image (fun i => c.symm (b i : Ω))
  have hfin : FiniteDimensional E (IntermediateField.adjoin E (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  show _ ∈ nhds (1 : G E Ω)
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨_, hfin, fun g hg => hSU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro x hx
  have hb : ∀ i, conjG c τ hτ g (b i : Ω) = b i := by
    intro i
    rw [conjG_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simp [s])), RingEquiv.apply_symm_apply]
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ω) := by
    have := congrArg (fun z : S => (z : Ω)) (b.sum_repr ⟨x, hx⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_smul] at this
    exact this.symm

  rw [hx', map_sum]
  simp [map_smul, hb]

theorem mem_Dec_iff' {A : ValuationSubring Ω} {σ : G E Ω} :
    σ ∈ Dec (F := E) A ↔ ∀ y, σ y ∈ A ↔ y ∈ A := by
  constructor
  · exact fun h y => apply_mem_iff_of_mem_Dec h y
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

theorem lt_one_transport {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) :
    A.valuation y < 1 ↔ A'.valuation (c y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hc, ← hc, map_eq_zero_iff _ c.injective]

theorem conjG_mem_Ine {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : g ∈ Ine (F := E) A) : conjG c τ hτ g ∈ Ine (F := E) A' := by
  have hsurj : ∀ y', ∃ y, y' = c y := fun y' => ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  refine ⟨?_, ?_⟩
  · have hD : g ∈ Dec (F := E) A := hg.1
    show conjG c τ hτ g ∈ Dec (F := E) A'
    rw [mem_Dec_iff'] at hD ⊢
    intro y'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← hc, ← hc, hD]
  · intro y' hy'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← map_sub, ← lt_one_transport c hc]
    rw [ValuationSubring.valuation_le_one_iff, ← hc, ← ValuationSubring.valuation_le_one_iff] at hy'
    exact hg.2 y hy'

theorem conjG_mem_wild {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : ∀ y : Ω, y ≠ 0 → A.valuation (g y / y - 1) < 1) :
    ∀ y : Ω, y ≠ 0 → A'.valuation (conjG c τ hτ g y / y - 1) < 1 := by
  intro y' hy'
  obtain ⟨y, rfl⟩ : ∃ y, y' = c y := ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  have hy : y ≠ 0 := fun h => hy' (by rw [h, map_zero])
  rw [conjG_apply_c, ← map_div₀, ← map_one c, ← map_sub, ← lt_one_transport c hc]
  exact hg y hy

end GlobalTheory.ConjTransport

namespace GlobalTheory

open GlobalTheory.ConjTransport

theorem conjGen_transport_exists : ∀ (D : D7) (w w' : PlE D.host) (γ : GE D.nd), IsConjPl D.host w w' →
    TameGenAt (D.nd.plOm.1 w) γ → ∃ γ' : GE D.nd, IsConjGen D w w' γ γ' ∧ TameGenAt (D.nd.plOm.1 w') γ' := by
  intro D w w' γ hww hγ
  let τ : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E)
  let c₀ : D.nd.Om ≃+* D.nd.Om := IsAlgClosure.equivOfEquiv D.nd.Om D.nd.Om τ
  have hc₀ : ∀ x, c₀ (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) :=
    IsAlgClosure.equivOfEquiv_algebraMap D.nd.Om D.nd.Om τ
  set A := D.nd.plOm.1 w with hAdef
  set A' := D.nd.plOm.1 w' with hA'def
  have hA : IsPlaceOver A w := D.nd.plOm.2 w
  have hA' : IsPlaceOver A' w' := D.nd.plOm.2 w'
  let B : ValuationSubring D.nd.Om := A.comap (c₀.symm : D.nd.Om →+* D.nd.Om)
  have hAB : ∀ y, y ∈ A ↔ c₀ y ∈ B := fun y => by
    show y ∈ A ↔ c₀.symm (c₀ y) ∈ A
    rw [RingEquiv.symm_apply_apply]
  have hB : IsPlaceOver B w' := by
    intro x
    let x'' : 𝓞 D.host.E := ⟨τ.symm x, (x.isIntegral_coe).map (τ.symm : D.host.E →+* D.host.E).toIntAlgHom⟩
    have h1 : algebraMap D.host.E D.nd.Om (x : D.host.E) = c₀ (algebraMap D.host.E D.nd.Om (x'' : D.host.E)) := by
      rw [hc₀]; congr 1
      show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm
    rw [h1, ← lt_one_transport c₀ hAB, hA x'']
    exact hww x'' x (by show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm)
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB hA'
  let c : D.nd.Om ≃+* D.nd.Om := c₀.trans σ.toRingEquiv
  have hcE : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) := by
    intro x
    show σ (c₀ _) = _
    rw [hc₀, AlgEquiv.commutes]
  have hcA : ∀ y, y ∈ A ↔ c y ∈ A' := by
    intro y
    rw [hAB, ← hσ, ← ValuationSubring.smul_mem_pointwise_smul_iff (g := σ), AlgEquiv.smul_def]
    rfl
  have hcA' : ∀ y, y ∈ A' ↔ c.symm y ∈ A := by
    intro y
    rw [hcA, RingEquiv.apply_symm_apply]
  refine ⟨conjG c τ hcE γ, ⟨c, fun x => hcE x, hcA, fun y => conjG_apply_c c τ hcE γ y⟩, ?_⟩
  refine ⟨conjG_mem_Ine c τ hcE hcA hγ.1, ?_⟩
  intro h hh
  have h1 := hγ.2 (conjG_mem_Ine c.symm τ.symm (symm_alg c τ hcE) hcA' hh)
  rw [← conjG_conjG_symm c τ hcE h]
  refine closure_mono ?_ (image_closure_subset_closure_image (conjG_continuous c τ hcE) ⟨_, h1, rfl⟩)
  rw [← Subgroup.coe_map, MonoidHom.map_closure]
  refine SetLike.coe_subset_coe.mpr (Subgroup.closure_mono ?_)
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with rfl | hg
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (conjG_mem_wild c τ hcE hcA hg)

end GlobalTheory
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LabTies

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def conjHom (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) :
    G E Ω →* G E Ω where
  toFun := GlobalTheory.AntiRamConj.conjAut c hc
  map_one' := by
    ext x
    exact c.apply_symm_apply x
  map_mul' g h := by
    ext x
    change c (g (h (c.symm x))) = c (g (c.symm (c (h (c.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem conjHom_apply (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (g : G E Ω) (x : Ω) : conjHom c hc g x = c (g (c.symm x)) := rfl

theorem continuous_conjHom (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) : Continuous (conjHom c hc) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).1 hU
  obtain ⟨S, hS⟩ := IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule
    ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))
  classical
  let L' := IntermediateField.adjoin E ((S.image c.symm : Finset Ω) : Set Ω)
  have hL' : FiniteDimensional E L' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Filter.mem_map.2 (Filter.mem_of_superset
    ((IntermediateField.fixingSubgroup_isOpen L').mem_nhds (Subgroup.one_mem _)) fun g hg => hLU ?_)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg
  have key : L ≤ IntermediateField.fixedField (Subgroup.zpowers (conjHom c hc g)) := by
    rw [← hS, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have h1 : conjHom c hc g x = x := by
      rw [conjHom_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer (G E Ω) x)).2 h1 hf
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (key hx) _ (Subgroup.mem_zpowers _)

theorem tameGenAt_transport (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (hc' : ∀ x : E, ∃ y : E, c (algebraMap E Ω x) = algebraMap E Ω y)
    {B B' : ValuationSubring Ω} (hB : ∀ y, y ∈ B ↔ c y ∈ B') {γ γ' : G E Ω} (hγ : ∀ y, γ' (c y) = c (γ y))
    (h : TameGenAt B γ) : TameGenAt B' γ' := by
  have hc'' : ∀ x : E, ∃ y : E, c.symm.symm (algebraMap E Ω x) = algebraMap E Ω y := hc'
  have eB : B' = GlobalTheory.AntiRamConj.moveVal c B := by
    ext y
    rw [GlobalTheory.AntiRamConj.mem_moveVal, hB, RingEquiv.apply_symm_apply]
  have eγ : γ' = conjHom c hc γ := by
    ext y
    rw [conjHom_apply, ← hγ, RingEquiv.apply_symm_apply]
  subst eB eγ
  set f := conjHom c hc
  refine ⟨GlobalTheory.AntiRamConj.conjAut_mem_ine c hc h.1, fun σ hσ => ?_⟩
  have h1 := GlobalTheory.AntiRamConj.conjAut_mem_ine c.symm hc'' hσ
  have e2 : GlobalTheory.AntiRamConj.moveVal c.symm (GlobalTheory.AntiRamConj.moveVal c B) = B := by
    ext x
    simp [GlobalTheory.AntiRamConj.mem_moveVal]
  rw [e2] at h1
  have e3 : σ = f (GlobalTheory.AntiRamConj.conjAut c.symm hc'' σ) := by
    ext x
    rw [conjHom_apply, GlobalTheory.AntiRamConj.conjAut_apply]
    simp
  rw [e3]
  refine map_mem_closure (continuous_conjHom c hc) (h.2 h1) fun τ hτ => ?_
  have h2 := Subgroup.mem_map_of_mem f hτ
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨a, ha | ha, rfl⟩
  · exact Or.inl (congrArg f ha)
  · refine Or.inr fun y hy => ?_
    rw [GlobalTheory.AntiRamConj.moveVal_lt_one, map_sub, map_div₀, map_one, conjHom_apply, RingEquiv.symm_apply_apply]
    exact ha _ ((map_ne_zero_iff _ c.symm.injective).2 hy)

end Galois

theorem main : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
    GlobalTheory.PendOf.LabAll D T → IneRep D ∧ LabDepth D ∧ LabGen D := by
  intro D T ⟨γ, h1, h2, h3⟩
  have hG : GenFam D γ := by
    refine ⟨h1, fun k w hw => ?_⟩
    obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [h1]
      exact D.ntypes.tg_gen k v
    · obtain ⟨c, hc1, hc2, hc3⟩ := h2 k v w hv
      refine tameGenAt_transport c (fun x => ⟨D.host.conj x, ?_⟩) (fun x => ⟨_, hc1 x⟩) hc2 hc3
        (D.ntypes.tg_gen k v)
      rw [RingEquiv.symm_apply_eq, hc1, GlobalTheory.AntiRamConj.host_conj_conj]
  have h3' : GlobalTheory.PendOf.Model.LabAll T γ := h3
  exact ⟨GlobalTheory.PendOf.Model.ineRep_of_tie T, GlobalTheory.PendOf.Model.labDepth_of_tie T hG h3',
    GlobalTheory.PendOf.Model.labGen_of_tie T hG h3'⟩

end GlobalTheory.LabTies

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.seriesIdempotentStarCompatible_of_labelling_agree : Green → ∀ (D : D7) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L → GlobalTheory.GoodTypes.SeriesConj D := by
  first | exact @GlobalTheory.GoodTypes.seriesConj_of_labTie | exact GlobalTheory.GoodTypes.seriesConj_of_labTie | (intros; apply GlobalTheory.GoodTypes.seriesConj_of_labTie <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.nonempty_typePlaceCompletionIdent : ∀ D : D7, Nonempty (Ident D) := by
  first | exact @GlobalTheory.TypeIdent.nonempty_ident | exact GlobalTheory.TypeIdent.nonempty_ident | (intros; apply GlobalTheory.TypeIdent.nonempty_ident <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.galois_sub_value_mem_filZero_of_monodromy_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ (hy : y ∈ ME D.toPhiMod) (σ : D.MMl), σ.1 ∈ D.desc.inv → D.conn σ.1 = D.zeta y → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) - (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero | exact GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero | (intros; apply GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.bcrisTensorIdentification_natural : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Q : PhiMod O K l e a κ) (T' : LocLat (Gl l) ℚ_[l] K O) (I' : Ident t ϖ Q T') (jB' : (κ → OB l O) ≃ₗ[OB l O] TW (OB l O) T') (f : LatHom T.L T'.L) (F : GlobalTheory.BK.Hom P Q), IsCrisCmp I' jB' → IsMapOf I I' f F → (∀ (m : P.MMl) (m' : Q.MMl), m'.1 = F.app m.1 → jB' (toBcris t ϖ Q m') = TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (jB (toBcris t ϖ P m))) ∧ ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ Q jB' (homW t ϖ F w) (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) b) := by
  first | exact @GlobalTheory.BKGal.cris_natural | exact GlobalTheory.BKGal.cris_natural | (intros; apply GlobalTheory.BKGal.cris_natural <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_fixes_crystalline_image_descentDatum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T), IsCrisCmp I jB → ∀ C : Conn P, C.nabla = P.nabla → Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C → IsHoriz (thetaW a LL) ϖ (sQ l) P jB := by
  first | exact @GlobalTheory.HorizXi.galois_fixes_xi | exact GlobalTheory.HorizXi.galois_fixes_xi | (intros; apply GlobalTheory.HorizXi.galois_fixes_xi <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.muPow_smul_crystallineValue_mem_ainfLattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (b₀ : TW (OB l O) T), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ → ∀ ε : OCb l, IsEps ε → ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) • b₀ = TWincl (toB l O) T z := by
  first | exact @GlobalTheory.BKExp.muPow_smul_crisVal_integral | exact GlobalTheory.BKExp.muPow_smul_crisVal_integral | (intros; apply GlobalTheory.BKExp.muPow_smul_crisVal_integral <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.cocycle_mem_lattice_on_kummerTowerGalois : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ ϖ.GKinf → ∃ x : ↥T.L.T, actB (sQ l) T g b - b = (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf | exact GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf | (intros; apply GlobalTheory.CocycleKinf.cocycle_mem_lattice_of_mem_GKinf <;> assumption)
end
