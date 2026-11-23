module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle101
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle435
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle457
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle454
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle453
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist

@[expose] public section

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.KType

theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]

    rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finsetSum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    LinearMap.pi fun k => LinearMap.applyₗ (ρ k)
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ.comp (LinearMap.applyₗ w), rfl⟩
  exact Submodule.finiteDimensional_of_le this

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem eventually_eq_chart (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a)
    (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, φ.1 (unip x * g) =
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hlev.mem_nhds h1)] with x hx
  have hx' : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) φ = φ := hx
  rw [chart_val, JointCont.unip_mul_eq, ← mul_inv_cancel_left (JointCont.finPart g x₀) (JointCont.finPart g x),
    map_mul, mul_assoc, ← infGL_comm, ← mul_assoc]
  exact congrArg (fun ψ : Sm E a => ψ.1 (finGL E a (JointCont.finPart g x₀) * infGL E a (JointCont.infPart g x))) hx'

theorem continuous_unip_mul (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hf₀ : ContDiffOn ℝ ∞ (chart φ.1 (finGL E a (JointCont.finPart g x₀))) (invSet E a) := φ.2 _
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E =>
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a (JointCont.finPart g x₀)))
      (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  have hE : (fun x : BlockIx a r → Ad E => φ.1 (unip x * g)) =ᶠ[𝓝 x₀]
      fun x => chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) :=
    eventually_eq_chart φ hlev g x₀
  exact hA.congr hE.symm

theorem exists_bound_unip_mul (φ : Sm E a) (hleft : ∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hCm : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hCm.exists_bound_of_continuousOn (continuous_unip_mul (r := r) φ hlev g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Set.univ.pi fun _ : BlockIx a r => K,
      x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  rw [unip_add, unip_algebraMap, mul_assoc, hleft]
  exact hC x' hx'm

theorem ct_mem_coeffSpan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  intro E _ _ _ a r φ hleft hlev W _ _ _ ρ hρ _ _ μ 𝓕 hμ hF g
  haveI := hμ
  haveI := finiteDimensional_coeffSpan ρ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine integral_mem (μ.restrict 𝓕) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun x k => φ.1 (unip x * (g * infGL E a (Unitary.toUnits k)))) (fun x => ?_) (fun k => ?_)
  · have e : ∀ k : Kinf E a, (cptRep E a k φ).1 (unip x * g) = φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) :=
      fun k => by rw [← mul_assoc]; rfl
    have := hρ (unip x * g)
    simp only [e] at this
    exact this
  · obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) φ hleft hlev (g * infGL E a (Unitary.toUnits k))
    exact Integrable.of_bound (continuous_unip_mul φ hlev _).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)

end GlobalTheory.CompanionTheory.CTFin.KType

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

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderSub

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)
open GlobalTheory.CompanionTheory.MPDict.Onto GlobalTheory.CompanionTheory.MPDict.Under

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem point_eq_pt {N : ℕ} (t : Fin (N + 1) → ℂ) (ht : t ≠ 0) (hu : Ideal.span (Set.range t) = ⊤) :
    GlobalTheory.TuplePoint.point ℤ t ht = GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) t hu := by
  unfold GlobalTheory.TuplePoint.point GlobalTheory.ProjSpace.pt
  congr 1

theorem le_mCoordIdeal_of_mem_mcPts {P : Ideal (Geo.MRing (Bk n))} (hP : Geo.IsMultiHomogIdeal P)
    {z : (Σ k, Bk n k) → ℂ} (hz : z ∈ mcPts P) : P ≤ Geo.mCoordIdeal z := by
  obtain ⟨S, hS, hPS⟩ := hP
  have h0 := hz.2
  rw [hPS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have e : aeval z f = 0 := by
    have := h0 f (hPS ▸ Ideal.subset_span hf)
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
    simpa using this
  rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, e, C_0, mul_zero]

theorem ptIdeal_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {w : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder w z) :
    ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) = Geo.mCoordIdeal z := by
  have ht := blockVec_ne_zero hz'
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => z ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hz' k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
  let g : Sp ℂ ⟶ MP ℤ m n := w.1
  have hg : ∀ k, g ≫ prB n k = a k := fun k =>
    (comp_of_isUnder ht hz' H k).trans (point_eq_pt _ _ (hu k))
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  let x : MP ℤ m n := g p
  let θ : ℂ →+* (Sp ℂ).residueField p :=
    ((Sp ℂ).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp ℂ).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (z ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (z ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp ℂ).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : ℂ, ((Sp ℂ).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp ℂ).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (z ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  change ptIdeal x = _
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ z,
    ← mCoordIdeal_blockScale (fun k => θ (z ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

theorem exists_cxPt_of_mem_mcPts : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (z : (Σ k, Bk n k) → ℂ), z ∈ mcPts (ptIdeal (i (genericPoint X))) →
    ∃ y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀, IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ z hz
  obtain ⟨w, hw, -⟩ := existsUnique_isUnder m n z hz.1
  have hP : ptIdeal (i (genericPoint X)) ≤ ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) := by
    rw [ptIdeal_of_isUnder hz.1 hw]
    exact le_mCoordIdeal_of_mem_mcPts (isMultiProjPrime_ptIdeal m n _).2.1 hz
  have hs := (GlobalTheory.T.specializes_iff_point_ideal_le m n _ _).2 hP
  have hr : w.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range i :=
    hs.mem_closed i.isClosedEmbedding.isClosed_range ⟨_, rfl⟩
  have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨f, hf⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i w.1 Set.univ dense_univ
    fun q _ => by rwa [Subsingleton.elim q (IsLocalRing.closedPoint ℂ)]
  refine ⟨⟨f, by rw [← Category.assoc, hf]; exact w.2⟩, ?_⟩
  have e : PtsOver.map i rfl _ (⟨f, by rw [← Category.assoc, hf]; exact w.2⟩ : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) = w :=
    Subtype.ext hf
  rw [e]
  exact hw

end GlobalTheory.CompanionTheory.MPDict.UnderSub
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup


theorem _root_.GlobalTheory.T.generic_point_nonvanishing_coordinate_section : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (k : Fin (m + 1)) (l : Bk n k), (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f (genericPoint Z)) → genericPoint Z ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.VertGen.genericPoint_mem_nonzeroLocus | exact GlobalTheory.CompanionTheory.MixZ.VertGen.genericPoint_mem_nonzeroLocus | (intros; apply GlobalTheory.CompanionTheory.MixZ.VertGen.genericPoint_mem_nonzeroLocus <;> assumption)
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup


theorem _root_.GlobalTheory.T.hermRep_class_decomposition : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)), IsHermRep M A → cls M.B M.isLB = ∑ k, A.a k • cls (pullO (prB n k) 1) (isLB_pullO _ 1) := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep | exact GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep | (intros; apply GlobalTheory.CompanionTheory.MPDict.ClsRep.cls_eq_of_isHermRep <;> assumption)
end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.UniSol

theorem exists_finset_separating {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset K, ∀ c ∈ A, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  classical
  have key : ∀ (n : ℕ) (B : Submodule ℂ A), Module.finrank ℂ B = n →
      ∃ S : Finset K, ∀ c ∈ B, (∀ κ ∈ S, (c : K → ℂ) κ = 0) → c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro B hB
      by_cases hbot : B = ⊥
      · refine ⟨∅, fun c hc _ => ?_⟩
        rw [hbot] at hc
        exact (Submodule.mem_bot ℂ).mp hc
      · obtain ⟨c0, hc0B, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
        obtain ⟨κ0, hκ0⟩ : ∃ κ0, (c0 : K → ℂ) κ0 ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hc0 (Subtype.ext (funext hcon))
        let ev : A →ₗ[ℂ] ℂ := (LinearMap.proj κ0).comp A.subtype
        let B' : Submodule ℂ A := B ⊓ LinearMap.ker ev
        have hlt : B' < B := by
          refine lt_of_le_of_ne inf_le_left (fun h => hκ0 ?_)
          have hmem : c0 ∈ B' := by
            rw [h]
            exact hc0B
          exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
        have hrk : Module.finrank ℂ B' < n := by
          have := Submodule.finrank_lt_finrank_of_lt hlt
          omega
        obtain ⟨S', hS'⟩ := ih _ hrk B' rfl
        refine ⟨insert κ0 S', fun c hc hvan => hS' c ?_ (fun κ hκ => hvan κ (Finset.mem_insert_of_mem hκ))⟩
        refine Submodule.mem_inf.mpr ⟨hc, LinearMap.mem_ker.mpr ?_⟩
        exact hvan κ0 (Finset.mem_insert_self κ0 S')
  obtain ⟨S, hS⟩ := key _ ⊤ rfl
  refine ⟨S, fun c hc hvan => ?_⟩
  have h0 := hS ⟨c, hc⟩ Submodule.mem_top hvan
  exact congrArg Subtype.val h0

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let m : (Module.Free.ChooseBasisIndex ℂ W) × (Module.Free.ChooseBasisIndex ℂ W) → (K → ℂ) :=
    fun ij k => b.repr (ρ k (b ij.2)) ij.1
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range m)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range m)
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ Submodule.span ℂ (Set.range m) := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.mpr ?_
    rintro f ⟨ℓ, w, rfl⟩
    have hw : ∀ v : W, ℓ v = ∑ i, b.repr v i * ℓ (b i) := by
      intro v
      conv_lhs => rw [← b.sum_repr v]

      simp only [map_sum, map_smul, smul_eq_mul]
    have hf : (fun k => ℓ ((ρ k) w)) = ∑ ij, (b.repr w ij.2 * ℓ (b ij.1)) • m ij := by
      funext k
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, m]
      rw [Fintype.sum_prod_type]
      dsimp only
      have h1 : ℓ (ρ k w) = ∑ j, b.repr w j * ℓ (ρ k (b j)) := by
        conv_lhs => rw [← b.sum_repr w]

        simp only [map_sum, map_smul, smul_eq_mul]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hw (ρ k (b j)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [hf]
    exact Submodule.sum_mem _ (fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle

theorem coeffSpan_unisolvent : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  intro K W _ _ _ _ ρ
  haveI := finiteDimensional_coeffSpan ρ
  exact exists_finset_separating _

end GlobalTheory.CompanionTheory.CTFin.UniSol

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem countable_mat_cosets : ∀ (D : D7) (a b : ℕ), Countable (Matrix (Fin a) (Fin b) D.host.E) ∧ Countable (GlobalTheory.Eis.Cosets (P D b) (GF D b)) := by
  intro D a b
  have hE : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  refine ⟨inferInstanceAs (Countable (Fin a → Fin b → D.host.E)), ?_⟩
  have hM : Countable (Matrix (Fin (b + b)) (Fin (b + b)) D.host.E) :=
    inferInstanceAs (Countable (Fin (b + b) → Fin (b + b) → D.host.E))
  have hGL : Countable (GL (Fin (b + b)) D.host.E) :=
    (Units.val_injective (α := Matrix (Fin (b + b)) (Fin (b + b)) D.host.E)).countable
  have hG : Countable (GF D b) := by
    have hR : Countable (GRat D.sp.cm.sig (Jst D b)) := by
      unfold GRat
      exact Subtype.val_injective.countable
    show Countable (ratPts D.sp.cm.sig (Jst D b))
    rw [← range_ratEmb]
    exact (Set.countable_range (ratEmb D.sp.cm.sig (Jst D b))).to_subtype
  exact Quotient.countable

end GlobalTheory.CompanionTheory.FJE
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.hyperbolic_sum_nondegenerate_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem <;> assumption)
end
