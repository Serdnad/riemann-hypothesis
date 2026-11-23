module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

open GlobalTheory.HeisOrbit GlobalTheory.HeisOrbitSmooth

noncomputable section

namespace GlobalTheory.HeisOrbitSmoothLeft

open scoped ContDiff

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

local notation "Vs" κ => (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)

theorem at_mul_left {x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hx : At (evI F) x) (A : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    At (evI F) (A * x) := by
  intro a ha
  rw [← Matrix.mul_smul, hx a ha, Matrix.mul_zero]

theorem continuous_mat_line_left (γ : Multiplicative ℝ →* UA σ X.J) (hγ : Continuous γ) :
    Continuous fun t : ℝ => mat (γ (Multiplicative.ofAdd t)) :=
  Units.continuous_val.comp (continuous_subtype_val.comp (hγ.comp continuous_ofAdd))

theorem mat_mul_left (g h : UA σ X.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one_left : mat (1 : UA σ X.J) = 1 := rfl

def opLl (M : Model σ X W) (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : (Vs (Fin n × Fin d)) →ₗ[ℝ] Vs (Fin n × Fin d) where
  toFun w := GlobalTheory.HeisOrbit.archCo M.co (g * lift M.co w)
  map_add' w w' := by rw [lift_add, Matrix.mul_add, archCo_add]
  map_smul' c w := by rw [lift_smul, Matrix.mul_smul, archCo_smul]; rfl

theorem opLl_apply (M : Model σ X W) (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (w) :
    opLl M g w = GlobalTheory.HeisOrbit.archCo M.co (g * lift M.co w) := rfl

theorem opLl_archCo (M : Model σ X W) (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) {x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hx : At (evI F) x) : opLl M g (GlobalTheory.HeisOrbit.archCo M.co x) = GlobalTheory.HeisOrbit.archCo M.co (g * x) := by
  rw [opLl_apply, lift_archCo M.co hx]

def opRl (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (t : ℝ) :
    (Vs (Fin n × Fin d)) →L[ℝ] Vs (Fin n × Fin d) :=
  LinearMap.toContinuousLinearMap (opLl M (mat (γ (Multiplicative.ofAdd t))))

theorem opRl_apply (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (t : ℝ) (w) :
    opRl M γ t w = opLl M (mat (γ (Multiplicative.ofAdd t))) w := rfl

theorem opRl_zero (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) : opRl M γ 0 = 1 := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [opRl_apply, opLl_apply, ofAdd_zero, map_one, mat_one_left, Matrix.one_mul, archCo_lift]
  rfl

theorem opRl_add (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (s t : ℝ) :
    opRl M γ (s + t) = opRl M γ s * opRl M γ t := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [ContinuousLinearMap.mul_apply, opRl_apply, opRl_apply, opRl_apply,
    opLl_apply M (mat (γ (Multiplicative.ofAdd t))) w,
    opLl_archCo M _ (at_mul_left (at_lift M.co w) _),
    opLl_apply, ofAdd_add, map_mul, mat_mul_left, Matrix.mul_assoc]

theorem continuous_opRl (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (hγ : Continuous γ) :
    Continuous (opRl M γ) := by
  haveI : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
  refine continuous_clm_apply.2 fun w => ?_
  simp only [opRl_apply, opLl_apply]
  exact (continuous_archCo M).comp ((continuous_mat_line_left γ hγ).matrix_mul continuous_const)

theorem archCo_orbit_smooth_left : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ X, ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  intro F E _ _ _ _ _ σ n d X W M γ hγ u hu
  haveI : CompleteSpace ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    FiniteDimensional.complete ℝ _
  haveI : FiniteDimensional ℝ (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) :=
    ContinuousLinearMap.finiteDimensional
  have hcomp : CompleteSpace (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) :=
    FiniteDimensional.complete ℝ _
  have hs : ContDiff ℝ ∞ (opRl M γ) :=
    @GlobalTheory.contDiff_of_continuous_oneParameter _ _ _ hcomp (opRl M γ) (continuous_opRl M γ hγ.1) (opRl_zero M γ)
      (opRl_add M γ)
  have hf : (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) =
      fun t => opRl M γ t (GlobalTheory.HeisOrbit.archCo M.co u) := by
    funext t
    rw [opRl_apply, opLl_archCo M _ hu]
  rw [hf]
  refine ⟨hs.clm_apply contDiff_const, lift M.co (deriv (opRl M γ) 0 (GlobalTheory.HeisOrbit.archCo M.co u)), at_lift _ _, ?_⟩
  rw [archCo_lift]
  have hd : HasDerivAt (opRl M γ) (deriv (opRl M γ) 0) 0 :=
    ((hs.differentiable (by simp)) 0).hasDerivAt
  simpa using hd.clm_apply (hasDerivAt_const (0 : ℝ) (GlobalTheory.HeisOrbit.archCo M.co u))

end GlobalTheory.HeisOrbitSmoothLeft

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

noncomputable section

namespace GlobalTheory.CuspTraceSum

open GlobalTheory.OpTrace GlobalTheory.DiscreteSum ContinuousLinearMap
open scoped InnerProductSpace

theorem hasSum_trace_restrict {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ι : Type}
    {W : ι → Submodule ℂ K} [hW : ∀ i, CompleteSpace (W i)]
    (hs : IsHilbertSum ℂ (fun i => W i) fun i => (W i).subtypeₗᵢ) {T : K →L[ℂ] K} (hT : IsTraceClass T)
    (hTW : ∀ i, ∀ x ∈ W i, T x ∈ W i) :
    (∀ i, IsTraceClass (T.restrict (hTW i))) ∧ Summable (fun i => ‖trace (T.restrict (hTW i))‖) ∧
      HasSum (fun i => trace (T.restrict (hTW i))) (trace T) := by
  let b : ∀ i, HilbertBasis (stdIndex (W i)) ℂ (W i) := fun i => stdBasis (H := W i)
  let v : (Σ i, stdIndex (W i)) → K := fun a => (W a.1).subtypeₗᵢ (b a.1 a.2)
  have ho : Orthonormal ℂ v := hs.OrthogonalFamily.orthonormal_sigma_orthonormal fun i => (b i).orthonormal
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine eq_zero_of_isHilbertSum hs fun i y hy => ?_
    have h1 := ((b i).hasSum_repr ⟨y, hy⟩).mapL ((innerSL ℂ x).comp (W i).subtypeL)
    have h2 : ∀ j, ((innerSL ℂ x).comp (W i).subtypeL) ((b i).repr ⟨y, hy⟩ j • b i j) = 0 := fun j => by
      have h3 : ⟪v ⟨i, j⟩, x⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨⟨i, j⟩, rfl⟩)
      have h4 : ⟪x, (b i j : K)⟫_ℂ = 0 := inner_eq_zero_symm.1 h3
      simp [inner_smul_right, h4]
    have h5 : ⟪x, y⟫_ℂ = 0 := by
      have := h1.unique (hasSum_zero.congr_fun fun j => (h2 j))
      simpa using this
    exact inner_eq_zero_symm.1 h5
  let e : HilbertBasis (Σ i, stdIndex (W i)) ℂ K := HilbertBasis.mkOfOrthogonalEqBot ho hsp
  have he : ∀ a, e a = v a := fun a => by simp [e]
  have hR : ∀ i, (T.restrict (hTW i)) = (W i).orthogonalProjection ∘L T ∘L (W i).subtypeL := fun i => by
    ext x
    simp [Submodule.orthogonalProjection_mem_subspace_eq_self (K := W i) ⟨_, hTW i x x.2⟩]
  have htc : ∀ i, IsTraceClass (T.restrict (hTW i)) := fun i => by
    rw [hR i]; exact hT.comp_comp _ _
  have hterm : ∀ a : Σ i, stdIndex (W i), ⟪e a, T (e a)⟫_ℂ = ⟪b a.1 a.2, T.restrict (hTW a.1) (b a.1 a.2)⟫_ℂ :=
    fun a => by rw [he]; rfl
  have hsum := hT.hasSum_trace e
  have hnorm := hT.summable_norm e
  simp only [hterm] at hsum hnorm
  refine ⟨htc, ?_, hsum.sigma fun i => (htc i).hasSum_trace (b i)⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hnorm.sigma
  rw [← ((htc i).hasSum_trace (b i)).tsum_eq]
  exact norm_tsum_le_tsum_norm ((htc i).summable_norm (b i))

end GlobalTheory.CuspTraceSum

namespace GlobalTheory.CuspTraceSum

open GlobalTheory.OpTrace GlobalTheory.DiscreteSum GlobalTheory.AutMult GlobalTheory.AutomorphicL2Unitary MeasureTheory

theorem hasSum_multIn_repTrace {G K : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ρ : G →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ) (hD : IsDiscreteSum ρ) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hT : IsTraceClass (repOp ρ μ f)) :
    (∀ c : UDual G, multIn c.rep.π ρ ⊤ ≠ 0 → IsTraceClass (repOp c.rep.π μ f)) ∧
      (Summable fun c : UDual G => ‖((multIn c.rep.π ρ ⊤).toNat : ℂ) * repTrace c.rep.π μ f‖) ∧
      HasSum (fun c : UDual G => ((multIn c.rep.π ρ ⊤).toNat : ℂ) * repTrace c.rep.π μ f) (trace (repOp ρ μ f)) := by
  obtain ⟨⟨ι, W, hWi, hs⟩, hfin⟩ := hD
  haveI : ∀ i, CompleteSpace (W i) := fun i => (hWi i).1.completeSpace
  have hR : IsRepOp ρ μ f (repOp ρ μ f) := hρ.isRepOp hf hfs
  have hTW : ∀ i, ∀ x ∈ W i, repOp ρ μ f x ∈ W i := fun i x hx => (hWi i).1.map_mem_of_isRepOp hR hx
  obtain ⟨htc, hsn, hsum⟩ := hasSum_trace_restrict hs hT hTW
  have hrest : ∀ i, repOp (hWi i).1.rep μ f = (repOp ρ μ f).restrict (hTW i) := fun i =>
    ContinuousLinearMap.ext fun x => Subtype.ext (((hWi i).1.coe_repOp_rep hR).2 x)
  let cls : ι → UDual G := fun i => (⟨W i, (hWi i).1.rep, isIrrUnitary_rep hρ (hWi i)⟩ : IrrU G).cl
  have hcls : ∀ c i, cls i = c ↔ IsCopy c.rep.π ρ (W i) := fun c i => by
    conv_lhs => rw [← UDual.cl_rep c]
    rw [IrrU.cl_eq_iff]
    exact ⟨fun h => ⟨(hWi i).1, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  have htr : ∀ c i, cls i = c →
      IsTraceClass (repOp c.rep.π μ f) ∧ repTrace c.rep.π μ f = trace ((repOp ρ μ f).restrict (hTW i)) := by
    intro c i hi
    obtain ⟨_, e, he⟩ := (hcls c i).1 hi
    have h2 : IsTraceClass (repOp (hWi i).1.rep μ f) := by rw [hrest]; exact htc i
    obtain ⟨h3, h4⟩ := ((hWi i).1.isUnitaryRep hρ).repTrace_eq_of_equiv c.rep.isIrr.unitary hf hfs
      e.symm.toContinuousLinearEquiv (fun g x => by
        apply e.injective
        rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, he, LinearIsometryEquiv.apply_symm_apply,
          LinearIsometryEquiv.apply_symm_apply]) h2
    refine ⟨h3, h4.trans ?_⟩
    rw [repTrace, hrest]
  have hmult : ∀ c : UDual G, (cls ⁻¹' {c}).Finite ∧ multIn c.rep.π ρ ⊤ = (cls ⁻¹' {c}).ncard := by
    intro c
    obtain ⟨h1, h2⟩ := multIn_eq_ncard hρ c.rep.isIrr (hfin c.rep) hWi hs
    have e : cls ⁻¹' {c} = {i | IsCopy c.rep.π ρ (W i)} := Set.ext fun i => hcls c i
    rw [e]
    exact ⟨h1, h2⟩
  have hfib : ∀ c : UDual G, ∑' b : ↑(cls ⁻¹' {c}), trace ((repOp ρ μ f).restrict (hTW b)) =
      ((multIn c.rep.π ρ ⊤).toNat : ℂ) * repTrace c.rep.π μ f := by
    intro c
    rw [tsum_congr fun b : ↑(cls ⁻¹' {c}) => (htr c b b.2).2.symm, tsum_const, nsmul_eq_mul, (hmult c).2,
      Cardinal.toNat_natCast, Nat.card_coe_set_eq]
  refine ⟨fun c hc => ?_, ?_, ?_⟩
  · rw [(hmult c).2] at hc
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (by exact_mod_cast hc)
    exact (htr c i hi).1
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => ?_)
      (hsn.hasSum.tsum_fiberwise cls).summable
    rw [← hfib]
    exact norm_tsum_le_tsum_norm (hsn.subtype _)
  · exact (hsum.tsum_fiberwise cls).congr_fun fun c => (hfib c).symm

end GlobalTheory.CuspTraceSum

namespace GlobalTheory.CuspTraceSum

open GlobalTheory.DiscreteSum

theorem hasSum_mCusp_repTrace : GlobalTheory.Published.CuspTraceClass → ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, (∀ c : UDual (GA D V), mCusp V μ c.rep.π ≠ 0 → IsTraceClass (repOp c.rep.π μ f)) ∧ (Summable fun c : UDual (GA D V) => ‖((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f‖) ∧ HasSum (fun c : UDual (GA D V) => ((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f) (trace (RcuspOp V μ f)) := by
  intro hP D V μ _ _ f hf
  have hfc := continuous_of_mem_ccAd hf
  have h := hasSum_multIn_repTrace (isUnitaryRep_Rcusp V μ)
    (Published.cuspDiscreteDecomposition_of_traceClass hP D V μ) μ hfc.1 hfc.2 (hP D V μ f hf)
  have e : ∀ c : UDual (GA D V), mCusp V μ c.rep.π = multIn c.rep.π (Rcusp V μ) ⊤ := fun c =>
    (multIn_rep (isSubrep_L2cusp V μ)).symm
  simp only [e]
  exact h

end GlobalTheory.CuspTraceSum

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.MovedField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.FunObj Formalism.L2.Host ValuativeRel

variable {D : D7}

theorem exists_zpow_unit (w : Pl D.host.E) (x : (Kw w)ˣ) :
    ∃ n : ℤ, Valued.v (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := by
  have h0 : Valued.v (x : Kw w) ≠ 0 := by simp
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx : Valued.v (x : Kw w) = WithZero.exp (WithZero.log (Valued.v (x : Kw w))) := (WithZero.exp_log h0).symm
  refine ⟨WithZero.log (Valued.v (x : Kw w)), ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, hu, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  simp

theorem natCast_cpow_half (N : ℕ) (m : ℤ) :
    (N : ℂ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N : ℝ) : ℂ) ^ m := by
  rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

theorem sqrt_absNorm_ne_zero (w : Pl D.host.E) : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ≠ 0 := by
  have h : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)
  exact_mod_cast (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)))

theorem apow_half_mem {w : Pl D.host.E} {K : Subfield ℂ}
    (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) (z : ℤ) : apow x ((z : ℂ) / 2) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have h1 : valuation (Kw w) (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := (Good.isEquiv_Kw w).eq_one_iff_eq_one.2 hn
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, apow_mul, apow_of_valuation_eq_one h1, one_mul, apow_zpow, (isUnif_unifAt w).apow_eq,
    GlobalTheory.LFun.SatBoundGL.resCard_completion]
  have e1 : -(((-n : ℤ) : ℂ) * ((z : ℂ) / 2)) = ((((n * z : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, natCast_cpow_half]
  exact zpow_mem hs _

theorem loc_mem_of_unrAt {w : Pl D.host.E} {K : Subfield ℂ} {χ : HChar D.host.E} (hu : χ.UnrAt w)
    (hv : χ.valTw (1 / 2) w ∈ K) (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) :
    ((χ.loc w x : ℂˣ) : ℂ) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, map_mul, hu _ hn, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  refine zpow_mem ?_ _
  have e1 : -(((1 / 2 : ℝ)) : ℂ) = ((((-1 : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hval : χ.valTw (1 / 2) w = ((χ.loc w (unifAt w) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)⁻¹ := by
    rw [HChar.valTw, e1, natCast_cpow_half, zpow_neg_one]
    rfl
  have : ((χ.loc w (unifAt w) : ℂˣ) : ℂ) = χ.valTw (1 / 2) w * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) := by
    rw [hval, inv_mul_cancel_right₀ (sqrt_absNorm_ne_zero w)]
  rw [this]
  exact mul_mem hv hs

theorem units_prod_mem {α : Type*} (K : Subfield ℂ) (f : α → ℂˣ) :
    ∀ l : List α, (∀ a ∈ l, ((f a : ℂˣ) : ℂ) ∈ K) → (((l.map f).prod : ℂˣ) : ℂ) ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons, Units.val_mul]
    exact mul_mem (h a List.mem_cons_self) (units_prod_mem K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem list_prod_mem' {α : Type*} (K : Subfield ℂ) (f : α → ℂ) :
    ∀ l : List α, (∀ a ∈ l, f a ∈ K) → (l.map f).prod ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (h a List.mem_cons_self) (list_prod_mem' K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

end GlobalTheory.MovedField


open GlobalTheory.MovedField GlobalTheory.SplitFlip GlobalTheory.SplitWeil Formalism.L2.Host in
theorem GlobalTheory.MovedField.moved_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b _ _ _ hF t Φ _ β _ w S hS z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (w : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt w.1 (.inr ⟨t, w.2⟩))

  have hmu : ∀ j (x : (Kw w.1)ˣ), (((locGrid ch.G t w).mu j x : ℂˣ) : ℂ) ∈ K := fun j x => by
    change ((GlobalTheory.FunObj.muBase R.toLevCh j).loc w.1 x : ℂ) *
      ((R.xiH t).loc w.1 x : ℂ) ∈ K
    refine mul_mem ?_ ((hK _).1 (hF.chars.xi t _ x))
    rcases j with _ | j
    · exact one_mem K
    · rw [GlobalTheory.FunObj.muBase]
      split_ifs with hj
      · exact (hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x)
      · exact one_mem K
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).chi i x : ℂˣ) : ℂ) ∈ K :=
    fun i h1 h2 x => (hK _).1 (hF.chars.chi i h1 h2 _ x)
  have heta : ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).eta x : ℂˣ) : ℂ) ∈ K := fun x => by
    have hu := R.toLevCh.C.isEta.unr w.1
    obtain ⟨y, hy⟩ := hF.chars.eta w.1 hu
    exact loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x

  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw w.1)ˣ), (((locGrid ch.G t w).kappa e X x : ℂˣ) : ℂ) ∈ K := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    refine div_mem ?_ (pow_mem (heta x) _)
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw w.1)ˣ) (n : ℕ), apow x ((n : ℂ) / 2) ∈ K ∧ apow x (-(n : ℂ) / 2) ∈ K := fun x n =>
    ⟨by simpa using apow_half_mem hsq x n, by simpa using apow_half_mem hsq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, (locGrid ch.G t w).edgeFactor .one g e ∈ K := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact mul_mem (mul_mem (mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))) (hap _ _).1) (hap _ _).2
  have hchar : ∀ g, ((((charFactor (locGrid ch.G t w) g)⁻¹ : ℂˣ)) : ℂ) ∈ K := by
    intro g
    rw [Units.val_inv_eq_inv_val]
    refine inv_mem (units_prod_mem K _ _ fun e he => ?_)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))
  rw [hK]
  simp only [moved, Grid.pathAct]
  refine mul_mem ?_ (mul_mem (list_prod_mem' K _ _ (hedge _)) ((hK _).1 (hS _)))
  split
  · exact one_mem K
  · exact hchar _
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

namespace GlobalTheory.FormCoef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem typeX_mem (R : RealDat D A Ks) (t : T) (M : Subfield ℂ)
    (hχ : ∀ i : Fin D.R.m, ∀ PP ∈ R.Pg, ∀ x, ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ M)
    (hξ : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t PP x : ℂˣ) : ℂ) ∈ M) (k) :
    (((levEnv D.sp.X' R.βX (R.datXt t)).χ k : ℂˣ) : ℂ) ∈ M := by
  show levFn R.βX (Lev.flag1L (R.datXt t)) _ ∈ GlobalTheory.RationalValues.unitsIn M
  unfold levFn
  refine mul_mem (mul_mem ?_ (prod_mem fun PP hPP => prod_mem fun c hc => ?_)) (prod_mem fun PP hPP => ?_)
  · have h1 : ∀ x, ext1 (Lev.flag1L (R.datXt t)).P.H (Lev.flag1L (R.datXt t)).P.chi x = 1 := fun x => Lev.subgroupCharExtension_one_apply _ x
    rw [h1]
    exact one_mem _
  · have hc' : c < D.R.m := Finset.mem_range.1 hc
    exact show R.chi ((⟨c, hc'⟩ : Fin D.R.m) + 1 : ℕ) PP _ ∈ GlobalTheory.RationalValues.unitsIn M from hχ ⟨c, hc'⟩ PP hPP _
  · exact inv_mem (show R.xiR t PP _ ∈ GlobalTheory.RationalValues.unitsIn M from hξ PP hPP _)

end GlobalTheory.FormCoef

namespace GlobalTheory.FormCoef

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem coeff_formC_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A),
    HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (x : A.fam.amb.FR t) (y : FinPt ch.G (.grid 0 D.R.m)) m,
      AddMonoidAlgebra.coeff (ch.S.formC t (R.jX t x) y).1 m ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F hS _ _ t x y m
  obtain ⟨gram, c₀, c₁, hT, hco⟩ := ch.S.co_is
  have hc := hS.core
  obtain ⟨k, v, hv⟩ := GlobalTheory.RationalValues.exists_ext_eq (R.B.R t).pres c₀ (GlobalTheory.RationalValues.coef_mem (hT.coefR t))
    (GlobalTheory.RationalValues.rho_mem hT.mapR) x (toXf y)
  have h0 : (R.HX t).e (R.jX t x) (toXf y) = (((levEnv D.sp.X' R.βX (R.datXt t)).χ k : ℂˣ) : ℂ) • c₀ v :=
    (congrFun (hc.models.jX t x) (toXf y)).trans hv
  have i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  obtain ⟨a, ha⟩ := typeX_mem R t D.what₂.embLL.fieldRange (GlobalTheory.RationalValues.chiVal_of_chiW R hc.grp.chiW)
    (GlobalTheory.RationalValues.xiR_mem R hc.lev hc.fam.pl_onto hc.fam.muVal hT.ok i0 t) k
  have h1 : ch.S.formC t (R.jX t x) y = ch.S.co (c₀ (a • v)) := by
    rw [SumChoice.formC, h0, map_smulₛₗ, ha]
  rw [h1, hco, ← MvPolynomial.map_rename, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩

end GlobalTheory.FormCoef
end
end
