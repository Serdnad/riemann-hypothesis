module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle653
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle667
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle911
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixTranslates
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle669
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTau

open GlobalTheory.FibreAtTau

variable {D : D7}

theorem isHaarSub_map_closedEmb {H G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) (N : Subgroup H)
    (hN : IsClosed (N : Set H)) (ν : Measure H) (hν : GlobalTheory.Dec.IsHaarSub (N : Set H) ν) :
    GlobalTheory.Dec.IsHaarSub ((N.map ι : Subgroup G) : Set G) (ν.map ι) := by
  have hm : Measurable ι := hι.continuous.measurable
  have hc : IsClosed ((N.map ι : Subgroup G) : Set G) := hι.isClosedMap _ hN
  obtain ⟨h0, hK, hc0, hinv⟩ := hν
  refine ⟨?_, ⟨fun K hK' => ?_⟩, ?_, ?_⟩
  · rwa [Ne, Measure.map_eq_zero_iff hm.aemeasurable]
  · rw [Measure.map_apply hm hK'.isClosed.measurableSet]
    exact (hι.isCompact_preimage hK').measure_lt_top
  · rw [Measure.map_apply hm hc.measurableSet.compl]
    refine measure_mono_null (t := (N : Set H)ᶜ) (fun z hz hzN => hz ⟨z, hzN, rfl⟩) hc0
  · rintro _ ⟨m, hmN, rfl⟩
    rw [Measure.map_map (measurable_const_mul _) hm]
    have : ((fun x => ι m * x) ∘ ι) = ι ∘ (fun x => m * x) := by
      funext x; simp
    rw [this, ← Measure.map_map hm (measurable_const_mul _), hinv m hmN]

theorem isHaarSub_top {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] : GlobalTheory.Dec.IsHaarSub ((⊤ : Subgroup H) : Set H) ν := by
  refine ⟨NeZero.ne ν, inferInstance, by simp, fun m _ => MeasureTheory.map_mul_left_eq_self ν m⟩

theorem L_closed (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) :
    IsClosed (atP θ V C τ : Set (NI V C)) ∧ IsClosed (offP θ V C τ : Set (NI V C)) :=
  GlobalTheory.T.isClosed_unipotentRadical_atRealPlace_trivialAtPlace D θ hθ V r C τ

theorem L_comm (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) :
    (∀ p ∈ atP θ V C τ, ∀ q ∈ offP θ V C τ, p * q = q * p) ∧ ∀ h, h ∈ atP θ V C τ → h ∈ offP θ V C τ → h = 1 :=
  GlobalTheory.T.unipotentRadical_atRealPlace_commute_inf_trivial D θ hθ V r C τ

theorem L_decomp (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : IsIsoFrame V C) (τ : D.what₂.Tau) (h : NI V C) : ∃ p ∈ atP θ V C τ, ∃ q ∈ offP θ V C τ, h = p * q :=
  GlobalTheory.T.unipotentRadical_eq_atRealPlace_mul_trivialAtPlace D θ hθ V r C hC τ h

theorem L_factor (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ) (τ : D.what₂.Tau) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (q : NI V C) (hq : q ∈ offP θ V C τ) (x y : GA D V) :
    ∃ R : ℂ, ∀ p ∈ atP θ V C τ, coef θ M K v a (x * ((p * q : NI V C) : GA D V) * y) =
      ⟪v τ, M.rep τ (cmp θ τ x * cmp θ τ (p : GA D V) * cmp θ τ y) (a τ)⟫_ℂ * R :=
  GlobalTheory.T.levelIndicatorTestFunction_factor_atRealPlace D θ hθ V S M K v a τ r C q hq x y

theorem L_hom (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) : ∃ E : GA D V →* Formalism.REAL.UJ (M.ε τ),
      ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ :=
  GlobalTheory.T.exists_realComponent_frame_hom_unitaryDiag D θ hθ V S M τ

theorem L_emb (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (E : GA D V →* Formalism.REAL.UJ (M.ε τ)) (hE : ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) :
    ∃ W : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.Dec.IsIsoC (M.ε τ) W ∧
      Topology.IsClosedEmbedding (fun p : atP θ V C τ => E ((p : NI V C) : GA D V)) ∧
      Set.range (fun p : atP θ V C τ => E ((p : NI V C) : GA D V)) = GlobalTheory.Dec.NW (M.ε τ) W :=
  GlobalTheory.T.isClosedEmbedding_realComponent_unipotentRadical D θ hθ V S M τ r C hC E hE

theorem fibre_integral_eq_zero : GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (v a : ∀ τ, M.H τ), (∀ τ, v τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → (∀ τ, a τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) →
    ∀ (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ P Q : Subgroup (NI V C), IsClosed (P : Set (NI V C)) ∧ IsClosed (Q : Set (NI V C)) ∧
      (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧ (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) ∧ (∀ h, h ∈ P → h ∈ Q → h = 1) ∧
      ∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∀ x y : GA D V,
        ∫ p, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) ∂ν = 0 := by
  intro hP D θ hθ V S M K v a hv ha τ r C hC
  refine ⟨atP θ V C τ, offP θ V C τ, (L_closed θ hθ V C τ).1, (L_closed θ hθ V C τ).2, (L_comm θ hθ V C τ).1,
    L_decomp θ hθ V C hC τ, (L_comm θ hθ V C τ).2, ?_⟩
  intro ν hν q hq x y
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.REAL.UJ (M.ε τ)) := ⟨rfl⟩
  obtain ⟨E, hE⟩ := L_hom θ hθ V S M τ
  obtain ⟨W, hW, hemb, hrange⟩ := L_emb θ hθ V S M τ C hC E hE
  obtain ⟨R, hR⟩ := L_factor θ hθ V S M K v a τ C q hq x y
  let ι : atP θ V C τ →* Formalism.REAL.UJ (M.ε τ) := E.comp ((NI V C).subtype.comp (atP θ V C τ).subtype)
  have hι : Topology.IsClosedEmbedding ι := hemb
  have hmap := isHaarSub_map_closedEmb ι hι ⊤ isClosed_univ ν (isHaarSub_top ν)
  have hr : (((⊤ : Subgroup (atP θ V C τ)).map ι : Subgroup _) : Set _) = GlobalTheory.Dec.NW (M.ε τ) W := by
    rw [← MonoidHom.range_eq_map, MonoidHom.coe_range]
    exact hrange
  rw [hr] at hmap
  have hsq : GlobalTheory.Dec.IsSqIntIrr (M.ε τ) (M.σ τ) := by
    have hDS := M.ds τ
    exact ⟨hDS.1, hDS.2.1, hDS.2.2.1, hDS.2.2.2.1, hDS.2.2.2.2.1⟩
  have h0 := ((GlobalTheory.Published.discreteSeriesCoefficientsCuspidal_iff.1 hP) V.rank (M.ε τ) (M.H τ) (M.σ τ) hsq (a τ) (v τ)
    (ha τ) (hv τ) W hW (ν.map ι) hmap (E x) (E y)).2
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ p : atP θ V C τ, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) =
      ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * ι p * E y)) (a τ)⟫_ℂ * R := by
    intro p
    rw [hR p p.2]
    congr 2
    show M.σ τ (M.fr τ * _ * (M.fr τ)⁻¹) (a τ) = M.σ τ _ (a τ)
    congr 2
    change M.fr τ * _ * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat (E x) * Formalism.MainNotions.S.umat (E ((p : NI V C) : GA D V)) * Formalism.MainNotions.S.umat (E y)
    rw [hE, hE, hE]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  simp_rw [key]
  have hint := hι.measurableEmbedding.integral_map (μ := ν)
    (fun m => ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * m * E y)) (a τ)⟫_ℂ)
  rw [integral_mul_const, ← hint, h0, zero_mul]

end GlobalTheory.FibreAtTau
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology


noncomputable section

namespace GlobalTheory.VacTranslateLeft

theorem exists_open_fix_translate_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∀ u : WO S T, u.map (infPart D) = 0 →
    ∃ U : Subgroup (GA D S), IsOpen (U : Set (GA D S)) ∧ ∀ κ ∈ U, κ ∈ GfC S →
      heisO ψ S T (actO S T κ 1 u) f₀ = heisO ψ S T u f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT hS hT f₀ hvac u hu
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO'
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) u hu
  have hN : 0 < 2 * (2 * 2) * M * M := by positivity
  have hev := GlobalTheory.LatNhds.eventually_move S T ΛS ΛT hS hT u hu (2 * (2 * 2) * M * M) hN
  have hc : Filter.Tendsto (fun κ : GA D S => (κ, (1 : GA D T))) (𝓝 1) (𝓝 1) := by
    have := (continuous_id.prodMk (continuous_const (y := (1 : GA D T)))).tendsto (1 : GA D S)
    simpa only [Prod.mk_one_one, id] using this
  have hev' := hc.eventually hev
  have key : ∃ n : ℕ, ∀ κ ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial κ →
      ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T κ 1 u = u + (2 * (2 * 2) * M * M) • l := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    obtain ⟨l, hl, e⟩ := hn
    exact hkne n l hl e
  obtain ⟨n, hn⟩ := key
  refine ⟨GlobalTheory.VacFixTarget.congGroup S n.factorial, GlobalTheory.VacFixTarget.isOpen_congGroup S n.factorial_pos,
    fun κ hκc hκ => ?_⟩
  obtain ⟨l, hl, e⟩ := hn κ hκ hκc
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have e2 : (2 * (2 * 2) * M * M) • l = 2 • ((2 * 2) • (M • (M • l))) := by
    simp only [smul_smul]
    congr 1
    ring
  have hu' : (2 * 2) • (M • (M • l)) ∈
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :=
    AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hl M) M) _
  have hs : ψ (symplOH S T u (2 • ((2 * 2) • (M • (M • l))))) = 1 := by
    rw [two_nsmul, GlobalTheory.SplitScalar.symplOH_add_right, GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.Mem.CoefInv.symplO_nsmul,
      ← GlobalTheory.Mem.CoefInv.symplO_nsmul, smul_comm M (2 * 2) u]
    exact GlobalTheory.VacTranslate.psi_four_eq_one hvac.2.lat.1 hw₀ hMu (AddSubgroup.nsmul_mem _ hl M)
  have h := GlobalTheory.SplitScalar.heisO_heisO ψ S T u (2 • ((2 * 2) • (M • (M • l)))) f₀
  rw [hvac.2.lat.1 _ hu', hs, one_smul] at h
  rw [e, e2, h]

end GlobalTheory.VacTranslateLeft

end
end
