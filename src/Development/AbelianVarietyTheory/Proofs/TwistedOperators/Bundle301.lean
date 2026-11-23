module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle082
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle080
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissible
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacuumLine

open GlobalTheory.FockCompare GlobalTheory.VacUnique

private theorem selfDual_isFullLattice {D : D7} {V : HSp D}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ) :
    Submodule.IsFullLattice D.host.E Λ := by
  exact Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ hΛ

theorem eq_smul_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∃ c : ℂ, f = c • f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ hb f hf hlat hfock
  have hne : f₀ ≠ 0 := GlobalTheory.PlaceTensor.base_ne_zero hb
  obtain ⟨hS, hT, dS, dT, hψ, hθ, ht₀, hl₀, hF₀, -⟩ := hb
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  obtain ⟨ρ, hρc, hρ1, hρ2⟩ := GlobalTheory.FockCompare.exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.RealChart.exists_chart D θ hθ ρ hρc hρ1 hρ2
  obtain ⟨hdual, hdec, heig⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ dS dT
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hinf : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
  have key : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u f = ε • f ∧ heisO ψ S T u f₀ = ε • f₀ := by
    intro u hu
    obtain ⟨ε, hε, h⟩ := heig f hlat u hu
    exact ⟨ε, hε, h f hlat, h f₀ hl₀⟩
  have ext : ∀ w, ∃ z : RW T S, ∃ a : ℂ, f w = a * f (iotaW σ T S z) ∧ f₀ w = a * f₀ (iotaW σ T S z) := by
    intro w
    obtain ⟨γ, z, u, hu, rfl⟩ := GlobalTheory.VacUnique.exists_decomp hσ hdec w
    obtain ⟨ε, -, h1, h2⟩ := key u hu
    refine ⟨z, ψ (-symplOH S T (ratW T S γ) (iotaW σ T S z + u)) * ε, ?_, ?_⟩
    · rw [hf.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h1 z]; ring
    · rw [ht₀.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h2 z]; ring
  have hN : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ :=
    GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT
      (selfDual_isFullLattice dS) (selfDual_isFullLattice dT)
  have hLd := GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf hdual hdec hN
  obtain ⟨hJ, hanti, hinv, hpos⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  classical
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv).choose else 1
  have hc : ∀ v, ‖c v‖ = 1 := by
    intro v
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψn, one_mul]
      rcases (key _ hv).choose_spec.1 with h | h <;> rw [h] <;> simp
    · simp
  have hfd := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ hσ ψ hψ S T sS sT f hf hfock
  have hfd₀ := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ hσ ψ hψ S T sS sT f₀ ht₀ hF₀
  have hspan : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := GlobalTheory.FockCompare.span_piW_ratW_eq_top D θ σ hσ T S
    simpa [GlobalTheory.VacUnique.piW_ratW hθ] using this
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) hJ hanti hinv hpos
    (Matrix (Fin T.rank) (Fin S.rank) D.host.E) (infRat S T) (GlobalTheory.VacUnique.infRat_injective S T) hspan
    (Λ.comap (finRat S T)) (fun x => by simpa using hN x) (fun x => by simpa using hLd x) c hc
    ![fun z => f₀ (iotaW σ T S z), fun z => f (iotaW σ T S z)]
    (Fin.forall_fin_two.2 ⟨hfd₀.1, hfd.1⟩) ?fock ?quasi
  case fock => exact Fin.forall_fin_two.2 ⟨hfd₀.2, hfd.2⟩
  case quasi =>
    intro k v hv z
    have hv' : finRat S T (-v) ∈ Λ := by
      rw [map_neg]
      exact Λ.neg_mem (AddSubgroup.mem_comap.1 hv)
    have hcv : c v = ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv').choose := by
      simp only [c, dif_pos hv']
    obtain ⟨-, h1, h2⟩ := (key _ hv').choose_spec
    have e1 := GlobalTheory.VacUnique.apply_add_infRat hσ hψ hf v h1 z
    have e2 := GlobalTheory.VacUnique.apply_add_infRat hσ hψ ht₀ v h2 z
    have ho : (omO S T z (infRat S T v) : ℂ) = ((-omO S T (infRat S T v) z : ℝ) : ℂ) := by rw [hanti]
    rw [hcv, ho]
    fin_cases k
    · exact e2
    · exact e1
  rw [LinearIndependent.pair_iff] at hli
  push_neg at hli
  obtain ⟨s, t, hst, hne0⟩ := hli
  have hpt : ∀ z, s * f₀ (iotaW σ T S z) + t * f (iotaW σ T S z) = 0 := fun z => by
    have := congrFun hst z
    simpa using this
  by_cases ht : t = 0
  · exfalso
    have hs : s ≠ 0 := fun hs => hne0 hs ht
    apply hne
    funext w
    obtain ⟨z, a, -, h2⟩ := ext w
    have := hpt z
    rw [ht, zero_mul, add_zero] at this
    rw [h2, (mul_eq_zero.1 this).resolve_left hs]
    simp
  · refine ⟨-s / t, ?_⟩
    funext w
    obtain ⟨z, a, h1, h2⟩ := ext w
    have := hpt z
    rw [Pi.smul_apply, smul_eq_mul, h1, h2, div_mul_eq_mul_div, eq_div_iff ht]
    linear_combination a * this

end GlobalTheory.VacuumLine

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Ker (ipO)
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.ThetaSquare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem cocompact (V W : HSp D) : Cocompact V W := by
  obtain ⟨-, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have h := hK.image (QuotientAddGroup.continuous_mk (N := (ratL W V : AddSubgroup (WO V W))))
  refine ⟨(Set.eq_univ_of_forall fun q => ?_ : _ = Set.univ) ▸ h⟩
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨γ, hγ, hk⟩ := hc w
  exact ⟨_, hk, QuotientAddGroup.eq.2 (by simpa using hγ)⟩

theorem symplOH_zero_right (w : WO V W) : symplOH V W w 0 = 0 := by
  have := symplOH_add_right w 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOH_zero_left (w : WO V W) : symplOH V W 0 w = 0 := by
  have := symplOH_add_left 0 0 w
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOH_neg_self (u : WO V W) : symplOH V W (-u) u = 0 := by
  have := symplOH_add_left (-u) u u
  rwa [neg_add_cancel, symplOH_zero_left, symplOH_self, add_zero, eq_comm] at this

theorem squareIntegrable (hψ : IsStdChar D ψ (-1)) : SquareIntegrable ψ V W :=
  fun _ h => ⟨theta_norm_periodic hψ h, theta_bounded hψ h, fun _ _ hμ h𝓕 => GlobalTheory.Size.memLp_theta hψ hμ h𝓕 h⟩

theorem heisUnitary (hψ : IsStdChar D ψ (-1)) : HeisUnitary ψ V W := by
  refine ⟨heisO_heisO, fun u f => ?_, fun u f h => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ h u,
    fun _ _ hμ h𝓕 u _ _ h h' => GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 h h' u, ?_⟩
  · rw [heisO_heisO, symplOH_neg_self, ψ.map_zero_eq_one, one_smul, neg_add_cancel, heisO_zero]
  · rintro _ ⟨γ, rfl⟩ f h
    have e := h.quasi γ 0
    rw [symplOH_zero_right, neg_zero, ψ.map_zero_eq_one, one_mul, add_zero] at e
    change ψ (symplOH V W 0 (ratW W V γ)) * f (0 + ratW W V γ) = f 0
    rw [symplOH_zero_left, ψ.map_zero_eq_one, one_mul, zero_add, e]

theorem norm_heisO (hψ : IsStdChar D ψ (-1)) (u : WO V W) (f : WO V W → ℂ) (x : WO V W) :
    ‖heisO ψ V W u f x‖ = ‖f (x + u)‖ := by
  rw [heisO, norm_mul, hψ.1.2.1, one_mul]

theorem ipO_dLine (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO V W} (hL : IsRealDir W V L)
    {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {f f' : WO V W → ℂ} (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    ipO μ 𝓕 (dLine ψ V W L f) f' = -ipO μ 𝓕 f (dLine ψ V W L f') := by
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμ h𝓕).2
  have hd := theta_dLine hθ hψ hL h
  have hd' := theta_dLine hθ hψ hL h'
  have hI := fun {g g'} => GlobalTheory.Size.integrableOn_mul_conj (f := g) (f' := g') hψ hμ h𝓕
  have hT := fun {g} (hg : IsThetaFunO ψ V W g) t => theta_heisO_real hθ hψ (hL.2 t) hg
  obtain ⟨a, ha⟩ := theta_bounded hψ h
  obtain ⟨b, hb⟩ := theta_bounded hψ h'
  obtain ⟨c, hc⟩ := theta_bounded hψ hd
  obtain ⟨d, hd0⟩ := theta_bounded hψ hd'
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ => c * b + a * d)
    (F := fun t x => heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) f' x))
    (F' := fun t x => heisO ψ V W (L t) (dLine ψ V W L f) x * conj (heisO ψ V W (L t) f' x) +
      heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) (dLine ψ V W L f') x))
    Filter.univ_mem
    (.of_forall fun t => (hI (hT h t) (hT h' t)).aestronglyMeasurable)
    (hI (hT h 0) (hT h' 0))
    ((hI (hT hd 0) (hT h' 0)).add (hI (hT h 0) (hT hd' 0))).aestronglyMeasurable
    (.of_forall fun x t _ => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
        rw [norm_mul, Complex.norm_conj, norm_heisO hψ, norm_heisO hψ]
      · exact mul_le_mul (hc _) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (hc 0))
      · exact mul_le_mul (ha _) (hd0 _) (norm_nonneg _) ((norm_nonneg _).trans (ha 0)))
    (integrable_const _)
    (.of_forall fun x t _ =>
      (hasDerivAt_heisO hθ hψ hL h x t).mul (hasDerivAt_heisO hθ hψ hL h' x t).star)).2
  have e : (fun t => ∫ x in 𝓕, heisO ψ V W (L t) f x * conj (heisO ψ V W (L t) f' x) ∂μ) = fun _ => ipO μ 𝓕 f f' :=
    funext fun t => GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 h h' (L t)
  rw [e] at key
  have k := key.unique (hasDerivAt_const _ _)
  simp only [map_zero, heisO_zero] at k
  rw [integral_add (hI hd h') (hI h hd')] at k
  exact eq_neg_of_add_eq_zero_left k

theorem derSkew (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) : DerSkew ψ θ V W := by
  intro τ z
  have hL := isRealDir_lineAt (S := V) (T := W) hθ τ z
  refine ⟨fun f h x => ?_, fun f h => theta_dRho hθ hψ τ z h, fun μ 𝓕 hμ h𝓕 f f' h h' => ipO_dLine hψ hθ hL hμ h𝓕 h h'⟩
  exact (hasDerivAt_heisO hθ hψ hL h x 0).differentiableAt.hasDerivAt

theorem commScalar_eq (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    commScalar V W τ τ' z w = -(2 * Real.pi * Complex.I) * (GlobalTheory.FockIndep.omDir V W τ z τ' w : ℝ) := by
  unfold commScalar GlobalTheory.FockIndep.omDir
  split_ifs
  · rfl
  · simp

theorem symplO_eq (x y : WO V W) : symplO V W x y = symplOH V W x y + symplOH V W x y := by
  rw [symplOH, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem derComm (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) : DerComm ψ θ V W := by
  intro τ τ' z w
  rw [commScalar_eq]
  refine ⟨fun s t => ?_, fun f h => sub_eq_of_eq_add (GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ' w h)⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (smooth_iff_sm_and_real_lines D θ σ h W V).2.1
  rw [symplO_eq, AddChar.map_add_eq_mul, e _ (isRealDir_lineAt hθ τ z) s, e _ (isRealDir_lineAt hθ τ' w) t,
    psi_symplOH h hψ, h.pi_iota, LinearMap.map_smul₂, map_smul, GlobalTheory.FockIndep.piW_lineAt hθ,
    GlobalTheory.FockIndep.piW_lineAt hθ, GlobalTheory.FockIndep.omO_single, ← Complex.exp_add]
  congr 1
  simp only [smul_eq_mul]
  push_cast
  ring

theorem finRealComm (hθ : IsInfFam θ) : FinRealComm ψ θ V W := by
  refine fun u hu => ⟨fun v hv f => ?_, fun τ z f _ => (GlobalTheory.FinTranslate.dRho_heisO hθ hu τ z f).symm⟩
  rw [heisO_heisO, heisO_heisO, (symplOH_fin_real hu hv).1, (symplOH_fin_real hu hv).2, add_comm]

theorem theta_square_integrable (D : D7) : ThetaSquareIntegrable D :=
  fun V W => ⟨cocompact V W, fun _ hψ => ⟨squareIntegrable hψ, heisUnitary hψ,
    fun _ hθ => ⟨derSkew hψ hθ, derComm hψ hθ, finRealComm hθ⟩⟩⟩

end GlobalTheory.ThetaSquare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.KFiniteDetermined

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_kFin_of_mem_lowT {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {v : M.sm τ} (hv : v ∈ lowT M τ) : (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ :=
  (sSup_le (a := GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) fun A hA _ hw => ⟨A, hA.1, hw, hA.2.1⟩) hv

theorem restrInj : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.RestrInj D :=
  fun D θ hθ V S M J χ T hT h0 =>
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D V S M θ hθ (GlobalTheory.LowTypeRestriction.lowT_ne_bot M) J χ T hT
      fun v => h0 _ fun τ => mem_kFin_of_mem_lowT M τ (v τ).2

end GlobalTheory.KFiniteDetermined
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : ι → Type} (T : ∀ i, (X i → ℂ) →ₗ[ℂ] (Y i → ℂ)) {δ : Type}

theorem sum_prod_partial_eq_zero (s : Finset δ) (a : δ → ℂ) (F : δ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s, a d * ∏ i, F d i (x i) = 0) (A : Finset ι) (x : ∀ i, X i) (y : ∀ i, Y i) :
    ∑ d ∈ s, a d * ((∏ i ∈ A, T i (F d i) (y i)) * ∏ i ∈ Aᶜ, F d i (x i)) = 0 := by
  induction A using Finset.induction_on generalizing x with
  | empty => simpa using h x
  | @insert b A hb ih =>
    set c : δ → ℂ := fun d => a d * ((∏ i ∈ A, T i (F d i) (y i)) * ∏ i ∈ (insert b A)ᶜ, F d i (x i)) with hc
    have hbA : b ∈ Aᶜ := Finset.mem_compl.2 hb
    have hcompl : (insert b A)ᶜ = (Aᶜ).erase b := by
      ext i; simp [Finset.mem_erase, and_comm]
    have hφ : (∑ d ∈ s, c d • F d b) = 0 := by
      funext z
      have := ih (Function.update x b z)
      rw [Finset.sum_apply, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hc, ← Finset.mul_prod_erase _ _ hbA, Function.update_self, hcompl]
      have : ∏ i ∈ (Aᶜ).erase b, F d i (Function.update x b z i) = ∏ i ∈ (Aᶜ).erase b, F d i (x i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [this]; ring
    have h2 := congrArg (fun f => T b f (y b)) hφ

    simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.prod_insert hb, hc]; ring

theorem sum_prod_map_eq_zero (s : Finset δ) (a : δ → ℂ) (F : δ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s, a d * ∏ i, F d i (x i) = 0) (y : ∀ i, Y i) :
    ∑ d ∈ s, a d * ∏ i, T i (F d i) (y i) = 0 := by
  by_cases hX : Nonempty (∀ i, X i)
  · obtain ⟨x⟩ := hX
    simpa using sum_prod_partial_eq_zero T s a F h Finset.univ x y
  · have hi : ∃ i, IsEmpty (X i) := by
      by_contra hn
      push_neg at hn
      exact hX ⟨fun i => Classical.choice (hn i)⟩
    obtain ⟨i, hi⟩ := hi
    have h0 : ∀ f : X i → ℂ, f = 0 := fun f => funext fun z => hi.elim z
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0 (F d i), map_zero]; rfl), mul_zero]

theorem sum_prod_map_congr {δ' : Type} (s : Finset δ) (s' : Finset δ') (a : δ → ℂ) (a' : δ' → ℂ) (F : δ → ∀ i, X i → ℂ)
    (F' : δ' → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ s', a' d * ∏ i, F' d i (x i) = ∑ d ∈ s, a d * ∏ i, F d i (x i)) (y : ∀ i, Y i) :
    ∑ d ∈ s', a' d * ∏ i, T i (F' d i) (y i) = ∑ d ∈ s, a d * ∏ i, T i (F d i) (y i) := by
  have key := sum_prod_map_eq_zero T (s'.disjSum s) (Sum.elim a' fun d => -a d) (Sum.elim F' F) (fun x => by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, h x, add_neg_cancel]) y
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
  exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact key)

end Tensor

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def stdLatO (S : GridChoice W U) (p : Pair T) : AddSubgroup (WO (G.pS p) (G.pT p)) :=
  latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E))
    fun _ => True

def movedFn (_S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) → ℂ :=
  Function.update (Function.update (fun j' => (d.1 j').fn) ⟨j, by omega⟩
      fun x => (d.1 ⟨j, by omega⟩).fn (actO _ _ 1⁻¹ (g : GA D (G.V (.top (j + 1))))⁻¹ x))
    ⟨j + 1, hj⟩ fun x => (d.1 ⟨j + 1, hj⟩).fn (actO _ _ (g : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x)

theorem vec_eq_model (S : GridChoice W U) {t : T} {p : Pair T} (d : FinDatum G t p) (hz : d.z = 1) (hv : S.Z.HasVec d)
    (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hTm : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) d.e (stdLatO S p) 1 (S.Z.vac p) Tm) : S.Z.vec d = Tm d.fn := by
  obtain ⟨f, hf⟩ := hv
  rw [Normal.vec, FinDatum.vec_eq W hf, hz, ← hf.2 Tm hTm]
  rw [show ((1 : GA D (G.pS p)), (1 : GA D (G.pT p))) = 1 from rfl, map_one]
  rfl

end GlobalTheory.ExpansionInvariance

end
end

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

theorem _root_.GlobalTheory.T.unitary_irreducible_smooth_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NonarchimedeanGroup G] [LocallyCompactSpace G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : G →* (H →L[ℂ] H)), IsIrrUnitary π → (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional ℂ (fixed (toRep π) K)) → (smRep π).IsIrreducible ∧ IsAdmissible (smRep π) := by
  first | exact @GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep | exact GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep | (intros; apply GlobalTheory.SmoothUnitary.isIrreducible_isAdmissible_smRep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdRealLift

theorem exists_real_point : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (v : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, (v τ)ᴴ * v τ = 1) → ∃ h ∈ GinfC S, ∀ τ, compAt C.θ τ (mt S h) = v τ := by
  intro D S T C v hv
  obtain ⟨L, hL, -⟩ := GlobalTheory.RealLift.exists_real_lift D C.θ S C.inf
  have hu : v ∈ HolDict.UG (gramAt D S) := by
    intro τ
    have hg : gramAt D S τ = 1 := by
      unfold gramAt
      rw [C.m.gS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    show (v τ)ᴴ * gramAt D S τ * v τ = gramAt D S τ
    rw [hg, Matrix.mul_one]
    exact hv τ
  refine ⟨L v, (hL v hu).1, fun τ => ?_⟩
  rw [← (hL v hu).2 τ]
  clear hL hu hv
  unfold compAt archM
  ext i j
  rfl

end GlobalTheory.StdRealLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_coefficientSpace_dual_discreteSeriesModel_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∃ (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), c.Is ∧ IsDualPair θ M c pr ∧ Function.Surjective pr := by
  first | exact @GlobalTheory.DualCoef.exists_dual_coef | exact GlobalTheory.DualCoef.exists_dual_coef | (intros; apply GlobalTheory.DualCoef.exists_dual_coef <;> assumption)
end
