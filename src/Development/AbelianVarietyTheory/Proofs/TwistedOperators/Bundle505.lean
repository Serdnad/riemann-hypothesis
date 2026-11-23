module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle815
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle382
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle145
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
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

namespace GlobalTheory.SepPer.KFinPer

open Formalism.MainNotions.S
open scoped Classical

variable {D : D7}

theorem isMultMap_bound (hP : GlobalTheory.Published.CuspRapidDecay) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have hPu := M.fr_unit τ
  have hG := M.fr_gram τ
  choose ℓ hℓ hℓT using fun g : GA D V => hT.cont τ v g
  have hsm : ∀ u : M.H τ, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) u → u ∈ M.sm τ := fun u hu =>
    Submodule.subset_span ((GlobalTheory.SmoothCyclic.smoothVec_transport hPu hG u).2 hu)
  obtain ⟨L, C, hL, hC⟩ := GlobalTheory.SobUnif.unif_model hσ ℓ
    (fun g => GlobalTheory.SmoothCyclic.sobCont_transport hPu hG (hℓ g))
    (fun u hu => by
      obtain ⟨B, hB⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut (Function.update v τ ⟨u, hsm u hu⟩))
        (hT.cusp (Function.update v τ ⟨u, hsm u hu⟩))
      exact ⟨B, fun g => by rw [hℓT g ⟨u, hsm u hu⟩]; exact hB g⟩)
  refine ⟨L.map fun l => l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ, C, ?_, fun w g => ?_⟩
  · intro l hl Y hY
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
    exact GlobalTheory.SmoothCyclic.conj_lie (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hPu)) hG
      (hL l0 hl0 X hX)
  · have hw := (GlobalTheory.SmoothCyclic.smoothVec_transport hPu hG (w : M.H τ)).1
      (GlobalTheory.HolRead.MultDer.smoothVec_of_mem M τ w.2)
    have h1 := hC g (w : M.H τ) hw
    rw [hℓT g w] at h1
    refine h1.trans_eq ?_
    congr 1
    rw [GlobalTheory.SmoothGlob.sobNorm, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun l _ => ?_)
    exact congrArg norm (GlobalTheory.SobUnif.foldr_conj_eq (M.σ τ) hPu l (w : M.H τ)).symm

theorem mult_bound (hP : GlobalTheory.Published.CuspRapidDecay) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {T : MMap M}
    (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact isMultMap_bound hP θ hθ M J χ T hT τ v
  | zero => exact ⟨[], 0, by simp, fun w g => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    obtain ⟨L₁, C₁, hL₁, hb₁⟩ := h₁
    obtain ⟨L₂, C₂, hL₂, hb₂⟩ := h₂
    refine ⟨L₁ ++ L₂, max C₁ 0 + max C₂ 0, fun l hl => ?_, fun w g => ?_⟩
    · rcases List.mem_append.1 hl with h | h
      exacts [hL₁ l h, hL₂ l h]
    · set s₁ := (L₁.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      set s₂ := (L₂.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      have hs₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      have hs₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [List.map_append, List.sum_append, MultilinearMap.add_apply, Pi.add_apply]
      calc _ ≤ ‖T₁ (Function.update v τ w) g‖ + ‖T₂ (Function.update v τ w) g‖ := norm_add_le _ _
        _ ≤ C₁ * s₁ + C₂ * s₂ := add_le_add (hb₁ w g) (hb₂ w g)
        _ ≤ max C₁ 0 * s₁ + max C₂ 0 * s₂ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₁)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₂)
        _ ≤ (max C₁ 0 + max C₂ 0) * (s₁ + s₂) := by
          have := le_max_right C₁ 0; have := le_max_right C₂ 0; nlinarith
  | smul c T _ h =>
    obtain ⟨L, C, hL, hb⟩ := h
    refine ⟨L, ‖c‖ * C, hL, fun w g => ?_⟩
    rw [MultilinearMap.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb w g) (norm_nonneg _)

theorem per_eq_zero_of_kF : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ y ∈ MultT θ M J χ, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (e : X → GA D V) (u : X → ℂ), Measurable e → Integrable u ν → (∀ a ∈ KF M, ∫ x, y a (e x) * u x ∂ν = 0) → ∀ a, ∫ x, y a (e x) * u x ∂ν = 0 := by
  intro hP hHC D θ hθ V S M J χ y hy X _ ν e u he hu h0 a
  have : BorelSpace (GA D V) := ⟨rfl⟩
  set T' : MMap M := PiTensorProduct.lift.symm y with hT'
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ y).1 hy
  have hTt : ∀ w : M.Vec, y (PiTensorProduct.tprod ℂ w) = T' w := by
    intro w
    have : y = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply y).symm
    rw [this, PiTensorProduct.lift.tprod]
  have hval : ∀ b, Continuous (y b) ∧ ∃ B : ℝ, ∀ g, ‖y b g‖ ≤ B := by
    intro b
    obtain ⟨h1, h2, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J χ y hy b
    exact ⟨h1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ h1 h2⟩
  have hint : ∀ b, Integrable (fun x => y b (e x) * u x) ν := by
    intro b
    obtain ⟨hc, B, hB⟩ := hval b
    have hm : AEStronglyMeasurable (fun x => y b (e x)) ν :=
      (hc.measurable.comp he).aestronglyMeasurable
    first
      | exact hu.bdd_mul hm ⟨B, fun x => hB (e x)⟩
      | exact hu.bdd_mul hm (Filter.Eventually.of_forall fun x => hB (e x))
  let Λ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun b => ∫ x, y b (e x) * u x ∂ν
      map_add' := fun b c => by
        simp only [map_add (f := _), Pi.add_apply, add_mul]
        exact integral_add (hint b) (hint c)
      map_smul' := fun c b => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hsep : GlobalTheory.Core.Mi.SepCont M Λ := by
    intro τ v
    obtain ⟨L, Cu, hL, hb⟩ := mult_bound hP θ hθ M J χ hT'm τ v
    let ℓ₀ : M.sm τ →ₗ[ℂ] ℂ := (Λ.compMultilinearMap (PiTensorProduct.tprod ℂ)).toLinearMap v τ
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hℓw : ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w)) := by
      intro w
      have := congrArg (fun m => m w) hℓ
      simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ⟨L, Cu * ∫ x, ‖u x‖ ∂ν, hL, fun w hw => ?_⟩, hℓw⟩
    have hw' : w ∈ M.sm τ := Submodule.subset_span hw
    rw [hℓw ⟨w, hw'⟩]
    change ‖∫ x, y (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩)) (e x) * u x ∂ν‖ ≤ _
    rw [hTt]
    set s := (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum
    have hpt : ∀ x, ‖T' (Function.update v τ ⟨w, hw'⟩) (e x) * u x‖ ≤ Cu * s * ‖u x‖ := by
      intro x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb ⟨w, hw'⟩ (e x)) (norm_nonneg _)
    calc _ ≤ ∫ x, Cu * s * ‖u x‖ ∂ν :=
          norm_integral_le_of_norm_le (hu.norm.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = Cu * s * ∫ x, ‖u x‖ ∂ν := integral_const_mul _ _
      _ = _ := by ring
  have hΛ : Λ = 0 := GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D V S M Λ hsep fun v hv =>
    h0 _ (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  exact congrArg (fun L : SmT M →ₗ[ℂ] ℂ => L a) hΛ

end GlobalTheory.SepPer.KFinPer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.TypeExpand

theorem typeAt_expand : ∀ (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) {D : D7} (θ : InfFam D) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {m : ℕ} (k : Fin m → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : ∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (B : Fin m → (M.H τ →ₗ[ℂ] M.H τ))
    (hB : ∀ A : M.H τ →ₗ[ℂ] M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) *
          LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
    {φ : GA D V → ℂ} (hφ : IsTypeAt θ V τ (S τ) φ) (x : GA D V) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), φ (x * atTau θ V τ g) = ∑ j, φ (x * atTau θ V τ (k j)) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j) := by
  intro hU D θ V S M τ _ m k hk B hB φ hφ x g hg
  obtain ⟨H', _, _, σ, lam, ε, P, hen, hds, hPu, hPg, hx⟩ := hφ
  obtain ⟨v, -, ℓ, -, -, hsum⟩ := hx x
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) hen
  subst hl he
  obtain ⟨U, hU'⟩ := hU _ (M.ε τ) (M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) P
    (M.fr_unit τ) hPu (M.fr_gram τ) hPg _ _ (M.σ τ) σ (M.ds τ) hds

  set A : ℕ → (M.H τ →ₗ[ℂ] M.H τ) := fun i =>
    ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (U (v i)) with hA
  have key : ∀ i, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      ℓ i (σ (P * h * P⁻¹) (v i)) =
        LinearMap.trace ℂ (M.H τ) ((M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) := by
    intro i h hh
    have e1 : (M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i =
        ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (M.rep τ h (U (v i))) := by
      ext w
      simp [hA]
    rw [e1, LinearMap.trace_smulRight]
    have e2 : M.rep τ h (U (v i)) = U (σ (P * h * P⁻¹) (v i)) := (hU' h hh (v i)).symm
    rw [e2]
    simp
  have h1 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
      (∑ j, φ (x * atTau θ V τ (k j)) *
        LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) := by
    refine hasSum_sum fun j _ => ?_
    refine HasSum.mul_right _ ?_
    have := hsum (k j) (hk j)
    refine this.congr_fun ?_
    intro i
    exact (key i (k j) (hk j)).symm
  have h2 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) (φ (x * atTau θ V τ g)) := by
    refine (hsum g hg).congr_fun ?_
    intro i
    rw [key i g hg, hB (A i) g hg]
  exact h2.unique h1

end GlobalTheory.TypeExpand

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.ProdLength

section General
variable {F G U V X : Type} [Field F] [Group G] [AddCommGroup U] [Module F U] [AddCommGroup V]
  [Module F V] [AddCommGroup X] [Module F X]

def comapSub {α : Representation F G U} {β : Representation F G V} (ι : α.IntertwiningMap β)
    (S : Subrepresentation β) : Subrepresentation α :=
  ⟨S.toSubmodule.comap ι.toLinearMap, fun g v hv => by
    show ι (α g v) ∈ S.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact S.apply_mem_toSubmodule g hv⟩

def mapSub {β : Representation F G V} {γ : Representation F G X} (p : β.IntertwiningMap γ)
    (S : Subrepresentation β) : Subrepresentation γ :=
  ⟨S.toSubmodule.map p.toLinearMap, by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨β g v, S.apply_mem_toSubmodule g hv, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _ p g v⟩

theorem hasFiniteLength_of_exact {α : Representation F G U} {β : Representation F G V}
    {γ : Representation F G X} (ι : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) (hα : HasFiniteLength α) (hγ : HasFiniteLength γ) :
    HasFiniteLength β := by
  obtain ⟨hα1, hα2⟩ := (hasFiniteLength_iff_wellFounded α).1 hα
  obtain ⟨hγ1, hγ2⟩ := (hasFiniteLength_iff_wellFounded γ).1 hγ
  let f : Subrepresentation β → Subrepresentation α × Subrepresentation γ :=
    fun S => (comapSub ι S, mapSub p S)
  have hmono : Monotone f := fun S T h =>
    ⟨fun v hv => h hv, Submodule.map_mono (f := p.toLinearMap) h⟩
  have hf : StrictMono f := by
    intro S T hST
    refine lt_of_le_of_ne (hmono hST.le) fun heq => hST.not_ge ?_
    have h1 : (comapSub ι S).toSubmodule = (comapSub ι T).toSubmodule := congrArg (fun x => x.1.toSubmodule) heq
    have h2 : (mapSub p S).toSubmodule = (mapSub p T).toSubmodule := congrArg (fun x => x.2.toSubmodule) heq
    intro x hx
    have hpx : p x ∈ (mapSub p T).toSubmodule := ⟨x, hx, rfl⟩
    rw [← h2] at hpx
    obtain ⟨y, hy, hyx⟩ := hpx
    have hyx' : p y = p x := hyx
    obtain ⟨u, hu⟩ := hex (x - y) (by rw [map_sub, hyx', sub_self])
    have huT : u ∈ (comapSub ι T).toSubmodule := by
      show ι u ∈ T.toSubmodule
      rw [hu]
      exact T.toSubmodule.sub_mem hx (hST.le hy)
    rw [← h1] at huT
    have huS : ι u ∈ S.toSubmodule := huT
    rw [hu] at huS
    have := S.toSubmodule.add_mem huS hy
    rwa [sub_add_cancel] at this
  exact (hasFiniteLength_iff_wellFounded β).2 ⟨hf.wellFoundedGT, hf.wellFoundedLT⟩

theorem hasFiniteLength_of_injective {α : Representation F G U} {β : Representation F G V}
    (ι : α.IntertwiningMap β) (hι : Function.Injective ι) (hβ : HasFiniteLength β) :
    HasFiniteLength α := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded β).1 hβ
  have hmono : Monotone (mapSub ι) := fun S T h => Submodule.map_mono (f := ι.toLinearMap) h
  have hf : StrictMono (mapSub ι) := by
    intro S T hST
    refine lt_of_le_of_ne (hmono hST.le) fun heq => hST.not_ge ?_
    have h3 : (mapSub ι S).toSubmodule = (mapSub ι T).toSubmodule := congrArg (·.toSubmodule) heq
    intro x hx
    have hx' : ι x ∈ (mapSub ι T).toSubmodule := ⟨x, hx, rfl⟩
    rw [← h3] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [← hι hyx]
  exact (hasFiniteLength_iff_wellFounded α).2 ⟨hf.wellFoundedGT, hf.wellFoundedLT⟩

theorem hasFiniteLength_of_subsingleton [Subsingleton V] (β : Representation F G V) :
    HasFiniteLength β := by
  haveI : Subsingleton (Subrepresentation β) := ⟨fun S T => by
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => T.toSubmodule.zero_mem, fun _ => S.toSubmodule.zero_mem⟩⟩
  exact (hasFiniteLength_iff_wellFounded β).2 ⟨Finite.to_wellFoundedGT, Finite.to_wellFoundedLT⟩

end General

section Tensor
open GlobalTheory.ParIndExact
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasFiniteLength_extTensor_left (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hA : HasFiniteLength A)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y), σ.IsIrreducible →
      IsSubquotient σ A → HasFiniteLength (extTensor σ B)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded A).1 hA
  have key : ∀ S T : Subrepresentation A, T ≤ S → HasFiniteLength (extTensor (subQuot S T) B) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_left (F := ℂ)
        (V := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule) (W := W)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := A) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_left B ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot A
  obtain ⟨ι', hι'⟩ := extTensor_injective_left B ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

theorem hasFiniteLength_extTensor_right (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hB : HasFiniteLength B)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H Y), τ.IsIrreducible →
      IsSubquotient τ B → HasFiniteLength (extTensor A τ)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded B).1 hB
  have key : ∀ S T : Subrepresentation B, T ≤ S → HasFiniteLength (extTensor A (subQuot S T)) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_right (F := ℂ) (V := V)
        (W := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := B) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_right A ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot B
  obtain ⟨ι', hι'⟩ := extTensor_injective_right A ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

end Tensor
end GlobalTheory.ProdLength

theorem GlobalTheory.ProdLength.prod₂_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), HasFiniteLength π₁ → HasFiniteLength π₂ → IsSmooth π₁ → IsSmooth π₂ → HasFiniteLength (prod₂ π₁ π₂) := by
  intro hBZ k _ _ _ _ r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂
  obtain ⟨hAdm, -, hInd, -⟩ := hBZ k
  have schur : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ (GL (Fin n) k) Y),
      IsSmooth σ → σ.IsIrreducible → ∀ φ : Y →ₗ[ℂ] Y, (∀ g x, φ (σ g x) = σ g (φ x)) →
        ∃ c : ℂ, φ = c • LinearMap.id := fun n Y _ _ σ hs hi =>
    GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin n)) GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO Y σ hi
      (hAdm (Fin n) Y σ hs hi)
  have hT : HasFiniteLength (extTensor π₁ π₂) :=
    GlobalTheory.ProdLength.hasFiniteLength_extTensor_left π₁ π₂ h₁ fun Y _ _ σ hσ hsq =>
      GlobalTheory.ProdLength.hasFiniteLength_extTensor_right σ π₂ h₂ fun Z _ _ τ hτ hsq' =>
        hasFiniteLength_of_isIrreducible (GlobalTheory.JacFactor.isIrreducible_extTensor σ τ hσ hτ
          (schur r Y σ (hsq.isSmooth s₁) hσ) (schur t Z τ (hsq'.isSmooth s₂) hτ))
  have hc : Continuous (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom :=
    (continuous_apply false).prodMk (continuous_apply true)
  exact hInd Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    (isSmooth_comp (isSmooth_extTensor s₁ s₂) _ hc)
    ((hasFiniteLength_comp_iff _ _ (leviTwo k (Fin r) (Fin t)).symm.surjective).2 hT)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.complexDerivative_adjoint_of_skew_form : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (A : Submodule ℂ (GA D V → ℂ)) (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ),
    (∀ X ∈ lieAt V τ, ∀ x ∈ A, ∀ y ∈ A, b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∀ (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ x ∈ A, ∀ y ∈ A,
      b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y := by
  first | exact @GlobalTheory.RderCAdjoint.rderC_adjoint | exact GlobalTheory.RderCAdjoint.rderC_adjoint | (intros; apply GlobalTheory.RderCAdjoint.rderC_adjoint <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.isCompact_unitaryRealPoints_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  first | exact @GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | exact GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | (intros; apply GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one <;> assumption)
end
