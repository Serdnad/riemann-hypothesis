module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle092
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle094
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.StdPos

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix

section Pure

variable {R : Type} [CommRing R] (s : R →+* R) {n r m : ℕ} (J : Matrix (Fin n) (Fin n) R)

end Pure

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n r m : ℕ}
  (J : Matrix (Fin n) (Fin n) E)







end Lattice

end GlobalTheory.RegSch.StdPos

namespace GlobalTheory.RegSch

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix StdPos

theorem exists_good_frameLat (D : D7) (V : HSp D) : ∃ a, Lvl.Good (⟨frameLat V, a⟩ : Lvl V) :=
  (exists_isMaj V).imp fun _ h => ⟨isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, h⟩

end GlobalTheory.RegSch

end
end

section

noncomputable section
open scoped Matrix Classical TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.Inhab
variable {D : D7}

section Generic

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) {n m k : Type}

variable [Fintype n] [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq m] [DecidableEq k]

end Generic

section Lattice

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

variable {L' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}

end Lattice

section Frame

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

variable (c : Mx D T'.rank T'.rank)

end Frame

theorem exists_good (V : HSp D) : ∃ l : Lvl V, l.Good :=
  let ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj V
  ⟨⟨frameLat V, a⟩, isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, ha⟩

end GlobalTheory.RegSch.Inhab
end
end

section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactAvgSchwartz

variable {D : D7}

theorem mt_mul_inv_self (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_inv]
  exact Units.mul_inv _

theorem map_cancel {R : Type} [CommRing R] (φ : AE D →+* R) (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).map φ * (Formalism.L2.Theta.mt V g⁻¹).map φ = 1 := by
  rw [← Matrix.map_mul, mt_mul_inv_self, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem map_mul_entry {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin m) (Fin n) R) : (fun i j => φ ((M * x) i j)) = fun i j => ∑ c, φ (M i c) * φ (x c j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul]

theorem integrable_and_projS_mem {θ : InfFam D} (hθ : IsInfFam θ) {T : HSp D} {n : ℕ} {K : Subgroup (GA D T)}
    (hK : IsCompact (K : Set (GA D T))) (ν : Measure K) [IsFiniteMeasure ν] {Φ : Mx D T.rank n → ℂ}
    (hΦ : Φ ∈ schwartzA θ T.rank n) :
    (∀ x : Mx D T.rank n, Integrable (fun k : K => Φ (Formalism.L2.Theta.mt T (k : GA D T)⁻¹ ⬝ x)) ν) ∧
      projS ν Φ ∈ schwartzA θ T.rank n := by
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨fun x => integrable_zero _ _ _, ?_⟩
    have e : projS ν (0 : Mx D T.rank n → ℂ) = 0 := funext fun x => integral_zero _ _
    rw [e]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun x => (h1.1 x).add (h2.1 x), ?_⟩
    have e : projS ν (Φ + Ψ) = projS ν Φ + projS ν Ψ := funext fun x => integral_add (h1.1 x) (h2.1 x)
    rw [e]
    exact Submodule.add_mem _ h1.2 h2.2
  | smul c Φ _ h1 =>
    refine ⟨fun x => (h1.1 x).smul c, ?_⟩
    have e : projS ν (c • Φ) = c • projS ν Φ := funext fun x => integral_smul c _
    rw [e]
    exact Submodule.smul_mem _ c h1.2
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    haveI : OpensMeasurableSpace K := inferInstance
    have c1 : Continuous fun k : K => Formalism.L2.Theta.mt T (k : GA D T) :=
      (GlobalTheory.RealWeil.continuous_mt T).1.comp continuous_subtype_val
    have c2 : Continuous fun k : K => Formalism.L2.Theta.mt T (k : GA D T)⁻¹ :=
      (GlobalTheory.RealWeil.continuous_mt T).2.comp continuous_subtype_val
    obtain ⟨hint, t, F, ht, hF⟩ := integral_tensor_matrix (n := n) ν
      (fun (k : K) τ => compAt θ τ (Formalism.L2.Theta.mt T (k : GA D T)⁻¹))
      (fun (k : K) τ => compAt θ τ (Formalism.L2.Theta.mt T (k : GA D T)))
      (fun τ => (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp c2)
      (fun τ => (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp c1)
      (fun k τ => map_cancel ((θ τ).comp (infPart D)) T k)
      (fun k : K => (Formalism.L2.Theta.mt T (k : GA D T)⁻¹).map (finPart D))
      (fun k : K => (Formalism.L2.Theta.mt T (k : GA D T)).map (finPart D))
      (c2.matrix_map (GlobalTheory.Member.continuous_finPart D)) (c1.matrix_map (GlobalTheory.Member.continuous_finPart D))
      (fun k => map_cancel (finPart D) T k) f hg
    have e : ∀ (M : Mx D T.rank T.rank) (x : Mx D T.rank n),
        f (fun τ i j => compAt θ τ (M ⬝ x) i j) * g (fun i j => finPart D ((M ⬝ x) i j)) =
        f (fun τ i j => ∑ c, compAt θ τ M i c * compAt θ τ x c j) *
          g (fun i j => ∑ c, M.map (finPart D) i c * finPart D (x c j)) := fun M x => by
      have e1 := fun τ => map_mul_entry ((θ τ).comp (infPart D)) M x
      have e2 := map_mul_entry (finPart D) M x
      exact congrArg₂ (· * ·) (congrArg f (funext e1)) (congrArg g e2)
    refine ⟨fun x => ?_, ?_⟩
    · simp only [e]
      exact hint (fun τ i j => compAt θ τ x i j) (fun i j => finPart D (x i j))
    · have e2 : projS ν (fun x : Mx D T.rank n => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) =
          ∑ g' ∈ t, fun x : Mx D T.rank n => F g' (fun τ i j => compAt θ τ x i j) * g' (fun i j => finPart D (x i j)) := by
        funext x
        rw [Finset.sum_apply]
        simp only [projS, e]
        exact hF (fun τ i j => compAt θ τ x i j) (fun i j => finPart D (x i j))
      rw [e2]
      exact Submodule.sum_mem _ fun g' hg' => Submodule.subset_span ⟨F g', g', ht g' hg', rfl⟩

theorem projS_mem : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T : HSp D) (n : ℕ) (K : Subgroup (GA D T)),
    IsCompact (K : Set (GA D T)) → ∀ ν : Measure K, IsProbabilityMeasure ν → ∀ Φ ∈ schwartzA θ T.rank n,
      projS ν Φ ∈ schwartzA θ T.rank n :=
  fun _ _ hθ _ _ _ hK ν _ _ hΦ => (integrable_and_projS_mem hθ hK ν hΦ).2

end GlobalTheory.CompactAvgSchwartz

end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOne

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma isHaarMeasure_framePositiveSum_rescale (ν : Measure k)
    [ν.IsAddHaarMeasure] (b : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) [hm : m.IsHaarMeasure] :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b m).IsHaarMeasure := by
  haveI : BorelSpace (GL n k) := (_root_.GlobalTheory.SplitWeil.volGL_haar k n ν).1
  have hpos := ENNReal.toReal_pos_iff.mp (_root_.GlobalTheory.StepData.volN_stabLat ν b)
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale
  exact @Measure.IsHaarMeasure.smul _ _ _ _ m hm _ _ (ENNReal.inv_ne_zero.mpr hpos.2.ne)
    (ENNReal.inv_ne_top.mpr hpos.1.ne')

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma posOne_toOne_zero (ν : Measure k)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ) :
    _root_.GlobalTheory.PosOne.toOne ν σ P (fun _ => 0) = fun _ => 0 := by
  have hdown : ∀ p, _root_.GlobalTheory.RootEx.exDown ν p σ (fun _ => (0 : ℂ)) = fun _ => 0 := by
    intro p
    funext v
    simp [_root_.GlobalTheory.RootEx.exDown]
  have key : ∀ m : ℕ, _root_.GlobalTheory.PosOne.toOne ν σ (m + 1) (fun _ => 0) = fun _ => 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show m + 1 + 1 = m + 2 from rfl, _root_.GlobalTheory.PosOne.toOne_succ, hdown, ih]
  cases P with
  | zero => rfl
  | succ m => exact key m

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_toOne_comm {X : Type} [TopologicalSpace X]
    (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ)
    (B B₁ : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] A →ₗ[ℂ] ℂ)
    (hB : ∀ Ψ v, B₁ Ψ v = _root_.GlobalTheory.PosOne.toOne ν σ P (B Ψ) v) (x : X → ℂ) (v : A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B₁ x v =
      _root_.GlobalTheory.PosOne.toOne ν σ P (fun w => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x w) v := by
  by_cases hx : x ∈ _root_.GlobalTheory.SplitWeil.SB X
  · simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_pos hx]
    exact hB _ _
  · simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_neg hx, LinearMap.zero_apply]
    rw [posOne_toOne_zero]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_of_mem_SB {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (B : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) {x : X → ℂ}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.SB X) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x = B ⟨x, hx⟩ := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_pos hx]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_of_not_mem_SB {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (B : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) {x : X → ℂ}
    (hx : x ∉ _root_.GlobalTheory.SplitWeil.SB X) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x = 0 := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_neg hx]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_zero_map {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (x : X → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (0 : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) x = 0 := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app
  split_ifs <;> rfl


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.PosOne.oneDbl_iff_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k) (_ : _root_.GlobalTheory.SplitWeil.IsUnitVol ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (L₁ : _root_.GlobalTheory.StepData.Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : _root_.GlobalTheory.StepData.Level (GL (n₂ ⊕ Fin c) k)) (_ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₁.J) (_ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₂.J) (_ : G₁ L₁.J = 1) (_ : G₂ L₂.J = 1) (b₁ : GL (n₁ ⊕ Fin (c + 1)) k) (b₂ : GL (n₂ ⊕ Fin c) k) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : _root_.GlobalTheory.SplitWeil.IsSmoothRep σ) (T : _root_.GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) →ₗ[ℂ] _root_.GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : _root_.GlobalTheory.PosOne.TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (_ : ∀ j : L₂.J, σ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) (Φ₁ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (_ : ∀ j : L₁.J, _root_.GlobalTheory.SplitWeil.om μ₁ 1 (j : GL (n₁ ⊕ Fin (c + 1)) k) Φ₁.1 = (((L₁.lam j)⁻¹ : ℂˣ) : ℂ) • Φ₁.1) (_ : _root_.GlobalTheory.StepData.HasTypes μ₂ L₁ L₂ Φ₂.1) (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (T₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (T₂ : Finset (GL (n₂ ⊕ Fin c) k)) (_ : _root_.GlobalTheory.PosOne.Covers 1 L₁.J T₁ fun h => _root_.GlobalTheory.StepData.flat ψ ν μ₁ Φ₁.1 α h) (_ : ∀ γ ∈ T₁, _root_.GlobalTheory.PosOne.Covers 1 L₂.J T₂ fun h => _root_.GlobalTheory.StepData.flat ψ ν μ₂ Φ₂.1 γ h) (z : ℂ), _root_.GlobalTheory.PosOne.OneDbl ψ ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ μ₁ μ₂ ρ σ T F (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1) Φ₂.1 z ↔ z = ∑ γ ∈ T₁, ∑ β ∈ T₂, (((m₁ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ hHaarM₁ G₁ hHaarG₁ m₂ hHaarM₂ G₂ hHaarG₂
    L₁ L₂ hL₁ hL₂ hG₁ hG₂ b₁ b₂ A _ _ σ hσ T hT F hF Φ₁ Φ₂ hΦ₁ hΦ₂ α T₁ T₂ hT₁ hT₂ z
  haveI : ν.IsAddHaarMeasure := hν.1
  have hψ1 : ψ ≠ 1 := hcond.ne_one
  have hsd : _root_.GlobalTheory.SplitWeil.IsSelfDual ψ ν :=
    _root_.GlobalTheory.SplitWeil.isSelfDual_of_isUnitVol ν hcond hν
  have hρ1 : 1 ≤ ρ := by omega
  have hρc : ρ ≤ c := by omega
  haveI hm₁ : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁).IsHaarMeasure :=
    isHaarMeasure_framePositiveSum_rescale ν b₁ m₁
  haveI hm₂ : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂).IsHaarMeasure :=
    isHaarMeasure_framePositiveSum_rescale ν b₂ m₂
  obtain ⟨ρ₁, hρ₁⟩ := (_root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂).1
  have hρ₁s := (_root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂).2 ρ₁ hρ₁
  obtain ⟨b, hb, -, hbone⟩ := @_root_.GlobalTheory.PosOne.MidVertex.exists_bilPos_mid
    k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hψ1 ν hsd
    μ₁ μ₂ hμ₁ hμ₂ m₁ hHaarM₁ G₁ hHaarG₁
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) hm₂ G₂ hHaarG₂ A _ _ σ hσ T hT F ρ₁ hρ₁
  obtain ⟨B', hB'eq, hB'⟩ := (_root_.GlobalTheory.PosOne.toOne_isPosOne k n₁ n₀ (c + 1) ρ hρ1 (by omega)
    ψ hψ hψ1 ν _ ρ₁ hρ₁s).2 μ₁ hμ₁ b hb
  have hin : ∀ Ψ, ∃ B₁ : _root_.GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ,
      (∀ Ψ' v, B₁ Ψ' v = _root_.GlobalTheory.PosOne.toOne ν σ ρ (T Ψ Ψ') v) ∧
        _root_.GlobalTheory.PosOne.BilPos ψ μ₂ 1 σ B₁ := fun Ψ =>
    (_root_.GlobalTheory.PosOne.toOne_isPosOne k n₂ n₁ c ρ hρ1 hρc ψ hψ hψ1 ν A σ hσ).2 μ₂ hμ₂ (T Ψ)
      (hT.1 Ψ)
  choose B₁ hB₁eq hB₁ using hin
  have uniq₁ := fun f => (@_root_.GlobalTheory.QuotInt.quotInt_unique_exists k _ _ _ _ _ _ n₁ _ _ (c + 1) 1 le_rfl
    (by omega) ν hν.1 (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) hm₁ G₁ hHaarG₁ f).1
  have uniq₂ := fun f => (@_root_.GlobalTheory.QuotInt.quotInt_unique_exists k _ _ _ _ _ _ n₂ _ _ c 1 le_rfl
    (by omega) ν hν.1 (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) hm₂ G₂ hHaarG₂ f).1
  have hinteg : ∀ Ψ Φb, _root_.GlobalTheory.PosOne.tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φb =
      _root_.GlobalTheory.PosOne.tInt ψ ν μ₂ 1 σ (B₁ Ψ) F Φb := by
    intro Ψ Φb
    funext h
    simp only [_root_.GlobalTheory.PosOne.tIntOne, _root_.GlobalTheory.PosOne.tInt]
    exact (fourierJacobiAverage_app_toOne_comm ν σ ρ (T Ψ) (B₁ Ψ) (hB₁eq Ψ) _ _).symm
  have hinner : ∀ h Ψ, _root_.GlobalTheory.RootEx.IsQuotInt ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂)
      G₂ 1 (_root_.GlobalTheory.PosOne.tInt ψ ν μ₂ 1 σ (B₁ Ψ) F (_root_.GlobalTheory.SplitWeil.om μ₂ h 1 Φ₂.1))
      (B' Ψ (ρ₁ h Φ₂)) := by
    intro h Ψ
    have := hbone Ψ (ρ₁ h Φ₂)
    rwa [hρ₁ h Φ₂, ← hB'eq Ψ, hinteg Ψ] at this
  have hF' : ∀ j : L₁.J, ρ₁ (j : GL (n₁ ⊕ Fin (c + 1)) k) Φ₂ = (L₁.lam j : ℂ) • Φ₂ := by
    intro j
    apply Subtype.ext
    rw [hρ₁, Submodule.coe_smul]
    exact hΦ₂.1 j
  have houter := @_root_.GlobalTheory.PosOneCell.quotInt_posOne
    k _ _ _ _ _ _ n₁ n₀ _ _ _ _ (c + 1) (by omega) ψ hψ hcond ν hν
    μ₁ hμ₁ m₁ hHaarM₁ G₁ hHaarG₁ L₁ hL₁ hG₁ b₁ _ _ _ ρ₁ hρ₁s B' hB' Φ₂ hF' Φ₁ hΦ₁ α T₁ hT₁
  have hinner_sum : ∀ γ ∈ T₁, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B' (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ) (ρ₁ γ Φ₂) = ∑ β ∈ T₂, (((m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
    intro γ hγ
    by_cases hx : _root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ ∈ _root_.GlobalTheory.SplitWeil.SB _
    · rw [fourierJacobiAverage_app_of_mem_SB B' hx, fourierJacobiAverage_app_of_mem_SB T hx]
      have hi := @_root_.GlobalTheory.PosOneCell.quotInt_posOne
        k _ _ _ _ _ _ n₂ n₁ _ _ _ _ c (by omega) ψ hψ hcond ν hν
        μ₂ hμ₂ m₂ hHaarM₂ G₂ hHaarG₂ L₂ hL₂ hG₂ b₂ A _ _ σ hσ
        (B₁ ⟨_, hx⟩) (hB₁ _) F hF Φ₂ hΦ₂.2 γ T₂ (hT₂ γ hγ)
      rw [uniq₂ _ _ _ (hinner γ ⟨_, hx⟩) hi]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [fourierJacobiAverage_app_toOne_comm ν σ ρ (T ⟨_, hx⟩) (B₁ ⟨_, hx⟩) (hB₁eq _)] <;> with_unfolding_all rfl
    · simp only [fourierJacobiAverage_app_of_not_mem_SB B' hx,
        fourierJacobiAverage_app_of_not_mem_SB T hx, fourierJacobiAverage_app_zero_map,
        LinearMap.zero_apply, posOne_toOne_zero, mul_zero,
        Finset.sum_const_zero]
  have hsum : ∀ S, _root_.GlobalTheory.RootEx.IsQuotInt ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ 1
      (_root_.GlobalTheory.PosOne.tInt ψ ν μ₁ 1 ρ₁ B' Φ₂ (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1)) S →
      S = ∑ γ ∈ T₁, ∑ β ∈ T₂, (((m₁ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
    intro S hS
    rw [uniq₁ _ _ _ hS houter]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hinner_sum γ hγ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    push_cast
    rw [mul_assoc] <;> with_unfolding_all rfl
  have hf : ∀ w : GL (n₁ ⊕ Fin (c + 1)) k → _root_.GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) →ₗ[ℂ] ℂ,
      (∀ h Ψ, w h Ψ = B' Ψ (ρ₁ h Φ₂)) →
      (fun h => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (w h) (_root_.GlobalTheory.RootEx.opE ψ ν 1
        (_root_.GlobalTheory.SplitWeil.om μ₁ 1 h (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1)))) =
      _root_.GlobalTheory.PosOne.tInt ψ ν μ₁ 1 ρ₁ B' Φ₂ (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1) := by
    intro w hw
    funext h
    simp only [_root_.GlobalTheory.PosOne.tInt, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app]
    split_ifs
    · exact hw _ _
    · rfl
  unfold _root_.GlobalTheory.PosOne.OneDbl
  constructor
  · rintro ⟨w, hw, hz⟩
    have hwv : ∀ h Ψ, w h Ψ = B' Ψ (ρ₁ h Φ₂) := by
      intro h Ψ
      have hwh := hw h Ψ
      rw [hinteg] at hwh
      exact uniq₂ _ _ _ hwh (hinner h Ψ)
    rw [hf w hwv] at hz
    exact hsum z hz
  · intro hz
    refine ⟨fun h => B'.flip (ρ₁ h Φ₂), fun h Ψ => ?_, ?_⟩
    · rw [hinteg]
      exact hinner h Ψ
    · rw [hf _ (fun h Ψ => rfl), hz, ← hsum _ houter]
      exact houter

end GlobalTheory.PosOne
end

section

namespace GlobalTheory.CoefficientSpanFinite

theorem finiteDimensional_span_coefficients {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) :
    FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let Φ : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun φ k => φ (ρ k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range Φ := by
    unfold GlobalTheory.Published.AutFin.coeffSpan
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ ∘ₗ LinearMap.applyₗ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CoefficientSpanFinite
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.typePrimes_product_not_mem_sq_place : ∀ (D : D7) (Q : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal ^ 2 := by
  first | exact @GlobalTheory.TypePrimeUnif.prod_not_mem_sq | exact GlobalTheory.TypePrimeUnif.prod_not_mem_sq | (intros; apply GlobalTheory.TypePrimeUnif.prod_not_mem_sq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryGroup_twoModels_rationalReal_unipotent_dictionary : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔ x ∈ (Formalism.IndefR.Eqv.UI.instV fr).GFset) ∧ (∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (Formalism.IndefR.Eqv.UI.brg fr x) = fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) ∧ ∀ W, (Formalism.IndefR.Eqv.UI.instV fr).IsIsot W → ∃ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ ∧ ∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ NI V C₀ → x ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W := by
  first | exact @GlobalTheory.BridgeDict.bridge_dict | exact GlobalTheory.BridgeDict.bridge_dict | (intros; apply GlobalTheory.BridgeDict.bridge_dict <;> assumption)
end
