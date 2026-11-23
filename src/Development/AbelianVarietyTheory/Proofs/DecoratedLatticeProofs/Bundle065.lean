module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle061
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle059
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.exists_colSpaceAutToLocalGL_mem_open_dense : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (y : GL A k) (V : Set (GL A k)), IsOpen V → y ∈ V → ∃ x : Sp E M ≃ₗ[E] Sp E M, locHom ι e x ∈ V := by
  first | exact @GlobalTheory.denseGL_completion | exact GlobalTheory.denseGL_completion | (intros; apply GlobalTheory.denseGL_completion <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.mem_N1_iff_locHom_mem_N_one : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1 := by
  first | exact @GlobalTheory.UnipRead.mem_N1_iff_local_hom | exact GlobalTheory.UnipRead.mem_N1_iff_local_hom | (intros; apply GlobalTheory.UnipRead.mem_N1_iff_local_hom <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.mem_R1_iff_local_hom : ∀ {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ x : Sp E (M + c') ≃ₗ[E] Sp E (M + c'), x ∈ Loc.R1 E M c' ↔ locHom ι e x ∈ R k A c 1 := by
  first | exact @GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange | exact GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange | (intros; apply GlobalTheory.RankOneMatrix.mem_rationalFirstParabolic_iff_localGL_mem_rootExchange <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL : ∀ {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (x : Sp E M ≃ₗ[E] Sp E M), x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  first | exact @GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | exact GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | (intros; apply GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.exists_N1_locHom_mem_open : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V := by
  first | exact @GlobalTheory.VolBridge.exists_N1_local_hom_mem_open | exact GlobalTheory.VolBridge.exists_N1_local_hom_mem_open | (intros; apply GlobalTheory.VolBridge.exists_N1_local_hom_mem_open <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem _root_.GlobalTheory.T.mem_mirabolicProjection_iff_colSpaceAutToLocalGL : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val), (∀ x, x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1) → (∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V) → ∀ (CE : Subgroup (Sp E (M + c') ≃ₗ[E] Sp E (M + c'))) (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (∀ z ∈ R k A c 1, z ∈ Ck ↔ z ∈ O) → Ck ≤ R k A c 1 → (∀ x, x ∈ CE ↔ locHom ι e x ∈ Ck) → ∀ y, y ∈ Loc.prX CE ↔ locHom ι (eX e hcc he) y ∈ prX Ck := by
  first | exact @GlobalTheory.VolBridge.prX_iff_locHom | exact GlobalTheory.VolBridge.prX_iff_locHom | (intros; apply GlobalTheory.VolBridge.prX_iff_locHom <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_of_sqrtDetTwist : ∀ (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ), HasTypes (Cover.twist R) lam → HasTypes R fun a => lam a + 1 / 2 := by
  first | exact @GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | exact GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist | (intros; apply GlobalTheory.CoverDS.TwistTypes.hasTypes_of_twist <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  first | exact @GlobalTheory.CoverDS.unitEquiv_of_dsUnique | exact GlobalTheory.CoverDS.unitEquiv_of_dsUnique | (intros; apply GlobalTheory.CoverDS.unitEquiv_of_dsUnique <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

namespace GlobalTheory.FinSubgroup

theorem exists_openAddSubgroup_finite_points :
    ∀ (D : D7) (V : Set (AE D)), V ∈ nhds (0 : AE D) →
      ∃ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) ∧ ∀ a ∈ U, infPart D a = 0 → a ∈ V := by
  intro D V hV
  obtain ⟨e, he, hc, hcs⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)
  letI : TopologicalSpace (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (InfiniteAdeleRing D.host.F) (InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E)
  have h0 : e.symm 0 = 0 := map_zero _
  have hV' : (e.symm : _ → AE D) ⁻¹' V ∈ 𝓝 ((0 : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E),
      (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) := by
    apply hcs.continuousAt.preimage_mem_nhds
    have : (e.symm : _ → AE D) (0, 0) = 0 := h0
    rw [this]
    exact hV
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hV'
  obtain ⟨N, hN, hNB⟩ := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (Subsingleton.elim _ _)).2 B hB
  let W : AddSubgroup (GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    (GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E))).map (nsmulAddMonoidHom N)
  have hW : IsOpen (W : Set (GlobalTheory.AdLat.RA D.host.F D.host.E)) := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN
    convert this using 1
    ext z
    simp only [W, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, nsmulAddMonoidHom_apply, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  let f : AE D →+ GlobalTheory.AdLat.RA D.host.F D.host.E := (AddMonoidHom.snd _ _).comp e.toAddMonoidHom
  have hf : Continuous f := continuous_snd.comp hc
  refine ⟨W.comap f, hW.preimage hf, fun a ha hinf => ?_⟩
  have h1 : (e a).1 = 0 := by rw [(he a).1]; exact hinf
  have h2 : (e a).2 ∈ B := by
    obtain ⟨y, hy, hya⟩ := AddSubgroup.mem_map.1 (AddSubgroup.mem_comap.1 ha)
    have : f a = (e a).2 := rfl
    rw [← this, ← hya]
    exact hNB y hy
  have h3 : e a ∈ A ×ˢ B := ⟨by rw [h1]; exact mem_of_mem_nhds hA, h2⟩
  have := hAB h3
  simpa using this

end GlobalTheory.FinSubgroup
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_integer_sub_conj_notMem_self_conjugate_place : ∀ (D : D7) (Q : Pl D.host.E), IsConjPl (D := D) Q Q → ∃ δ δ' : 𝓞 D.host.E, (δ' : D.host.E) = star (δ : D.host.E) ∧ δ - δ' ∉ Q.asIdeal := by
  first | exact @GlobalTheory.ConjMovesResidue.exists_sub_star_notMem | exact GlobalTheory.ConjMovesResidue.exists_sub_star_notMem | (intros; apply GlobalTheory.ConjMovesResidue.exists_sub_star_notMem <;> assumption)
end

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct

namespace GlobalTheory.FlagBasis

def dualIdx (ρ k i : ℕ) : ℕ :=
  if i < ρ then 2 * ρ + k - i else if i < ρ + k then 2 * ρ + k - 1 - i else if i = ρ + k then i else 2 * ρ + k - i

def flagGram (A : Type) [CommRing A] (n ρ k : ℕ) : Matrix (Fin n) (Fin n) A :=
  fun i j => if j.val = dualIdx ρ k i.val then (if i.val = ρ + k then -1 else 1) else 0

def FlagCond {A : Type} [CommRing A] {n : ℕ} (P : A → Prop) (ρ k : ℕ) (ε : A) (m : Matrix (Fin n) (Fin n) A) : Prop :=
  (∀ i j : Fin n, j.val < ρ → j.val ≤ i.val → P ((m - 1) i j)) ∧
  (∀ i j : Fin n, j.val = ρ + k → ρ ≤ i.val → P ((m - 1) i j)) ∧
  ∀ i j : Fin n, ρ ≤ j.val → j.val < ρ + k → j.val ≤ i.val → P (ε * (m - 1) i j)

def rootSum {A : Type} [CommRing A] {n : ℕ} (ρ k : ℕ) (ε : A) (m : Matrix (Fin n) (Fin n) A) : A :=
  ∑ i : Fin n, ∑ j : Fin n,
    if (i.val + 1 < ρ ∧ j.val = i.val + 1) ∨ (i.val + 1 = ρ ∧ j.val = ρ + k) then m i j
    else if ρ ≤ i.val ∧ j.val = i.val + 1 ∧ j.val < ρ + k then ε * m i j else 0

def flagVec {V : Type} [AddCommGroup V] {ρ k : ℕ} (e0 f0 : Fin ρ → V) (z0 : V) (bw bwd : Fin k → V) (j : ℕ) : V :=
  if h : j < ρ then e0 ⟨j, h⟩
  else if h : j - ρ < k then bw ⟨j - ρ, h⟩ + bwd (Fin.rev ⟨j - ρ, h⟩)
  else if j = ρ + k then z0
  else if h : 2 * ρ + k - j < ρ then f0 ⟨2 * ρ + k - j, h⟩ else 0

def IsRefFrame (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : I.E ⊗[I.F] Af I.F) : Prop :=
  ((∀ a, e0 a ∈ I.Lf ∧ f0 a ∈ I.Lf) ∧ z0 ∈ I.Lf ∧ ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf) ∧
  (∀ a b, ZMod' I g (hA I (e0 a) (e0 b)) ∧ ZMod' I g (hA I (f0 a) (f0 b)) ∧
    ZMod' I g (hA I (e0 a) (f0 b) - if a = b then 1 else 0)) ∧
  (ZMod' I g (hA I z0 z0 + 1) ∧ ∀ a, ZMod' I g (hA I (e0 a) z0) ∧ ZMod' I g (hA I (f0 a) z0)) ∧
  (∀ i, ZMod' I g (hA I z0 (bw i)) ∧ ZMod' I g (hA I z0 (bwd i)) ∧
    ∀ a, ZMod' I g (hA I (e0 a) (bw i)) ∧ ZMod' I g (hA I (f0 a) (bw i)) ∧
      ZMod' I g (hA I (e0 a) (bwd i)) ∧ ZMod' I g (hA I (f0 a) (bwd i))) ∧
  (ew * ew = ew ∧ ew * sigA I ew = 0 ∧ ew ∈ IntAf I.F I.E ∧ ∀ y ∈ I.Lf, (1 - ew - sigA I ew) • y ∈ mL I g) ∧
  ((∀ i, bw i = ew • bw i) ∧ ∀ i, bwd i = sigA I ew • bwd i) ∧
  (∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)) ∧
  ∀ y ∈ I.Lf, InMod I g (Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd) y

theorem isRefFrame_setting {D : Formalism.BasicNotions.D7} (X : HidaSetting D) :
    IsRefFrame X.B.I X.B.g X.e0 X.f0 X.z0 X.bw X.bwd X.ew :=
  ⟨X.vectorsInLattice, X.gramIntegral, X.formsAtZero, X.weightVectorsIntegral, ⟨X.ew_idem, X.ew_orth, X.ew_int, X.ew_full⟩, ⟨X.bw_w, X.bwd_w⟩,
    fun i j => by convert X.bw_dual i j, X.latticeSpan⟩

def IsLiftFrame (I : AutInst) (g : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Prop :=
  Formalism.L2.DIV.IsFrame β I.L ∧
    ∀ j : Fin I.n, (fun i => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j) - b j.val ∈ mL I g

def matIn (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (x : I.Gf) :
    Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  ((β⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _)

def gramIn (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  fun i j => hA I (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) l i)
    (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) l j)

def sigInt (I : AutInst) : Formalism.L2.Herm.intAf I.F I.E →+* Formalism.L2.Herm.intAf I.F I.E :=
  ((sigA I).comp (Formalism.L2.Herm.intAf I.F I.E).subtype).codRestrict _ fun s => Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I s.2

theorem sigInt_coe (I : AutInst) (s : Formalism.L2.Herm.intAf I.F I.E) :
    ((sigInt I s : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) = sigA I s := rfl

def chiArg (I : AutInst) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (x : I.Gf) :
    I.E ⊗[I.F] Af I.F :=
  (∑ a, hA I (f0 a) (I.fmat x *ᵥ nxt e0 z0 a)) +
    ∑ i : Fin k, if h : i.1 + 1 < k then hA I (bwd i) (I.fmat x *ᵥ bw ⟨i.1 + 1, h⟩) else 0

theorem flagLevelCharacter_eq_psi_divN (I : AutInst) (psiEf : I.E ⊗[I.F] Af I.F → ℂ) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I)
    (bw bwd : Fin k → VA I) (x : I.Gf) :
    chi2f I psiEf g e0 f0 z0 bw bwd x = psiEf (divN I g (chiArg I e0 f0 z0 bw bwd x)) := rfl

end GlobalTheory.FlagBasis

end
end

section

noncomputable section

namespace GlobalTheory.Core.Rk.RapidInt

open scoped TensorProduct ENNReal NNReal ComplexConjugate Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Cont GlobalTheory.GaugeEx
open NumberField.mixedEmbedding
open scoped Classical

section Mixed

variable (F : Type) [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

end Mixed

section Tup

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (M n : ℕ)

def crdTup : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₗ[Ainf F] (Fin n → Fin M → Fin d → Ainf F) :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.piCongrRight fun _ =>
    (Algebra.TensorProduct.basis (Ainf F) b).equivFun

def mixTup : (Fin n → Fin M → Fin d → Ainf F) ≃+ (Fin n → Fin M → Fin d → mixedSpace F) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ =>
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv

theorem continuous_crdTup : Continuous (crdTup F E b M n) :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).toLinearMap

theorem continuous_crdTup_symm : Continuous (crdTup F E b M n).symm :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).symm.toLinearMap

theorem continuous_mixTup : Continuous (mixTup F M n (d := d)) :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_toMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

theorem continuous_mixTup_symm : Continuous (mixTup F M n (d := d)).symm :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (continuous_ofMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

def tupEquiv : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (Fin n → Fin M → Fin d → mixedSpace F) where
  toAddEquiv := (crdTup F E b M n).toAddEquiv.trans (mixTup F M n)
  continuous_toFun := (continuous_mixTup F M n).comp (continuous_crdTup F E b M n)
  continuous_invFun := (continuous_crdTup_symm F E b M n).comp (continuous_mixTup_symm F M n)


end Tup


end GlobalTheory.Core.Rk.RapidInt
end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_openAddSubgroup_finite_points_alt : ∀ (D : D7) (V : Set (AE D)), V ∈ nhds (0 : AE D) → ∃ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) ∧ ∀ a ∈ U, infPart D a = 0 → a ∈ V := by
  first | exact @GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points | exact GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points | (intros; apply GlobalTheory.FinSubgroup.exists_openAddSubgroup_finite_points <;> assumption)

end
end
