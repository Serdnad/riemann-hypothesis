module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle841
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.IsoRankMult

open GlobalTheory.RepCount in
theorem iso_of_hom_into_sum : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X), σ0.IsIrreducible → σ.IsIrreducible → ∀ f ∈ homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g), f ≠ 0 → Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) := by
  intro H S0 S X _ _ _ _ _ _ _ σ0 σ ρ C h0 h1 f hf hne
  let R := MonoidAlgebra ℂ H
  haveI : IsSimpleModule R σ0.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ0).mp h0
  haveI : IsSimpleModule R σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp h1

  let N' : Submodule R ρ.asModule :=
    ⨆ (g : S0 →ₗ[ℂ] X) (hg : g ∈ homInto σ0 ρ C), LinearMap.range (modMap g hg.2)
  have hN'iso : N' ≤ isotypicComponent R ρ.asModule σ0.asModule := by
    refine iSup₂_le fun g hg => ?_
    rcases LinearMap.injective_or_eq_zero (modMap (σ := σ0) (ρ := ρ) g hg.2) with hi | hz
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [hz, LinearMap.range_zero]; exact bot_le
  have hsub : (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ≤
      (N'.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨s, rfl⟩
    have hmem : modMap (σ := σ0) (ρ := ρ) g hg.2 (σ0.asModuleEquiv.symm s) ∈ N' :=
      (le_iSup₂_of_le (f := fun (g : S0 →ₗ[ℂ] X) (hg : g ∈ homInto σ0 ρ C) =>
        LinearMap.range (modMap (σ := σ0) (ρ := ρ) g hg.2)) g hg le_rfl) ⟨_, rfl⟩
    show ρ.asModuleEquiv.symm (g s) ∈ N'
    convert hmem using 1
    apply ρ.asModuleEquiv.injective
    rw [modMap_apply]; simp
  let F := modMap (σ := σ) (ρ := ρ) f hf.2
  have hFi : Function.Injective F := by
    rcases LinearMap.injective_or_eq_zero F with hi | hz
    · exact hi
    · exfalso; apply hne
      ext s
      have := congrArg (fun φ => ρ.asModuleEquiv (φ (σ.asModuleEquiv.symm s))) hz
      simp only [F, modMap_apply, LinearMap.zero_apply, map_zero] at this
      simpa using this
  have hle : LinearMap.range F ≤ isotypicComponent R ρ.asModule σ0.asModule := by
    refine le_trans ?_ hN'iso
    rintro _ ⟨x, rfl⟩
    have hx := hsub (hf.1 (σ.asModuleEquiv x))
    have : ρ.asModuleEquiv.symm (f (σ.asModuleEquiv x)) = F x := by
      apply ρ.asModuleEquiv.injective; simp [F, modMap_apply]
    rw [← this]; exact hx
  let e := LinearEquiv.ofInjective F hFi
  haveI : IsSimpleModule R (LinearMap.range F) := IsSimpleModule.congr e.symm
  obtain ⟨e'⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R ρ.asModule σ0.asModule) (LinearMap.range F) hle
  exact ⟨e.trans e'⟩

end GlobalTheory.IsoRankMult
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

noncomputable section

namespace GlobalTheory.IsotConj

open GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem conjMap_zero' (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) : conjMap M M' c h 0 = 0 :=
  MultilinearMap.ext fun _ => star_zero _

theorem conjMap_add (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T T' : MMap M) :
    conjMap M M' c h (T + T') = conjMap M M' c h T + conjMap M M' c h T' :=
  MultilinearMap.ext fun _ => star_add _ _

theorem conjMap_smul (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (r : ℂ) (T : MMap M) :
    conjMap M M' c h (r • T) = star r • conjMap M M' c h T := by
  refine MultilinearMap.ext fun v' => ?_
  show star (r • (T : MMap M) _) = star r • star ((T : MMap M) _)
  rw [star_smul]

theorem conjMap_actM {n : ℕ} (P : principalLevelFrame.RowPsi V n) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (k : Formalism.AUTREP.GAf D.host.E n) (T : MMap M) :
    conjMap M M' c h (principalLevelFrame.actM P M k T) = principalLevelFrame.actM P M' k (conjMap M M' c h T) :=
  MultilinearMap.ext fun _ => funext fun _ => rfl

theorem conjMap_minf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (hM : ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec),
      (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g))
    (T : MMap M) (hT : T ∈ principalLevelFrame.Minf θ P M) : conjMap M M' c h T ∈ principalLevelFrame.Minf θ P M' := by
  unfold principalLevelFrame.Minf at hT ⊢
  refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ _) hT ?_ ?_ ?_
  · intro N T hT
    obtain ⟨T', hT', e1⟩ := hM _ _ T hT
    have : conjMap M M' c h T = T' := by
      refine MultilinearMap.ext fun v' => funext fun g => ?_
      rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
      rfl
    rw [this]
    exact Submodule.mem_iSup_of_mem N (mult_congr θ M' (fun k _ => by simp) hT')
  · rw [conjMap_zero']; exact zero_mem _
  · intro T T' h1 h2
    rw [conjMap_add]; exact add_mem h1 h2

def cjS {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (x : π.S) : (principalLevelFrame.FinTyp.conjT π).S :=
  ⟨fun g => star ((x : Formalism.AUTREP.GAf D.host.E n → ℂ) g), by
    show (fun g => star (star ((x : Formalism.AUTREP.GAf D.host.E n → ℂ) g))) ∈ π.S
    simpa using x.2⟩

theorem cjS_add {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (x y : π.S) : cjS π (x + y) = cjS π x + cjS π y :=
  Subtype.ext (funext fun _ => star_add _ _)

theorem cjS_smul {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (a : ℂ) (x : π.S) : cjS π (a • x) = star a • cjS π x :=
  Subtype.ext (funext fun _ => by simp [cjS, mul_comm])

theorem conjT_conjT {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) : principalLevelFrame.FinTyp.conjT (principalLevelFrame.FinTyp.conjT π) = π := by
  rcases π with ⟨S0, _, _, _, _⟩
  show Formalism.L2.NG.FinTyp.mk (principalLevelFrame.conjSub (principalLevelFrame.conjSub S0)) _ _ _ _ = _
  congr 1
  exact principalLevelFrame.conjSub_conjSub S0

theorem conjMap_isot (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (hM : ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec),
      (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g))
    (π : Formalism.L2.NG.FinTyp D.host.E n) (T : MMap M)
    (hT : T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) (principalLevelFrame.FinTyp.conjT π)) :
    conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π := by
  unfold principalLevelFrame.isotIn at hT
  refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π) hT ?_ ?_ ?_
  · intro Φ T hT
    refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π) hT ?_ ?_ ?_
    · rintro ⟨hΦ, hR⟩ T ⟨f, rfl⟩
      let Ψ : π.S →ₗ[ℂ] MMap M' :=
        { toFun := fun x => conjMap M M' c h (Φ (cjS π x))
          map_add' := fun x y => by rw [cjS_add, map_add (f := _), conjMap_add]
          map_smul' := fun a x => by simp only [RingHom.id_apply]; rw [cjS_smul, map_smul, conjMap_smul, star_star] }
      have hΨ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M') π Ψ := by
        intro k x
        show conjMap M M' c h (Φ (cjS π _)) = principalLevelFrame.actM P M' k (conjMap M M' c h (Φ (cjS π x)))
        rw [← conjMap_actM, ← hΦ k]
        rfl
      have hΨR : LinearMap.range Ψ ≤ principalLevelFrame.Minf θ P M' := by
        rintro _ ⟨x, rfl⟩
        exact conjMap_minf θ P M M' c h hM _ (hR (LinearMap.mem_range_self Φ _))
      have e : cjS π ⟨fun g => star ((f : Formalism.AUTREP.GAf D.host.E n → ℂ) g), f.2⟩ = f :=
        Subtype.ext (funext fun _ => star_star _)
      refine Submodule.mem_iSup_of_mem Ψ (Submodule.mem_iSup_of_mem ⟨hΨ, hΨR⟩ ⟨⟨fun g => star ((f : Formalism.AUTREP.GAf D.host.E n → ℂ) g), f.2⟩, ?_⟩)
      show conjMap M M' c h (Φ (cjS π _)) = conjMap M M' c h (Φ f)
      rw [e]
    · rw [conjMap_zero']; exact zero_mem _
    · intro T T' h1 h2
      rw [conjMap_add]; exact add_mem h1 h2
  · rw [conjMap_zero']; exact zero_mem _
  · intro T T' h1 h2
    rw [conjMap_add]; exact add_mem h1 h2

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {n : ℕ}
    (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) :
    Module.rank ℂ (principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π)) ≤ Module.rank ℂ (principalLevelFrame.isotL θ P M' J χ' e' π) := by
  obtain ⟨h, hM⟩ := GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc
  have key : ∀ T ∈ principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π), conjMap M M' c h T ∈ principalLevelFrame.isotL θ P M' J χ' e' π := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, conjMap_isot θ P M M' c h hM π T h3⟩
    · obtain ⟨T', hT', e1⟩ := hM J χ T h1
      have : conjMap M M' c h T = T' := by
        refine MultilinearMap.ext fun v' => funext fun g => ?_
        rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
        rfl
      rw [this]
      exact mult_congr θ M' hχ hT'
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
  let j : principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π) →+ principalLevelFrame.isotL θ P M' J χ' e' π :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π)) = Module.rank ℂ (principalLevelFrame.isotL θ P M' J χ' e' π) := by
  intro D V S S' θ M M' c hc J χ χ' e e' n P π hχ he
  refine le_antisymm (rank_le θ M M' c hc J χ χ' e e' P π hχ he) ?_
  have := rank_le θ M' M (fun τ => (c τ).symm) ?_ J χ' χ e' e P (principalLevelFrame.FinTyp.conjT π) ?_ ?_
  · rwa [conjT_conjT] at this
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]

end GlobalTheory.IsotConj

end
end

section

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.CoefInt

attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing of_isDiscreteValuationRing

open IsLocalRing Topology

variable {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  [FiniteDimensional ℚ_[l] K]


omit [FiniteDimensional ℚ_[l] K] in
theorem dvd_iff_norm_le {a : integralClosure ℤ_[l] K} (ha : a ≠ 0) (x : integralClosure ℤ_[l] K) :
    a ∣ x ↔ ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((a : K) : PadicAlgCl l)‖ := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy := (GlobalTheory.mem_integralClosure_padicInt_iff K y).mp y.2
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  · intro h
    have h0 : (a : K) ≠ 0 := fun h0 => ha (Subtype.ext h0)
    have h1 : ((a : K) : PadicAlgCl l) ≠ 0 := fun h1 => h0 (Subtype.ext h1)
    have hm : (x : K) / (a : K) ∈ integralClosure ℤ_[l] K := by
      rw [GlobalTheory.mem_integralClosure_padicInt_iff, IntermediateField.coe_div, norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)
    exact ⟨⟨_, hm⟩, Subtype.ext (mul_div_cancel₀ _ h0).symm⟩

theorem isAdic_maximalIdeal : IsAdic (maximalIdeal (integralClosure ℤ_[l] K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[l] K)
  have hind : IsInducing (fun x : integralClosure ℤ_[l] K => ((x : K) : PadicAlgCl l)) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have hlt : ‖((π : K) : PadicAlgCl l)‖ < 1 :=
    (GlobalTheory.mem_maximalIdeal_integralClosure_iff K π).1 hπ.not_isUnit
  have hpos : 0 < ‖((π : K) : PadicAlgCl l)‖ :=
    norm_pos_iff.2 fun h => hπ.ne_zero (Subtype.ext (Subtype.ext h))
  have hmem : ∀ (n : ℕ) (x : integralClosure ℤ_[l] K),
      x ∈ maximalIdeal (integralClosure ℤ_[l] K) ^ n ↔
        ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((π : K) : PadicAlgCl l)‖ ^ n := fun n x => by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      dvd_iff_norm_le K (pow_ne_zero n hπ.ne_zero)]
    push_cast
    rw [norm_pow]
  have hn : ∀ s : Set (integralClosure ℤ_[l] K), s ∈ 𝓝 (0 : integralClosure ℤ_[l] K) ↔
      ∃ ε > 0, ∀ x : integralClosure ℤ_[l] K, ‖((x : K) : PadicAlgCl l)‖ < ε → x ∈ s := fun s => by
    rw [hind.nhds_eq_comap, ((Metric.nhds_basis_ball).comap _).mem_iff]
    refine exists_congr fun ε => and_congr_right fun _ => ?_
    simp [Set.subset_def]
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds
      (maximalIdeal (integralClosure ℤ_[l] K) ^ n).toAddSubgroup (g := 0) ?_
    exact (hn _).2 ⟨_, pow_pos hpos n, fun x hx => (hmem n x).2 hx.le⟩
  · obtain ⟨ε, hε, h⟩ := (hn s).1 hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    exact ⟨n, fun x hx => h x (((hmem n x).1 hx).trans_lt hn)⟩

theorem finite_residueField : Finite (ResidueField (integralClosure ℤ_[l] K)) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] K
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] K
  have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (ResidueField ℤ_[l])

theorem integers_laws : ∀ (l : ℕ) [Fact l.Prime] (LL : Loc.FinExt l), ∃ (_ : IsDiscreteValuationRing ↥(Loc.OL LL)), Module.Finite ℤ_[l] ↥(Loc.OL LL) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ↥(Loc.OL LL) ∧ Finite (IsLocalRing.ResidueField ↥(Loc.OL LL)) ∧ IsFractionRing ↥(Loc.OL LL) ↥LL.1 := by
  intro l _ LL
  have := LL.2
  exact ⟨GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l LL.1,
    GlobalTheory.finite_integralClosure_padicInt l LL.1, isAdic_maximalIdeal LL.1,
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] (integralClosure ℤ_[l] LL.1),
    finite_residueField LL.1, GlobalTheory.isFractionRing_integralClosure_padicInt l LL.1⟩

end GlobalTheory.CoefInt
end

section

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical

namespace GlobalTheory.InertExchange

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem patchAt_commens (A B : Submodule (𝓞 E) (Sp E n)) (hA : Submodule.IsFullLattice E A)
    (hB : Submodule.IsFullLattice E B) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ (∀ x ∈ A, d • x ∈ B) ∧ (∀ x ∈ B, d • x ∈ A) := by
  obtain ⟨a, ha, hA1, hA2⟩ := Formalism.L2.DIV.lc_sandwich A hA
  obtain ⟨b, hb, hB1, hB2⟩ := Formalism.L2.DIV.lc_sandwich B hB
  refine ⟨a * b, mul_ne_zero ha hb, fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_comm, mul_smul]
    exact hB2 _ (hA1 x hx)
  · rw [mul_smul]
    exact hA2 _ (hB1 x hx)

theorem patchAt_isLattice_locP (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) :
    Submodule.IsFullLattice E A → Submodule.IsFullLattice E B → Submodule.IsLattice E (patchAt P A B) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (patchAt P A B) = localization₂ Q.asIdeal (if Q = P then A else B) := by
  intro hA hB
  obtain ⟨d, hd, hAB, hBA⟩ := patchAt_commens A B hA hB
  let Λ : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) (Sp E n) := fun Q => localization₂ Q.asIdeal (if Q = P then A else B)
  have hcl : ∀ Q, localization₂ Q.asIdeal (Λ Q) = Λ Q := fun Q => Formalism.L2.DIV.localized_localized Q _
  have h1 : ∀ Q, ∀ x ∈ Λ Q, d • x ∈ localization₂ Q.asIdeal B := by
    intro Q x hx
    by_cases hQ : Q = P
    · subst hQ
      simp only [Λ, if_true] at hx
      obtain ⟨s, hs, hsx⟩ := hx
      refine ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact hAB _ hsx
    · simp only [Λ, hQ, if_false] at hx
      exact Submodule.smul_mem _ d hx
  have h2 : ∀ Q, ∀ x ∈ B, d • x ∈ Λ Q := by
    intro Q x hx
    by_cases hQ : Q = P
    · simp only [Λ, hQ, if_true]
      exact Formalism.L2.DIV.lc_le_locP _ _ (hBA x hx)
    · simp only [Λ, hQ, if_false]
      exact Formalism.L2.DIV.lc_le_locP _ _ (B.smul_mem d hx)
  have hpat : patchAt P A B = ⨅ Q, Λ Q := rfl
  refine ⟨?_, fun Q => ?_⟩
  · have hdE : (algebraMap (𝓞 E) E d) ≠ 0 := by
      intro h
      exact hd (FaithfulSMul.algebraMap_injective (𝓞 E) E (by rw [h, map_zero]))
    have hmem : ∀ x ∈ B, d • x ∈ patchAt P A B := by
      intro x hx
      rw [hpat, Submodule.mem_iInf]
      exact fun Q => h2 Q x hx
    have hle : ∀ x ∈ patchAt P A B, d • x ∈ B := by
      intro x hx
      rw [hpat, Submodule.mem_iInf] at hx
      have : Submodule.span (𝓞 E) {d • x} ≤ B :=
        Formalism.L2.DIV.lc_le_of_le_locP fun Q => by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact h1 Q x (hx Q)
      exact this (Submodule.subset_span rfl)
    let f : Sp E n →ₗ[𝓞 E] Sp E n := d • LinearMap.id
    have hf : Function.Injective f := by
      intro x y hxy
      have e : algebraMap (𝓞 E) E d • x = algebraMap (𝓞 E) E d • y := by
        simpa [f, algebraMap_smul] using hxy
      exact smul_right_injective _ hdE e
    refine ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hB.fg ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hle x hx
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · rw [hpat]
    exact Formalism.L2.DIV.localized_iInf Λ B d hd hcl h1 h2 Q

end GlobalTheory.InertExchange
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.casselmanWallach_extension_banach_target : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → ∀ T₀ : H →ₗ[ℂ] E, (∀ k ∈ Kset ε, ∀ v, IsKFin ε σ v → T₀ (σ k v) = ρ k (T₀ v)) → (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0) → ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ (∀ g ∈ UJset ε, ∀ w, Sm ε σ w → T (σ g w) = ρ g (T w)) ∧ ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ ∀ w, Sm ε σ w → ‖T w‖ ≤ C * sobNorm σ S w := by
  first | exact @GlobalTheory.TypeSum.casselmanWallach_banach | exact GlobalTheory.TypeSum.casselmanWallach_banach | (intros; apply GlobalTheory.TypeSum.casselmanWallach_banach <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceOverSplit

theorem eq_or_eq_cP : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w := by
  intro D _ s Q hQ
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE (D := D) s.w Q (hQ.trans s.w_under.symm) with e | e
  · exact Or.inl e
  · refine Or.inr (e.trans (HeightOneSpectrum.ext (Ideal.ext fun x => ?_)))
    rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.IdemSupport.mem_cP]
    have : IsCMField.ringOfIntegersComplexConj D.host.E x = GlobalTheory.IdemSupport.cO D x := by
      apply RingOfIntegers.ext
      rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.IdemSupport.cO_coe]
      rfl
    rw [this]

end GlobalTheory.PlaceOverSplit
end
