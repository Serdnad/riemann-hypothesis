module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.HaarIdx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uLeKfHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle002
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

variable {D : D7}

def levelSubgroupOfCharacter (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' := fun ha hb => hK.2.1 _ ha _ hb
  inv_mem' := fun ha => hK.2.2.1 _ ha

def conjugateLevelSubgroup (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) :
    Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  ((levelSubgroupOfCharacter X hK).map (PI.MassDataKppVolLemmas.tfHom X.B.I hb)).map
    (MulAut.conj (finHA X hb (X.xu w))).toMonoidHom

theorem coe_K2uSub (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) :
    (conjugateLevelSubgroup X hb hK w : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) = K2u X hb w := by
  rw [conjugateLevelSubgroup, Subgroup.coe_map, Subgroup.coe_map]
  rfl

def conjugateLevelLocal (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word)
    (v : HeightOneSpectrum (𝓞 X.B.I.F)) : Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :=
  (conjugateLevelSubgroup X hb hK w).map (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v))

theorem coe_K2vSub (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word)
    (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    (conjugateLevelLocal X hb hK w v : Set (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J)) =
      compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) v := by
  rw [conjugateLevelLocal, Subgroup.coe_map, coe_K2uSub]
  rfl

def KvSub (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :=
  (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).comap
    (HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J).subtype

theorem local_level_le_maximal (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (w : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) : conjugateLevelLocal X hb hK w v ≤ KvSub X v := by
  rintro _ ⟨h, hh, rfl⟩
  have h1 : h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    k2uLeKf_holds X hb hK hL w (by rw [← coe_K2uSub X hb hK w]; exact hh)
  rw [Kf, Subgroup.mem_iInf] at h1
  exact h1 v

def ConjugateLevelOpenUnitary : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ w : D.what₂.Word, IsOpen (Subtype.val ⁻¹' K2u X hb w :
      Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)))

def ParabolicLevelOpenLocal : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X), IsOpen (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))

theorem contMul_sub {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] (S : Subgroup G) :
    ContinuousMul S := by
  have hc : Continuous fun q : S × S => ((q.1 : G) * (q.2 : G)) :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  exact ⟨hc.subtype_mk (fun q => S.mul_mem q.1.2 q.2.2)⟩

theorem contMul_HAf {D : D7} (X : HidaSetting D) : ContinuousMul (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsModuleTopology (Af X.B.I.F) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E) := ⟨rfl⟩
  have := IsModuleTopology.isTopologicalRing (Af X.B.I.F) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)
  exact inferInstanceAs (ContinuousMul (HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))

theorem contMul_HAv {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    ContinuousMul (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsModuleTopology (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := ⟨rfl⟩
  have := IsModuleTopology.isTopologicalRing (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
  exact inferInstanceAs (ContinuousMul (HR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J))

theorem haarIdxGlob_of (hO : ConjugateLevelOpenUnitary) : HaarIdxGlob := by
  intro D X hb hK hT hL w
  have hH : ((X.measW w).μHf).IsHaarMeasure := (X.measW_norm w).2.2.1
  have := contMul_HAf X
  have := contMul_sub (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
  haveI : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have eA : (Subtype.val ⁻¹' K2u X hb w : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := by
    ext x
    show (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb w ↔ (x : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ conjugateLevelSubgroup X hb hK w
    rw [← coe_K2uSub X hb hK w]
    rfl
  have eB : (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := rfl
  have hle : (conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) ≤
      (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact k2uLeKf_holds X hb hK hL w (by rw [← coe_K2uSub X hb hK w]; exact hx)
  have hop := hO X hb hK hT hL w
  rw [eA] at hop
  have hBor : BorelSpace (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) :=
    Subtype.borelSpace (fun x => x ∈ ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) : Subgroup _) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))
  have key := toReal_eq_relIndex_mul_of_haar (G := Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))
    (contMul_sub _) hBor
    (X.measW w).μHf hH _ _ hle hop
  have eA' : Subgroup.closure (Subtype.val ⁻¹' K2u X hb w :
      Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (conjugateLevelSubgroup X hb hK w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eA, Subgroup.closure_eq]
  have eB' : Subgroup.closure (Subtype.val ⁻¹' (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
      Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eB, Subgroup.closure_eq]
  unfold muHf muHfpp idxH
  erw [eA', eB', eA, eB]
  all_goals exact key

theorem haarIdxLoc_of (hO : ParabolicLevelOpenLocal) : HaarIdxLoc := by
  intro D X hb hK hT hL w p
  have hH : ((X.measW w).μSv p.1).IsHaarMeasure := (X.measW_norm w).2.2.2.2.2.2.2.1 p.1
  have := contMul_HAv X p.1
  have := contMul_sub (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))
  haveI : BorelSpace (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have eA : (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := by
    ext x
    show (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 ↔
      (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ conjugateLevelLocal X hb hK w p.1
    rw [← coe_K2vSub X hb hK w p.1]
    rfl
  have eB : (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (((KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) : Set _) := rfl
  have hle : (conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) ≤
      (KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact local_level_le_maximal X hb hK hL w p.1 hx
  have hop := hO X hb hK hT hL w p
  rw [eA] at hop
  have hBor : BorelSpace (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) :=
    Subtype.borelSpace (fun x => x ∈ ((Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) : Subgroup _) :
      Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)))
  have key := toReal_eq_relIndex_mul_of_haar (G := Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))
    (contMul_sub _) hBor
    ((X.measW w).μSv p.1) hH _ _ hle hop
  have eA' : Subgroup.closure (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (conjugateLevelLocal X hb hK w p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eA, Subgroup.closure_eq]
  have eB' : Subgroup.closure (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
      Set (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      (KvSub X p.1).subgroupOf (Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    rw [eB, Subgroup.closure_eq]
  unfold muSv muSvpp idxS
  erw [eA', eB', eA, eB]
  all_goals exact key

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

theorem compK_holds : CompK := by
  intro D X v h hh
  exact (Subgroup.mem_iInf.1 hh) v

theorem compH_holds : CompH := by
  intro D X w v h hh
  unfold Hsub at hh ⊢
  rw [mem_stabT] at hh ⊢
  intro b
  funext i
  have hi := congrFun (hh b) i
  change (∑ j, ((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j *
      inclR (Af X.B.I.F) (tupH (frameOf X w) b j)) = inclR (Af X.B.I.F) (tupH (frameOf X w) b i) at hi
  change (∑ j, ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
      (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h) : GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) i j *
      inclR (Fv X.B.I.F v) (tupH (frameOf X w) b j)) = inclR (Fv X.B.I.F v) (tupH (frameOf X w) b i)

  rw [← tensMap_inclR (E := X.B.I.E) (evalV X.B.I.F v) (tupH (frameOf X w) b i), ← hi, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, tensMap_inclR]
  rfl

section Fin

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem finHA_mul (x y : X.B.I.Gf) : finHA X hb (x * y) = finHA X hb x * finHA X hb y := by
  unfold finHA
  rw [show ((1 : X.B.I.Ginf), x * y) = (1, x) * (1, y) by simp, map_mul, map_mul, Prod.snd_mul]

theorem finHA_one : finHA X hb 1 = 1 := by
  unfold finHA
  rw [show ((1 : X.B.I.Ginf), (1 : X.B.I.Gf)) = 1 from rfl, map_one, map_one, Prod.snd_one]

theorem finHA_inv (x : X.B.I.Gf) : finHA X hb x⁻¹ = (finHA X hb x)⁻¹ := by
  unfold finHA
  rw [show ((1 : X.B.I.Ginf), x⁻¹) = (1, x)⁻¹ by simp, map_inv, map_inv, Prod.snd_inv]

end Fin

theorem k2uGrp_holds : ConjugateLevelIsSubgroup := by
  intro D X hb hK w
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨finHA X hb 1, ⟨1, hK.1, rfl⟩, ?_⟩
    simp only [finHA_one, mul_one, mul_inv_cancel]
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb', rfl⟩, rfl⟩
    refine ⟨finHA X hb (a * b), ⟨a * b, hK.2.1 a ha b hb', rfl⟩, ?_⟩
    simp only [finHA_mul]
    group
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨finHA X hb a⁻¹, ⟨a⁻¹, hK.2.2.1 a ha, rfl⟩, ?_⟩
    simp only [finHA_inv]
    group

end MassDataLevelSSteps
end
end
