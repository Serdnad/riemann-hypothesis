module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uLeKfHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
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

@[expose] public section

section

noncomputable section

namespace MassDataLevelSSteps.FrameW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem host_star_conj : Formalism.BasicNotions.bridge_star := by
  apply Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.host_star_conj <;> assumption

theorem sig_apply {D : D7} (X : HidaSetting D) (a : X.B.I.E) : X.B.I.cm.sig a = star a := rfl

theorem hE_crdOf {D : D7} (X : HidaSetting D) (x y : (VS D).V) :
    hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas x) (crdOf X.B.I X.ιE X.bas y) =
      X.ιE.symm ((VS D).hT x y) := by
  apply Formalism.L2.SG.Pf.NcVal.OmVSt.OmW.hE_crdOf <;> assumption

theorem frameOf_isStd {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) := by
  refine ⟨fun a b => (hE_crdOf X (X.eX a) (X.eX b)).trans ?_,
    fun a b => (hE_crdOf X (X.fY a) (X.fY b)).trans ?_,
    fun a b => (hE_crdOf X (X.eX a) (X.fY b)).trans ?_,
    fun a => (hE_crdOf X (X.eX a) (X.zu u)).trans ?_,
    fun a => (hE_crdOf X (X.fY a) (X.zu u)).trans ?_,
    (hE_crdOf X (X.zu u) (X.zu u)).trans ?_, ?_⟩
  · rw [X.ee, map_zero]
  · rw [X.ff, map_zero]
  · rw [X.ef]
    split_ifs <;> simp
  · rw [(X.zu_orth u a).1, map_zero]
  · rw [(X.zu_orth u a).2, map_zero]
  · rw [X.zu_norm]
    simp
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact (D.mem u).A.T_prime.ne_zero

end MassDataLevelSSteps.FrameW

namespace MassDataLevelSSteps

theorem frameStd_holds : FrameStd := by
  intro D X w
  exact ⟨_, FrameW.frameOf_isStd X w⟩

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def GlueHA : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (t : ∀ p : TypX X, HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    ∃ h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J,
      (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h = t p) ∧
      ∀ v, v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1) →
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h = 1

def TensInj : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (x y : Af X.B.I.F ⊗[X.B.I.F] X.B.I.E),
    (∀ v : HeightOneSpectrum (𝓞 X.B.I.F), tensMap (E := X.B.I.E) (evalV X.B.I.F v) x =
      tensMap (E := X.B.I.E) (evalV X.B.I.F v) y) → x = y

def LevelCongruenceLocal : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ κ : X.B.I.Gf,
    κ ∈ X.B.I.Kset → (∀ p : TypX X, ∃ κ' ∈ X.K2,
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) =
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ')) → κ ∈ X.K2

theorem tens_lin {D : D7} (X : HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) (x : Fin X.B.I.n → X.B.I.E) (i : Fin X.B.I.n) :
    tensMap (E := X.B.I.E) (evalV X.B.I.F v) (lin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h
      (ratV (Af X.B.I.F) x) i) =
    lin (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h)
      (ratV (Fv X.B.I.F v) x) i := by
  change tensMap (E := X.B.I.E) (evalV X.B.I.F v) (∑ j, ((HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J h :
      GL (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j * inclR (Af X.B.I.F) (x j)) =
    ∑ j, ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
      (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h) : GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) i j * inclR (Fv X.B.I.F v) (x j)

  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, tensMap_inclR]
  rfl

theorem surjKH_of (hg : GlueHA) (hi : TensInj) : SurjKH := by
  intro D X w t htH htK
  classical
  obtain ⟨h, hT, hO⟩ := hg X t
  have hloc : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v := by
    intro v
    by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
    · have e := hT ⟨v, hv⟩
      simp only at e
      rw [e]
      exact ⟨htH ⟨v, hv⟩, htK ⟨v, hv⟩⟩
    · rw [hO v hv]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))⟩
  refine ⟨h, ?_, ?_, hT⟩
  · unfold Hsub
    rw [mem_stabT]
    intro b
    funext i
    apply hi X
    intro v
    rw [tens_lin X v h]
    have hv := (hloc v).1
    unfold Hsub at hv
    rw [mem_stabT] at hv
    rw [hv b]
    simp only [ratV, tensMap_inclR]
  · exact Subgroup.mem_iInf.2 fun v => (hloc v).2

theorem conjugate_level_congruence_of (hl : LevelCongruenceLocal) : ConjugateLevelLocalCongruence := by
  intro D X hb hK hL w h _ hKf hp
  have hc : finHA X hb (X.xu w) ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    finHA_mem_Kf X hb (X.xu w) (X.xu_K w)
  obtain ⟨κ, hκ⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb
    ((finHA X hb (X.xu w))⁻¹ * h * finHA X hb (X.xu w))
  have hκf : finHA X hb κ = (finHA X hb (X.xu w))⁻¹ * h * finHA X hb (X.xu w) := hκ
  have hκK : κ ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb κ).1 ?_
    change finHA X hb κ ∈ _
    rw [hκf]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hKf) hc
  have hmem : κ ∈ X.K2 := by
    refine hl X hb hK hL κ hκK (fun p => ?_)
    obtain ⟨y, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, hy⟩ := hp p
    refine ⟨k, hk, ?_⟩
    rw [hκf]
    simp only [map_mul, map_inv] at hy ⊢
    rw [← hy]
    group
  exact ⟨finHA X hb κ, ⟨κ, hmem, rfl⟩, by rw [hκf]; group⟩

theorem global_product_of_local (hg : GlueHA) (hi : TensInj) (hl : LevelCongruenceLocal) : GlobProd :=
  globProd_of compH_holds compK_holds k2uGrp_holds (surjKH_of hg hi) (conjugate_level_congruence_of hl)

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge PI.MassDataKppVolLemmas
open Formalism.MainNotions.S (AutInst)
open scoped TensorProduct

def FinProjOpen : Prop :=
  ∀ I : AutInst, IsOpenMap (fun h : HAd I => (splitA I.cm.sig I.J h).2)

theorem finPart_inf_one (I : AutInst) (hb : AdBridgeIso I) (s : I.Ginf) :
    (splitA I.cm.sig I.J (toHA I hb (s, 1))).2 = 1 := by
  apply Bridge_HA_ext
  have hB : I.fmat 1 = ofHAFin I (toHA I hb (s, 1)) := (toHA_isBridge I hb (s, 1)).2
  have hm : ((HA.mat (Af I.F) I.cm.sig I.J ((splitA I.cm.sig I.J (toHA I hb (s, 1))).2) :
      GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _) =
      (ofHAFin I (toHA I hb (s, 1))).map (swapE I) := by
    ext i j
    simp only [ofHAFin, Matrix.map_apply]
    rw [← Bridge_tens_eq]
    rfl
  rw [hm, ← hB]
  have h1 : I.fmat 1 = 1 := rfl
  rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem finPart_eq (I : AutInst) (hb : AdBridgeIso I) (s : I.Ginf) (x : I.Gf) :
    (splitA I.cm.sig I.J (toHA I hb (s, x))).2 = tf I hb x := by
  unfold tf
  rw [show ((s, x) : I.GA) = (s, 1) * (1, x) by ext <;> simp, map_mul, map_mul, Prod.snd_mul,
    finPart_inf_one I hb s, one_mul]

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, by simp [Formalism.MainNotions.S.AutInst.fmat]⟩⟩
  show _ ∈ Formalism.UG.stabGL I.Lf
  simpa using one_mem (Formalism.UG.stabGL I.Lf)

theorem level_subgroup_isOpen {D : D7} (X : HidaSetting D) (hL : X.LevelSubgroupNormalized) (hK : X.LevelSubgroupCharacter) :
    IsOpen (X.K2 : Set X.B.I.Gf) := by
  have hg1 : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hKg : IsOpen (X.B.I.Kg X.B.g : Set X.B.I.Gf) := X.B.I.topf_open X.B.g hg1
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (X.B.I.Kg X.B.g : Set X.B.I.Gf)) :=
    hKg.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using one_mem_Kg X.B.I X.B.g)) ?_
  intro y hy
  have h2 := hK.2.1 x hx _ (hL.1 _ hy).1
  simpa using h2

theorem conjugate_level_isOpen (hP : FinProjOpen) {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)
    (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    IsOpen (K2u X hb w) := by
  set a := X.xu w
  have hU : IsOpen ((fun y => a * y * a⁻¹) '' X.K2) := by
    have e : (fun y => a * y * a⁻¹) '' X.K2 = (fun y => a⁻¹ * y * a) ⁻¹' X.K2 := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [mul_assoc] using hk
      · intro hy
        exact ⟨a⁻¹ * y * a, hy, by group⟩
    rw [e]
    exact (level_subgroup_isOpen X hL hK).preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hW : IsOpen ((toHA X.B.I hb) '' (Set.univ ×ˢ ((fun y => a * y * a⁻¹) '' X.K2))) :=
    (toHA X.B.I hb).toHomeomorph.isOpenMap _ (isOpen_univ.prod hU)
  have e : K2u X hb w = (fun h : HAd X.B.I => (splitA X.B.I.cm.sig X.B.I.J h).2) ''
      ((toHA X.B.I hb) '' (Set.univ ×ˢ ((fun y => a * y * a⁻¹) '' X.K2))) := by
    have hom : ∀ k, tf X.B.I hb (a * k * a⁻¹) = finHA X hb a * finHA X hb k * (finHA X hb a)⁻¹ := by
      intro k
      show tfHom X.B.I hb (a * k * a⁻¹) = tfHom X.B.I hb a * tfHom X.B.I hb k * (tfHom X.B.I hb a)⁻¹
      rw [map_mul, map_mul, map_inv]
    ext h
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨toHA X.B.I hb (1, a * k * a⁻¹), ⟨(1, a * k * a⁻¹), ⟨trivial, k, hk, rfl⟩, rfl⟩, ?_⟩
      show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, a * k * a⁻¹))).2 = _
      rw [finPart_eq, hom]
    · rintro ⟨_, ⟨⟨s, x⟩, ⟨-, k, hk, rfl⟩, rfl⟩, rfl⟩
      show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, a * k * a⁻¹))).2 ∈ K2u X hb w
      rw [finPart_eq, hom]
      exact ⟨finHA X hb k, ⟨k, hk, rfl⟩, rfl⟩
  rw [e]
  exact hP X.B.I _ hW

theorem k2uOpenH_of (hP : FinProjOpen) : ConjugateLevelOpenUnitary := by
  unfold ConjugateLevelOpenUnitary
  intro D X hb hK _ hL w
  exact (conjugate_level_isOpen hP X hb hK hL w).preimage continuous_subtype_val

theorem haarIdxGlob_of_finProj (hP : FinProjOpen) : HaarIdxGlob :=
  haarIdxGlob_of (k2uOpenH_of hP)

def EvalVOpen : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsOpenMap (haMap I.cm.sig I.J (evalV I.F v))

theorem k2vOpenS_of (hP : FinProjOpen) (hE : EvalVOpen) : ParabolicLevelOpenLocal := by
  intro D X hb hK _ hL w p
  exact ((hE X.B.I p.1) _ (conjugate_level_isOpen hP X hb hK hL w)).preimage continuous_subtype_val

theorem haarIdxLoc_of_open (hP : FinProjOpen) (hE : EvalVOpen) : HaarIdxLoc :=
  haarIdxLoc_of (k2vOpenS_of hP hE)

end MassDataLevelSSteps
end
end
