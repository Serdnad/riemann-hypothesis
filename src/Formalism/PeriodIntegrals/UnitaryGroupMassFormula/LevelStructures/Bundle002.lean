module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace MassDataLevelSSteps.ProdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes MeasureTheory NumberField
  IsDedekindDomain Topology PI.AdicCompletionValuation
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosed_stabT (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R]
    {a : ℕ} (X0 : Fin a → Fin n → E) :
    IsClosed ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) := by
  have hcont : Continuous fun g : HA R σ J => g • ratTup (F := F) R X0 := by
    show Continuous fun g : HA R σ J => actTup R (HA.mat R σ J g) (ratTup (F := F) R X0)
    unfold actTup HA.mat
    refine continuous_pi fun b => Continuous.matrix_mulVec ?_ continuous_const
    exact Units.continuous_val.comp
      (continuous_subtype_val : Continuous fun g : HR R σ J => (g : GL (Fin n) (R ⊗[F] E)))
  have : ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) =
      {g | g • ratTup (F := F) R X0 = ratTup (F := F) R X0} := by
    ext g
    exact MulAction.mem_stabilizer_iff
  rw [this]
  exact isClosed_eq hcont continuous_const

instance secondCountable_HAf : SecondCountableTopology (HA (Af F) σ J) :=
  PI.VolStabSW.TopoAF.secondCountable_HA_of (Af F) σ J

theorem prodNH_of {r : ℕ} (P : Frame E n r) (M : MeasW σ J P) (hM : M.IsTextNorm) :
    IsProdNH F E σ n J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) M.μSf M.μNf M.μHf := by
  obtain ⟨-, -, hH, -, -, -, -, -, -, -, hS⟩ := hM
  have hcl : IsClosed ((Hsub (Af F) σ J P : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) :=
    isClosed_stabT σ J (Af F) (tupH P)
  have : LocallyCompactSpace (Hsub (Af F) σ J P) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have := hH
  have : SecondCountableTopology (HA (Af F) σ J) := secondCountable_HAf σ J
  have : SecondCountableTopology (Hsub (Af F) σ J P) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : WeaklyLocallyCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : IsFiniteMeasureOnCompacts M.μHf := inferInstance
  have : IsLocallyFiniteMeasure M.μHf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  have : SigmaFinite M.μHf := sigmaFinite_of_locallyFinite
  have : SFinite (amb M.μHf) := inferInstance
  have hmul : Measurable fun p : HA (Af F) σ J × HA (Af F) σ J => p.1 * p.2 := measurable_mul
  intro f hf
  have e1 : ∫⁻ k, f (k : HA (Af F) σ J) ∂M.μSf = ∫⁻ x, f x ∂(amb M.μSf) :=
    (lintegral_map hf measurable_subtype_coe).symm
  rw [e1, hS, lintegral_map hf hmul, lintegral_prod (fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2)) (hf.comp hmul).aemeasurable]
  have hin : Measurable fun x : HA (Af F) σ J => ∫⁻ y, f (x * y) ∂(amb M.μHf) :=
    Measurable.lintegral_prod_right' (f := fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2))
      (hf.comp hmul)
  rw [lintegral_map hin measurable_subtype_coe]
  refine lintegral_congr fun m => ?_
  exact lintegral_map (hf.comp (measurable_const_mul _)) measurable_subtype_coe

end MassDataLevelSSteps.ProdW

namespace MassDataLevelSSteps

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

theorem prodNH_holds : ProdNH := by
  intro D X w
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  exact ProdW.prodNH_of X.B.I.cm.sig X.B.I.J _ (X.measW w) (X.measW_norm w)

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem index_pi_dep {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Group (β i)]
    (C : ∀ i, Subgroup (β i)) : (Subgroup.pi Set.univ C).index = ∏ i, (C i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem index_comap_pi {A : Type*} [Group A] {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Group (β i)]
    (φ : A →* ((i : ι) → β i)) (hφ : Function.Surjective φ) (C : ∀ i, Subgroup (β i)) :
    ((Subgroup.pi Set.univ C).comap φ).index = ∏ i, (C i).index := by
  rw [Subgroup.index_comap_of_surjective _ hφ, index_pi_dep]

theorem closure_val_preimage {G : Type*} [Group G] (H T : Subgroup G) :
    Subgroup.closure (Subtype.val ⁻¹' (T : Set G) : Set H) = T.subgroupOf H :=
  Subgroup.closure_eq (T.subgroupOf H)

def CompH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J), h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈ Hsub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (frameOf X w)

def CompK : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F))
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J),
    h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) →
    haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
      Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v

def ConjugateLevelIsSubgroup : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → ∀ w : D.what₂.Word,
    (1 : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb w ∧
    (∀ x ∈ K2u X hb w, ∀ y ∈ K2u X hb w, x * y ∈ K2u X hb w) ∧ (∀ x ∈ K2u X hb w, x⁻¹ ∈ K2u X hb w)

def SurjKH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word)
    (t : ∀ p : TypX X, HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    (∀ p, t p ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) →
    (∀ p, t p ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1) →
    ∃ h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w),
      h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ∧
      ∀ p, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h = t p

def ConjugateLevelLocalCongruence : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ (w : D.what₂.Word)
    (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J), h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) →
    (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) h ∈
      compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1) → h ∈ K2u X hb w

section Der

variable {D : D7} (X : HidaSetting D)

def KvS (v : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F)) : Subgroup (HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) where
  carrier := Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v
  one_mem' := Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
  mul_mem' := fun {_ _} ha hb => Subgroup.mul_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) ha hb
  inv_mem' := fun {_} ha => Subgroup.inv_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) ha

def concreteLevelAdelicSubset (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hg : ConjugateLevelIsSubgroup) (w : D.what₂.Word) :
    Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) where
  carrier := K2u X hb w
  one_mem' := (hg X hb hK w).1
  mul_mem' := fun {a b} ha hb' => (hg X hb hK w).2.1 a ha b hb'
  inv_mem' := fun {a} ha => (hg X hb hK w).2.2 a ha

def compHom (ha : CompH) (hk : CompK) (w : D.what₂.Word) :
    ↥((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) →*
      ((p : TypX X) → ↥((KvS X p.1).subgroupOf (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))) where
  toFun x := fun p => ⟨⟨haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) x.1.1, ha X w p.1 x.1.1 x.1.2⟩,
    hk X p.1 x.1.1 (Subgroup.mem_subgroupOf.1 x.2)⟩
  map_one' := by
    funext p
    apply Subtype.ext; apply Subtype.ext
    exact map_one _
  map_mul' := by
    intro x y
    funext p
    apply Subtype.ext; apply Subtype.ext
    exact map_mul _ _ _

end Der

theorem globProd_of (ha : CompH) (hk : CompK) (hg : ConjugateLevelIsSubgroup) (hs : SurjKH) (hp : ConjugateLevelLocalCongruence) : GlobProd := by
  intro D X hb hK hT hL w
  classical
  have e1 : idxH X hb w = (((concreteLevelAdelicSubset X hb hK hg w).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))).subgroupOf
      ((Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).subgroupOf
        (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w)))).index := by
    unfold idxH
    rw [show (Subtype.val ⁻¹' K2u X hb w : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      Subtype.val ⁻¹' ((concreteLevelAdelicSubset X hb hK hg w : Subgroup _) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) from rfl,
      closure_val_preimage, closure_val_preimage]
    rfl
  have e2 : ∀ p : TypX X, idxHp X hb w p =
      ((((concreteLevelAdelicSubset X hb hK hg w).map (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1))).subgroupOf
        (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))).subgroupOf
        ((KvS X p.1).subgroupOf (Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)))).index := by
    intro p
    unfold idxHp
    rw [show (Subtype.val ⁻¹' compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 :
        Set ↥(Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      Subtype.val ⁻¹' ((((concreteLevelAdelicSubset X hb hK hg w).map (haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1))) :
        Subgroup _) : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) from by
          rw [Subgroup.coe_map]; rfl,
      show (Subtype.val ⁻¹' Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 :
        Set ↥(Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w))) =
      Subtype.val ⁻¹' ((KvS X p.1 : Subgroup _) : Set (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J)) from rfl,
      closure_val_preimage, closure_val_preimage]
    rfl
  rw [e1, Finset.prod_congr rfl (fun p _ => e2 p), ← index_comap_pi (compHom X ha hk w)]
  · congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx p
      exact ⟨x.1.1, hx, rfl⟩
    · intro hx
      exact hp X hb hK hL w x.1.1 x.1.2 (Subgroup.mem_subgroupOf.1 x.2) (fun p => hx p)
  · intro y
    obtain ⟨h, hH, hKf, hh⟩ := hs X w (fun p => (y p).1.1) (fun p => (y p).1.2) (fun p => (y p).2)
    refine ⟨⟨⟨h, hH⟩, Subgroup.mem_subgroupOf.2 hKf⟩, ?_⟩
    funext p
    apply Subtype.ext; apply Subtype.ext
    exact hh p

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

theorem globFromParts_holds : GlobFromParts := by
  intro hLS h1 h2 h3 h4 D X hb _ _ w
  obtain ⟨hCM, hJ⟩ := h1 X
  obtain ⟨T, hT⟩ := h2 X w
  obtain ⟨ΛX, ΛW, ΛY, hA, hK⟩ := h3 X w
  obtain ⟨-, -, hHf, -, -, hNf, hSf, -⟩ := X.measW_norm w
  have key := (hLS X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hJ hJ D.R.rS (frameOf X w) T hT
    ΛX ΛW ΛY hA (X.measW w).μNf hNf (X.measW w).μHf hHf).2 (X.measW w).μSf ⟨hSf, h4 X w⟩
  simp only [KS, NO, KH, Subgroup.mem_inf, hK, SetLike.coe_mem, true_and] at key
  unfold muSf muNf muHf
  rw [← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal key

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem relIndex_eq_of_le_of_dec {G : Type*} [Group G] (U A B : Subgroup G) (hBA : B ≤ A)
    (hdec : ∀ a ∈ A, ∃ u ∈ U, ∃ b ∈ B, a = u * b) : U.relIndex A = U.relIndex B := by
  unfold Subgroup.relIndex
  rw [Subgroup.index, Subgroup.index]
  symm
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' (Subgroup.inclusion hBA) ?_) ⟨?_, ?_⟩)
  · intro x y h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · intro p q h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h' : (QuotientGroup.mk (Subgroup.inclusion hBA x) : A ⧸ U.subgroupOf A) =
        QuotientGroup.mk (Subgroup.inclusion hBA y) := h
    rw [QuotientGroup.eq] at h' ⊢
    simpa [Subgroup.mem_subgroupOf] using h'
  · intro p
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨u, hu, b, hb, hab⟩ := hdec (a : G)⁻¹ (A.inv_mem a.2)
    refine ⟨QuotientGroup.mk ⟨b⁻¹, B.inv_mem hb⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hBA ⟨b⁻¹, B.inv_mem hb⟩) : A ⧸ U.subgroupOf A) = QuotientGroup.mk a
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have ha : (a : G) = b⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← hab, inv_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, inv_inv]
    rw [ha, ← mul_assoc, mul_inv_cancel, one_mul]
    exact U.inv_mem hu

theorem closure_val_preimage_eq_subgroupOf {G : Type*} [Group G] (S V : Subgroup G) :
    Subgroup.closure (Subtype.val ⁻¹' (V : Set G) : Set S) = V.subgroupOf S := by
  rw [show (Subtype.val ⁻¹' (V : Set G) : Set S) = (V.subgroupOf S : Set S) from
    (Subgroup.coe_subgroupOf V S).symm, Subgroup.closure_eq]

theorem relIndex_traces {G : Type*} [Group G] (S U K : Subgroup G) :
    (Subgroup.closure (Subtype.val ⁻¹' (U : Set G) : Set S)).relIndex
      (Subgroup.closure (Subtype.val ⁻¹' (K : Set G) : Set S)) = U.relIndex (K ⊓ S) := by
  rw [closure_val_preimage_eq_subgroupOf, closure_val_preimage_eq_subgroupOf, ← Subgroup.inf_subgroupOf_right K S,
    Subgroup.relIndex_subgroupOf inf_le_right]

theorem Hsub_le_Ssub {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) :
    Hsub R σ J P ≤ Ssub R σ J P := by
  intro g hg
  rw [Hsub, mem_stabT] at hg
  show UniC R σ J (F0 P) g
  intro b
  have h := hg (Fin.castAdd r b)
  simp only [tupH, Fin.append_left] at h
  rw [h, sub_self]
  exact Submodule.zero_mem _

variable {D : D7}

def KvSubT (X : HidaSetting D) (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) where
  carrier := Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1
  one_mem' := (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).one_mem
  mul_mem' := fun ha hb => (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).mul_mem ha hb
  inv_mem' := fun ha => (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).inv_mem ha

theorem finiteAdelic_map_mul (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x y : X.B.I.Gf) :
    finHA X hb (x * y) = finHA X hb x * finHA X hb y := by
  unfold finHA
  rw [show ((1 : _), x * y) = ((1, x) * (1, y) : X.B.I.GA) from by simp, map_mul, map_mul, Prod.snd_mul]

theorem finiteAdelic_map_inv (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x⁻¹ = (finHA X hb x)⁻¹ := by
  unfold finHA
  rw [show ((1 : _), x⁻¹) = ((1, x)⁻¹ : X.B.I.GA) from by simp, map_inv, map_inv, Prod.snd_inv]

theorem finiteAdelic_map_one (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : finHA X hb 1 = 1 := by
  unfold finHA
  rw [show ((1 : _), (1 : X.B.I.Gf)) = (1 : X.B.I.GA) from rfl, map_one, map_one, Prod.snd_one]

theorem mem_local_component_iff (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X)
    (z : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :
    z ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 ↔
      ∃ k ∈ X.K2, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1)
        (finHA X hb (X.xu w) * finHA X hb k * (finHA X hb (X.xu w))⁻¹) = z := by
  simp only [compSet, K2u, levelUnitary, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨y', ⟨k, hk, rfl⟩, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, rfl⟩

def conjugateLevelLocalSubgroup (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) (p : TypX X) :
    Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) where
  carrier := compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1
  one_mem' := by
    refine (mem_local_component_iff X hb w p _).2 ⟨1, hK.1, ?_⟩
    rw [finiteAdelic_map_one, mul_one, mul_inv_cancel, map_one]
  mul_mem' := by
    intro a b ha hb'
    obtain ⟨k1, hk1, e1⟩ := (mem_local_component_iff X hb w p _).1 ha
    obtain ⟨k2, hk2, e2⟩ := (mem_local_component_iff X hb w p _).1 hb'
    refine (mem_local_component_iff X hb w p _).2 ⟨k1 * k2, hK.2.1 _ hk1 _ hk2, ?_⟩
    rw [← e1, ← e2, ← map_mul, finiteAdelic_map_mul]
    congr 1
    group
  inv_mem' := by
    intro a ha
    obtain ⟨k1, hk1, e1⟩ := (mem_local_component_iff X hb w p _).1 ha
    refine (mem_local_component_iff X hb w p _).2 ⟨k1⁻¹, hK.2.2.1 _ hk1, ?_⟩
    rw [← e1, ← map_inv, finiteAdelic_map_inv]
    congr 1
    group

def LeviRat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) (s : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    s ∈ Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    ∃ n h, n ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧
      h ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧ s = n * h

def LeviIntH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) (n h : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    n ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    h ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    n * h ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 →
    h ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1

def UnipotentIntegralInLevel : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X) (n : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
      n ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
      n ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 →
      n ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1

theorem locLevi_of (ha : LeviRat) (hbI : LeviIntH) (hc : UnipotentIntegralInLevel) : LocLevi := by
  intro D X hb hK hM hL w p
  have e1 : idxS X hb w p = (conjugateLevelLocalSubgroup X hb hK w p).relIndex
      (KvSubT X p ⊓ Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    unfold idxS
    exact relIndex_traces _ (conjugateLevelLocalSubgroup X hb hK w p) (KvSubT X p)
  have e2 : idxHp X hb w p = (conjugateLevelLocalSubgroup X hb hK w p).relIndex
      (KvSubT X p ⊓ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    unfold idxHp
    exact relIndex_traces _ (conjugateLevelLocalSubgroup X hb hK w p) (KvSubT X p)
  rw [e1, e2]
  apply relIndex_eq_of_le_of_dec
  · exact inf_le_inf_left _ (Hsub_le_Ssub _ _ _ _)
  · rintro a ⟨haK, haS⟩
    obtain ⟨n, h, hn, hh, rfl⟩ := ha X w p a haS
    have hhK := hbI X w p n h hn hh haK
    have hnK : n ∈ KvSubT X p := by
      have e : n = (n * h) * h⁻¹ := by group
      rw [e]
      exact (KvSubT X p).mul_mem haK ((KvSubT X p).inv_mem hhK)
    exact ⟨n, hc X hb hK hM hL w p n hn hnK, h, ⟨hhK, hh⟩, rfl⟩

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem cmInst_holds : CMInst := by
  intro D X
  refine ⟨⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩,
    fun i j => ?_, X.B.I.J_det⟩
  have h := congrFun (congrFun X.B.I.J_herm i) j
  have h' : (starRingEnd X.B.I.E) (X.B.I.J j i) = X.B.I.J i j := by simpa [Formalism.UG.cT] using h
  exact h'

end MassDataLevelSSteps
end
end

section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

theorem inLevelSAt_of_parts (hLS : LevelSAll) (a1 : KSpCompact) (a2 : KSpOpen) (b1 : CMInst) (b2 : FrameStd)
    (b3 : LatAdapted) (b4 : ProdNH) (b5 : GlobFromParts) (c1 : HaarIdxLoc) (c2 : HaarIdxGlob) (c3 : LocLevi)
    (c4 : GlobProd) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of (typedNe_of a1 a2) (b5 hLS b1 b2 b3 b4) (ratioH_of c1 c2 c3 c4)

end MassDataLevelSSteps
end
end
