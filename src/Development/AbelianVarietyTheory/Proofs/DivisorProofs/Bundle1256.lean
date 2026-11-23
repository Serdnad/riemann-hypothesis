module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrFixFin

variable {F : Type} [Field F] [NumberField F]

theorem nonarch_of_inducing {G S : Type} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    [AddGroup S] [TopologicalSpace S] [IsTopologicalAddGroup S] (f : S →+ G) (hf : Topology.IsInducing f) :
    NonarchimedeanAddGroup S where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean t ht
    exact ⟨V.comap f hf.continuous, fun x hx => hsub (hV hx)⟩

theorem nonarch_pi' {ι : Type} {G : ι → Type} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi I fun i => (K i : AddSubgroup (G i)), isOpen_set_pi hI fun i _ => (K i).isOpen⟩,
      fun x hx => hs fun i hi => hK i (hx i hi)⟩


variable (F) in
theorem nonarch_finAdeles : NonarchimedeanAddGroup (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), NonarchimedeanAddGroup (v.adicCompletionIntegers F) := fun v =>
    nonarch_of_inducing (v.adicCompletionIntegers F).subtype.toAddMonoidHom Topology.IsInducing.subtypeVal
  haveI := nonarch_pi' (G := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ FiniteAdeleRing (𝓞 F) F :=
    { toFun := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact NonarchimedeanAddGroup.nonarchimedean_of_emb f
    (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _))

def transFix {M : Type} [AddCommGroup M] (Φ : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, Φ (x + u) = Φ x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_transFix {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : IsOpen (transFix Φ : Set M) := by
  have h : ∀ᶠ u in nhds (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  have key : ∀ᶠ u in nhds (0 : M), ∀ x, Φ (x + u) = Φ x := by
    filter_upwards [h] with u hu x
    by_cases hx : x ∈ tsupport Φ
    · exact (hu x hx).1
    · by_cases hx' : x + u ∈ tsupport Φ
      · have := (hu _ hx').2
        rw [add_sub_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  exact AddSubgroup.isOpen_of_mem_nhds _ key

theorem adeleJoin_zero {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) (i : κ) :
    GlobalTheory.WeilCont.adeleJoin F 0 y i = ((0 : InfiniteAdeleRing F), y i) := by
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
  exact map_zero _

theorem dot_adeleJoin_zero {κ : Type} [Fintype κ] (v : κ → AdeleRing (𝓞 F) F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    v ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y = ((0 : InfiniteAdeleRing F), (fun i => (v i).2) ⬝ᵥ y) := by
  let p1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have e1 : ∀ s : AdeleRing (𝓞 F) F, s.1 = p1 s := fun _ => rfl
  have e2 : ∀ s : AdeleRing (𝓞 F) F, s.2 = p2 s := fun _ => rfl
  refine Prod.ext ?_ ?_

  · rw [e1, dotProduct, map_sum]
    change (∑ i, p1 (v i * GlobalTheory.WeilCont.adeleJoin F 0 y i)) = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, adeleJoin_zero]
    exact mul_zero _

  · rw [e2, dotProduct, map_sum]
    change (∑ i, p2 (v i * GlobalTheory.WeilCont.adeleJoin F 0 y i)) = _
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, adeleJoin_zero]
    rfl

theorem exists_fix_pure (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (κ : Type) [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) (pureA F f g) =
        pureA F f g := by
  haveI := nonarch_finAdeles F
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hχ : Continuous χ := hψ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨H, hH⟩ := GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact χ hχ κ (tsupport g) hg.2.isCompact
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2
  refine ⟨transFix g ⊓ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)).comap
    (DistribSMul.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c), H, ?_, H.isOpen, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact (isOpen_transFix hg.1 hg.2).inter (H.isOpen.preimage (continuous_const_smul c))
  rintro x ⟨hx1, hx2⟩ y hy
  funext z
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1 := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero]
    exact congrArg _ (add_zero (z i).1)
  have hgz : (fun i => ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).2) = (fun i => (z i).2) + x := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero]
    rfl
  have hz : pureA F f g (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = pureA F f g z := by
    simp only [pureA]
    rw [hf, hgz, hx1]
  simp only [schr]
  rw [hz]
  by_cases hg0 : g (fun i => (z i).2) = 0
  · simp only [pureA, hg0, mul_zero]
  have hzc : (fun i => (z i).2) ∈ tsupport g := subset_tsupport _ hg0
  have harg : z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y + ⅟(2 : AdeleRing (𝓞 F) F) *
      (GlobalTheory.WeilCont.adeleJoin F 0 x ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y) =
      ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) := by
    rw [dot_adeleJoin_zero, dot_adeleJoin_zero, smul_dotProduct]
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing F) + (⅟(2 : AdeleRing (𝓞 F) F)).1 * 0 = 0
      rw [mul_zero, add_zero]
    · show (fun i => (z i).2) ⬝ᵥ y + c * ((fun i => (GlobalTheory.WeilCont.adeleJoin F 0 x i).2) ⬝ᵥ y) = _
      rfl
  rw [harg]
  have h1 : ψ ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) = 1 :=
    hH _ hzc (c • x) hx2 y hy
  rw [h1, one_mul]

theorem exists_fix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) Φ = Φ := by
  intro F _ _ ψ hψ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact exists_fix_pure ψ hψ κ f g hg
  | zero =>
    refine ⟨⊤, ⊤, isOpen_univ, isOpen_univ, fun x _ y _ => ?_⟩
    funext z
    simp [schr]
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h1
    obtain ⟨M₁, M₂, p₁, p₂, h'⟩ := h2
    refine ⟨L₁ ⊓ M₁, L₂ ⊓ M₂, by rw [AddSubgroup.coe_inf]; exact o₁.inter p₁,
      by rw [AddSubgroup.coe_inf]; exact o₂.inter p₂, fun x hx y hy => ?_⟩
    have e1 := h x hx.1 y hy.1
    have e2 := h' x hx.2 y hy.2
    funext z
    have a1 := congrFun e1 z
    have a2 := congrFun e2 z
    simp only [schr, Pi.add_apply] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  | smul a Φ _ h =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h
    refine ⟨L₁, L₂, o₁, o₂, fun x hx y hy => ?_⟩
    funext z
    have a1 := congrFun (h x hx y hy) z
    simp only [schr, Pi.smul_apply, smul_eq_mul] at a1 ⊢
    rw [mul_left_comm, a1]

end GlobalTheory.SchrFixFin

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ArchTransportDir

section Mixed

variable (F : Type) [Field F] [NumberField F]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

def eInf : AF F := (1, 0)

def rInf (t : ℝ) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t), 0)

variable {F} {κ : Type} [Fintype κ]

def archParts (y : (κ → AF F) × (κ → AF F)) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (GlobalTheory.WeilL2Words.archPart F y.1, GlobalTheory.WeilL2Words.archPart F y.2)

local notation "toM" => InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem archimedean_map_add (z z' : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (z + z') = GlobalTheory.WeilL2Words.arch1 F z + GlobalTheory.WeilL2Words.arch1 F z' := by
  show (((toM).symm (z + z'), 0) : AF F) = (((toM).symm z + (toM).symm z', 0 + 0) : AF F)
  rw [map_add (f := _), add_zero]

theorem arch_projection_real_smul (t : ℝ) (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (t • z) = rInf F t * GlobalTheory.WeilL2Words.arch1 F z := by
  show (((toM).symm (t • z), 0) : AF F) = (((toM).symm (algebraMap ℝ _ t) * (toM).symm z, 0 * 0) : AF F)
  rw [Algebra.smul_def, map_mul, mul_zero]

theorem arch_projection_idempotent (z : mixedEmbedding.mixedSpace F) : GlobalTheory.WeilL2Words.arch1 F z = eInf F * GlobalTheory.WeilL2Words.arch1 F z := by
  show (((toM).symm z, 0) : AF F) = ((1 * (toM).symm z, 0 * 0) : AF F)
  rw [one_mul, mul_zero]

theorem toM_add (a b : AF F) : toM (a + b).1 = toM a.1 + toM b.1 := map_add (toM) a.1 b.1

theorem toM_rInf (t : ℝ) (a : AF F) : toM (rInf F t * a).1 = t • toM a.1 := by
  show toM ((toM).symm (algebraMap ℝ _ t) * a.1) = _
  rw [map_mul, RingEquiv.apply_symm_apply, Algebra.smul_def]

theorem arch_projection_to_mixed_space {a : AF F} (ha : eInf F * a = a) : GlobalTheory.WeilL2Words.arch1 F (toM a.1) = a := by
  have h2 : a.2 = 0 := by
    rw [← ha]
    show (0 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0
    exact zero_mul _
  show (((toM).symm (toM a.1), 0) : AF F) = a
  rw [RingEquiv.symm_apply_apply]
  show ((a.1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = a
  exact Prod.ext rfl h2.symm

theorem archPair_add (h h' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    GlobalTheory.WeilL2Words.archPair F (h + h') = GlobalTheory.WeilL2Words.archPair F h + GlobalTheory.WeilL2Words.archPair F h' :=
  Prod.ext (funext fun i => archimedean_map_add (h.1 i) (h'.1 i)) (funext fun i => archimedean_map_add (h.2 i) (h'.2 i))

theorem archPair_smul (t : ℝ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    GlobalTheory.WeilL2Words.archPair F (t • h) = rInf F t • GlobalTheory.WeilL2Words.archPair F h :=
  Prod.ext (funext fun i => arch_projection_real_smul t (h.1 i)) (funext fun i => arch_projection_real_smul t (h.2 i))

theorem archPair_eInf (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    GlobalTheory.WeilL2Words.archPair F h = eInf F • GlobalTheory.WeilL2Words.archPair F h :=
  Prod.ext (funext fun i => arch_projection_idempotent (h.1 i)) (funext fun i => arch_projection_idempotent (h.2 i))

theorem archParts_add (y y' : (κ → AF F) × (κ → AF F)) : archParts (y + y') = archParts y + archParts y' :=
  Prod.ext (funext fun i => toM_add (y.1 i) (y'.1 i)) (funext fun i => toM_add (y.2 i) (y'.2 i))

theorem archParts_smul (t : ℝ) (y : (κ → AF F) × (κ → AF F)) : archParts (rInf F t • y) = t • archParts y :=
  Prod.ext (funext fun i => toM_rInf t (y.1 i)) (funext fun i => toM_rInf t (y.2 i))

theorem archPair_archParts {y : (κ → AF F) × (κ → AF F)} (hy : eInf F • y = y) :
    GlobalTheory.WeilL2Words.archPair F (archParts y) = y :=
  Prod.ext (funext fun i => arch_projection_to_mixed_space (congrFun (congrArg Prod.fst hy) i))
    (funext fun i => arch_projection_to_mixed_space (congrFun (congrArg Prod.snd hy) i))

theorem continuous_archParts : Continuous (archParts (F := F) (κ := κ)) := by
  refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_)
  · exact (continuous_toMixed F).comp (continuous_fst.comp ((continuous_apply i).comp continuous_fst))
  · exact (continuous_toMixed F).comp (continuous_fst.comp ((continuous_apply i).comp continuous_snd))

end Mixed

section Lin

variable {S R' : Type} [CommRing S] [CommRing R'] [Algebra S R'] {α β : Type} [Fintype α] [Fintype β]

def mulMulT (P : Matrix α α R') (Q : Matrix β β R') : Matrix α β R' →ₗ[S] Matrix α β R' where
  toFun x := P * x * Qᵀ
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

end Lin

theorem archDir_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ)
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ p w, ∀ φ ∈ schA F κ, om p (co.rho ψ w φ) = co.rho ψ (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w) (om p φ)) →
    ∃ M : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ p h, ∀ φ ∈ schA F κ,
        om p (schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  intro F E _ _ _ _ _ σ ψ m n JA JB ξ κ _ co om hom
  let L : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →
      ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F)) := fun p =>
    co.e.toLinearMap ∘ₗ mulMulT (S := AF F) (((p⁻¹).1 : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E))
      (((p⁻¹).2 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) ∘ₗ co.e.symm.toLinearMap
  have hL : ∀ p x, L p x = co.e (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ (co.e.symm x)) := fun p x => rfl
  have hfix : ∀ p h, eInf F • L p (GlobalTheory.WeilL2Words.archPair F h) = L p (GlobalTheory.WeilL2Words.archPair F h) := by
    intro p h
    conv_rhs => rw [archPair_eInf h, map_smul]
  have hact : ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) (x : Matrix (Fin m) (Fin n) (AE F E)), actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ x) = x := by
    intro p x
    have h1 : ((p.1 : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)) *
        (((p⁻¹).1 : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)) = 1 := by
      rw [Prod.fst_inv, Subgroup.coe_inv, Units.mul_inv]
    have h2 : (((p⁻¹).2 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ *
        ((p.2 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Prod.snd_inv, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one]
    simp only [actAB, Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨fun p => { toFun := fun h => archParts (L p (GlobalTheory.WeilL2Words.archPair F h)), map_add' := ?_, map_smul' := ?_ },
    ?_, ?_⟩
  · intro h h'
    rw [archPair_add, map_add (f := _), archParts_add]
  · intro t h
    rw [RingHom.id_apply, archPair_smul, map_smul, archParts_smul]
  · intro p h φ hφ
    have key := hom p (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ (co.e.symm (GlobalTheory.WeilL2Words.archPair F h))) φ hφ
    show om p (schr ψ (GlobalTheory.WeilL2Words.archPair F (archParts (L p (GlobalTheory.WeilL2Words.archPair F h)))) φ) = _
    rw [archPair_archParts (hfix p h), hL]
    simp only [Darboux.rho] at key
    rw [hact, LinearEquiv.apply_symm_apply] at key
    exact key
  · intro h
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
    haveI : IsModuleTopology (AF F) (Matrix (Fin m) (Fin n) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin m → Fin n → AE F E))
    have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
    have hP : Continuous fun p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) =>
        (((p⁻¹).1 : GL (Fin m) (AE F E)) : Matrix (Fin m) (Fin m) (AE F E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_inv))
    have hQ : Continuous fun p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) =>
        (((p⁻¹).2 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_inv))
    exact continuous_archParts.comp (hce.comp ((hP.matrix_mul continuous_const).matrix_mul hQ.matrix_transpose))

end GlobalTheory.ArchTransportDir

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.UPel.HT.LiftUniq

theorem eq_of_same_image : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (M' : Model b N') (π : M'.X ⟶ S), π ≫ s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) o π) (T : Scheme.{0}) (g₁ g₂ : T ⟶ M'.X), g₁ ≫ π = g₂ ≫ π → (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ om.φ = g₂ ≫ (M'.univ.eta a).left ≫ om.φ) → g₁ = g₂ := by
  intro p _ D R _ b N N' hd hc S s o M' π hπ om T g₁ g₂ hg hη
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N' M'.X T M'.s g₁ M'.univ
  obtain ⟨ψ, ψ₂, hcart, hsq, hact0, hpol, hη'⟩ : ∃ (ψ : M'.univ.A.left ⟶ o.A.left)
      (ψ₂ : (M'.univ.A ⊗ M'.univ.A).left ⟶ (o.A ⊗ o.A).left), IsGrpPullback M'.univ.A o.A π ψ ∧
      IsSquare ψ ψ₂ ∧ (∀ c, (M'.univ.act.act c).left ≫ ψ = ψ ≫ (o.act.act c).left) ∧
      Nonempty (LBIso M'.univ.P (o.P.pull ψ₂)) ∧
      (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ ψ = g₂ ≫ (M'.univ.eta a).left ≫ ψ) :=
    ⟨om.φ, om.φ₂, om.cart, om.sq, om.act, ⟨om.pol⟩, hη⟩
  obtain ⟨hpol⟩ := hpol
  clear hη
  have hpb : IsPullback ψ M'.univ.A.hom o.A.hom π := hcart.1
  have w : (m₁.φ ≫ ψ) ≫ o.A.hom = (o₁.A.hom ≫ g₂) ≫ π := by
    have h2 : m₁.φ ≫ M'.univ.A.hom = o₁.A.hom ≫ g₁ := m₁.cart.1.w
    rw [Category.assoc, hpb.w, ← Category.assoc, h2, Category.assoc, hg, Category.assoc]
  obtain ⟨φ, hφ, hφ'⟩ : ∃ φ : o₁.A.left ⟶ M'.univ.A.left, φ ≫ ψ = m₁.φ ≫ ψ ∧
      φ ≫ M'.univ.A.hom = o₁.A.hom ≫ g₂ :=
    ⟨hpb.lift _ _ w, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have n : IsGrpPullback o₁.A o.A (g₂ ≫ π) (φ ≫ ψ) := by
    rw [hφ, ← hg]; exact m₁.cart.comp hcart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m₁.φ₂ ≫ ψ₂ = φ₂ ≫ ψ₂ :=
    isSquare_unique (isSquare_comp m₁.sq hsq) (hφ ▸ isSquare_comp sq hsq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (M'.univ.act.act c).left := by
    intro c
    apply hpb.hom_ext
    · rw [Category.assoc, hφ, ← Category.assoc, m₁.act, Category.assoc, hact0, Category.assoc, hact0,
        ← Category.assoc, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = g₂ ≫ (M'.univ.eta y).left := by
    intro y
    apply hpb.hom_ext
    · rw [Category.assoc, hφ, ← Category.assoc, m₁.eta, Category.assoc, Category.assoc]
      exact hη' y
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ g₂ = g₂ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  have pol : LBIso o₁.P (M'.univ.P.pull φ₂) :=
    LBIso.trans o₁.isLB (pull_isLB o.isLB _) (pull_isLB M'.univ.isLB _)
      (LBIso.trans o₁.isLB (pull_isLB M'.univ.isLB _) (pull_isLB o.isLB _) m₁.pol
        (lbIso_pull_comp hpol m₁.φ₂ rfl))
      (LBIso.symm (lbIso_pull_comp hpol φ₂ e))
  let m₂ : ObjMap o₁ M'.univ g₂ :=
    { φ := φ, φ₂ := φ₂, cart := hcart.cancel n hφ', sq := sq, act := hact, pol := pol, eta := heta }
  have h2 : g₂ ≫ M'.s = g₁ ≫ M'.s := by rw [← hπ, ← Category.assoc, ← hg, Category.assoc]
  exact ((M'.rep T (g₁ ≫ M'.s) o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨h2, ⟨m₂⟩⟩)

end GlobalTheory.UPel.HT.LiftUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem _root_.GlobalTheory.T.weilPairing_eq_exp_riemannForm_appellHumbert_frame : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB →
    ∀ (n : ℕ) (u : HolUnif A L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      ∀ (k : ℕ) (a b : Fin n → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm.mulVec (star b)).im : ℝ) : ℂ) / k) →
        Out.WeilIs A L k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  first | exact @GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | exact GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | (intros; apply GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_absFrobenius_apply_F : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt) (l l' : Mod B G h), IsTr B (frobRing (p_eq_zero p k)) h h (absFrob (p_eq_zero p k) G) l l' → ∀ y, l' (B.F G.dual (dual_conn h) y) = p * WittVector.frobenius (l y) := by
  first | exact @GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F | exact GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F | (intros; apply GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F <;> assumption)
end
