module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle497
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle498
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle940
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PolOfFnOfOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle499
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.CellLevels

variable {D : D7}

private theorem congGrp_mono' (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  unfold congGrp at hg ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  rw [← Ideal.Quotient.factor_comp_mk h, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hg, map_one]

private theorem idAt_mono_decorated_lattice {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' := by
  intro x hx
  unfold idAt at hx ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

theorem grpAt_le_of_imp (V : HSp D) {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : grpAt V P ≤ grpAt V P' := by
  unfold grpAt
  exact congGrp_mono' V (idAt_mono_decorated_lattice h)

def commProd {G : Type*} [Group G] (A B : Subgroup G) (h : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) : Subgroup G where
  carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    rw [mul_assoc, ← mul_assoc b, h b hb a' ha']; simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by rw [_root_.mul_inv_rev, h _ (B.inv_mem hb) _ (A.inv_mem ha)]⟩

private theorem idAt_inf_le_idAt_and (P P' : Pl D → Prop) : idAt D P ⊓ idAt D P' ≤ idAt D (fun p => P p ∧ P' p) := by
  intro x hxx
  have hx := (Ideal.mem_inf.1 hxx).1
  have hx' := (Ideal.mem_inf.1 hxx).2
  unfold idAt at hx hx' ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx hx' ⊢
  refine ⟨hx.1, fun w => ?_⟩
  by_cases hp : P w.1
  · exact hx'.2 ⟨w.1, fun h' => w.2 ⟨hp, h'⟩⟩
  · exact hx.2 ⟨w.1, hp⟩

private theorem congGrp_inf_le_congGrp_inf (V : HSp D) (I J : Ideal (AE D)) : congGrp V I ⊓ congGrp V J ≤ congGrp V (I ⊓ J) := by
  intro g hg
  have hI := (Subgroup.mem_inf.1 hg).1
  have hJ := (Subgroup.mem_inf.1 hg).2
  unfold congGrp at hI hJ ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hI hJ ⊢
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have eI := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hI i j
  have eJ := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hJ i j
  simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply] at eI eJ ⊢
  split_ifs at eI eJ ⊢ with hij
  · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩

private theorem mem_grpAt_and_of_mem_grpAt (V : HSp D) {P P' : Pl D → Prop} {g : GA D V} (h : g ∈ grpAt V P) (h' : g ∈ grpAt V P') :
    g ∈ grpAt V (fun p => P p ∧ P' p) := by
  unfold grpAt at h h' ⊢
  exact congGrp_mono' V (idAt_inf_le_idAt_and P P') (congGrp_inf_le_congGrp_inf V _ _ ⟨h, h'⟩)

private theorem inK_congr_of_iff {V : HSp D} {L : Lat V} {P P' : Pl D → Prop} (h : ∀ p, P p ↔ P' p) (κ : GA D V) :
    InK V L P κ ↔ InK V L P' κ := by
  rw [show P = P' from funext fun p => propext (h p)]

private theorem mem_grpAt_of_inK {V : HSp D} {L : Lat V} {P : Pl D → Prop} {κ : GA D V} (h : InK V L P κ) : κ ∈ grpAt V P := by
  unfold InK at h
  exact h.1

theorem levels : ∀ (D : D7) (V : HSp D) (L : Lat V) (gP Q : Finset (Pl D)) (JG : Subgroup (GA D V)), IsSelfDualC V L → Disjoint Q gP → JG ≤ grpAt V (· ∈ gP) → IsCompact (JG : Set (GA D V)) → IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) → ∃ K₁ K₂ : Subgroup (GA D V), (∀ g, g ∈ K₁ ↔ InK V L (· ∈ Q) g) ∧ K₁ ≤ grpAt V (· ∈ Q) ∧ K₂ ≤ grpAt V (· ∉ Q) ∧ IsCompact (K₁ : Set (GA D V)) ∧ IsCompact (K₂ : Set (GA D V)) ∧ IsOpen ((K₁.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) ∧ IsOpen ((K₂.subgroupOf (grpAt V (· ∉ Q)) : Subgroup _) : Set (grpAt V (· ∉ Q))) ∧ (∀ g, g ∈ K₂ ↔ ∃ κ, InK V L (fun p => p ∉ gP ∧ p ∉ Q) κ ∧ ∃ k ∈ JG, g = κ * k) ∧ ∀ g, (∃ a ∈ K₁, ∃ b ∈ K₂, g = a * b) ↔ ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g = κ * k := by
  intro D V L gP Q JG hL hdisj hJle hJc hJo
  obtain ⟨-, -, -, hQcle, -, -, -, -, hKQ, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V Q
  obtain ⟨-, -, -, -, hPcomm, ⟨e, he⟩, -, -, -, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V gP
  have hQP : ∀ p, p ∈ Q → p ∉ gP := fun p hp => Finset.disjoint_left.mp hdisj hp

  obtain ⟨⟨K₁, hK₁, hK₁c, hK₁o⟩, -⟩ := hKQ L hL (· ∈ Q)

  obtain ⟨⟨K₃, hK₃, hK₃c, hK₃o⟩, -⟩ := hKQ L hL (fun p => p ∉ gP ∧ p ∉ Q)
  have hpq : ∀ p, (p ∉ gP ∧ p ∈ Q) ↔ p ∈ Q := fun p => ⟨And.right, fun h => ⟨hQP p h, h⟩⟩

  have hsplit : ∀ κ, InK V L (· ∉ gP) κ ↔
      ∃ a b, InK V L (· ∈ Q) a ∧ InK V L (fun p => p ∉ gP ∧ p ∉ Q) b ∧ κ = a * b := by
    intro κ
    refine ((hKQ L hL (· ∉ gP)).2 κ).trans ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).1 ha, hb, rfl⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).2 ha, hb, rfl⟩
  have hK₁le : K₁ ≤ grpAt V (· ∈ Q) := fun g hg => mem_grpAt_of_inK ((hK₁ g).1 hg)
  have hK₃le : K₃ ≤ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := fun g hg => mem_grpAt_of_inK ((hK₃ g).1 hg)
  have hJQ : grpAt V (· ∈ gP) ≤ grpAt V (· ∉ Q) := grpAt_le_of_imp V fun p hp hq => hQP p hq hp

  have hc : ∀ b ∈ JG, ∀ a ∈ K₃, b * a = a * b := fun b hb a ha =>
    hPcomm b (hJle hb) a (grpAt_le_of_imp V (fun p hp => hp.1) (hK₃le ha))
  have hmem : ∀ g, g ∈ commProd K₃ JG hc ↔ ∃ a ∈ K₃, ∃ b ∈ JG, g = a * b := fun g => Iff.rfl
  refine ⟨K₁, commProd K₃ JG hc, hK₁, hK₁le, ?_, hK₁c, ?_, hK₁o, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (hmem g).1 hg
    exact mul_mem (grpAt_le_of_imp V (fun p hp => hp.2) (hK₃le ha)) (hJQ (hJle hb))
  · have hset : (commProd K₃ JG hc : Set (GA D V)) =
        (fun p : GA D V × GA D V => p.1 * p.2) '' ((K₃ : Set (GA D V)) ×ˢ (JG : Set (GA D V))) := by
      ext g
      rw [SetLike.mem_coe, hmem, Set.mem_image]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [hset]
    exact (hK₃c.prod hJc).image continuous_mul
  ·
    obtain ⟨φ, hφc, hφ, hφ1⟩ : ∃ φ : grpAt V (· ∉ Q) → grpAt V (· ∈ gP) × grpAt V (· ∉ gP),
        Continuous φ ∧ (∀ g : grpAt V (· ∉ Q), (g : GA D V) = ((φ g).1 : GA D V) * (φ g).2) ∧ φ 1 = 1 := by
      refine ⟨fun g => e.symm ⟨g, hQcle g.2⟩, ?_, ?_, ?_⟩
      · exact e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
      · intro g
        rw [← he, Homeomorph.apply_symm_apply]
      · rw [Homeomorph.symm_apply_eq]
        apply Subtype.ext
        rw [he]
        simp

    have h3 : ∀ g : grpAt V (· ∉ Q), ((φ g).2 : GA D V) ∈ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := by
      intro g
      have e2 : ((φ g).2 : GA D V) = ((φ g).1 : GA D V)⁻¹ * g := by
        rw [hφ g, inv_mul_cancel_left]
      refine mem_grpAt_and_of_mem_grpAt V (φ g).2.2 ?_
      rw [e2]
      exact mul_mem (inv_mem (hJQ (φ g).1.2)) g.2
    obtain ⟨ψ, hψc, hψ⟩ : ∃ ψ : grpAt V (· ∉ Q) → grpAt V (fun p => p ∉ gP ∧ p ∉ Q),
        Continuous ψ ∧ ∀ g : grpAt V (· ∉ Q), (ψ g : GA D V) = (φ g).2 :=
      ⟨fun g => ⟨(φ g).2, h3 g⟩, (continuous_subtype_val.comp (continuous_snd.comp hφc)).subtype_mk _, fun _ => rfl⟩
    apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    have hU : ψ ⁻¹' ((K₃.subgroupOf (grpAt V (fun p => p ∉ gP ∧ p ∉ Q)) : Subgroup _) :
        Set (grpAt V (fun p => p ∉ gP ∧ p ∉ Q))) ∩
        (fun g => (φ g).1) ⁻¹' ((JG.subgroupOf (grpAt V (· ∈ gP)) : Subgroup _) : Set (grpAt V (· ∈ gP))) ∈
        nhds (1 : grpAt V (· ∉ Q)) := by
      refine IsOpen.mem_nhds ((hK₃o.preimage hψc).inter (hJo.preimage (continuous_fst.comp hφc))) ⟨?_, ?_⟩
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ, hφ1]
        exact K₃.one_mem
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hφ1]
        exact JG.one_mem
    refine Filter.mem_of_superset hU ?_
    rintro g ⟨h1, h2⟩
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ] at h1
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf] at h2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmem]
    refine ⟨(φ g).2, h1, (φ g).1, h2, ?_⟩
    rw [hφ g]
    exact hPcomm _ (φ g).1.2 _ (φ g).2.2
  · intro g
    rw [hmem]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, (hK₃ a).1 ha, b, hb, rfl⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      exact ⟨κ, (hK₃ κ).2 hκ, k, hk, rfl⟩
  · intro g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨κ, hκ, k, hk, rfl⟩ := (hmem b).1 hb
      exact ⟨a * κ, (hsplit _).2 ⟨a, κ, (hK₁ a).1 ha, (hK₃ κ).1 hκ, rfl⟩, k, hk, (mul_assoc a κ k).symm⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := (hsplit κ).1 hκ
      exact ⟨a, (hK₁ a).2 ha, b * k, (hmem _).2 ⟨b, (hK₃ b).2 hb, k, hk, rfl⟩, mul_assoc a b k⟩

end GlobalTheory.CellLevels
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.InvLat

open GlobalTheory.FinPl.SuppShift

variable {D : D7}

theorem single_mul_mul_single {ρ : ℕ} (M : Mx D ρ ρ) (i : Fin ρ) :
    (Matrix.single i i 1 : Mx D ρ ρ) ⬝ (M ⬝ (Matrix.single i i 1 : Mx D ρ ρ)) = Matrix.single i i (M i i) := by
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single, one_mul, mul_one]

theorem pairS_single {W W₀ : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (i : Fin ρ) (c : AE D) (x : Mx D W.rank ρ) :
    pairS W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) x = cA D ((dW.pY ⬝ x) i i) * c := by
  have h : adj (dW.pY ⬝ x) = adj x ⬝ (gA W ⬝ dW.jX) := by
    rw [dW.pY_eq, adj_mul, adj_mul, adj_adj, adj_gA]
  rw [pairS, ← Matrix.mul_assoc (gA W), ← Matrix.mul_assoc, ← h, Matrix.trace_mul_single, op_smul_eq_mul]
  rfl



theorem int_of_psi_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i : Fin ρ) (c : AE D), c - 1 ∈ idAt D (· = v) → (∀ b ∈ idAt D (· = v), dV.extY W (dW.jY ⬝ Matrix.single i i b) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) → ψ (symplO V W (dV.extX W (dW.jX ⬝ Matrix.single i i c)) (dV.extY W (dW.jY ⬝ Matrix.single i i b))) = 1) → c - 1 ∈ intAt D (· = v) := by
  intro D ψ hψ V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v _ hV hW hmV hmW hcols i c hc1 hyp
  have hU : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) ∈
      latO V W (LV : Set _) (LW : Set _) (· = v) := by
    refine (SelfDualAt.latO_ann_at D ψ hψ V W LV LW hV hW (· = v) _ fun k l => ?_).2 fun u hu => ?_
    · rw [Matrix.smul_apply, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (eps_idAt v)
    have hux := LatMem.latO_mxAt hu
    have hfixu : SelfDualAt.cP (· = v) • u = u := by
      ext k l
      rw [Matrix.smul_apply, Algebra.smul_def]
      exact eps_mul (hux k l)
    have hπ := sandwich_latO hV hW (dW.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dW.pY) (fun z hz => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hmW z).1 hz).2.1 i)
      (dV.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dV.pY) (fun z hz => by
        rw [← Matrix.mulVec_mulVec, single_mulVec', one_mul]
        exact ((hmV z).1 hz).2.1 i) hu
    have e : dW.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dW.pY ⬝ (u ⬝ (dV.jY ⬝ (Matrix.single i i 1 : Mx D ρ ρ) ⬝ dV.pY)) =
        dV.extY W (dW.jY ⬝ (Matrix.single i i ((dW.pY ⬝ (u ⬝ dV.jY)) i i) : Mx D ρ ρ)) := by
      rw [HypDec.extY_apply, ← single_mul_mul_single]
      simp only [Matrix.mul_assoc]
    rw [e] at hπ
    have h1 := hyp _ (mxAt_mul_left dW.pY (mxAt_mul_right hux dV.jY) i i) hπ
    rw [symplO_eq, hO_extX, pairS_single, HypDec.extY_apply, Matrix.mul_assoc, dV.pY_jY, Matrix.mul_one,
      ← Matrix.mul_assoc dW.pY dW.jY, dW.pY_jY, Matrix.one_mul, Matrix.single_apply_same] at h1
    rw [← SelfDualAt.symplO_smul_swap, hfixu, symplO_eq, hO_extX, pairS_single]
    exact h1
  have hint : finPart D c ∈ intAE D := by
    refine int_of_stable dV hV hmV i hc1 fun a ha => ?_
    have ha' := idAt_of_colMul dV ha
    have h := LatMem.latO_maps hV hU ha
    have e : (SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ))) *ᵥ colMul dV.jX i a =
        colMul dW.jX i (c * a) := by
      have e0 : SelfDualAt.cP (· = v) • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) =
          eps v • dV.extX W (dW.jX ⬝ (Matrix.single i i c : Mx D ρ ρ)) := by
        ext k l
        rw [Matrix.smul_apply, Algebra.smul_def]
        rfl
      rw [e0, Matrix.smul_mulVec, HypDec.extX_apply, ← Matrix.mulVec_mulVec, single_mulVec', pX_colMul,
        ← colMul_mul, eps_mul (Ideal.mul_mem_left _ _ ha')]
    rw [e] at h
    exact (hcols i _ (Ideal.mul_mem_left _ _ ha')).2 h
  refine ⟨hc1, ?_⟩
  rw [RingHom.map_sub]
  exact sub_mem hint (int_of_idem (one_mul 1))

end GlobalTheory.FinPl.InvLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem normAt_exists : ∀ (D : D7) (V : HSp D) (R : Subgroup (GA D V)), IsClosed (R : Set (GA D V)) → ∀ (L : Lat V),
    IsSelfDualC V L → ∀ Q : Finset (Pl D), ∃ ρ μ, IsNormAt V R L (· ∈ Q) ρ μ := by
  intro D V R hR L hL Q
  obtain ⟨⟨K, hK, hKc, hKo⟩, -⟩ := (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V Q).2.2.2.2.2.2.2.2.1 L hL (· ∈ Q)
  have hKG : ∀ g : GA D V, g ∈ K → g ∈ grpAt V (· ∈ Q) := fun g hg => ((hK g).1 hg).1
  have h1 : InK V L (· ∈ Q) 1 := (hK 1).1 K.one_mem

  let S : Set (grpAt V (· ∈ Q)) := {g | InK V L (· ∈ Q) g.1}
  have hSe : S = ((K.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) := by
    ext g; simp [S, Subgroup.mem_subgroupOf, hK]
  have hSo : IsOpen S := hSe ▸ hKo
  have hSc : IsCompact S := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    convert hKc using 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩; exact (hK _).2 hg
    · intro hx; exact ⟨⟨x, hKG x hx⟩, (hK x).1 hx, rfl⟩

  let T := R.subgroupOf (grpAt V (· ∈ Q))
  let S' : Set T := {g | InK V L (· ∈ Q) g.1.1}
  have hS'o : IsOpen S' := hSo.preimage continuous_subtype_val
  have hS'c : IsCompact S' := by
    rw [(Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).isCompact_iff]
    convert hKc.inter_right hR using 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩; exact ⟨(hK _).2 hg, Subgroup.mem_subgroupOf.1 g.2⟩
    · rintro ⟨hx, hxR⟩
      exact ⟨⟨⟨x, hKG x hx⟩, Subgroup.mem_subgroupOf.2 hxR⟩, (hK x).1 hx, rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts (grpAt V (· ∈ Q)) :=
    ⟨⟨S, hSc⟩, by rw [hSo.interior_eq]; exact ⟨1, h1⟩⟩
  let K₁ : TopologicalSpace.PositiveCompacts T :=
    ⟨⟨S', hS'c⟩, by rw [hS'o.interior_eq]; exact ⟨1, h1⟩⟩
  refine ⟨Measure.haarMeasure K₁, Measure.haarMeasure K₀, inferInstance, inferInstance, ?_, ?_⟩
  · exact Measure.haarMeasure_self (K₀ := K₀)
  · exact Measure.haarMeasure_self (K₀ := K₁)

end GlobalTheory.SeeSaw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.unfoldedTerm_basePoint_eq_flatMap_pairing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖tFlat s vL y Ψ‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  first | exact @GlobalTheory.Unf.FB.fl_base_eq_tFlat | exact GlobalTheory.Unf.FB.fl_base_eq_tFlat | (intros; apply GlobalTheory.Unf.FB.fl_base_eq_tFlat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kappa_maps_besselLineLattice_iff_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ (B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P) := by
  first | exact @GlobalTheory.KappaLat.kappa_line_lat_iff | exact GlobalTheory.KappaLat.kappa_line_lat_iff | (intros; apply GlobalTheory.KappaLat.kappa_line_lat_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftCoefCont

theorem continuous_l2_weil_action_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ Q₁ Q₂, Continuous fun g : GA D (Wc D i) => l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hc Q₁ Q₂
  obtain ⟨-, -, -, -, -, hom, -, -, hpt, -, -⟩ := h
  have e : ∀ g : GA D (Wc D i), l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) =
      GlobalTheory.RawLift.thetaIP μ 𝓧 (ptAt R i σ BW f Q₂) (ω (1, g) (ptAt R i σ BW f Q₁)) := fun g => by
    rw [← GlobalTheory.RawLift.FockCoef.thetaInner_star, GlobalTheory.RawLift.GoodModulus.thetaInner_eq_star_l2, star_star]
  simp only [e]
  exact GlobalTheory.RawLift.FockCoef.continuous_coef hom hc (hpt Q₂) (hpt Q₁)

end GlobalTheory.LiftCoefCont

end
end

section

noncomputable section

namespace GlobalTheory.KerDia.Eqv

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem ent_smul : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ)
    {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b') (g : (I.stp u a i).G b)
    (g' : (I.stp u a (i + 1)).G b') (x : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
    (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) →
    ent I l u a i ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') ((I.stp u a i).tr B.fields.emb B.embLL b g x) =
      (I.stp u a (i + 1)).tr B.fields.emb B.embLL b' g' (ent I l u a i q q' x) := by
  intro B X I l h u a i b b' q q' g g' x hx
  obtain ⟨P, hP⟩ := hx
  funext y'
  have hP' : fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1 P = fun y : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) =>
      (∏ τ, deFr y τ ^ (I.chain l u a).sSharp i τ) * x y := hP
  have hr : I.rho u a i b ((I.stp u a i).act b g q) * I.rho' u a i b' ((I.stp u a (i + 1)).act b' g' q') ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have key := opOf_equiv B.fields.emb B.embLL ((I.chain l u a).sSharp i) ((I.chain l u a).sDiv i) I.J.cD (th_contDiff I h u a i q q')
    ((I.stp u a i).gam b g) ((I.stp u a (i + 1)).gam b' g') ((I.stp u a i).chr b g) ((I.stp u a (i + 1)).chr b' g') hr
    (th_move I l h u a i q q' g g') hP' y'
  refine (ent_apply I l u a i _ _ _ y').trans (key.trans ?_)
  rw [← ent_apply]
  rfl

end GlobalTheory.KerDia.Eqv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.periodGroups_reduce_splitPlaceFamily_succ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ (μ₁ : Measure (grpAt S.J.W (places Q))) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places Q)))) (μ₂ : Measure (grpAt S.B'.V (places Q))) (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places Q)))), Norm Q μ₁ ρ₁ μ₂ ρ₂ → LocallyCompactSpace (grpAt S.J.W (places fun i => Q i.succ)) ∧ LocallyCompactSpace (grpAt S.B'.V (places fun i => Q i.succ)) ∧ IsClosed (((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ)) : Set (grpAt S.J.W (places fun i => Q i.succ)))) ∧ IsClosed (((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ)) : Set (grpAt S.B'.V (places fun i => Q i.succ)))) ∧ IsClosed ((RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1) : Set (GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k))) ∧ IsClosed ((R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1) : Set (GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k))) ∧ ∃ (μ₁' : Measure (grpAt S.J.W (places fun i => Q i.succ))) (ρ₁' : Measure ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ)))) (μ₂' : Measure (grpAt S.B'.V (places fun i => Q i.succ))) (ρ₂' : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ)))) (m₁ : Measure (GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k)) (s₁ : Measure (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1))) (m₂ : Measure (GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k)) (s₂ : Measure (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1))) (p₁ : Measure (((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ))).prod (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1)))) (p₂ : Measure (((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ))).prod (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1)))), Norm (fun i => Q i.succ) μ₁' ρ₁' μ₂' ρ₂' ∧ LocNorm (Q 0) m₁ s₁ m₂ s₂ ∧ ρ₁'.IsInvInvariant ∧ ρ₂'.IsInvInvariant ∧ s₁.IsInvInvariant ∧ s₂.IsInvInvariant ∧ p₁.map (Subgroup.prodEquiv _ _) = ρ₁'.prod s₁ ∧ p₂.map (Subgroup.prodEquiv _ _) = ρ₂'.prod s₂ ∧ ∀ (F : GA D S.J.W → GA D S.B'.V → ℂ) (z : ℂ), Iter2 p₁ (μ₁'.prod m₁) p₂ (μ₂'.prod m₂) (fun x y => F (x.1.1 * (Q 0).gl₁ x.2) (y.1.1 * (Q 0).gl₂ y.2)) z → Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => F x.1 y.1) z := by
  first | exact @GlobalTheory.QRed.reduce | exact GlobalTheory.QRed.reduce | (intros; apply GlobalTheory.QRed.reduce <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.columnLevel_iff_rowLattice_kept_at_place : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ v : GlobalTheory.FinPl.Pl D, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ a ∈ grpAt (D.sp.X 0) (· = v), ∃ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = y.1.1 ∧ ((y : GL _ _) ∈ F.cls0.lev.U ↔ Moves (D.sp.Y 0) (embA B.d B.o (a₀ * a * a₀⁻¹)) (latS D) (latS D) (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LevRow.levrow | exact GlobalTheory.Core.Mi.LevRow.levrow | (intros; apply GlobalTheory.Core.Mi.LevRow.levrow <;> assumption)
end
