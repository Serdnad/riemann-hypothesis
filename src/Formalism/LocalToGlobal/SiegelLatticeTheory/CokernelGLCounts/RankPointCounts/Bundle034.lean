module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Lemmata.GeneralBFactRightBisAlt.Imports
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

namespace Formalism.L2.SG.Pf.StabIntGrp

section Tri

variable {K : Type*} [CommRing K] {n : ℕ}

def LoIn (S : Subring K) (l : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ a, l a a = 1) ∧ (∀ a b, a < b → l a b = 0) ∧ ∀ a b, l a b ∈ S

theorem loIn_lower {S : Subring K} {l : Matrix (Fin n) (Fin n) K} (h : LoIn S l) : l.IsLowerTriangular := by
  intro i j hij
  exact h.2.1 i j hij

theorem mul_diag_of_lower {l l' : Matrix (Fin n) (Fin n) K} (hl : ∀ a b, a < b → l a b = 0)
    (hl' : ∀ a b, a < b → l' a b = 0) (a : Fin n) : (l * l') a a = l a a * l' a a := by
  first | exact Bl.general_b_fact_right_bis_other.goal1 .. | (apply Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_bis_other.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_bis_other.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' hl hl' a | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' hl hl' | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' hl | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l l' | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n l | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› n | exact @Bl.general_b_fact_right_bis_other.goal1 K ‹_› | exact @Bl.general_b_fact_right_bis_other.goal1 K

theorem loIn_one (S : Subring K) : LoIn S (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_lt h), fun a b => ?_⟩
  by_cases h : a = b
  · subst h; rw [Matrix.one_apply_eq]; exact S.one_mem
  · rw [Matrix.one_apply_ne h]; exact S.zero_mem

theorem loIn_mul {S : Subring K} {l l' : Matrix (Fin n) (Fin n) K} (hl : LoIn S l) (hl' : LoIn S l') :
    LoIn S (l * l') := by
  refine ⟨fun a => by rw [mul_diag_of_lower hl.2.1 hl'.2.1, hl.1, hl'.1, one_mul], fun a b hab => ?_,
    fun a b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with h | h
    · rw [hl.2.1 a c h, zero_mul]
    · rw [hl'.2.1 c b (lt_of_le_of_lt h hab), mul_zero]
  · rw [Matrix.mul_apply]
    exact S.sum_mem fun c _ => S.mul_mem (hl.2.2 a c) (hl'.2.2 c b)

theorem det_loIn {S : Subring K} {l : Matrix (Fin n) (Fin n) K} (hl : LoIn S l) : l.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular l (loIn_lower hl)]
  exact Finset.prod_eq_one fun a _ => hl.1 a

theorem loIn_inv {S : Subring K} {l : Matrix (Fin n) (Fin n) K} (hl : LoIn S l) : LoIn S l⁻¹ := by
  have hd : IsUnit l.det := by rw [det_loIn hl]; exact isUnit_one
  have hinv : l⁻¹ = l.adjugate := by rw [Matrix.inv_def, det_loIn hl, Ring.inverse_one, one_smul]
  letI : Invertible l := Matrix.invertibleOfIsUnitDet l hd
  have hlow : l⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular (loIn_lower hl)
  have hlow' : ∀ a b, a < b → l⁻¹ a b = 0 := fun a b h => hlow h
  refine ⟨fun a => ?_, hlow', fun a b => ?_⟩
  · have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul l hd) a) a
    rw [mul_diag_of_lower hlow' hl.2.1, hl.1, mul_one, Matrix.one_apply_eq] at h1
    exact h1
  · let lS : Matrix (Fin n) (Fin n) S := fun i j => ⟨l i j, hl.2.2 i j⟩
    have hmap : l = S.subtype.mapMatrix lS := by ext i j; rfl
    rw [hinv, hmap, ← RingHom.map_adjugate]
    exact (lS.adjugate a b).2

theorem upIn_iff (S : Subring K) (ρ : Matrix (Fin n) (Fin n) K) :
    ((∀ a, ρ a a = 1) ∧ (∀ a b, b < a → ρ a b = 0) ∧ ∀ a b, ρ a b ∈ S) ↔ LoIn S ρ.transpose := by
  unfold LoIn
  simp only [Matrix.transpose_apply]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, fun a b h => h2 b a h, fun a b => h3 b a⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, fun a b h => h2 b a h, fun a b => h3 b a⟩⟩

end Tri

section Loc

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ}

theorem intUp_iff (ρ : Matrix (Fin n) (Fin n) E) : Formalism.MainNotions.S.TieN.IntUp Mp ρ ↔ LoIn Mp.R ρ.transpose :=
  upIn_iff Mp.R ρ

theorem intLow_one : Formalism.MainNotions.S.TieN.IntLow Mp (1 : Matrix (Fin n) (Fin n) E) := loIn_one _

theorem intUp_one : Formalism.MainNotions.S.TieN.IntUp Mp (1 : Matrix (Fin n) (Fin n) E) := by
  rw [intUp_iff, Matrix.transpose_one]; exact loIn_one _

theorem intLow_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntLow Mp l') : Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := loIn_mul h h'

theorem intUp_mul {ρ ρ' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp ρ)
    (h' : Formalism.MainNotions.S.TieN.IntUp Mp ρ') : Formalism.MainNotions.S.TieN.IntUp Mp (ρ * ρ') := by
  rw [intUp_iff] at *; rw [Matrix.transpose_mul]; exact loIn_mul h' h

theorem intLow_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) :
    Formalism.MainNotions.S.TieN.IntLow Mp l⁻¹ := loIn_inv h

theorem intUp_inv {ρ : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp ρ) :
    Formalism.MainNotions.S.TieN.IntUp Mp ρ⁻¹ := by
  rw [intUp_iff] at *; rw [Matrix.transpose_nonsing_inv]; exact loIn_inv h

theorem intLow_det {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) : IsUnit l.det := by
  rw [det_loIn h]; exact isUnit_one

theorem intUp_det {ρ : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp ρ) : IsUnit ρ.det := by
  rw [intUp_iff] at h; rw [← Matrix.det_transpose, det_loIn h]; exact isUnit_one

end Loc

section Field

variable {E : Type*} [Field E] {n : ℕ}

theorem isLoUni_iff (a : Matrix (Fin n) (Fin n) E) : IsLoUni a ↔ LoIn (⊤ : Subring E) a := by
  unfold IsLoUni LoIn
  exact ⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij, fun _ _ => Subring.mem_top _⟩,
    fun h i j => ⟨h.2.1 i j, fun hij => hij ▸ h.1 i⟩⟩

theorem isUpUni_iff (b : Matrix (Fin n) (Fin n) E) : IsUpUni b ↔ LoIn (⊤ : Subring E) b.transpose := by
  rw [← upIn_iff]
  unfold IsUpUni
  exact ⟨fun h => ⟨fun i => (h i i).2 rfl, fun i j hij => (h i j).1 hij, fun _ _ => Subring.mem_top _⟩,
    fun h i j => ⟨h.2.1 i j, fun hij => hij ▸ h.1 i⟩⟩

end Field

theorem zhatOM_zhatOM {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM (ZhatOM Z) = Z := by
  funext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word) (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
  (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (w : Point D.host.E (D.R.rS + 1))

theorem one_mem_set : (1 : GLR D) ∈ stabIntSet D u u' δ M w := by
  refine ⟨(isLoUni_iff _).2 (by simpa using loIn_one _), 1, (isUpUni_iff _).2 (by simpa using loIn_one _),
    by simp, fun p => ⟨1, 1, intLow_one _, intUp_one _, fun Z => ?_⟩⟩
  simp [zhatOM_zhatOM]

theorem mul_mem_set {a a' : GLR D} (ha : a ∈ stabIntSet D u u' δ M w) (ha' : a' ∈ stabIntSet D u u' δ M w) :
    a * a' ∈ stabIntSet D u u' δ M w := by
  obtain ⟨hla, b, hb, hab, hp⟩ := ha
  obtain ⟨hla', b', hb', hab', hp'⟩ := ha'
  refine ⟨?_, b' * b, ?_, ?_, fun p => ?_⟩
  · rw [Units.val_mul, isLoUni_iff]; exact loIn_mul ((isLoUni_iff _).1 hla) ((isLoUni_iff _).1 hla')
  · rw [isUpUni_iff, Matrix.transpose_mul]; exact loIn_mul ((isUpUni_iff _).1 hb) ((isUpUni_iff _).1 hb')
  · rw [Units.val_mul]
    calc (a : MatR D) * a' * ptMat w * (b' * b) = (a : MatR D) * ((a' : MatR D) * ptMat w * b') * b := by
          simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hab', hab]
  · obtain ⟨l, ρ, hl, hρ, hm⟩ := hp p
    obtain ⟨l', ρ', hl', hρ', hm'⟩ := hp' p
    refine ⟨l * l', ρ' * ρ, intLow_mul _ hl hl', intUp_mul _ hρ' hρ, fun Z => ?_⟩
    have e : ((a * a' : GLR D) : MatR D) * ZhatOM Z * (b' * b) =
        (a : MatR D) * ZhatOM (ZhatOM ((a' : MatR D) * ZhatOM Z * b')) * b := by
      rw [zhatOM_zhatOM, Units.val_mul]; simp only [Matrix.mul_assoc]
    rw [e, hm, hm']
    simp only [Matrix.mul_assoc]

theorem inv_mem_set {a : GLR D} (ha : a ∈ stabIntSet D u u' δ M w) : a⁻¹ ∈ stabIntSet D u u' δ M w := by
  obtain ⟨hla, b, hb, hab, hp⟩ := ha
  have hbT := (isUpUni_iff _).1 hb
  have hbd : IsUnit b.det := by rw [← Matrix.det_transpose, det_loIn hbT]; exact isUnit_one
  have hai : ((a⁻¹ : GLR D) : MatR D) = (a : MatR D)⁻¹ := Matrix.coe_units_inv a
  have had : IsUnit (a : MatR D).det := by rw [det_loIn ((isLoUni_iff _).1 hla)]; exact isUnit_one
  refine ⟨?_, b⁻¹, ?_, ?_, fun p => ?_⟩
  · rw [hai, isLoUni_iff]; exact loIn_inv ((isLoUni_iff _).1 hla)
  · rw [isUpUni_iff, Matrix.transpose_nonsing_inv]; exact loIn_inv hbT
  · rw [hai]
    calc (a : MatR D)⁻¹ * ptMat w * b⁻¹ = (a : MatR D)⁻¹ * ((a : MatR D) * ptMat w * b) * b⁻¹ := by rw [hab]
      _ = ptMat w := by
        rw [show (a : MatR D)⁻¹ * ((a : MatR D) * ptMat w * b) * b⁻¹ =
            ((a : MatR D)⁻¹ * (a : MatR D)) * ptMat w * (b * b⁻¹) by simp only [Matrix.mul_assoc],
          Matrix.nonsing_inv_mul _ had, Matrix.mul_nonsing_inv _ hbd, Matrix.one_mul, Matrix.mul_one]
  · obtain ⟨l, ρ, hl, hρ, hm⟩ := hp p
    refine ⟨l⁻¹, ρ⁻¹, intLow_inv _ hl, intUp_inv _ hρ, fun Z => ?_⟩
    set Z' := ZhatOM (((a⁻¹ : GLR D) : MatR D) * ZhatOM Z * b⁻¹) with hZ'
    have e : (a : MatR D) * ZhatOM Z' * b = ZhatOM Z := by
      rw [hZ', zhatOM_zhatOM, hai, show (a : MatR D) * ((a : MatR D)⁻¹ * ZhatOM Z * b⁻¹) * b =
          ((a : MatR D) * (a : MatR D)⁻¹) * ZhatOM Z * (b⁻¹ * b) by simp only [Matrix.mul_assoc],
        Matrix.mul_nonsing_inv _ had, Matrix.nonsing_inv_mul _ hbd, Matrix.one_mul, Matrix.mul_one]
    have h1 := hm Z'
    rw [e, zhatOM_zhatOM] at h1
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (intLow_det _ hl), Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ (intUp_det _ hρ)]

def stabIntGrp : Subgroup (GLR D) where
  carrier := stabIntSet D u u' δ M w
  one_mem' := one_mem_set D u u' δ M w
  mul_mem' := mul_mem_set D u u' δ M w
  inv_mem' := inv_mem_set D u u' δ M w

theorem stabInt_eq : stabInt D u u' δ M w = stabIntGrp D u u' δ M w := by
  unfold stabInt
  exact Subgroup.closure_eq (stabIntGrp D u u' δ M w)

theorem mem_stabInt_iff (a : GLR D) : a ∈ stabInt D u u' δ M w ↔ a ∈ stabIntSet D u u' δ M w := by
  rw [stabInt_eq]; rfl

end Formalism.L2.SG.Pf.StabIntGrp
end
end

section

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem nOinf_closed_under_mul_inv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ⊆ X.NinfU u ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      δ * δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, δ⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) := by
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hc := Formalism.L2.SG.Pf.NOsub_coe X u hK
  refine ⟨fun s hs => Formalism.L2.SG.Pf.no_sub_ninf X u hs, fun δ hδ δ' hδ' => ?_, fun δ hδ => ?_⟩
  · rw [← hc] at hδ hδ' ⊢
    exact (Formalism.L2.SG.Pf.NOsub X u hK).mul_mem hδ hδ'
  · rw [← hc] at hδ ⊢
    exact (Formalism.L2.SG.Pf.NOsub X u hK).inv_mem hδ

end Formalism.L2.SG.Pf.NcReal.JX
end

section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ind

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem inv_apply' (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : (VS D).V) : (δ⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) y = δ.symm y :=
  rfl

theorem xa_top : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp [Fin.is_lt]

theorem st_mul {γ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (hδ : δ ∈ stabF D F0) :
    γ * δ ∈ stabF D F0 := by
  refine ⟨mul_mem hγ.1 hδ.1, fun j => ?_, ?_⟩
  · rw [kmap_mul, hδ.2.1 j, hγ.2.1 j]
  · show γ (δ F0.z) = F0.z
    rw [hδ.2.2, hγ.2.2]

theorem st_inv {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : γ⁻¹ ∈ stabF D F0 := by
  refine ⟨inv_mem hγ.1, fun j => ?_, ?_⟩
  · conv_lhs => rw [← hγ.2.1 j]
    rw [← kmap_mul, inv_mul_cancel, kmap_one]
  · show γ.symm F0.z = F0.z
    conv_lhs => rw [← hγ.2.2]
    exact γ.symm_apply_apply _

theorem stab_X_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} (hx : x ∈ F0.X) :
    γ x ∈ F0.X := by
  rw [← xa_top] at hx ⊢
  rw [← hγ.2.1 D.R.rS]
  exact Submodule.mem_map_of_mem hx

theorem stab_perp_mem {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ y ∈ perpS (VS D) F0.X := by
  intro x hx
  have h1 := hy _ (stab_X_mem F0 (st_inv F0 hγ) hx)
  have h2 := hγ.1 (γ⁻¹ x) y
  rw [inv_apply', LinearEquiv.apply_symm_apply] at h2
  rw [h2]
  exact h1

def ind {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : WbQ D F0 → WbQ D F0 :=
  Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
    ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (fun y hy => stab_perp_mem F0 hγ hy))
    (fun x hx => stab_X_mem F0 hγ hx)

theorem ind_mk {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (x : perpS (VS D) F0.X) :
    ind F0 hγ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, stab_perp_mem F0 hγ x.2⟩ := rfl

theorem autLz_iff (Λ : Submodule (𝓞 D.host.E) (VS D).V) (φ : WbQ D F0 → WbQ D F0) :
    φ ∈ autLz D F0 Λ ↔ ∃ γ, ∃ hγ : γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ ∧ φ = ind F0 hγ := by
  constructor
  · rintro ⟨γ, hγ, hΛ, hφ⟩
    refine ⟨γ, hγ, hΛ, funext fun q => ?_⟩
    refine Submodule.Quotient.induction_on _ q (fun x => ?_)
    exact (hφ x (stab_perp_mem F0 hγ x.2)).trans rfl
  · rintro ⟨γ, hγ, hΛ, rfl⟩
    exact ⟨γ, hγ, hΛ, fun x hx => rfl⟩

theorem ind_inv_cancel {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0) (q : WbQ D F0) :
    ind F0 (st_inv F0 hδ) (ind F0 hδ q) = q := by
  refine Submodule.Quotient.induction_on _ q (fun x => ?_)
  rw [ind_mk, ind_mk]
  congr 1
  apply Subtype.ext
  show δ⁻¹ (δ x.1) = x.1
  rw [inv_apply', LinearEquiv.symm_apply_apply]

theorem card_autLz_gmap {δ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hδ : δ ∈ stabF D F0)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Nat.card ↥(autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ)) = Nat.card ↥(autLz D F0 Λ) := by
  let c : (WbQ D F0 → WbQ D F0) → (WbQ D F0 → WbQ D F0) := fun φ => ind F0 hδ ∘ φ ∘ ind F0 (st_inv F0 hδ)
  have hc : Function.Injective c := by
    intro φ ψ hφψ
    funext q
    have h1 := congrFun hφψ (ind F0 hδ q)
    simp only [c, Function.comp, ind_inv_cancel] at h1
    have h2 := congrArg (ind F0 (st_inv F0 hδ)) h1
    rwa [ind_inv_cancel, ind_inv_cancel] at h2
  have hset : autLz D F0 (Formalism.HermitianLatticesTheory.gmap δ Λ) = c '' autLz D F0 Λ := by
    ext ψ
    rw [autLz_iff, Set.mem_image]
    constructor
    · rintro ⟨γ', hγ', hΛ', rfl⟩
      refine ⟨ind F0 (st_mul F0 (st_mul F0 (st_inv F0 hδ) hγ') hδ),
        (autLz_iff F0 Λ _).2 ⟨_, _, ?_, rfl⟩, ?_⟩
      · rw [gmap_mul', gmap_mul', hΛ', ← gmap_mul', inv_mul_cancel, gmap_one']
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => ?_)
        simp only [c, Function.comp]
        rw [ind_mk, ind_mk, ind_mk, ind_mk]
        congr 1
        apply Subtype.ext
        show δ ((δ⁻¹ * γ' * δ) (δ⁻¹ x.1)) = γ' x.1
        show δ (δ⁻¹ (γ' (δ (δ⁻¹ x.1)))) = γ' x.1
        rw [inv_apply', inv_apply', LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨γ, hγ, hΛ, rfl⟩ := (autLz_iff F0 Λ φ).1 hφ
      refine ⟨δ * γ * δ⁻¹, st_mul F0 (st_mul F0 hδ hγ) (st_inv F0 hδ), ?_, ?_⟩
      · rw [gmap_mul', ← gmap_mul' δ⁻¹ δ, inv_mul_cancel, gmap_one', gmap_mul', hΛ]
      · funext q
        refine Submodule.Quotient.induction_on _ q (fun x => rfl)
  rw [hset]
  exact Nat.card_image_of_injective hc _

end Ind

end Formalism.L2.SG.RhoPf
end
end
