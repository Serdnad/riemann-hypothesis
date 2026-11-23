module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle792
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle815
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle794
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_isIso_morphismRestrict_of_isHom_id : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z), M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  intro o Ω _ _ _ Y M q hq
  have := M.sep
  have : IsSeparated (q ≫ M.s) := hq.inducedModelMorphism_comp_structureMap.symm ▸ Y.sep
  have : IsSeparated q := IsSeparated.of_comp q M.s
  obtain ⟨U, hU, hgU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint Y.Z) trivial
  obtain ⟨S, hS⟩ := fg_ringOn hU ⟨_, hgU⟩
  have hop : IsOpen (⋂ x ∈ S, {z | x ∈ M.O z}) :=
    isOpen_biInter_finset fun x _ => M.isOpen_setOf_mem_O x
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, hop⟩) (x := genericPoint M.Z)
      (Set.mem_iInter₂.2 fun x _ => by
        show x ∈ M.O _
        rw [O_genericPoint]
        exact Algebra.mem_top)
  have hR : Y.ringOn U ≤ M.ringOn V := by
    rw [← hS]
    exact Algebra.adjoin_le fun x hx => mem_ringOn.2 fun w hw => Set.mem_iInter₂.1 (hle hw) x hx
  refine ⟨V, ⟨_, hzV⟩, isIso_morphismRestrict_of_local_dominant_sections q V fun z hz => ?_⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint Y.Z, hgU⟩ (V := V) ⟨z, hz⟩ fun x hx => hR hx
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hz⟩)
  have hid : ∀ {X : Scheme.{0}} (a : Spec (CommRingCat.of Ω) ⟶ X),
      Spec.map (CommRingCat.ofHom (AlgHom.id o Ω).toRingHom) ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hz, hV.range_fromSpec ▸ fun w hw => hw,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hq

end GlobalTheory.ZH.RatModel
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_isIso_morphismRestrict_of_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω), IsProjOver Y.s → ∀ q : Y.Z ⟶ M.Z, M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  intro o Ω _ _ _ Y M hY q hq
  have := M.sep
  have : IsSeparated (q ≫ M.s) := hq.inducedModelMorphism_comp_structureMap.symm ▸ Y.sep
  have : IsSeparated q := IsSeparated.of_comp q M.s
  obtain ⟨m, d, hd⟩ := exists_isCl_of_isProjOver hY
  obtain ⟨i, hi⟩ := hd.1 (genericPoint Y.Z)
  obtain ⟨U, hU, hD, hR⟩ := hd.2 i hi.1
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, M.isOpen_setOf_div d i⟩) (x := genericPoint M.Z)
      (div_genericPoint hi.1)
  refine ⟨V, ⟨_, hzV⟩, isIso_morphismRestrict_of_local_dominant_sections q V fun z hz => ?_⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint Y.Z, hD ▸ hi⟩ (V := V) ⟨z, hz⟩
    fun x hx => mem_ringOn.2 fun w hw =>
      Div.map_mem_O_of_mem_adjoin (M' := M) (φ := AlgHom.id o Ω) (t := d) (i := i) (z := w) (hle hw) (hR ▸ hx)
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hz⟩)
  have hid : ∀ {X : Scheme.{0}} (a : Spec (CommRingCat.of Ω) ⟶ X),
      Spec.map (CommRingCat.ofHom (AlgHom.id o Ω).toRingHom) ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hz, hV.range_fromSpec ▸ fun w hw => hw,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hq

end GlobalTheory.ZH.RatModel
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem isChar_conj_eq {G : Type} [Group G] {Y : G → ℂ} (hY : IsChar ℂ ℂ Y) (g z : G) :
    Y (z * g * z⁻¹) = Y g := by
  obtain ⟨n, ρ, h⟩ := hY
  rw [h, h, Representation.char_conj]

theorem conv_op_eq {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (Y h : G → ℂ) :
    ∑ x, star (∑ y, Y y * h (y⁻¹ * x)) • ρ x =
      (∑ y, star (Y y) • ρ y) * (∑ z, star (h z) • ρ z) := by
  rw [Finset.sum_mul_sum]
  simp_rw [star_sum, star_mul', Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [map_mul, smul_mul_smul_comm, smul_smul, mul_comm]

def convL {G : Type} [Group G] [Fintype G] (Y : G → ℂ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  ∑ g, star (Y g) • LinearMap.funLeft ℂ ℂ (fun z => g * z)

theorem convL_apply {G : Type} [Group G] [Fintype G] (Y : G → ℂ) (a : G → ℂ) (z : G) :
    convL Y a z = ∑ g, star (Y g) * a (g * z) := by
  simp [convL, LinearMap.funLeft, Finset.sum_apply]

def regKer {G : Type} [Group G] [Fintype G] (Y : G → ℂ) :
    Representation ℂ G (LinearMap.ker (convL Y)) where
  toFun g := (LinearMap.funLeft ℂ ℂ (fun z => z * g)).restrict (p := LinearMap.ker (convL Y))
      (q := LinearMap.ker (convL Y)) (by
        intro a ha
        rw [LinearMap.mem_ker] at ha ⊢
        funext z
        have := congrFun ha (z * g)
        simp only [convL_apply, Pi.zero_apply] at this ⊢
        simpa [LinearMap.funLeft, mul_assoc] using this)
  map_one' := by ext a z; simp [LinearMap.funLeft]
  map_mul' g h := by ext a z; simp [LinearMap.funLeft, mul_assoc]

theorem regKer_apply {G : Type} [Group G] [Fintype G] (Y : G → ℂ) (g : G) (a : LinearMap.ker (convL Y))
    (z : G) : ((regKer Y g a : LinearMap.ker (convL Y)) : G → ℂ) z = (a : G → ℂ) (z * g) := rfl

theorem kills_iff_conv : ∀ (G : Type) [Group G] [Finite G] (φ Y : G → ℂ), IsChar ℂ ℂ Y →
    (Kills φ Y ↔ ∃ h : G → ℂ, ∀ x, φ x = ∑ᶠ y, Y y * h (y⁻¹ * x)) := by
  intro G _ _ φ Y hY
  have := Fintype.ofFinite G
  constructor
  · intro hK
    set K := LinearMap.ker (convL Y)

    have hT : ∑ g, star (Y g) • regKer Y g = 0 := by
      ext a z
      have ha := congrFun (LinearMap.mem_ker.1 a.2) z
      rw [convL_apply, Pi.zero_apply] at ha
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, regKer_apply, smul_eq_mul, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rw [← ha, ← Equiv.sum_comp (MulAut.conj z⁻¹).toEquiv]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hc := isChar_conj_eq hY g z⁻¹
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv] at hc ⊢
      rw [hc]
      congr 2
      group
    have hK' := hK K (regKer Y) (by
      rw [finsum_eq_sum_of_fintype]
      have := congrArg (LinearMap.trace ℂ K) hT

      simpa [map_sum, smul_eq_mul] using this)
    rw [finsum_eq_sum_of_fintype] at hK'

    let ℓ : Module.Dual ℂ (G → ℂ) := ∑ x, star (φ x) • (LinearMap.proj x : (G → ℂ) →ₗ[ℂ] ℂ)
    have hℓ : ∀ a, ℓ a = ∑ x, star (φ x) * a x := fun a => by simp [ℓ]
    have hmem : ℓ ∈ K.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro a ha
      have := congrFun (congrArg Subtype.val (LinearMap.congr_fun hK' ⟨a, ha⟩)) 1
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, regKer_apply, smul_eq_mul, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply] at this
      have e : ∀ x, ((regKer Y x ⟨a, ha⟩ : LinearMap.ker (convL Y)) : G → ℂ) 1 = a x := fun x => by
        show a (1 * x) = a x
        rw [one_mul]
      simp only [e] at this
      rw [hℓ, this]
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
    obtain ⟨μ, hμ⟩ := hmem
    refine ⟨fun w => star (μ (Pi.single w 1)), fun x => ?_⟩
    have hδ : convL Y (Pi.single x 1) = ∑ g, star (Y g) • Pi.single (g⁻¹ * x) 1 := by
      funext z
      rw [convL_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      congr 1
      simp only [Pi.single_apply, eq_inv_mul_iff_mul_eq]
    have h1 := LinearMap.congr_fun hμ (Pi.single x 1)

    rw [LinearMap.dualMap_apply, hδ, map_sum, hℓ] at h1
    simp only [map_smul, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    rw [finsum_eq_sum_of_fintype]
    have h2 := congrArg star h1
    simp only [star_sum, star_mul', star_star] at h2
    rw [← h2]
  · rintro ⟨h, hφ⟩ V _ _ _ ρ hV
    have hY0 := GlobalTheory.T.isInCharacterIsotypicPart_self G Y hY V ρ hV
    rw [finsum_eq_sum_of_fintype] at hY0 ⊢
    simp_rw [hφ, finsum_eq_sum_of_fintype]
    rw [conv_op_eq, hY0, zero_mul]

end GlobalTheory.Shin
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraProduct_shintaniLift_galois : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ) (t : F' ≃ₐ[F] F') (L : List (ℕ × ℕ)) (n : ℕ), n = deg (liftL (Nat.card F) (Module.finrank F F') L) → ∀ x : GL (Fin n) F', J θ (liftL (Nat.card F) (Module.finrank F F') L) n (galAct F F' n t x) = J θ (liftL (Nat.card F) (Module.finrank F F') L) n x := by
  first | (exact @GlobalTheory.Shin.J_liftL_galAct) | (exact GlobalTheory.Shin.J_liftL_galAct) | (intros; apply GlobalTheory.Shin.J_liftL_galAct <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFamGL

theorem vact_vmul (N : ℕ) (D α : GL (Fin 2) (ZMod N)) (e : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    vact N (vmul e (α * D)) γ = vmul e (gact N D α γ * D) := by
  have h : gact N D α γ * D = α * D * redGL N γ := by
    simp only [gact]
    group
  rw [h]
  simp only [vact, vmul, Units.val_mul, Matrix.vecMul_vecMul]

theorem main : ∀ (N : ℕ) [NeZero N] (D : GL (Fin 2) (ZMod N)) (e : Fin 2 → ZMod N), IsFam (gact N D) 2 (fun α => wp N (vmul e (α * D))) ∧ IsFam (gact N D) 3 (fun α => wpd N (vmul e (α * D))) := by
  intro N _ D e
  obtain ⟨h2, h3⟩ := GlobalTheory.T.weierstrassP_torsion_isModularFamily N
  refine ⟨fun α γ => ?_, fun α γ => ?_⟩
  · have h := h2 (vmul e (α * D)) γ
    rw [vact_vmul] at h
    exact h
  · have h := h3 (vmul e (α * D)) γ
    rw [vact_vmul] at h
    exact h

end GlobalTheory.WpFamGL
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpInt

theorem isIntegral_int_of_closure (y : ℂ)
    (hy : IsIntegral (integralClosure ℤ ℂ).toSubring y) : IsIntegral ℤ y := by
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ (r : ℂ) := r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).mp h⟩
  exact isIntegral_trans (R := ℤ) (A := R) y hy

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x : Fin 2 → ZMod N, IsIntegral ℤ (12 * (N : ℂ) ^ 2 * wp N x τ / ω ^ 2) ∧
      IsIntegral ℤ ((N : ℂ) ^ 3 * wpd N x τ / ω ^ 3) := by
  intro N _ τ ω hj hω x
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring with hR
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hbij : ActBij (vact N) := (GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).1.actBij
  have hfam := GlobalTheory.T.weierstrassP_torsion_isModularFamily N
  have halg := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure (Fin 2 → ZMod N) (vact N)
  have hlin := GlobalTheory.T.hasQExpansionOfLevel_linear_operations N
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNx : ∀ y : Fin 2 → ZMod N, N • y = 0 := fun y => by
    funext i; simp [nsmul_eq_mul]
  constructor
  · have hF : IsFam (vact N) ((2 : ℕ) : ℤ) (fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) :=
      halg.2.2.1 2 _ (wp N) hfam.1
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) y) := fun y =>
      ⟨fun k => 12 * (N : ℂ) ^ 2 * cP N y k, hlin.2.2.1 _ _ _ (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N y),
        fun k => (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N y k hN (hNx y)).2.2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 2 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h
  · have hF : IsFam (vact N) ((3 : ℕ) : ℤ) (fun y t => ((N : ℂ) ^ 3) * wpd N y t) :=
      halg.2.2.1 3 _ (wpd N) hfam.2
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => ((N : ℂ) ^ 3) * wpd N y t) y) := fun y =>
      ⟨fun k => (N : ℂ) ^ 3 * cD N y k, hlin.2.2.1 _ _ _ (GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N y),
        fun k => (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N y k hN (hNx y)).2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 3 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h

end GlobalTheory.WpInt
end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem isIntegral_sq_mul_wp_sub_div : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x y : Fin 2 → ZMod N, x ≠ 0 → y ≠ 0 →
      IsIntegral ℤ ((N : ℂ) ^ 2 * (wp N x τ - wp N y τ) / ω ^ 2) := by
  intro N _ τ ω hj hω x y hx hy
  obtain ⟨hR, -, -, -, hz, -⟩ := GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N
  have hvz : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)), vact N v γ = 0 ↔ v = 0 := fun v γ => hz v _
  let ι := {p : (Fin 2 → ZMod N) × (Fin 2 → ZMod N) // p.1 ≠ 0 ∧ p.2 ≠ 0}
  let act : ι → SL(2, ℤ) → ι := fun p γ =>
    ⟨(vact N p.1.1 γ, vact N p.1.2 γ), by simp only [ne_eq, hvz]; exact p.2⟩
  have hRA : IsRAct act :=
    ⟨fun p => Subtype.ext (Prod.ext (hR.1 _) (hR.1 _)),
     fun p γ δ => Subtype.ext (Prod.ext (hR.2 _ _ _) (hR.2 _ _ _))⟩
  have h1 : IsFam act 2 (fun p => wp N p.1.1) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.1) 2 (wp N) (fun _ _ => rfl) (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1
  have h2 : IsFam act 2 (fun p => wp N p.1.2) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.2) 2 (wp N) (fun _ _ => rfl) (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1
  have hsub := ((GlobalTheory.QFam.isFam_algebra ι act).2.1 2 _ _ h1 h2).2
  have hfam : IsFam act ((2 : ℕ) : ℤ) (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    have := (GlobalTheory.QFam.isFam_algebra ι act).2.2.1 2 ((N : ℂ) ^ 2) _ hsub
    simpa using this
  let R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  have hmem : ∀ z : ℂ, z ∈ R ↔ IsIntegral ℤ z := fun z => by
    simp [R, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  have hNx : ∀ v : Fin 2 → ZMod N, N • v = 0 := fun v => by
    funext i; simp [nsmul_eq_mul, ZMod.natCast_self]
  have hQ : ∀ p : ι, QAll (· ∈ R) N (fun τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    intro p
    refine ⟨fun n => (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n), ?_, fun n => ?_⟩
    · exact (GlobalTheory.QFam.hasQ_linear N).2.2.1 _ _ _ ((GlobalTheory.QFam.hasQ_linear N).2.1 _ _ _ _ (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N _) (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N _))
    · show (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) ∈ R
      rw [hmem]
      have e : (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) =
          (N : ℂ) ^ 2 * cB N p.1.1 n - (N : ℂ) ^ 2 * cB N p.1.2 n := by
        simp only [cP, if_neg p.2.1, if_neg p.2.2]; ring
      rw [e]
      exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N p.1.1 n (NeZero.pos N) (hNx _)).1.sub
        (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N p.1.2 n (NeZero.pos N) (hNx _)).1
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hT := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act 2 N (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) R τ ω
    (NeZero.pos N) hRA.actBij hfam hQ hjR hω ⟨(x, y), hx, hy⟩
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ ((r : ℂ)) := (hmem _).1 r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).1 h⟩
  exact isIntegral_trans _ hT

end GlobalTheory.WpFam
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  first | exact @GlobalTheory.WpFam.TauVal.main | exact GlobalTheory.WpFam.TauVal.main | (intros; apply GlobalTheory.WpFam.TauVal.main <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.CoverCurv

theorem curv_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ t : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, CurvGe C (G + k • H) t := by
  intro n Y _ _ _ _ _ ι La _ A C H G hH t
  have hk : ∀ a : Fin C.m, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ v ∈ Metric.closedBall (C.c a) (C.r a),
      ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤
        A.leviAt (C.idx a) (A.ph (G + k • H) (C.idx a)) ((A.chart (C.idx a)).symm v) ξ :=
    fun a => GlobalTheory.T.leviAt_weight_add_nsmul_large_on_compact n Y ι La A H G hH (C.idx a) _ t
      (isCompact_closedBall (C.c a) (C.r a)) (C.sub a)
  choose k0 hk0 using hk
  refine ⟨Finset.univ.sup k0, fun k hk a v hv ξ => ?_⟩
  exact hk0 a k (le_trans (Finset.le_sup (Finset.mem_univ a)) hk) v
    (Metric.ball_subset_closedBall hv) ξ

end GlobalTheory.OTY.CoverCurv
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.formallyUnramified_homWithFixedPullback_scheme : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B → FormallyUnramified R.π := by
  first | exact @GlobalTheory.EndLoc.formallyUnramified_homFixRep | exact GlobalTheory.EndLoc.formallyUnramified_homFixRep | (intros; apply GlobalTheory.EndLoc.formallyUnramified_homFixRep; all_goals assumption)
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, (∀ n, ghost p O n a = 0) → Sandwich.mu ε ∣ a := by
  first | exact @GlobalTheory.GhostKer.mu_dvd_of_ghost | exact GlobalTheory.GhostKer.mu_dvd_of_ghost | (intros; apply GlobalTheory.GhostKer.mu_dvd_of_ghost <;> assumption)
end
