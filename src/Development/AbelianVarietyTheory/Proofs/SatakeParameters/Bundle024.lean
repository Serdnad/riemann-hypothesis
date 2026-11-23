module

import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.MemMaxVAIff
public import Formalism.SatakeDualWeyl.Bundle001
import ReciprocityTheory.SemistableReduction.Bundle018
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.Hk3.Inh

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  apply Formalism.IndefR.LocBrg.two_val <;> assumption




section Main

variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ}







end Main

section Laurent

end Laurent

end GlobalTheory.Hk3.Inh

end
end

section

noncomputable section
namespace GlobalTheory.Hk3.LatModel
open Classical

section Abstract
variable {W G : Type} [AddCommGroup W] [Group G]

end Abstract

section Concrete
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  apply Formalism.IndefR.LocBrg.two_val <;> assumption

end Concrete

end GlobalTheory.Hk3.LatModel
end
end

section

namespace GlobalTheory.ExistsSmulMem

theorem exists_smul_mem {E : Type} [inst : Field E] [NumberField E] {N : ℕ}
    (Lb : Submodule (NumberField.RingOfIntegers E) (Fin N → E))
    (h : Submodule.span E (↑Lb : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • v ∈ Lb := by
  apply ReciprocityTheory.MultiplicativeHeights.sc_scale <;> assumption

end GlobalTheory.ExistsSmulMem
end

section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

noncomputable section
namespace GlobalTheory.NCyc.StrictLocLift

theorem lift_unique {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (g₁ g₂ : Q →+* T)
    (h₁ : g₁.comp tQ = b) (h₂ : g₂.comp tQ = b)
    (h : (residue T).comp g₁ = (residue T).comp g₂) : g₁ = g₂ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let G₁ : Q →ₐ[R] T := { g₁ with commutes' := fun r => DFunLike.congr_fun h₁ r }
  let G₂ : Q →ₐ[R] T := { g₂ with commutes' := fun r => DFunLike.congr_fun h₂ r }
  have := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).1 (a₁ := G₁) (a₂ := G₂) (by
    ext q; exact DFunLike.congr_fun h q)
  ext q; exact DFunLike.congr_fun this q

theorem lift_exists {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (ψ : Q →+* ResidueField T)
    (hψ : ψ.comp tQ = (residue T).comp b) :
    ∃ g : Q →+* T, g.comp tQ = b ∧ (residue T).comp g = ψ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let Ψ : Q →ₐ[R] ResidueField T := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  obtain ⟨G, hG⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).2 Ψ
  refine ⟨G.toRingHom, RingHom.ext fun r => G.commutes r, RingHom.ext fun q => ?_⟩
  exact DFunLike.congr_fun hG q

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isIndEtale {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [HenselianLocalRing T]
    (a : R →+* S) (b : R →+* T) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale a) (ψ : S →+* ResidueField T)
    (hψ : ψ.comp a = (residue T).comp b) : ∃ g : S →+* T, g.comp a = b := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := ha
  have hts' : ∀ j, (s.app j).hom.comp (t.app j).hom = a := fun j => by
    have := congrArg CommRingCat.Hom.hom (hts j).2
    simpa using this
  have hψj : ∀ j, (ψ.comp (s.app j).hom).comp (t.app j).hom = (residue T).comp b := fun j => by
    rw [RingHom.comp_assoc, hts' j, hψ]
  choose g hg using fun j => lift_exists (t.app j).hom (hts j).1 b (ψ.comp (s.app j).hom) (hψj j)
  have nat : ∀ {j k : J} (u : j ⟶ k), (g k).comp (D.map u).hom = g j := by
    intro j k u
    have ht : (D.map u).hom.comp (t.app j).hom = (t.app k).hom := by
      have := congrArg CommRingCat.Hom.hom (t.naturality u)
      simpa using this.symm
    have hs' : (s.app k).hom.comp (D.map u).hom = (s.app j).hom := by
      have e : D.map u ≫ s.app k = s.app j := by
        have := s.naturality u
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        exact this
      have := congrArg CommRingCat.Hom.hom e
      rwa [CommRingCat.hom_comp] at this
    apply lift_unique (t.app j).hom (hts j).1 b
    · rw [RingHom.comp_assoc, ht, (hg k).1]
    · exact (hg j).1
    · rw [← RingHom.comp_assoc, (hg k).2, RingHom.comp_assoc, hs', (hg j).2]
  let c : Cocone D :=
    { pt := CommRingCat.of T
      ι := { app := fun j => CommRingCat.ofHom (g j)
             naturality := fun j k u => by
               ext q
               simpa using DFunLike.congr_fun (nat u) q } }
  refine ⟨(hs.desc c).hom, ?_⟩
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  have hf : (hs.desc c).hom.comp (s.app j).hom = g j := by
    have := congrArg CommRingCat.Hom.hom (hs.fac c j)
    simpa [c] using this
  rw [← hts' j, ← RingHom.comp_assoc, hf, (hg j).1]

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isStrictHenselisation {R S T : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [CommRing T] [HenselianLocalRing T] [IsSepClosed (ResidueField T)]
    (a : R →+* S) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation a) (b : R →+* T) [IsLocalHom b] :
    ∃ g : S →+* T, g.comp a = b := by
  letI : Algebra R S := a.toAlgebra
  haveI : IsLocalHom (algebraMap R S) := ha.2.2.1
  obtain ⟨-, -, hsep⟩ := GlobalTheory.IndEtaleLocal.flat_map_maximalIdeal_isSeparable R S ha.2.2.2
  letI : Algebra (ResidueField R) (ResidueField T) := (ResidueField.map b).toAlgebra
  let ι : ResidueField S →ₐ[ResidueField R] ResidueField T := IsSepClosed.lift
  refine exists_ringHom_of_isIndEtale a b ha.2.2.2 (ι.toRingHom.comp (residue S)) (RingHom.ext fun r => ?_)
  have h1 : residue S (a r) = algebraMap (ResidueField R) (ResidueField S) (residue R r) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [h1, ι.commutes]
  rfl

end GlobalTheory.NCyc.StrictLocLift
end
end

section


theorem _root_.GlobalTheory.T.isIndEtale_over_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W] [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O] [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := by
  first | (exact @GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale) | (exact GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale) | (intros; apply GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale  <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_local_subring_monic_roots_residue : ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) (R : Subring K) (𝔪 : Ideal R),
    φ.range ≤ R → 𝔪.IsMaximal → (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) →
    (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) → (∀ x : K, IsIntegral R x → x ∈ R) →
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  first | (exact @GlobalTheory.LocInField.exists_local_subring) | (exact GlobalTheory.LocInField.exists_local_subring) | (intros; apply GlobalTheory.LocInField.exists_local_subring  <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.AugmentationEigenvector

section General

variable {K X Y : Type} [Group K] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

def aug (ψ : K →* ℂˣ) : MonoidAlgebra ℂ K →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ K ((Units.coeHom ℂ).comp ψ)

theorem aug_single (ψ : K →* ℂˣ) (g : K) (r : ℂ) :
    aug ψ (MonoidAlgebra.single g r) = r * (ψ g : ℂ) := by
  simp [aug]

theorem act_eigen (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (y : X)
    (hy : ∀ g, σ g y = (ψ g : ℂ) • y) (c : MonoidAlgebra ℂ K) :
    σ.asAlgebraHom c y = aug ψ c • y := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, ha, hb, add_smul]
  | single g r => rw [aug_single, Representation.asAlgebraHom_single, LinearMap.smul_apply, hy, smul_smul]

theorem act_comm (σ : Representation ℂ K X) (τ : Representation ℂ K Y) (f : X →ₗ[ℂ] Y)
    (hf : ∀ g x, f (σ g x) = τ g (f x)) (c : MonoidAlgebra ℂ K) (x : X) :
    f (σ.asAlgebraHom c x) = τ.asAlgebraHom c (f x) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  | single g r => simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul, hf]

theorem exists_kill [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (hσ : IsSmooth σ) (hψ : IsSmoothChar ψ)
    (h0 : ∀ z, (∀ g, σ g z = (ψ g : ℂ) • z) → z = 0) (z : X) :
    ∃ c, aug ψ c ≠ 0 ∧ σ.asAlgebraHom c z = 0 := by
  classical
  let π := twist σ ψ⁻¹
  have hπ : IsSmooth π := isSmooth_twist hσ hψ.inv
  have hlc : IsLocallyConstant fun g : K => π g z := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h : {g : K | π g z = z} ∈ nhds ((fun y => x⁻¹ * y) x) :=
      IsOpen.mem_nhds (hπ z) (by simp)
    filter_upwards [(continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds h] with y hy
    have hy' : π (x⁻¹ * y) z = z := hy
    calc π y z = π x (π (x⁻¹ * y) z) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = π x z := by rw [hy']
  have hfin := hlc.range_finite
  let O : Finset X := hfin.toFinset
  have hO : ∀ w, w ∈ O ↔ ∃ g, π g z = w := fun w => by simp [O]
  have hmem : ∀ g, ∀ w ∈ O, π g w ∈ O := fun g w hw => by
    obtain ⟨x, rfl⟩ := (hO w).1 hw
    exact (hO _).2 ⟨g * x, by rw [map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ g, π g (∑ w ∈ O, w) = ∑ w ∈ O, w := fun g => by

    rw [map_sum]
    refine Finset.sum_nbij' (fun w => π g w) (fun w => π g⁻¹ w) (hmem g) (hmem g⁻¹)
      (fun w _ => ?_) (fun w _ => ?_) (fun _ _ => rfl)
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hz : ∑ w ∈ O, w = 0 := h0 _ fun g => by
    have h1 := hinv g
    have h2 : π g (∑ w ∈ O, w) = ((ψ g)⁻¹ : ℂˣ).val • σ g (∑ w ∈ O, w) := rfl
    rw [h2] at h1
    conv_rhs => rw [← h1]
    rw [smul_smul, Units.mul_inv, one_smul]
  choose s hs using fun w : O => (hO w).1 w.2
  refine ⟨∑ w : O, MonoidAlgebra.single (s w) ((ψ (s w))⁻¹ : ℂˣ).val, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [aug_single, Units.inv_mul]
    have : O.Nonempty := ⟨z, (hO z).2 ⟨1, by simp⟩⟩
    simpa using this.ne_empty
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, ← hz, ← Finset.sum_coe_sort O]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
    exact hs w

end General

section Tensor

variable {β : Type} [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (Γ j) (X j)) (a : β) {K : Type} [Group K]
  (i : K →* Γ a)

def viaFactor : Representation ℂ K (⨂[ℂ] j, X j) :=
  (piTensor ρ).comp ((MonoidHom.mulSingle Γ a).comp i)

theorem viaFactor_tprod (x : ∀ j, X j) (g : K) (z : X a) :
    viaFactor ρ a i g (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a (i g) z)) := by
  show piTensor ρ (Pi.mulSingle a (i g)) _ = _
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]

theorem viaFactor_alg (x : ∀ j, X j) (c : MonoidAlgebra ℂ K) (z : X a) :
    (viaFactor ρ a i).asAlgebraHom c (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ
        (Function.update x a (Representation.asAlgebraHom ((ρ a).comp i) c z)) :=
  (act_comm ((ρ a).comp i) (viaFactor ρ a i) ((PiTensorProduct.tprod ℂ).toLinearMap x a)
    (fun g z => (viaFactor_tprod ρ a i x g z).symm) c z).symm

theorem exists_kill_tensor (ψ : K →* ℂˣ)
    (h : ∀ z, ∃ c, aug ψ c ≠ 0 ∧ Representation.asAlgebraHom ((ρ a).comp i) c z = 0)
    (v : ⨂[ℂ] j, X j) (b : MonoidAlgebra ℂ K) :
    ∃ c, aug ψ c ≠ 0 ∧
      (viaFactor ρ a i).asAlgebraHom c ((viaFactor ρ a i).asAlgebraHom b v) = 0 := by
  induction v using PiTensorProduct.induction_on generalizing b with
  | smul_tprod r x =>
    obtain ⟨c, hc, hc'⟩ := h (Representation.asAlgebraHom ((ρ a).comp i) b (x a))
    refine ⟨c, hc, ?_⟩
    rw [← Function.update_eq_self a x, map_smul, map_smul, viaFactor_alg, viaFactor_alg, hc',
      MultilinearMap.map_update_zero, smul_zero]
  | add v w hv hw =>
    obtain ⟨c, hc, hc'⟩ := hv b
    obtain ⟨d, hd, hd'⟩ := hw (c * b)
    refine ⟨d * c, by rw [map_mul]; exact mul_ne_zero hd hc, ?_⟩
    rw [map_mul, Module.End.mul_apply] at hd'
    rw [map_mul, Module.End.mul_apply, map_add (f := _), map_add (f := _), hc', zero_add, hd']

end Tensor

theorem exists_eigenvector (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type)
    [(j : β) → Fintype (m j)] [(j : β) → DecidableEq (m j)] (X : β → Type)
    [(j : β) → AddCommGroup (X j)] [(j : β) → Module ℂ (X j)]
    (ρ : (j : β) → Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y)
    (hρ : ∀ j, IsSmooth (ρ j)) (hχ : IsSmoothChar χ) (hs : IsSubquotient τ (piTensor ρ))
    (hy : y ≠ 0)
    (he : ∀ g ∈ KO k (m a),
      τ (Pi.mulSingle a g) y = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • y) :
    ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a),
      ρ a g z = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • z := by
  by_contra hne
  haveI : CompactSpace (KO k (m a)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  let i := (KO k (m a)).subtype
  let ψ : KO k (m a) →* ℂˣ := χ.comp (Matrix.GeneralLinearGroup.det.comp i)
  have hψ : IsSmoothChar ψ :=
    hχ.comp _ (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  have h1 := exists_kill ((ρ a).comp i) ψ (isSmooth_comp (hρ a) i continuous_subtype_val) hψ
    fun z hz => by
      by_contra h
      exact hne ⟨z, h, fun g hg => hz ⟨g, hg⟩⟩
  obtain ⟨S, f, hf⟩ := hs
  obtain ⟨v, rfl⟩ := hf y
  obtain ⟨c, hc, hc'⟩ := exists_kill_tensor ρ a i ψ h1 v.1 1
  rw [map_one, Module.End.one_apply] at hc'
  let e : KO k (m a) →* Levi k m := (MonoidHom.mulSingle (fun j => GL (m j) k) a).comp i
  have h2 := act_comm (S.toRepresentation.comp e) (viaFactor ρ a i) S.toSubmodule.subtype
    (fun _ _ => rfl) c v
  have h3 : Representation.asAlgebraHom (S.toRepresentation.comp e) c v = 0 :=
    Subtype.ext (h2.trans hc')
  have h4 := act_comm (S.toRepresentation.comp e) (τ.comp e) f.toLinearMap
    (fun g x => f.isIntertwining _ _ (e g) x) c v
  rw [h3, map_zero, act_eigen (τ.comp e) ψ (f.toLinearMap v) (fun g => he g.1 g.2)] at h4
  exact hy ((smul_eq_zero.1 h4.symm).resolve_left hc)

end GlobalTheory.AugmentationEigenvector
end
end

section

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.OmTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ χ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om (μ * χ) g h Φ =
      (((χ (Matrix.GeneralLinearGroup.det g)) * (χ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) •
        om μ g h Φ := by
  funext x
  simp only [om, MonoidHom.mul_apply, Pi.smul_apply, smul_eq_mul, Units.val_mul, mul_inv]
  ring

theorem tmap_twist {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) (χ : kˣ →* ℂˣ)
    (g : GL (Fin r) k) (h : GL (Fin n) k) :
    TensorProduct.map (twist σ (detChar (Fin r) χ) g) (twist τ (detChar (Fin n) χ⁻¹) h) =
      (((χ (Matrix.GeneralLinearGroup.det g)) * (χ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) •
        TensorProduct.map (σ g) (τ h) := by
  apply TensorProduct.ext'
  intro v w
  simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]

theorem omQuot_mul {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (μ χ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W)
    (hq : OmQuot μ σ τ) :
    OmQuot (μ * χ) (twist σ (detChar (Fin r) χ)) (twist τ (detChar (Fin n) χ⁻¹)) := by
  obtain ⟨f, hf0, hf⟩ := hq
  refine ⟨f, hf0, fun g h Φ Φ' hΦ' => ?_⟩
  set c : ℂˣ := χ (Matrix.GeneralLinearGroup.det g) * (χ (Matrix.GeneralLinearGroup.det h))⁻¹ with hc
  let Ψ : SB (Matrix (Fin n) (Fin r) k) := ((c⁻¹ : ℂˣ) : ℂ) • Φ'
  have hΨ : (Ψ : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ := by
    show ((c⁻¹ : ℂˣ) : ℂ) • (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = _
    rw [hΦ', om_mul, ← hc, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hΦΨ : Φ' = (c : ℂ) • Ψ := by
    show Φ' = (c : ℂ) • (((c⁻¹ : ℂˣ) : ℂ) • Φ')
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  rw [tmap_twist, ← hc, hΦΨ, map_smul, hf g h Φ Ψ hΨ, LinearMap.smul_apply]

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), OmQuot μ σ τ ↔ OmQuot 1 (twist σ (detChar (Fin r) μ⁻¹)) (twist τ (detChar (Fin n) μ)) := by
  intro k _ _ _ _ r n μ V W _ _ _ _ σ τ
  constructor
  · intro hq
    have := omQuot_mul μ μ⁻¹ σ τ hq
    rwa [mul_inv_cancel, inv_inv] at this
  · intro hq
    have := omQuot_mul 1 μ _ _ hq
    have e1 : detChar (Fin r) μ * detChar (Fin r) μ⁻¹ = (1 : GL (Fin r) k →* ℂˣ) := by
      ext g; simp
    have e2 : detChar (Fin n) μ⁻¹ * detChar (Fin n) μ = (1 : GL (Fin n) k →* ℂˣ) := by
      ext g; simp
    rwa [one_mul, twist_twist, twist_twist, e1, e2, twist_one, twist_one] at this

end GlobalTheory.OmTwist
end
end
