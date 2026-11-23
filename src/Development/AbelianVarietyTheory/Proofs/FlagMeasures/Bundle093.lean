module

public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle086
public import ReciprocityTheory.Automorphisms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralIdempotentSplitPlaceCmFiniteAdeles
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem adForm_from_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (ι : Type) [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W) (Jm : W →ₗ⋆[ℂ] (Frames (gramC J emb) → ℂ)), (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ (h : Gf) (hk : h ∈ K) (hy : ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U), ((ψ ⟨h, hk⟩ : ℂˣ) : ℂ) = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ)) → (∀ γ : Γ, ∃ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J ∧ (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ (γ : Γ) (g : GL (Fin n) E), (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g → ∀ (ξ : W) (y y' : Frames (gramC J emb)), IsTr (atInf emb g.1) y' y → Jm (π (ιi γ) ξ) y = Jm ξ y') → Function.Injective Jm → (∀ p ∈ ValC (gramC J emb) lam, ∃ ξ, Jm ξ = p) → ∀ g ∈ AdForms S emb lam, ∃ φ : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) ∧ ∀ y : UPts σ J (FiniteAdeleRing (𝓞 F) F), g y = Jm (φ (Φ.symm (y * h0⁻¹))) := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gi Gf _ _ _ ιi ιf K ψ Φ h0 ι _ emb lam W _ _ π Jm
    hψ hK hχ hrat hint hinj hsurj g hg

  have hval : ∀ z, g z ∈ ValC (gramC J emb) lam := fun z => (Submodule.mem_inf.mp hg).2 z (Set.mem_univ z)
  have hfun := (Submodule.mem_inf.mp hg).1
  choose pre hpre using fun z => hsurj (g z) (hval z)
  refine ⟨fun x => pre (Φ x * h0), ?_, ?_⟩
  · intro γ x κ
    obtain ⟨gr, hgrU, hgr⟩ := hrat γ
    apply hinj
    rw [hpre, LinearMap.map_smulₛₗ]
    funext y
    obtain ⟨y', hy'⟩ := exists_isTr' emb gr y
    rw [Pi.smul_apply, hint γ gr hgr (pre (Φ x * h0)) y y' hy', hpre]

    have hconj : (starRingEnd ℂ) ((((ψ κ)⁻¹ : ℂˣ) : ℂ)) = ((ψ κ : ℂˣ) : ℂ) := by
      rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hψ κ), Complex.conj_conj]
    rw [smul_eq_mul, hconj]
    have hk : ((h0⁻¹ * Φ κ.1 * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U :=
      (hK κ.1).1 κ.2
    have hx : (Φ (ιf γ * x * κ.1) * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) =
        Φ (ιf γ) * (Φ x * h0) * (h0⁻¹ * Φ κ.1 * h0) := by
      simp only [map_mul]; group
    have key := hfun gr hgrU (Φ x * h0) (Φ (ιf γ * x * κ.1) * h0) ⟨_, hk⟩
      (by rw [hx, Subgroup.coe_mul, Subgroup.coe_mul, hgr]) y y' hy'
    rw [key, ← hχ κ.1 κ.2 hk]
  · intro y
    rw [hpre]
    congr 1
    simp

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.ProdCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {M n : ℕ}

noncomputable def glueTup (Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E)) :
    Fin n → Fin M → AF F ⊗[F] E :=
  fun a i => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y.1 a i) k)
      ((Algebra.TensorProduct.basis (Af F) b).repr (Y.2 a i) k)

theorem continuous_glueTup : Continuous (glueTup (F := F) (E := E) b (M := M) (n := n)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _
  have hs : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap
  have hi : Continuous (Algebra.TensorProduct.basis (Ainf F) b).equivFun :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toLinearMap
  have hf : Continuous (Algebra.TensorProduct.basis (Af F) b).equivFun :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (Af F) b).equivFun.toLinearMap
  refine continuous_pi fun a => continuous_pi fun i => hs.comp (continuous_pi fun k => ?_)
  have h1 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) =>
      (Algebra.TensorProduct.basis (Ainf F) b).equivFun (Y.1 a i) k :=
    (continuous_apply k).comp (hi.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_fst)))
  have h2 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) =>
      (Algebra.TensorProduct.basis (Af F) b).equivFun (Y.2 a i) k :=
    (continuous_apply k).comp (hf.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_snd)))
  exact (h1.prodMk h2 :)

theorem glueTup_proj (X : Fin n → Fin M → AF F ⊗[F] E) :
    glueTup b (projInf X, projFin X) = X := by
  funext a i
  refine GlobalTheory.GaugeGlue.tens_ext b fun k => ?_
  simp only [glueTup]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [projInf, projFin, Module.Basis.equivFun_apply, GlobalTheory.GaugeGlue.repr_map]
  rfl

end GlobalTheory.ProdCont


open GlobalTheory.ProdCont in
theorem GlobalTheory.prod_continuous_hasCompactSupport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n : ℕ) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ), Continuous Φi → HasCompactSupport Φi → Continuous Φf → HasCompactSupport Φf → IsProdInfFin Φ Φi Φf → Continuous Φ ∧ HasCompactSupport Φ := by
  intro F E _ _ _ _ _ M n Φ Φi Φf hci hki hcf hkf hΦ
  haveI : FiniteDimensional F E := inferInstance
  let b := Module.finBasis F E
  have hpf : Continuous (projFin (F := F) (E := E) (M := M) (n := n)) :=
    continuous_pi fun a => continuous_pi fun i =>
      (GlobalTheory.GaugeGlue.continuous_map b (sndA F) GlobalTheory.GaugeGlue.continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a))
  have hpi := GlobalTheory.GaugeGlue.continuous_projInf (F := F) (E := E) (M := M) (n := n) b
  have hEq : Φ = fun X => Φi (projInf X) * Φf (projFin X) := funext hΦ
  refine ⟨hEq ▸ (hci.comp hpi).mul (hcf.comp hpf), ?_⟩
  have hg : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X) :=
    hpi.prodMk hpf
  have hK : IsCompact (tsupport Φi ×ˢ tsupport Φf) := hki.isCompact.prod hkf.isCompact
  have hsub : tsupport Φ ⊆ (fun X => (projInf X, projFin X)) ⁻¹' (tsupport Φi ×ˢ tsupport Φf) := by
    refine closure_minimal (fun X hX => ?_)
      ((isClosed_tsupport Φi).prod (isClosed_tsupport Φf) |>.preimage hg)
    have h0 : Φi (projInf X) * Φf (projFin X) ≠ 0 := by rw [← hΦ]; exact hX
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul h0), subset_tsupport _ (right_ne_zero_of_mul h0)⟩
  have hsub2 : tsupport Φ ⊆ glueTup b '' (tsupport Φi ×ˢ tsupport Φf) := fun X hX =>
    ⟨_, hsub hX, glueTup_proj b X⟩
  exact (hK.image (continuous_glueTup b)).of_isClosed_subset (isClosed_tsupport Φ) hsub2
end

section

open NumberField

theorem _root_.GlobalTheory.T.finite_lattices_between_of_smul_le' : ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N → {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  first | exact @GlobalTheory.finite_lattices_between_of_smul_le | exact GlobalTheory.finite_lattices_between_of_smul_le | (intros; apply GlobalTheory.finite_lattices_between_of_smul_le <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_integralIdempotent_splitPlace_cmFiniteAdeles : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L), ∃ ε : ReciprocityTheory.Aut.AL L, ε * ε = ε ∧ ε * ReciprocityTheory.Aut.conjAL L ε = 0 ∧ ε ∈ ReciprocityTheory.Aut.ALint L ∧ s.proj ε = 1 ∧ ReciprocityTheory.Aut.compAt L s.v (ε + ReciprocityTheory.Aut.conjAL L ε) = 1 ∧ ∀ v, v ≠ s.v → ReciprocityTheory.Aut.compAt L v ε = 0 ∧ ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L ε) = 0 := by
  first | exact @GlobalTheory.SplitIdem.exists_idem | exact GlobalTheory.SplitIdem.exists_idem | (intros; apply GlobalTheory.SplitIdem.exists_idem <;> assumption)
end
