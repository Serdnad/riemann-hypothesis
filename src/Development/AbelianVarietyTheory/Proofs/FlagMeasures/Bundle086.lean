module

public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.BVRApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Mathlib.NumberTheory.NumberField.Basic
public import Formalism.HermitianLattices.FinalNeighbourConstruct
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ClassDict

theorem exu_rep {G Γ Gf : Type} [Group G] [Group Γ] [Group Gf] (P R U : Subgroup G) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (Φ : Gf ≃* P) (h0 : P)
    (hK : ∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : P) : G) ∈ U)
    (h1 : ∀ γ : Γ, (Φ (ιf γ)).1 ∈ R) (h2 : ∀ r ∈ R, ∃ γ : Γ, (Φ (ιf γ)).1 = r)
    {C : Type} (yc : C → P)
    (hb : Function.Bijective
      (fun c => (Quotient.mk'' (yc c) : ClassSet (R.subgroupOf P) (U.subgroupOf P)))) (h : Gf) :
    ∃! c : C, ∃ (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf) := by
  have key : ∀ a b : P, (Quotient.mk'' a : ClassSet (R.subgroupOf P) (U.subgroupOf P)) = Quotient.mk'' b ↔
      ∃ x ∈ R.subgroupOf P, ∃ y ∈ U.subgroupOf P, b = x * a * y := fun a b => @DoubleCoset.eq _ _ _ _ a b
  have fwd : ∀ (c : C) (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf) →
      (Quotient.mk'' (yc c) : ClassSet (R.subgroupOf P) (U.subgroupOf P)) = Quotient.mk'' (Φ h * h0) := by
    intro c γ κ hc
    rw [key]
    refine ⟨Φ (ιf γ), ?_, h0⁻¹ * Φ κ * h0, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact h1 γ
    · rw [Subgroup.mem_subgroupOf]
      exact (hK κ).1 κ.2
    · simp only [hc, map_mul, MulEquiv.apply_symm_apply, mul_assoc]
  obtain ⟨c, hc⟩ := hb.2 (Quotient.mk'' (Φ h * h0))
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := (key _ _).1 hc
    rw [Subgroup.mem_subgroupOf] at hx hy
    obtain ⟨γ, hγ⟩ := h2 _ hx
    have hκ : Φ.symm (h0 * y * h0⁻¹) ∈ K := by
      rw [hK, MulEquiv.apply_symm_apply]
      have e : h0⁻¹ * (h0 * y * h0⁻¹) * h0 = y := by group
      rw [e]
      exact hy
    refine ⟨γ, ⟨_, hκ⟩, ?_⟩
    apply Φ.injective
    have hγ' : Φ (ιf γ) = x := Subtype.ext hγ
    have hΦ : Φ h = x * yc c * y * h0⁻¹ := by
      rw [← hxy]
      group
    simp only [map_mul, MulEquiv.apply_symm_apply, hγ', hΦ]
    group
  · rintro c' ⟨γ, κ, hc'⟩
    exact hb.1 ((fwd c' γ κ hc').trans hc.symm)

theorem stab_triv {G Γ Gf : Type} [Group G] [Group Γ] [Group Gf] (P U : Subgroup G) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (Φ : Gf ≃* P) (h0 : P)
    (hK : ∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : P) : G) ∈ U)
    (hn : ∀ (x : Gf) (γ : Γ), x⁻¹ * ιf γ * x ∈ K → γ = 1) (y : P) (γ : Γ)
    (hγ : (Φ (ιf γ)).1 ∈ U.map (MulAut.conj y.1).toMonoidHom) : (Φ (ιf γ)).1 = 1 := by
  obtain ⟨u, hu, hyu⟩ := Subgroup.mem_map.1 hγ
  have e : ((Φ (ιf γ) : P) : G) = (y : G) * u * (y : G)⁻¹ := by
    rw [← hyu]
    simp [MulAut.conj_apply]
  have hmem : (Φ.symm (y * h0⁻¹))⁻¹ * ιf γ * Φ.symm (y * h0⁻¹) ∈ K := by
    rw [hK]
    convert hu using 1
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    push_cast
    rw [e]
    group
  rw [hn _ _ hmem]
  simp

theorem bc_inj_of_inj {A B : Type} [CommRing A] [CommRing B] {k : ℕ} {φ : A →+* B}
    (hφ : Function.Injective φ) : Function.Injective (bc (n := Fin k) φ) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  funext i j
  exact hφ (congrFun (congrFun h' i) j)

theorem finAdele_algebraMap_inj (F : Type) [Field F] [NumberField F] :
    Function.Injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  have : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
    rw [← map_zero (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_one (algebraMap F (FiniteAdeleRing (𝓞 F) F))] at h'
    simp only [FiniteAdeleRing.algebraMap_apply] at h'
    rw [HeightOneSpectrum.adicCompletion.coe_zero, HeightOneSpectrum.adicCompletion.coe_one] at h'
    exact zero_ne_one h'
  exact (algebraMap F _).injective

theorem classReps_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gf : Type) [Group Γ] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)), (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ γ : Γ, ∃ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J ∧ (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J → ∃ γ : Γ, (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → ∀ (C : Type) (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → (∀ h : Gf, ∃! c : C, ∃ (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf)) ∧ ((∀ (x : Gf) (γ : Γ), x⁻¹ * ιf γ * x ∈ K → γ = 1) → ∀ (c : C) (g : GL (Fin n) E), g ∈ UJ (σ : E →+* E) J → bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → g = 1) := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gf _ _ ιf K Φ h0 hK h1 h2 C yc hb
  have hR1 : ∀ γ : Γ, (Φ (ιf γ)).1 ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F) := by
    intro γ
    obtain ⟨g, hg, hgγ⟩ := h1 γ
    rw [hgγ]
    unfold ratPts
    exact Subgroup.mem_map_of_mem _ hg
  have hR2 : ∀ r ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ γ : Γ, (Φ (ιf γ)).1 = r := by
    intro r hr
    unfold ratPts at hr
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hr
    exact h2 g hg
  refine ⟨fun h => exu_rep _ _ S.U ιf K Φ h0 hK hR1 hR2 yc hb h, fun hn c g hg hgU => ?_⟩
  obtain ⟨γ, hγ⟩ := h2 g hg
  have hs := stab_triv _ S.U ιf K Φ h0 hK hn (yc c) γ (by rw [hγ]; exact hgU)
  rw [hγ] at hs
  have hinj : Function.Injective (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) := by
    intro a b hab
    exact Algebra.TensorProduct.includeLeft_injective (S := F) (finAdele_algebraMap_inj F) hab
  exact bc_inj_of_inj hinj (hs.trans (map_one _).symm)

end GlobalTheory.ClassDict
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem adForms_of_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (ι : Type) [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W) (Jm : W →ₗ⋆[ℂ] (Frames (gramC J emb) → ℂ)), (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ (h : Gf) (hk : h ∈ K) (hy : ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U), ((ψ ⟨h, hk⟩ : ℂˣ) : ℂ) = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ)) → (∀ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J → ∃ γ : Γ, (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ (γ : Γ) (g : GL (Fin n) E), (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g → ∀ (ξ : W) (y y' : Frames (gramC J emb)), IsTr (atInf emb g.1) y' y → Jm (π (ιi γ) ξ) y = Jm ξ y') → (∀ ξ, Jm ξ ∈ ValC (gramC J emb) lam) → ∀ φ : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (fun y : UPts σ J (FiniteAdeleRing (𝓞 F) F) => Jm (φ (Φ.symm (y * h0⁻¹)))) ∈ AdForms S emb lam := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gi Gf _ _ _ ιi ιf K ψ Φ h0 ι _ emb lam W _ _ π Jm hψ hK hχ hΓ hJ hV φ hφ
  refine Submodule.mem_inf.2 ⟨?_, fun x _ => hV _⟩
  intro g hg x x' κ hx y y' hy
  obtain ⟨γ, hγ⟩ := hΓ g hg
  let κ' : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩
  let k : Gf := Φ.symm (h0 * κ' * h0⁻¹)
  have hk1 : h0⁻¹ * Φ k * h0 = κ' := by
    simp only [k, MulEquiv.apply_symm_apply]; group
  have hy1 : ((h0⁻¹ * Φ k * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U := by
    rw [hk1]; exact κ.2
  have hk : k ∈ K := (hK k).2 hy1
  have hc : ((ψ ⟨k, hk⟩ : ℂˣ) : ℂ) = ((S.chi κ : ℂˣ) : ℂ) := by
    rw [hχ k hk hy1]
    congr 2
    apply Subtype.ext
    show ((h0⁻¹ * Φ k * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = κ.1
    rw [hk1]
  have hx' : x' = Φ (ιf γ) * x * κ' := by
    apply Subtype.ext
    rw [hx, ← hγ]; rfl
  have hdec : Φ.symm (x' * h0⁻¹) = ιf γ * Φ.symm (x * h0⁻¹) * ((⟨k, hk⟩ : K) : Gf) := by
    apply Φ.injective
    simp only [k, map_mul Φ, MulEquiv.apply_symm_apply, hx']
    group
  have hconj : (starRingEnd ℂ) (((ψ ⟨k, hk⟩)⁻¹ : ℂˣ) : ℂ) = ((ψ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
    rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hψ _), Complex.conj_conj]
  show Jm (φ (Φ.symm (x' * h0⁻¹))) y = (S.chi κ : ℂ) * Jm (φ (Φ.symm (x * h0⁻¹))) y'
  rw [hdec, hφ, LinearMap.map_smulₛₗ, hconj, hc, Pi.smul_apply, smul_eq_mul, hJ γ g hγ _ y y' hy]

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.LocalUnitaryHaar

open PI.VolSemiDirect.W.Cj Measure
open scoped NNReal Matrix

theorem stableRankOne_field (K : Type) [Field K] : HasStableRangeOne K := by
  intro a b x y h
  by_cases ha : a = 0
  · refine ⟨1, ?_⟩
    subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      simp at h
    simpa using isUnit_iff_ne_zero.2 hb
  · exact ⟨0, by simpa using isUnit_iff_ne_zero.2 ha⟩

theorem map_mulVec_eq_of_preserves_form {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
    [BorelSpace A] (hA : HasStableRangeOne A) (k : ℕ) (G X : Matrix (Fin k) (Fin k) A)
    (hG : IsUnit G.det) (hXG : X.transpose * G * X = G)
    (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure] : μ.map X.mulVec = μ := by
  have hd := congrArg Matrix.det hXG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hdd : X.det * X.det = 1 := by
    have : (X.det * X.det) * G.det = 1 * G.det := by
      calc (X.det * X.det) * G.det = X.det * G.det * X.det := by ring
        _ = 1 * G.det := by rw [hd, one_mul]
    exact hG.mul_left_inj.1 this
  have hX : IsUnit X.det := ⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩
  let Xu : GL (Fin k) A := Matrix.nonsingInvUnit X hX
  let Gu : GL (Fin k) A := Matrix.nonsingInvUnit G hG
  have hrel : trG Xu * Gu * Xu = Gu := by
    ext1
    exact hXG
  have hm := congrArg modM hrel
  rw [modM_mul, modM_mul, modM_tr_of_mem transvection_preserves_haar Xu (gl_generated_transvections_diag A hA k Xu)] at hm
  have hpos : 0 < modM Gu := addEquivAddHaarChar_pos (phi Gu)
  have hsq : modM Xu * modM Xu = 1 := by
    have : (modM Xu * modM Xu) * modM Gu = 1 * modM Gu := by
      calc (modM Xu * modM Xu) * modM Gu = modM Xu * modM Gu * modM Xu := by ring
        _ = 1 * modM Gu := by rw [hm, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have hmod := nnreal_eq_one_of_mul_self hsq
  have e := map_phi_of_modM Xu hmod μ
  have e2 : (phi Xu : (Fin k → A) → (Fin k → A)) = Matrix.mulVec X := by
    funext v
    rfl
  rw [e2] at e
  exact e

theorem map_lin_eq_of_stableRankOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] (hR1 : HasStableRangeOne R) (g : HA R σ J)
    (μ : Measure (Fin M → R ⊗[F] E)) [μ.IsAddHaarMeasure] :
    μ.map (lin R σ J g) = μ := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  haveI : LocallyCompactSpace (R ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (R ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (R ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  set k := Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E))
  set b := bV F E M
  set bR := bVR F E M R
  set e : (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin k → R) := bR.equivFun
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  have c2 : Continuous e.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap (R := R) _
  let ec : (Fin M → R ⊗[F] E) ≃ₜ+ (Fin k → R) :=
    { e.toAddEquiv with
      continuous_toFun := by simpa using c1
      continuous_invFun := by simpa using c2 }
  have hec : ∀ u, ec u = e u := fun _ => rfl
  have hecs : ∀ x, ec.symm x = e.symm x := fun _ => rfl
  set μ' := μ.map ec
  have hμ' : μ'.IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  let L : (Fin k → R) →ₗ[R] (Fin k → R) :=
    e.toLinearMap ∘ₗ ((lin R σ J g).restrictScalars R) ∘ₗ e.symm.toLinearMap
  set X := LinearMap.toMatrix' L
  have hX : ∀ x, X.mulVec x = e (lin R σ J g (e.symm x)) := fun x =>
    LinearMap.toMatrix'_mulVec L x
  set G0 : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))
  set G := G0.map (algebraMap F R)
  have hGu : IsUnit G.det := by
    have hd : G.det = algebraMap F R G0.det := by
      rw [RingHom.map_det]
      rfl
    rw [hd]
    exact (isUnit_iff_ne_zero.2 (trace_gram_nondegenerate F E σ hCM M J hJ k b)).map _
  have hBG : ∀ i j, Bf σ J (bR i) (bR j) = G i j := by
    intro i j
    rw [bVR_apply, bVR_apply, Bf, trace_basis_holds F E R σ M J]
    rfl
  have key : ∀ x y : Fin k → R, Bf σ J (e.symm x) (e.symm y) = x ⬝ᵥ (G *ᵥ y) := by
    intro x y
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Bf_expand]
    simp only [hBG, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rfl
  have e1 : ∀ u w : Fin k → R, u ⬝ᵥ ((X.transpose * G * X) *ᵥ w) = u ⬝ᵥ (G *ᵥ w) := by
    intro u w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, ← key, hX, hX, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Bf_lin, key]
  have hXG : X.transpose * G * X = G := by
    ext i j
    simpa using e1 (Pi.single i 1) (Pi.single j 1)
  have hinv := map_mulVec_eq_of_preserves_form hR1 k G X hGu hXG μ'
  have hlin : (lin R σ J g : (Fin M → R ⊗[F] E) → (Fin M → R ⊗[F] E)) =
      ec.symm ∘ X.mulVec ∘ ec := by
    funext u
    simp only [Function.comp_apply, hec, hecs, hX, LinearEquiv.symm_apply_apply]
  have mec : Measurable ec := ec.continuous.measurable
  have mecs : Measurable ec.symm := ec.symm.continuous.measurable
  have mX : Measurable X.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hlin, ← Measure.map_map mecs (mX.comp mec), ← Measure.map_map mX mec, hinv,
    Measure.map_map mecs mec]
  have : (ec.symm ∘ ec : (Fin M → R ⊗[F] E) → _) = id := by
    funext u
    simp
  rw [this, Measure.map_id]

theorem haar_tuple_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ hμ g
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (Fv F v ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  let ν : Measure (Fin n → Fv F v ⊗[F] E) := addHaar
  have hmeas : Measurable (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hν : ∀ _ : Fin a, MeasurePreserving (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) ν ν :=
    fun _ => ⟨hmeas, map_lin_eq_of_stableRankOne F E σ hCM n J hJ (Fv F v) (stableRankOne_field _) g ν⟩
  have hpi := measurePreserving_pi (fun _ : Fin a => ν) (fun _ => ν) hν
  have e1 : (fun X : Fin a → Fin n → Fv F v ⊗[F] E => g • X) =
      fun X i => lin (Fv F v) σ J g (X i) := rfl
  rw [isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin a => ν), Measure.map_smul, e1,
    hpi.map_eq]
  rw [e1]
  exact hpi.measurable.aemeasurable

end GlobalTheory.LocalUnitaryHaar
end
end

section

open NumberField

namespace GlobalTheory

theorem finite_lattices_between_of_smul_le :
    ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N →
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  intro K V _ _ _ _ _ _ M hM N hN
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  let f : V →ₗ[𝓞 K] V := (((N : K)⁻¹) • LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)
  have hf : ∀ x, f x = (N : K)⁻¹ • x := fun x => rfl
  have hback : ∀ x : V, f ((N : K) • x) = x := by
    intro x; rw [hf, smul_smul, inv_mul_cancel₀ hNK, one_smul]
  have hsm : ∀ x ∈ M, (N : K) • x ∈ M := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx N
  set D := M.map f with hD
  have hMD : M ≤ D := fun x hx => ⟨(N : K) • x, hsm x hx, hback x⟩
  have hsub : {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M} ⊆
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ Λ ≤ D} := by
    rintro Λ ⟨h1, h2⟩
    exact ⟨h1, fun x hx => ⟨(N : K) • x, h2 x hx, hback x⟩⟩
  refine Set.Finite.subset ?_ hsub
  have h1 := Formalism.HermitianLatticesTheory.final_finIntermediate V M.toAddSubgroup D.toAddSubgroup hMD ?_
  · refine Set.Finite.of_finite_image (f := Submodule.toAddSubgroup) (h1.subset ?_)
      (Submodule.toAddSubgroup_injective.injOn)
    rintro _ ⟨Λ, ⟨h2, h3⟩, rfl⟩
    exact ⟨h2, h3⟩
  · have f1 : Module.Finite (𝓞 K) D := Module.Finite.iff_fg.mpr (hM.map f)
    have f2 : Module.Finite ℤ D := Module.Finite.trans (𝓞 K) D
    have f3 : AddGroup.FG D.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨(N : ℤ), by exact_mod_cast hN.ne', ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      obtain ⟨m, hm, hq⟩ := q.2
      have : (((N : ℤ) • q : D.toAddSubgroup) : V) = m := by
        rw [AddSubgroup.coe_zsmul, ← hq, hf, ← Int.cast_smul_eq_zsmul K, Int.cast_natCast,
          smul_smul, mul_inv_cancel₀ hNK, one_smul]
      rw [this]
      exact hm

end GlobalTheory
end
