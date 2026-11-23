module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle295
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.OrbitT

open GlobalTheory.LatOrb

theorem stable_of_conj {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} (g : GL (Fin n) K)
    (γ : Matrix (Fin n) (Fin n) K)
    (h : matLat O ((g⁻¹ : GL (Fin n) K).val * γ * g.val) (stdLat O n) = stdLat O n) :
    ∀ v ∈ matLat O g.val (stdLat O n), γ *ᵥ v ∈ matLat O g.val (stdLat O n) := by
  intro v hv
  have e : γ * g.val = g.val * ((g⁻¹ : GL (Fin n) K).val * γ * g.val) := by
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : matLat O γ (matLat O g.val (stdLat O n)) = matLat O g.val (stdLat O n) := by
    rw [← matLat_mul, e, matLat_mul, h]
  rw [← h2]
  exact (mem_matLat _ _ _).2 ⟨v, hv, rfl⟩

theorem orbit_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g₁ g₂ : UL n w, g₁⁻¹ * γ * g₁ ∈ KL n w → g₂⁻¹ * γ * g₂ ∈ KL n w →
    ∃ t ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ k ∈ KL n w, g₂ = t * g₁ * k := by
  intro E _ _ _ n w hcc hcv P₀ hcop γ hγ g₁ g₂ h₁ h₂
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
  have hσO : ∀ a : w.adicCompletionIntegers E, ∃ b : w.adicCompletionIntegers E,
      cj w (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) a) =
        algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) b := by
    intro a
    refine ⟨⟨cj w a, ?_⟩, rfl⟩
    have ha := a.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hcv]; exact ha
  have hK : ∀ h : UL n w, h ∈ KL n w ↔ matLat (w.adicCompletionIntegers E) h.1.val
      (stdLat (w.adicCompletionIntegers E) n) = stdLat (w.adicCompletionIntegers E) n := by
    intro h
    exact (Subgroup.mem_subgroupOf).trans (GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq (w.adicCompletionIntegers E) n h.1)
  have st : ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w → ∀ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n), γ.1.val *ᵥ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n) := by
    intro g hg
    have h := (hK _).1 hg
    have e : ((g⁻¹ * γ * g : UL n w).1.val) = (g.1⁻¹ : GLw n w).val * γ.1.val * g.1.val := by simp
    rw [e] at h
    exact stable_of_conj g.1 γ.1.val h
  obtain ⟨t, htU, htc, htM⟩ : ∃ t : GLw n w, t ∈ UL n w ∧ t * γ.1 = γ.1 * t ∧
      matLat (w.adicCompletionIntegers E) t.val (matLat (w.adicCompletionIntegers E) g₁.1.val
        (stdLat (w.adicCompletionIntegers E) n)) = matLat (w.adicCompletionIntegers E) g₂.1.val
        (stdLat (w.adicCompletionIntegers E) n) := by
    obtain ⟨p, hpu, hp⟩ := GlobalTheory.T.exists_unit_eq_of_stable_lattices n P₀ hcop γ.1.val hγ _ _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1) (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₂.1) (st g₁ h₁) (st g₂ h₂)
    by_cases hs : IsSplitAt w
    · refine ⟨hpu.unit, by simp [UL, hs], ?_, hp.symm⟩
      ext : 1
      simp only [Units.val_mul, IsUnit.unit_spec]
      have e1 : aeval γ.1.val p * γ.1.val = aeval γ.1.val (p * X) := by rw [map_mul, aeval_X]
      have e2 : γ.1.val * aeval γ.1.val p = aeval γ.1.val (X * p) := by rw [map_mul, aeval_X]
      rw [e1, e2, mul_comm]
    · have hUL : ∀ h : UL n w, ((h.1.val).map (cj w))ᵀ * h.1.val = 1 := by
        intro h
        have := h.2
        simp only [UL, hs, if_false] at this
        simpa [UJ, cT] using this
      have sd : ∀ g : UL n w, SelfDual (w.adicCompletionIntegers E) (cj w)
          (matLat (w.adicCompletionIntegers E) g.1.val (stdLat (w.adicCompletionIntegers E) n)) :=
        fun g => GlobalTheory.T.isSelfDual_image_standardLattice_unitary (cj w) hcc hσO n _ (hUL g)
      have hc := GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices (cj w) hcc n (aeval γ.1.val p) hpu _ (sd g₁) (hp ▸ sd g₂)
      obtain ⟨t, ht1, htc, htM⟩ := GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq n P₀ hcop γ.1.val hγ (cj w) hcc hσO (hUL γ) _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1)
        (st g₁ h₁) p hpu hc
      have htu : IsUnit t := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse ht1)
      refine ⟨htu.unit, ?_, ?_, by rw [hp]; exact htM⟩
      · show _ ∈ UL n w
        simp only [UL, hs, if_false]
        show cT (cj w) _ * 1 * _ = 1
        simpa [cT] using ht1
      · ext : 1
        simpa using htc
  refine ⟨⟨t, htU⟩, ?_, (⟨t, htU⟩ * g₁)⁻¹ * g₂, ?_, by group⟩
  · show (⟨t, htU⟩ : UL n w) * γ = γ * (⟨t, htU⟩ : UL n w)
    exact Subtype.ext htc
  · rw [hK]
    have e : (((⟨t, htU⟩ : UL n w) * g₁)⁻¹ * g₂ : UL n w).1.val =
        (g₁.1⁻¹ : GLw n w).val * ((t⁻¹ : GLw n w).val * g₂.1.val) := by simp [mul_assoc]
    rw [e, matLat_mul, matLat_mul, ← htM, ← matLat_mul (a := ((t⁻¹ : GLw n w).val)), Units.inv_mul, matLat_one,
      ← matLat_mul, Units.inv_mul, matLat_one]

end GlobalTheory.BCT.OrbitT
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.RatDarbouxTransferF

theorem finDim (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem finrank_AEF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Module.Free (AF F) (AF F ⊗[F] E) ∧ Module.Finite (AF F) (AF F ⊗[F] E) ∧
    Module.finrank (AF F) (AF F ⊗[F] E) = Module.finrank F E := by
  haveI := finDim F E
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  let bA := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  exact ⟨Module.Free.of_basis bA, Module.Finite.of_basis bA, by
    rw [Module.finrank_eq_card_basis bA, Fintype.card_fin]⟩

theorem card_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (nS nT : ℕ) (κ : Type) [Fintype κ]
    (e : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) :
    2 * Fintype.card κ = nT * nS * Module.finrank F E := by
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AEF F E
  have h := e.finrank_eq
  have ha : Module.finrank (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) = nT * nS * Module.finrank F E := by
    show Module.finrank (AF F) (Fin nT → Fin nS → AF F ⊗[F] E) = _
    simp [Module.finrank_pi_fintype, hAE, mul_assoc]
  have hb : Module.finrank (AF F) ((κ → AF F) × (κ → AF F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    ring
  rw [← hb, ← h, ha]


theorem onto (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (nS nT : ℕ) (κ : Type) [Fintype κ]
    (e : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, e.symm p ∈ ratLF F E nS nT := by
  have hκ := card_eq F E nS nT κ e
  haveI := finDim F E
  let J1 : (κ → F) →ₗ[F] (κ → AF F) := LinearMap.compLeft (Algebra.linearMap F (AF F)) κ
  let J : ((κ → F) × (κ → F)) →ₗ[F] (κ → AF F) × (κ → AF F) := J1.prodMap J1
  let I : Matrix (Fin nT) (Fin nS) E →ₗ[F] Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) :=
    (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
  let L := (e.toLinearMap.restrictScalars F).comp I
  have hJinj : Function.Injective J := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    have hi := AdeleRing.algebraMap_injective (𝓞 F) F
    simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
    refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have hLinj : Function.Injective L := by
    haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    have hr : Function.Injective (inclR (F := F) (E := E) (AF F)) := RingHom.injective _
    intro x x' h
    have := e.injective h
    exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
  have hle : LinearMap.range L ≤ LinearMap.range J := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨(y, z), by rw [show L x = e (incM F x) from rfl, h]; rfl⟩
  have heq : LinearMap.range L = LinearMap.range J := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
    have hm : Module.finrank F (Matrix (Fin nT) (Fin nS) E) = nT * nS * Module.finrank F E := by
      show Module.finrank F (Fin nT → Fin nS → E) = _
      simp [Module.finrank_pi_fintype, mul_assoc]
    have hp : Module.finrank F ((κ → F) × (κ → F)) = 2 * Fintype.card κ := by
      rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
      ring
    rw [hm, hp, hκ]
  intro p hp
  obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
  have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, ?_⟩
  have hx' : e (incM F x) = J (y, z) := hx
  show incM F x = e.symm (J (y, z))
  rw [← hx']
  exact (e.symm_apply_apply _).symm

open scoped Pointwise



theorem haar_fundDomain_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
            IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
            ∃ (ν' : @Measure ((κ → AF F) × (κ → AF F)) (borel _)) (𝓕' : Set ((κ → AF F) × (κ → AF F))),
              @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
              @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕' ν' ∧
              ∀ f : (κ → AF F) × (κ → AF F) → ℂ,
                ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  obtain ⟨hfr, hfin, -⟩ := finrank_AEF F E
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI hMT : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  letI mP : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
  haveI : BorelSpace ((κ → AF F) × (κ → AF F)) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let ce : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃L[AF F] (κ → AF F) × (κ → AF F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : WOF F E nS nT ≃ₜ+ (κ → AF F) × (κ → AF F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me : WOF F E nS nT ≃ᵐ (κ → AF F) × (κ → AF F) := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratLF F E nS nT, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, co.e.symm p ∈ ratLF F E nS nT :=
    onto F E nS nT κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : WOF F E nS nT) + x) = co.e g + co.e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS nT := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratLF F E nS nT := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS nT => co.e (t : WOF F E nS nT)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F κ) (k : ratLF F E nS nT),
          (k : WOF F E nS nT) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF F) × (κ → AF F)) + co.e w = co.e ((k : WOF F E nS nT) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl

end GlobalTheory.RatDarbouxTransferF

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.DarbouxMeasure

theorem transport_covol_one : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  intro D S T κ _ e he ν 𝓕 hc
  letI mP : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.Datum.WO S T) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F)
      (Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)))
  obtain ⟨hH, hF, h1⟩ := hc
  have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : Formalism.IndefR.Datum.WO S T ≃ₜ ((κ → AF D.host.F) × (κ → AF D.host.F)) :=
    { toEquiv := e.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }
  let m := h.toMeasurableEquiv
  refine ⟨Measure.map m ν, m '' 𝓕, ?_, ?_, ?_, ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map ν e.toAddEquiv hc1 hc2
  · let r : GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ ≃ ratL T S :=
      { toFun := fun p => ⟨e.symm p, (he (e.symm p)).2 (by simpa using p.2)⟩
        invFun := fun γ => ⟨e γ, (he γ).1 γ.2⟩
        left_inv := fun p => by ext1; simp
        right_inv := fun γ => by ext1; simp }
    refine hF.image_of_equiv m.toEquiv (m.measurePreserving_symm ν).quasiMeasurePreserving r ?_
    intro g x
    change e (e.symm (g : (κ → AF D.host.F) × (κ → AF D.host.F)) + x) = (g : (κ → AF D.host.F) × (κ → AF D.host.F)) + e x
    rw [map_add (f := _), LinearEquiv.apply_symm_apply]
  · rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ m.injective, h1]
  · intro g
    rw [m.measurableEmbedding.setIntegral_map, Set.preimage_image_eq _ m.injective]
    rfl

end GlobalTheory.DarbouxMeasure
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CharKer

theorem pmap_eq_whiskerRight {S : Scheme.{0}} {A A' : Over S} (q : A ⟶ A') (T : Over S) : pmap q T = q ▷ T := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [pmap]

theorem isPullback_over_left {S : Scheme.{0}} {P X Y Z : Over S} {f : P ⟶ X} {g : P ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z}
    (H : IsPullback f g h k) : IsPullback f.left g.left h.left k.left :=
  H.map (Over.forget S)

theorem res_res_units {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  apply Units.ext
  change _ = (X.presheaf.map ((homOfLE h₁).op ≫ (homOfLE h₂).op)).hom x.val
  rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]; rfl

theorem res_pullU_units {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (f.preimage_mono h) (pullU f U x) := by
  apply Units.ext
  have := f.naturality (homOfLE h).op
  change (X.presheaf.map (homOfLE h).op ≫ f.app V).hom x.val = _
  rw [this]; rfl

theorem mul_mul_inv_mul_inv_cancel {G : Type*} [CommGroup G] (c x y : G) : (c * x) * (c * y)⁻¹ = x * y⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]

theorem exists_equivGen : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∃ (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), M.IsLB ∧ IsEquivGen i q χ M e := by
  intro S A A' N T _ _ _ i q χ hi hq hfin hflat hsurj hker hχ
  have hloc := GlobalTheory.T.exists_nhds_characterUnit_kernel_action S A A' N T i q χ hi hq hfin hflat hsurj hker hχ
  have : Flat (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have : Surjective (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have : QuasiCompact (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have hpb : IsPullback (prMap A N T).left (actMap i T).left (pmap q T).left (pmap q T).left :=
    isPullback_over_left (GlobalTheory.T.kernelAction_isPullback_prodMap_torsor S A A' N T i q hi hq hker)
  have hw : ∀ z, (pmap q T).left ((actMap i T).left z) = (pmap q T).left ((prMap A N T).left z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  have inj : ∀ U : (A' ⊗ T).left.Opens, Function.Injective (pullU (pmap q T).left U) := fun U x y hxy =>
    Units.ext (ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj (pmap q T).left U (congrArg Units.val hxy))
  have desc : ∀ (U : (A' ⊗ T).left.Opens) (u : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ U)ˣ),
      (∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U))
        (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U)),
        res h₁ (pullU (actMap i T).left _ u) = res h₂ (pullU (prMap A N T).left _ u)) →
      ∃ g : Γ((A' ⊗ T).left, U)ˣ, pullU (pmap q T).left U g = u := by
    intro U u hu
    have hg : (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U) ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U) :=
      fun z hz => show (pmap q T).left ((actMap i T).left z) ∈ U from (hw z) ▸ hz
    have key := GlobalTheory.FlatDescent.existsUnique_app_eq_iff (pmap q T).left hpb U _ rfl le_rfl hg u.val
    obtain ⟨a, ha, -⟩ := key.2 (congrArg Units.val (hu _ hg le_rfl)).symm
    obtain ⟨a, rfl⟩ := (GlobalTheory.FlatDescent.isUnit_app_iff (pmap q T).left U a).1 (ha ▸ u.isUnit)
    exact ⟨a, Units.ext ha⟩
  choose V hyV e he using hloc
  have hu : ∀ k l, ∃ g : Γ((A' ⊗ T).left, V k ⊓ V l)ˣ, pullU (pmap q T).left _ g =
      res ((pmap q T).left.preimage_mono inf_le_left) (e k) *
        (res ((pmap q T).left.preimage_mono inf_le_right) (e l))⁻¹ := fun k l => desc _ _ (by
    intro W h₁ h₂
    simp only [map_mul, map_inv, res_pullU_units, res_res_units]
    rw [he k W _ (h₂.trans ((prMap A N T).left.preimage_mono ((pmap q T).left.preimage_mono inf_le_left))),
      he l W _ (h₂.trans ((prMap A N T).left.preimage_mono ((pmap q T).left.preimage_mono inf_le_right))),
      mul_mul_inv_mul_inv_cancel])
  choose g hg using hu
  refine ⟨⟨(A' ⊗ T).left, V, g⟩, e, ⟨?_, ?_, ?_⟩, ?_, fun k W h₁ h₂ => he k W h₁ h₂⟩
  · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV y⟩
  · intro k
    apply inj
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, map_one, mul_inv_cancel]
  · intro a b c
    apply inj
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, _root_.mul_assoc, inv_mul_cancel_left]
  · intro k l W h₁ h₂ h₃
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]

end GlobalTheory.CharKer
end
end
