module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle909
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

open Topology Filter

namespace GlobalTheory.AdelicBumpTest

theorem exists_nonneg_test : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : Set (κ → AF F)), U ∈ nhds 0 →
    ∃ Φ ∈ schA F κ, Continuous Φ ∧ (∀ x, Φ x ≠ 0 → x ∈ U) ∧ (∀ x, (Φ x).im = 0 ∧ 0 ≤ (Φ x).re) ∧ Φ 0 = 1 := by
  intro F _ _ κ _ U hU
  classical
  let e' : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have he' : Continuous e' := continuous_pi fun i =>
    ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst)).prodMk
      ((continuous_apply i).comp continuous_snd)
  have he'0 : e' (0, 0) = 0 := by
    funext i
    refine Prod.ext ?_ rfl
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
    exact map_zero _
  have hpre : e' ⁻¹' U ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → FiniteAdeleRing (𝓞 F) F)) :=
    he'.continuousAt.preimage_mem_nhds (by rw [he'0]; exact hU)
  obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV₁

  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ y, f y = ((b y : ℝ) : ℂ) := fun y => rfl

  obtain ⟨L, hLo, hLc, hL⟩ : ∃ L : AddSubgroup (FiniteAdeleRing (𝓞 F) F), IsOpen (L : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact (L : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, u i ∈ L) → u ∈ V₂ := by
    let q := Fintype.equivFin κ
    have hc : Continuous fun (u : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) (i : κ) => u (q i) :=
      continuous_pi fun i => continuous_apply _
    have hV' : (fun (u : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) (i : κ) => u (q i)) ⁻¹' V₂ ∈
        𝓝 (0 : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) :=
      hc.continuousAt.preimage_mem_nhds hV₂
    obtain ⟨L, hLo, hLc, hL⟩ := GlobalTheory.SWQ.FinAnnih.basis_nhds (F := F) _ hV'
    refine ⟨L, hLo, hLc, fun u hu => ?_⟩
    have := hL (fun l => u (q.symm l)) fun l => hu _
    simpa using this
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.pi Set.univ fun _ => (L : Set (FiniteAdeleRing (𝓞 F) F))
  have hSo : IsOpen S := isOpen_set_pi Set.finite_univ fun _ _ => hLo
  have hSc : IsClosed S := isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen L hLo
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := S.indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨?_, ?_⟩
    · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
      by_cases hx : x ∈ S
      · exact ⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
      · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
    · exact HasCompactSupport.intro (isCompact_univ_pi fun _ => hLc) fun x hx => Set.indicator_of_notMem hx _
  refine ⟨pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact (f.continuous.comp (continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp
      (continuous_fst.comp (continuous_apply i)))).mul
      (hg.1.continuous.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))
  · intro x hx
    have hx1 : f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ≠ 0 := left_ne_zero_of_mul hx
    have hx2 : g (fun i => (x i).2) ≠ 0 := right_ne_zero_of_mul hx
    have hb : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ∈ V₁ := by
      refine hball ?_
      rw [← b.support_eq]
      intro h0
      apply hx1
      rw [hf, h0]; simp
    have hS : (fun i => (x i).2) ∈ S := by
      by_contra h
      exact hx2 (Set.indicator_of_notMem h _)
    have hmem := hsub (Set.mk_mem_prod hb (hL _ fun i => hS i (Set.mem_univ i)))
    have hxe : e' ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), fun i => (x i).2) = x := by
      funext i
      refine Prod.ext ?_ rfl
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
    rw [← hxe]
    exact hmem
  · intro x
    show (f _ * g _).im = 0 ∧ 0 ≤ (f _ * g _).re
    rw [hf]
    by_cases h : (fun i => (x i).2) ∈ S
    · simp only [g, Set.indicator_of_mem h, Pi.one_apply, mul_one, Complex.ofReal_im, Complex.ofReal_re, true_and]
      exact b.nonneg
    · simp only [g, Set.indicator_of_notMem h, mul_zero, Complex.zero_im, Complex.zero_re, le_refl, and_self]
  · show f _ * g _ = 1
    have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
      funext i
      exact map_zero _
    have hS0 : (fun i => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ S := fun i _ => L.zero_mem
    rw [h0, hf, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε).le)]
    simp only [g, Set.indicator_of_mem hS0, Pi.one_apply, Complex.ofReal_one, mul_one]

end GlobalTheory.AdelicBumpTest
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.NormSignEven

variable {M : Type} [Field M] [NumberField M]

lemma cc (φ : M →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ

lemma conj_re (φ : M →+* ℂ) (x : M) : (ComplexEmbedding.conjugate φ x).re = (φ x).re := by
  rw [ComplexEmbedding.conjugate_coe_eq]; simp

lemma conj_ne {σ : M →+* M} (hσ : σ ≠ RingHom.id M)
    (hc : ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : M →+* ℂ) :
    ComplexEmbedding.conjugate φ ≠ φ := by
  intro h
  apply hσ
  ext x
  apply φ.injective
  rw [hc, RingHom.id_apply]
  have := congrArg (fun ψ : M →+* ℂ => ψ x) h
  simpa [ComplexEmbedding.conjugate_coe_eq] using this

lemma im_eq_zero {σ : M →+* M}
    (hc : ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : M →+* ℂ) {x : M} (hx : σ x = x) :
    (φ x).im = 0 := by
  have h := hc φ x
  rw [hx] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma re_mul {σ : M →+* M}
    (hc : ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : M →+* ℂ) {x y : M}
    (hx : σ x = x) :
    (φ (x * y)).re = (φ x).re * (φ y).re := by
  rw [map_mul, Complex.mul_re, im_eq_zero hc φ hx, zero_mul, sub_zero]

end GlobalTheory.NormSignEven

open GlobalTheory.NormSignEven in
theorem GlobalTheory.NormSign.exists_neg_even_norm_away : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ (S : Finset (M →+* ℂ)), (∀ φ ∈ S, ComplexEmbedding.conjugate φ ∈ S) → 4 ∣ S.card → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (∀ φ ∈ S, (φ a).re < 0) ∧ (∀ φ : M →+* ℂ, φ ∉ S → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  intro M _ _ σ hσ hc S hS h4 p _
  obtain ⟨n, hn⟩ := h4
  induction n generalizing S with
  | zero =>
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by simpa using hn)
    subst hS0
    refine ⟨1, one_ne_zero, map_one σ, by simp, fun φ _ => by simp, 1, ?_⟩
    simp [Algebra.TensorProduct.one_def]
  | succ n ih =>
    obtain ⟨ε, hε⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hε1 : ComplexEmbedding.conjugate ε ∈ (S.erase ε) :=
      Finset.mem_erase.mpr ⟨conj_ne hσ hc ε, hS ε hε⟩
    have hT : 0 < ((S.erase ε).erase (ComplexEmbedding.conjugate ε)).card := by
      rw [Finset.card_erase_of_mem hε1, Finset.card_erase_of_mem hε]; omega
    obtain ⟨ε', hε'⟩ := Finset.card_pos.mp hT
    simp only [Finset.mem_erase] at hε'
    obtain ⟨h1, h2, hε'S⟩ := hε'
    have hcc : ∀ φ ψ : M →+* ℂ, ComplexEmbedding.conjugate φ = ψ → φ = ComplexEmbedding.conjugate ψ := by
      intro φ ψ h; rw [← h, cc]
    have h3 : ε ≠ ComplexEmbedding.conjugate ε' := by
      intro h; apply h1; rw [h, cc]
    set S' := (((S.erase ε).erase (ComplexEmbedding.conjugate ε)).erase ε').erase
      (ComplexEmbedding.conjugate ε') with hS'def
    have hmem : ∀ φ, φ ∈ S' ↔ φ ≠ ComplexEmbedding.conjugate ε' ∧ φ ≠ ε' ∧
        φ ≠ ComplexEmbedding.conjugate ε ∧ φ ≠ ε ∧ φ ∈ S := by
      intro φ; simp [hS'def, Finset.mem_erase]
    have hcard : S'.card = 4 * n := by
      have e1 : ε' ∈ ((S.erase ε).erase (ComplexEmbedding.conjugate ε)) := by
        simp [Finset.mem_erase]; exact ⟨h1, h2, hε'S⟩
      have e2 : ComplexEmbedding.conjugate ε' ∈
          ((S.erase ε).erase (ComplexEmbedding.conjugate ε)).erase ε' := by
        simp only [Finset.mem_erase]
        refine ⟨conj_ne hσ hc ε', ?_, fun h => h3 h.symm, hS _ hε'S⟩
        intro h
        exact h2 (by have := congrArg ComplexEmbedding.conjugate h; simpa [cc] using this)
      rw [hS'def, Finset.card_erase_of_mem e2, Finset.card_erase_of_mem e1,
        Finset.card_erase_of_mem hε1, Finset.card_erase_of_mem hε]
      omega
    have hS'stab : ∀ φ ∈ S', ComplexEmbedding.conjugate φ ∈ S' := by
      intro φ hφ
      rw [hmem] at hφ ⊢
      obtain ⟨a1, a2, a3, a4, a5⟩ := hφ
      refine ⟨fun h => a2 ?_, fun h => a1 ?_, fun h => a4 ?_, fun h => a3 ?_, hS φ a5⟩
      · have := congrArg ComplexEmbedding.conjugate h; simpa [cc] using this
      · exact hcc _ _ h
      · have := congrArg ComplexEmbedding.conjugate h; simpa [cc] using this
      · exact hcc _ _ h
    obtain ⟨b, hb0, hbσ, hbneg, hbpos, ub, hub⟩ := ih S' hS'stab hcard
    obtain ⟨c, hc0, hcσ, hcε, hcε', hcpos, uc, huc⟩ :=
      GlobalTheory.T.exists_realSubfield_negative_twoPlaces_normEverywhere M σ hσ hc ε ε' (Ne.symm h2) h3 p
    have hcneg : ∀ φ, φ = ε ∨ φ = ComplexEmbedding.conjugate ε ∨ φ = ε' ∨ φ = ComplexEmbedding.conjugate ε' →
        (φ c).re < 0 := by
      rintro φ (rfl | rfl | rfl | rfl)
      · exact hcε
      · rw [conj_re]; exact hcε
      · exact hcε'
      · rw [conj_re]; exact hcε'
    refine ⟨b * c, mul_ne_zero hb0 hc0, by rw [map_mul, hbσ, hcσ], ?_, ?_, ub * uc, ?_⟩
    · intro φ hφ
      rw [re_mul hc φ hbσ]
      by_cases hφ' : φ ∈ S'
      · exact mul_neg_of_neg_of_pos (hbneg φ hφ') (hcpos φ (by rw [hmem] at hφ'; exact hφ'.2.2.2.1)
          (by rw [hmem] at hφ'; exact hφ'.2.2.1) (by rw [hmem] at hφ'; exact hφ'.2.1)
          (by rw [hmem] at hφ'; exact hφ'.1))
      · refine mul_neg_of_pos_of_neg (hbpos φ hφ') (hcneg φ ?_)
        rw [hmem] at hφ'
        by_contra hne
        push_neg at hne
        exact hφ' ⟨hne.2.2.2, hne.2.2.1, hne.2.1, hne.1, hφ⟩
    · intro φ hφ
      rw [re_mul hc φ hbσ]
      have hφ' : φ ∉ S' := fun h => hφ (((hmem φ).mp h).2.2.2.2)
      refine mul_pos (hbpos φ hφ') (hcpos φ ?_ ?_ ?_ ?_)
      · rintro rfl; exact hφ hε
      · rintro rfl; exact hφ (hS ε hε)
      · rintro rfl; exact hφ hε'S
      · rintro rfl; exact hφ (hS ε' hε'S)
    · rw [Units.val_mul, map_mul]
      calc (ub : AfP p ⊗[ℚ] M) * uc * (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom ub *
            Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom uc)
          = ((ub : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom ub) *
            ((uc : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom uc) := by ring
        _ = 1 ⊗ₜ (b * c) := by rw [hub, huc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.StdReps

section General

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_nat_smul_mem (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ x ∈ L, (c : E) • x ∈ L' := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | (apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le ..)

theorem fg_colLat (B : GL (Fin n) E) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem span_colLat (B : GL (Fin n) E) : Submodule.span E (colLat B : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, ((B⁻¹).1 *ᵥ x) j • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) E) a j) := by
    have e : x = B.1 *ᵥ ((B⁻¹).1 *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [e]
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hx]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Submodule.subset_span ⟨j, rfl⟩

end General

variable {D : D7}

def stabGL {R : Type} [CommRing R] {m : ℕ} (H : Set (Fin m → R)) : Subgroup (GL (Fin m) R) where
  carrier := {g | ∀ v, v ∈ H ↔ g.1 *ᵥ v ∈ H}
  one_mem' := fun v => by rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb v => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb v).trans (ha _)
  inv_mem' := fun {a} ha v => by
    have := ha ((a⁻¹).1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

def stabG (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Subgroup (GA D V) :=
  (stabGL (Formalism.L2.Herm.hatL (F := D.host.F) M : Set (Fin V.rank → Formalism.IndefR.Lev.EAf D))).comap (Formalism.IndefR.Lev.finE V)



theorem mulVec_mem_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M,
      (Formalism.IndefR.Lev.finE V a).1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have hl := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hcong : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
        (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c * c) • y := by
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap _ _ _ ha
  intro z hz
  obtain ⟨y, hy, e⟩ := hcong _ (GlobalTheory.LevSplit.hatL_smul _ _ c h1 z hz)
  have hcE : IsUnit (c : D.host.E) := (Nat.cast_ne_zero.2 hc.ne').isUnit
  have hu : IsUnit (c : Formalism.IndefR.Lev.EAf D) := by
    have := hcE.map (eToEAf D)
    rwa [map_natCast] at this
  have e2 : (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c : Formalism.IndefR.Lev.EAf D) • y := by
    refine (hu.smul_left_cancel).1 ?_
    rw [smul_sub, ← Matrix.mulVec_smul, e, ← Nat.cast_smul_eq_nsmul (Formalism.IndefR.Lev.EAf D), Nat.cast_mul, mul_smul]
  rw [sub_eq_iff_eq_add'] at e2
  rw [e2]
  exact Submodule.add_mem _ hz (GlobalTheory.LevSplit.hatL_smul _ _ c h2 y hy)



theorem mem_stabG_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    a ∈ stabG V M := by
  intro v
  refine ⟨mulVec_mem_of_finCong V M c hc h1 h2 a ha v, fun hv => ?_⟩
  have := mulVec_mem_of_finCong V M c hc h1 h2 a⁻¹ (GlobalTheory.Member.PrincLevel.finCong_inv ha) _ hv
  rwa [map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this



theorem exists_rep_std : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (S : Finset ℕ), (∀ q ∈ S, q.Prime) →
    ∀ x : GA D V, x ∈ GfC V →
    ∃ (γ : GL (Fin V.rank) D.host.E) (h k : GA D V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram ∧ h ∈ GfC V ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) ∧
      k ∈ GfC V ∧ (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) ∧
      (Formalism.IndefR.Lev.finE V x).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (Formalism.IndefR.Lev.finE V k).1 := by
  intro D V fr S hS x hx
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨c1, hc1, h1⟩ := exists_nat_smul_mem (colLat fr) (GlobalTheory.Member.latC V) (fg_colLat fr) hsp
  obtain ⟨c2, hc2, h2⟩ := exists_nat_smul_mem (GlobalTheory.Member.latC V) (colLat fr) hfg (span_colLat fr)
  have h1' : ∀ y ∈ colLat fr, ((c1 * c2 : ℕ) : D.host.E) • y ∈ GlobalTheory.Member.latC V := fun y hy => by
    rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c2]
    exact (GlobalTheory.Member.latC V).toAddSubmonoid.nsmul_mem (h1 y hy) c2
  have h2' : ∀ y ∈ GlobalTheory.Member.latC V, ((c1 * c2 : ℕ) : D.host.E) • y ∈ colLat fr := fun y hy => by
    rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c1]
    exact (colLat fr).toAddSubmonoid.nsmul_mem (h2 y hy) c1
  have hc : 0 < c1 * c2 := Nat.mul_pos hc1 hc2
  let J' : Subgroup (Formalism.IndefR.Bridge.Gf V) := (GfC V ⊓ stabG V (colLat fr)).map (finHom V).rangeRestrict
  have hK : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V ((c1 * c2) * (c1 * c2)) k → Formalism.IndefR.FWT.fin V k ∈ J' :=
    fun k hk hck => ⟨k, ⟨hk, mem_stabG_of_finCong V (colLat fr) _ hc h1' h2' k hck⟩, rfl⟩
  have hbad : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS q hq).pos
  obtain ⟨h, ⟨hh, hs⟩, γ, k, e⟩ :=
    GlobalTheory.SplitReps.exists_split_rep V (Nat.mul_pos hc hc) hK hbad (Formalism.IndefR.FWT.fin V x)
  obtain ⟨k0, ⟨hk0, hk0s⟩, hk0e⟩ := Subgroup.mem_map.1 k.2
  obtain ⟨-, e0, P, he0, hP, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  obtain ⟨γE, hU, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  have hfγ : finHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
    rw [finHom, MonoidHom.comp_apply, hm]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  have ef : finHom V x = finHom V γ.1 * finHom V h * finHom V k0 := by
    have := congrArg Subtype.val e
    rw [← hk0e] at this
    exact this
  refine ⟨γE, h, k0, hU, hh, ⟨P, e0, he0, hsupp, fun w hw q hq hqw => hP w hw ?_⟩, hk0, hk0s, ?_⟩
  · obtain ⟨m, hm'⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
    rw [hm', Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqw
  · have eE : Formalism.IndefR.Lev.finE V x = Formalism.IndefR.Lev.finE V γ.1 * Formalism.IndefR.Lev.finE V h * Formalism.IndefR.Lev.finE V k0 := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, ef, map_mul]
    have eγ : (Formalism.IndefR.Lev.finE V γ.1).1 = γE.1.map (eToEAf D) := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, hfγ]
      ext i j
      rfl
    rw [eE, Units.val_mul, Units.val_mul, eγ]

end GlobalTheory.FunObj.StdReps
end
end

section

open GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.ShapeSmoothFinite

theorem continuous_matCoord_ujMat {n : ℕ} (ε : Fin n → Bool) : Continuous (matCoord (ujMat ε)) :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val

theorem mem_ccMat_and_isBiFinite {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : Mat n → ℂ) (hφ : φ ∈ ShapeM ε d) :
    (fun g : UJ ε => φ (toM g)) ∈ CcMat (ujMat ε) ∧ IsBiFinite (KG ε) (fun g : UJ ε => φ (toM g)) := by
  obtain ⟨h0, hadd, hsmul⟩ := GlobalTheory.isBiFinite_subspace (UJ ε) (KG ε)
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, ⟨hH, R, hR⟩, -, rfl⟩ := h
    exact ⟨GlobalTheory.CutoffPoly.cutoff_mul_poly_mem_ccMat n ε H R hH hR P, GlobalTheory.PolyShapeFinite.main n ε H P⟩
  | zero => exact ⟨Submodule.zero_mem _, h0⟩
  | add φ ψ _ _ h h' => exact ⟨Submodule.add_mem _ h.1 h'.1, hadd _ _ h.2 h'.2⟩
  | smul c φ _ h => exact ⟨Submodule.smul_mem _ c h.1, hsmul c _ h.2⟩

theorem stShape : GlobalTheory.PsCo.Pc1.StShape := by
  intro n ε d φ hφ
  obtain ⟨h1, h2⟩ := mem_ccMat_and_isBiFinite ε d φ hφ
  exact ⟨h1, h2, continuous_of_mem_ccSmooth (continuous_matCoord_ujMat ε) h1, (mem_ccSmooth.1 h1).1⟩

end GlobalTheory.ShapeSmoothFinite
end
