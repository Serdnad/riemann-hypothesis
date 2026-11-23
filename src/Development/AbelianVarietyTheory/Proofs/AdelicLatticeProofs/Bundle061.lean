module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPolynomialSectionBlockDiagonalMap
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle058
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle022
import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem normSub_eq_top_of_isSquare_image {F L : Type} [Field F] [Field L] [CharZero L]
    (φ : F →+* L) (δ : F) (hδ : δ ≠ 0) (h : IsSquare (φ δ)) (x : Fˣ) : x ∈ normSub φ δ := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hδ ((map_eq_zero φ).1 (by simpa using hr))
  refine ⟨(φ x + 1) / 2, (φ x - 1) / (2 * r), ?_⟩
  rw [hr]
  field_simp
  ring

theorem exists_not_mem_not_isSquare_completion :
    ∀ (F : Type) [Field F] [NumberField F] (u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), u ≠ 0 → ¬ IsSquare u → ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  classical
  intro F _ _ u S₀ hu hns
  by_contra hcon
  push Not at hcon
  have hle : ∀ S, locNorm F u S₀ ≤ locNorm F u S := by
    intro S x hx
    rw [locNorm, Subgroup.mem_inf] at hx ⊢
    refine ⟨?_, hx.2⟩
    have h1 := hx.1
    simp only [Subgroup.mem_iInf] at h1 ⊢
    intro v _
    by_cases hv : v ∈ S₀
    · exact h1 v hv
    · haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      exact normSub_eq_top_of_isSquare_image _ u hu (hcon v hv) x
  have hidx := (GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension F u S₀ hu).1
  haveI : (locNorm F u S₀).FiniteIndex := ⟨hidx⟩
  haveI : Fintype (Fˣ ⧸ locNorm F u S₀) := Fintype.ofFinite _
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F
    (insert (Units.mk0 u hu)
      (Finset.univ.image (fun q : Fˣ ⧸ locNorm F u S₀ => q.out))) S₀
  obtain ⟨S, hS, hadm⟩ := exists_admissible_superset_finite_places F S₁
  have hX := hS₁ S hS
  refine GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top F (Units.mk0 u hu) S hadm (hX _ (Finset.mem_insert_self _ _)) hns ?_
  rw [eq_top_iff]
  intro x _
  have hy : (QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out ∈ sUnits F S :=
    hX _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz : ((QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out)⁻¹ * x ∈ locNorm F u S₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have hx : x = (QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out *
      (((QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hy (hle S hz)

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem mem_normSub_of_isSquare {F L : Type} [Field F] [CharZero F] [Field L] (φ : F →+* L)
    (δ : Fˣ) (h : IsSquare (φ (δ : F))) (x : Fˣ) : x ∈ normSub φ (δ : F) := by
  obtain ⟨c, hc⟩ := h
  have hδ : φ (δ : F) ≠ 0 := (map_ne_zero φ).mpr δ.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hc
    exact hδ hc
  have h2 : (2 : L) ≠ 0 := by
    have : φ 2 ≠ 0 := (map_ne_zero φ).mpr two_ne_zero
    rwa [map_ofNat] at this
  rw [mem_normSub]
  refine ⟨(φ (x : F) + 1) / 2, (φ (x : F) - 1) / (2 * c), ?_⟩
  rw [hc]
  field_simp
  ring

theorem isSquare_of_mem_locSq : ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ → ∀ y ∈ sUnits F (S ∪ T), y ∈ locSq F S → IsSquare (y : F) := by
  intro F _ _ _ S T hS hT y hy hloc
  by_contra hns
  apply GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top F y (S ∪ T) (hS.mono Finset.subset_union_left) hy hns
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  intro x hx
  rw [finSq, Subgroup.mem_iInf] at hx
  rw [locSq, Subgroup.mem_inf, finSq, Subgroup.mem_iInf, Subgroup.mem_iInf] at hloc
  obtain ⟨hlocS, hlocR⟩ := hloc
  rw [locNorm, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_iInf]
  refine ⟨fun v => ?_, fun σ => ?_⟩
  · rw [Subgroup.mem_iInf]
    intro hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact mem_normSub_of_isSquare _ y
        ((mem_sqSub _ _).mp (Subgroup.mem_iInf.mp (hlocS v) hvS)) x
    · exact sqSub_le_normSub _ _ (Subgroup.mem_iInf.mp (hx v) hvT)
  · exact mem_normSub_of_isSquare _ y ((mem_sqSub _ _).mp (hlocR σ)) x

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_polynomial_section_blockDiagonal_map : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∃ (c : ι × ι → ι × ι → ℚ) (b : ι → ι → MvPolynomial (ι × ι) ℚ), (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℂ)) = 1 ∧ ∀ g ∈ Γ, (Matrix.of fun i j => ev (b i j) (blk e g)) ∈ Γ ∧ blk e (Matrix.of fun i j => ev (b i j) (blk e g)) = blk e g ∧ g = (1 + linExt c (e.map (algebraMap ℚ ℂ) * g * (1 - e.map (algebraMap ℚ ℂ)) * (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g)) := by
  first | exact @GlobalTheory.ClassFin.exists_blk_section | exact GlobalTheory.ClassFin.exists_blk_section | (intros; apply GlobalTheory.ClassFin.exists_blk_section <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_tensor_stabiliser_closed_orbit : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsQGroup Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ (∀ y : Matrix ι ι ℂ, y.det = 1 → act d (fun k => ((t k : ℚ) : ℂ)) y = (fun k => ((t k : ℚ) : ℂ)) → y ∈ Γ) ∧ IsClosed (orb d (fun k => ((t k : ℚ) : ℂ))) := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨Rey, hRey⟩ := GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ.toIsPre hss
  obtain ⟨m, d, t, hfix, hgen⟩ := GlobalTheory.T.exists_rational_invariant_tensor' ι Γ hΓ.toIsPre hss
  obtain ⟨h1, hmul, -⟩ := (GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra ι ℂ).2 m d (fun k => ((t k : ℚ) : ℂ))
  refine ⟨m, d, t, hfix, ?_, ?_⟩
  · intro y hy hyt
    by_contra hn
    obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_leftInvariantPoly_separating_coset ι Γ Rey hΓ hRey y hy hn
    obtain ⟨P, hP⟩ := hgen f hf
    apply hne
    rw [hP, hP, h1, hyt]
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_ratPoly_eval_eq_tensorPowerSumRightAction ι m d t
    have hev : ∀ (y : Matrix ι ι ℂ) (k : TIdx ι d),
        evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y = act d (fun k => ((t k : ℚ) : ℂ)) y k := by
      intro y k
      have h := hΦ ℂ y k
      simp only [eq_ratCast] at h
      rw [← h, evC, ev, MvPolynomial.eval_map, MvPolynomial.aeval_def]
    have hcl := GlobalTheory.T.isClosed_image_SL_under_generating_invariants ι Γ Rey (TIdx ι d) (fun k => MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) hRey
      hΓ.det_eq (fun k g hg y => by rw [hev, hev, hmul, hfix g hg]) (fun f hf => by
        obtain ⟨P, hP⟩ := hgen f hf
        rw [Algebra.adjoin_range_eq_range_aeval]
        refine ⟨P, ?_⟩
        apply MvPolynomial.funext
        intro x
        have h := hP (Matrix.of fun i j => x (i, j))
        have hx : (fun ij : ι × ι => (Matrix.of fun i j => x (i, j)) ij.1 ij.2) = x := rfl
        have h2 : act d (fun k => ((t k : ℚ) : ℂ)) (Matrix.of fun i j => x (i, j)) =
            fun k => MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) := by
          funext k
          rw [← hev, evC, hx]
        rw [evC, hx, h2] at h
        rw [h]
        show MvPolynomial.eval x (MvPolynomial.aeval _ P) = _
        clear hP h
        induction P using MvPolynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add (f := _), hp, hq]
        | mul_X p n hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X])
    have : orb d (fun k => ((t k : ℚ) : ℂ)) = {z : TIdx ι d → ℂ | ∃ y : Matrix ι ι ℂ, y.det = 1 ∧
        z = fun k => evC (MvPolynomial.map (algebraMap ℚ ℂ) (Φ k)) y} := by
      ext z
      simp only [orb, hev]
    rw [this]
    exact hcl

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_norm_one_reflection_correction_at_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.UnRep.exists_refl_correction | exact GlobalTheory.UnRep.exists_refl_correction | (intros; apply GlobalTheory.UnRep.exists_refl_correction <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isOpen_congruence_ideles_and_real_finite_parts : ∀ (D : D7), (∀ N : ℕ, 0 < N → IsOpen {x : (AE D)ˣ | finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y}) ∧ ∃ a b : (AE D)ˣ →* (AE D)ˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧ (∀ x, infPart D (a x : AE D) = infPart D (x : AE D) ∧ finPart D (a x : AE D) = 1) ∧ ∀ x, infPart D (b x : AE D) = 1 ∧ finPart D (b x : AE D) = finPart D (x : AE D) := by
  first | exact @GlobalTheory.IdeleParts.congr_open_and_parts | exact GlobalTheory.IdeleParts.congr_open_and_parts | (intros; apply GlobalTheory.IdeleParts.congr_open_and_parts <;> assumption)
end
