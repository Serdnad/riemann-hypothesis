module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ReFormPosOfThetaNeZero
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle004
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle006
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultiplicativeDerivationRank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle001
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

open scoped nonZeroDivisors

theorem differentIdeal_principal_in_localSubring :
    ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [CharZero Ω] (R : Subring Ω)
      [IsLocalRing R] (σ : 𝓞 F →+* Ω), (∀ a, σ a ∈ R) →
      ∃ d₀ ∈ differentIdeal ℤ (𝓞 F), σ d₀ ≠ 0 ∧
        ∀ d ∈ differentIdeal ℤ (𝓞 F), σ d / σ d₀ ∈ R := by
  intro F _ _ Ω _ _ R _ σ hσ
  have hinj : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  set I : Ideal (𝓞 F) := differentIdeal ℤ (𝓞 F) with hIdef
  have hI0 : I ≠ ⊥ := differentIdeal_ne_bot
  let J : FractionalIdeal (𝓞 F)⁰ F := (I : FractionalIdeal (𝓞 F)⁰ F)
  have hJ0 : J ≠ 0 := by
    simpa [J] using hI0
  have hJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ0
  let σ' : 𝓞 F →+* R := σ.codRestrict R hσ
  let P : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal R).comap σ'
  have hP1 : (1 : 𝓞 F) ∉ P := by
    intro h
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by simpa [P] using h
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top this

  have hex : ∃ x ∈ I, ∃ y ∈ J⁻¹, ∃ u : 𝓞 F, algebraMap (𝓞 F) F u = algebraMap (𝓞 F) F x * y ∧
      u ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hle : J * J⁻¹ ≤ (P : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mul_le]
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
      have hab : algebraMap (𝓞 F) F x * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← hJ]
        exact FractionalIdeal.mul_mem_mul ha hb
      obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1 hab
      rw [← hu]
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨u, hcon x hx b hb u hu, rfl⟩
    have h1 : (1 : F) ∈ (P : FractionalIdeal (𝓞 F)⁰ F) :=
      hle (by rw [hJ]; exact FractionalIdeal.one_mem_one _)
    obtain ⟨w, hw, hw1⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
    have : w = 1 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hw1
    exact hP1 (this ▸ hw)
  obtain ⟨x, hx, y, hy, u, hu, huP⟩ := hex
  have hunit : IsUnit (σ' u) := by
    by_contra hnu
    exact huP ((IsLocalRing.mem_maximalIdeal _).2 hnu)
  have hσu : σ u ≠ 0 := by
    intro h0
    have : σ' u = 0 := Subtype.ext h0
    rw [this] at hunit
    exact not_isUnit_zero hunit
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : u = 0 := by
      apply IsFractionRing.injective (𝓞 F) F
      simpa using hu
    exact hσu (by simp [this])
  refine ⟨x, hx, fun h => hx0 (hinj (by simpa using h)), fun d hd => ?_⟩
  have hdJ : algebraMap (𝓞 F) F d ∈ J := (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  have hdy : algebraMap (𝓞 F) F d * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← hJ]
    exact FractionalIdeal.mul_mem_mul hdJ hy
  obtain ⟨v, hv⟩ := (FractionalIdeal.mem_one_iff _).1 hdy
  have hrel : d * u = x * v := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [map_mul, map_mul, hu, hv]
    ring
  have hrel' : σ d * σ u = σ x * σ v := by rw [← map_mul, ← map_mul, hrel]
  have hσx : σ x ≠ 0 := fun h => hx0 (hinj (by simpa using h))
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hw' : σ u * (w : Ω) = 1 := congrArg Subtype.val hw
  have key : σ d / σ x = σ v * (w : Ω) := by
    rw [div_eq_iff hσx]
    calc σ d = σ d * (σ u * (w : Ω)) := by rw [hw', _root_.mul_one]
      _ = (σ d * σ u) * (w : Ω) := by ring
      _ = σ v * (w : Ω) * σ x := by rw [hrel']; ring
  rw [key]
  exact R.mul_mem (hσ v) w.2

end GlobalTheory.CompanionTheory.Ar
end

section


theorem _root_.GlobalTheory.T.implicit_root_analytic : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ) (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ), (∀ j, AnalyticAt ℂ (c j) w₀) → ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0 → ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧ AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W, ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  first | exact @GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | exact GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | (intros; apply GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root <;> assumption)
end

section

open Filter Topology Metric

namespace GlobalTheory.CompanionTheory.HoloChart

theorem holomorphic_inverse_with_parameters :
    ∀ (n : ℕ) (I J : Type) [Fintype I] [Fintype J] (Ω : Set ((Fin n → ℂ) × (I → ℂ)))
      (Φ : (Fin n → ℂ) × (I → ℂ) → (J → ℂ)) (b₀ : Fin n → ℂ) (x₀ : I → ℂ)
      (L : (I → ℂ) ≃L[ℂ] (J → ℂ)), IsOpen Ω → (b₀, x₀) ∈ Ω → DifferentiableOn ℂ Φ Ω →
      HasFDerivAt (fun x => Φ (b₀, x)) (L : (I → ℂ) →L[ℂ] (J → ℂ)) x₀ →
  ∃ (ε δ : ℝ) (X : (Fin n → ℂ) × (J → ℂ) → (I → ℂ)), 0 < ε ∧ 0 < δ ∧ X (b₀, Φ (b₀, x₀)) = x₀ ∧
    DifferentiableOn ℂ X (ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε) ∧
    (∀ p ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε, (p.1, X p) ∈ Ω ∧ Φ (p.1, X p) = p.2 ∧
      ∀ v, fderiv ℂ (fun x => Φ (p.1, x)) (X p) v = 0 → v = 0) ∧
    ∀ b ∈ ball b₀ δ, ∀ x ∈ ball x₀ δ, (b, x) ∈ Ω ∧ Φ (b, x) ∈ ball (Φ (b₀, x₀)) ε ∧
      X (b, Φ (b, x)) = x := by
  intro n I J _ _ Ω Φ b₀ x₀ L hΩ ha hΦ hL
  have cS := ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hΩ hΦ
  have cΦ : ContDiffAt ℂ 1 Φ (b₀, x₀) :=
    (cS.contDiffAt (hΩ.mem_nhds ha)).of_le (by exact_mod_cast le_top)
  have hinr : ∀ p : (Fin n → ℂ) × (I → ℂ), DifferentiableAt ℂ Φ p →
      HasFDerivAt (fun x => Φ (p.1, x))
        ((fderiv ℂ Φ p).comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (I → ℂ))) p.2 := fun p hp =>
    HasFDerivAt.comp p.2 (f := fun x => (p.1, x)) hp.hasFDerivAt (hasFDerivAt_prodMk_right p.1 p.2)
  let D := fderiv ℂ Φ (b₀, x₀)
  have hD : HasFDerivAt Φ D (b₀, x₀) := (cΦ.differentiableAt one_ne_zero).hasFDerivAt
  have hDL : D.comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (I → ℂ)) = (L : (I → ℂ) →L[ℂ] (J → ℂ)) :=
    (hinr (b₀, x₀) hD.differentiableAt).unique hL
  have hDuv : ∀ u v, D (u, v) = D (u, 0) + L v := fun u v => by
    have h1 : D (0, v) = L v := by
      have := congrArg (fun A : (I → ℂ) →L[ℂ] (J → ℂ) => A v) hDL
      simpa using this
    rw [← h1, ← map_add (f := _)]; simp
  let F₀ : ((Fin n → ℂ) × (I → ℂ)) →L[ℂ] ((Fin n → ℂ) × (J → ℂ)) :=
    (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod D
  let G₀ : ((Fin n → ℂ) × (J → ℂ)) →L[ℂ] ((Fin n → ℂ) × (I → ℂ)) :=
    (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (J → ℂ)).prod
      ((L.symm : (J → ℂ) →L[ℂ] (I → ℂ)).comp
        (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (J → ℂ) -
          (D.comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) (I → ℂ))).comp
            (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (J → ℂ))))
  have hGF : Function.LeftInverse G₀ F₀ := by
    rintro ⟨u, v⟩
    simp [F₀, G₀, hDuv u v]
  have hFG : Function.RightInverse G₀ F₀ := by
    rintro ⟨u, w⟩
    have h : G₀ (u, w) = (u, L.symm (w - D (u, 0))) := by simp [G₀]
    rw [h]
    refine Prod.ext rfl ?_
    show D (u, L.symm (w - D (u, 0))) = w
    rw [hDuv]
    simp
  let F' : ((Fin n → ℂ) × (I → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (J → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse F₀ G₀ hGF hFG
  let F : (Fin n → ℂ) × (I → ℂ) → (Fin n → ℂ) × (J → ℂ) := fun p => (p.1, Φ p)
  have hF : HasFDerivAt F (F' : ((Fin n → ℂ) × (I → ℂ)) →L[ℂ] ((Fin n → ℂ) × (J → ℂ))) (b₀, x₀) :=
    hasFDerivAt_fst.prodMk hD
  have cF : ContDiffAt ℂ 1 F (b₀, x₀) := contDiffAt_fst.prodMk cΦ
  let T := cF.toOpenPartialHomeomorph F (f' := F') hF one_ne_zero
  have hTF : ∀ p, T p = F p := fun _ => rfl
  have src : (b₀, x₀) ∈ T.source := cF.mem_toOpenPartialHomeomorph_source (f' := F') hF one_ne_zero
  have tgt : F (b₀, x₀) ∈ T.target :=
    cF.image_mem_toOpenPartialHomeomorph_target (f' := F') hF one_ne_zero
  have hinv : T.symm (F (b₀, x₀)) = (b₀, x₀) := T.left_inv src
  let O := (T.target ∩ interior {w | ContDiffAt ℂ 1 T.symm w}) ∩ (T.target ∩ T.symm ⁻¹' Ω)
  have oO : IsOpen O := (T.open_target.inter isOpen_interior).inter (T.isOpen_inter_preimage_symm hΩ)
  have mO : F (b₀, x₀) ∈ O := by
    refine ⟨⟨tgt, mem_interior_iff_mem_nhds.2 ?_⟩, tgt, ?_⟩
    · exact (cF.to_localInverse (f' := F') hF one_ne_zero).eventually (by simp)
    · simpa [hinv] using ha
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.1 oO _ mO
  have hball : ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε ⊆ O := by
    rw [ball_prod_same]; exact hε
  obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem
    (T.open_source.mem_nhds src) (hΩ.mem_nhds ha))
    (hF.continuousAt.preimage_mem_nhds (ball_mem_nhds (F (b₀, x₀)) ε0)))
  have hsec : ∀ p ∈ O, T.symm p = (p.1, (T.symm p).2) ∧ Φ (T.symm p) = p.2 := fun p hp => by
    have h : F (T.symm p) = p := T.right_inv hp.1.1
    have h1 : (T.symm p).1 = p.1 := congrArg Prod.fst h
    have h2 : Φ (T.symm p) = p.2 := congrArg Prod.snd h
    exact ⟨Prod.ext h1 rfl, h2⟩
  refine ⟨ε, min δ δ, fun p => (T.symm p).2, ε0, lt_min δ0 δ0, ?_, ?_, ?_, ?_⟩
  · exact congrArg Prod.snd hinv
  · intro p hp
    have c : ContDiffAt ℂ 1 T.symm p := interior_subset (hball hp).1.2
    exact ((differentiableAt_snd).comp p (c.differentiableAt one_ne_zero)).differentiableWithinAt
  · intro p hp
    have hpO := hball hp
    obtain ⟨e1, e2⟩ := hsec p hpO
    have hq : T.symm p ∈ Ω := hpO.2.2
    have hq' : (p.1, (T.symm p).2) ∈ Ω := e1 ▸ hq
    refine ⟨hq', by rw [← e1]; exact e2, fun v hv => ?_⟩
    have dΦ : DifferentiableAt ℂ Φ (T.symm p) := (hΦ _ hq).differentiableAt (hΩ.mem_nhds hq)
    have h1 := (hinr (T.symm p) dΦ).fderiv
    have h2 : (T.symm p).1 = p.1 := congrArg Prod.fst e1
    rw [h2] at h1
    rw [h1] at hv
    have dF : HasFDerivAt F ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod
        (fderiv ℂ Φ (T.symm p))) (T.symm p) := hasFDerivAt_fst.prodMk dΦ.hasFDerivAt
    have c : ContDiffAt ℂ 1 T.symm p := interior_subset hpO.1.2
    have dS : HasFDerivAt T.symm (fderiv ℂ T.symm p) (F (T.symm p)) := by
      rw [show F (T.symm p) = p from T.right_inv hpO.1.1]
      exact (c.differentiableAt one_ne_zero).hasFDerivAt
    have hcomp := dS.comp (T.symm p) dF
    have hid : HasFDerivAt (T.symm ∘ F) (ContinuousLinearMap.id ℂ _) (T.symm p) := by
      refine (hasFDerivAt_id (𝕜 := ℂ) (T.symm p)).congr_of_eventuallyEq ?_
      filter_upwards [T.open_source.mem_nhds (T.map_target hpO.1.1)] with q hq
      exact T.left_inv hq
    have hu := hcomp.unique hid
    have hv' : fderiv ℂ Φ (T.symm p) (0, v) = 0 := by simpa using hv
    have e0 : ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod
        (fderiv ℂ Φ (T.symm p))) (0, v) = 0 := Prod.ext (by simp) (by simpa using hv')
    have h3 := DFunLike.congr_fun hu (0, v)
    rw [ContinuousLinearMap.comp_apply, e0, map_zero] at h3
    exact (congrArg Prod.snd h3).symm
  · intro b hb x hx
    have hbx : (b, x) ∈ ball (b₀, x₀) δ := by
      rw [← ball_prod_same]; exact ⟨by simpa using hb, by simpa using hx⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hδ hbx
    have h3' : F (b, x) ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε := by
      rw [ball_prod_same]; exact h3
    exact ⟨h2, h3'.2, congrArg Prod.snd (T.left_inv h1)⟩

end GlobalTheory.CompanionTheory.HoloChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeFormAna

theorem pos_of_theta_power : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (N : ℕ) (J : Type) (Θ : J → (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → 0 < N → (∀ i, Differentiable ℂ (Θ i)) → (∀ i (l : Λ) z, Θ i (z + l) = (χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ N * Θ i z) → (∃ i, Θ i ≠ 0) → (∀ w : Fin g → ℂ, w ≠ 0 → ¬ ∀ i (t : ℂ) z, Θ i (z + t • w) = Θ i z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro g Λ hΛ hspan Hm χ N J Θ hH hχ hN hΘ htr hne hinv z hz
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨H', hH'⟩ : ∃ H' : Matrix (Fin g) (Fin g) ℂ, H' = (N : ℂ) • Hm := ⟨_, rfl⟩
  have hH'h : H'.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH', Matrix.conjTranspose_smul, hH.eq]
    simp
  have hform : ∀ u v : Fin g → ℂ, u ⬝ᵥ H'.mulVec v = (N : ℂ) * (u ⬝ᵥ Hm.mulVec v) := by
    intro u v
    rw [hH', Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hre : ∀ u : Fin g → ℂ,
      (u ⬝ᵥ H'.mulVec (star u)).re = N * (u ⬝ᵥ Hm.mulVec (star u)).re := by
    intro u
    rw [hform]
    simp
  have htr' : ∀ i (l : Λ) z, Θ i (z + l) =
      ((χ l) ^ N * Complex.exp (Real.pi * (z ⬝ᵥ H'.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H'.mulVec (star (l : Fin g → ℂ))))) * Θ i z := by
    intro i l z
    rw [htr i l z, mul_pow, ← Complex.exp_nat_mul, hform, hform]
    congr 3
    ring
  have hχ' : ∀ l, ‖(χ l) ^ N‖ = 1 := fun l => by rw [norm_pow, hχ, one_pow]
  have hbd : ∀ i, ∃ C : ℝ, ∀ z, ‖Θ i z‖ ≤
      C * Real.exp (Real.pi / 2 * (z ⬝ᵥ H'.mulVec (star z)).re) := fun i =>
    GlobalTheory.ThetaPositivity.exists_norm_le Λ hH'h (fun l => χ l ^ N) hχ' (hΘ i).continuous (htr' i)
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨C0, hC0⟩ := hbd i0
  have hnn : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := fun w =>
    not_lt.mp fun hw => hi0 (GlobalTheory.ThetaPositivity.eq_zero_of_neg hH'h (hΘ i0) hC0 (w := w)
      (by rw [hre]; exact mul_neg_of_pos_of_neg hNr hw))
  have him : ∀ w : Fin g → ℂ, (w ⬝ᵥ Hm.mulVec (star w)).im = 0 := fun w => by
    have h := congrArg Complex.im (GlobalTheory.ThetaPositivity.form_conj hH w w)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  refine lt_of_le_of_ne (hnn z) fun h0 => ?_
  open scoped ComplexOrder in
  have hpsd : Hm.PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hH, fun x => ?_⟩
    have h1 := hnn (star x)
    have h2 := him (star x)
    rw [star_star] at h1 h2
    exact Complex.le_def.mpr ⟨h1, h2.symm⟩
  have hker : Hm.mulVec (star z) = 0 :=
    hpsd.dotProduct_mulVec_zero_iff.mp (by
      rw [star_star]
      exact Complex.ext h0.symm (him z))
  have hker' : ∀ t : ℂ, H'.mulVec (star (t • z)) = 0 := by
    intro t
    rw [star_smul, Matrix.mulVec_smul, hH', Matrix.smul_mulVec, hker]
    simp
  refine hinv z hz fun i t y => ?_
  obtain ⟨C, hC⟩ := hbd i
  have hd : Differentiable ℂ fun t : ℂ => Θ i (y + t • z) :=
    (hΘ i).comp ((differentiable_const _).add (differentiable_id.smul_const z))
  have hq : ∀ t : ℂ, ((y + t • z) ⬝ᵥ H'.mulVec (star (y + t • z))).re =
      (y ⬝ᵥ H'.mulVec (star y)).re := by
    intro t
    rw [GlobalTheory.ThetaPositivity.form_add_self hH'h, hker' t]
    simp
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => Θ i (y + t • z)) := by
    refine isBounded_iff_forall_norm_le.2
      ⟨C * Real.exp (Real.pi / 2 * (y ⬝ᵥ H'.mulVec (star y)).re), ?_⟩
    rintro _ ⟨t, rfl⟩
    have h := hC (y + t • z)
    rwa [hq t] at h
  have h := hd.apply_eq_apply_of_bounded hb t 0
  simpa using h

end GlobalTheory.CompanionTheory.Ar.HodgeFormAna
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.kaehler_differentials_span_local : ∀ (S B : Type) [CommRing S] [Algebra ℚ S] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra ℂ B] (ψ : S →+* B) (φ : S →+* ℂ),
    (∀ s, ψ s - algebraMap ℂ B (φ s) ∈ IsLocalRing.maximalIdeal B) →
    ∀ (T : Set S), IsLocalRing.maximalIdeal B = Ideal.span ((fun s => ψ s - algebraMap ℂ B (φ s)) '' T) →
    ∀ (n : ℕ) (z : Fin n → S),
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    IsLocalRing.maximalIdeal B = Ideal.span (Set.range fun i => ψ (z i) - algebraMap ℂ B (φ (z i))) := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | exact GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | (intros; apply GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D <;> assumption)
end

section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem _root_.GlobalTheory.T.nonarch_valuation_of_prime : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (μ : R →*₀ ℝ) (a : R), a ≠ 0 → (∀ x, 0 ≤ μ x) → (∀ x, μ x ≤ 1) → (∀ x y, μ (x + y) ≤ max (μ x) (μ y)) → μ a < 1 → μ a ≠ 0 → ∃ (P : Ideal R) (c : ℝ), P.IsPrime ∧ P ≠ ⊥ ∧ a ∈ P ∧ 0 < c ∧ ∀ x : R, x ≠ 0 → μ x = c ^ (normalizedFactors (Ideal.span {x})).count P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.map_eq_pow_count_of_ultrametric | exact GlobalTheory.CompanionTheory.Ggeo.map_eq_pow_count_of_ultrametric | (intros; apply GlobalTheory.CompanionTheory.Ggeo.map_eq_pow_count_of_ultrametric <;> assumption)
end

section


theorem _root_.GlobalTheory.T.lu_factors_generate_same_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (A : Matrix (Fin n) (Fin n) K) (u v w : Matrix (Fin n) (Fin n) L), A.det ≠ 0 → (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) → (∀ k, v k k = 1) → (∀ l k, l < k → v l k = 0) → (∀ l k, k < l → w l k = 0) → (∀ k, w k k ≠ 0) → A.map (algebraMap K L) * u = v * w → IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) = IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
  first | exact @GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | exact GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | (intros; apply GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.alg_indep_of_same_adjoin : ∀ (K L J : Type) [Field K] [Field L] [Algebra K L] [Finite J] (x y : J → L), AlgebraicIndependent K x → IntermediateField.adjoin K (Set.range x) = IntermediateField.adjoin K (Set.range y) → AlgebraicIndependent K y := by
  first | exact @GlobalTheory.CompanionTheory.FieldGen.algebraicIndependent_of_adjoin_eq | exact GlobalTheory.CompanionTheory.FieldGen.algebraicIndependent_of_adjoin_eq | (intros; apply GlobalTheory.CompanionTheory.FieldGen.algebraicIndependent_of_adjoin_eq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.kaehler_rank_transcendence_degree : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (I : Type) [Fintype I] (u : I → L),
    AlgebraicIndependent K u → IntermediateField.adjoin K (Set.range u) = ⊤ →
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | exact GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | (intros; apply GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.frobenius_stable_subspace_element : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (V : Submodule k A),
    V ≠ ⊥ → (∀ f ∈ V, f ^ p ∈ V) → ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
  first | exact @GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed | exact GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed | (intros; apply GlobalTheory.CompanionTheory.HopfFrob.exists_frobenius_fixed_or_killed <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.subspace_contains_unit : ∀ (k : Type) [Field k] [IsAlgClosed k] (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R]
    (U : Submodule k R), (∀ x : R →ₐ[k] k, ∃ t ∈ U, x t ≠ 0) → ∃ w ∈ U, IsUnit w := by
  first | exact @GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | exact GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | (intros; apply GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.multiplicative_derivation_rank : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = D a) → ∀ z₀ : R, IsUnit z₀ → D z₀ = z₀ →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PowerDerivation.finrank_eq_and_derivation_eq_zero | exact GlobalTheory.CompanionTheory.PowerDerivation.finrank_eq_and_derivation_eq_zero | (intros; apply GlobalTheory.CompanionTheory.PowerDerivation.finrank_eq_and_derivation_eq_zero <;> assumption)
end
