module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle066
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle026
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsGradedMatrixEigenBound
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HilbertSchmidtProjectionBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

theorem _root_.GlobalTheory.T.FubiniParabolicMultiple : CompanionTheory.RgExh.Dec.N.S.Fub2 :=
  GlobalTheory.CompanionTheory.FubNM.fub2
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem fibAc_of_closed_fibres : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) [LocallyOfFiniteType (t ≫ b)] (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    (hfib : ∀ (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z), s ≫ t ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X →
      σ ≫ q = a ≫ s ≫ t → FibAc a (G.pull σ)), FibAc f (G.pull π) := by
  intro k _ _ X T Z a b p q H ha _ _ G hG R _ t _ Y π f Hy hfib κ _ _ D hD hc n
  have HP := Hy.paste_horiz H
  have hproj : IsProjBy f := by
    obtain ⟨c, hcb⟩ := Spec.map_surjective (t ≫ b)
    have HP' : IsPullback (π ≫ p) f a (spMap c.hom) := by
      have : spMap c.hom = t ≫ b := by
        rw [← hcb]; rfl
      rw [this]; exact HP
    exact (ProjSpace.isProjBy_iff_isProjOver f).2
      (ProjSpace.isProjOver_of_isPullback_spMap c.hom HP'
        ((ProjSpace.isProjBy_iff_isProjOver a).1 ha))
  haveI : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) HP inferInstance
  haveI : Flat f := MorphismProperty.of_isPullback (P := @Flat) HP inferInstance
  haveI hN : IsNoetherianRing R := by
    haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
      LocallyOfFiniteType.isLocallyNoetherian (t ≫ b)
    exact (isLocallyNoetherian_Spec (R := CommRingCat.of R)).1 inferInstance
  have hM := LB.isLB_pull hG π
  have hI := GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated f hD
  have hflat : ∀ p, Module.Flat R ((cechLB f (G.pull π) D).X p) := flat_cechLB_X f hM hI
  have hfin := GlobalTheory.T.finite_cechLB_homology_of_affine_cover R Y f _ κ D hM inferInstance hproj hD hc
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine GlobalTheory.MumfordAway.subsingleton_of_points k R (t ≫ b) _ fun χ hχ => ?_
  refine exists_smul_homology_eq_zero_of_acyclic_fibre R k χ _ (Fintype.card κ)
    (fun p hp => isZero_cechLB_X _ _ _ hp.le) hflat hfin ?_ n
  have h' := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  have P1 := h'.paste_horiz HP
  rw [hχ] at P1
  let u := pullback.fst f (Spec.map (CommRingCat.ofHom χ))
  let v := pullback.snd f (Spec.map (CommRingCat.ofHom χ))
  let e := u ≫ π ≫ p
  haveI : IsIso e := P1.isIso_fst_of_isIso
  have he : e ≫ a = v := P1.w.trans (Category.comp_id _)
  let σ : X ⟶ Z := inv e ≫ u ≫ π
  have hσp : σ ≫ p = 𝟙 X := by
    simp only [σ, Category.assoc]
    exact IsIso.inv_hom_id e
  have hes : e ≫ σ = u ≫ π := by simp [σ]
  have hσq : σ ≫ q = a ≫ Spec.map (CommRingCat.ofHom χ) ≫ t := by
    rw [← cancel_epi e, ← Category.assoc e σ, hes, ← Category.assoc e a, he, Category.assoc u, Hy.w]
    exact (reassoc_of% h'.w) t
  have hac := hfib (Spec.map (CommRingCat.ofHom χ)) σ hχ hσp hσq κ (fun i => inv e ⁻¹ᵁ u ⁻¹ᵁ D i)
    (fun i => (isAffineOpen_preimage_of_isPullback h' (hD i)).preimage_of_isIso _)
    (by rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hc]; rfl)
  obtain ⟨i₁⟩ := cechLB_pull_iso_of_isOpenImmersion k X a (G.pull σ) _ e κ
    (fun i => inv e ⁻¹ᵁ u ⁻¹ᵁ D i) (LB.isLB_pull hG σ)
    (fun i => by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  have hD' : (fun i => e ⁻¹ᵁ inv e ⁻¹ᵁ u ⁻¹ᵁ D i) = fun i => u ⁻¹ᵁ D i := funext fun i => by
    rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]; rfl
  rw [he, hD'] at i₁
  obtain ⟨w₁, hw₁⟩ : ∃ w : LB.Iso ((G.pull σ).pull e) (G.pull (u ≫ π)), w.IsGen :=
    hes ▸ GlobalTheory.MumfordSupport.exists_iso_pull_pull hG σ e
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.MumfordSupport.exists_iso_pull_pull hG π u
  have hL₁ : ((G.pull σ).pull e).IsLB := LB.isLB_pull (LB.isLB_pull hG σ) e
  have hL₂ : ((G.pull π).pull u).IsLB := LB.isLB_pull hM u
  have hL₃ : (G.pull (u ≫ π)).IsLB := LB.isLB_pull hG _
  have c₁ := cechLBCongr v (fun i => u ⁻¹ᵁ D i) hL₁ hL₃ w₁ hw₁
  have c₂ := cechLBCongr v (fun i => u ⁻¹ᵁ D i) hL₂ hL₃ w₂ hw₂
  have E := cechLBBaseChangeIso hM h' hI ≪≫ c₂ ≪≫ c₁.symm ≪≫ i₁
  exact fun m => (hac m).of_iso E.symm

end GlobalTheory.CompanionTheory.PointSurjectivity
end

section

open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo
theorem _root_.GlobalTheory.T.exists_graded_matrix_eigen_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε) (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) (f : ℝ → ℝ) (α β : ℝ), (∀ l : ℝ, 0 < l → (f l = -1 ∨ f l = 0 ∨ f l = 1) ∧ f l⁻¹ = - f l) → (∀ i, f (hT.eigenvalues i) = -1 → α ≤ hT.eigenvalues i) → (∀ i, f (hT.eigenvalues i) = 0 → β⁻¹ ≤ hT.eigenvalues i) → (∃ i, f (hT.eigenvalues i) ≠ 0) → ∃ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' ∧ ∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM g⁻¹ *ᵥ y) := by
  exact SpecGrad.grading_of_spectral
end

section

open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

theorem _root_.GlobalTheory.T.hilbert_schmidt_projection_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (A₀ A' : Matrix (Fin n) (Fin n) ℂ) (α β : ℝ) (x : PSub ε A₀) (k : S7.KG ε), IsGrad ε A₀ → IsGrad ε A' → Formalism.REAL.hs (Pm A₀ - Pm A') ≤ 1 / 4 → Formalism.REAL.hs (Pp A₀ - Pp A') ≤ 1 / 4 → 1 ≤ β → β ≤ α → (∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM ((x : S7.UJ ε) * (k : S7.UJ ε))⁻¹ *ᵥ y)) → Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Pm A₀) ≤ 4 * n / α ∧ Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Pz A₀) ≤ 4 * n * β := by
  exact Est.est
end
