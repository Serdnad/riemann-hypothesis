module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle964
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle975
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWachModuleMapMatrixReductionComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing

theorem GlobalTheory.HTSummand.Corep.mat_sum (n : ℕ) (α : Type) [CommRing α] : ∑ i : Fin n, Matrix.single i i (1:α) = 1 := by
  ext a c
  rw [Matrix.sum_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.single_apply, hb]) (by simp)]
    simp [Matrix.single_apply]
  · exact Finset.sum_eq_zero fun x _ => by
      simp only [Matrix.single_apply]; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl

theorem GlobalTheory.HTSummand.Corep.mat_sand (n : ℕ) (α : Type) [CommRing α] (i j z : Fin n) (M : Matrix (Fin n) (Fin n) α) :
    Matrix.single z i 1 * M * Matrix.single j z 1 = Matrix.scalar _ (M i j) * Matrix.single z z 1 := by
  rw [Matrix.single_mul_mul_single, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_single,
    smul_eq_mul, _root_.mul_one, _root_.mul_one, _root_.one_mul]

theorem GlobalTheory.HTSummand.Corep.exists_summand_lie_p : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → (p : C) ∈ IsLocalRing.maximalIdeal C → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  intro p _ D R _ b C _ _ _ I hI hp tR H _ _ _ _ ρ hP e he heρ _heω F hIF hFρ hFe hcompl hLie
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (p : C) ^ k = 0 := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have : (p : C) ^ k ∈ (maximalIdeal C) ^ k := Ideal.pow_mem_pow hp k
    rw [hk] at this; simpa using this
  obtain ⟨Ψ, hΨρ, hΨc, hΨN, hΨs⟩ := GlobalTheory.T.exists_matrixAction_of_padicOrderSplitting p D C k hk H ρ D.splitP.some
  haveI : NeZero D.m := ⟨D.m_pos.ne'⟩
  let σ : 𝓞 D.F →+* Module.End C H := ρ.comp (algebraMap (𝓞 D.F) D.O)
  let χ : Fin D.a → 𝓞 D.F →+* C := fun i => tR.comp (b.t i)
  let E : Fin D.m → Fin D.m → Module.End C H := fun i j => Ψ (Matrix.single i j 1)
  have hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    simp only [E, ← map_mul]
    split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, _root_.mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
  have hsum : ∑ i, E i i = 1 := by

    simp only [E, ← map_sum, GlobalTheory.HTSummand.Corep.mat_sum, map_one]
  have hρσ : ∀ c c', ρ c' * σ c = σ c * ρ c' := by
    intro c c'
    show ρ c' * ρ (algebraMap _ _ c) = ρ (algebraMap _ _ c) * ρ c'
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hEσ : ∀ i j c, E i j * σ c = σ c * E i j := fun i j c => hΨc (σ c) (hρσ c) _
  have hEe : ∀ i j, E i j * e = e * E i j := fun i j => hΨc e heρ _
  have hFE : ∀ i j, ∀ x ∈ F, E i j x ∈ F := fun i j => hΨN F hFρ _
  have hθ : ∀ (c : D.O) i j (N : Submodule C H), (∀ c', ∀ x ∈ N, σ c' x ∈ N) → ∀ x ∈ N, E 0 0 x = x →
      E 0 i (ρ c (E j 0 x)) ∈ N := by
    intro c i j N hN x hx h0
    have : E 0 i (ρ c (E j 0 x)) = Ψ (Matrix.scalar _ (D.splitP.some (c ⊗ₜ 1) i j)) (E 0 0 x) := by
      rw [← hΨρ c]
      show (Ψ (Matrix.single 0 i 1) * Ψ _ * Ψ (Matrix.single j 0 1)) x = _
      rw [← map_mul, ← map_mul, GlobalTheory.HTSummand.Corep.mat_sand, map_mul]; rfl
    rw [this, h0]
    exact hΨs _ N (fun a x hx => hN a x hx) x hx
  let π : Module.End C H := E 0 0 * e
  have hππ : π * π = π := by
    show E 0 0 * e * (E 0 0 * e) = E 0 0 * e
    rw [_root_.mul_assoc, ← _root_.mul_assoc e, ← hEe, _root_.mul_assoc, he, ← _root_.mul_assoc, hE]; simp
  have hπσ : ∀ c, σ c * π = π * σ c := by
    intro c
    show σ c * (E 0 0 * e) = E 0 0 * e * σ c
    have h1 : e * σ c = σ c * e := (heρ _).symm
    rw [_root_.mul_assoc, h1, ← _root_.mul_assoc, ← _root_.mul_assoc, hEσ]
  have hFπ : ∀ x ∈ F, π x ∈ F := fun x hx => hFE 0 0 _ (hFe x hx)
  have hFσ : ∀ c, ∀ x ∈ F, σ c x ∈ F := fun c x hx => hFρ _ x hx
  have hπapp : ∀ c x, σ c (π x) = π (σ c x) := fun c x => LinearMap.congr_fun (hπσ c) x
  have hLieπ : ∀ d ∈ LinearMap.range π, ∃ w : Fin D.a → H,
      (∀ i c, σ c (w i) - χ i c • w i ∈ F) ∧ d - ∑ i, w i ∈ F := by
    rintro d ⟨x, rfl⟩
    have hde : π x ∈ LinearMap.range e := by
      refine ⟨π x, ?_⟩
      show e (E 0 0 (e x)) = E 0 0 (e x)
      rw [← Module.End.mul_apply, ← hEe, Module.End.mul_apply, ← Module.End.mul_apply e e, he]
    obtain ⟨w, hw1, hw2⟩ := hLie _ hde
    refine ⟨fun i => π (w i), fun i c => ?_, ?_⟩
    · have := hFπ _ (hw1 i c)
      rw [map_sub, map_smul] at this
      rw [hπapp]; exact this
    · have := hFπ _ hw2

      rw [map_sub, map_sum, ← Module.End.mul_apply π π, hππ] at this
      exact this
  have hcomax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤ := by
    intro i j hij
    have h2 : Ideal.map tR (Ideal.span (Set.range fun x => b.t i x - b.t j x)) = ⊤ := by
      rw [b.comax i j hij, Ideal.map_top]
    rw [Ideal.map_span, ← Set.range_comp] at h2
    simpa [Function.comp_def, χ] using h2
  obtain ⟨n, κ, ℓ, y, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_eigenCoordinates_idempotentRange_quotient I hI σ D.a χ hcomax π hππ hπσ F hIF hFσ hFπ hcompl hLieπ
  obtain ⟨G₀, M₀, g1, g2, g3, g4, g5⟩ := GlobalTheory.T.exists_sigmaStable_summand_from_lifted_eigenCoords I hI σ hP D.a χ π hππ hπσ F hIF n κ ℓ y h1 h2 h3 h4
  exact GlobalTheory.T.moritaSpread_stableSummand_lieDecomposition I D.m E hE hsum σ hEσ ρ hθ e he hEe F hIF hFE hFe D.a χ G₀ M₀ g1 g2 g3 g4 g5
end

section

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem reps_iso : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X), (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) → ∀ (W : S.Opens) (T : Scheme.{0}) (y : HomGlue.Pt A B L M T) (πT : T ⟶ W), y.t = πT ≫ W.ι → (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ W), x.t = b ≫ W.ι → ∃! c : Z ⟶ T, y.map hL hM c = x) → ∃ e : T ≅ (u.t ⁻¹ᵁ W).toScheme, e.hom ≫ (u.t ∣_ W) = πT := by
  intro S A B _ _ L M hL hM X u hu W T y πT hy hloc
  obtain ⟨c, hc, -⟩ := hu T y
  have hcW : Set.range c ⊆ ((u.t ⁻¹ᵁ W).ι).opensRange := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    show u.t (c z) ∈ W
    have e : c ≫ u.t = πT ≫ W.ι := by rw [← hy, ← hc]; rfl
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
    exact (πT z).2
  let c' := IsOpenImmersion.lift (u.t ⁻¹ᵁ W).ι c (by simpa using hcW)
  have hc' : c' ≫ (u.t ⁻¹ᵁ W).ι = c := IsOpenImmersion.lift_fac _ _ _
  have hx : (u.map hL hM (u.t ⁻¹ᵁ W).ι).t = (u.t ∣_ W) ≫ W.ι := by
    rw [HomGlue.Pt.map_t, morphismRestrict_ι]
  obtain ⟨d, hd, -⟩ := hloc _ (u.map hL hM (u.t ⁻¹ᵁ W).ι) (u.t ∣_ W) hx
  have h1 : c' ≫ d = 𝟙 T := by
    refine (hloc T y πT hy).unique ?_ ?_
    · rw [HomGlue.Pt.map_comp, hd, ← HomGlue.Pt.map_comp, hc', hc]
    · exact HomGlue.Pt.map_id hL hM y
  have h2 : d ≫ c' = 𝟙 _ := by
    have : d ≫ c = (u.t ⁻¹ᵁ W).ι := (hu _ (u.map hL hM (u.t ⁻¹ᵁ W).ι)).unique
      (by rw [HomGlue.Pt.map_comp, hc, hd]) rfl
    rw [← cancel_mono (u.t ⁻¹ᵁ W).ι, Category.assoc, hc', this, Category.id_comp]
  refine ⟨⟨c', d, h1, h2⟩, ?_⟩
  show c' ≫ (u.t ∣_ W) = πT
  rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hc', ← hy, ← hc]
  rfl

theorem wit_of_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z : Scheme.{0}} {t t' : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} {f' : pullback A.hom t' ⟶ B.left} (h : t = t')
    (hf : ∀ e : pullback A.hom t' ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = pullback.fst _ _ →
      e ≫ pullback.snd _ _ = pullback.snd _ _ → e ≫ f = f') (w : HomGlue.Wit A B L M t f) :
    HomGlue.Wit A B L M t' f' := by
  subst h
  have := hf (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  rw [Category.id_comp] at this
  subst this
  exact w

theorem glue_pts : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB), IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → ∀ (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (x : ∀ i, HomGlue.Pt A B L M (𝒰.X i)), (∀ i j (T : Scheme.{0}) (b : T ⟶ 𝒰.X i) (c : T ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → (x i).map hL hM b = (x j).map hL hM c) → ∃ y : HomGlue.Pt A B L M Z, ∀ i, y.map hL hM (𝒰.f i) = x i := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB Z 𝒰 x hx
  obtain ⟨t, f, h⟩ := GlobalTheory.T.exists_glued_morphism_of_compatible_family S A B L M hL hM Z 𝒰 x hx
  have hw : ∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f) := by
    intro i
    have hc : pullback.fst A.hom (x i).t ≫ A.hom = (pullback.snd A.hom (x i).t ≫ 𝒰.f i) ≫ t := by
      rw [pullback.condition, Category.assoc, (h i).1]
    refine wit_of_eq (h i).1.symm (fun e e1 e2 => ?_) (x i).wit
    rw [← (h i).2 (pullback.lift _ _ hc) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, e1, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, e2, pullback.lift_snd]
  refine ⟨⟨t, f, GlobalTheory.T.glue_wit_alt hiso S A B L M hL hM hA hB hrA hrB Z 𝒰 t f hw⟩, fun i => ?_⟩
  refine HomGlue.Pt.ext' (h i).1 ?_
  show _ ≫ HomGlue.pmap A t (𝒰.f i) ≫ f = _
  exact (Category.assoc _ _ _).symm.trans ((h i).2 _
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _)))
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ 𝒰.f i) (pullback.lift_snd _ _ _))))))

theorem isSheaf_homFun : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB), IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → Presieve.IsSheaf Scheme.zariskiTopology (HomGlue.homFun A B L M hL hM) := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique
    (glue_pts hiso S A B L M hL hM hA hB hrA hrB Y 𝒰 x fun i j T b c h => hx i j T b c h)
    fun y y' h h' => GlobalTheory.T.homGlue_pt_ext_of_openCover S A B L M hL hM Y 𝒰 y y' fun i => (h i).trans (h' i).symm

theorem homFixRep_glue : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (Ix : Type) (V : Ix → Scheme.{0}) (j : ∀ i, V i ⟶ S), (∀ i, IsOpenImmersion (j i)) → (∀ s : S, ∃ i, s ∈ Set.range (j i)) → (∀ i, ∃ (A' B' : Over (V i)) (_ : GrpObj A') (_ : GrpObj B') (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)), IsGrpPullback A' A (j i) φA ∧ IsGrpPullback B' B (j i) φB ∧ QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro hiso S A B _ _ _ _ L M hA hB hL hM hrA hrB Ix V j hj hcov hR
  choose A' B' gA gB φA φB R hpA hpB hqc hsep hlft using hR
  have hy : ∀ i, ∃ y : HomGlue.Pt A B L M (R i).H, y.t = (R i).π ≫ j i ∧ ∀ (Z : Scheme.{0})
      (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V i), x.t = b ≫ j i → ∃! c : Z ⟶ (R i).H, y.map hL hM c = x := by
    intro i
    letI := gA i; letI := gB i
    exact GlobalTheory.T.exists_universal_pt_of_isGrpPullback S A B L M hL hM (V i) (j i) (A' i) (B' i) (φA i) (φB i) (R i) (hpA i) (hpB i)
  choose y hyt hyu using hy
  let W : Ix → S.Opens := fun i => (j i).opensRange
  have hW : iSup W = ⊤ := by
    refine top_le_iff.1 fun s _ => ?_
    obtain ⟨i, hi⟩ := hcov s
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  let πW : ∀ i, (R i).H ⟶ W i := fun i => (R i).π ≫ (j i).isoOpensRange.hom
  have hπW : ∀ i, πW i ≫ (W i).ι = (R i).π ≫ j i := fun i => by
    simp [πW, W]
  have hloc : ∀ i (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ W i), x.t = b ≫ (W i).ι →
      ∃! c : Z ⟶ (R i).H, (y i).map hL hM c = x := by
    intro i Z x b hb
    refine hyu i Z x (b ≫ (j i).isoOpensRange.inv) ?_
    rw [hb, Category.assoc]; simp [W]
  have hrep : (HomGlue.homFun A B L M hL hM).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover _ (isSheaf_homFun hiso S A B L M hL hM hA hB hrA hrB) (HomGlue.homProj A B L M hL hM)
      W hW (fun i => (R i).H) y πW (fun i => (hyt i).trans (hπW i).symm) hloc
  set F := HomGlue.homFun A B L M hL hM
  let X := F.reprX
  let u : HomGlue.Pt A B L M X := F.reprx
  have huniv : ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x := by
    intro Z x
    have key : ∀ c : Z ⟶ X, u.map hL hM c = F.representableBy.homEquiv c := fun c => by
      rw [F.representableBy.homEquiv_eq c]; rfl
    refine ⟨F.representableBy.homEquiv.symm x, ?_, fun c hc => ?_⟩
    · dsimp only; rw [key]; exact F.representableBy.homEquiv.apply_symm_apply x
    · dsimp only at hc; rw [key] at hc; rw [← hc]; exact (F.representableBy.homEquiv.symm_apply_apply c).symm
  obtain ⟨R0, e, he⟩ := GlobalTheory.T.exists_homFixRep_iso_of_universal S A B L M hL hM X u huniv
  have hloc' : ∀ i, ∃ e : (R i).H ≅ (u.t ⁻¹ᵁ W i).toScheme, e.hom ≫ (u.t ∣_ W i) = πW i := fun i =>
    reps_iso S A B L M hL hM X u huniv (W i) (R i).H (y i) (πW i) ((hyt i).trans (hπW i).symm) (hloc i)
  choose ei hei using hloc'
  have key : ∀ i, u.t ∣_ W i = (ei i).inv ≫ πW i := fun i => by
    rw [← hei i, Iso.inv_hom_id_assoc]
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P],
      (∀ i, P (R i).π) → P R0.π := by
    intro P _ hR
    rw [← he]
    refine (MorphismProperty.cancel_left_of_respectsIso P e.hom u.t).2 ?_
    refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun i => ?_
    rw [key i]
    refine (MorphismProperty.cancel_left_of_respectsIso P _ _).2 ?_
    exact (MorphismProperty.cancel_right_of_respectsIso P _ _).2 (hR i)
  have : IsZariskiLocalAtTarget @QuasiCompact.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : IsZariskiLocalAtTarget @LocallyOfFiniteType.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType)
  exact ⟨R0, hP @QuasiCompact hqc, hP @IsSeparated hsep, hP @LocallyOfFiniteType hlft⟩

end GlobalTheory.EndLoc.HomGlue
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem _root_.GlobalTheory.T.exists_section_nonzero_chart_of_effective_class : ∀ {X : Scheme.{0}} (N : LB X) (hN : N.IsLB), GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.cls N hN) → ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0 := by
  first | exact @GlobalTheory.EffBound.exists_sec_of_eff | exact GlobalTheory.EffBound.exists_sec_of_eff | (intros; apply GlobalTheory.EffBound.exists_sec_of_eff <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Matrix

namespace GlobalTheory.FlatDegreeCompare.ArchExists

theorem linearIndependent_of_indep {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {g n : ℕ}
    (u : HolUnif A L g) (hu : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {v : Fin n → (epsR ℂ ⟶ A)} (hv : Indep v)
    {W : Fin n → Fin g → ℂ} (hW : ∀ i, u.IsDiff (W i) (v i)) : LinearIndependent ℂ W := by
  have key : ∀ c : Fin n → ℂ, ∃ w, IsTangent w ∧ IsLieComb c v w ∧ u.IsDiff (∑ i, c i • W i) w := fun c => by
    have h := UnifDifferential.isDiff_prod u (fun i => c i • W i) _
      (fun i => Chart.isTan_scale (c i) ((Chart.isTan_iff _).2 (hv.1 i)))
      (fun i => UnifDifferential.isDiff_scale u (hW i) (c i))
    exact ⟨_, (Chart.isTan_iff _).1 h.1, (Chart.isLieComb_iff c v _).2 rfl, h.2⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  obtain ⟨w, h1, h2, h3⟩ := key c
  obtain ⟨w', h1', h2', h3'⟩ := key 0
  rw [hc] at h3
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at h3'
  obtain rfl := (hu 0).unique ⟨h1, h3⟩ ⟨h1', h3'⟩
  exact congrFun (hv.2 _ _ w h2 h2')

end GlobalTheory.FlatDegreeCompare.ArchExists
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.integralClosure_torsor_etale_height_one_abhyankar : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], P₁.height ≤ 1 → algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  first | (exact @GlobalTheory.KeyOriginBC.closureEtaleAt_of_mem_height_le_one) | (exact GlobalTheory.KeyOriginBC.closureEtaleAt_of_mem_height_le_one) | (intros; apply GlobalTheory.KeyOriginBC.closureEtaleAt_of_mem_height_le_one  <;> assumption)
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

theorem _root_.GlobalTheory.T.exists_wachModule_map_matrix_reduction_comm : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (γ : (H.W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (N' : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n' ↥(OL LL)) (u : ℤ_[l]) (un : PowerSeries ↥(OL LL)) (g : LatHom T.L T'.L), IsCrys (P.PD K) T.ρ → IsCrys (P.PD K) T'.ρ → IsFrame (H.W K 1 LL hA.2.2) T γ b N → IsFrame (H.W K 1 LL hA.2.2) T' γ b' N' → ((H.W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → IsUn l ↥(OL LL) u un → ∃ A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n, IsMapMat (H.W K 1 LL hA.2.2) g b b' A ∧ ∀ i, RedHom l ((PowerSeries.map (residue ↥(OL LL))) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((A i).map (PowerSeries.map (residue ↥(OL LL)))) ((A (i - 1)).map (PowerSeries.map (residue ↥(OL LL)))) := by
  first | exact @GlobalTheory.WachMap.exists_mapMat_redHom | exact GlobalTheory.WachMap.exists_mapMat_redHom | (intros; apply GlobalTheory.WachMap.exists_mapMat_redHom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem unit_mem_identityComponents (S : Scheme.{0}) (G : Over S) [GrpObj G] (s : S) :
    (η[G]).left s ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  have hs : G.hom ((η[G]).left s) = s := by
    have h := Over.w (η[G])
    have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [h2] at h
    rw [← Scheme.Hom.comp_apply, h]
    rfl
  show (η[G]).left s ∈ connectedComponentIn (G.hom ⁻¹' {G.hom ((η[G]).left s)}) ((η[G]).left (G.hom ((η[G]).left s)))
  rw [hs]
  exact mem_connectedComponentIn hs

theorem identityComponentOpen : GlobalTheory.Published.IdentityComponentOpen := by
  intro S G _ hG
  obtain ⟨G₀, i, j, h1, h2, h3⟩ := GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable S G
    {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}
    (GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme S G hG) (unit_mem_identityComponents S G) (GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem S G hG) (GlobalTheory.T.inv_mem_identity_component_fibre S G)
  refine ⟨G₀, i, j, h1, h2, fun x => ?_⟩
  rw [h3]
  rfl

end GlobalTheory
end

section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

theorem _root_.GlobalTheory.T.tensorLift_ev_rho_eq_taylor_slice : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I ⊕ Fin g → D), (∀ s : Fin (N + 1) → I ⊕ Fin g, ∏ a, t (s a) = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens ((I → ℂ) × (Fin g → ℂ))) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∃ ρ : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, ∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ h) = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
  first | exact @GlobalTheory.AnPer.exists_sliceTaylor_algHom | exact GlobalTheory.AnPer.exists_sliceTaylor_algHom | (intros; apply GlobalTheory.AnPer.exists_sliceTaylor_algHom <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.taylor_comp_eq_taylor_taylor_of_analyticAt : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {K : Type} [Fintype K] [DecidableEq K] (Φ : (I → ℂ) → K → ℂ) (h : (K → ℂ) → ℂ), AnalyticAt ℂ Φ 0 → Φ 0 = 0 → AnalyticAt ℂ h 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (Φ z)) = GlobalTheory.PeriodFamily.taylor N (fun k ↦ GlobalTheory.PeriodFamily.taylor N t fun z ↦ Φ z k) h := by
  first | exact @GlobalTheory.PeriodFamily.taylor_comp_chain | exact GlobalTheory.PeriodFamily.taylor_comp_chain | (intros; apply GlobalTheory.PeriodFamily.taylor_comp_chain <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.taylor_coord_and_taylor_eval_of_prod_eq_zero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → (∀ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ z i) = t i) ∧ ∀ P : MvPolynomial I ℂ, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ MvPolynomial.eval z P) = MvPolynomial.aeval t P := by
  first | exact @GlobalTheory.PeriodFamily.taylor_coord_and_eval | exact GlobalTheory.PeriodFamily.taylor_coord_and_eval | (intros; apply GlobalTheory.PeriodFamily.taylor_coord_and_eval <;> assumption)
end

section

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.ResidueEisenstein.ModConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def skewA (σ : E →ₐ[F] E) (j : ℕ) : AddSubgroup (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) where
  carrier := {c | c + cT (sigR (AF F) σ) c = 0}
  add_mem' := fun {a b} ha hb => by
    have e : cT (sigR (AF F) σ) (a + b) = cT (sigR (AF F) σ) a + cT (sigR (AF F) σ) b :=
      Matrix.ext fun i k => by simp [cT]
    change a + b + cT _ (a + b) = 0
    change a + cT _ a = 0 at ha
    change b + cT _ b = 0 at hb
    rw [e, add_add_add_comm, ha, hb, add_zero]
  zero_mem' := by
    change (0 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + cT _ 0 = 0
    ext i k; simp [cT]
  neg_mem' := fun {a} ha => by
    have e : cT (sigR (AF F) σ) (-a) = -cT (sigR (AF F) σ) a := Matrix.ext fun i k => by simp [cT]
    change -a + cT _ (-a) = 0
    change a + cT _ a = 0 at ha
    rw [e, ← neg_add, ha, neg_zero]

theorem mem_skewA {σ : E →ₐ[F] E} {j : ℕ} {c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)} :
    c ∈ skewA σ j ↔ c + cT (sigR (AF F) σ) c = 0 := Iff.rfl

end GlobalTheory.ResidueEisenstein.ModConj

end
end
