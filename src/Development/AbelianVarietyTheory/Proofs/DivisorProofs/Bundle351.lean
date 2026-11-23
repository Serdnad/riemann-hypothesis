module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle039
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle076
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle087
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle121
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartLocalizationFiniteTypeFormallyUnramifiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle278
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.SubChoose

theorem exists_num {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {U : X.Opens} (hU : IsAffineOpen U) (h : Γ(X, U)) (z : F.obj (op (X.basicOpen h))) :
    ∃ (a : F.obj (op U)) (n : ℕ), z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a := by
  letI := (F.map (homOfLE (X.basicOpen_le h)).op).hom.toAlgebra
  haveI := isLocalizationAway F α hα hU h
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj ((α.app (op U)).hom h) z
  refine ⟨a, n, ?_⟩
  have nat := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom h)
  simp only [CommRingCat.comp_apply] at nat
  rw [nat]
  exact e

theorem mem_gen_of_eq {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    {U : X.Opens} (h : Γ(X, U)) (T : Set (F.obj (op U))) {a : F.obj (op U)} (ha : a ∈ T)
    (z : F.obj (op (X.basicOpen h))) (n : ℕ)
    (e : z * ((α.app (op (X.basicOpen h))).hom
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h)) ^ n =
        (F.map (homOfLE (X.basicOpen_le h)).op).hom a) :
    z ∈ gen F α (X.basicOpen_le h) T := by
  have hu0 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) :=
    X.toRingedSpace.isUnit_res_basicOpen h
  obtain ⟨u, hu⟩ := hu0
  have key : (α.app (op (X.basicOpen h))).hom (X.presheaf.map (homOfLE (X.basicOpen_le h)).op h) *
      (α.app (op (X.basicOpen h))).hom ↑u⁻¹ = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  have hz : z = (F.map (homOfLE (X.basicOpen_le h)).op).hom a *
      ((α.app (op (X.basicOpen h))).hom ↑u⁻¹) ^ n := by
    rw [← e, mul_assoc, ← mul_pow, key, one_pow, mul_one]
  rw [hz]
  exact mul_mem (res_mem_gen F α _ T ha) (pow_mem (algebraMap_mem_gen F α _ T _) n)

end GlobalTheory.SubChoose

theorem GlobalTheory.sub_choose_finite : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  intro X hX F α hα ι _ V hV S hS
  choose s hs1 hs2 using fun i j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX (V j) (V i) (hV j) (hV i)
  have hDi : ∀ i j, ∀ h ∈ s i j, X.basicOpen h ≤ V i := by
    intro i j h hh
    obtain ⟨r, hr⟩ := hs1 i j h hh
    rw [hr]
    exact X.basicOpen_le r
  haveI : ∀ i, Finite (S i) := fun i => (hS i).to_subtype
  choose a n ha using fun (j : ι) (p : Σ i, (S i) × (s i j)) =>
    GlobalTheory.SubChoose.exists_num F α hα (hV j) p.2.2.1
      ((F.map (homOfLE (hDi p.1 j p.2.2.1 p.2.2.2)).op).hom p.2.1.1)
  refine ⟨fun j => Set.range (a j), fun j => Set.finite_range _, ?_⟩
  intro i x hx
  rw [SetLike.mem_coe, mem_sub]
  intro j W' hW' hWi hWj
  apply GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) (V i) (Set.range (a j)) x _ W' hW' hWi hWj
  intro y hy
  have hy' : y ∈ ((V j ⊓ V i : X.Opens) : Set X) := ⟨hy.2, hy.1⟩
  have := hs2 i j hy'
  simp only [Set.mem_iUnion] at this
  obtain ⟨h, hh, hyh⟩ := this
  refine ⟨X.basicOpen h, (hV j).basicOpen h, hyh, hDi i j h hh, X.basicOpen_le h, ?_⟩
  exact GlobalTheory.SubChoose.mem_gen_of_eq F α h _ (Set.mem_range_self (⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩ : Σ i, (S i) × (s i j))) _ _
    (ha j ⟨i, ⟨x, hx⟩, ⟨h, hh⟩⟩)
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.GaussPairing

section Coord

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type} [Fintype ι]

theorem norm_sq_eq_dot (e : V ≃L[ℝ] (ι → ℂ)) (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) (v : V) :
    (‖v‖ : ℂ) ^ 2 = star (e v) ⬝ᵥ e v := by
  have h : ((‖v‖ ^ 2 : ℝ) : ℂ) = ((∑ i, ‖e v i‖ ^ 2 : ℝ) : ℂ) := by rw [he v]
  push_cast at h
  rw [h, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Complex.conj_mul' _).symm

theorem inner_eq_dot (e : V ≃L[ℝ] (ι → ℂ)) (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) (x y : V) :
    ((⟪x, y⟫ : ℝ) : ℂ) = (1 / 2 : ℂ) * (star (e x) ⬝ᵥ e y + star (e y) ⬝ᵥ e x) := by
  have h : ((‖x + y‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_add_sq_real]
  push_cast at h
  rw [norm_sq_eq_dot e he (x + y), norm_sq_eq_dot e he x, norm_sq_eq_dot e he y, map_add (f := _), star_add,
    add_dotProduct, dotProduct_add, dotProduct_add] at h
  linear_combination (-1 / 2 : ℂ) * h

theorem star_mulVec_dot (g : Matrix ι ι ℂ) (z w : ι → ℂ) :
    star (g *ᵥ z) ⬝ᵥ w = star z ⬝ᵥ gᴴ *ᵥ w := by
  rw [star_mulVec, dotProduct_mulVec]

end Coord

theorem posDef_one_add {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (g : Matrix κ ι ℂ) :
    (1 + gᴴ * g).PosDef :=
  PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self g)

theorem integral_sum_elim {ι : Type} [Fintype ι] (F : (ι ⊕ ι → ℂ) → ℂ) (hF : Integrable F) :
    ∫ z : ι → ℂ, ∫ w : ι → ℂ, F (Sum.elim z w) = ∫ x, F x := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℂ)
  have hF' : Integrable (fun p => F ((MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℂ).symm p))
      ((volume : Measure (ι → ℂ)).prod volume) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  rw [← hmp.integral_comp' F, Measure.volume_eq_prod, integral_prod _ hF']
  rfl

private lemma half_smul_add_conjTranspose_eq_of_hermitian {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (hX : Xᴴ = X) :
    (1 / 2 : ℂ) • X + ((1 / 2 : ℂ) • X)ᴴ = X := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, hX, h2, ← smul_add, GlobalTheory.RealWeil.PosDet.half_add_self]

private lemma half_cross_add_conjTranspose_eq_mul {ι : Type} [Fintype ι] [DecidableEq ι] (s a b : Matrix ι ι ℂ) (hs : sᴴ = s) :
    (1 / 2 : ℂ) • (aᴴ * (1 + s) * b) + ((1 / 2 : ℂ) • (bᴴ * (1 - s) * a))ᴴ = 0 + aᴴ * b := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_sub, conjTranspose_one, hs, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, zero_add]
  module

private lemma half_cross_add_conjTranspose_eq_mul_swap {ι : Type} [Fintype ι] [DecidableEq ι] (s a b : Matrix ι ι ℂ) (hs : sᴴ = s) :
    (1 / 2 : ℂ) • (bᴴ * (1 - s) * a) + ((1 / 2 : ℂ) • (aᴴ * (1 + s) * b))ᴴ = 0 + bᴴ * a := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_add, conjTranspose_one, hs, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, zero_add]
  module

theorem lam_mu_eq : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι] (e : V ≃L[ℝ] (ι → ℂ)), (∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) → ∀ (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 → ∀ J : V ≃ₗᵢ[ℝ] V, (∀ v, e (J v) = I • s *ᵥ e v) → (∀ (g : Matrix ι ι ℂ) (k : V → V), gᴴ * s * g = s → (∀ v, e (k v) = g *ᵥ e v) → dP s g ≠ 0 ∧ dP s g⁻¹ = star (dP s g) ∧ lam k = (dP s g * dP s g⁻¹)⁻¹) ∧ ∀ (g₁ g₂ : Matrix ι ι ℂ) (k₁ k₂ : V → V), g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s → (∀ v, e (k₁ v) = g₁ *ᵥ e v) → (∀ v, e (k₂ v) = g₂ *ᵥ e v) → mu J k₁ k₂ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by
  intro V _ _ _ _ _ ι _ _ e he s hs hss J hJ
  have hmp := GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords V ι e he
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  obtain ⟨hd1, hd2⟩ := GlobalTheory.RealWeil.PosDet.detPlus_identities ι s hs hss
  have hHerm : ∀ g : Matrix ι ι ℂ, (1 + gᴴ * g)ᴴ = 1 + gᴴ * g := fun g => by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
  refine ⟨fun g k hg hk => ?_, fun g₁ g₂ k₁ k₂ hg₁ hg₂ hk₁ hk₂ => ?_⟩
  · obtain ⟨A, hA⟩ : ∃ A : Matrix ι ι ℂ, A = (1 / 2 : ℂ) • (1 + gᴴ * g) := ⟨_, rfl⟩
    have hAA : A + Aᴴ = 1 + gᴴ * g := by rw [hA]; exact half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g)
    obtain ⟨hA0, -, hAint⟩ := GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part ι A (by rw [hAA]; exact posDef_one_add g)
    obtain ⟨hstar, hdet⟩ := hd1 g hg
    rw [← hA] at hdet
    have hpt : ∀ u, gau u * gau (k u) = cexp (-(π : ℂ) * (star (e u) ⬝ᵥ A *ᵥ e u)) := by
      intro u
      simp only [gau, ← Complex.exp_add]
      congr 1
      rw [norm_sq_eq_dot e he u, norm_sq_eq_dot e he (k u), hk u, star_mulVec_dot, hA, smul_mulVec,
        dotProduct_smul, add_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add, smul_eq_mul]
      ring
    have hlam : lam k = A.det⁻¹ :=
      calc lam k = ∫ u, cexp (-(π : ℂ) * (star (e u) ⬝ᵥ A *ᵥ e u)) := by
            unfold lam
            congr 1
            funext u
            exact hpt u
        _ = ∫ z, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) :=
            hmp.integral_comp hme (fun z => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)))
        _ = A.det⁻¹ := hAint
    refine ⟨fun h0 => hA0 (by rw [hdet, h0, zero_mul]), hstar, ?_⟩
    rw [hlam, hdet]
  · obtain ⟨M, hM⟩ : ∃ M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ, M =
        fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
          ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂)) := ⟨_, rfl⟩
    have hdet2 := hd2 g₁ g₂ hg₁ hg₂
    rw [← hM] at hdet2
    have hMM : M + Mᴴ = 1 + (fromCols g₁ g₂)ᴴ * fromCols g₁ g₂ := by
      rw [hM, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
        fromBlocks_conjTranspose, fromBlocks_add, ← fromBlocks_one, fromBlocks_add,
        half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g₁), half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g₂), half_cross_add_conjTranspose_eq_mul s g₁ g₂ hs,
        half_cross_add_conjTranspose_eq_mul_swap s g₁ g₂ hs]
    obtain ⟨-, hMi, hMint⟩ := GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part (ι ⊕ ι) M (by rw [hMM]; exact posDef_one_add _)
    have hpt : ∀ u v, gau u * gau v * (cexp (π * I * (omJ J (k₁ u) (k₂ v) : ℂ)) * gau (k₁ u + k₂ v)) =
        cexp (-(π : ℂ) * (star (Sum.elim (e u) (e v)) ⬝ᵥ M *ᵥ Sum.elim (e u) (e v))) := by
      intro u v
      simp only [gau, ← Complex.exp_add]
      congr 1
      have hsum : star (Sum.elim (e u) (e v)) = Sum.elim (star (e u)) (star (e v)) := by
        funext i
        cases i <;> rfl
      have hA1 : ∀ (g : Matrix ι ι ℂ) (z : ι → ℂ),
          star z ⬝ᵥ ((1 / 2 : ℂ) • (1 + gᴴ * g)) *ᵥ z = 1 / 2 * (star z ⬝ᵥ z + star (g *ᵥ z) ⬝ᵥ g *ᵥ z) := by
        intro g z
        rw [smul_mulVec, dotProduct_smul, add_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add,
          ← star_mulVec_dot, smul_eq_mul]
      have hB1 : star (e u) ⬝ᵥ ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂)) *ᵥ e v =
          1 / 2 * (star (g₁ *ᵥ e u) ⬝ᵥ g₂ *ᵥ e v + star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v)) := by
        rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dot,
          add_mulVec, one_mulVec, dotProduct_add, smul_eq_mul]
      have hC1 : star (e v) ⬝ᵥ ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) *ᵥ e u =
          1 / 2 * (star (g₂ *ᵥ e v) ⬝ᵥ g₁ *ᵥ e u - star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u)) := by
        rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dot,
          sub_mulVec, one_mulVec, dotProduct_sub, smul_eq_mul]
      have hJ1 : star (g₁ *ᵥ e u) ⬝ᵥ I • s *ᵥ (g₂ *ᵥ e v) = I * (star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v)) := by
        rw [dotProduct_smul, smul_eq_mul]
      have hJ2 : star (I • s *ᵥ (g₂ *ᵥ e v)) ⬝ᵥ g₁ *ᵥ e u =
          -I * (star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u)) := by
        rw [star_smul, smul_dotProduct, star_mulVec_dot, hs, smul_eq_mul, Complex.star_def, Complex.conj_I]
      have hN : star (g₁ *ᵥ e u + g₂ *ᵥ e v) ⬝ᵥ (g₁ *ᵥ e u + g₂ *ᵥ e v) =
          star (g₁ *ᵥ e u) ⬝ᵥ g₁ *ᵥ e u + star (g₁ *ᵥ e u) ⬝ᵥ g₂ *ᵥ e v +
            (star (g₂ *ᵥ e v) ⬝ᵥ g₁ *ᵥ e u + star (g₂ *ᵥ e v) ⬝ᵥ g₂ *ᵥ e v) := by
        rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add]
      unfold omJ
      rw [inner_eq_dot e he, hJ, norm_sq_eq_dot e he u, norm_sq_eq_dot e he v,
        norm_sq_eq_dot e he (k₁ u + k₂ v), map_add, hk₁, hk₂, hJ1, hJ2, hN, hM, hsum, fromBlocks_mulVec,
        sumElim_dotProduct_sumElim]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_add]
      rw [hA1, hA1, hB1, hC1]
      linear_combination ((π : ℂ) / 2 * (star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v) -
        star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u))) * Complex.I_sq
    calc mu J k₁ k₂ = ∫ u, ∫ v, cexp (-(π : ℂ) * (star (Sum.elim (e u) (e v)) ⬝ᵥ M *ᵥ Sum.elim (e u) (e v))) := by
          unfold mu
          congr 1
          funext u
          congr 1
          funext v
          exact hpt u v
      _ = ∫ u, ∫ w, cexp (-(π : ℂ) * (star (Sum.elim (e u) w) ⬝ᵥ M *ᵥ Sum.elim (e u) w)) := by
          congr 1
          funext u
          exact hmp.integral_comp hme (fun w => cexp (-(π : ℂ) * (star (Sum.elim (e u) w) ⬝ᵥ M *ᵥ Sum.elim (e u) w)))
      _ = ∫ z, ∫ w, cexp (-(π : ℂ) * (star (Sum.elim z w) ⬝ᵥ M *ᵥ Sum.elim z w)) :=
          hmp.integral_comp hme (fun z => ∫ w, cexp (-(π : ℂ) * (star (Sum.elim z w) ⬝ᵥ M *ᵥ Sum.elim z w)))
      _ = ∫ x, cexp (-(π : ℂ) * (star x ⬝ᵥ M *ᵥ x)) := integral_sum_elim _ hMi
      _ = M.det⁻¹ := hMint
      _ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by rw [hdet2]

end GlobalTheory.RealWeil.GaussPairing
end

section

open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerStep

open GlobalTheory.KummerAlg

theorem p1 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), 0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := GlobalTheory.T.kummerAlgebra_finite_projective_faithfullyFlat
theorem p2 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective
theorem p4 : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 → ∃ φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => CommRing.Pic.AsModule c) B, ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := GlobalTheory.T.exists_multilinear_form_of_pic_torsion

theorem free_of_section (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B) (hq : 0 < q)
    (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p)
    (s : Alg φ →ₐ[B] B) : Module.Free B L := by
  let f : L →ₗ[B] B := s.toLinearMap ∘ₗ gen φ
  have hf : ∀ e : L, f e ^ q = φ (fun _ => e) := fun e => by
    have := congrArg s (prod_gen φ (fun _ => e))
    simpa [f, map_prod, Finset.prod_const, AlgHom.commutes] using this
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (LinearMap.range f) h
    obtain ⟨e, he⟩ := hφ m hm.isPrime
    apply he
    rw [← hf e]
    exact Ideal.pow_mem_of_mem _ (hle ⟨e, rfl⟩) q hq
  exact Module.Free.of_equiv
    (LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hsurj)).symm

theorem kummer_step : ∀ (B : Type) [CommRing B] (q : ℕ), 0 < q → IsUnit (q : B) →
    (∃ ζ : B, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) →
    (∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
      Module.FaithfullyFlat B D → ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
      Function.Bijective (Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) → Nonempty (D →ₐ[B] B)) →
    ∀ c : CommRing.Pic B, c ^ q = 1 → c = 1 := by
  intro B _ q hq hqu ⟨ζ, hζ, hζk⟩ hT c hc
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨φ, hφ⟩ := p4 B q c hc
  obtain ⟨hfin, hproj, hff⟩ := p1 B (CommRing.Pic.AsModule c) q φ hq hφ
  obtain ⟨s⟩ := hT (Alg φ) hfin hproj hff (act φ ζ hζ) (p2 B (CommRing.Pic.AsModule c) q φ hqu hφ ζ hζ hζk)
  have := free_of_section B (CommRing.Pic.AsModule c) q φ hq hφ s
  rw [← CommRing.Pic.mk_eq_self (M := c), CommRing.Pic.mk_eq_one_iff_free]
  exact this

end GlobalTheory.KummerStep
end
end

section

open scoped Classical

theorem _root_.GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    ∀ x : X, ∑ᶠ O : {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) //
        (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x},
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O.1)) : ℂ)) *
          f (Quotient.out O.1).elt (Quotient.out O.1).pt =
      (1 / (Nat.card (MulAction.stabilizer H x) : ℂ)) * ∑ᶠ γ : H, f γ x := by
  first | exact @GlobalTheory.PtFib.ptFib_mass | exact GlobalTheory.PtFib.ptFib_mass | (intros; apply GlobalTheory.PtFib.ptFib_mass <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.finrank_weightSpace_projective_tensor_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  first | (exact @GlobalTheory.WtRank.weight_finrank_eq) | (exact GlobalTheory.WtRank.weight_finrank_eq) | (intros; apply GlobalTheory.WtRank.weight_finrank_eq  <;> assumption)
end

section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (a b : F), ((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  first | exact @GlobalTheory.GaussExt.norm_gEmb | exact GlobalTheory.GaussExt.norm_gEmb | (intros; apply GlobalTheory.GaussExt.norm_gEmb <;> assumption)
end

section

open IsLocalRing

namespace GlobalTheory.DenseSec
open TensorProduct

theorem exists_poly_vanishing_of_fibre : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by
  intro R _ A _ _ g t h hE Ω _ _ hirr f hf
  have hN : (nilradical (TensorProduct R Ω A)).IsPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 hirr
  have kill : ∀ (a : A →ₐ[R] Ω) (x : TensorProduct R Ω A), x ∈ nilradical (TensorProduct R Ω A) → GlobalTheory.DenseSec.pt a x = 0 := by
    intro a x hx
    exact ((mem_nilradical.1 hx).map (GlobalTheory.DenseSec.pt a)).eq_zero
  have pth : ∀ (a : A →ₐ[R] Ω) (x : A), GlobalTheory.DenseSec.pt a (1 ⊗ₜ[R] x) = a x := by
    intro a x
    simp [GlobalTheory.DenseSec.pt]
  have ptw : ∀ (a : A →ₐ[R] Ω) (w : Ω), GlobalTheory.DenseSec.pt a (w ⊗ₜ[R] 1) = w := by
    intro a w
    simp [GlobalTheory.DenseSec.pt]
  by_cases h1 : (1 ⊗ₜ[R] h : TensorProduct R Ω A) ∈ nilradical (TensorProduct R Ω A)
  · refine ⟨1, one_ne_zero, fun a ha _ => ?_⟩
    exact absurd (by rw [← pth a h]; exact kill a _ h1) ha
  set N := nilradical (TensorProduct R Ω A)
  set u : TensorProduct R Ω A ⧸ N := Ideal.Quotient.mk N (1 ⊗ₜ[R] h)
  have hu : u ≠ 0 := by
    simpa [u, Ideal.Quotient.eq_zero_iff_mem] using h1
  letI : IsDomain (TensorProduct R Ω A ⧸ N) := Ideal.Quotient.isDomain N
  have hle : Submonoid.powers u ≤ nonZeroDivisors (TensorProduct R Ω A ⧸ N) := powers_le_nonZeroDivisors_of_noZeroDivisors hu
  letI : IsDomain (Localization.Away u) := IsLocalization.isDomain_localization hle
  obtain ⟨hFT, hFU⟩ := GlobalTheory.T.etaleChart_localization_finiteType_formallyUnramified R A g t h hE Ω N
  letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away u) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  have hf' : algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N f) ≠ 0 := by
    intro h0
    rw [map_eq_zero_iff _ (IsLocalization.injective (Localization.Away u) hle), Ideal.Quotient.eq_zero_iff_mem] at h0
    exact hf (mem_nilradical.1 h0)
  obtain ⟨Q, hQ, d, hd⟩ := GlobalTheory.T.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified' (MvPolynomial (Fin g) Ω) (Localization.Away u) _ hf'
  refine ⟨Q, hQ, fun a ha hfa => ?_⟩
  let φ : TensorProduct R Ω A ⧸ N →+* Ω := Ideal.Quotient.lift N (GlobalTheory.DenseSec.pt a).toRingHom (fun x hx => kill a x hx)
  have hφu : IsUnit (φ u) := by
    simp only [φ, u, Ideal.Quotient.lift_mk]
    exact isUnit_iff_ne_zero.2 (by simpa [pth] using ha)
  let χ : Localization.Away u →+* Ω := IsLocalization.Away.lift u hφu
  have hχ : ∀ x : TensorProduct R Ω A, χ (algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N x)) = GlobalTheory.DenseSec.pt a x := by
    intro x
    simp [χ, φ, IsLocalization.Away.lift]
  have hP : χ.comp (algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away u)) = MvPolynomial.eval₂Hom (RingHom.id Ω) (fun i => a (t i)) := by
    apply MvPolynomial.ringHom_ext
    · intro w
      show χ (MvPolynomial.aeval _ (MvPolynomial.C w)) = _
      have e : algebraMap Ω (TensorProduct R Ω A ⧸ N) w = Ideal.Quotient.mk N (w ⊗ₜ[R] 1) := rfl
      rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ N) (Localization.Away u), e, hχ, ptw]
      simp
    · intro i
      show χ (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, hχ, pth]
      simp
  have := congrArg χ hd
  rw [← RingHom.comp_apply, hP, map_mul, hχ, hfa, zero_mul] at this
  exact this

end GlobalTheory.DenseSec
end

section

open IsLocalRing
open scoped TensorProduct

theorem _root_.GlobalTheory.T.algHom_quotient_span_pow_eq_of_etaleLow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ (n : ℕ) (f f' : C →ₐ[R] R ⧸ Ideal.span {t} ^ n),
      (∀ c : C, f c - f' c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t}) → f = f' := by
  first | (exact @GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (exact GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (intros; apply GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow  <;> assumption)
end
