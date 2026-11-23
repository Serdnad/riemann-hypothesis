module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle762
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
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CharPMatrix

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]

def redHom : ℤ_[p] →+* k := (ZMod.castHom (dvd_refl p) k).comp PadicInt.toZMod

lemma exists_nat_add (z : ℤ_[p]) : ∃ n : ℕ, ∃ w : ℤ_[p], z = n + p * w := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨PadicInt.zmodRepr z, w, by rw [mul_comm, hw]; ring⟩

variable (B : Type) [Ring B] [Algebra k B]

def tensorPadicEquiv : B ⊗[ℤ] ℤ_[p] ≃ₐ[k] B :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (AlgHom.id k B)
      (((algebraMap k B).comp (redHom p k)).toIntAlgHom)
      (by intro x y; exact Algebra.commute_algebraMap_right _ _))
    Algebra.TensorProduct.includeLeft
    (by ext b; simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply]; erw [Algebra.TensorProduct.lift_tmul]; simp)
    (by
      apply Algebra.TensorProduct.ext'
      intro b z
      obtain ⟨n, w, rfl⟩ := exists_nat_add p z
      have hp : (p : B) = 0 := by
        rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero, map_zero]
      simp [redHom, Algebra.TensorProduct.lift_tmul]
      have h1 : b ⊗ₜ[ℤ] ((p : ℤ_[p]) * w) = 0 := by
        rw [show ((p : ℤ_[p]) * w) = (p : ℤ) • w by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, hp, zero_mul,
          TensorProduct.zero_tmul]
      have h2 : b ⊗ₜ[ℤ] (n : ℤ_[p]) = (b * n) ⊗ₜ[ℤ] 1 := by
        rw [show (n : ℤ_[p]) = (n : ℤ) • (1 : ℤ_[p]) by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, Nat.cast_comm]
      rw [TensorProduct.tmul_add, h1, h2, add_zero])

def matrixBaseChange (R : Type) [CommRing R] (K : Type) [CommRing K] [Algebra R K]
    (n : Type) [Fintype n] [DecidableEq n] : K ⊗[R] Matrix n n R ≃ₐ[K] Matrix n n K :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n R K).symm.toRingEquiv) (by
    intro c
    simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Algebra.algebraMap_eq_smul_one])

end GlobalTheory.CharPMatrix

namespace GlobalTheory.UPel.HT


open GlobalTheory.CharPMatrix in
theorem Datum.charP_tensor_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k]
    [CharP k p] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  intro p _ D k _ _ _
  obtain ⟨e⟩ := D.splitP
  have E0 : k ⊗[𝓞 D.F] (𝓞 D.F ⊗[ℤ] ℤ_[p]) ≃ₐ[k] k :=
    (Algebra.TensorProduct.cancelBaseChange ℤ (𝓞 D.F) k k ℤ_[p]).trans (tensorPadicEquiv p k k)
  have E1 := (Algebra.TensorProduct.assoc ℤ (𝓞 D.F) (𝓞 D.F) D.O (𝓞 D.F) ℤ_[p]).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid (𝓞 D.F) (𝓞 D.F) D.O) (AlgEquiv.refl (R := ℤ) (A₁ := ℤ_[p])))
  have E2 := E1.trans e
  exact ⟨(Algebra.TensorProduct.congr E0.symm (AlgEquiv.refl (R := 𝓞 D.F) (A₁ := D.O))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl
      ((Algebra.TensorProduct.comm (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
        (E2.trans (matrixEquivTensor (Fin D.m) (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]))))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p])
      (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F))).symm.trans
    ((Algebra.TensorProduct.congr E0 AlgEquiv.refl).trans
    (matrixBaseChange (𝓞 D.F) k (Fin D.m))))))⟩

end GlobalTheory.UPel.HT
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {q' : Y' ⟶ Sp R'} {χ : Y' ⟶ Y}
    (k : IsPullback χ q' q (spMap σ)) : IsClosedImmersion χ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) k.flip this

theorem tmul_pull_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → CohomZeroIsConstants (OAff q') → ∀ (u : HO1 s₀) (y : HO1 s), TMul h₀.w t u y → pullHO1 w y = 0 → pullHO1 w₀ u = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀
    _hψ' hψ₀ hE _hs hq hC u y hT hy
  obtain ⟨hσ, hker, hσ₀, hker₀⟩ := hE
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_surj hσ k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_surj hσ₀ k₀
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_surj hσ₀ h₀
  have ht : σ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  obtain ⟨f, c, hcf, hcy, hred⟩ := hT

  have h1 : (pairPull w).pull1 y = 0 := by
    have e := isPullO_pullHO1 w y
    unfold IsPullO at e
    rw [e, hy, map_zero]
  rw [← hcy, CoefMap.pullCohomologyOne_class, GlobalTheory.CatCoh.H1.mk_eq_zero] at h1
  obtain ⟨g, hg⟩ := h1
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : C1 (OPair ψ q), ∀ T T' (a : T ⟶ T'),
      f₁ T T' a = (pairPull w).α T' (f _ _ ((pairPull w).G.map a)) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hg' : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'), g T' - mp (OPair ψ q) a (g T) = t • f₁ T T' a := by
    intro T T' a
    have e := congrFun (congrFun (congrFun hg T) T') a
    rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
    rw [e, hf₁, hcf, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, (pairPull w).smul, RingHom.id_apply]

  let gb : C0 (pairFst ψ ⋙ OPre χ q') := fun T ↦ preα χ q q' ((pairFst ψ).obj T) (g T)
  have hgb : d0 _ gb = 0 := by
    funext T T' a
    rw [amitsur_d0_apply]
    have nat : preα χ q q' _ (mp (OAff q) ((pairFst ψ).map a) (g T)) =
        mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) := (preCoef k.w).naturality _ _
    change preα χ q q' _ (g T') - mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) = 0
    rw [← nat]
    change preα χ q q' _ (g T') - preα χ q q' _ (mp (OPair ψ q) a (g T)) = 0
    have sm : ∀ U (r0 : R) b, preα χ q q' U (r0 • b) = σ r0 • preα χ q q' U b := (preCoef k.w).smul
    rw [← map_sub, hg', sm, ht, zero_smul]
  obtain ⟨r', hr', -⟩ := (GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion R' X Y Y' ψ χ q').2.2 hC gb hgb
  obtain ⟨r, rfl⟩ := hσ r'
  have hsec := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ⟨hσ, hker, hσ₀, hker₀⟩ hq
  have hex : ∀ T : (Pair ψ)ᵒᵖ, ∃ e, g T - algebraMap R _ r = t • e := by
    intro T
    refine ((hsec ((pairFst ψ).obj T)).2.1 _).1 ?_
    have e : preα χ q q' ((pairFst ψ).obj T) (algebraMap R ((OPair ψ q).obj T) r) =
        algebraMap R' ((pairFst ψ ⋙ OPre χ q').obj T) (σ r) :=
      SemiHom.map_algebraMap ((preCoef k.w).smul _) r
    rw [map_sub, e]
    exact sub_eq_zero.2 (hr' T)
  choose g₁ hg₁ using hex
  have hkill : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'),
      t • (f₁ T T' a - (g₁ T' - mp (OPair ψ q) a (g₁ T))) = 0 := by
    intro T T' a
    rw [smul_sub, smul_sub, ← map_smul (mp (OPair ψ q) a), ← hg₁ T', ← hg₁ T, map_sub, AlgHom.commutes,
      ← hg' T T' a]
    abel

  obtain ⟨c₀, hc₀, hc₀'⟩ :=
    (GlobalTheory.T.cohomologyClass_pullback_reduction_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hψ₀ inferInstance).1 f u hred
  have hz : (CoefMap.restrict (OAff q₀) (pairFst ψ ⋙ preAff χ₀)).pull1 (pullHO1 w₀ u) = 0 := by
    rw [← hc₀', GlobalTheory.CatCoh.H1.mk_eq_zero]
    refine ⟨fun T ↦ preα χ₀ q q₀ ((pairFst ψ).obj T) (g₁ T), ?_⟩
    funext T T' a
    rw [hc₀, amitsur_d0_apply, ← hf₁]
    have e1 := ((hsec ((pairFst ψ).obj T')).2.2.2 _).2 (hkill T T' a)
    rw [map_sub, map_sub, sub_eq_zero] at e1
    have nat : preα χ₀ q q₀ _ (mp (OAff q) ((pairFst ψ).map a) (g₁ T)) =
        mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) := (preCoef k₀.w).naturality _ _
    change _ - mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) = _
    rw [← nat]
    exact e1.symm
  exact (GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion R₀ X Y Y₀ ψ χ₀ q₀).1.1 (hz.trans (map_zero _).symm)

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem wsum_eq_zero_iff : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (n : ℕ) (u v : Fin n → Glob1 F), wsum F u v = 0 ↔ ∀ l l' : Glob1 F →ₗ[R] R, ∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k)) = 0 := by
  intro R _ C _ F hfr hH n u v
  constructor
  · intro hw l l'
    obtain ⟨δ, -, hδ⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l
    obtain ⟨δ', -, hδ'⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l'
    have key : ∀ T, algebraMap R (F.obj T) (∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k))) = 0 := by
      intro T
      have h0 := congrArg (exteriorPower.pairingDual (F.obj T) Ω[F.obj T⁄R] 2
        (exteriorPower.ιMulti (F.obj T) 2 ![δ T, δ' T])) (congrFun hw T)

      simp only [wsum, map_sum, wedge_eq_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti,
      Matrix.det_fin_two, map_zero, Pi.zero_apply] at h0
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons, hδ, hδ'] at h0

      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sub, map_mul, map_mul]
      ring
    obtain ⟨r, -, huniq⟩ := hH 0 (map_zero _)
    have h1 := huniq _ (fun T => by rw [key T]; rfl)
    have h2 := huniq 0 (fun T => by rw [map_zero]; rfl)
    rw [h1, h2]
  · intro h
    obtain ⟨m, ⟨Φ⟩⟩ := hfr
    obtain ⟨L, -, hL⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F hH m Φ
    funext T
    have hexp : ∀ w : Glob1 F, w.1 T = ∑ i, L i w • (Φ.w i).1 T := by
      intro w
      conv_lhs => rw [hL w]
      simp [Submodule.coe_sum, Finset.sum_apply]
    let x : Fin m → Fin m → Om R (F.obj T) 2 := fun i j => wedge R _ ((Φ.w i).1 T) ((Φ.w j).1 T)
    let c : Fin m → Fin m → R := fun i j => ∑ k, L i (u k) * L j (v k)
    have hc : ∀ i j, c i j = c j i := by
      intro i j
      have := h (L i) (L j)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c, this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hsum : wsum F u v T = ∑ i, ∑ j, c i j • x i j := by
      have hu : ∀ k, (u k).1 T = ∑ i, L i (u k) • (Φ.w i).1 T := fun k => hexp _
      have hv : ∀ k, (v k).1 T = ∑ i, L i (v k) • (Φ.w i).1 T := fun k => hexp _

      simp only [wsum, hu, hv, map_sum, LinearMap.sum_apply, wedge_smul_left, wedge_smul_right, c, x,
      Finset.sum_smul, mul_smul]
      conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [Pi.zero_apply, hsum, ← Finset.sum_product' (f := fun i j => c i j • x i j)]
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ _
      simp only [Prod.swap_prod_mk, x]
      rw [hc j i, wedge_swap ((Φ.w j).1 T), smul_neg, add_neg_cancel]
    · rintro ⟨i, j⟩ _ hne heq
      apply hne
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [x]
    · simp
    · simp

end GlobalTheory.AbCoh
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.SpanCup

theorem sum_append {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (B : M →ₗ[R] N →ₗ[R] P) {n m : ℕ} (a : Fin n → M) (b : Fin n → N)
    (a' : Fin m → M) (b' : Fin m → N) :
    ∑ k, B (a k) (b k) + ∑ k, B (a' k) (b' k) = ∑ k, B (Fin.append a a' k) (Fin.append b b' k) := by
  rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

theorem exists_sum_ιMulti {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (x y : Fin n → M), w = ∑ k, exteriorPower.ιMulti R 2 ![x k, y k] := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    refine ⟨1, fun _ ↦ v 0, fun _ ↦ v 1, ?_⟩
    rw [Fin.sum_univ_one]
    congr 1
    ext i; fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨n, x, y, rfl⟩ := hu
    obtain ⟨m, x', y', rfl⟩ := hv
    refine ⟨n + m, Fin.append x x', Fin.append y y', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r v _ hv =>
    obtain ⟨n, x, y, rfl⟩ := hv
    refine ⟨n, fun k ↦ r • x k, y, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : (![r • x k, y k] : Fin 2 → M) = Function.update ![x k, y k] 0 (r • ![x k, y k] 0) := by
      ext i; fin_cases i <;> simp
    rw [e, AlternatingMap.map_update_smul, Function.update_eq_self]

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def fn2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cechDeRhamFunctionPart_cup_eq_cup (a b : cechDeRhamTotalCocyclesOne F) : fn2 F (cupZZ F a b) = cupZ F (cechDeRhamTotalCocyclesOne.fn F a) (cechDeRhamTotalCocyclesOne.fn F b) := rfl

end GlobalTheory.AbCoh.SpanCup


open GlobalTheory.AbCoh.SpanCup in
theorem GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) →
    WedgeO F → ∀ z : Hyp2 F, ∃ (n : ℕ) (a b : Fin n → Hyp1 F), z = ∑ k, cupHyp F (a k) (b k) := by
  intro R _ C _ F hfr h0 hc hsurj hw z
  obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F z
  obtain ⟨e, he⟩ := hw
  obtain ⟨n, x, y, hxy⟩ := exists_sum_ιMulti (e.symm (H2.mk F (fn2 F c)))
  have hrep : ∀ u : H1 F, ∃ p : cechDeRhamTotalCocyclesOne F, toO F (Hyp1.mk F p) = u := fun u ↦ by
    obtain ⟨q, hq⟩ := hsurj u
    obtain ⟨p, rfl⟩ := Hyp1.mk_surjective F q
    exact ⟨p, hq⟩
  choose p hp using hrep
  have hcls : H2.mk F (fn2 F c) = ∑ k, cup F (x k) (y k) := by
    have h := congrArg e hxy
    rw [LinearEquiv.apply_symm_apply] at h

    rw [h, map_sum]
    simp only [he]
  obtain ⟨c', hc'⟩ : ∃ c' : cechDeRhamTotalCocyclesTwo F, c' = c - ∑ k, cupZZ F (p (x k)) (p (y k)) := ⟨_, rfl⟩
  have hfn : ∃ f, d1 F f = c'.1.1 := by
    have h : H2.mk F (fn2 F c') = 0 := by
      rw [hc']

      simp only [map_sub, map_sum]
      rw [hcls, sub_eq_zero]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [cechDeRhamFunctionPart_cup_eq_cup, ← cup_mk, ← toO_mk, ← toO_mk, hp, hp]
    exact H2.mk_eq_zero.1 h
  obtain ⟨m, a, w, hm⟩ := GlobalTheory.T.hyper_h2_sum_of_cups_exact R C F hfr h0 hc hsurj c' hfn
  refine ⟨m + n, Fin.append a (fun k ↦ Hyp1.mk F (p (x k))),
    Fin.append (fun k ↦ clAll F hc (w k)) (fun k ↦ Hyp1.mk F (p (y k))), ?_⟩
  rw [← sum_append, ← hm, hc']

  simp only [map_sub, map_sum, cupHyp_mk, sub_add_cancel]
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem sum_toO_eq_zero_of_sum_cup : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • toO F (a k) = 0 := by
  intro R _ C _ F hF hH hc hsurj n a w hsum l
  obtain ⟨δ, hδnat, hδw⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hF hH l
  choose c hcA using fun k => Hyp1.mk_surjective F (a k)
  have hmem : ∀ v : Glob1 F, v ∈ Closed1 F := fun v => hc ▸ Submodule.mem_top
  have hcl : ∀ v : Glob1 F, clAll F hc v = Hyp1.mk F (formZZ F ⟨v, hmem v⟩) := fun v => rfl
  have hf : ∀ v : Glob1 F, (formZZ F ⟨v, hmem v⟩).1 = (0, v.1) := fun v => rfl
  have h2 : Hyp2.mk F (∑ k, cupZZ F (c k) (formZZ F ⟨w k, hmem (w k)⟩)) = 0 := by

    rw [map_sum, ← hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcl, ← hcA k, cupHyp_mk]
  obtain ⟨e, he⟩ := Hyp2.mk_eq_zero.1 h2
  have hsumv : (∑ k, cupZZ F (c k) (formZZ F ⟨w k, hmem (w k)⟩)).1 =
      ∑ k, cupTot F (c k).1 (0, (w k).1) := by
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_cupZZ, hf]
  rw [hsumv] at he
  have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), d1 F e.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    have := congrArg (fun x : Tot2 F => x.1 T T' T'' φ ψ) he
    simp only [Prod.fst_sum, Finset.sum_apply, cupTot_apply, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at this
    exact this
  have ha : ∀ T T' (φ : T ⟶ T'), e.2 T' - p1 F φ (e.2 T) - D R _ (e.1 T T' φ) =
      ∑ k, (c k).1.1 T T' φ • (w k).1 T' := by
    intro T T' φ
    have := congrArg (fun x : Tot2 F => x.2.1 T T' φ) he
    simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, cupTot_a, Pi.zero_apply, zero_smul,
      sub_zero] at this
    exact this
  have he1 : e.1 ∈ Z1 F := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
    funext T T' T'' φ ψ
    exact hz T T' T'' φ ψ
  obtain ⟨b, hb⟩ := hsurj (H1.mk F ⟨e.1, he1⟩)
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective F b
  rw [toO_mk, H1.mk_eq_mk] at hb
  obtain ⟨g, hg⟩ := hb
  have hfn : ∀ x : cechDeRhamTotalCocyclesOne F, ((cechDeRhamTotalCocyclesOne.fn F x : Z1 F) : C1 F) = x.1.1 := fun x => rfl
  rw [hfn] at hg
  have hg' : ∀ T T' (φ : T ⟶ T'), e.1 T T' φ = c'.1.1 T T' φ - (g T' - mp F φ (g T)) := by
    intro T T' φ
    have := congrFun (congrFun (congrFun hg T) T') φ
    simp only [amitsur_d0_apply, Pi.sub_apply] at this
    rw [this]; abel
  have hD : ∀ T T' (φ : T ⟶ T'), D R _ (e.1 T T' φ) =
      (c'.1.2 T' - D R _ (g T')) - p1 F φ (c'.1.2 T - D R _ (g T)) := by
    intro T T' φ
    rw [hg', cechDeRhamTotalCocyclesOne.conn c' φ]
    simp only [map_sub, ← p1_D]
    abel
  have hgoal : ∑ k, l (w k) • toO F (a k) = H1.mk F (∑ k, l (w k) • cechDeRhamTotalCocyclesOne.fn F (c k)) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← hcA k, toO_mk]
  rw [hgoal, H1.mk_eq_zero]
  refine ⟨fun T => δ T (e.2 T - (c'.1.2 T - D R _ (g T))), ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply, ← hδnat, ← map_sub]
  have key : e.2 T' - (c'.1.2 T' - D R _ (g T')) - p1 F φ (e.2 T - (c'.1.2 T - D R _ (g T))) =
      ∑ k, (c k).1.1 T T' φ • (w k).1 T' := by
    rw [← ha, hD]
    simp only [map_sub]
    abel

  rw [key, map_sum]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, hfn,
    LinearMap.map_smul, hδw, smul_eq_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.AbCoh
end
