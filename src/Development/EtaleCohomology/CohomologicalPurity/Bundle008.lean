module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle005
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

@[expose] public section

section

noncomputable section
open MvPolynomial TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafPolyPf

theorem one_tmul_algebraMap {P S A : Type} [CommRing P] [CommRing S] [CommRing A] [Algebra P S] [Algebra P A]
    (p : P) : (1 : S) ⊗ₜ[P] algebraMap P A p = algebraMap P S p ⊗ₜ[P] (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

def kap (d e : ℕ) (R : Type) [CommRing R] :
    MvPolynomial (Fin d ⊕ Fin e) R →+* MvPolynomial (Fin d) (MvPolynomial (Fin e) R) :=
  eval₂Hom (C.comp C) (Sum.elim 0 fun i => C (X i))

theorem leafPoly : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  intro e d R A _ _ φ I x y h
  obtain ⟨hψ, hI⟩ := h
  set ψ := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hψdef
  let P := MvPolynomial (Fin d ⊕ Fin e) R
  let S := MvPolynomial (Fin d) (MvPolynomial (Fin e) R)
  let Cc := MvPolynomial (Fin d) (A ⧸ I)
  letI : Algebra P A := ψ.toAlgebra
  letI : Algebra P S := (kap d e R).toAlgebra
  letI : Algebra S (S ⊗[P] A) := Algebra.TensorProduct.leftAlgebra (R := P) (A := S) (B := A)
  have hb : (algebraMap S (S ⊗[P] A)).Etale :=
    RingHom.IsStableUnderBaseChange.tensorProduct RingHom.Etale.isStableUnderBaseChange S hψ
  have hx : ∀ j, x j ∈ I := fun j => hI ▸ Ideal.subset_span ⟨j, rfl⟩
  have hψX : ∀ i, ψ (X i) = Sum.elim x y i := fun i => by simp [ψ]
  let gy : MvPolynomial (Fin e) R →+* A ⧸ I := eval₂Hom ((Ideal.Quotient.mk I).comp φ) fun i => Ideal.Quotient.mk I (y i)
  let FS : S →+* Cc := eval₂Hom ((C : A ⧸ I →+* Cc).comp gy) X
  let ρ : P →+* Cc := (C : A ⧸ I →+* Cc).comp ((Ideal.Quotient.mk I).comp ψ)
  letI : Algebra P Cc := ρ.toAlgebra
  have hFSC : ∀ p, FS (C p) = C (gy p) := fun p => MvPolynomial.eval₂Hom_C _ _ _
  have hFSX : ∀ j, FS (X j) = X j := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hgC : ∀ r, gy (C r) = Ideal.Quotient.mk I (φ r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ i, gy (X i) = Ideal.Quotient.mk I (y i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have kC : ∀ r, kap d e R (C r) = C (C r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have kl : ∀ j, kap d e R (X (Sum.inl j)) = 0 := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have kr : ∀ i, kap d e R (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have ψC : ∀ r, ψ (C r) = φ r := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hFS : FS.comp (kap d e R) = ρ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show FS (kap d e R (C r)) = C (Ideal.Quotient.mk I (ψ (C r)))
      rw [kC, hFSC, hgC, ψC]
    · rintro (j | i)
      · show FS (kap d e R (X (Sum.inl j))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inl j))))
        rw [kl, hψX, map_zero]; simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hx j)]
      · show FS (kap d e R (X (Sum.inr i))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inr i))))
        rw [kr, hFSC, hgX, hψX]; rfl
  let fS : S →ₐ[P] Cc := { FS with commutes' := fun p => RingHom.congr_fun hFS p }
  let fA : A →ₐ[P] Cc := { (C : A ⧸ I →+* Cc).comp (Ideal.Quotient.mk I) with commutes' := fun _ => rfl }
  let F : S ⊗[P] A →+* Cc := (Algebra.TensorProduct.productMap fS fA).toRingHom
  have hk : I ≤ RingHom.ker (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : x j = algebraMap P A (X (Sum.inl j)) := by
      rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
    have h2 : algebraMap P S (X (Sum.inl j)) = 0 := by
      rw [RingHom.algebraMap_toAlgebra]; exact kl j
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply]
    rw [h1, one_tmul_algebraMap, h2, TensorProduct.zero_tmul]
  let G : Cc →+* S ⊗[P] A :=
    eval₂Hom (Ideal.Quotient.lift I (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom
      fun a ha => hk ha) fun j => X j ⊗ₜ[P] (1 : A)
  have hF1 : ∀ s : S, F (s ⊗ₜ[P] (1 : A)) = FS s := fun s => by simp [F, fS, fA]
  have hGC : ∀ a, G (C (Ideal.Quotient.mk I a)) = (1 : S) ⊗ₜ[P] a := fun a => by
    erw [MvPolynomial.eval₂Hom_C]; rfl
  have hGX : ∀ j, G (X j) = X j ⊗ₜ[P] (1 : A) := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hFG : F.comp G = RingHom.id Cc := by
    apply MvPolynomial.ringHom_ext
    · intro r
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp [F, G, fS, fA]
    · intro j
      show F (G (X j)) = X j
      rw [hGX, hF1, hFSX]
  have hS : (G.comp F).comp (Algebra.TensorProduct.includeLeftRingHom (R := P) (A := S) (B := A)) =
      Algebra.TensorProduct.includeLeftRingHom := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        show G (F (C (C r) ⊗ₜ[P] (1 : A))) = C (C r) ⊗ₜ[P] (1 : A)
        have e1 : φ r = algebraMap P A (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact (MvPolynomial.eval₂Hom_C _ _ _).symm
        have e2 : algebraMap P S (C r) = C (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_C _ _ _
        rw [hF1, hFSC, hgC, hGC, e1, one_tmul_algebraMap, e2]
      · intro i
        show G (F (C (X i) ⊗ₜ[P] (1 : A))) = C (X i) ⊗ₜ[P] (1 : A)
        have e1 : y i = algebraMap P A (X (Sum.inr i)) := by rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
        have e2 : algebraMap P S (X (Sum.inr i)) = C (X i) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_X' _ _ _
        rw [hF1, hFSC, hgX, hGC, e1, one_tmul_algebraMap, e2]
    · intro j
      show G (F (X j ⊗ₜ[P] (1 : A))) = X j ⊗ₜ[P] (1 : A)
      rw [hF1, hFSX, hGX]
  have hGF : G.comp F = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      have hs := RingHom.congr_fun hS s
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply] at hs
      have ha : G (F ((1 : S) ⊗ₜ[P] a)) = (1 : S) ⊗ₜ[P] a := by
        simp [F, G, fS, fA]; erw [MvPolynomial.eval₂Hom_C]; rfl
      have hm : s ⊗ₜ[P] a = (s ⊗ₜ[P] (1 : A)) * ((1 : S) ⊗ₜ[P] a) := by simp
      rw [RingHom.id_apply, RingHom.comp_apply, hm, map_mul, map_mul, hs, ha]
    | add u v hu hv => simp only [RingHom.comp_apply, RingHom.id_apply, map_add (f := _)] at hu hv ⊢; rw [hu, hv]
  let E : S ⊗[P] A ≃+* Cc := RingEquiv.ofRingHom F G hFG hGF
  let σ : P ≃+* S := (MvPolynomial.sumAlgEquiv R (Fin d) (Fin e)).toRingEquiv
  have s1 : ∀ r, σ (C r) = C (C r) := fun r => MvPolynomial.sumAlgEquiv_C_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) r
  have s2 : ∀ j, σ (X (Sum.inl j)) = X j := fun j => MvPolynomial.sumAlgEquiv_X_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) j
  have s3 : ∀ i, σ (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.sumAlgEquiv_X_inr (R := R) (S₁ := Fin d) (S₂ := Fin e) i
  have key : (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
      ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))) =
      (E.toRingHom.comp (algebraMap S (S ⊗[P] A))).comp σ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (C r)); rw [s1]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
    · rintro (j | i)
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inl j))); rw [s2]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_X']
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inr i))); rw [s3]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
  rw [key]
  exact RingHom.Etale.respectsIso.2 _ σ (RingHom.Etale.respectsIso.1 _ E hb)

theorem LeafPoly_of : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := leafPoly

end LateralTheory.CohomologicalPurity.LeafPolyPf
end
end

section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem chart_of_data (hS : LeafSec) {d : ℕ} {A T : Type} [CommRing A] [CommRing T] (I : Ideal A) (x : Fin d → A)
    (ι : A →+* T) (κ : MvPolynomial (Fin d) (A ⧸ I) →+* T) (μ : T →+* A ⧸ I)
    (hι : ι.Etale) (hκ : κ.Etale) (hμι : μ.comp ι = Ideal.Quotient.mk I)
    (hμκ : μ.comp κ = MvPolynomial.constantCoeff) (hx : ∀ j, ι (x j) = κ (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  obtain ⟨t, ht1, ht⟩ := hS A T ι I μ hι hμι
  have hu : IsUnit (algebraMap T (Localization.Away t) t) := IsLocalization.Away.algebraMap_isUnit t
  have hloc : (algebraMap T (Localization.Away t)).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t)
  have hμι' : ∀ a, μ (ι a) = Ideal.Quotient.mk I a := fun a => RingHom.congr_fun hμι a
  have hμκ' : ∀ q, μ (κ q) = MvPolynomial.constantCoeff q := fun q => RingHom.congr_fun hμκ q
  have key : ∀ s : T, μ s = 0 →
      algebraMap T (Localization.Away t) s ∈ I.map ((algebraMap T (Localization.Away t)).comp ι) := by
    intro s hs
    have h1 := Ideal.mem_map_of_mem (algebraMap T (Localization.Away t)) (ht s hs)
    rw [Ideal.map_map, map_mul] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1
  have hut : IsUnit (μ t) := by rw [ht1]; exact isUnit_one
  let μB : Localization.Away t →+* A ⧸ I := IsLocalization.Away.lift t hut
  have hμB : ∀ a, μB ((algebraMap T (Localization.Away t)).comp ι a) = Ideal.Quotient.mk I a := by
    intro a
    simp only [RingHom.comp_apply, μB, IsLocalization.Away.lift_eq, hμι']
  refine ⟨Localization.Away t, inferInstance, (algebraMap T (Localization.Away t)).comp ι,
    (algebraMap T (Localization.Away t)).comp κ, ⟨RingHom.Etale.stableUnderComposition _ _ hι hloc, ?_, ?_⟩,
    RingHom.Etale.stableUnderComposition _ _ hκ hloc, ?_, ?_⟩
  · apply Ideal.quotientMap_injective'
    intro a ha
    have hker : I.map ((algebraMap T (Localization.Away t)).comp ι) ≤ RingHom.ker μB := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem]
      exact hb
    have := hker (Ideal.mem_comap.mp ha)
    rw [RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  · intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hbn⟩ := IsLocalization.surj (Submonoid.powers t) b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (μ s)
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk]
    have e1 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) t) = 1 := by
      rw [← map_one (Ideal.Quotient.mk _)]
      refine Ideal.Quotient.eq.mpr ?_
      have := key (t - 1) (by rw [map_sub, map_one, ht1, sub_self])
      simpa [map_sub] using this
    have e2 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) s) =
        Ideal.Quotient.mk _ (((algebraMap T (Localization.Away t)).comp ι) a) := by
      refine Ideal.Quotient.eq.mpr ?_
      have := key (s - ι a) (by rw [map_sub, hμι', ha, sub_self])
      simpa [map_sub] using this
    simp only at hbn
    rw [← e2, ← hbn, map_mul, map_pow, map_pow, e1, one_pow, mul_one]
  · rw [show I.map ((algebraMap T (Localization.Away t)).comp ι) =
        (Ideal.span (Set.range x)).map ((algebraMap T (Localization.Away t)).comp ι) by rw [← hI],
      Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [hx]
  · intro a
    have := key (ι a - κ (MvPolynomial.C (Ideal.Quotient.mk I a)))
      (by rw [map_sub, hμι', hμκ', MvPolynomial.constantCoeff_C, sub_self])
    simpa [map_sub] using this

theorem chart_of_tensor (hS : LeafSec) {d : ℕ} {P A Q : Type} [CommRing P] [CommRing A] [CommRing Q] [Algebra P A]
    [Algebra P Q] (I : Ideal A) (x : Fin d → A) (c : MvPolynomial (Fin d) (A ⧸ I) ≃+* Q) [Algebra.Etale P A]
    [Algebra.Etale P Q]
    (hcomm : ∀ p, MvPolynomial.constantCoeff (c.symm (algebraMap P Q p)) = Ideal.Quotient.mk I (algebraMap P A p))
    (px : Fin d → P) (hpx1 : ∀ j, algebraMap P A (px j) = x j)
    (hpx2 : ∀ j, algebraMap P Q (px j) = c (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  let f : A →ₐ[P] A ⧸ I := Ideal.Quotient.mkₐ P I
  have hg : ∀ p, (MvPolynomial.constantCoeff.comp c.symm.toRingHom) (algebraMap P Q p) =
      algebraMap P (A ⧸ I) p := fun p => by
    rw [RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap]; exact hcomm p
  let g : Q →ₐ[P] A ⧸ I := { MvPolynomial.constantCoeff.comp c.symm.toRingHom with commutes' := hg }
  let μ := (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
  let ι := algebraMap A (A ⊗[P] Q)
  let κ := ((Algebra.TensorProduct.comm P Q A).toRingHom.comp (algebraMap Q (Q ⊗[P] A))).comp c.toRingHom
  have hκa : ∀ q, κ q = (1 : A) ⊗ₜ c q := fun q => by
    simp [κ, Algebra.TensorProduct.comm_tmul]
  refine chart_of_data hS I x ι κ μ (RingHom.etale_algebraMap.mpr inferInstance) ?_ ?_ ?_ ?_ hI
  · exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective c.bijective)
      (RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.mpr inferInstance)
        (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm P Q A).bijective))
  · ext a; simp [μ, ι, f, g]
  · apply RingHom.ext; intro q; simp [μ, hκa, f, g]
  · intro j
    rw [hκa]
    show x j ⊗ₜ 1 = _
    rw [← hpx1, ← hpx2, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Q),
      TensorProduct.smul_tmul]

theorem LeafNbhd_of (hS : LeafSec) (hP : LeafPoly) : LeafNbhd := by
  intro e d R A _ _ φ I x y hc
  have hπ := hP e d R A φ I x y hc
  set α := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hα
  set π := (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
    ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i))))
    with hπdef
  have hxI : ∀ j, x j ∈ I := fun j => hc.2 ▸ Ideal.subset_span ⟨j, rfl⟩
  have hcomm : MvPolynomial.constantCoeff.comp π = (Ideal.Quotient.mk I).comp α := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [π, α]
    · intro i
      rcases i with j | i
      · simp [π, α, Ideal.Quotient.eq_zero_iff_mem.mpr (hxI j)]
      · simp [π, α]
  exact @chart_of_tensor hS d _ A _ _ _ _ α.toAlgebra π.toAlgebra I x (RingEquiv.refl _) hc.1.toAlgebra hπ.toAlgebra
    (fun p => RingHom.congr_fun hcomm p) (fun j => MvPolynomial.X (Sum.inl j)) (fun j => by show α _ = x j; rw [hα]; simp)
    (fun j => by show π _ = _; rw [hπdef]; simp) hc.2

end LateralTheory.CohomologicalPurity.ChartCut
end
end

section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafSecPf

theorem LeafSec_of : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  intro A T _ _ φ I μ hφ hμ
  algebraize [φ]
  have : Algebra.Etale A T := RingHom.etale_algebraMap.mp hφ
  set J : Ideal T := I.map φ with hJ
  have hle : I ≤ J.comap φ := Ideal.le_comap_map
  have hker : ∀ a ∈ J, μ a = 0 := by
    intro a ha
    have : J ≤ RingHom.ker μ := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro c hc
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      rw [← RingHom.comp_apply, hμ]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
    exact this ha
  let q : A ⧸ I →+* T ⧸ J := Ideal.quotientMap J φ hle
  let μb : T ⧸ J →+* A ⧸ I := Ideal.Quotient.lift J μ hker
  have hμq : ∀ z, μb (q z) = z := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    show μb (Ideal.Quotient.mk J (φ c)) = _
    simp only [μb, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply, hμ]
  let g : T →ₐ[A] T ⧸ J :=
    { (q.comp μ) with
      commutes' := fun a => by
        show q (μ (φ a)) = Ideal.Quotient.mk J (φ a)
        rw [← RingHom.comp_apply μ φ, hμ]; rfl }
  let f : T →ₐ[A] T ⧸ J := Ideal.Quotient.mkₐ A J
  let ψ : T ⊗[A] T →ₐ[A] T ⧸ J := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have key : ∀ x : T ⊗[A] T, μb (ψ x) = μ (Algebra.TensorProduct.lmul' A x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [ψ, Algebra.TensorProduct.lift_tmul, map_mul, Algebra.TensorProduct.lmul'_apply_tmul]
      congr 1
      all_goals first | rfl | exact hμq _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (ψ (Algebra.FormallyUnramified.elem A T))
  refine ⟨t, ?_, ?_⟩
  · have h1 : μb (Ideal.Quotient.mk J t) = μ t := Ideal.Quotient.lift_mk _ _ _
    rw [← h1, ht, key, Algebra.FormallyUnramified.lmul_elem, map_one]
  · intro s hs
    have h2 := congrArg ψ (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) s)
    simp only [map_mul, ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at h2
    have hg : g s = 0 := by show q (μ s) = 0; rw [hs, map_zero]
    rw [hg, zero_mul] at h2
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht, mul_comm]
    exact h2.symm

end LateralTheory.CohomologicalPurity.LeafSecPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def HtOffCont (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) {J : Type} [SmallCategory J]
    (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
    (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)) (n i : ℤ) : Prop :=
  (∀ x : Ht q (opn (off B (I.map φ))).left n i, ∃ j h, ∃ y,
    pull _ (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h).left (tw q i) n y = x) ∧
  (∀ j h y, pull _ (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h).left
      (tw q i) n y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), pull _ (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h').left (tw q i) n y = 0)

def LeafOffCont : Prop := A1 → A4 → B1 → LeafBd → LeafExc → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (I : Ideal A), I.FG → IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ, HtOffCont q φ I D s t n i

def LeafHsFive : Prop := A1 → B1 → LeafBd → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
  (I : Ideal A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ i : ℤ,
  (∀ m : ℤ, HtOffCont q φ I D s t m i) → ∀ n : ℤ,
  (∀ x : Hs q (opn (off B (I.map φ))) n i, ∃ j h, ∃ y,
    Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = x) ∧
  (∀ j h y, Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), Hs.pull q (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h') n i y = 0)

theorem opn_mono {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  unfold sch
  infer_instance

theorem spec_cont (b1 : B1) (q : ℕ) {B : Type} [CommRing B] {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)) (hc : IsColimit (Cocone.mk _ t))
    (hq : IsUnit (q : B)) (hqj : ∀ j, IsUnit (q : D.obj j)) (n i : ℤ) :
    (∀ x : Ht q (sp B) n i, ∃ j, ∃ y, pull _ (sch.map (Spec.map (t.app j))) (tw q i) n y = x) ∧
    ∀ j (y : Ht q (sch.obj (Spec (D.obj j))) n i), pull _ (sch.map (Spec.map (t.app j))) (tw q i) n y = 0 →
      ∃ (k : J) (f : j ⟶ k), pull _ (sch.map (Spec.map (D.map f))) (tw q i) n y = 0 := by
  have h := b1 q D _ hc n i
  exact ⟨fun x => h.1 x hq, fun j y hy => h.2 j y (hqj j) hy⟩

theorem leafHsCont_of (hB : LeafBd) (hE : LeafExc) (hO : LeafOffCont) (hF : LeafHsFive) : LeafHsCont := by
  intro a1 a4 b1 q A B _ _ φ I hI hq J _ _ D s t hc he n i
  exact hF a1 b1 hB q φ I hq J D s t hc he i (fun m => hO a1 a4 b1 hB hE q φ I hI hq J D s t hc he m i) n

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section

namespace LateralTheory.CohomologicalPurity.ChartCut


open RingHom in
theorem shrink_away {n : ℕ} {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (u v : S)
    (T : Type) [CommRing T] [Algebra S T] [IsLocalization.Away (u * v) T]
    (h : ((algebraMap S (Localization.Away u)).comp ψ).IsStandardSmoothOfRelativeDimension n) :
    ((algebraMap S T).comp ψ).IsStandardSmoothOfRelativeDimension n := by
  let B := Localization.Away (algebraMap S (Localization.Away u) v)
  have h2 : ((algebraMap (Localization.Away u) B).comp
      ((algebraMap S (Localization.Away u)).comp ψ)).IsStandardSmoothOfRelativeDimension n :=
    zero_add n ▸ (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
      (algebraMap S (Localization.Away u) v)).comp h
  have hB : IsLocalization.Away (u * v) B := inferInstance
  let eT : B ≃ₐ[S] T := IsLocalization.algEquiv (Submonoid.powers (u * v)) B T
  have h3 : ((algebraMap S B).comp ψ).IsStandardSmoothOfRelativeDimension n := by
    rw [IsScalarTower.algebraMap_eq S (Localization.Away u) B, RingHom.comp_assoc]; exact h2
  have h4 := (isStandardSmoothOfRelativeDimension_respectsIso (n := n)).left _ eT.toRingEquiv h3
  have hT : algebraMap S T = (eT.toRingEquiv.toRingHom).comp (algebraMap S B) := by
    ext x; exact (eT.commutes x).symm
  rw [hT, RingHom.comp_assoc]; exact h4

theorem LeafShrink_of : LeafShrink := by
  intro e d R A _ _ φ I p hp hIp ⟨h1, h2⟩
  obtain ⟨a, ha1, hap⟩ : ∃ a : A, ((algebraMap A (Localization.Away a)).comp φ).IsStandardSmoothOfRelativeDimension (e + d) ∧ a ∉ p := by
    by_contra hcon
    push Not at hcon
    apply hp.ne_top
    rw [eq_top_iff, ← h1.span_eq_top, Ideal.span_le]
    intro g hg; exact hcon g hg
  have hq : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  obtain ⟨c, hc1, hcq⟩ : ∃ c : A ⧸ I, ((algebraMap (A ⧸ I) (Localization.Away c)).comp ((Ideal.Quotient.mk I).comp φ)).IsStandardSmoothOfRelativeDimension e ∧ c ∉ p.map (Ideal.Quotient.mk I) := by
    by_contra hcon
    push Not at hcon
    apply hq.ne_top
    rw [eq_top_iff, ← h2.span_eq_top, Ideal.span_le]
    intro g hg; exact hcon g hg
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hbp : b ∉ p := fun hb => hcq (Ideal.mem_map_of_mem _ hb)
  refine ⟨a * b, fun h => (hp.mem_or_mem h).elim hap hbp, ?_⟩
  intro A' _ _ _
  refine ⟨shrink_away φ a b A' ha1, ?_⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b)))
      (A' ⧸ I.map (algebraMap A A')) := inferInstance
  have key : Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b)) =
      Submonoid.powers (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, mul_comm a b, map_mul]; rfl
  have : IsLocalization.Away (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a)
      (A' ⧸ I.map (algebraMap A A')) := by
    unfold IsLocalization.Away; rw [← key]; exact hloc
  have hcomp : (Ideal.Quotient.mk (I.map (algebraMap A A'))).comp ((algebraMap A A').comp φ) =
      (algebraMap (A ⧸ I) (A' ⧸ I.map (algebraMap A A'))).comp ((Ideal.Quotient.mk I).comp φ) := by
    ext x; rfl
  rw [hcomp]
  exact shrink_away _ _ (Ideal.Quotient.mk I a) _ hc1

end LateralTheory.CohomologicalPurity.ChartCut
end
end
