module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
public import Mathlib.Algebra.MvPolynomial.Funext
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle005
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.KrullDimension.PID
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem ChartPointTrdeg.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : AffineChartTrdeg.Statement) :
    ChartPointTrdeg.Statement := by
  intro k L _ _ _ n e Q g hQ hg x j₀ hx hj
  have := hQ.isPrime
  have hdim := h₁ k n (e + 1) Q g hQ hg
  have hXj : (X j₀ : MvPolynomial (Fin n) k) ∉ Q := fun h => hj (by simpa using hx _ h)
  have htr := h₂ k n e Q j₀ hQ hdim hXj
  let R := MvPolynomial (Fin n) k ⧸ Q
  let K := FractionRing R
  let π : R →ₐ[k] L := Ideal.Quotient.liftₐ Q (aeval x) hx
  let s : R := Ideal.Quotient.mk Q (X j₀)
  have hs : s ≠ 0 := by
    intro h
    exact hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hπX : ∀ m, π (Ideal.Quotient.mk Q (X m)) = x m := fun m =>
    (AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp Q (aeval x) hx) (X m)).trans (aeval_X x m)
  have hπs : π s = x j₀ := hπX j₀
  have hπu : IsUnit (π s) := by rw [hπs]; exact hj.isUnit
  have hKs : algebraMap R K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs
  let S := Localization.Away s
  let ρ : S →ₐ[k] L := IsLocalization.Away.liftAlgHom s hπu
  let ι : S →ₐ[k] K :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom k R K) s hKs.isUnit
  have hSinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hι : Function.Injective ι := by
    show Function.Injective (IsLocalization.Away.lift (g := algebraMap R K) s hKs.isUnit)
    refine (IsLocalization.lift_injective_iff _).mpr fun a b => ?_
    rw [hSinj.eq_iff, (IsFractionRing.injective R K).eq_iff]
  let y : Fin n → S := fun m => algebraMap R S (Ideal.Quotient.mk Q (X m)) * IsLocalization.Away.invSelf s
  have hinv : ∀ {B : Type} [Field B] [Algebra k B] (φ : S →ₐ[k] B),
      φ (IsLocalization.Away.invSelf s) = (φ (algebraMap R S s))⁻¹ := by
    intro B _ _ φ
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hιR : ∀ a, ι (algebraMap R S a) = algebraMap R K a := fun a =>
    IsLocalization.Away.lift_eq (g := algebraMap R K) s hKs.isUnit a
  have hρR : ∀ a, ρ (algebraMap R S a) = π a := fun a =>
    IsLocalization.Away.lift_eq (g := (π : R →+* L)) s hπu a
  have hιy : ι ∘ y = fun m => genPt Q m * (genPt Q j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ι, hιR]
    rfl
  have hρy : ρ ∘ y = fun m => x m * (x j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ρ, hρR, hπX, s]
  let T := Algebra.adjoin k (Set.range y)
  have hA : T.map ι = Algebra.adjoin k (Set.range fun m => genPt Q m * (genPt Q j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hιy]
  have hB : T.map ρ = Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hρy]
  have hTA : Algebra.trdeg k T = Algebra.trdeg k (T.map ι) :=
    (Subalgebra.equivMapOfInjective T ι hι).trdeg_eq
  have hBT : Algebra.trdeg k (T.map ρ) ≤ Algebra.trdeg k T := by
    refine trdeg_le_of_surjective ((ρ.comp T.val).codRestrict (T.map ρ)
      (fun t => ⟨t, t.2, rfl⟩)) ?_
    rintro ⟨b, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  rw [← hB]
  rw [hA, htr] at hTA
  exact hBT.trans hTA.le

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem exists_relComps_of_mem_incidence_field {F : Type*} [Field F] {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) F)} {v : Fin k × Fin n → AlgebraicClosure F}
    (hv : v ∈ incidence J k) : ∃ W ∈ relComps J, v ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxv⟩ := hv
  have hP : (RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F)).IsPrime :=
    RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) :=
    fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxv⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  simpa using RingHom.mem_ker.mp (hWP hj)

theorem SpecFirstNeField.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₃ : ChowFormExists.Statement) (h₄ : IncidenceZeroLocus.Statement) :
    SpecFirstNeField.Statement := by
  classical
  intro F _ n e I f u hI hf hu h0
  have hdim := h₁ F n (e + 1) I f hI hf

  have hG : ∀ W : Ideal (MvPolynomial (Fin n) F), ∃ g : MvPolynomial (Fin e × Fin n) F,
      g ≠ 0 ∧ (W ∈ relComps (I ⊔ Ideal.span {linForm u}) → IsChowForm W e g) := by
    intro W
    by_cases hW : W ∈ relComps (I ⊔ Ideal.span {linForm u})
    · obtain ⟨hWp, hWd⟩ := h₂ F n e I W u hI hdim hu hW
      obtain ⟨g, hg⟩ := h₃ F n e W hWp hWd
      exact ⟨g, hg.1, fun _ => hg⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hW⟩
  choose G hG0 hGc using hG
  let S := ((I ⊔ Ideal.span {linForm u}).finite_minimalPrimes_of_isNoetherianRing _).toFinset
  have hprod : ∀ v : Fin e × Fin n → AlgebraicClosure F, aeval v (∏ W ∈ S, G W) = 0 := by
    intro v
    let w : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
      Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F _ (u ij.2))
        (fun i => v (i, ij.2)) ij.1
    have hw : aeval w f = 0 := by
      have hs : aeval v (specFirst f u) = aeval w f := by
        have hfun : (fun ij => aeval v (specFirstVar u ij)) = w := by
          funext ij
          obtain ⟨i, j⟩ := ij
          induction i using Fin.cases with
          | zero => simp [specFirstVar, w]
          | succ i => simp [specFirstVar, w]
        unfold specFirst
        rw [aeval_bind₁, hfun]
      rw [← hs, h0, map_zero]
    have hinc : ∀ g ∈ GroundTheory.Heights₂.Heights.incIdeal I (e + 1), aeval w g = 0 := by
      intro g hg
      simp only [GroundTheory.Heights₂.Heights.incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
      obtain ⟨h, rfl⟩ := (hf.2 g).1 hg
      rw [map_mul, hw, zero_mul]
    obtain ⟨y, hy0, hyI, hyw⟩ := h₄ F n (e + 1) I hI.isHomog (AlgebraicClosure F) w hinc
    have hvJ : v ∈ incidence (I ⊔ Ideal.span {linForm u}) e := by
      refine ⟨y, hy0, fun g hg => ?_, fun i => by simpa [w] using hyw i.succ⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hg
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      have hu0 : aeval y (linForm u) = 0 := by
        simpa [w, linForm] using hyw 0
      rw [map_add (f := _), map_mul, hu0, mul_zero, add_zero, hyI a ha]
    obtain ⟨W, hW, hvW⟩ := exists_relComps_of_mem_incidence_field hvJ
    rw [map_prod]
    exact Finset.prod_eq_zero ((Set.Finite.mem_toFinset _).mpr hW.1)
      (((hGc W hW).2 (G W)).2 dvd_rfl v hvW)
  have hne : (∏ W ∈ S, G W) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => hG0 W
  apply hne
  apply MvPolynomial.map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro v
  rw [eval_map, ← aeval_def, hprod v, map_zero]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem parToFrac_algebraMap {K : Type*} [Field K] [NumberField K] (e n : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    parToFrac e n v (algebraMap (𝓞 K) (ParDVR e n v) x) = kToFrac K e n (algebraMap (𝓞 K) K x) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac,
    IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    MvPolynomial.algebraMap_eq]

theorem map_secLin {R S : Type*} [CommRing R] [CommRing S] {n e : ℕ}
    {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R} {Q' : Ideal (MvPolynomial (Fin n) S)}
    {y' : Par e n → S} (ψ : SecAlg Q y →+* SecAlg Q' y') (c : R →+* S)
    (hc : ∀ j, ψ (secCoord Q y j) = secCoord Q' y' j)
    (hr : ∀ r : R, ψ (algebraMap R _ r) = algebraMap S _ (c r)) (w : Fin n → R) :
    ψ (secLin Q y w) = secLin Q' y' (fun j => c (w j)) := by

  simp only [secLin, linForm, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (Ideal.Quotient.mk (secIdeal Q y) (C (w j))) = algebraMap R (SecAlg Q y) (w j) := rfl
  have h2 : (Ideal.Quotient.mk (secIdeal Q' y') (C (c (w j)))) = algebraMap S (SecAlg Q' y') (c (w j)) :=
    rfl
  rw [h1, h2, hr]
  exact congrArg _ (hc j)

theorem SecBLinInj.proof (h1 : SecBGeneric.Statement) (h2 : SecBTorsionFree.Statement)
    (h3 : SecLinNZD.Statement) (h4 : ParAlgIndep.Statement) : SecBLinInj.Statement := by
  intro K _ _ n e I f u v hI hf hu
  obtain ⟨φ, hφc, hφr, hloc⟩ := h1 K n e I v hI
  let _ : Algebra (SecB e I v) (SecAlg (idealF e I) (parYF K e n)) := φ.toAlgebra
  have hφinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨m, hm⟩, hmb⟩ := (IsLocalization.map_eq_zero_iff
      (Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)))
      (SecAlg (idealF e I) (parYF K e n)) b).mp hb
    obtain ⟨r, hr, rfl⟩ := hm
    exact h2 K n e I v hI r b (nonZeroDivisors.ne_zero hr) ((Algebra.smul_def r b).trans hmb)
  let _ := (kToFrac K e n).toAlgebra
  have hnzd := h3 K (ParFrac K e n) n e I f (parYF K e n) (fun j => (u j : K)) (h4 K e n) hI hf hu
  have hmap : φ (secLin (modelR e I v) (parY e n v) fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      secLin (idealF e I) (parYF K e n) (fun j => kToFrac K e n (u j : K)) := by
    rw [map_secLin φ (parToFrac e n v) hφc hφr]
    simp only [parToFrac_algebraMap]
  intro b c hbc
  apply hφinj
  have h := congrArg φ hbc
  simp only [map_mul, hmap] at h
  exact (mul_cancel_left_mem_nonZeroDivisors hnzd).mp h

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

theorem PrimitiveScale.proof : PrimitiveScale.Statement := by
  intro K _ _ v σ f hf
  classical
  set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanFinset (𝓞 K) f.support (fun m => f.coeff m)
    with hJdef
  have hJ : J ≠ 0 := by
    rw [hJdef, FractionalIdeal.spanFinset_ne_zero]
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
    exact ⟨m, MvPolynomial.mem_support_iff.mpr hm, hm⟩
  have hJJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ
  have hcoeff : ∀ m, f.coeff m ∈ J := by
    intro m
    by_cases hm : f.coeff m = 0
    · rw [hm, ← FractionalIdeal.mem_coe]; exact Submodule.zero_mem _
    · rw [← FractionalIdeal.mem_coe, hJdef, FractionalIdeal.spanFinset_coe]
      exact Submodule.subset_span ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
  have hint : ∀ c ∈ J⁻¹, ∀ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m := by
    intro c hc m
    have h1 : f.coeff m * c ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul (hcoeff m) hc
    rw [hJJ, FractionalIdeal.mem_one_iff] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [hy, mul_comm]⟩

  have hex : ∃ c ∈ J⁻¹, ∃ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m ∧ y ∉ v.asIdeal := by
    by_contra hne
    push Not at hne
    let S : Submodule (𝓞 K) K := Submodule.map (Algebra.linearMap (𝓞 K) K) v.asIdeal
    have hle : ((J * J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ S := by
      rw [FractionalIdeal.coe_mul, Submodule.mul_le]
      intro j hj c hc
      have hJS : (J : Submodule (𝓞 K) K) ≤ S.comap (LinearMap.mulRight (𝓞 K) c) := by
        rw [hJdef, FractionalIdeal.spanFinset_coe, Submodule.span_le]
        rintro _ ⟨m, -, rfl⟩
        obtain ⟨y, hy⟩ := hint c hc m
        refine Submodule.mem_map.mpr ⟨y, hne c hc m y hy, ?_⟩
        simp only [Algebra.linearMap_apply, LinearMap.mulRight_apply]
        rw [hy, mul_comm]
      exact hJS hj
    have h1 : (1 : K) ∈ S := by
      apply hle
      rw [hJJ, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨1, map_one _⟩
    obtain ⟨y, hy, hy1⟩ := Submodule.mem_map.mp h1
    have : y = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      simpa using hy1
    rw [this] at hy
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hy)
  obtain ⟨c, hc, m0, y0, hy0, hy0v⟩ := hex
  have hcoeffs : ((C c * f).coeffs : Set K) ⊆ Set.range (algebraMap (𝓞 K) K) := by
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    obtain ⟨y, hy⟩ := hint c hc m
    exact ⟨y, by rw [hy, MvPolynomial.coeff_C_mul]⟩
  obtain ⟨g, hg⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hcoeffs
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy0v
    have : algebraMap (𝓞 K) K y0 = 0 := by rw [hy0, zero_mul]
    rw [(IsFractionRing.injective (𝓞 K) K).eq_iff.mp (this.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨c, g, hc0, hg, m0, ?_⟩
  have hgm : algebraMap (𝓞 K) K (g.coeff m0) = algebraMap (𝓞 K) K y0 := by
    rw [hy0, ← MvPolynomial.coeff_map, hg, MvPolynomial.coeff_C_mul]
  rwa [(IsFractionRing.injective (𝓞 K) K) hgm]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem specComps_finite {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) : (specComps I v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1

theorem vertComps_finite' {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1.1


open Classical in
theorem OrdEq.proof (hni : NormIdentity.Statement) (hnl : NormLength.Statement)
    (hld : LengthDecomp.Statement) (hmax : SpecMax.Statement) (hlen : SpecLength.Statement)
    (hres : SpecResidue.Statement) (hvs : VertSpec.Statement) (hinj : SecBLinInj.Statement)
    (hfin : SecBFinite.Statement) (htf : SecBTorsionFree.Statement) (hdvr : ParDVRIsDVR.Statement) :
    OrdEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := hdvr K e n v
  set f := g.map (algebraMap (𝓞 K) K)
  set ℓ := secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))
  obtain ⟨w, hw⟩ := hni K n e I g u v hI hf hu hprim
  rw [hw, Ring.ord_mul_of_isUnit_left w.isUnit]
  have hfinB : Module.Finite (ParDVR e n v) (SecB e I v) := hfin K n e I f v hI hf
  have htfB : Module.IsTorsionFree (ParDVR e n v) (SecB e I v) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r b h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · exact Or.inr (htf K n e I v hI r b hr h)
  have hfreeB : Module.Free (ParDVR e n v) (SecB e I v) := Module.free_of_finite_type_torsion_free'
  have hℓ : Function.Injective fun b : SecB e I v => ℓ * b := hinj K n e I f u v hI hf hu
  rw [hnl _ _ ℓ hℓ]

  have hN0 : Algebra.norm (ParDVR e n v) ℓ ≠ 0 := by
    rw [Algebra.norm_apply, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
    exact hℓ
  have hfinite : Module.length (ParDVR e n v) (SecB e I v ⧸ Ideal.span {ℓ}) ≠ ⊤ := by
    rw [← hnl _ _ ℓ hℓ]
    exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hN0)
  rw [hld _ _ ℓ hfinite]

  obtain ⟨hmax1, hmax2⟩ := hmax K n e I f v hI hf
  choose W hW hWu using fun 𝔫 : MaximalSpectrum (SecB e I v) => hmax2 𝔫.asIdeal 𝔫.isMaximal
  set G : Ideal (MvPolynomial (Fin n) (𝓞 K)) → ℕ∞ := fun W =>
    (if linForm u ∈ W then (localMult (integralModel I ⊔ Ideal.span {linForm u}) W : ℕ∞) else 0) *
      (chowDegree (reduceMod v W) (e + 1) : ℕ∞) with hG
  have hbij : Set.BijOn W Set.univ (specComps I v) := by
    refine ⟨fun 𝔫 _ => (hW 𝔫).1, fun 𝔫₁ _ 𝔫₂ _ h => ?_, fun W' hW' => ?_⟩
    · apply MaximalSpectrum.ext
      rw [← (hW 𝔫₁).2, ← (hW 𝔫₂).2, h]
    · refine ⟨⟨secIdealOf e I v W', hmax1 W' hW'⟩, Set.mem_univ _, ?_⟩
      exact (hWu _ W' ⟨hW', rfl⟩).symm
  rw [← finsum_mem_univ, finsum_mem_eq_of_bijOn W hbij (g := G) fun 𝔫 _ => by
    rw [hlen K n e I f u v hI hf hu 𝔫 (W 𝔫) (hW 𝔫).1 (hW 𝔫).2, ← (hW 𝔫).2,
      hres K n e I f v hI hf (W 𝔫) (hW 𝔫).1]]

  have hs := specComps_finite I v
  have hv := vertComps_finite' I u v
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, vertDeg, Nat.cast_finsum_mem hv,
    finsum_mem_eq_finite_toFinset_sum _ hv]
  have hset : hv.toFinset = hs.toFinset.filter fun W => linForm u ∈ W := by
    ext W
    simp [hvs K n e I f u v hI hf hu]
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [hG]
  split_ifs <;> simp

end

end GroundTheory.Heights₂.Heights.Vertical
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

def toSecB {K : Type*} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)) : MvPolynomial (Fin n) (𝓞 K) →+* SecB e I v :=
  (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))).comp
    (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))

def SecIdealOfPrime.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      (secIdealOf e I v W).IsPrime ∧ (secIdealOf e I v W).comap (toSecB e I v) = W

end

end GroundTheory.Heights₂.Heights.Vertical
end
