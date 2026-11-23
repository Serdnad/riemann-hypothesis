module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
public import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
public import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action

@[expose] public section

section

open scoped nonZeroDivisors Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

namespace UpperTheory.Gal.TP.Skew

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end

end UpperTheory.Gal.TP.Skew

private theorem count_le_count_galois_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (g : Gal(E/F)) (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ 0) :
    FractionalIdeal.count E P (J : FractionalIdeal (𝓞 E)⁰ E) ≤
      FractionalIdeal.count E (g • P) ((g • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
  classical
  have hgJ : g • J ≠ 0 := fun h => hJ ((smul_eq_zero_iff_eq g).mp h)
  rw [FractionalIdeal.count_coe E P hJ, FractionalIdeal.count_coe E (g • P) hgJ, Nat.cast_le,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hgJ)
      (g • P).associates_irreducible]
  have h1 := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
    P.associates_irreducible).mpr le_rfl
  rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at h1 ⊢
  obtain ⟨c, hc⟩ := h1
  refine ⟨g • c, ?_⟩
  change g • J = (g • P.asIdeal) ^ _ * g • c
  conv_lhs => rw [hc]
  rw [smul_mul', smul_pow']

private theorem count_galois_smul_eq_count {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (g : Gal(E/F)) (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E)) (hJ : J ≠ 0) :
    FractionalIdeal.count E (g • P) ((g • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.count E P (J : FractionalIdeal (𝓞 E)⁰ E) := by
  refine le_antisymm ?_ (count_le_count_galois_smul g P J hJ)
  have h := count_le_count_galois_smul g⁻¹ (g • P) (g • J) (fun h => hJ ((smul_eq_zero_iff_eq g).mp h))
  rwa [inv_smul_smul, inv_smul_smul] at h

private theorem count_smul_eq_of_mem_iff_inv_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (g : Gal(E/F)) (w : HeightOneSpectrum (𝓞 E))
    (I I' : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) (h : ∀ x : E, x ∈ I' ↔ (g⁻¹ : Gal(E/F)) x ∈ I) :
    FractionalIdeal.count E (g • w) I' = FractionalIdeal.count E w I := by
  obtain ⟨b, J, hb, hbJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ 0 := FractionalIdeal.ideal_factor_ne_zero hI hbJ
  have hb' : Ideal.span {b} ≠ 0 := FractionalIdeal.constant_factor_ne_zero hI hbJ
  have hspan : g • Ideal.span {b} = Ideal.span {g • b} := by
    rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hinv : ∀ y : E, (g⁻¹ : Gal(E/F)) (g y) = y := fun y => by simp
  have hI' : I' = FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E (g • b))⁻¹ *
      ((g • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
    ext x
    rw [h, hbJ, FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_singleton_mul]
    simp only [FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, hx⟩
      have hgj : g • j ∈ g • J := by
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
        exact hj
      refine ⟨_, ⟨g • j, hgj, rfl⟩, ?_⟩
      have hx' : x = g ((g⁻¹ : Gal(E/F)) x) := by simp
      rw [hx', hx, map_mul, map_inv₀]
      rfl
    · rintro ⟨_, ⟨j, hj, rfl⟩, hx⟩
      refine ⟨_, ⟨g⁻¹ • j, Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hj, rfl⟩, ?_⟩
      rw [hx, map_mul, map_inv₀]
      exact congrArg₂ (· * ·) (congrArg Inv.inv (hinv (algebraMap (𝓞 E) E b))) rfl
  have hgJ : g • J ≠ 0 := fun h => hJ ((smul_eq_zero_iff_eq g).mp h)
  have hgb : g • Ideal.span {b} ≠ 0 := fun h => hb' ((smul_eq_zero_iff_eq g).mp h)
  rw [hI', hbJ, ← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv,
    ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton, ← hspan,
    FractionalIdeal.count_mul E (g • w) (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hgb))
      (FractionalIdeal.coeIdeal_ne_zero.mpr hgJ),
    FractionalIdeal.count_mul E w (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hb'))
      (FractionalIdeal.coeIdeal_ne_zero.mpr hJ),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, count_galois_smul_eq_count g w _ hb', count_galois_smul_eq_count g w J hJ]

private theorem galois_apply_mem_dual_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (h : Gal(E/F)) (y : E)
    (hy : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    h y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hinv : ∀ y : E, (h⁻¹ : Gal(E/F)) (h y) = y := fun y => by simp
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
  rw [FractionalIdeal.mem_dual h1] at hy ⊢
  intro a ha
  obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
  have hz := hy (algebraMap (𝓞 E) E (h⁻¹ • z)) ((FractionalIdeal.mem_one_iff _).mpr ⟨_, rfl⟩)
  rw [Algebra.traceForm_apply] at hz ⊢
  have e : Algebra.trace ℚ E (h y * algebraMap (𝓞 E) E z) =
      Algebra.trace ℚ E (y * algebraMap (𝓞 E) E (h⁻¹ • z)) := by
    rw [← Algebra.trace_eq_of_algEquiv ((h⁻¹ : Gal(E/F)).restrictScalars ℚ)
      (h y * algebraMap (𝓞 E) E z)]
    change Algebra.trace ℚ E ((h⁻¹ : Gal(E/F)) (h y * algebraMap (𝓞 E) E z)) = _
    rw [map_mul, hinv]
    rfl
  rw [e]
  exact hz

theorem UpperTheory.Gal.TP.Skew.ordAut :
    UpperTheory.Gal.TP.Skew.OrdAut := by
  intro F E _ _ _ _ _ g w
  have hinv : ∀ y : E, (g⁻¹ : Gal(E/F)) (g y) = y := fun y => by simp
  have hinv2 : ∀ y : E, g ((g⁻¹ : Gal(E/F)) y) = y := fun y => by simp
  refine ⟨fun x => ?_, ?_⟩
  · change FractionalIdeal.count E (g • w) (FractionalIdeal.spanSingleton (𝓞 E)⁰ (g x)) =
      FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰ x)
    by_cases hx : x = 0
    · subst hx
      simp [FractionalIdeal.count_zero]
    · apply count_smul_eq_of_mem_iff_inv_mem g w
      · exact FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hx
      · intro y
        simp only [FractionalIdeal.mem_spanSingleton, Algebra.smul_def]
        constructor
        · rintro ⟨z, rfl⟩
          refine ⟨g⁻¹ • z, ?_⟩
          rw [map_mul, hinv]
          rfl
        · rintro ⟨z, hz⟩
          refine ⟨g • z, ?_⟩
          rw [← hinv2 y, ← hz, map_mul]
          rfl
  · apply count_smul_eq_of_mem_iff_inv_mem g w
    · refine FractionalIdeal.dual_ne_zero ℤ ℚ ?_
      rw [← FractionalIdeal.coeIdeal_top]
      exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
    · intro y
      constructor
      · exact galois_apply_mem_dual_one g⁻¹ y
      · intro hy
        have := galois_apply_mem_dual_one g _ hy
        rwa [hinv2] at this
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

theorem posEx : PosEx := by
  intro F E _ _ _ _ _ σ hc δ hδ hs
  have key : ∀ w : InfinitePlace F, ∃ t : EmbOver E w, ∃ c : ℝ, 0 < c ∧ Complex.I * t.1 δ = c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    have hconj : ∀ (t : E →+* ℂ) (x : E), t (σ x) = star (t x) := hc.2.2.2
    set z : ℂ := τ.1 δ with hz
    have hstar : star z = -z := by
      rw [hz, ← hconj, hs, map_neg]
    have hre : z.re = 0 := by
      have := congrArg Complex.re hstar
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have hz0 : z ≠ 0 := by
      rw [hz]
      exact (map_ne_zero τ.1).2 hδ
    have him : z.im ≠ 0 := fun h => hz0 (Complex.ext hre h)
    have hI : Complex.I * z = ((-z.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨τ, -z.im, by linarith, hI⟩
    · refine ⟨⟨τ.1.comp (σ : E →+* E), ?_⟩, z.im, h, ?_⟩
      · refine Eq.trans ?_ τ.2
        ext x
        simp
      · have : (τ.1.comp (σ : E →+* E)) δ = -z := by
          simp [hs, hz]
        rw [this, mul_neg, hI]
        simp
  choose emb hemb using key
  exact ⟨emb, hemb⟩

end UpperTheory.Gal.TP.Skew

end
end

section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.memDual :
    UpperTheory.Gal.TP.Skew.MemDual := by
  intro E _ _ z
  have h0 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h0]
  constructor
  · intro h o
    have h1 := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at h1
    obtain ⟨n, hn⟩ := h1
    have h2 : Algebra.trace ℚ E ((o : E) * z) = algebraMap ℤ ℚ n := hn.symm
    rw [h2]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h o)
    exact ⟨n, hn⟩
end

section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

private theorem ordE_neg {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    ordE w (-x) = ordE w x := by
  by_cases hx : x = 0
  · simp [hx]
  · unfold ordE
    rw [GroundTheory.Global.count_spanSingleton w hx, GroundTheory.Global.count_spanSingleton w (neg_ne_zero.2 hx),
      Valuation.map_neg]

private theorem ordE_mul {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {x y : E}
    (hx : x ≠ 0) (hy : y ≠ 0) : ordE w (x * y) = ordE w x + ordE w y := by
  unfold ordE
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul E w (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.2 hy)]

theorem UpperTheory.Gal.TP.Skew.ordLine :
    UpperTheory.Gal.TP.Skew.ConjAut → UpperTheory.Gal.TP.Skew.IdeleStep → UpperTheory.Gal.TP.Skew.OrdEmb → UpperTheory.Gal.TP.Skew.InvFun → UpperTheory.Gal.TP.Skew.OrdAut → UpperTheory.Gal.TP.Skew.OrdLine := by
  intro hCA hIS hOE hIF hOA F E _ _ _ _ _ σ hc hu
  classical
  obtain ⟨hG, s, hsσ, hs1, hss, hall, δ₀, hδ0, hδσ⟩ := hCA F E σ hc
  haveI := hG
  let m : HeightOneSpectrum (𝓞 E) → ℤ := fun w =>
    FractionalIdeal.count E w (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) - ordE w δ₀
  have hcof : ∀ᶠ w in Filter.cofinite, m w = 0 :=
    ((FractionalIdeal.finite_factors (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))).and
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 E)⁰ δ₀))).mono
      fun w h => by
        change _ - FractionalIdeal.count E w _ = 0
        rw [h.1, h.2, sub_zero]
  have hinv : ∀ (g : E ≃ₐ[F] E) w, m (g • w) = m w := by
    intro g w
    rcases hall g with hg | hg
    · rw [hg, one_smul]
    · rw [hg]
      have h1 := (hOA F E s w).1 δ₀
      have h2 := (hOA F E s w).2
      rw [hsσ, hδσ, ordE_neg] at h1
      change _ - _ = _ - _
      rw [h1, h2]
  obtain ⟨a, ha⟩ := hIF F E m hcof hinv
  obtain ⟨x, b, hxb⟩ := hIS F E σ hc a
  have hx0 : algebraMap F E (x : F) ≠ 0 :=
    (map_ne_zero (algebraMap F E)).2 x.ne_zero
  refine ⟨s, algebraMap F E (x : F) * δ₀,
    ((toFractionalIdeal b : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E),
    hsσ, hss, mul_ne_zero hx0 hδ0, ?_, Units.ne_zero _, ?_⟩
  · rw [map_mul, AlgHom.commutes, hδσ, mul_neg]
  · intro w
    have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
      ext g
      simpa using hall g
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have h1 : m w = ord (w.under (𝓞 F)) (diagonal F x) + ord (w.under (𝓞 F)) (ideleNorm F E b) :=
      (ha w).symm.trans (hxb _)
    rw [← hOE F E hu _ w, ← hOE F E hu _ w, ideleEmbedding_diagonal, ideleEmbedding_ideleNorm,
      huniv, Finset.prod_pair hs1.symm, ord_mul, one_smul, ord_smul, hsi, ord_diagonal,
      ← GroundTheory.Global.count_spanSingleton w (by simpa using x.ne_zero)] at h1
    have h3 : FractionalIdeal.count E w (FractionalIdeal.spanSingleton (𝓞 E)⁰
        ((Units.map (algebraMap F E).toMonoidHom x : Eˣ) : E)) = ordE w (algebraMap F E (x : F)) := rfl
    rw [h3] at h1
    rw [ordE_mul w hx0 hδ0, count_toFractionalIdeal, count_toFractionalIdeal]
    change _ - _ = _ at h1
    linarith
end

section

open scoped nonZeroDivisors Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal

theorem UpperTheory.Gal.TP.Skew.ordEmb :
    UpperTheory.Gal.TP.Skew.OrdEmb := by
  intro F E _ _ _ _ _ hu a w
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  have hc : ((ideleEmbedding F E a : IdeleGroup E) : 𝔸[E]).2 w =
      completionMap (below F w) w ((a : 𝔸[F]).2 (below F w)) := by
    rw [coe_ideleEmbedding]
    exact GroundTheory.BlockD.ThmBHecke.adeleMap_snd_apply _ w
  unfold ord
  rw [hc, valued_completionMap, he, pow_one]
  rfl
end
