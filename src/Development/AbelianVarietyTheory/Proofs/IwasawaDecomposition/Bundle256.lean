module

public import Formalism.LocalRingCardinality.Bundle001
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle251
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.LocalNormNegOne

open Polynomial IsLocalRing

theorem exists_sq_sub_finite {k : Type*} [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ x y : k, x ^ 2 - (D * y ^ 2 - 4) = 0 := by
  classical
  have := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := fun h => h2 (by
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this)
  have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two hc
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic (R := k) (f := X ^ 2)
    (g := C (-D) * X ^ 2 + C 0 * X + C 4) (degree_X_pow 2) (degree_quadratic (neg_ne_zero.2 hD)) hodd
  refine ⟨x, y, ?_⟩
  simp only [eval_pow, eval_X, eval_add, eval_mul, eval_C] at h
  linear_combination h

variable {R : Type*} [CommRing R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]

theorem exists_root_quadratic (p q x₀ : R) (h₀ : x₀ ^ 2 + p * x₀ + q ∈ maximalIdeal R)
    (h₁ : IsUnit (2 * x₀ + p)) : ∃ x : R, x ^ 2 + p * x + q = 0 ∧ x - x₀ ∈ maximalIdeal R := by
  obtain ⟨x, hx, hx'⟩ := HenselianRing.is_henselian (I := maximalIdeal R)
    (X ^ 2 + C p * X + C q) (by monicity!) x₀ (by simpa using h₀) (by
      have : (X ^ 2 + C p * X + C q : R[X]).derivative.eval x₀ = 2 * x₀ + p := by
        simp [one_add_one_eq_two]
      rw [this]
      exact h₁.map _)
  exact ⟨x, by simpa [IsRoot] using hx, hx'⟩

theorem exists_eq_neg_one [Finite (ResidueField R)] (t n : R) (hD : IsUnit (t ^ 2 - 4 * n)) :
    ∃ a b : R, a ^ 2 + a * b * t + b ^ 2 * n = -1 := by
  by_cases h2 : IsUnit (2 : R)
  · obtain ⟨u, hu⟩ := h2.exists_left_inv
    have key : ∃ x b : R, x ^ 2 - ((t ^ 2 - 4 * n) * b ^ 2 - 4) = 0 := by
      generalize t ^ 2 - 4 * n = D at hD
      obtain ⟨x, y, h⟩ := exists_sq_sub_finite (k := ResidueField R)
        (by have := (h2.map (residue R)).ne_zero; rwa [map_ofNat] at this) (residue R D) (hD.map _).ne_zero
      obtain ⟨x, rfl⟩ := residue_surjective x
      obtain ⟨y, rfl⟩ := residue_surjective y
      have hm : x ^ 2 - (D * y ^ 2 - 4) ∈ maximalIdeal R := by
        rw [← residue_eq_zero_iff, ← h]
        simp [map_ofNat]
      by_cases hx : IsUnit x
      · obtain ⟨z, hz, -⟩ := exists_root_quadratic 0 (-(D * y ^ 2 - 4)) x
          (by simpa [sub_eq_add_neg] using hm) (by simpa using h2.mul hx)
        exact ⟨z, y, by linear_combination hz⟩
      · have hxm : x ∈ maximalIdeal R := hx
        have hm' : D * y ^ 2 - 4 ∈ maximalIdeal R := by
          have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ x hxm) hm
          convert this using 1; ring
        obtain ⟨d, hd⟩ := hD.exists_left_inv
        have hy : IsUnit y := by
          by_contra hy
          have hym : y ∈ maximalIdeal R := hy
          have h4 : (2 * 2 : R) ∈ maximalIdeal R := by
            have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ (D * y) hym) hm'
            convert this using 1; ring
          exact h4 (h2.mul h2)
        obtain ⟨z, hz, -⟩ := exists_root_quadratic 0 (-(4 * d)) y
          (by
            have := Ideal.mul_mem_left _ d hm'
            convert this using 1
            linear_combination (-y ^ 2) * hd) (by simpa using h2.mul hy)
        exact ⟨0, z, by linear_combination (-D) * hz - 4 * hd⟩
    obtain ⟨x, b, h⟩ := key
    refine ⟨u * (x - t * b), b, ?_⟩
    linear_combination u ^ 2 * h
      - (u * (x - t * b) * b * t + (b ^ 2 * n + 1) * (u * 2 + 1)) * hu
  · have h2m : (2 : R) ∈ maximalIdeal R := h2
    have ht : IsUnit t := by
      by_contra ht
      have htm : t ∈ maximalIdeal R := ht
      have : t ^ 2 - 4 * n ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ t htm) (Ideal.mul_mem_left _ (2 * n) h2m)
        convert this using 1; ring
      exact this hD
    obtain ⟨c, hc, hc'⟩ := exists_root_quadratic t (2 * n) (-t)
      (by
        have := Ideal.mul_mem_left _ n h2m
        convert this using 1; ring)
      (by
        have : 2 * -t + t = -t := by ring
        rw [this]; exact ht.neg)
    have hcu : IsUnit c := by
      by_contra hcu
      have hcm : c ∈ maximalIdeal R := hcu
      have : t ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem hc' hcm
        convert this using 1; ring
      exact this ht
    obtain ⟨e, he⟩ := hcu.exists_left_inv
    refine ⟨1, 2 * e, ?_⟩
    linear_combination 2 * e ^ 2 * hc - (2 * e * t + 2 * (e * c + 1)) * he

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (v : HeightOneSpectrum (𝓞 F)) (θ : 𝓞 E), (∃ t : 𝓞 F, ∃ n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧ (θ : E) * star (θ : E) = algebraMap F E n ∧ t ^ 2 - 4 * n ∉ v.asIdeal) → ∃ a b : v.adicCompletionIntegers F, ∃ t n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧ (θ : E) * star (θ : E) = algebraMap F E n ∧ a ^ 2 + a * b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t + b ^ 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = -1 := by
  rintro F E _ _ _ _ _ _ - v θ ⟨t, n, h1, h2, h3⟩
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hD := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3
  rw [map_sub, map_pow, map_mul, map_ofNat] at hD
  obtain ⟨a, b, h⟩ := exists_eq_neg_one _ _ hD
  exact ⟨a, b, t, n, h1, h2, h⟩

end GlobalTheory.LocalNormNegOne
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairIntegral

theorem sum_mem_intAf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → E)
    (hu : ∀ y ∈ Λ, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = ∑ k, u k * y k)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∑ k, (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * z k ∈ Formalism.L2.Herm.intAf F E := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨c, hc⟩ := hu y hy
    have hm : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E :=
      Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
    convert hm using 1
    rw [hc, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y k ⊗ₜ[F] 1) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hx hy
  | smul c x _ hx =>
    have := mul_mem c.2 hx
    convert this using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (c.1 * x k) = _
    ring

theorem pair_mem_intAf : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ v : Fin W.rank → D.host.E, finVec W v ∈ gLat W 1 → ∀ a : Fin W.rank, ∑ k, eToEAf D (∑ l, D.sp.cm.sig (v l) * W.gram l k) * β.val k a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D W β Λ hβ v hv a
  have hΛ := GlobalTheory.PrincInLevel.eq_latC hβ
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hβ; exact h
  obtain ⟨h1, -, hfg, hsp, -, -, -, -, -, -, hsd⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D W
  have hv' : v ∈ GlobalTheory.Member.latC W := by
    obtain ⟨z, hz, e⟩ := hv
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    rw [h1] at hz
    exact ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E W.rank _ hfg hsp).1 v).1 hz
  have hcol : (fun k => β.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    refine (hfr _).2 fun i => ?_
    have e : ((β⁻¹).val *ᵥ fun k => β.val k a) i = ((β⁻¹).val * β.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine sum_mem_intAf Λ (fun k => ∑ l, D.sp.cm.sig (v l) * W.gram l k) (fun y hy => ?_) _ hcol
  rw [hΛ] at hy
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 ((hsd y).2 hy v hv')
  refine ⟨c, hc.trans (Finset.sum_congr rfl fun k _ => ?_)⟩
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  change y k * W.gram l k * D.sp.cm.sig (v l) = _
  ring

end GlobalTheory.PairIntegral
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.CharZero

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
private theorem extensionEmbedding_infiniteAdele_algebraMap (F : Type) [Field F] [NumberField F]
    (x : F) (v : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding v ((algebraMap F (InfiniteAdeleRing F) x) v) =
      v.embedding x := by
  simp [InfinitePlace.Completion.extensionEmbedding_coe]

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
private theorem sum_infinitePlace_embedding_eq_trace (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (x : F) :
    ∑ v : InfinitePlace F, v.embedding x = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  let e : InfinitePlace F ≃ (F →+* ℂ) :=
    { toFun := fun v => v.embedding
      invFun := InfinitePlace.mk
      left_inv := fun v => InfinitePlace.mk_embedding v
      right_inv := fun φ => InfinitePlace.embedding_mk_eq_of_isReal
        (IsTotallyReal.complexEmbedding_isReal φ) }
  rw [Fintype.sum_equiv e (fun v => v.embedding x) (fun φ => φ x) (fun _ => rfl)]
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := x)
  rw [← eq_ratCast (algebraMap ℚ ℂ), h]
  convert Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x)
    (fun φ : F →ₐ[ℚ] ℂ => φ x) (fun _ => rfl)


open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
theorem _root_.GlobalTheory.GaugeEx.CharZero.exists_isCharAF :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ ψ, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF F ψ := by
  intro F _ _ _
  let L : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F →+ ℂ := ∑ v : InfinitePlace F,
    (InfinitePlace.Completion.extensionEmbedding v).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun w : InfinitePlace F => w.Completion) v)
  have hLapply : (L : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F → ℂ) = fun a => ∑ v : InfinitePlace F,
      InfinitePlace.Completion.extensionEmbedding v (a v) := by
    ext a
    simp [L, Pi.evalAddMonoidHom]
  have hL : Continuous L := by
    rw [hLapply]
    exact continuous_finsetSum _ fun v _ =>
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
        (continuous_apply v)
  obtain ⟨ψ, hψ, -⟩ := _root_.GlobalTheory.StdAdelicChar.exists_char_of_trace F L hL (fun x => by
    rw [hLapply]
    change ∑ v : InfinitePlace F, InfinitePlace.Completion.extensionEmbedding v
      ((algebraMap F (InfiniteAdeleRing F) x) v) = _
    simp only [extensionEmbedding_infiniteAdele_algebraMap]
    exact sum_infinitePlace_embedding_eq_trace F x)
  exact ⟨ψ, hψ⟩

end GlobalTheory.GaugeEx.CharZero

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct Pointwise

namespace GlobalTheory.HostSplit

theorem jacobiSym_neg_eq_one {r p : ℕ} (hr : r % 2 = 1) (h4 : p % 4 = 1) (h1 : p % r = 1) :
    jacobiSym (-(r : ℤ)) p = 1 := by
  have hgo : Odd p := Nat.odd_iff.mpr (by omega)
  have hdo : Odd r := Nat.odd_iff.mpr hr
  rw [jacobiSym.neg _ hgo, ZMod.χ₄_nat_one_mod_four h4, one_mul,
    jacobiSym.quadratic_reciprocity_one_mod_four' hdo h4, jacobiSym.mod_left]
  have h2 : ((p : ℤ) % (r : ℤ)) = 1 := by
    rw [← Int.natCast_mod, h1]
    rfl
  rw [h2, jacobiSym.one_left]

theorem ncard_placesOver (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    (placesOver E p).ncard = (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have himg : HeightOneSpectrum.asIdeal '' placesOver E p =
      Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hPp := v.isPrime
      refine ⟨hPp, ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_⟩⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ v.asIdeal
      rw [map_natCast]
      exact hv
    · rintro ⟨h1, h2⟩
      refine ⟨⟨P, h1, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
      have h3 : (p : ℤ) ∈ P.under ℤ := by
        rw [← Ideal.over_def P (Ideal.span {(p : ℤ)})]
        exact Ideal.mem_span_singleton_self _
      have h4 : algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ P := h3
      rw [map_natCast] at h4
      exact h4
  rw [← himg, Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)]

theorem ncard_primesOver_of_stabilizer (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (h : ∀ σ : E ≃ₐ[ℚ] E, σ ∈ MulAction.stabilizer (E ≃ₐ[ℚ] E) P → σ = 1) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hr : Set.range (fun σ : E ≃ₐ[ℚ] E => σ • P) = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have hinj : Function.Injective (fun σ : E ≃ₐ[ℚ] E => σ • P) := by
    intro σ τ hστ
    have h1 : τ⁻¹ * σ = 1 := by
      apply h
      rw [MulAction.mem_stabilizer_iff, mul_smul]
      have h2 : σ • P = τ • P := hστ
      rw [h2, inv_smul_smul]
    exact (inv_mul_eq_one.mp h1).symm
  rw [← hr, Set.ncard_range_of_injective hinj, IsGalois.card_aut_eq_finrank]

theorem split_of_one_mod : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → p % (H.QS * H.q * H.d) = 1 →
    (placesOver H.E p).ncard = Module.finrank ℚ H.E ∧ H.cls p = PrimeClass.splitK := by
  intro R H p hp hc
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hmod : ∀ m : ℕ, 1 < m → m ∣ H.QS * H.q * H.d → p % m = 1 := by
    intro m hm hdv
    rw [← Nat.mod_mod_of_dvd p hdv, hc]
    exact Nat.mod_eq_of_lt hm
  have h4Q : 4 ∣ H.QS := (show (2 : ℕ) ^ 2 ∣ 2 ^ (R.e + 2) from pow_dvd_pow 2 (by omega)).trans H.tower_dvd
  have h4 : p % 4 = 1 := hmod 4 (by norm_num) ((h4Q.mul_right _).mul_right _)
  have hd : p % H.d = 1 := hmod _ (by omega) (dvd_mul_left _ _)
  have hnd : ∀ m : ℕ, m ∣ H.QS * H.q * H.d → ¬ p ∣ m := by
    intro m hm hpm
    have h := hmod p hp.one_lt (hpm.trans hm)
    rw [Nat.mod_self] at h
    omega
  have hN : ¬ p ∣ H.condN := hnd _ dvd_rfl
  have hp2 : p ∉ H.small := fun h =>
    hnd H.QS (((dvd_refl _).mul_right _).mul_right _) (Nat.dvd_of_mem_primeFactors h)
  have hpq : p ≠ H.q := fun h => hnd H.q ((dvd_mul_left _ _).mul_right _) (h ▸ dvd_rfl)
  have hpd : p ≠ H.d := fun h => hnd H.d (dvd_mul_left _ _) (h ▸ dvd_rfl)
  have jd := jacobiSym_neg_eq_one (r := H.d) (by omega) h4 hd
  refine ⟨?_, ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hG : IsGalois ℚ H.E := H.galois
    have := Formalism.FrobeniusOrbits.SplitK.span_prime p
    obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E)))
    obtain ⟨-, hF, -, hI⟩ := H.der.frob p hN P
    have h1 : IsArithFrobAt ℤ (1 : H.E ≃ₐ[ℚ] H.E) P := by
      refine (hF 1 1 ?_).2 (by rw [map_one, map_one])
      rw [← ZMod.natCast_mod p, show p % H.condN = 1 from hc]
      simp
    rw [ncard_placesOver H.E hp]
    refine ncard_primesOver_of_stabilizer H.E p P fun σ hσ => ?_
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul p P 1 σ h1 hσ
    rw [(hI ρ).1 hρ, one_pow, mul_one]
  · unfold Host.cls primeClass
    rw [if_neg hp2, if_neg hpq, if_neg hpd, if_pos jd]

end GlobalTheory.HostSplit
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem prod_norm_embeddings_eq_abs_norm (E : Type) [Field E] [NumberField E] (γ : E) :
    ∏ φ : E →+* ℂ, ‖φ γ‖ = |((Algebra.norm ℚ γ : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ γ
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_prod, eq_ratCast] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => ‖φ γ‖)
    (fun φ : E →ₐ[ℚ] ℂ => ‖φ γ‖) (fun _ => rfl), ← h2]
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  simp

theorem norm_typeNorm_sq_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (γ : E) (σ : K →+* ℂ), ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ ^ 2 = |(Algebra.norm ℚ γ : ℝ)| ^ n := by
  intro E _ _ _ _ r n hr K _ hK γ σ
  let s : (E →+* ℂ) → (E →+* ℂ) := fun τ => σ.comp (τ.codRestrict K (hK τ))
  have hs : ∀ τ x, s τ x = σ ⟨τ x, hK τ x⟩ := fun _ _ => rfl
  have hinj : Function.Injective s := by
    intro a b hab
    ext x
    have := DFunLike.congr_fun hab x
    rw [hs, hs] at this
    exact congrArg Subtype.val (σ.injective this)
  have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
  have hconj : ∀ τ, ‖s (ComplexEmbedding.conjugate τ) γ‖ = ‖s τ γ‖ := by
    intro τ
    have h1 : s (ComplexEmbedding.conjugate τ) γ = s τ (IsCMField.complexConj E γ) := by
      rw [hs, hs]
      congr 2
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    rw [h1, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have hinv : Function.Involutive
      (fun τ : E →+* ℂ => ComplexEmbedding.conjugate τ) := fun τ => star_star τ
  have hP : ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ := by
    rw [map_prod, norm_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, norm_pow, hs]
  have hQ : ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ
      = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r (ComplexEmbedding.conjugate τ) := by
    rw [← hinv.bijective.prod_comp (fun τ => ‖s τ γ‖ ^ r τ)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hconj]
  rw [hP, sq]
  nth_rewrite 2 [hQ]
  rw [← Finset.prod_mul_distrib, ← prod_norm_embeddings_eq_abs_norm,
    ← hbij.prod_comp (fun φ => ‖φ γ‖), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← pow_add, hr]

end GlobalTheory.Mem
end
