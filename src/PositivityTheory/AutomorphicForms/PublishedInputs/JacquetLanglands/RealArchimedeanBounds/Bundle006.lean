module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.OhatCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightMultiplicativityAlt

theorem rowF_mul {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x y : GF F) :
    rowF s (x * y) = rowF s x ᵥ* y.val := by
  simp only [rowF, Units.val_mul, Matrix.vecMul_vecMul]

theorem row_mul {F : Type} [Field F] [NumberField F] (t : Af F) (k : GF F) (M : Matrix (Fin 2) (Fin 2) (Af F)) :
    (fun i => t * k.val 1 i) ᵥ* M = fun i => t * (k.val * M) 1 i := by
  ext i
  simp [Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, mul_add, mul_assoc]

theorem zc_val {F : Type} [Field F] [NumberField F] (z : (Af F)ˣ) :
    (zc F z).val = Matrix.scalar (Fin 2) (z : Af F) := rfl

theorem det_zc {F : Type} [Field F] [NumberField F] (z : (Af F)ˣ) :
    Matrix.GeneralLinearGroup.det (zc F z) = z * z := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, zc_val, pow_two]

theorem part1 (hM : AMem) (hR : ARow) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ)
    (s : Fin 2 → F) (hs : s ≠ 0) (x h : GF F) (hh : h ∈ Hc c) :
    absF (Matrix.GeneralLinearGroup.det (x * h)) / nF s (x * h) ^ 2 =
      absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 := by
  obtain ⟨-, -, hKc, hH, hdet, -⟩ := hM F
  obtain ⟨hA1, hA2, hA3, -⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨k', hk', z, rfl⟩ := (hH c h).1 hh
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  have hk'0 : k' ∈ K0 F := hKc c hk'
  have e1 : nF s x = absF t := (hR F s x).2 t k hk ht
  have hx : rowF s x = fun i => (t : Af F) * k.val 1 i := funext ht
  have e2 : nF s (x * (k' * zc F z)) = absF (t * z) := by
    refine (hR F s _).2 (t * z) (k * k') (mul_mem hk hk'0) fun i => ?_
    rw [rowF_mul, hx, row_mul]
    simp only [Units.val_mul, zc_val, ← Matrix.mul_assoc, Matrix.scalar_apply, Matrix.mul_diagonal]
    ring
  have e3 : absF (Matrix.GeneralLinearGroup.det k') = 1 := hA3 _ fun w => (hdet k' hk'0 w).1
  rw [e1, e2, map_mul, map_mul, det_zc]
  simp only [hA2, e3]
  have := (hA1 t).ne'
  have := (hA1 z).ne'
  field_simp

theorem part2 (hM : AMem) (hR : ARow) (hMo : AMono) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (a : GF F) : ∃ C : ℝ, ∀ s : Fin 2 → F, s ≠ 0 → ∀ x : GF F,
      absF (Matrix.GeneralLinearGroup.det (x * a)) / nF s (x * a) ^ 2 ≤
        C * (absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2) := by
  obtain ⟨hK, hO, -, -, hdet, -, hN, -⟩ := hM F
  obtain ⟨hA1, hA2, -, -⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨N, hN0, hNa⟩ := hN a⁻¹
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨n, hn⟩ : ∃ n : (Af F)ˣ, (n : Af F) = (N : Af F) :=
    ⟨ratU F (Units.mk0 (N : F) hNF), by simp [ratU]⟩
  refine ⟨absF (Matrix.GeneralLinearGroup.det a) / absF n ^ 2, fun s hs x => ?_⟩
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  obtain ⟨t', k', hk', ht'⟩ := (hR F s (x * a)).1 hs
  rw [(hR F s x).2 t k hk ht, (hR F s (x * a)).2 t' k' hk' ht']
  have key : absF (n * t) ≤ absF t' := by
    refine hMo F _ _ fun w => ?_
    have hrow : rowF s x = rowF s (x * a) ᵥ* (a⁻¹ : GF F).val := by
      rw [← rowF_mul, mul_inv_cancel_right]
    have hint : ∀ i j, Valued.v (pLoc F w (k'.val i j)) ≤ 1 := fun i j =>
      (hO _).1 (((hK k').1 hk').1 i j) w
    have hint2 : ∀ i j, Valued.v (pLoc F w ((N : Af F) * (a⁻¹ : GF F).val i j)) ≤ 1 := fun i j =>
      (hO _).1 (hNa i j) w
    have heq : ∀ i, (n : Af F) * ((t : Af F) * k.val 1 i) = (t' : Af F) * (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
        k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i)) := by
      intro i
      have h1 := congrFun hrow i
      rw [← ht i, hn, h1]
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ht']
      ring
    have hS : ∀ i, Valued.v (pLoc F w (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
        k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i))) ≤ 1 := by
      intro i
      rw [map_add (f := _)]
      refine Valuation.map_add_le _ ?_ ?_ <;> rw [map_mul, map_mul] <;> exact mul_le_one' (hint _ _) (hint2 _ _)
    have hmax := (hdet k hk w).2
    obtain ⟨i, hi⟩ : ∃ i, Valued.v (pLoc F w (k.val 1 i)) = 1 := by
      rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with h | h
      · exact ⟨0, h.symm.trans hmax⟩
      · exact ⟨1, h.symm.trans hmax⟩
    calc Valued.v (pLoc F w ((n * t : (Af F)ˣ) : Af F))
        = Valued.v (pLoc F w ((n : Af F) * ((t : Af F) * k.val 1 i))) := by
          simp only [Units.val_mul, map_mul, hi, mul_one]
      _ = Valued.v (pLoc F w (t' : Af F)) * Valued.v (pLoc F w (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
          k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i))) := by
          rw [heq i, map_mul (pLoc F w), map_mul Valued.v]
      _ ≤ Valued.v (pLoc F w (t' : Af F)) * 1 := mul_le_mul' le_rfl (hS i)
      _ = _ := mul_one _
  rw [map_mul, hA2]
  have key2 : absF n * absF t ≤ absF t' := by rw [← hA2]; exact key
  have p1 := hA1 n
  have p2 := hA1 t
  have p3 := hA1 t'
  have p4 := hA1 (Matrix.GeneralLinearGroup.det x)
  have p5 := hA1 (Matrix.GeneralLinearGroup.det a)
  calc absF (Matrix.GeneralLinearGroup.det x) * absF (Matrix.GeneralLinearGroup.det a) / absF t' ^ 2
      ≤ absF (Matrix.GeneralLinearGroup.det x) * absF (Matrix.GeneralLinearGroup.det a) / (absF n * absF t) ^ 2 :=
        div_le_div_of_nonneg_left (mul_pos p4 p5).le (pow_pos (mul_pos p1 p2) 2)
          (pow_le_pow_left₀ (mul_pos p1 p2).le key2 2)
    _ = _ := by
      field_simp

end UpperTheory.Esk.HeightMultiplicativityAlt

theorem UpperTheory.Esk.dMul : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.AMono → UpperTheory.Esk.ARow → UpperTheory.Esk.DMul := by
  intro hM _ hMo hR F _ _ _ c _ χ
  exact ⟨fun s hs x h hh => UpperTheory.Esk.HeightMultiplicativityAlt.part1 hM hR F c s hs x h hh,
    fun a => UpperTheory.Esk.HeightMultiplicativityAlt.part2 hM hR hMo F a⟩
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightFunctionLemmas

variable {F : Type} [Field F] [NumberField F]

theorem nF_eq (s : Fin 2 → F) (x : GF F) :
    nF s x = ∏ᶠ w : Pl F, max ‖pLoc F w (rowF s x 0)‖ ‖pLoc F w (rowF s x 1)‖ := rfl

theorem rowF_jF (s : Fin 2 → F) (γ : GL (Fin 2) F) (x : GF F) :
    rowF s (jF F γ * x) = rowF (s ᵥ* γ.val) x := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((s ᵥ* γ.val) i)) =
      (fun i => algebraMap F (Af F) (s i)) ᵥ* (jF F γ).val := by
    funext i
    exact RingHom.map_vecMul (algebraMap F (Af F)) γ.val s i
  rw [h, Units.val_mul, Matrix.vecMul_vecMul]

theorem rowF_smul (s : Fin 2 → F) (a : F) (x : GF F) (i : Fin 2) :
    rowF (a • s) x i = algebraMap F (Af F) a * rowF s x i := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((a • s) i)) = algebraMap F (Af F) a • (fun i => algebraMap F (Af F) (s i)) := by
    funext i
    simp [map_mul]
  rw [h, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]

theorem det_jF (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (jF F γ) = ratU F (Matrix.GeneralLinearGroup.det γ) := by
  apply Units.ext
  change (γ.val.map (algebraMap F (Af F))).det = algebraMap F (Af F) γ.val.det
  exact (RingHom.map_det (algebraMap F (Af F)) γ.val).symm

variable [IsTotallyReal F]

theorem nF_pos (hR : ARow) {s : Fin 2 → F} (hs : s ≠ 0) (x : GF F) : 0 < nF s x := by
  obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
  rw [(hR F s x).2 t k hk h]
  exact (Hm.absf F).1 t

theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = sg v x := by
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem prod_rat (a : Fˣ) : (∏ v, |sg v (a : F)|) * absF (ratU F a) = 1 := by
  have := (Hm.absf F).2.2.2 a
  simp only [reAt_eq] at this
  exact this

end UpperTheory.Esk.HeightFunctionLemmas

open UpperTheory.Esk.HeightFunctionLemmas in
theorem UpperTheory.Esk.dHt : UpperTheory.Esk.ARow → UpperTheory.Esk.DHt := by
  intro hR F _ _ _ c _ χ
  refine ⟨fun s hs x => ?_, fun s hs γ x => ?_, fun s hs a ha x => ?_⟩
  · change 0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2
    exact div_pos ((Hm.absf F).1 _) (pow_pos (nF_pos hR hs x) 2)
  · change absF (Matrix.GeneralLinearGroup.det (jF F γ * x)) / nF s (jF F γ * x) ^ 2 * ∏ v, |sg v γ.val.det| =
      absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2
    have hP := prod_rat (Matrix.GeneralLinearGroup.det γ)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hP
    rw [map_mul, det_jF, (Hm.absf F).2.1, nF_eq s, rowF_jF, ← nF_eq]
    calc absF (ratU F (Matrix.GeneralLinearGroup.det γ)) * absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2 *
          ∏ v, |sg v γ.val.det|
        = ((∏ v, |sg v γ.val.det|) * absF (ratU F (Matrix.GeneralLinearGroup.det γ))) *
          (absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2) := by ring
      _ = _ := by rw [hP, one_mul]
  · change absF (Matrix.GeneralLinearGroup.det x) / nF (a • s) x ^ 2 =
      absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * ∏ v, sg v a ^ 2
    obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
    have h1 := (hR F s x).2 t k hk h
    have h2 : nF (a • s) x = absF (ratU F (Units.mk0 a ha)) * nF s x := by
      rw [(hR F (a • s) x).2 (ratU F (Units.mk0 a ha) * t) k hk (fun i => by
        rw [rowF_smul, h i, Units.val_mul, mul_assoc]; rfl), (Hm.absf F).2.1, h1]
    have hP := prod_rat (Units.mk0 a ha)
    simp only [Units.val_mk0] at hP
    have hA := (Hm.absf F).1 (ratU F (Units.mk0 a ha))
    have hN := nF_pos hR hs x
    have hsq : ∏ v, sg v a ^ 2 = (∏ v, |sg v a|) ^ 2 := by
      rw [← Finset.prod_pow]; simp [sq_abs]
    rw [h2, hsq, eq_inv_of_mul_eq_one_left hP]
    field_simp
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aOrb : AMem → AOrb := by
  intro _ F _ _ c hc x
  have hT := UpperTheory.V.Sd.Wc.kcTop F
  have hK0 : IsCompact (K0 F : Set (GF F)) := ((hT.1 (fun _ => 0) (by simp)).2)
  have hKo : IsOpen (Kc c : Set (GF F)) := (hT.1 c hc).1
  have hs : IsCompact ((fun k : GF F => k * x) '' (K0 F : Set (GF F))) :=
    hK0.image (continuous_id.mul continuous_const)
  obtain ⟨t, -, ht⟩ := hs.elim_nhds_subcover (fun g => (fun y : GF F => g⁻¹ * y) ⁻¹' (Kc c : Set (GF F)))
    (fun g _ => (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [(Kc c).one_mem]))
  refine ⟨t, fun k hk => ?_⟩
  have hm := ht ⟨k, hk, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at hm
  obtain ⟨g, hg, hgk⟩ := hm
  exact ⟨g, hg, g⁻¹ * (k * x), hgk, by rw [mul_inv_cancel_left]⟩

end UpperTheory.Esk
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CentralScalarMap

theorem central_of_map {K L : Type} [Field K] [Field L] (f : K →+* L) {g : GL (Fin 2) K}
    (h : Matrix.GeneralLinearGroup.map f g ∈ Subgroup.center (GL (Fin 2) L)) :
    g ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro δ
  have e := h (Matrix.GeneralLinearGroup.map f δ)
  rw [← map_mul, ← map_mul] at e
  apply Units.ext
  exact Matrix.map_injective f.injective (congrArg Units.val e)

theorem map_scalar_center {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) ∈ Subgroup.center (GL (Fin 2) S) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end UpperTheory.Esk.CentralScalarMap

namespace UpperTheory.Esk

open CentralScalarMap in
theorem dTwo : AMem → DTwo := by
  intro hA F _ _ _ c χ ⟨u, hu, hu2⟩ ω S hS hfin
  obtain ⟨-, -, -, hH, -⟩ := hA F
  have hc0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hc0 (p := 2) ?_⟩
  intro p hp hd
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' (G := S) p hd
  set g : GL (Fin 2) F := (γ : PG F).out with hg
  have hmk : ((g : PG F)) = (γ : PG F) := QuotientGroup.out_eq' _
  have hgp : g ^ p ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← Subgroup.coe_pow, ← hγ, pow_orderOf_eq_one,
      Subgroup.coe_one]
  have hst : (γ : PG F) • ω = ω := hS γ.2
  obtain ⟨x, hx⟩ : ∃ x : GF F, ((x : GF F ⧸ Hc c) : (mkDat c χ).Om) = ω := QuotientGroup.mk_surjective ω
  have h1 : ((jF F g * x : GF F) : GF F ⧸ Hc c) = (x : GF F ⧸ Hc c) := by
    rw [← hmk, ← hx] at hst
    exact hst
  have h2 : x⁻¹ * (jF F g * x) ∈ Hc c := QuotientGroup.eq.1 h1.symm
  obtain ⟨k, hk, z, hkz⟩ := (hH c _).1 h2
  obtain ⟨z0, hz0⟩ := jF_center hgp
  have hzc : ∀ z, zc F z ∈ Subgroup.center (GF F) := zc_center
  have hyp : (x⁻¹ * (jF F g * x)) ^ p = zc F z0 := by
    have := conj_pow (a := x⁻¹) (b := jF F g) (i := p)
    rw [inv_inv] at this
    rw [← mul_assoc, this, ← map_pow, hz0, Subgroup.mem_center_iff.1 (hzc _) x⁻¹, inv_mul_cancel_right]
  have hkp : k ^ p = zc F (z0 * (z ^ p)⁻¹) := by
    have e1 : (k * zc F z) ^ p = k ^ p * zc F z ^ p :=
      Commute.mul_pow (Subgroup.mem_center_iff.1 (hzc z) k) p
    rw [map_mul, map_inv, map_pow, ← hyp, hkz, e1, mul_inv_cancel_right]
  set P := Matrix.GeneralLinearGroup.map (n := Fin 2) (pLoc F u) with hP
  have hPz : ∀ z, P (zc F z) ∈ Subgroup.center _ := fun z => map_scalar_center _ z
  have hku : P k ∈ K1 u (c u) := Subgroup.mem_iInf.1 hk u
  have hkc := locTwo F u (c u) hu hu2 _ hku p (hp.odd_of_ne_two hne) (by rw [← map_pow, hkp]; exact hPz _)
  have hc2 : P (x⁻¹ * (jF F g * x)) ∈ Subgroup.center _ := by
    rw [hkz, map_mul]; exact mul_mem hkc (hPz z)
  have hc3 : P (jF F g) ∈ Subgroup.center _ := by
    have := (Subgroup.normal_of_characteristic _).conj_mem _ hc2 (P x)
    simpa [mul_assoc] using this
  have hcen : g ∈ Subgroup.center (GL (Fin 2) F) :=
    central_of_map ((pLoc F u).comp (algebraMap F (Af F))) hc3
  have h1' : (γ : PG F) = 1 := by
    rw [← hmk]; exact (QuotientGroup.eq_one_iff _).2 hcen
  have : γ = 1 := Subtype.ext h1'
  rw [this, orderOf_one] at hγ
  exact hp.one_lt.ne hγ

end UpperTheory.Esk
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.ClassNumberLemmas

theorem v_one {F : Type} [Field F] [NumberField F] (e : (Af F)ˣ) (h1 : (e : Af F) ∈ PIW.ClassFinD.Ohat F)
    (h2 : ((e⁻¹ : (Af F)ˣ) : Af F) ∈ PIW.ClassFinD.Ohat F) (w : Pl F) : Valued.v (pLoc F w (e : Af F)) = 1 := by
  have a1 : Valued.v (pLoc F w (e : Af F)) ≤ 1 := by
    have h := h1 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have a2 : Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := by
    have h := h2 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hm : Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc (1 : _) = Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) := hm.symm
    _ ≤ Valued.v (pLoc F w (e : Af F)) * 1 := by gcongr
    _ = Valued.v (pLoc F w (e : Af F)) := mul_one _

end UpperTheory.Esk.ClassNumberLemmas

namespace UpperTheory.Esk

theorem aCls : ACls := by
  intro F _ _
  obtain ⟨C, hC⟩ := PIW.ClassFinD.idele_class_finite F
  refine ⟨C, fun z => ?_⟩
  obtain ⟨f, c, hc, e, he1, he2, hz⟩ := hC z
  exact ⟨f, e, c, hc, ClassNumberLemmas.v_one e he1 he2, hz⟩

end UpperTheory.Esk
end
end
