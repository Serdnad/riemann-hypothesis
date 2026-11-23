module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AeEqCosetAvgOfMemInvariantSubspace
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap.PGap

theorem pt_bound {z p q t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : 0 < t) (h : z ^ 2 ≤ 1 / 25 * (p * q)) :
    |z| ≤ (t * p + q / t) / 10 := by
  have hts : t * (q / t) = q := by field_simp
  have hw : 0 ≤ (t * p + q / t) / 10 := by positivity
  have h4 : z ^ 2 ≤ ((t * p + q / t) / 10) ^ 2 := by
    nlinarith [sq_nonneg (t * p - q / t)]
  exact abs_le_of_sq_le_sq' h4 hw |> fun h => abs_le.mpr h

section Ang

variable {Λ S : Type} [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  {μ : Measure S} [μ.IsMulLeftInvariant] {j : Λ →* S}
  (hU : Unfold) (hj : Function.Injective j) {B : Subgroup Λ} {DB : Set S}
  (hDB : IsFundamentalDomain (B.map j) DB μ)

include hU hj hDB

theorem perp_avg {K : Subgroup Λ} (hBK : B ≤ K) (hiK : (B.subgroupOf K).index ≠ 0) {DK : Set S}
    (hDK : IsFundamentalDomain (K.map j) DK μ) {a : S → ℝ} (ha : Good j B μ DB a)
    (hperp : cls j B μ DB a ∈ (W j B μ DB K)ᗮ) : cls j B μ DB (avg j B K a) = 0 := by
  have hm := good_avg hU hj hDB hBK hiK hDK ha
  have hmK : LInv j K (avg j B K a) := u_inv μ hU hj hBK hiK ha.2.1
  have hmW := mem_W_of_inv hU hj hDB hBK hiK hDK hm hmK
  have h0 := Submodule.inner_right_of_mem_orthogonal hmW hperp
  rw [cls_inner hm ha] at h0
  have key : ∫ x in DB, avg j B K a x ^ 2 ∂μ = ∫ x in DB, avg j B K a x * a x ∂μ := by
    have e : (fun x => avg j B K a x ^ 2) = fun x => avg j B K a x * avg j B K a x := by
      funext x; ring
    rw [e, u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => avg j B K a x * avg j B K a x) (hm.1.mul hm.1) (linv_mul j hm.2.1 hm.2.1)
        (integrableOn_mul hm.2.2 hm.2.2),
      u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => avg j B K a x * a x) (hm.1.mul ha.1) (linv_mul j hm.2.1 ha.2.1)
        (integrableOn_mul hm.2.2 ha.2.2)]
    congr 2; funext x
    rw [avg_mul_left j hmK, avg_mul_left j hmK, u_id μ hU hj hBK hiK hmK]
  have hn : ‖cls j B μ DB (avg j B K a)‖ ^ 2 = 0 := by rw [cls_norm_sq hm, key, h0]
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hn)

theorem core (hD : Design) {E E' K : Subgroup Λ} (hB : B = E ⊓ E') (hEK : E ≤ K) (hE'K : E' ≤ K)
    (hiK : (B.subgroupOf K).index ≠ 0) (htwo : TwoTr E K) (hbig : 25 ≤ (B.subgroupOf E').index)
    {DK : Set S} (hDK : IsFundamentalDomain (K.map j) DK μ) {a b : S → ℝ} (ha : Good j B μ DB a)
    (haE : LInv j E a) (hz : ∀ x, avg j B K a x = 0) (hb : Good j B μ DB b) (hbE : LInv j E' b) :
    |∫ x in DB, a x * b x ∂μ| ≤
      1 / 5 * (Real.sqrt (∫ x in DB, a x ^ 2 ∂μ) * Real.sqrt (∫ x in DB, b x ^ 2 ∂μ)) := by
  have hBK : B ≤ K := hB ▸ inf_le_left.trans hEK
  have hab := integrableOn_mul ha.2.2 hb.2.2
  have haa := integrableOn_mul ha.2.2 ha.2.2
  have hbb := integrableOn_mul hb.2.2 hb.2.2
  have sa : (fun x => a x ^ 2) = fun x => a x * a x := by funext x; ring
  have sb : (fun x => b x ^ 2) = fun x => b x * b x := by funext x; ring
  rw [sa, sb]
  rw [u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => a x * b x) (ha.1.mul hb.1) (linv_mul j ha.2.1 hb.2.1) hab,
    u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => a x * a x) (ha.1.mul ha.1) (linv_mul j ha.2.1 ha.2.1) haa,
    u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => b x * b x) (hb.1.mul hb.1) (linv_mul j hb.2.1 hb.2.1) hbb]
  have iab := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => a x * b x) (ha.1.mul hb.1) (linv_mul j ha.2.1 hb.2.1) hab
  have iaa := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => a x * a x) (ha.1.mul ha.1) (linv_mul j ha.2.1 ha.2.1) haa
  have ibb := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => b x * b x) (hb.1.mul hb.1) (linv_mul j hb.2.1 hb.2.1) hbb
  set n : ℝ := ((B.subgroupOf K).index : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Nat.pos_of_ne_zero hiK
  set I := ∫ x in DK, avg j B K (fun y => a y * b y) x ∂μ
  set X := ∫ x in DK, avg j B K (fun y => a y * a y) x ∂μ
  set Y := ∫ x in DK, avg j B K (fun y => b y * b y) x ∂μ
  have pa : ∀ x, 0 ≤ avg j B K (fun y => a y * a y) x := fun x => avg_nonneg j (fun y => mul_self_nonneg _) x
  have pb : ∀ x, 0 ≤ avg j B K (fun y => b y * b y) x := fun x => avg_nonneg j (fun y => mul_self_nonneg _) x
  have hX : 0 ≤ X := integral_nonneg pa
  have hY : 0 ≤ Y := integral_nonneg pb
  have hpt : ∀ x, avg j B K (fun y => a y * b y) x ^ 2 ≤
      1 / 25 * (avg j B K (fun y => a y * a y) x * avg j B K (fun y => b y * b y) x) := by
    intro x
    have := hD Λ S j B E E' K hB hEK hE'K hiK htwo hbig a b haE hbE x (hz x)
    simpa only [sq] using this
  have ht : ∀ t : ℝ, 0 < t → |I| ≤ (t * X + Y / t) / 10 := by
    intro t ht
    calc |I| ≤ ∫ x in DK, |avg j B K (fun y => a y * b y) x| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ.restrict DK)
            (fun x => avg j B K (fun y => a y * b y) x)
      _ ≤ ∫ x in DK, (t * avg j B K (fun y => a y * a y) x + avg j B K (fun y => b y * b y) x / t) / 10 ∂μ :=
          integral_mono iab.abs (((iaa.const_mul t).add (ibb.div_const t)).div_const 10)
            fun x => pt_bound (pa x) (pb x) ht (hpt x)
      _ = (t * X + Y / t) / 10 := by
          rw [integral_div, integral_add (iaa.const_mul t) (ibb.div_const t), integral_const_mul,
            integral_div]
  have h1 := t_trick hX hY ht
  rw [abs_mul, abs_of_pos hn0, Real.sqrt_mul hn0.le, Real.sqrt_mul hn0.le]
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  calc n * |I| ≤ n * (1 / 5 * (Real.sqrt X * Real.sqrt Y)) := mul_le_mul_of_nonneg_left h1 hn0.le
    _ = 1 / 5 * (Real.sqrt n * Real.sqrt X * (Real.sqrt n * Real.sqrt Y)) := by
      linear_combination (-(1 / 5 * (Real.sqrt X * Real.sqrt Y))) * hs

theorem angle (hD : Design) {E E' K : Subgroup Λ} (hB : B = E ⊓ E') (hEK : E ≤ K) (hE'K : E' ≤ K)
    (hiK : (B.subgroupOf K).index ≠ 0) (htwo : TwoTr E K) (hbig : 25 ≤ (B.subgroupOf E').index)
    {DK DE DE' : Set S} (hDK : IsFundamentalDomain (K.map j) DK μ)
    (hDE : IsFundamentalDomain (E.map j) DE μ) (hDE' : IsFundamentalDomain (E'.map j) DE' μ) :
    ∀ u ∈ W j B μ DB E, u ∈ (W j B μ DB K)ᗮ → ∀ u' ∈ W j B μ DB E',
      |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖) := by
  intro u hu hperp u' hu'
  have hBE : B ≤ E := hB ▸ inf_le_left
  have hBE' : B ≤ E' := hB ▸ inf_le_right
  have hBK : B ≤ K := hBE.trans hEK
  have hiE := (idx_ne hBE hEK hiK).1
  have hiE' := (idx_ne hBE' hE'K hiK).1
  obtain ⟨a, ha, rfl⟩ := cls_surj u
  obtain ⟨b, hb, rfl⟩ := cls_surj u'
  have ha1 := good_avg hU hj hDB hBE hiE hDE ha
  have ha1E : LInv j E (avg j B E a) := u_inv μ hU hj hBE hiE ha.2.1
  have e1 : cls j B μ DB a = cls j B μ DB (avg j B E a) :=
    (cls_eq_iff ha ha1).2 (ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE hiE hDE ha hu)
  have hb1 := good_avg hU hj hDB hBE' hiE' hDE' hb
  have hb1E : LInv j E' (avg j B E' b) := u_inv μ hU hj hBE' hiE' hb.2.1
  have e2 : cls j B μ DB b = cls j B μ DB (avg j B E' b) :=
    (cls_eq_iff hb hb1).2 (ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE' hiE' hDE' hb hu')
  rw [e1] at hperp ⊢
  rw [e2]
  have hm := good_avg hU hj hDB hBK hiK hDK ha1
  have hmK : LInv j K (avg j B K (avg j B E a)) := u_inv μ hU hj hBK hiK ha1.2.1
  have h0 := perp_avg hU hj hDB hBK hiK hDK ha1 hperp
  have ha2 := good_sub ha1 hm
  have e3 : cls j B μ DB (avg j B E a) =
      cls j B μ DB (fun x => avg j B E a x - avg j B K (avg j B E a) x) := by
    rw [cls_sub ha1 hm, h0, sub_zero]
  rw [e3]
  have ha2E : LInv j E (fun x => avg j B E a x - avg j B K (avg j B E a) x) :=
    linv_sub j ha1E (linv_mono j hEK hmK)
  have hz : ∀ x, avg j B K (fun x => avg j B E a x - avg j B K (avg j B E a) x) x = 0 := by
    intro x
    rw [avg_sub j hiK, u_id μ hU hj hBK hiK hmK, sub_self]
  rw [cls_inner ha2 hb1, ← Real.sqrt_sq (norm_nonneg (cls j B μ DB _)),
    ← Real.sqrt_sq (norm_nonneg (cls j B μ DB (avg j B E' b))), cls_norm_sq ha2, cls_norm_sq hb1]
  exact core hU hj hDB hD hB hEK hE'K hiK htwo hbig hDK ha2 ha2E hz hb1 hb1E

end Ang

end PositivityTheory.KB.SpectralGap.PGap

end
end

section

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SpectralGap.GlueM

instance instLCSL (n : ℕ) : LocallyCompactSpace (Matrix.SpecialLinearGroup (Fin n) ℂ) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance instSCSL (n : ℕ) : SecondCountableTopology (Matrix.SpecialLinearGroup (Fin n) ℂ) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.secondCountableTopology

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

instance instCountSL : Countable (Matrix.SpecialLinearGroup (Fin N) L) := by
  have : Countable L := Countable.of_equiv _ (Module.finBasis ℚ L).equivFun.symm.toEquiv
  have : Countable (Matrix (Fin N) (Fin N) L) := inferInstanceAs (Countable (Fin N → Fin N → L))
  exact inferInstanceAs (Countable (Subtype _))

theorem continuous_ofS : Continuous (ofS L N) := by
  show Continuous fun x : Sp L N => fun w => Matrix.SpecialLinearGroup.toGL (x w)
  exact continuous_pi fun w => Matrix.SpecialLinearGroup.continuous_toGL.comp (continuous_apply w)

theorem coe_jS (g : Matrix.SpecialLinearGroup (Fin N) L) (w : InfinitePlace L) :
    ((jS L N g w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (g : Matrix (Fin N) (Fin N) L).map w.embedding := rfl

theorem jS_injective : Function.Injective (jS L N) := by
  intro g g' h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have h1 := congrArg (fun x : Sp L N => ((x w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) h
  simp only [coe_jS] at h1
  ext i j
  exact w.embedding.injective (congrFun (congrFun h1 i) j)

theorem scal_comm (s : InfinitePlace L → ℂˣ) (g : Gp L N) : scal L N s * g = g * scal L N s := by
  funext w
  apply Units.ext
  show Matrix.scalar (Fin N) (s w : ℂ) * ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
    ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * Matrix.scalar (Fin N) (s w : ℂ)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ _) _).eq

theorem det_dg_ne (π : 𝓞 L) (hπ : π ≠ 0) (r : ℕ) : (dg L N π r).det ≠ 0 := by
  rw [dg, det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  split_ifs
  · exact_mod_cast hπ
  · exact one_ne_zero

theorem exists_q (π : 𝓞 L) (hπ : π ≠ 0) (r : ℕ) (hN : 0 < N) : ∃ (q : Sp L N) (s : InfinitePlace L → ℂˣ),
    ∀ w, (q w : Matrix (Fin N) (Fin N) ℂ) = (s w : ℂ) • (dg L N π r).map w.embedding := by
  have hc : ∀ w : InfinitePlace L, ((dg L N π r).map w.embedding).det ≠ 0 := fun w => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (det_dg_ne L N π hπ r)
  choose t ht using fun w : InfinitePlace L => IsAlgClosed.exists_pow_nat_eq (((dg L N π r).map w.embedding).det) hN
  have ht0 : ∀ w, t w ≠ 0 := fun w h0 => hc w (by rw [← ht w, h0, zero_pow hN.ne'])
  let s : InfinitePlace L → ℂˣ := fun w => Units.mk0 (t w)⁻¹ (inv_ne_zero (ht0 w))
  refine ⟨fun w => ⟨(s w : ℂ) • (dg L N π r).map w.embedding, ?_⟩, s, fun w => rfl⟩
  rw [Matrix.det_smul, Fintype.card_fin, ← ht w]
  simp only [s, Units.val_mk0, inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero _ (ht0 w))

theorem coe_latS (γ : Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) (w : InfinitePlace L) :
    ((((MonoidHom.pi fun w : InfinitePlace L => Matrix.SpecialLinearGroup.map (n := Fin N) (embO w)) γ) w :
      Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = (mo L N γ).map w.embedding := by
  ext i j
  simp [mo, mt, embO]

theorem mem_map_congruence_iff_conj_mem_lattice_of_inverse (π : 𝓞 L) (r : ℕ) (Di : Matrix (Fin N) (Fin N) L) (hDiD : Di * dg L N π r = 1)
    (hDDi : dg L N π r * Di = 1) (q : Sp L N) (s : InfinitePlace L → ℂˣ)
    (hq : ∀ w, (q w : Matrix (Fin N) (Fin N) ℂ) = (s w : ℂ) • (dg L N π r).map w.embedding) (y : Sp L N) :
    y ∈ (Kg L N π r).map (jS L N) ↔ q * y * q⁻¹ ∈ latS L N := by
  have key : ∀ l : Sp L N, q * y * q⁻¹ = l ↔ q * y = l * q := fun l => mul_inv_eq_iff_eq_mul
  constructor
  · rintro ⟨g, ⟨γ, hγ⟩, rfl⟩
    refine ⟨γ, ?_⟩
    rw [eq_comm, key]
    funext w
    apply Subtype.ext
    show (q w : Matrix (Fin N) (Fin N) ℂ) * (jS L N g w : Matrix (Fin N) (Fin N) ℂ) =
      ((((MonoidHom.pi fun w : InfinitePlace L => Matrix.SpecialLinearGroup.map (n := Fin N) (embO w)) γ) w :
        Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (q w : Matrix (Fin N) (Fin N) ℂ)
    rw [hq, coe_latS, coe_jS, smul_mul_assoc, mul_smul_comm, ← Matrix.map_mul, ← Matrix.map_mul]
    rw [show dg L N π r * (g : Matrix (Fin N) (Fin N) L) = mo L N γ * dg L N π r from hγ]
  · rintro ⟨γ, hγ⟩
    rw [eq_comm, key] at hγ
    have hw : ∀ w : InfinitePlace L, (dg L N π r).map w.embedding * (y w : Matrix (Fin N) (Fin N) ℂ) =
        (mo L N γ).map w.embedding * (dg L N π r).map w.embedding := by
      intro w
      have h1 := congrArg (fun x : Sp L N => ((x w : Matrix.SpecialLinearGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)) hγ
      change (q w : Matrix (Fin N) (Fin N) ℂ) * (y w : Matrix (Fin N) (Fin N) ℂ) =
        ((((MonoidHom.pi fun w : InfinitePlace L => Matrix.SpecialLinearGroup.map (n := Fin N) (embO w)) γ) w :
          Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (q w : Matrix (Fin N) (Fin N) ℂ) at h1
      rw [hq, coe_latS, smul_mul_assoc, mul_smul_comm] at h1
      exact smul_right_injective _ (s w).ne_zero h1
    have hdet : (Di * mo L N γ * dg L N π r).det = 1 := by
      rw [det_mul, det_mul, show (mo L N γ).det = 1 from (Matrix.SpecialLinearGroup.map (algebraMap (𝓞 L) L) γ).2,
        mul_one, ← det_mul, hDiD, det_one]
    refine ⟨⟨Di * mo L N γ * dg L N π r, hdet⟩, ⟨γ, ?_⟩, ?_⟩
    · show dg L N π r * (Di * mo L N γ * dg L N π r) = mo L N γ * dg L N π r
      rw [← mul_assoc, ← mul_assoc, hDDi, one_mul]
    · funext w
      apply Subtype.ext
      show (Di * mo L N γ * dg L N π r).map w.embedding = (y w : Matrix (Fin N) (Fin N) ℂ)
      have hDw : Di.map w.embedding * (dg L N π r).map w.embedding = 1 := by
        rw [← Matrix.map_mul, hDiD]
        exact map_one w.embedding.mapMatrix
      rw [Matrix.map_mul, Matrix.map_mul, mul_assoc, ← hw, ← mul_assoc, hDw, one_mul]

theorem mem_map_Kg (π : 𝓞 L) (hπ : π ≠ 0) (r : ℕ) (q : Sp L N) (s : InfinitePlace L → ℂˣ)
    (hq : ∀ w, (q w : Matrix (Fin N) (Fin N) ℂ) = (s w : ℂ) • (dg L N π r).map w.embedding) (y : Sp L N) :
    y ∈ (Kg L N π r).map (jS L N) ↔ q * y * q⁻¹ ∈ latS L N := by
  have hπL : (π : L) ≠ 0 := by exact_mod_cast hπ
  refine mem_map_congruence_iff_conj_mem_lattice_of_inverse L N π r (diagonal fun i : Fin N => if (i : ℕ) < r then (π : L)⁻¹ else 1) ?_ ?_ q s hq y
  · rw [dg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [hπL]
  · rw [dg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [hπL]

theorem map_Kg_zero (π : 𝓞 L) : (Kg L N π 0).map (jS L N) = latS L N := by
  have hdg : dg L N π 0 = 1 := by simp [dg]
  ext y
  rw [mem_map_congruence_iff_conj_mem_lattice_of_inverse L N π 0 1 (by rw [hdg, one_mul]) (by rw [hdg, one_mul]) 1 1 (fun w => by simp [hdg]) y]
  simp

theorem latS_emb (x : Sp L N) (hx : x ∈ latS L N) : ∃ γ : Gm L N, ofS L N x = emb L N γ := by
  obtain ⟨γ, rfl⟩ := hx
  refine ⟨Matrix.SpecialLinearGroup.toGL γ, ?_⟩
  funext w
  apply Units.ext
  ext i j
  simp [ofS, emb, toP, toK, embO]

theorem ofS_q (π : 𝓞 L) (hπ : π ≠ 0) (q : Sp L N) (s : InfinitePlace L → ℂˣ)
    (hq : ∀ w, (q w : Matrix (Fin N) (Fin N) ℂ) = (s w : ℂ) • (dg L N π 1).map w.embedding) :
    ofS L N q = scal L N s * toP L N (qel L N π hπ) := by
  funext w
  apply Units.ext
  show (q w : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (s w : ℂ) *
    ((qel L N π hπ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L).map w.embedding
  rw [hq, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  congr 2
  show dg L N π 1 = diagonal fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1
  simp only [dg, Nat.lt_one_iff]

end PositivityTheory.KB.SpectralGap.GlueM

end
end
