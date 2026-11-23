module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofFinrankIRLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.ETSymmApply
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.MemSpanMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.NstatementOf

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Frame

variable (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
  (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)

theorem sgn_sq (a : Fin r) : ((sgn X.p0 a : ℝ) : ℂ) * ((sgn X.p0 a : ℝ) : ℂ) = 1 := by
  unfold sgn; split_ifs <;> push_cast <;> norm_num

include he in
theorem pair_sum (β : Fin r → ℂ) (s : Finset (Fin r)) (c : Fin r) :
    hermC τ.1 X.Gm (∑ a ∈ s, β a • e a) (e c) =
      if c ∈ s then β c * ((sgn X.p0 c : ℝ) : ℂ) else 0 := by
  rw [hermC_sum_left]
  simp only [hermC_smul_left, he, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']

include he in
theorem e_linInd : LinearIndependent ℂ e := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 := pair_sum X τ e he g Finset.univ i
  rw [hg, hermC_zero_left, if_pos (Finset.mem_univ i)] at h1
  have h2 := sgn_sq X i
  calc g i = g i * (((sgn X.p0 i : ℝ) : ℂ) * ((sgn X.p0 i : ℝ) : ℂ)) := by rw [h2, mul_one]
    _ = (g i * ((sgn X.p0 i : ℝ) : ℂ)) * ((sgn X.p0 i : ℝ) : ℂ) := by ring
    _ = 0 := by rw [← h1, zero_mul]

include he in
theorem e_span : Submodule.span ℂ (Set.range e) = ⊤ := by
  rcases isEmpty_or_nonempty (Fin r) with h | h
  · exact Subsingleton.elim _ _
  · exact (e_linInd X τ e he).span_eq_top_of_card_eq_finrank (by simp)

include he in
theorem expand (u : Fin r → ℂ) :
    u = ∑ a : Fin r, (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a)) • e a := by
  have hu : u ∈ Submodule.span ℂ (Set.range e) := by rw [e_span X τ e he]; trivial
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
  have hc : ∀ a : Fin r, ((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a) = β a := by
    intro a
    rw [← hβ, pair_sum X τ e he β Finset.univ a, if_pos (Finset.mem_univ a)]
    calc ((sgn X.p0 a : ℝ) : ℂ) * (β a * ((sgn X.p0 a : ℝ) : ℂ))
        = β a * (((sgn X.p0 a : ℝ) : ℂ) * ((sgn X.p0 a : ℝ) : ℂ)) := by ring
      _ = β a := by rw [sgn_sq, mul_one]
  simp_rw [hc]
  exact hβ.symm

include he in
theorem self_pair (u : Fin r → ℂ) :
    (hermC τ.1 X.Gm u u).re = ∑ a : Fin r, sgn X.p0 a * ‖hermC τ.1 X.Gm u (e a)‖ ^ 2 := by
  have hx := expand X τ e he u
  calc (hermC τ.1 X.Gm u u).re
      = (hermC τ.1 X.Gm u (∑ a : Fin r,
          (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a)) • e a)).re := by rw [← hx]
    _ = ∑ a : Fin r, sgn X.p0 a * ‖hermC τ.1 X.Gm u (e a)‖ ^ 2 := by
      rw [hermC_sum_right, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hermC_smul_right, map_mul, Complex.conj_ofReal, mul_assoc, Complex.conj_mul',
        ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

end Frame

section Pos

variable (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
  (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
  (x : Frame X.Ψ r)
  (hflag : Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a))
  (hind : LinearIndependent ℂ (X.colP x τ))

theorem sgn_castLE (a : Fin X.p0) : ((sgn X.p0 (Fin.castLE X.p0_le a : ℕ) : ℝ) : ℂ) = 1 := by
  simp [sgn, Fin.coe_castLE, a.isLt]

include he in
theorem proj (y : Fin r → ℂ)
    (hy : y ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a))) :
    y = ∑ a : Fin X.p0, hermC τ.1 X.Gm y (e (Fin.castLE X.p0_le a)) • e (Fin.castLE X.p0_le a) := by
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  symm
  rw [hermC_sum_left]
  simp only [hermC_smul_left, he, Fin.castLE_inj, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ c), sgn_castLE, mul_one]

include he hflag hind in
theorem gramPos_det_ne : (X.gramPos x τ).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨w, hw⟩ : ∃ w : Fin r → ℂ, w = ∑ b : Fin X.p0, conj (v b) • X.colP x τ b := ⟨_, rfl⟩
  have h1 : ∀ a, hermC τ.1 X.Gm (X.colP x τ a) w = 0 := by
    intro a
    have ha := congrFun hv a
    simp only [Matrix.mulVec, dotProduct, Data.gramPos_apply, Pi.zero_apply] at ha
    rw [hw, hermC_sum_right]
    simp only [hermC_smul_right, Complex.conj_conj]
    rw [← ha]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have h2 : ∀ a, hermC τ.1 X.Gm w (X.colP x τ a) = 0 := fun a => by
    rw [← hermC_conj τ.1 X.Gm_herm (X.colP x τ a) w, h1, map_zero]
  have h3 : ∀ y ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a),
      hermC τ.1 X.Gm w y = 0 := by
    intro y hy
    obtain ⟨δ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
    simp [hermC_sum_right, hermC_smul_right, h2]
  have hwf : w ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) := by
    rw [hflag, hw]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hw0 : w = 0 := by
    rw [proj X τ e he w hwf]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [h3 _ (by rw [← hflag]; exact Submodule.subset_span ⟨a, rfl⟩), zero_smul]
  have hz := Fintype.linearIndependent_iff.mp hind (fun b => conj (v b)) (hw ▸ hw0)
  apply hv0
  funext b
  simpa using hz b

include he hflag hind in
theorem posPart_eq (u : Fin r → ℂ) :
    X.posPart x τ u = ∑ a : Fin X.p0, ‖hermC τ.1 X.Gm u (e (Fin.castLE X.p0_le a))‖ ^ 2 := by
  have hdet := gramPos_det_ne X τ e he x hflag hind
  have hG : (X.gramPos x τ)⁻¹ * X.gramPos x τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have hA : ∀ d, hermC τ.1 X.Gm (X.ppos x τ u) (X.colP x τ d) = hermC τ.1 X.Gm u (X.colP x τ d) := by
    intro d
    rw [Data.ppos_eq, hermC_sum_left]
    simp only [hermC_smul_left, ← Data.gramPos_apply]
    have hs : ∑ a : Fin X.p0, (∑ b : Fin X.p0, hermC τ.1 X.Gm u (X.colP x τ b) *
        (X.gramPos x τ)⁻¹ b a) * X.gramPos x τ a d
        = ∑ b : Fin X.p0, hermC τ.1 X.Gm u (X.colP x τ b) *
          ((X.gramPos x τ)⁻¹ * X.gramPos x τ) b d := by
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    rw [hs, hG]
    simp [Matrix.one_apply]
  have hmemC : ∀ y ∈ Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a),
      hermC τ.1 X.Gm (X.ppos x τ u) y = hermC τ.1 X.Gm u y := by
    intro y hy
    obtain ⟨δ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
    simp only [hermC_sum_right, hermC_smul_right, hA]
  have hp : X.ppos x τ u ∈
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) := by
    rw [hflag, Data.ppos_eq]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hpe := proj X τ e he (X.ppos x τ u) hp
  have hcoef : ∀ a : Fin X.p0, hermC τ.1 X.Gm (X.ppos x τ u) (e (Fin.castLE X.p0_le a))
      = hermC τ.1 X.Gm u (e (Fin.castLE X.p0_le a)) := fun a =>
    hmemC _ (by rw [← hflag]; exact Submodule.subset_span ⟨a, rfl⟩)
  simp_rw [hcoef] at hpe
  have h1 : X.posPart x τ u = (hermC τ.1 X.Gm (X.ppos x τ u) u).re := by
    rw [Data.hermC_ppos_self]; rfl
  rw [h1, hpe, hermC_sum_left, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hermC_smul_left, ← hermC_conj τ.1 X.Gm_herm u (e (Fin.castLE X.p0_le a)),
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

include he hflag hind in
theorem maj_eq_sum (u : Fin r → ℂ) :
    X.maj x τ u = ∑ b : Fin r, ‖hermC τ.1 X.Gm u (e b)‖ ^ 2 := by
  set t : Fin r → ℝ := fun b => ‖hermC τ.1 X.Gm u (e b)‖ ^ 2 with ht
  have hsplit : ∑ b : Fin r, (if (b : ℕ) < X.p0 then t b else 0)
      = ∑ a : Fin X.p0, t (Fin.castLE X.p0_le a) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_bij' (fun b hb => ⟨b, (Finset.mem_filter.mp hb).2⟩)
      (fun a _ => Fin.castLE X.p0_le a) (fun _ _ => Finset.mem_univ _)
      (fun a _ => by simp [Finset.mem_filter, a.isLt]) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl)
  have hsg : ∑ b : Fin r, sgn X.p0 b * t b
      = 2 * ∑ b : Fin r, (if (b : ℕ) < X.p0 then t b else 0) - ∑ b : Fin r, t b := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold sgn; split_ifs <;> ring
  unfold Data.maj
  rw [posPart_eq X τ e he x hflag hind u, self_pair X τ e he u]
  change 2 * ∑ a : Fin X.p0, t (Fin.castLE X.p0_le a) - ∑ b : Fin r, sgn X.p0 b * t b
    = ∑ b : Fin r, t b
  rw [hsg, hsplit]
  ring

end Pos

end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem tof_pack_card [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) (R : ℝ) (hR : 1 ≤ R)
    (F : Finset (Vsp X.dim)) (hF : ∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x)
    (hFR : ∀ y ∈ F, ‖u - y‖ ≤ R) : (F.card : ℝ) ≤ (3 * R) ^ Module.finrank ℝ (IR I) := by
  classical

  let K : Submodule ℝ (Vsp X.dim) := IR I
  let B := stdOrthonormalBasis ℝ K
  let φ : Vsp X.dim → EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) :=
    fun v => B.repr (K.orthogonalProjectionOnto (v - u))
  have hmem : ∀ y ∈ F, y - u ∈ K := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := hF y hy
    exact K.sub_mem (isU_uMap I x).1 hu
  have hpr : ∀ y (hy : y ∈ F), K.orthogonalProjectionOnto (y - u) = ⟨y - u, hmem y hy⟩ := fun y hy =>
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨y - u, hmem y hy⟩
  have hφ : ∀ y ∈ F, ∀ y' ∈ F, ‖φ y - φ y'‖ = ‖y - y'‖ := by
    intro y hy y' hy'
    show ‖B.repr (K.orthogonalProjectionOnto (y - u)) - B.repr (K.orthogonalProjectionOnto (y' - u))‖
      = ‖y - y'‖
    rw [hpr y hy, hpr y' hy', ← map_sub, LinearIsometryEquiv.norm_map]
    show ‖(y - u) - (y' - u)‖ = ‖y - y'‖
    congr 1
    abel
  have hinj : Set.InjOn φ F := by
    intro y hy y' hy' h
    have e := hφ y hy y' hy'
    rw [h, sub_self, norm_zero] at e
    exact sub_eq_zero.mp (norm_eq_zero.mp e.symm)
  have hcard : ((F.image φ).card : ℝ) ≤ (3 * R / 1) ^ Module.finrank ℝ K := by
    apply hP (Module.finrank ℝ K) (F.image φ) 1 R one_pos hR
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      show ‖B.repr (K.orthogonalProjectionOnto (y - u))‖ ≤ R
      rw [hpr y hy, LinearIsometryEquiv.norm_map]
      show ‖y - u‖ ≤ R
      rw [norm_sub_rev]
      exact hFR y hy
    · intro z hz z' hz' hne
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
      rw [dist_eq_norm, hφ y hy y' hy']
      have hyy : y ≠ y' := fun h => hne (by rw [h])
      obtain ⟨x, hx, rfl⟩ := hF y hy
      obtain ⟨x', hx', rfl⟩ := hF y' hy'
      exact tof_uMap_sep P hI hx hx' hyy
  rw [Finset.card_image_of_injOn hinj, div_one] at hcard
  exact hcard

theorem tof_exists_nearest [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) :
    ∃ y0 ∈ X.L, ∀ x ∈ X.L, ‖u - uMap I y0‖ ≤ ‖u - uMap I x‖ := by
  classical

  let S : Set (Vsp X.dim) := {y | (∃ x ∈ X.L, y = uMap I x) ∧ ‖u - y‖ ≤ ‖u‖}
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (Nat.ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I)) + 1)
    have hb := tof_pack_card P hI hP u hu (‖u‖ + 1) (by linarith [norm_nonneg u]) t
      (fun y hy => (ht (Finset.mem_coe.2 hy)).1)
      (fun y hy => le_trans (ht (Finset.mem_coe.2 hy)).2 (by linarith))
    rw [hcard] at hb
    push_cast at hb
    have hc := Nat.le_ceil ((3 * (‖u‖ + 1)) ^ Module.finrank ℝ (IR I))
    linarith
  have h0 : (0 : Vsp X.dim) ∈ S :=
    ⟨⟨0, X.L.zero_mem, (map_zero (uMap I)).symm⟩, by rw [sub_zero]⟩
  obtain ⟨y, hyS, hmin⟩ :=
    hfin.toFinset.exists_min_image (fun y => ‖u - y‖) ⟨0, hfin.mem_toFinset.2 h0⟩
  obtain ⟨⟨y0, hy0, rfl⟩, hyu⟩ := hfin.mem_toFinset.1 hyS
  refine ⟨y0, hy0, fun x hx => ?_⟩
  by_cases hxs : ‖u - uMap I x‖ ≤ ‖u‖
  · exact hmin _ (hfin.mem_toFinset.2 ⟨⟨x, hx, rfl⟩, hxs⟩)
  · push_neg at hxs
    linarith

theorem tof_gauss_min_sum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) :
    ∃ y0 ∈ X.L, ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2) ≤
        2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m *
          Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) := by
  obtain ⟨y0, hy0, hmin⟩ := tof_exists_nearest P hI hP u hu
  refine ⟨y0, hy0, fun F hF => ?_⟩
  have hsum := tof_sep_sum P hI hP u hu F hF
  have hc0 : 0 ≤ ‖u - uMap I y0‖ := norm_nonneg _

  have hterm : ∀ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2) ≤
      Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
        Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hF y hy
    have h1 : ‖u - uMap I y0‖ ≤ ‖u - uMap I x‖ := hmin x hx
    have h2 : ‖u - uMap I y0‖ ^ 2 ≤ ‖u - uMap I x‖ ^ 2 := by
      nlinarith [mul_self_le_mul_self hc0 h1]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]
  calc ∑ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2)
      ≤ ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
          Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) := Finset.sum_le_sum hterm
    _ = Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
          ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) *
          (2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = 2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m *
          Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) := by ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

open NumberField.InfinitePlace Classical in
lemma emb_comb [IsCMField E] (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ τ : E →+* ℂ,
      ∑ i, (r i : ℂ) * τ (RingOfIntegers.basis E i : E) =
        if τ = σ then c else if τ = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c else 0 := by
  classical
  have hne := ne_conj σ
  have hcx : ∀ τ : E →+* ℂ, (mk τ).IsComplex := fun τ => IsTotallyComplex.isComplex _
  let wc : {w : InfinitePlace E // w.IsComplex} := ⟨mk σ, hcx σ⟩
  let c' : ℂ := if (mk σ).embedding = σ then c else (starRingEnd ℂ) c
  let y : mixedEmbedding.mixedSpace E := (0, Pi.single wc c')
  let B := mixedEmbedding.latticeBasis E
  refine ⟨fun i => B.repr y i, fun τ => ?_⟩
  have hsum := B.sum_repr y

  have hcoord : ∑ i, (B.repr y i : ℂ) * (mk τ).embedding (RingOfIntegers.basis E i : E) =
      y.2 ⟨mk τ, hcx τ⟩ := by
    conv_rhs => rw [← hsum]
    rw [Prod.snd_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [B, Prod.smul_snd, Pi.smul_apply, mixedEmbedding.latticeBasis_apply,
      mixedEmbedding.mixedEmbedding_apply_isComplex, integralBasis_apply, Complex.real_smul]
  have hy : y.2 ⟨mk τ, hcx τ⟩ = if mk τ = mk σ then c' else 0 := by
    simp only [y]
    by_cases h : mk τ = mk σ
    · rw [if_pos h]
      have : (⟨mk τ, hcx τ⟩ : {w : InfinitePlace E // w.IsComplex}) = wc := Subtype.ext h
      rw [this, Pi.single_eq_same]
    · rw [if_neg h, Pi.single_eq_of_ne]
      intro h'; exact h (congrArg Subtype.val h')
  have hemb := embedding_mk_eq τ

  have hval : ∑ i, (B.repr y i : ℂ) * τ (RingOfIntegers.basis E i : E) =
      if (mk τ).embedding = τ then (if mk τ = mk σ then c' else 0)
      else (starRingEnd ℂ) (if mk τ = mk σ then c' else 0) := by
    rcases hemb with h | h
    · rw [if_pos h, ← hy, ← hcoord, h]
    · by_cases h' : (mk τ).embedding = τ
      · rw [if_pos h', ← hy, ← hcoord, h']
      · rw [if_neg h', ← hy, ← hcoord, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h, map_mul, Complex.conj_ofReal, ComplexEmbedding.conjugate_coe_eq]
        simp
  rw [hval]
  by_cases hτ : τ = σ
  · subst hτ
    simp only [if_true, c']
    split_ifs with h1 <;> simp
  · by_cases hτ' : τ = ComplexEmbedding.conjugate σ
    · subst hτ'
      have hm : mk (ComplexEmbedding.conjugate σ) = mk σ := mk_conjugate_eq σ
      simp only [if_neg hτ, if_true, hm, c']
      rcases embedding_mk_eq σ with h | h
      · have : (mk σ).embedding ≠ ComplexEmbedding.conjugate σ := by rw [h]; exact hne.symm
        simp [h, hm, this, hne, hne.symm]
      · simp [h, hm, hne, hne.symm]
    · have hm : mk τ ≠ mk σ := by
        intro h; rcases mk_eq_iff.mp h with h | h
        · exact hτ h
        · exact hτ' (by rw [← h]; exact (ComplexEmbedding.involutive_conjugate (K := E) τ).symm)
      simp [hτ, hτ', hm]


open Classical in
lemma Mc_comb [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ v : Vsp dim,
      Mc σ c v = ∑ i, r i • act (RingOfIntegers.basis E i) v := by
  classical
  obtain ⟨r, hr⟩ := emb_comb σ c
  refine ⟨r, fun v => ?_⟩
  ext j
  rw [Mc_apply, WithLp.ofLp_sum, Finset.sum_apply]
  have := hr j.1
  simp only [PiLp.smul_apply, act_apply, Complex.real_smul]
  rw [show (∑ i, (r i : ℂ) * (j.1 (RingOfIntegers.basis E i : E) * v j)) =
    (∑ i, (r i : ℂ) * j.1 (RingOfIntegers.basis E i : E)) * v j by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring, this]
  split_ifs <;> simp

lemma Mc_mem [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (S : Submodule ℝ (Vsp dim))
    (hS : ∀ (α : 𝓞 E) v, v ∈ S → act α v ∈ S) (c : ℂ) {v : Vsp dim} (hv : v ∈ S) :
    Mc σ c v ∈ S := by
  obtain ⟨r, hr⟩ := Mc_comb (dim := dim) σ c
  rw [hr]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hS _ _ hv)

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

section

theorem ReciprocityTheory.ChartRestriction.G.I2.thetaBasis_holds : ReciprocityTheory.ChartRestriction.G.I2.NStatement :=
  ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.nstatement_of ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepT ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepI ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepF ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepP ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepPos ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepDual ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepK
    ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepD
end
