module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle015
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Subring (funField P) where
  carrier := {x | ∀ W, IsClosedPt W → P ≤ W → (x : FractionRing (MRing ι ⧸ P)) ∈ locRing P W}
  mul_mem' ha hb W h1 h2 := mul_mem (ha W h1 h2) (hb W h1 h2)
  one_mem' _ _ _ := one_mem _
  add_mem' ha hb W h1 h2 := add_mem (ha W h1 h2) (hb W h1 h2)
  zero_mem' _ _ _ := zero_mem _
  neg_mem' ha W h1 h2 := neg_mem (ha W h1 h2)

def RegularityOrder.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → Module.Free ℤ (regRing P) ∧ Module.Finite ℤ (regRing P) ∧
      ∀ hF : IsField (funField P), letI := hF.toField; ∀ [NumberField (funField P)],
        Module.finrank ℤ (regRing P) = Module.finrank ℚ (funField P)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFFibreMult.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d e : ℕ)
    (G : GenFibre v P') (s : MRing ι') (W : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' e → IsArithVar (imageZ v P') d →
    W ∈ divSupp P' s → IsHorizontal W → imageZ v W = imageZ v P' →
    multAt (fibreIdeal κ G ⊔ Ideal.span {baseSubst κ G s}) (fibreOf κ G W) = multAt (P' ⊔ Ideal.span {s}) W

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section


open Classical in
def PFFibreSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (N : Fin (r + 1) → HermLine ι') (s : MRing ι') (a : K' → ℕ),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ k, (N (Fin.last r)).a k = a k) → IsMultiHomog s a → s ∉ P' →
    ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) *
        (if IsHorizontal W ∧ imageZ v W = imageZ v P' then
          (J (fibreOf κ G W) r (fun j => fibreDeg κ (N (Fin.castSucc j)).a) : ℝ) else 0) =
      (J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) : ℝ)

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ArithmeticIntersectionHorizontal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem isHorizontal_imageZ {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (h : IsHorizontal W') :
    IsHorizontal (imageZ v W') := by
  have h' : W'.comap (C : ℤ →+* MRing ι') = ⊥ := h
  show (imageZ v W').comap (C : ℤ →+* MRing ι) = ⊥
  rw [← h']
  ext c
  simp [imageZ, Ideal.mem_comap]

theorem dim_eq {P : Ideal (MRing ι)} {d d' : ℕ} (h : IsArithVar P d) (h' : IsArithVar P d') : d = d' := by
  have e := h.2.2.2.symm.trans h'.2.2.2
  have e2 : d + Fintype.card K = d' + Fintype.card K := by exact_mod_cast e
  omega

theorem dim_add_one_le {R : Type*} [CommRing R] {Q Q₂ : Ideal R} [Q.IsPrime] (hle : Q ≤ Q₂)
    {x : R} (hx : x ∈ Q₂) (hxQ : x ∉ Q) : ringKrullDim (R ⧸ Q₂) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))
  intro y hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul]
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isRelevant_of_le {Y Z : Ideal (MRing ι)} (hZ : IsRelevant Z) (hY : Y ≤ Z) : IsRelevant Y :=
  fun k => let ⟨i, hi⟩ := hZ k; ⟨i, fun h => hi (hY h)⟩

theorem mem_minimalPrimes {J Q : Ideal (MRing ι)} {n : ℕ} (hQ : IsArithVar Q n) (hJQ : J ≤ Q)
    (hdim : ∀ M ∈ J.minimalPrimes, IsRelevant M → IsHorizontal M → IsArithVar M n) :
    Q ∈ J.minimalPrimes := by
  have hQp : Q.IsPrime := hQ.2.1.1
  refine ⟨⟨hQp, hJQ⟩, fun q hq hqQ => ?_⟩
  have : q.IsPrime := hq.1
  obtain ⟨M, hM, hMq⟩ := Ideal.exists_minimalPrimes_le hq.2
  have hMQ : M ≤ Q := hMq.trans hqQ
  have hQh : Q.comap (C : ℤ →+* MRing ι) = ⊥ := hQ.2.2.1
  have hMh : IsHorizontal M := by
    show M.comap (C : ℤ →+* MRing ι) = ⊥
    rw [eq_bot_iff, ← hQh]
    exact Ideal.comap_mono hMQ
  have hMn := hdim M hM (isRelevant_of_le hQ.2.1.2.2 hMQ) hMh
  have : M.IsPrime := hM.1.1
  refine le_trans ?_ hMq
  by_contra hQM
  obtain ⟨x, hxQ, hxM⟩ := Set.not_subset.1 hQM
  have h := dim_add_one_le hMQ hxQ hxM
  rw [hQ.2.2.2, hMn.2.2.2] at h
  have h2 : n + Fintype.card K + 1 ≤ n + Fintype.card K := by exact_mod_cast h
  omega


open Classical in
theorem sum_block (F : (Σ k', ι' k') → ℕ) (k' : K') :
    ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single k']
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {s : MRing ι} {α : K → ℕ} (hs : IsMultiHomog s α) :
    IsMultiHomog (rename v s) (Function.extend κ α 0) := by
  classical
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1, Finset.mem_image] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  rw [sum_block]
  have h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) =
      ∑ p, if κ p.1 = k' then m p else 0 := by
    have := Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0)
      (s := m) hv.2.1
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [hv.2.2.1] using this
  have h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then α k else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hs m hm k
    · simp
  convert h1.trans h2
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hv.1.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hv.1.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg fun hk => h ⟨k, hk⟩]

end ArithmeticIntersectionHorizontal


open ArithmeticIntersectionHorizontal in
theorem ArithmeticIntersectionHorizontal.proof (hDiv : DivSuppArithStatement) (hIm : ImageArithStatement)
    (hP0 : GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.Statement) : ArithmeticIntersectionHorizontal.Statement := by
  intro I hI n hn K _ ι _ K' _ ι' _ κ v P' L L' s α W' hv hP' hP hL hLL' hs hsP hW' hh
  classical

  let A : HermLine ι := HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) (fun k => (α k : ℤ))
  let A' : HermLine ι' :=
    HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι' k)) (fun k => ((Function.extend κ α 0 : K' → ℕ) k : ℤ))
  have hsec : IsSectionOn (imageZ v P') A s := ⟨α, fun _ => rfl, hs, hsP⟩
  have hsec' : IsSectionOn P' A' (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, fun h => hsP (Ideal.mem_comap.mpr h)⟩
  have hW'n : IsArithVar W' n := (hDiv K' ι' P' n A' (rename v s) W' hP' hsec' hW').1 hh
  have hhQ : IsHorizontal (imageZ v W') := isHorizontal_imageZ hh
  obtain ⟨d, hdn, hQd⟩ := hIm K ι K' ι' κ v W' n hP.1 hv hW'n
  rcases hdn.lt_or_eq with hlt | heq
  ·
    right
    refine ⟨fun hm => ?_, hP0 I hI K ι K' ι' κ v W' d n L L' hv hW'n hQd hlt hL hLL'⟩
    have := dim_eq hQd ((hDiv K ι (imageZ v P') n A s _ hP hsec hm).1 hhQ)
    omega
  ·
    left
    rw [heq] at hQd
    have hle := hW'.1.1.2
    have hm : imageZ v W' ∈ divSupp (imageZ v P') s := by
      refine ⟨mem_minimalPrimes hQd ?_ fun M hM hMr hMh => (hDiv K ι (imageZ v P') n A s M hP hsec ⟨hM, hMr⟩).1 hMh,
        hQd.2.1.2.2⟩
      refine sup_le (Ideal.comap_mono (le_sup_left.trans hle)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_comap.mpr (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact ⟨hm, fun G' J' hJ' => hn K ι K' ι' κ v W' G' J' L L' hv hW'n hQd hJ' hL hLL'⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace Conservation

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_const {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs <;> simp
  · simp


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem C_not_mem {P : Ideal (MRing ι)} (hP : IsHorizontal P) {a : ℤ} (ha : a ≠ 0) : C a ∉ P := by
  intro h
  have : a ∈ P.comap (C : ℤ →+* MRing ι) := Ideal.mem_comap.mpr h
  rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hP, Ideal.mem_bot] at this
  exact ha this


omit [Fintype K] in
theorem isMultiHomog_C (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem comap_eq_of_mem {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    W.comap (C : ℤ →+* MRing ι) = Ideal.span {(p : ℤ)} := by
  have hWp : W.IsPrime := hW.1.1.1
  have hpW : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
    Ideal.mem_comap.mpr (hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  exact (hmax.eq_of_le (Ideal.IsPrime.comap C).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hpW)).symm


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem not_horizontal {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    ¬ IsHorizontal W := by
  intro h
  have := comap_eq_of_mem hp hW
  rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from h, eq_comm, Ideal.span_singleton_eq_bot] at this
  exact hp.ne_zero (by exact_mod_cast this)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charOf_eq {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    charOf W = p := by
  have h := comap_eq_of_mem hp hW
  unfold charOf
  have hg : Ideal.span {Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))} =
      Ideal.span {(p : ℤ)} := by
    rw [← h]; exact Submodule.IsPrincipal.span_singleton_generator _
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at hg
  simpa using hg

theorem vertR_C_prime (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) {p : ℕ} (hp : p.Prime) :
    vertR P L (C (p : ℤ)) = Real.log p * ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
      (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (fun j => (L j).a) : ℝ) := by
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Set.Finite.mem_toFinset] at hV
  rw [if_neg (not_horizontal hp hV), charOf_eq hp hV]
  ring

end Conservation

theorem Conservation.statement_holds : Conservation.Statement := by
  unfold Conservation.Statement ConservationStatement
  intro K _ ι _ I hI P n L p hP hL hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hA : IsSmoothHerm (constLine (ι := ι) (-Real.log p)) := contDiffOn_const
  have ha : ∀ k, (constLine (ι := ι) (-Real.log p)).a k = ((0 : K → ℕ) k : ℤ) := fun _ => rfl
  have hpot : (fun j z => Real.log ((L j).h z)) = pot L := rfl
  constructor
  · rw [hI.2.2 P n L _ (C (p : ℤ)) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 (by exact_mod_cast hp.ne_zero))]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C (p : ℤ)) = fun _ => 0 := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C (p : ℤ)))‖ / Real.exp (-(-Real.log p))) = 0
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [hp0.ne']
    unfold recR vertR arInt
    rw [hlog, Conservation.ptsIntegral_const, zero_mul, sub_zero]
    refine finsum_mem_congr rfl fun W hW => ?_
    rw [if_neg (Conservation.not_horizontal hp hW), if_neg (Conservation.not_horizontal hp hW)]
  · rw [hI.2.2 P n L _ (C 1) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 one_ne_zero)]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C 1) = fun _ => -Real.log p := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C 1))‖ / Real.exp (-(-Real.log p))) = _
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [Real.log_inv]
    have hempty : divSupp P (C 1 : MRing ι) = ∅ := by
      ext W
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hW
      have hle := hW.1.1.2
      rw [C_1, Ideal.span_singleton_one, sup_top_eq, top_le_iff] at hle
      exact hW.1.1.1.ne_top hle
    unfold recR arInt
    rw [hempty, finsum_mem_empty, hlog, Conservation.ptsIntegral_const, hpot]
    ring

theorem Conservation.conservation_degree_form_of_existence (hE : ThmIExists.Statement) (hC : Conservation.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement := by
  intro K _ ι _ P n L p hP hL hp
  obtain ⟨I, hI⟩ := hE
  obtain ⟨h1, h2⟩ := hC K ι (I K ι) (hI K ι) P n L p hP hL hp
  have h := h1.symm.trans h2
  rw [Conservation.vertR_C_prime P L hp] at h
  exact mul_left_cancel₀ (Real.log_pos (by exact_mod_cast hp.one_lt)).ne' h

theorem Conservation.conservation_iff_degree_statement :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement ↔ DegreeStatement := by
  constructor
  · intro h K _ ι _ P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
    exact (h K ι P e L p hP hL hp).symm
  · intro h K _ ι _ P e L p hP hL hp
    have h' := h K ι P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at h'
    exact h'.symm

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem pfAt_zero (hAI3 : PushforwardArithIntersection.Statement) (I : AllFam) (hI : I.IsFamily) : PFAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' _
  have hN : (fun j => fibreDeg κ (N j).a) = (Fin.elim0 : Fin 0 → FibreBlock κ → ℤ) :=
    funext fun j => j.elim0
  have hA : Fin.append L' N = L' := funext fun j => by
    rw [Fin.append_right_nil L' N rfl]
    rfl
  rw [hN, hA]
  exact hAI3 I hI K ι K' ι' κ v P' d G J L L' hv hP' hP hJ hL hL'

theorem PushforwardProjLineFlag.proof (hAI3 : PushforwardArithIntersection.Statement) (hStep : PFStep.Statement) : PushforwardProjLineFlag.Statement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d r
  have key : ∀ r, PFAt I r := fun r =>
    Nat.rec (pfAt_zero hAI3 I hI) (fun r h => hStep I hI r h) r
  exact key r K ι K' ι' κ v P' d

end GroundTheory.Heights₂.Heights.Inter
end
