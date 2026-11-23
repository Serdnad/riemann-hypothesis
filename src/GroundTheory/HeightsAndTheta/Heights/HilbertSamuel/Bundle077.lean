module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUpperNormalisation
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace IsomInvariance

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_ratSection {P : Ideal (MRing ι)} (hP : P.IsPrime) (hrel : IsRelevant P) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    ∃ s t : MRing ι, IsRatSectionOn P B s t := by
  classical
  let c : ∀ k, ι k := fun k => (hrel k).choose
  have hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P := fun k => (hrel k).choose_spec
  exact ⟨_, _, fun k => (B.a k).toNat, fun k => (-B.a k).toNat, Inter.AvoidRing.isMultiHomog_coordProd c _,
    Inter.AvoidRing.isMultiHomog_coordProd c _, Inter.AvoidRing.coordProd_not_mem hP c hc _,
    Inter.AvoidRing.coordProd_not_mem hP c hc _, fun k => Int.toNat_sub_toNat_neg _⟩

theorem snoc_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {m : ℕ} (N : Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (hP : IsArithVar P (m + 1)) (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAB : IsIsometricOn P A B) : I P (m + 1) (Fin.snoc N A) = I P (m + 1) (Fin.snoc N B) := by
  obtain ⟨f, g, α, β, hf, hg, hfP, hgP, hdeg, hdiv, hnorm⟩ := hAB
  have hPp : P.IsPrime := hP.2.1.1
  have nm : ∀ {x y : MRing ι}, x ∉ P → y ∉ P → x * y ∉ P := fun hx hy h => (hPp.mem_or_mem h).elim hx hy
  obtain ⟨s, t, σ, τ, hs, ht, hsP, htP, hst⟩ := exists_ratSection hPp hP.2.1.2.2 B
  have hB' : IsRatSectionOn P B (s * g) (t * g) :=
    ⟨σ + β, τ + β, Inter.AvoidRing.isMultiHomog_mul hs hg, Inter.AvoidRing.isMultiHomog_mul ht hg,
      nm hsP hgP, nm htP hgP, fun k => by have := hst k; simp only [Pi.add_apply]; push_cast; linarith⟩
  have hA' : IsRatSectionOn P A (s * f * g) (t * g * g) :=
    ⟨σ + α + β, τ + β + β,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hs hf) hg,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul ht hg) hg,
      nm (nm hsP hfP) hgP, nm (nm htP hgP) hgP,
      fun k => by have := hst k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith⟩
  rw [hR K ι I hI P m N A _ _ hP hN hA hA', hR K ι I hI P m N B _ _ hP hN hB hB']
  unfold recRRat
  have hfg : cycR I P N f = cycR I P N g := by
    rw [Inter.cycR_eq_sum, Inter.cycR_eq_sum, hdiv]
  have hint : ptsIntegral P (pot N) (logNormRat A (s * f * g) (t * g * g)) =
      ptsIntegral P (pot N) (logNormRat B (s * g) (t * g)) := by
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun _ _ _ => rfl) fun z hz => ?_
    unfold logNormRat
    congr 1
    have ha := A.pos z hz.1
    have hb := B.pos z hz.1
    have hn := hnorm z hz
    simp only [map_mul, norm_mul] at hn ⊢
    set S := ‖eval z (map (Int.castRingHom ℂ) s)‖
    set T := ‖eval z (map (Int.castRingHom ℂ) t)‖
    set F := ‖eval z (map (Int.castRingHom ℂ) f)‖
    set G := ‖eval z (map (Int.castRingHom ℂ) g)‖
    rcases eq_or_ne T 0 with hT | hT
    · simp [hT]
    rcases eq_or_ne G 0 with hG | hG
    · simp [hG]
    rw [div_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S * G * G * T) * hn
  rw [Inter.cycR_mul I hPp N (nm hsP hfP) hgP, Inter.cycR_mul I hPp N hsP hfP,
    Inter.cycR_mul I hPp N (nm htP hgP) hgP, Inter.cycR_mul I hPp N htP hgP,
    Inter.cycR_mul I hPp N hsP hgP, hint, hfg]
  ring

theorem update_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (j : Fin n)
    (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hP : IsArithVar P n) (hL : ∀ i, IsSmoothHerm (L i)) (hB : IsSmoothHerm B)
    (hLB : IsIsometricOn P (L j) B) : I P n L = I P n (Function.update L j B) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2))
  have hL' : ∀ i, IsSmoothHerm (Function.update L j B i) := fun i => by
    by_cases hi : i = j
    · subst hi; simpa using hB
    · simpa [Function.update_of_ne hi] using hL i
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let N : Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun i => L (σ i.castSucc)
  have hne : ∀ i : Fin m, σ i.castSucc ≠ j := fun i h => by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact Fin.castSucc_ne_last i h
  have e1 : L ∘ σ = Fin.snoc N (L j) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N]
  have e2 : Function.update L j B ∘ σ = Fin.snoc N B := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N, Function.update_of_ne (hne i)]
  rw [← hI.1 P _ L σ hP hL, ← hI.1 P _ _ σ hP hL', e1, e2]
  exact snoc_eq hR hI N (L j) B hP (fun i => hL _) (hL j) hB hLB

end IsomInvariance

theorem IsomInvariance.proof (hR : Inter.RatR.Statement) : IsomInvariance.Statement := by
  classical
  intro K _ ι _ I hI P n L L' hP hL hL' hiso
  let M : Finset (Fin n) → Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun S j => if j ∈ S then L' j else L j
  have hM : ∀ S j, IsSmoothHerm (M S j) := fun S j => by
    by_cases h : j ∈ S
    · simpa [M, h] using hL' j
    · simpa [M, h] using hL j
  have key : ∀ S : Finset (Fin n), I P n L = I P n (M S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [M]
    | insert a S ha ih =>
      have e : M (insert a S) = Function.update (M S) a (L' a) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [M]
        · simp [M, hj]
      have hMa : M S a = L a := by simp [M, ha]
      rw [ih, e]
      exact IsomInvariance.update_eq hR hI (M S) a (L' a) hP (hM S) (hL' a) (hMa ▸ hiso a)
  have hU : M Finset.univ = L' := by funext j; simp [M]
  rw [key Finset.univ, hU]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

namespace CoordArithOfFnField

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ratioField_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    CoordinateConeArithVar.ratioField y c = blockFnField y := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, q, hpq, rfl⟩
    have hp : y p / y ⟨p.1, c p.1⟩ ∈ CoordinateConeArithVar.ratioField y c :=
      IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨q.1, c q.1⟩ ∈ CoordinateConeArithVar.ratioField y c :=
      IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    have he : y p / y q = (y p / y ⟨p.1, c p.1⟩) / (y q / y ⟨q.1, c q.1⟩) := by
      rw [← hpq, div_div_div_cancel_right₀ (hc p.1)]
    rw [he]
    exact div_mem hp hq

theorem dim_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (blockFnField y)).toENat + Fintype.card K + 1 : ℕ∞) : WithBot ℕ∞) := by
  have hhor : IsHorizontal (mCoordIdeal y) := horizontal y
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have htr := ConeTrdeg.proof K ι (CoordinateConeArithVar.ratioField y c) (ratioPtL y c) (birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [mCoordIdeal_ratioPtL y c hc, ratioField_eq y c hc] at htr
  have hA := IntDomainDim.proof (MRing ι ⧸ mCoordIdeal y)
    (CoordinateConeArithVar.algebraMap_injective _ hhor)
  rw [hA, htr]
  simp only [map_add (f := _), map_natCast]


omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem nonzero_of_relevant (y : (Σ k, ι k) → Ω) (h : IsRelevant (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using h
  refine ⟨c, fun k h0 ↦ hc k ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

end CoordArithOfFnField


open CoordArithOfFnField in
theorem CoordArithOfFnField.proof : CoordArithOfFnField.Statement := by
  intro K _ ι _ K' _ ι' _ Ω _ _ y y' d hK' hy' hF hA
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := nonzero_of_relevant y hrel
  choose c' hc' using hy'
  refine ⟨hK', ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y', relevant y' c' hc'⟩, horizontal y', ?_⟩
  rw [dim_eq y c hc, hF] at hdim
  rw [dim_eq y' c' hc']
  generalize (Algebra.trdeg ℤ (blockFnField y')).toENat = e at hdim ⊢
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    simp only [top_add] at hdim
    norm_cast at hdim
  | coe n =>
    norm_cast at hdim ⊢
    omega

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace SecEqProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


variable (ι) in
abbrev Mono (a : K → ℕ) : Type := {μ : (Σ k, ι k) → ℕ // ∀ k, ∑ i, μ ⟨k, i⟩ = a k}

theorem Mono.le {a : K → ℕ} (μ : Mono ι a) (p : Σ k, ι k) : μ.1 p ≤ a p.1 := by
  obtain ⟨k, i⟩ := p
  rw [← μ.2 k]
  exact Finset.single_le_sum (f := fun i => μ.1 ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

instance (a : K → ℕ) : Finite (Mono ι a) :=
  Finite.of_injective
    (fun μ : Mono ι a => fun p => (⟨μ.1 p, Nat.lt_succ_of_le (μ.le p)⟩ : Fin (a p.1 + 1)))
    fun _ _ h => Subtype.ext (funext fun p => congrArg Fin.val (congrFun h p))

def monVal (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) → ℕ) : Ω := ∏ p, y p ^ μ p

def monPoly (μ : (Σ k, ι k) → ℕ) : MRing ι := monomial (Finsupp.equivFunOnFinite.symm μ) 1

theorem aeval_monPoly (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) → ℕ) : aeval y (monPoly μ) = monVal y μ := by
  rw [monPoly, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

theorem homog_monPoly {a : K → ℕ} (μ : Mono ι a) : IsMultiHomog (monPoly μ.1) a := by
  intro m hm k
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  subst this
  simpa using μ.2 k

theorem homog_prod {J : Type} (s : Finset J) (f : J → MRing ι) (d : J → K → ℕ)
    (h : ∀ j ∈ s, IsMultiHomog (f j) (d j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SectionBounded.homog_one (ι := ι)
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact SectionBounded.homog_mul (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem homog_bind₁ {a : K → ℕ} {N : ℕ} (φ : Fin (N + 1) → MRing ι) (hφ : ∀ j, IsMultiHomog (φ j) a)
    {f : MvPolynomial (Fin (N + 1)) ℤ} {n : ℕ} (hf : f.IsHomogeneous n) :
    IsMultiHomog (bind₁ φ f) (fun k => n * a k) := by

  rw [f.as_sum, map_sum]
  refine SectionBounded.homog_sum _ fun m hm => ?_
  rw [bind₁_monomial]
  refine SectionBounded.homog_congr (SectionBounded.homog_mul (SectionBounded.homog_C _)
    (homog_prod _ _ _ fun j _ => SectionBounded.homog_pow (hφ j) (m j))) fun k => ?_
  have hdeg : ∑ j ∈ m.support, m j = n := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [← hdeg, Finset.sum_mul]
  simp [Finset.sum_apply]

variable [DecidableEq K] [∀ k, DecidableEq (ι k)]

def swap (μ : (Σ k, ι k) → ℕ) (q p : Σ k, ι k) : (Σ k, ι k) → ℕ :=
  fun r => μ r + (if p = r then 1 else 0) - (if q = r then 1 else 0)

theorem sum_boole_block (k : K) (i₀ : ι k) (k' : K) :
    ∑ i : ι k', (if (⟨k, i₀⟩ : Σ k, ι k) = ⟨k', i⟩ then 1 else 0) = if k = k' then 1 else 0 := by
  by_cases h : k = k'
  · subst h; simp
  · simp [h]

theorem swap_mem {a : K → ℕ} (μ : Mono ι a) (k : K) (i₀ i : ι k) (h : μ.1 ⟨k, i₀⟩ ≠ 0) (k' : K) :
    ∑ i', swap μ.1 ⟨k, i₀⟩ ⟨k, i⟩ ⟨k', i'⟩ = a k' := by
  unfold swap
  rw [Finset.sum_tsub_distrib, Finset.sum_add_distrib, μ.2 k', sum_boole_block, sum_boole_block,
    Nat.add_sub_cancel]
  intro i' _
  by_cases hq : (⟨k, i₀⟩ : Σ k, ι k) = ⟨k', i'⟩
  · cases hq
    rw [if_pos rfl]
    omega
  · rw [if_neg hq]
    exact Nat.zero_le _

theorem monVal_swap (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) → ℕ) (q p : Σ k, ι k) (h : μ q ≠ 0) :
    monVal y (swap μ q p) * y q = monVal y μ * y p := by
  have hq : ∏ r, y r ^ (if q = r then 1 else 0) = y q := by simp
  have hp : ∏ r, y r ^ (if p = r then 1 else 0) = y p := by simp
  rw [← hq, ← hp, monVal, monVal, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← pow_add, ← pow_add, swap, Nat.sub_add_cancel]
  by_cases h1 : q = r
  · subst h1
    rw [if_pos rfl]
    omega
  · rw [if_neg h1]
    exact Nat.zero_le _

def pure (c : ∀ k, ι k) (a : K → ℕ) : Mono ι a :=
  ⟨fun r => if c r.1 = r.2 then a r.1 else 0, fun k => by simp⟩

theorem monVal_pure (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℕ) :
    monVal y (pure c a).1 = ∏ k, y ⟨k, c k⟩ ^ a k := by
  rw [monVal, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [pure, pow_ite]

def svPt (y : (Σ k, ι k) → Ω) {a : K → ℕ} {N : ℕ} (e : Mono ι a ≃ Fin (N + 1)) : Fin (N + 1) → Ω :=
  fun j => monVal y (e.symm j).1

theorem chartLat_le_secs (y : (Σ k, ι k) → Ω) {a : K → ℕ} (ha : ∀ k, 1 ≤ a k) {N : ℕ}
    (e : Mono ι a ≃ Fin (N + 1)) (τ : ℕ) {s : Ω} (hs : s ∈ chartLat y (fun k => (a k : ℤ)) τ) :
    s ∈ (Kleiman.twistSys ℤ (svPt y e) (τ : ℤ)).secs := by
  rw [Kleiman.SubSystem.secs, Submodule.mem_iInf]
  intro I
  obtain ⟨j, hj⟩ := I.2.1
  have hzj : monVal y (e.symm j).1 ≠ 0 := (Kleiman.mem_support (svPt y e)).mp (I.2.2 hj)
  have hex : ∀ k, ∃ i, (e.symm j).1 ⟨k, i⟩ ≠ 0 := fun k => by
    have h0 : ∑ i, (e.symm j).1 ⟨k, i⟩ ≠ 0 := by rw [(e.symm j).2 k]; exact Nat.one_le_iff_ne_zero.mp (ha k)
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    exact ⟨i, hi⟩
  choose c hc using hex
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 =>
    hzj (Finset.prod_eq_zero (Finset.mem_univ ⟨k, c k⟩) (by rw [h0, zero_pow (hc k)]))
  have hle : chartRingZ y c ≤ Kleiman.chartRing ℤ (svPt y e) I := by
    rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine ⟨X (e ⟨swap (e.symm j).1 ⟨k, c k⟩ ⟨k, i⟩, swap_mem (e.symm j) k (c k) i (hc k)⟩), X j, 1,
      Kleiman.X_mem_monos hj, isHomogeneous_X _ _, isHomogeneous_X _ _, ?_⟩
    simp only [aeval_X, svPt, Equiv.symm_apply_apply]
    rw [div_eq_div_iff (hyc k) hzj, monVal_swap y _ _ _ (hc k), mul_comm]
  have hj0 : svPt y e (e (pure c a)) ^ τ ∈ Kleiman.twistMod ℤ (svPt y e) (τ : ℤ) I :=
    Submodule.subset_span ⟨X (e (pure c a)) ^ τ, 1, 0, τ, one_mem _, isHomogeneous_X_pow _ _,
      isHomogeneous_one _ _, by simp, by simp⟩
  have hmem := Submodule.smul_mem _ (⟨_, hle (hs c hyc)⟩ : Kleiman.chartRing ℤ (svPt y e) I) hj0
  rw [Submodule.restrictScalars_mem]
  change s ∈ Kleiman.twistMod ℤ (svPt y e) (τ : ℤ) I
  convert hmem using 1
  change s = (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ)))) * _
  rw [svPt, Equiv.symm_apply_apply, monVal_pure, ← Finset.prod_pow, mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one, mul_one]
  intro k _
  rw [← pow_mul, zpow_neg, show (τ : ℤ) * (a k : ℤ) = ((a k * τ : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ (hyc k))]

theorem piece_le_secM (y : (Σ k, ι k) → Ω) {a : K → ℕ} {N : ℕ} (e : Mono ι a ≃ Fin (N + 1)) (τ : ℕ) {s : Ω}
    (hs : s ∈ (Kleiman.coordGraded ℤ (svPt y e)).piece (τ : ℤ)) : s ∈ secM y (fun k => τ * a k) := by
  have hle : (Kleiman.coordGraded ℤ (svPt y e)).piece (τ : ℤ) ≤
      Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g (fun k => τ * a k) ∧ aeval y g = s} := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, n, hf, hn, rfl⟩
    obtain rfl : n = τ := by exact_mod_cast hn
    refine Submodule.subset_span ⟨bind₁ (fun j => monPoly (e.symm j).1) f,
      homog_bind₁ _ (fun j => homog_monPoly (e.symm j)) hf, ?_⟩
    rw [aeval_bind₁]
    simp only [aeval_monPoly]
    rfl
  exact hle hs

end SecEqProof


open SecEqProof in
theorem SecEq.proof : SecEq.Statement := by
  intro K _ ι _ Ω _ y a ha hy
  classical
  choose c hc using hy
  obtain ⟨N, ⟨e⟩⟩ : ∃ N, Nonempty (Mono ι a ≃ Fin (N + 1)) := by
    have : Nonempty (Mono ι a) := ⟨pure c a⟩
    exact ⟨Nat.card (Mono ι a) - 1,
      ⟨(Finite.equivFin _).trans (finCongr (Nat.sub_add_cancel Nat.card_pos).symm)⟩⟩
  have hz : svPt y e ≠ 0 := fun h => by
    have h1 := congrFun h (e (pure c a))
    simp only [svPt, Equiv.symm_apply_apply, monVal_pure, Pi.zero_apply] at h1
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hc k)) h1
  obtain ⟨τ₀, hτ₀⟩ := Filter.eventually_atTop.mp (Kleiman.TwistSections.full ℤ Ω N (svPt y e) hz)
  refine ⟨τ₀, fun τ hτ => le_antisymm (fun s hs => ?_)
    (UpperNormalisation.secM_le_chartLat y _ τ fun k => by push_cast; ring)⟩
  exact piece_le_secM y e τ ((hτ₀ τ hτ) ▸ chartLat_le_secs y ha e τ hs)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (m N : ℕ) (v : Fin N → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, v j ∈ chartLat y a m) →
    KH.GeneratesOn y (fun k => (m : ℤ) * a k) v → IsArithVar (mCoordIdeal (addBlock y v)) (D + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
