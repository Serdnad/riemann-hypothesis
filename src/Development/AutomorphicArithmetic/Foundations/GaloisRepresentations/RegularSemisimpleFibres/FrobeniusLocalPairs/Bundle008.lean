module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open ValuativeRel UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.Gal.InertialTypesAlt.L.normOpen :
    UpperTheory.Gal.InertialTypesAlt.L.NormOpen := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ r hr0 hr1
  have hc : Continuous (algebraMap k E) := (UpperTheory.V.Z.Tf.Orb.extCont_holds k E).1
  have hS : {z : E | valuation E (z - 1) < r} ∈ nhds (algebraMap k E 1) := by
    rw [map_one]
    exact (IsValuativeTopology.hasBasis_nhds' (1 : E)).mem_of_mem hr0.ne'
  obtain ⟨γ, hγ0, hγ⟩ :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_iff.mp (hc.continuousAt.preimage_mem_nhds hS)
  set d := Module.finrank k E with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hdk : (d : k) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  set δ := valuation k (d : k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ] using hdk
  have hδ1 : δ ≤ 1 := by
    rw [hδ]
    clear hδ hδ0 hdk hdpos hd
    induction d with
    | zero => simp
    | succ n ih =>
      push_cast
      exact ((valuation k).map_add _ _).trans (max_le ih (by simp))
  obtain ⟨t, ht0, ht1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  set ε := valuation k t with hεdef
  set μ := min γ δ
  have hμ0 : 0 < μ := lt_min (zero_lt_iff.mpr hγ0) (zero_lt_iff.mpr hδ0)
  have hε0 : 0 < ε := zero_lt_iff.mpr (by simpa [hεdef] using ht0)
  set r₂ := μ * ε
  have hr₂0 : 0 < r₂ := mul_pos hμ0 hε0
  have hr₂μ : r₂ < μ := by
    calc r₂ = μ * ε := rfl
      _ < μ * 1 := mul_lt_mul_of_pos_left ht1 hμ0
      _ = μ := mul_one μ
  have hr₂γ : r₂ < γ := hr₂μ.trans_le (min_le_left _ _)
  have hr₂δ : r₂ < δ := hr₂μ.trans_le (min_le_right _ _)
  have hr₀r₂ : r₂ * δ ≤ r₂ := by
    calc r₂ * δ ≤ r₂ * 1 := mul_le_mul_of_nonneg_left hδ1 zero_le'
      _ = r₂ := mul_one r₂
  refine ⟨r₂ * δ, mul_pos hr₂0 (zero_lt_iff.mpr hδ0), hr₀r₂.trans_lt (hr₂δ.trans_le hδ1), ?_⟩
  intro x hx
  have hmem : ∀ y : k, valuation k (y - 1) ≤ r₂ → valuation E (algebraMap k E y - 1) ≤ r := by
    intro y hy
    exact le_of_lt (hγ (lt_of_le_of_lt hy hr₂γ))
  refine ⟨hmem x (hx.trans hr₀r₂), ?_⟩
  have hg : Matrix.GeneralLinearGroup.scalar (Fin 1) x ∈ UpperTheory.ConvolutionTheory.Loc.ball 1 (r₂ * δ) := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa [Matrix.GeneralLinearGroup.scalar] using hx
  obtain ⟨u, ⟨hu, hud⟩, -⟩ := UpperTheory.ConvolutionTheory.Loc.rootEx k 1 d r₂ hr₂δ _ hg
  have hpow : ∀ (M : Matrix (Fin 1) (Fin 1) k) (m : ℕ), (M ^ m) 0 0 = (M 0 0) ^ m := by
    intro M m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, pow_succ]
  have hw : ((u : Matrix (Fin 1) (Fin 1) k) 0 0) ^ d = (x : k) := by
    have := congrArg (fun g : GL (Fin 1) k => (g : Matrix (Fin 1) (Fin 1) k) 0 0) hud
    simp only [Units.val_pow_eq_pow_val] at this
    rw [← hpow, this]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hw1 : valuation k ((u : Matrix (Fin 1) (Fin 1) k) 0 0 - 1) ≤ r₂ := by
    simpa using hu 0 0
  have hw0 : (u : Matrix (Fin 1) (Fin 1) k) 0 0 ≠ 0 := by
    intro h
    rw [h, zero_pow hdpos.ne'] at hw
    exact x.ne_zero hw.symm
  refine ⟨Units.mk0 (algebraMap k E ((u : Matrix (Fin 1) (Fin 1) k) 0 0))
    ((map_ne_zero (algebraMap k E)).mpr hw0), hmem _ hw1, ?_⟩
  rw [Units.val_mk0, Algebra.norm_algebraMap, ← hd, hw]
end

section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private theorem near_mul {r : ValueGroupWithZero E} (h1 : r < 1) {x y : E} (hx : valuation E (x - 1) ≤ r)
    (hy : valuation E (y - 1) ≤ r) : valuation E (x * y - 1) ≤ r := by
  have hx1 : valuation E x ≤ 1 := by
    have e : x = (x - 1) + 1 := by ring
    rw [e]
    exact (Valuation.map_add_le _ (hx.trans h1.le) (by simp))
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine Valuation.map_add_le _ ?_ hx
  rw [map_mul]
  exact (mul_le_mul' hx1 hy).trans (by simp)

private theorem near_prod {r : ValueGroupWithZero E} (h0 : 0 < r) (h1 : r < 1) {ι : Type} (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, valuation E (f i - 1) ≤ r) : valuation E (∏ i ∈ s, f i - 1) ≤ r := by
  induction s using Finset.induction_on with
  | empty => simpa using h0.le
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact near_mul h1 (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem small_prod {r : ValueGroupWithZero E} {ι : Type} (s : Finset ι) (f : ι → E) (hs : ∀ i ∈ s, valuation E (f i) ≤ 1)
    (a : ι) (ha : a ∈ s) (hr : valuation E (f a) ≤ r) : valuation E (∏ i ∈ s, f i) ≤ r := by
  rw [← Finset.mul_prod_erase s f ha, map_mul, map_prod]
  exact (mul_le_of_le_one_right' (Finset.prod_le_one' fun i hi => hs i (Finset.mem_of_mem_erase hi))).trans hr

private theorem det_near {r : ValueGroupWithZero E} (h0 : 0 < r) (h1 : r < 1) {M : Matrix (Fin n) (Fin n) E}
    (hM : ∀ i j, valuation E (M i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ r) : valuation E (M.det - 1) ≤ r := by
  have hb : ∀ i j, valuation E (M i j) ≤ 1 := fun i j => by
    have e : M i j = (M i j - (1 : Matrix (Fin n) (Fin n) E) i j) + (1 : Matrix (Fin n) (Fin n) E) i j := by ring
    rw [e]
    refine Valuation.map_add_le _ ((hM i j).trans h1.le) ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n))), add_sub_right_comm]
  refine Valuation.map_add_le _ ?_ (Valuation.map_sum_le _ fun p hp => ?_)
  · have hd : valuation E (∏ i, M i i - 1) ≤ r := near_prod h0 h1 _ _ fun i _ => by simpa using hM i i
    simpa using hd
  · have hp1 : p ≠ 1 := Finset.ne_of_mem_erase hp
    obtain ⟨a, ha⟩ : ∃ a, p a ≠ a := by
      by_contra hc
      push Not at hc
      exact hp1 (Equiv.ext hc)
    have hs : valuation E (∏ i, M (p i) i) ≤ r := by
      refine small_prod _ _ (fun i _ => hb _ _) a (Finset.mem_univ _) ?_
      simpa [Matrix.one_apply, ha] using hM (p a) a
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with e | e <;> simpa [e, Units.smul_def] using hs

end

private theorem diag_cont (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) :
    Continuous (diagT E (Fin n)) :=
  (continuous_leviEmb E (points (Fin n))).comp (continuous_leviTorus E (Fin n))

theorem elemTest : ElemTest := by
  intro E _ _ _ _ n r h0 h1 A hA
  obtain ⟨K, hK, hKo, hKc⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub E n r h0 h1
  haveI := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.1
  have mK : ∀ g : GL (Fin n) E, g ∈ ball n r ↔ g ∈ K := fun g => by rw [← hK]; rfl
  have e : elemSet r A = (fun z : GL (Fin n) E × (Fin n → Eˣ) × GL (Fin n) E => z.1 * diagT E (Fin n) z.2.1 * z.2.2) ''
      ((K : Set (GL (Fin n) E)) ×ˢ (A ×ˢ (K : Set (GL (Fin n) E)))) := by
    ext g
    constructor
    · rintro ⟨a, ha, b, hb, s, hs, rfl⟩
      exact ⟨(a, s, b), ⟨(mK a).1 ha, hs, (mK b).1 hb⟩, rfl⟩
    · rintro ⟨⟨a, s, b⟩, ⟨ha, hs, hb⟩, rfl⟩
      exact ⟨a, (mK a).2 ha, b, (mK b).2 hb, s, hs, rfl⟩
  have hS : IsCompact (elemSet r A) := by
    rw [e]
    refine (hKc.prod (hA.prod hKc)).image ?_
    exact (continuous_fst.mul ((diag_cont E n).comp (continuous_fst.comp continuous_snd))).mul
      (continuous_snd.comp continuous_snd)
  have hO : IsOpen (elemSet r A) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨a, ha, b, hb, s, hs, rfl⟩
    refine Filter.mem_of_superset ((hKo.preimage (f := fun g => (a * diagT E (Fin n) s)⁻¹ * g) (by fun_prop)).mem_nhds
      (by simpa [mul_assoc] using (mK b).1 hb)) fun g hg => ?_
    exact ⟨a, ha, _, (mK _).2 hg, s, hs, by group⟩
  have hT : UpperTheory.ConvolutionTheory.C.Test ((elemSet r A).indicator (1 : GL (Fin n) E → ℂ)) := by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_, HasCompactSupport.intro hS fun g hg => Set.indicator_of_notMem hg _⟩
    by_cases h : g ∈ elemSet r A
    · filter_upwards [hO.mem_nhds h] with y hy
      exact (Set.indicator_of_mem hy _).trans (Set.indicator_of_mem h (1 : GL (Fin n) E → ℂ)).symm
    · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds h] with y hy
      exact (Set.indicator_of_notMem hy _).trans (Set.indicator_of_notMem h _).symm
  refine ⟨hO, hS, hT, hT, ?_⟩
  rintro _ ⟨a, ha, b, hb, s, hs, rfl⟩
  have hd : ∀ g ∈ ball (E := E) n r, valuation E (((GeneralLinearGroup.det g : Eˣ) : E) - 1) ≤ r := fun g hg => by
    simpa [GeneralLinearGroup.val_det_apply] using det_near h0 h1 hg
  refine ⟨s, hs, GeneralLinearGroup.det a * GeneralLinearGroup.det b, ?_, ?_⟩
  · rw [Units.val_mul]
    exact near_mul h1 (hd a ha) (hd b hb)
  · have hdiag : GeneralLinearGroup.det (diagT E (Fin n) s) = ∏ i, s i := by
      ext
      simp [GeneralLinearGroup.val_det_apply, val_diagT, Matrix.det_diagonal]
    rw [map_mul, map_mul, hdiag]
    simp only [mul_comm, mul_left_comm, mul_assoc]

end UpperTheory.Gal.InertialTypesAlt.L
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem quot_smul {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) (c : ℂ) (F : G → ℂ) :
    quotIntegral μ H ν (fun g => c * F g) = c * quotIntegral μ H ν F := by
  unfold quotIntegral
  split_ifs
  · simp only [mul_assoc, integral_const_mul]
  · simp

private theorem quot_zero {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) (F : G → ℂ)
    (h : ∀ g, F g = 0) : quotIntegral μ H ν F = 0 := by
  have := quot_smul μ H ν 0 F
  rw [zero_mul] at this
  rw [← this]
  congr 1
  funext g
  rw [h, mul_zero]

private theorem alg {A : Type} [CommGroup A] (d a b u v t : A) : d * a / u / t = d * b / v / t * (b⁻¹ * a / (v⁻¹ * u)) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel


theorem elemLoc_of (hS : SuppE) (hO : OneField) (hR : Reps) (hN : NormOpen) (hD : NormDiag) (hA : Align) (hV : VolRatio)
    (hB : ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
      (r : ValueGroupWithZero E), 0 < r → r < 1 → ∃ K : Subgroup (GL (Fin n) E), (K : Set (GL (Fin n) E)) = ball n r ∧
        IsOpen (K : Set (GL (Fin n) E)) ∧ IsCompact (K : Set (GL (Fin n) E))) : ElemLoc := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n _ _ _ _ μE μk hE hk r hr0 hr1
  obtain ⟨r₀, h00, h01, hn⟩ := hN k E σ hσ r hr0 hr1
  refine ⟨r₀, h00, h01, fun r' hle h'0 => ⟨fun x hx => (hn x (hx.trans hle)).2, ?_⟩⟩
  have h'1 : r' < 1 := hle.trans_lt h01
  obtain ⟨hcyc, -, hbr⟩ := bridge k E σ
  obtain ⟨hsg, -, -, hcl, -⟩ := hbr n
  have hc1 : Cyc (RingEquiv.refl k) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  obtain ⟨R, hRne, hR1, hR2, hnear, hR3⟩ := hR E n σ _ hcyc r hr0 hr1
  obtain ⟨j, hj, hvol⟩ := hV k E σ hσ n r r' hr0 hr1 h'0 h'1 fun x hx => (hn x (hx.trans hle)).1
  obtain ⟨d1, d2, d3⟩ := hD k E σ hσ n
  obtain ⟨K, hK, hKo, hKc⟩ := hB E n r hr0 hr1
  obtain ⟨K', hK', hKo', hKc'⟩ := hB k n r' h'0 h'1
  obtain ⟨a1, a2, a3, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop E n
  have pE : 0 < μE.real (ball n r) := hK ▸ ENNReal.toReal_pos (hKo.measure_ne_zero μE ⟨1, one_mem _⟩) hKc.measure_ne_top
  have pk : 0 < μk.real (ball n r') := hK' ▸ ENNReal.toReal_pos (hKo'.measure_ne_zero μk ⟨1, one_mem _⟩) hKc'.measure_ne_top
  have pR : (0 : ℝ) < R.card := Nat.cast_pos.2 hRne.card_pos
  refine ⟨R.card * μE.real (ball n r) / (j * μk.real (ball n r')), by positivity, fun t ht => ?_⟩
  have hA1 : ∀ x ∈ ({t} : Set (Fin n → Eˣ)), Strict x := fun x hx => hx ▸ ht
  have hA2 := (d3 r hr1 t ht).1
  have key : ∀ x ∈ nrmSet k r t, ∀ s, Near r' s → x * s ∈ nrmSet k r t := by
    rintro _ ⟨u, hu, rfl⟩ s hs
    choose u' hu' hu'' using fun i => (hn (s i) ((hs i).trans hle)).2
    refine ⟨u * u', (hnear u u' hu hu').1, funext fun i => Units.ext ?_⟩
    simp only [nrmT, Pi.mul_apply, Units.val_mul, Units.coe_map, map_mul, hu'', mul_assoc]
  obtain ⟨-, -, -, -, hnear', -⟩ := hR k n _ _ hc1 r' h'0 h'1
  have meet' : ∀ γ g : GL (Fin n) k, g⁻¹ * γ * g ∈ elemSet r' (nrmSet k r t) →
      ∃ d : Fin n → Eˣ, Strict d ∧ IsNormOf σ (diagT E (Fin n) d) γ := fun γ g hg => by
    obtain ⟨y, x, hx, s, hs, -, e⟩ := (hS k n _ _ hc1 r' h'0 h'1 _ hA2).1 γ g hg
    obtain ⟨u, hu, e'⟩ := key x hx s hs
    refine ⟨t * u, fun i i' h => ?_, (incl y)⁻¹, ?_⟩
    · have hv : ∀ i, valuation E (u i : E) = 1 := fun i => by
        have := Valuation.map_one_add_of_lt (valuation E) ((hu i).trans_lt hr1)
        rwa [add_sub_cancel] at this
      simpa [hv] using ht i i' h
    · rw [(d1 _).1, ← e', ← e, inv_inv, map_mul, map_mul, map_inv]
      rfl
  refine ⟨fun δ γ h μδ μγ hδ hNm hμδ hμγ hm => ?_, fun γ μγ hγ hnn hμ => ?_⟩
  · unfold twOrbIntegralC orbIntegralC
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [quot_smul]
    by_cases hcase : ∃ y d, Strict d ∧ y⁻¹ * δ * sigmaGL σ y = diagT E (Fin n) d
    · obtain ⟨y, d, hd, hy⟩ := hcase
      obtain ⟨y', hy', hal⟩ := hA k E σ hσ n δ h y γ d hd hNm hy
      have oE := hO E n σ _ hcyc r hr0 hr1 μE hE _ hA1 δ y d hd (by rw [hsg]; exact hy) (twCent (sigmaGL σ) δ)
        (fun c => by rw [hsg]; rfl) μδ hμδ
      have ok := hO k n _ _ hc1 r' h'0 h'1 μk hk _ hA2 γ y' (nrmT k d) ((d1 d).2.1 hd) hy' (Subgroup.centralizer {γ})
        (fun c => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          change _ ↔ c⁻¹ * γ * c = γ
          rw [mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]
          rfl) μγ hμγ
      simp only [hsg] at oE
      have hdiv : ∀ u : Fin n → kˣ, nrmT k d * sgT (RingEquiv.refl k) u / u = nrmT k d := fun u => mul_div_cancel_right _ u
      by_cases hmem : nrmT k d ∈ nrmSet k r t
      · obtain ⟨u₀, hu₀⟩ := (d2 r d t).2 hmem
        have e1 := oE (R.image (u₀ * ·)) (fun u => by
          have e : d * sgT σ u / u / t = d * sgT σ u₀ / u₀ / t * (sgT σ (u₀⁻¹ * u) / (u₀⁻¹ * u)) := by
            have hm' : sgT (σ : E ≃+* E) (u₀⁻¹ * u) = (sgT (σ : E ≃+* E) u₀)⁻¹ * sgT (σ : E ≃+* E) u := by
              funext i
              simp only [sgT, Pi.mul_apply, Pi.inv_apply, map_mul, map_inv]
            rw [hm']
            exact alg _ _ _ _ _ _
          constructor
          · rintro ⟨_, rfl, hu⟩
            have h1 := (hnear _ _ (hnear _ _ hu₀ hu₀).2 hu).1
            rw [e, inv_mul_cancel_left] at h1
            obtain ⟨ρ, hρ, h2⟩ := (hR1 _).1 h1
            exact ⟨u₀ * ρ, Finset.mem_image_of_mem _ hρ, by simpa using (hR3 u₀ _ _).2 h2⟩
          · rintro ⟨_, hρ, h2⟩
            obtain ⟨ρ, hρ', rfl⟩ := Finset.mem_image.1 hρ
            refine ⟨t, rfl, ?_⟩
            rw [e]
            exact (hnear _ _ hu₀ ((hR1 _).2 ⟨ρ, hρ', (hR3 u₀ _ _).1 (by simpa using h2)⟩)).1)
          (by
            intro a ha b hb hab
            obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 ha
            obtain ⟨b, hb', rfl⟩ := Finset.mem_image.1 hb
            rw [hR2 a ha' b hb' ((hR3 _ _ _).1 hab)])
        have n1 : Near r' (1 : Fin n → kˣ) := fun i => by simp
        have e2 := ok {1} (fun u => ⟨fun _ => ⟨1, Finset.mem_singleton_self _, u, 1, rfl, n1, by simp⟩,
          fun _ => ⟨_, hmem, by rw [hdiv, div_self']; exact n1⟩⟩) (by simp)
        rw [Finset.card_image_of_injective _ (mul_right_injective u₀)] at e1
        have hmeas : MeasurableSet {z : GL (Fin n) E | y⁻¹ * (h * z * h⁻¹) * y ∈ ball n r} :=
          ((hK ▸ hKo : IsOpen (ball n r)).preimage (by fun_prop)).measurableSet
        have v1 := congrArg (fun m : Measure (GL (Fin n) E) => m {z | y⁻¹ * (h * z * h⁻¹) * y ∈ ball n r}) hm
        rw [Measure.map_apply (Continuous.measurable (by fun_prop)) hmeas,
          Measure.map_apply (f := fun t : Subgroup.centralizer {γ} => (incl (t : GL (Fin n) k) : GL (Fin n) E))
            (hcl.continuous.comp continuous_subtype_val).measurable hmeas] at v1
        have v2 : μδ.real {x : twCent (sigmaGL σ) δ | y⁻¹ * x * y ∈ ball n r} =
            j * μγ.real {x | y'⁻¹ * (x : GL (Fin n) k) * y' ∈ ball n r'} := by
          rw [← hvol γ y' _ ((d1 d).2.1 hd) hy' μγ hμγ]
          unfold Measure.real
          congr 1
          convert v1 using 2
          · ext x
            simp only [Set.mem_setOf_eq, Set.mem_preimage]
            rw [show h * (h⁻¹ * (x : GL (Fin n) E) * h) * h⁻¹ = x by group]
          · ext x
            simp only [Set.mem_setOf_eq, Set.mem_preimage]
            rw [hal _ x.2]
        refine e1.trans ?_
        rw [show quotIntegral μk _ μγ (fun g => (elemSet r' (nrmSet k r t)).indicator 1 (g⁻¹ * γ * g)) = _ from e2]
        rw [v2, ← Complex.ofReal_mul]
        congr 1
        rw [Finset.card_singleton, Nat.cast_one, one_mul, div_mul_div_comm, mul_right_comm j, mul_div_mul_right _ _ pk.ne']
      · have e1 := oE ∅ (fun u => ⟨fun ⟨_, hx, hu⟩ => absurd ((d2 r d t).1 ⟨u, hx ▸ hu⟩) hmem, by simp⟩) (by simp)
        have e2 := ok ∅ (fun u => ⟨fun ⟨x, hx, hu⟩ => absurd (by
          rw [hdiv] at hu
          simpa using key x hx _ hu) hmem, by simp⟩) (by simp)
        refine e1.trans ?_
        rw [show quotIntegral μk _ μγ (fun g => (elemSet r' (nrmSet k r t)).indicator 1 (g⁻¹ * γ * g)) = _ from e2]
        simp
    · rw [quot_zero, quot_zero, mul_zero]
      · intro g
        refine Set.indicator_of_notMem (fun hg => hcase ?_) _
        obtain ⟨d, hd, hnm⟩ := meet' γ g hg
        have hγ : IsRegSemisimple γ := by
          have e : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
              (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := by
            rw [hNm, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]
            rfl
          unfold IsTwRegSemisimple at hδ
          rw [e] at hδ
          exact (Polynomial.separable_map _).1 hδ
        obtain ⟨x, hx⟩ := normInj k E σ hσ n γ hγ δ _ ⟨h, hNm⟩ hnm
        exact ⟨x, d, hd, hx.symm⟩
      · intro g
        refine Set.indicator_of_notMem (fun hg => hcase ?_) _
        obtain ⟨y, x, -, s, -, hs, e⟩ := (hS E n σ _ hcyc r hr0 hr1 _ hA1).1 δ g (by rw [hsg]; exact hg)
        exact ⟨y, _, hs, by rw [← hsg]; exact e⟩
  · refine quot_zero _ _ _ _ fun g => ?_
    rw [Pi.smul_apply, Set.indicator_of_notMem (fun hg => hnn ?_), smul_zero]
    obtain ⟨d, -, hnm⟩ := meet' γ g hg
    exact ⟨_, hnm⟩

end UpperTheory.Gal.InertialTypesAlt.L
end
end
