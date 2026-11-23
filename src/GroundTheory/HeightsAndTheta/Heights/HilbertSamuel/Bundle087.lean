module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle072
public import GroundTheory.HeightsAndTheta.Heights.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle079
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountIntegrals

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Mul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLatQ_add {B γ : K → ℤ} {g s : Ω} (hg : g ∈ chartLatQ y γ 1) (hs : s ∈ chartLatQ y B 1) :
    g * s ∈ chartLatQ y (B + γ) 1 := by
  intro c' hc'
  have hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (B + γ) k)) =
      y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * γ k)) * y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * B k)) := by
    intro k
    rw [← zpow_add₀ (hc' k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  have heq : g * s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (B + γ) k)) =
      (g * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * γ k))) * (s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * B k))) := by
    simp only [hk, Finset.prod_mul_distrib]
    ring
  rw [heq]
  exact Subalgebra.mul_mem _ (hg c' hc') (hs c' hc')

theorem finrank_quot_le_of_regular {B γ : K → ℤ} {g : Ω} [FiniteDimensional ℚ (chartLatQ y (B + γ) 1)]
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hg : g ∈ chartLatQ y γ 1)
    (hreg : ∀ s : Ω, s ∈ chartLatQ y B 1 → g * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (B + γ - 1) 1 →
      s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (B - 1) 1) :
    Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) ≤
      Module.finrank ℚ (chartLatQ y (B + γ) 1 ⧸ chartDivSec y c (B + γ)) := by
  let φ : chartLatQ y B 1 →ₗ[ℚ] chartLatQ y (B + γ) 1 :=
    { toFun := fun s => ⟨g * s, mul_mem_chartLatQ_add hg s.2⟩
      map_add' := fun s t => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm r g (s : Ω)) }
  have hle : chartDivSec y c B ≤ (chartDivSec y c (B + γ)).comap φ := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hs)
    refine Submodule.mem_comap.mpr (Submodule.mem_comap.mpr (Submodule.mem_map.mpr
      ⟨g * t, ?_, ?_⟩))
    · have h := mul_mem_chartLatQ_add hg ht
      rwa [show B - 1 + γ = B + γ - 1 by abel] at h
    · change (∏ k, y ⟨k, c k⟩) * (g * t) = g * (s : Ω)
      have hts' : (∏ k, y ⟨k, c k⟩) * t = (s : Ω) := hts
      rw [← hts']
      ring
  refine LinearMap.finrank_le_finrank_of_injective (f := Submodule.mapQ _ _ φ hle) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.Quotient.mk_eq_zero]
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
  have hts' : (∏ k, y ⟨k, c k⟩) * t = g * (s : Ω) := hts
  have hu := hreg s s.2 (by rwa [← hts', mul_div_cancel_left₀ _ hm0])
  refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨_, hu, ?_⟩)
  change (∏ k, y ⟨k, c k⟩) * ((s : Ω) / ∏ k, y ⟨k, c k⟩) = (s : Ω)
  exact mul_div_cancel₀ _ hm0

end Mul

theorem ShiftQuotientBound.proof (hfin : SectionLatticeFinite.Statement) (hQ : HyperplaneQuotientBound.Statement)
    (hR : HyperplaneRegularSection.Statement) : ShiftQuotientBound.Statement := by
  intro K _ ι _ Ω _ _ y D a b c hD hV hB hc
  obtain ⟨C₀, hC₀⟩ := hQ K ι Ω y D (fun _ => 1) c hD hV hB hc
  set N : ℕ := 1 + ∑ k, (a k).natAbs with hN
  set M : ℕ := ∑ k, (b k).natAbs with hM
  have hN1 : 1 ≤ N := by omega
  have ht : Tendsto (fun n : ℕ => n * N + M) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; nlinarith [Nat.zero_le n, hN1]) tendsto_id
  refine ⟨|C₀| * ((N + M : ℕ) : ℝ) ^ (D - 1),
    ((ht.eventually hC₀).and (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_⟩
  set B : K → ℤ := (n : ℤ) • a + b with hBdef
  set γ : K → ℤ := (((n * N + M : ℕ) : ℤ) • fun _ => (1 : ℤ)) - B with hγdef
  have hγ : ∀ k, 0 ≤ γ k := by
    intro k
    have ha : (a k).natAbs ≤ ∑ j, (a j).natAbs :=
      Finset.single_le_sum (f := fun j => (a j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hb : (b k).natAbs ≤ ∑ j, (b j).natAbs :=
      Finset.single_le_sum (f := fun j => (b j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have ha' : a k < (N : ℤ) :=
      calc a k ≤ (a k).natAbs := Int.le_natAbs
        _ ≤ ((∑ j, (a j).natAbs : ℕ) : ℤ) := by exact_mod_cast ha
        _ < (N : ℤ) := by rw [hN]; exact_mod_cast (by omega : ∑ j, (a j).natAbs < 1 + ∑ j, (a j).natAbs)
    have hb' : b k ≤ (M : ℤ) :=
      calc b k ≤ (b k).natAbs := Int.le_natAbs
        _ ≤ (M : ℤ) := by rw [hM]; exact_mod_cast hb
    simp only [hγdef, hBdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ha'.le (Int.natCast_nonneg n)]
  obtain ⟨g, -, hg, hreg⟩ := hR K ι Ω y c (fun k => (γ k).toNat) hc
  have he : (fun k => ((γ k).toNat : ℤ)) = γ := funext fun k => Int.toNat_of_nonneg (hγ k)
  rw [he] at hg hreg
  have := finiteDimensional_chartLatQ hfin (fun k => ⟨c k, hc k⟩) (B + γ)
  have h1 := finrank_quot_le_of_regular hc hg (hreg B)
  rw [show B + γ = ((n * N + M : ℕ) : ℤ) • fun _ => (1 : ℤ) by rw [hγdef]; abel] at h1
  have h2 : (Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) : ℝ) ≤ C₀ * ((n * N + M : ℕ) : ℝ) ^ (D - 1) :=
    le_trans (by exact_mod_cast h1) hn
  have h3 : ((n * N + M : ℕ) : ℝ) ≤ ((N + M : ℕ) : ℝ) * (n : ℝ) := by
    have : n * N + M ≤ (N + M) * n := by nlinarith
    exact_mod_cast this
  calc (Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) : ℝ)
      ≤ |C₀| * ((n * N + M : ℕ) : ℝ) ^ (D - 1) :=
        h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    _ ≤ |C₀| * (((N + M : ℕ) : ℝ) * (n : ℝ)) ^ (D - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 _) (abs_nonneg _)
    _ = |C₀| * ((N + M : ℕ) : ℝ) ^ (D - 1) * (n : ℝ) ^ (D - 1) := by rw [mul_pow, mul_assoc]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Matrix SupBoundCount

noncomputable section

namespace BlockChiCovolume

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem gram_symm (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (k l : Fin r) :
    blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) l k =
      blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) k l := by
  rw [blockGram_eq d n f hf, blockGram_eq d n f hf]
  simp only [pairRe_comm]

theorem quad_nonneg (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    0 ≤ a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) := by
  rw [gram_quad d n f hf]
  have h : ∀ z, 0 ≤ ‖comb f a z‖ ^ 2 / d.A.h z ^ (2 * n) := fun z =>
    div_nonneg (sq_nonneg _) ((even_two_mul n).pow_nonneg _)
  have h1 := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n)) fun x => h _
  have h2 := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n)) fun x => h _
  exact mul_nonneg (by norm_num) (add_nonneg h1 h2)

theorem entry_of_quad {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (hG : ∀ k l, G l k = G k l) (k l : Fin r) :
    G k l = ((Pi.single k 1 + Pi.single l 1) ⬝ᵥ (G *ᵥ (Pi.single k 1 + Pi.single l 1)) -
      Pi.single k 1 ⬝ᵥ (G *ᵥ Pi.single k 1) - Pi.single l 1 ⬝ᵥ (G *ᵥ Pi.single l 1)) / 2 := by
  simp [mulVec_add, dotProduct_add, add_dotProduct, hG l k]
  ring

theorem cast_single_add {r : ℕ} (k l : Fin r) :
    (fun j => (((Pi.single k 1 + Pi.single l 1 : Fin r → ℤ) j : ℤ) : ℝ)) = Pi.single k 1 + Pi.single l 1 := by
  funext j
  simp only [Pi.add_apply, Int.cast_add, Pi.single_apply]
  split_ifs <;> simp

theorem cast_single {r : ℕ} (k : Fin r) :
    (fun j => (((Pi.single k 1 : Fin r → ℤ) j : ℤ) : ℝ)) = Pi.single k 1 := by
  funext j
  simp only [Pi.single_apply]
  split_ifs <;> simp

end BlockChiCovolume


open BlockChiCovolume in
theorem BlockChiCovolume.proof : BlockChiCovolume.Statement := by
  intro D K _ _ ι _ Ω _ _ d n E hE r ψ hψ hnorm _ _
  have hex := exists_isSecBasisM d.y d.k₀ n
  rw [blockChi, dite_eq_left hex]
  have hb := hex.choose_spec
  generalize hex.choose = p at hb ⊢
  obtain ⟨hbf, hli, hspan⟩ := hb
  choose f hf hfb using hbf
  have hbeq : p.2 = fun j => map (Int.castRingHom ℚ) (f j) := funext hfb
  rw [hbeq] at hli hspan ⊢
  beta_reduce at hli hspan
  obtain ⟨w, hw⟩ : ∃ w : Fin p.1 → Ω, w = fun j => aeval d.y (map (Int.castRingHom ℚ) (f j)) := ⟨_, rfl⟩
  rw [← hw] at hli hspan
  have hEN : E = (Submodule.span ℤ (Set.range w)).toAddSubgroup := hE.trans hspan.symm
  let eN : E ≃+ Submodule.span ℤ (Set.range w) :=
    (AddEquiv.addSubgroupCongr hEN).trans (AddEquiv.refl _)
  let bE : Module.Basis (Fin p.1) ℤ E := (Module.Basis.span hli).map eN.symm.toIntLinearEquiv
  have hrange : LinearMap.range ψ.toIntLinearMap = imageLattice ψ := by
    ext v
    simp [imageLattice]
  let B : Module.Basis (Fin p.1) ℤ (imageLattice ψ) :=
    (bE.map (LinearEquiv.ofInjective ψ.toIntLinearMap hψ)).map (LinearEquiv.ofEq _ _ hrange)
  let ε : Fin p.1 → E := fun j => ⟨w j, hEN ▸ Submodule.subset_span ⟨j, rfl⟩⟩
  have hB : ∀ j, (B j : EuclideanSpace ℝ (Fin r)) = ψ (ε j) := by
    intro j
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.map_apply]
    show ψ (bE j) = ψ (ε j)
    congr 1
    apply Subtype.ext
    rw [Module.Basis.map_apply]
    have h : ((Module.Basis.span hli j : Submodule.span ℤ (Set.range w)) : Ω) = w j :=
      congrArg Subtype.val (Module.Basis.span_apply hli j)
    exact h
  set G := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) with hG
  have key : ∀ m : Fin p.1 → ℤ,
      ‖ψ (∑ j, m j • ε j)‖ ^ 2 = (fun j => (m j : ℝ)) ⬝ᵥ (G *ᵥ fun j => (m j : ℝ)) := by
    intro m
    rw [hnorm _ (∑ j, m j • f j) (isMultiHomog_zsum f m hf), blockL2Norm_sum_eq_sqrt_gram d n f hf m,
      Real.sq_sqrt (quad_nonneg d n f hf _)]

    simp [ε, hw, SupBoundCount.aeval_map_int, map_sum]
  have hgram : Matrix.gram ℝ (fun i => (B i : EuclideanSpace ℝ (Fin r))) = G := by
    ext k l
    rw [entry_of_quad G (gram_symm d n f hf) k l, ← cast_single_add, ← cast_single, ← cast_single, ← key, ← key,
      ← key]
    simp only [Matrix.gram, of_apply, hB]
    simp [Pi.single_apply, add_smul, Finset.sum_add_distrib]
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
    ring
  have hdet : 0 ≤ G.det := hgram ▸ (Matrix.posSemidef_gram ℝ _).det_nonneg
  rw [covolume_eq_sqrt_det_gram (imageLattice ψ) B, hgram, Real.log_sqrt hdet]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PowerBlockArith

variable {K : Type} [Fintype K] {ι : K → Type}

theorem blockFnField_addBlock {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {a : K → ℤ} {m N : ℕ}
    {v : Fin N → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hv : ∀ j, v j ∈ chartLat y a m) :
    blockFnField (addBlock y v) = blockFnField y := by
  have hZ : ∀ s ∈ chartRingZ y c, s ∈ blockFnField y := by
    intro s hs
    have : chartRingZ y c ≤ (blockFnField y).toSubalgebra.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin ℚ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
    exact this hs
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨⟨_ | k, i⟩, ⟨_ | k', i'⟩, hpq, rfl⟩
    · have hP0 : (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have e : addBlock y v ⟨none, i⟩ / addBlock y v ⟨none, i'⟩ =
          (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) / (v i' * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) := by
        rw [mul_div_mul_right _ _ hP0]
        rfl
      rw [e]
      exact div_mem (hZ _ (hv i c hc)) (hZ _ (hv i' c hc))
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · obtain rfl : k = k' := Option.some_injective _ hpq
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _
      ⟨(⟨some p.1, p.2⟩ : Σ k, addIdx ι N k), (⟨some q.1, (hpq ▸ q.2 : ι q.1)⟩ : Σ k, addIdx ι N k),
        by simp [hpq], by cases p; cases q; simp at hpq; subst hpq; rfl⟩

end PowerBlockArith


open PowerBlockArith in
theorem PowerBlockArith.proof (hF : CoordArithOfFnField.Statement) : PowerBlockArith.Statement := by
  intro K _ ι _ Ω _ _ y D a m N v hy hv hgen

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0]
  choose c hc using hnz

  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    obtain ⟨u, -, hu⟩ := hgen c hc
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hu
  exact hF K ι (Option K) (addIdx ι N) Ω y (addBlock y v) (D + 1) ⟨none⟩
    (fun k => by
      cases k with
      | none => exact ⟨j₀, hj₀⟩
      | some k => exact ⟨c k, hc k⟩)
    (blockFnField_addBlock c hc hv).symm hy

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
