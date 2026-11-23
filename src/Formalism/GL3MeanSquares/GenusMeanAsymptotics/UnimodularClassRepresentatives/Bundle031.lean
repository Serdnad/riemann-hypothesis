module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.HermitianLattices.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle026
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinG

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def red (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ↥(locF 𝔭 (spanO b)) →ₗ[𝓞 K] (κ → 𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (qE b (extP K 𝔭 ^ k)).toLinearMap ∘ₗ (quotLocF h𝔭 (spanO b) k).symm.toLinearMap ∘ₗ
    Submodule.mkQ _

theorem red_of_mem (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (w : ↥(locF 𝔭 (spanO b))) (hw : (w : V) ∈ spanO b) :
    red b h𝔭 k w = fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (crd b ⟨w, hw⟩ i) := by
  have e : (quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨(w : V), hw⟩ := by
    rw [LinearEquiv.symm_apply_eq, quotLocF_mk h𝔭 (spanO b) k ⟨(w : V), hw⟩ w.2]
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w)) = _
  rw [e, qE_mk]

theorem red_smul_one (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) {c : 𝓞 F}
    (hc : c - 1 ∈ 𝔭 ^ k) (w : ↥(locF 𝔭 (spanO b))) : red b h𝔭 k (ι c • w) = red b h𝔭 k w := by
  rw [map_smul]
  funext i
  rw [Pi.smul_apply, Algebra.smul_def]
  have : algebraMap (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ k) (ι c) = 1 := by
    show Ideal.Quotient.mk _ (ι c) = 1
    rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq, ← map_one ι, ← map_sub]
    exact ι_mem_pow hc
  rw [this, one_mul]

theorem red_eq_of_sub_mem (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (w w' : ↥(locF 𝔭 (spanO b)))
    (hww : (w : V) - w' ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V)) :
    red b h𝔭 k w = red b h𝔭 k w' := by
  have e : (Submodule.Quotient.mk w : ↥(locF 𝔭 (spanO b)) ⧸
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))) = Submodule.Quotient.mk w' := by
    rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
    exact hww
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w)) =
    qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w'))
  rw [e]

def bM (b : Basis κ K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (j : κ) : ↥(locF 𝔭 (spanO b)) :=
  ⟨b j, le_locF 𝔭 _ (Submodule.subset_span (Set.mem_range_self j))⟩

theorem red_bM (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (k : ℕ) (j : κ) :
    red b h𝔭 k (bM b 𝔭 j) = Pi.single j 1 := by
  have e : (quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk (bM b 𝔭 j)) =
      Submodule.Quotient.mk (bO b j) := by
    rw [LinearEquiv.symm_apply_eq, quotLocF_mk h𝔭 (spanO b) k (bO b j)
      (by rw [bO_apply]; exact (bM b 𝔭 j).2)]
    congr 1
    apply Subtype.ext
    exact (bO_apply b j).symm
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk (bM b 𝔭 j))) = _
  rw [e, qE_bO]

variable [Fact (IsFixF K F)]

theorem red_form (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (w w' : ↥(locF 𝔭 (spanO b))) {z : 𝓞 K} (hz : h (w : V) (w' : V) = algebraMap (𝓞 K) K z) :
    star (red b h𝔭 k w) ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ red b h𝔭 k w') =
      Ideal.Quotient.mk (extP K 𝔭 ^ k) z := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨c, hc, hcw⟩ := exists_approx h𝔭 (spanO b) k w.2
  obtain ⟨c', hc', hcw'⟩ := exists_approx h𝔭 (spanO b) k w'.2
  rw [← red_smul_one b h𝔭 k hc w, ← red_smul_one b h𝔭 k hc' w',
    red_of_mem b h𝔭 k (ι c • w) hcw, red_of_mem b h𝔭 k (ι c' • w') hcw', ← mk_form]
  have e1 := form_eq h b hH ⟨_, hcw⟩ ⟨_, hcw'⟩
  have e2 : h (ι c • (w : V)) (ι c' • (w' : V)) = algebraMap (𝓞 K) K (ι (c * c') * z) := by
    rw [form_smul hF, hz, map_mul (algebraMap (𝓞 K) K)]
  have e3 := FaithfulSMul.algebraMap_injective (𝓞 K) K (e1.symm.trans e2)
  have e4 : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (c * c')) = 1 := by
    rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq, ← map_one ι, ← map_sub]
    apply ι_mem_pow
    have : c * c' - 1 = (c - 1) * c' + (c' - 1) := by ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hc) hc'
  calc _ = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι (c * c') * z) := congrArg _ e3
    _ = _ := by rw [map_mul, e4, one_mul]

omit [Fact (IsFixF K F)] in
theorem map_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h M) {x : V} (hx : x ∈ M) : g x ∈ M := by
  have h2 : Formalism.HermitianLatticesTheory.gmap g M = M := hg.2
  rw [← h2]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

def gM {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V} (hg : g ∈ autSub h M) :
    ↥M →ₗ[𝓞 K] ↥M :=
  ((g : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict fun _ hx => map_mem hg hx

def gMat {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    [𝔭.IsPrime] (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) :
    Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.of fun i j => red b h𝔭 k (gM hg (bM b 𝔭 j)) i

omit [Fact (IsFixF K F)] in
theorem red_gM {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    [𝔭.IsPrime] (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b)))
    (w : ↥(locF 𝔭 (spanO b))) : red b h𝔭 k (gM hg w) = gMat b h𝔭 k hg *ᵥ red b h𝔭 k w := by
  have key : (red b h𝔭 k ∘ₗ gM hg) ∘ₗ Submodule.inclusion (le_locF 𝔭 (spanO b)) =
      (((gMat b h𝔭 k hg).mulVecLin.restrictScalars (𝓞 K)) ∘ₗ red b h𝔭 k) ∘ₗ
        Submodule.inclusion (le_locF 𝔭 (spanO b)) := by
    apply (bO b).ext
    intro j
    have e : Submodule.inclusion (le_locF 𝔭 (spanO b)) (bO b j) = bM b 𝔭 j := by
      apply Subtype.ext
      exact bO_apply b j
    simp only [LinearMap.comp_apply, e, LinearMap.restrictScalars_apply, mulVecLin_apply]
    rw [red_bM, mulVec_single_one]
    rfl
  obtain ⟨c, hc, hcw⟩ := exists_approx h𝔭 (spanO b) k w.2
  have h1 := LinearMap.congr_fun key ⟨_, hcw⟩
  have e : Submodule.inclusion (le_locF 𝔭 (spanO b)) ⟨_, hcw⟩ = ι c • w := rfl
  simp only [LinearMap.comp_apply, e, LinearMap.restrictScalars_apply, mulVecLin_apply] at h1
  rw [map_smul, red_smul_one b h𝔭 k hc, red_smul_one b h𝔭 k hc] at h1
  exact h1

theorem exists_matrix (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b))) :
    ∃ G G' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k),
      Gᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * G = H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ∧
      G * G' = 1 ∧ ∀ w w' : ↥(locF 𝔭 (spanO b)), (w' : V) = g w →
        red b h𝔭 k w' = G *ᵥ red b h𝔭 k w := by
  have := h𝔭.isPrime
  have hg' : g⁻¹ ∈ autSub h (locF 𝔭 (spanO b)) := inv_mem hg
  refine ⟨gMat b h𝔭 k hg, gMat b h𝔭 k hg', ?_, ?_, ?_⟩
  · ext i j
    rw [← form_single (_ᴴ * _ * _) i j, ← form_mulVec, ← red_bM b h𝔭 k i, ← red_bM b h𝔭 k j,
      ← red_gM, ← red_gM, Matrix.map_apply]
    apply red_form h b hH h𝔭 k
    show h (g (b i)) (g (b j)) = _
    rw [hg.1 (b i) (b j), hH]
  · ext i j
    have h1 : (gMat b h𝔭 k hg * gMat b h𝔭 k hg') *ᵥ Pi.single j 1 = Pi.single j 1 := by
      rw [← mulVec_mulVec, ← red_bM b h𝔭 k j, ← red_gM, ← red_gM]
      congr 1
      apply Subtype.ext
      show g (g⁻¹ (b j)) = b j
      exact g.apply_symm_apply (b j)
    have h2 := congrFun h1 i
    rw [mulVec_single_one] at h2
    rw [Matrix.one_apply, ← Pi.single_apply]
    exact h2
  · intro w w' hww
    rw [← red_gM]
    congr 1
    apply Subtype.ext
    exact hww

end Formalism.HermitianLattices.Ext.L3.PinG
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def cmb (b : Basis κ K V) (c : κ → 𝓞 K) : spanO b := (bO b).equivFun.symm c

theorem coe_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : (cmb b c : V) = ∑ l, c l • b l := by
  rw [cmb, Basis.equivFun_symm_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [Submodule.coe_smul, bO_apply]

theorem crd_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : crd b (cmb b c) = c :=
  (bO b).equivFun.apply_symm_apply c

theorem cmb_crd (b : Basis κ K V) (y : spanO b) : cmb b (crd b y) = y :=
  (bO b).equivFun.symm_apply_apply y

def inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) : spanO b →ₗ[𝓞 K] ↥(locF 𝔭 (spanO b)) :=
  Submodule.inclusion (le_locF 𝔭 (spanO b))

theorem coe_inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) (y : spanO b) : (inA 𝔭 b y : V) = y := rfl

abbrev QA (𝔭 : Ideal (𝓞 F)) (b : Basis κ K V) (k : ℕ) : Type :=
  ↥(locF 𝔭 (spanO b)) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))

theorem mk_eq_iff {𝔭 : Ideal (𝓞 F)} (b : Basis κ K V) (k : ℕ) (x y : ↥(locF 𝔭 (spanO b))) :
    (Submodule.Quotient.mk x : QA 𝔭 b k) = Submodule.Quotient.mk y ↔
      (x : V) - y ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl

theorem quotLocF_mk' {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (y : spanO b) : quotLocF h𝔭 (spanO b) k (Submodule.Quotient.mk y) = Submodule.Quotient.mk (inA 𝔭 b y) :=
  rfl

theorem exists_cmb {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (q : QA 𝔭 b k) : ∃ c : κ → 𝓞 K, q = Submodule.Quotient.mk (inA 𝔭 b (cmb b c)) := by
  obtain ⟨q₀, rfl⟩ := (quotLocF h𝔭 (spanO b) k).surjective q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q₀
  exact ⟨crd b y, by rw [cmb_crd, quotLocF_mk']⟩

theorem cmb_eq_sum (b : Basis κ K V) (c : κ → 𝓞 K) : cmb b c = ∑ i, c i • cmb b (Pi.single i 1) := by
  apply (bO b).equivFun.injective
  show crd b _ = crd b _
  rw [crd_cmb]
  have : crd b (∑ i, c i • cmb b (Pi.single i 1)) = ∑ i, c i • crd b (cmb b (Pi.single i 1)) := by
    unfold crd

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [this]
  funext l
  simp [crd_cmb, Pi.single_apply]

theorem end_apply_cmb {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (Y : Matrix κ κ (𝓞 K))
    (hXY : ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
      Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i))) (c : κ → 𝓞 K) :
    X (Submodule.Quotient.mk (inA 𝔭 b (cmb b c))) = Submodule.Quotient.mk (inA 𝔭 b (cmb b (Y *ᵥ c))) := by
  have h1 : cmb b (Y *ᵥ c) = ∑ i, c i • cmb b fun l => Y l i := by
    apply (bO b).equivFun.injective
    show crd b _ = crd b _
    have : crd b (∑ i, c i • cmb b fun l => Y l i) = ∑ i, c i • crd b (cmb b fun l => Y l i) := by
      unfold crd

      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    rw [this, crd_cmb]
    funext l
    simp [crd_cmb, mulVec, dotProduct, mul_comm]
  rw [h1, cmb_eq_sum b c]
  simp only [← Submodule.mkQ_apply] at hXY ⊢

  simp only [map_sum, map_smul, hXY]

end Formalism.HermitianLattices.Ext.L3.HU
end
end

section

open NumberField Module nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem exists_ne_zero_of_isLattice {A : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A) :
    ∃ a ∈ A, a ≠ 0 := by
  by_contra hne
  push Not at hne
  have h2 : Submodule.span K (A : Set K) = ⊥ := by
    rw [Submodule.span_eq_bot]; exact hne
  have h3 : (1 : K) ∈ Submodule.span K (A : Set K) := by
    rw [hA.span_eq_top]; exact Submodule.mem_top
  rw [h2, Submodule.mem_bot] at h3
  exact one_ne_zero h3

theorem span_eq_top_of_ne_zero {A : Submodule (𝓞 K) K} {a : K} (ha : a ∈ A) (h0 : a ≠ 0) :
    Submodule.span K (A : Set K) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = (x * a⁻¹) • a := by rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ h0, mul_one]
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ha)

theorem isLattice_mul {A B : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A)
    (hB : Submodule.IsFullLattice K B) : Submodule.IsFullLattice K (A * B) := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  obtain ⟨b, hb, hb0⟩ := exists_ne_zero_of_isLattice hB
  have := Submodule.IsLattice.of_fg K (hA.toIsLattice.fg.mul hB.toIsLattice.fg)
  exact ⟨span_eq_top_of_ne_zero (Submodule.mul_mem_mul ha hb) (mul_ne_zero ha0 hb0)⟩

theorem exists_inv {A : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A) :
    ∃ A' : Submodule (𝓞 K) K, Submodule.IsFullLattice K A' ∧ A' * A = 1 := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_of_isLattice hA
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨A, FractionalIdeal.isFractional_of_fg hA.toIsLattice.fg⟩
  have hI : I ≠ 0 := by
    intro h
    have h' : a ∈ (I : Submodule (𝓞 K) K) := ha
    rw [h, FractionalIdeal.coeToSubmodule_zero, Submodule.mem_bot] at h'
    exact ha0 h'
  have hmul : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * A = 1 := by
    have e := congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K))
      (inv_mul_cancel₀ hI)
    have e2 : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) * (I : Submodule (𝓞 K) K) = 1 := by
      simpa only [FractionalIdeal.coeToSubmodule_mul, FractionalIdeal.coeToSubmodule_one] using e
    exact e2
  have := Submodule.IsLattice.of_fg K (FractionalIdeal.fg_of_isNoetherianRing le_rfl I⁻¹)
  refine ⟨_, ⟨?_⟩, hmul⟩
  have hne : ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.bot_mul] at hmul
    have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.one_le.1 le_rfl
    rw [← hmul, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact span_eq_top_of_ne_zero hc hc0

def mulE (I J : Submodule (𝓞 K) K) (hJI : J * I = 1) :
    Submodule (𝓞 K) K ≃ Submodule (𝓞 K) K where
  toFun M := I * M
  invFun M := J * M
  left_inv M := by change J * (I * M) = M; rw [← mul_assoc, hJI, one_mul]
  right_inv M := by change I * (J * M) = M; rw [← mul_assoc, mul_comm I J, hJI, one_mul]

theorem gmap_mul (g : K ≃ₗ[K] K) (I M : Submodule (𝓞 K) K) : I * gmap g M = gmap g (I * M) := by
  have key : ∀ x y : K, g (x * y) = x * g y := fun x y => by
    simpa only [smul_eq_mul] using g.map_smul x y
  unfold gmap
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨i * m, Submodule.mul_mem_mul hi hm, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.mul_le.2 fun i hi m hm => ?_)
    rw [Submodule.mem_comap]
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]
    exact Submodule.mul_mem_mul hi (Submodule.mem_map_of_mem hm)

theorem ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsMaximal) {s : 𝓞 K}
    (hs : s ∈ hcompl (K := K) p) : s ≠ 0 := by
  intro h0
  exact Formalism.HermitianLatticesTheory.genusBasic_hS (K := K) p hp s hs (by rw [h0]; exact p.zero_mem)

theorem loc_mul {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (I M : Submodule (𝓞 K) K) :
    I * loc (K := K) p M = loc (K := K) p (I * M) := by
  apply le_antisymm
  · refine Submodule.mul_le.2 fun i hi y hy => ?_
    have hy' : ∃ s ∈ hcompl (K := K) p, s • y ∈ M := hy
    obtain ⟨s, hs, hsy⟩ := hy'
    show ∃ s ∈ hcompl (K := K) p, s • (i * y) ∈ I * M
    refine ⟨s, hs, ?_⟩
    have e : s • (i * y) = i * (s • y) := by rw [Algebra.smul_def, Algebra.smul_def]; ring
    rw [e]
    exact Submodule.mul_mem_mul hi hsy
  · intro x hx
    have hx' : ∃ s ∈ hcompl (K := K) p, s • x ∈ I * M := hx
    obtain ⟨s, hs, hsx⟩ := hx'
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact ne_zero_of_mem_hcompl hp hs
    have hle : I * M ≤ (I * loc (K := K) p M).comap
        (LinearMap.mulLeft (𝓞 K) (algebraMap (𝓞 K) K s)⁻¹) := by
      refine Submodule.mul_le.2 fun i hi m hm => ?_
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      have e : (algebraMap (𝓞 K) K s)⁻¹ * (i * m) = i * ((algebraMap (𝓞 K) K s)⁻¹ * m) := by ring
      rw [e]
      refine Submodule.mul_mem_mul hi ?_
      show ∃ t ∈ hcompl (K := K) p, t • ((algebraMap (𝓞 K) K s)⁻¹ * m) ∈ M
      refine ⟨s, hs, ?_⟩
      rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
      exact hm
    have h2 := hle hsx
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply, Algebra.smul_def, ← mul_assoc,
      inv_mul_cancel₀ hs0, one_mul] at h2
    exact h2

theorem form_eq (h : K →ₗ⋆[K] K →ₗ[K] K) (x y : K) : h x y = star x * y * h 1 1 := by
  rw [show h x y = h (x • (1 : K)) (y • (1 : K)) by simp only [smul_eq_mul, mul_one],
    LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply]
  simp only [smul_eq_mul]
  ring

theorem mem_isom_iff {h : K →ₗ⋆[K] K →ₗ[K] K} (h1 : h 1 1 ≠ 0) (g : K ≃ₗ[K] K) :
    g ∈ isom h ↔ star (g 1) * g 1 = 1 := by
  have hg : ∀ x, g x = x * g 1 := fun x => by
    rw [show g x = g (x • (1 : K)) by rw [smul_eq_mul, mul_one], LinearEquiv.map_smul, smul_eq_mul]
  constructor
  · intro hm
    have hm' : ∀ x y, h (g x) (g y) = h x y := hm
    have e := hm' 1 1
    rw [form_eq h (g 1) (g 1)] at e
    exact mul_right_cancel₀ h1 (by rw [one_mul]; exact e)
  · intro he
    show ∀ x y, h (g x) (g y) = h x y
    intro x y
    rw [form_eq h (g x) (g y), form_eq h x y, hg x, hg y, star_mul']
    calc star x * star (g 1) * (y * g 1) * h 1 1 = star x * y * (star (g 1) * g 1) * h 1 1 := by ring
      _ = star x * y * h 1 1 := by rw [he, mul_one]

theorem mass_eq_of_lattices {h₁ h₂ : K →ₗ⋆[K] K →ₗ[K] K} (hn₁ : h₁ 1 1 ≠ 0) (hn₂ : h₂ 1 1 ≠ 0)
    {A B : Submodule (𝓞 K) K} (hA : Submodule.IsFullLattice K A) (hB : Submodule.IsFullLattice K B)
    (hex : ∃ s, IsClassReps h₁ A s) : mass h₂ B = mass h₁ A := by
  obtain ⟨A', hA', hA'A⟩ := exists_inv hA
  obtain ⟨B', hB', hB'B⟩ := exists_inv hB
  have hJC : (A * B') * (B * A') = 1 := by
    calc (A * B') * (B * A') = (A' * A) * (B' * B) := by ring
      _ = 1 := by rw [hA'A, hB'B, one_mul]
  have t1 : ∀ g : K ≃ₗ[K] K, (Equiv.refl (K ≃ₗ[K] K)) g ∈ isom h₂ ↔ g ∈ isom h₁ := fun g => by
    rw [Equiv.refl_apply, mem_isom_iff hn₂, mem_isom_iff hn₁]
  have t2 : ∀ (g : K ≃ₗ[K] K) (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (gmap g M) =
        gmap ((Equiv.refl (K ≃ₗ[K] K)) g) (mulE (B * A') (A * B') hJC M) := fun g M =>
    gmap_mul g (B * A') M
  have t3 : ∀ (p : Ideal (𝓞 K)), p.IsMaximal → ∀ (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (loc p M) = loc p (mulE (B * A') (A * B') hJC M) :=
    fun p hp M => loc_mul hp (B * A') M
  have t4 : ∀ (M : Submodule (𝓞 K) K),
      Submodule.IsFullLattice K (mulE (B * A') (A * B') hJC M) ↔ Submodule.IsFullLattice K M := by
    intro M
    change Submodule.IsFullLattice K (B * A' * M) ↔ Submodule.IsFullLattice K M
    constructor
    · intro hM
      have e := isLattice_mul (isLattice_mul hA hB') hM
      rwa [← mul_assoc, hJC, one_mul] at e
    · intro hM
      exact isLattice_mul (isLattice_mul hB hA') hM
  have hΦA : mulE (B * A') (A * B') hJC A = B := by
    show B * A' * A = B
    rw [mul_assoc, hA'A, mul_one]
  have he := (mass_transfer (mulE (B * A') (A * B') hJC) (Equiv.refl _) t1 t2 t3 t4 hex).2
  rw [hΦA] at he
  exact he

end Formalism.HermitianLattices.Ext.L3.RankOne
end
end
