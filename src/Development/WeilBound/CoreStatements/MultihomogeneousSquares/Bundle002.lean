module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

section

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {σ : Type} (blk : σ → Option K)

def baseInc : (Σ k, baseIdx ι blk k) → Σ k, ι k := fun q => ⟨q.1.1, q.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem baseInc_injective : Function.Injective (baseInc (ι := ι) blk) := by
  rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
  simp only [baseInc, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  cases h2
  rfl


open Classical in
def extDeg (b : NonPluckerBlocks blk → ℕ) : K → ℕ := fun k => if h : ∀ p, blk p ≠ some k then b ⟨k, h⟩ else 0

theorem isMultiHomog_rename_baseInc {β : MRing (baseIdx ι blk)} {b : NonPluckerBlocks blk → ℕ} (hβ : IsMultiHomog β b) :
    IsMultiHomog (rename (baseInc (ι := ι) blk) β) (extDeg blk b) := by
  classical
  intro m hm k
  rw [support_rename_of_injective (baseInc_injective blk)] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.1 hm
  by_cases h : ∀ p, blk p ≠ some k
  · have e : ∀ i : ι k, (Finsupp.mapDomain (baseInc blk) m₀) ⟨k, i⟩ = m₀ ⟨⟨k, h⟩, i⟩ := fun i =>
      Finsupp.mapDomain_apply_of_injective (baseInc_injective blk) m₀ (⟨⟨k, h⟩, i⟩ : Σ k, baseIdx ι blk k)
    simp only [e, extDeg, dif_pos h]
    exact hβ m₀ hm₀ ⟨k, h⟩
  · have e : ∀ i : ι k, (Finsupp.mapDomain (baseInc blk) m₀) ⟨k, i⟩ = 0 := fun i =>
      Finsupp.mapDomain_of_notMem_range _ _ (by
        rintro ⟨q, hq⟩
        have : q.1.1 = k := congrArg Sigma.fst hq
        exact h (this ▸ q.1.2))
    simp only [e, extDeg, dif_neg h, Finset.sum_const_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem evC_rename_baseInc (z : (Σ k, ι k) → ℂ) (β : MRing (baseIdx ι blk)) :
    Cmp.evC z (rename (baseInc blk) β) = Cmp.evC (basePart blk z) β := by
  simp only [Cmp.evC, map_rename, eval_rename]
  rfl

end SlopeTestRemainingChoices

theorem alg_of : StEmb → StForm → StAlg := by
  intro hE hF E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie n d BM FA hH
  obtain ⟨β, b, hβ, hβn, hβz⟩ := hF E H D l Xo c Y S M.Ω (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐
  have hβ' := isMultiHomog_rename_baseInc M.blk hβ
  refine hE K ι (mCoordIdeal y) (d + 1) _ (FA.S.comap some) (FA.Re.comap some) (rename (baseInc M.blk) β)
    (extDeg M.blk b) FA.J_top FA.deg_one FA.br_empty hβ' ?_ ?_
  · rw [form_mem_mCoordIdeal_iff y hβ', aeval_rename]
    have e : y ∘ baseInc M.blk = algebraMap M.Ω Φ ∘ M.x := funext fun q => M.y_base q
    rw [e, aeval_algebraMap_apply]
    intro h0
    apply hβn
    rw [form_mem_mCoordIdeal_iff M.x hβ]
    exact (algebraMap M.Ω Φ).injective (by rw [h0, map_zero])
  · intro x hx
    have hx' : FA.pr (FA.Re.π x) ∈ ReciprocityTheory.AnForm.P.bdry BM.s := by
      have : FA.S.s (FA.Re.π x) (FA.Re.π x) = 0 := hx
      rw [FA.s_eq] at this
      exact this
    set xb := FA.pr (FA.Re.π x)
    have hmem : BM.Rb.lift xb xb ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem xb xb (BM.Rb.mem_U xb)
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).1 hmem
    have hnot : ¬ 𝔐.Interior z := fun hI => ((hH.interior xb z hz).2 hI) hx'
    have h0 : Cmp.evC (BM.Rb.lift xb xb) β = 0 := hβz z _ hz hnot
    obtain ⟨c₀, -, hc⟩ := FA.pr_eq x
    show Cmp.evC (FA.Re.R.lift x x) (rename (baseInc M.blk) β) = 0
    rw [evC_rename_baseInc, hc]
    unfold Cmp.evC at h0 ⊢
    rw [eval_smul_homog β b hβ c₀, h0, mul_zero]

end SquareStatements
end
end

section

noncomputable section

namespace SquareStatements

open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem smooth_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (Top.combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  refine contDiffOn_prod fun j _ => ?_
  rcases n j with m | m
  · simpa using (h j).pow m
  · simp only [zpow_negSucc]
    exact ((h j).pow (m + 1)).inv fun z hz => (pow_pos ((ℓ j).pos z hz) _).ne'

theorem stXB : StX := by
  intro Ψ _ _ N K _ ι _ P e S Re sing h0 hd hc
  classical
  let cl : ℝ → ℝ := fun t => if 0 < t ∧ t ≤ S.t₀ then t else S.t₀
  have hcl : ∀ t, 0 < cl t ∧ cl t ≤ S.t₀ := fun t => by
    by_cases h : 0 < t ∧ t ≤ S.t₀
    · simp only [cl, if_pos h]; exact h
    · simp only [cl, if_neg h]; exact ⟨h0, le_rfl⟩
  refine ⟨fun t r => Top.combLine (fun a => Re.line a (cl t)) (Cmp.rootOnFund r), fun t r => ?_,
    fun t r => smooth_comb _ _ fun a => Re.line_smooth a _ (hcl t).1 (hcl t).2, fun t r z => ?_, ?_⟩
  · funext k
    have h1 : ∀ a, (Re.line a (cl t)).a k = -∑ m ∈ Finset.Iic a.2, (sing (a.1, m)).a k := fun a => by
      rw [Re.line_deg, hd]
      show (∑ r, _ • (sing r).a) k = _
      rw [RootFieldNumerics.Sq.sum_fundOnRoot]
      simp [Finset.sum_apply]
    have h2 := RootFieldNumerics.Sq.sum_root_fund r fun r' => ((sing r').a k : ℝ)
    show (∑ a, Cmp.rootOnFund r a • (Re.line a (cl t)).a) k = _
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, h1, smul_eq_mul]
    simp only [zsmul_eq_mul] at h2
    exact_mod_cast h2
  · show ∏ a, _ = ∏ a, _
    exact Finset.prod_congr rfl fun a _ => by rw [hc a (cl t) z]
  · filter_upwards [Ioo_mem_nhdsGT h0] with t ht r z _
    have : cl t = t := if_pos ⟨ht.1, ht.2.le⟩
    rw [this]

end SquareStatements
end
end
