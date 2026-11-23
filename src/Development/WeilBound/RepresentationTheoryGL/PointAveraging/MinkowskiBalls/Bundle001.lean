module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002

@[expose] public section

section

open MeasureTheory GlobalTheory.SplitWeil ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n r : ℕ}

theorem ballM_mono_loc {c c' : kˣ} (h : valuation k (c : k) ≤ valuation k (c' : k))
    (x : Matrix (Fin n) (Fin r) k) : ballM c x ⊆ ballM c' x :=
  fun _ hy i l => (hy i l).trans h

theorem mem_ballM_self_loc (c : kˣ) (x : Matrix (Fin n) (Fin r) k) : x ∈ ballM c x := by
  intro i l
  simp

theorem isCompact_support_SB (Φ : SB (Matrix (Fin n) (Fin r) k)) :
    IsCompact (Function.support Φ.1) := by
  obtain ⟨hlc, hcs⟩ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  refine IsCompact.of_isClosed_subset hcs ?_ (subset_tsupport _)
  have h := (hlc.isClopen_fiber 0).isOpen
  rw [← isOpen_compl_iff]
  convert h using 1
  ext x
  simp [Function.mem_support]

theorem loc (hB : BallSt) : LocSt := by
  intro k _ _ _ _ n r P Φ hΦ
  obtain ⟨hball, hsmall, hdec⟩ := hB k n r
  have hpick : ∀ x : {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ,
      ∀ Ψ : SB (Matrix (Fin n) (Fin r) k),
        (∀ y, (Ψ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0 →
          y ∈ ballM c x.1 ∧ (Φ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0) → Ψ ∈ P := by
    intro x
    obtain ⟨U, hU, hxU, hP⟩ := hΦ x.1 x.2
    obtain ⟨c, -, hc⟩ := hsmall x.1 U (hU.mem_nhds hxU)
    exact ⟨c, fun Ψ hΨ => hP Ψ fun y hy => ⟨hc (hΨ y hy).1, (hΨ y hy).2⟩⟩
  choose cs hcs using hpick
  obtain ⟨t, ht⟩ := (isCompact_support_SB Φ).elim_finite_subcover
    (fun x => ballM (cs x) x.1) (fun x => (hball (cs x) x.1).1)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, mem_ballM_self_loc _ _⟩)
  obtain ⟨c₀, hc₀⟩ := hdec Φ
  have hmin : ∀ s : Finset {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ,
      valuation k (c : k) ≤ valuation k (c₀ : k) ∧
        ∀ i ∈ s, valuation k (c : k) ≤ valuation k (cs i : k) := by
    intro s
    classical
    refine Finset.induction_on s ⟨c₀, le_rfl, by simp⟩ ?_
    intro a s _ ih
    obtain ⟨c, hc1, hc2⟩ := ih
    rcases le_total (valuation k (c : k)) (valuation k (cs a : k)) with h | h
    · refine ⟨c, hc1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h
      · exact hc2 i hi
    · refine ⟨cs a, h.trans hc1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_rfl
      · exact h.trans (hc2 i hi)
  obtain ⟨c, hcc₀, hcci⟩ := hmin t
  obtain ⟨S, hS, hsum⟩ := hc₀ c hcc₀
  have hind : ∀ x, ((ballM c x).indicator fun _ => (1 : ℂ)) ∈ SB (Matrix (Fin n) (Fin r) k) :=
    fun x => (hball c x).2.2.1
  have hterm : ∀ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x •
      (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) ∈ P := by
    intro x hx
    have hx0 : (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0 := (hS x hx x (mem_ballM_self_loc c x)).2
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht (show x ∈ Function.support (Φ : Matrix (Fin n) (Fin r) k → ℂ) from hx0))
    have hsub : ballM c x ⊆ ballM (cs i) i.1 := by
      rw [← (hball (cs i) i.1).2.2.2.1 x hxi]
      exact ballM_mono_loc (hcci i hi) x
    apply P.smul_mem
    apply hcs i
    intro y hy
    have hy' : y ∈ ballM c x := by
      by_contra hn
      exact hy (by simp [Set.indicator, hn])
    exact ⟨hsub hy', by rw [(hS x hx y hy').1]; exact hx0⟩
  have hΦeq : Φ = ∑ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x •
      (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) := by
    apply Subtype.ext
    refine hsum.trans ?_
    simp [Submodule.coe_sum, Submodule.coe_smul]
  rw [hΦeq]
  exact P.sum_mem hterm

end PositivityTheory.Rg.Ming
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3
open scoped Topology Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.Rg.Ming.UniqX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valSet_eq (a : k) (c : kˣ) :
    {y : k | valuation k (y - a) ≤ valuation k (c : k)} = (fun y => -a + y) ⁻¹' (c • (𝒪[k] : Set k)) := by
  ext y
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]; simp
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, Valuation.mem_integer_iff, Units.smul_def,
    Units.val_inv_eq_inv_val, smul_eq_mul, map_mul, map_inv₀, neg_add_eq_sub, inv_mul_le_one₀ hc]

theorem isOpen_valSet (a : k) (c : kˣ) : IsOpen {y : k | valuation k (y - a) ≤ valuation k (c : k)} := by
  rw [valSet_eq]
  exact (Valuation.isOpen_integer.smul c).preimage (continuous_const.add continuous_id)

theorem vol_valSet [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (a : k) (c : kˣ) :
    ν {y : k | valuation k (y - a) ≤ valuation k (c : k)} = ENNReal.ofReal (nabs k c) := by
  obtain ⟨hH, h1⟩ := hν
  haveI := hH
  haveI : SecondCountableTopology k := by exact secondCountable k
  rw [valSet_eq, measure_preimage_add, ← distribHaarChar_mul, h1, mul_one, nabs, ENNReal.ofReal_coe_nnreal]

variable {n r : ℕ}

theorem ballM_eq_pi (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    (ballM c x₀ : Set (Matrix (Fin n) (Fin r) k)) =
      (Set.univ.pi fun i => Set.univ.pi fun l => {y : k | valuation k (y - x₀ i l) ≤ valuation k (c : k)} :
        Set (Fin n → Fin r → k)) := by
  ext x
  simp only [ballM, Set.mem_setOf_eq]
  constructor
  · intro h i _ l _
    exact h i l
  · intro h i l
    exact h i (Set.mem_univ _) l (Set.mem_univ _)

theorem measurableSet_ballM [MeasurableSpace k] [BorelSpace k] (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    MeasurableSet (ballM c x₀) := by
  rw [ballM_eq_pi]
  exact MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun l => (isOpen_valSet _ c).measurableSet

theorem volM_ballM [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) :
    volM ν (Fin n) (Fin r) (ballM c x₀) = ∏ _i : Fin n, ∏ _l : Fin r, ENNReal.ofReal (nabs k c) := by
  obtain ⟨hH, h1⟩ := hν
  haveI := hH
  haveI : SecondCountableTopology k := by exact secondCountable k
  rw [volM, ballM_eq_pi]
  erw [Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.pi_pi]
  exact Finset.prod_congr rfl fun l _ => vol_valSet ν ⟨hH, h1⟩ (x₀ i l) c

theorem volM_ballM_ne_zero [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) : (volM ν (Fin n) (Fin r) (ballM c x₀)).toReal ≠ 0 := by
  have hpos : 0 < nabs k c := by
    unfold nabs
    have h : distribHaarChar k c * distribHaarChar k c⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hne : distribHaarChar k c ≠ 0 := left_ne_zero_of_mul_eq_one h
    exact_mod_cast pos_iff_ne_zero.2 hne
  rw [volM_ballM ν hν, ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
  rw [ENNReal.toReal_ofReal hpos.le]
  exact hpos.ne'

theorem integral_ind [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    ∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r) =
      ((volM ν (Fin n) (Fin r) (ballM c x₀)).toReal : ℂ) := by
  rw [integral_indicator_const _ (measurableSet_ballM c x₀)]
  simp [Measure.real]

theorem ballM_mono {c c' : kˣ} (hle : valuation k (c : k) ≤ valuation k (c' : k))
    {x₀ : Matrix (Fin n) (Fin r) k} : ballM c x₀ ⊆ ballM c' x₀ :=
  fun _ hx i l => (hx i l).trans hle

theorem exists_le_both (c₁ c₂ : kˣ) :
    ∃ c : kˣ, valuation k (c : k) ≤ valuation k (c₁ : k) ∧ valuation k (c : k) ≤ valuation k (c₂ : k) := by
  rcases le_total (valuation k (c₁ : k)) (valuation k (c₂ : k)) with h | h
  · exact ⟨c₁, le_rfl, h⟩
  · exact ⟨c₂, h, le_rfl⟩

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem germ_zero [MeasurableSpace k] (ν : Measure k) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V)
    (x₀ : Matrix (Fin n) (Fin r) k) : IsGerm ν B x₀ 0 0 :=
  ⟨1, fun Φ _ => by simp⟩

theorem germ_comb [MeasurableSpace k] (ν : Measure k) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V)
    (x₀ : Matrix (Fin n) (Fin r) k) (a : ℂ) {w₁ w₂ : W} {v₁ v₂ : V}
    (h₁ : IsGerm ν B x₀ w₁ v₁) (h₂ : IsGerm ν B x₀ w₂ v₂) : IsGerm ν B x₀ (a • w₁ + w₂) (a • v₁ + v₂) := by
  obtain ⟨c₁, e₁⟩ := h₁
  obtain ⟨c₂, e₂⟩ := h₂
  obtain ⟨c, hc₁, hc₂⟩ := exists_le_both c₁ c₂
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [map_add (f := _), map_smul, e₁ Φ (fun x hx => ballM_mono hc₁ (hΦ x hx)),
    e₂ Φ (fun x hx => ballM_mono hc₂ (hΦ x hx)), smul_add, smul_comm a]

theorem germ_unique (hb : BallSt) [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν)
    (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (x₀ : Matrix (Fin n) (Fin r) k) {w : W} {v₁ v₂ : V}
    (h₁ : IsGerm ν B x₀ w v₁) (h₂ : IsGerm ν B x₀ w v₂) : v₁ = v₂ := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  obtain ⟨c, hle₁, hle₂⟩ := exists_le_both c₁ c₂
  let Φ : SB (Matrix (Fin n) (Fin r) k) :=
    ⟨(ballM c x₀).indicator fun _ => (1 : ℂ), ((hb k n r).1 c x₀).2.2.1⟩
  have hsupp : ∀ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0 → x ∈ ballM c x₀ := by
    intro x hx
    by_contra h
    exact hx (by simp [Φ, Set.indicator, h])
  have e₁ := hc₁ Φ fun x hx => ballM_mono hle₁ (hsupp x hx)
  have e₂ := hc₂ Φ fun x hx => ballM_mono hle₂ (hsupp x hx)
  have hI : (∫ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ∂volM ν (Fin n) (Fin r)) ≠ 0 := by
    change (∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r)) ≠ 0
    rw [integral_ind]
    exact Complex.ofReal_ne_zero.2 (volM_ballM_ne_zero ν hν c x₀)
  exact smul_right_injective V hI (e₁.symm.trans e₂)

end PositivityTheory.Rg.Ming.UniqX

namespace PositivityTheory.Rg.Ming

open PositivityTheory.Rg.Ming.UniqX in
theorem uniq : BallSt → UniqSt := by
  intro hb
  unfold UniqSt
  intro k _ _ _ _ _ _ ν hν n r V _ _ W _ _ B x₀ hex
  choose f hf using hex
  have hadd : ∀ w₁ w₂ : W, f (w₁ + w₂) = f w₁ + f w₂ := by
    intro w₁ w₂
    have h := germ_comb ν B x₀ 1 (hf w₁) (hf w₂)
    rw [one_smul, one_smul] at h
    exact germ_unique hb ν hν B x₀ (hf (w₁ + w₂)) h
  have hsmul : ∀ (a : ℂ) (w : W), f (a • w) = a • f w := by
    intro a w
    have h := germ_comb ν B x₀ a (hf w) (germ_zero ν B x₀)
    rw [add_zero, add_zero] at h
    exact germ_unique hb ν hν B x₀ (hf (a • w)) h
  refine ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, fun w v => ?_⟩
  constructor
  · intro h
    exact germ_unique hb ν hν B x₀ h (hf w)
  · rintro rfl
    exact hf w

end PositivityTheory.Rg.Ming

end
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem idem_eq_eMat (r t : ℕ) : idem k r (r + t) r = GlobalTheory.GodementJacquet.eMat k r t := by
  ext i l
  simp [idem, GlobalTheory.GodementJacquet.eMat]

theorem rank_eq_of_ne {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : SB (Matrix (Fin (r + t)) (Fin r) k))
    (hΦ : ∀ x : Matrix (Fin (r + t)) (Fin r) k, x.rank < r → Φ.1 x = 0)
    (x : Matrix (Fin (r + t)) (Fin r) k) (hx : Φ.1 x ≠ 0) : x.rank = r := by
  have h1 : x.rank ≤ r := by
    simpa using Matrix.rank_le_width x
  have h2 : ¬ x.rank < r := fun h => hx (hΦ x h)
  omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rep_inv_apply {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin n) k) W) (h : GL (Fin n) k) (w : W) : π h (π h⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

end PositivityTheory.Rg.Ming

namespace PositivityTheory.Rg.Ming

theorem nz : BallSt → LocSt → NfSt → NzSt := by
  intro hball hloc hnf k _ _ _ _ _ _ ν hν r t μ V _ _ W _ _ σ π B hEq hG Φ hΦ
  ext w
  show B Φ w = 0
  set e := GlobalTheory.GodementJacquet.eMat k r t with he
  have key := hloc k (r + t) r (LinearMap.ker (B.flip w)) Φ
  have hmem := key ?_
  · simpa using hmem
  intro x hx
  have hrk := rank_eq_of_ne (V := V) (W := W) Φ hΦ x hx
  obtain ⟨⟨H, G, hxHG⟩, -⟩ := hnf k (r + t) r r x hrk
  rw [idem_eq_eMat] at hxHG
  obtain ⟨c, hc⟩ := hG (π H⁻¹ w)
  let f : Matrix (Fin (r + t)) (Fin r) k → Matrix (Fin (r + t)) (Fin r) k :=
    fun z => (H⁻¹ : GL (Fin (r + t)) k).val * z * (G⁻¹ : GL (Fin r) k).val
  have hf : Continuous f := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨f ⁻¹' ballM c e, ((hball k (r + t) r).1 c e).1.preimage hf, ?_, ?_⟩
  · show f x ∈ ballM c e
    have : f x = e := by
      simp only [f, hxHG, ← Matrix.mul_assoc]
      rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [this]
    exact fun i l => by simp
  · intro Ψ hΨ
    obtain ⟨Ψ', hΨ'def⟩ : ∃ Ψ' : SB (Matrix (Fin (r + t)) (Fin r) k),
        Ψ'.1 = om μ G H⁻¹ Ψ.1 :=
      ⟨⟨_, om_mem_SB μ _ _ Ψ.2⟩, rfl⟩
    have hΨΨ' : (Ψ : Matrix (Fin (r + t)) (Fin r) k → ℂ) = om μ G⁻¹ H Ψ'.1 := by
      show Ψ.1 = _
      rw [hΨ'def, ← om_mul, inv_mul_cancel, mul_inv_cancel, om_one]
    have hsupp : ∀ y, Ψ'.1 y ≠ 0 → y ∈ ballM c e := by
      intro y hy
      rw [hΨ'def] at hy
      simp only [om, inv_inv] at hy
      have h2 := (hΨ _ (right_ne_zero_of_mul hy)).1
      have h3 : f (H.val * y * G.val) = y := by
        simp only [f, ← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      simpa [Set.mem_preimage, h3] using h2
    have h1 := hEq G⁻¹ H Ψ' Ψ hΨΨ' (π H⁻¹ w)
    rw [rep_inv_apply] at h1
    show B Ψ w = 0
    rw [h1, hc Ψ' hsupp, smul_zero, map_zero]

end PositivityTheory.Rg.Ming
end
