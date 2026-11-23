module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle081
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle044
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Formalism.LocalRingCardinality.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle092
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem volSt_conj_self {G : Type} [Group G] (H : Subgroup G) {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

theorem volSt_inf_stab_smul {G X : Type} [Group G] [MulAction G X] (H : Subgroup G) {h : G} (hh : h ∈ H)
    (x : X) : H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  rw [Subgroup.smul_inf, volSt_conj_self H hh]
  congr 1
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, MulAction.mem_stabilizer_iff, mul_smul,
    inv_smul_eq_iff]

theorem volSt {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
    (r k : ℕ) (S : Frames L r k) :
    (∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.K0 ≠ 0 ∧ ∀ h ∈ S.St, S.mu (h • Λ) = S.mu Λ) ∧
    ∀ C, S.IsCls C → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 ∧ 1 ≤ S.wC C ∧
      ∀ h ∈ S.St, S.wC (h • C) = S.wC C := by
  obtain ⟨Λ1, hΛ1, hK0, -⟩ := GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S 1 S.N.one_mem 1 S.N'.one_mem
  have hK : S.K0 = S.St ⊓ stabL L Λ1 := hK0.symm
  have hc : ∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ stabL L Λ) ≠ 0 ∧
      (S.St ⊓ stabL L Λ).relIndex S.K0 ≠ 0 := by
    intro Λ hΛ
    rw [hK]
    exact ⟨(GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ1 hΛ hΛ1 S.St).1, (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ hΛ1 hΛ S.St).1⟩
  have hconj : ∀ h ∈ S.St, S.K0.relIndex (MulAut.conj h • S.K0) ≠ 0 ∧
      (MulAut.conj h • S.K0).relIndex S.K0 ≠ 0 := by
    intro h hh
    have e : MulAut.conj h • S.K0 = S.St ⊓ stabL L (h • Λ1) := by
      rw [hK]; exact (volSt_inf_stab_smul S.St hh Λ1).symm
    rw [e]
    exact hc _ ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ1 hΛ1 hΛ1 S.St).2 h).1
  have hle : S.K0 ≤ S.St := by rw [hK]; exact inf_le_left
  have hmod := (GlobalTheory.T.haarInvVolume_conj_modular_character S.St S.K0 hle hconj).2.2.2
  have hone : ∀ h ∈ S.St, invVol S.K0 (MulAut.conj h • S.K0) = 1 := by
    intro h hh
    obtain ⟨Λ, hΛ, hs⟩ := GlobalTheory.T.unipotent_stabilizes_some_lattice L h _ (GlobalTheory.T.pow_eq_zero_of_mem_hermitianFrameUnipotent L r k S h hh.1)
    exact (hmod _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh).2 (volSt_conj_self _ ⟨hh, hs⟩)
  have hinv : ∀ K' : Subgroup S.GLV, S.K0.relIndex K' ≠ 0 → K'.relIndex S.K0 ≠ 0 → ∀ h ∈ S.St,
      invVol S.K0 (MulAut.conj h • K') = invVol S.K0 K' := by
    intro K' h1 h2 h hh
    rw [(hmod K' h1 h2 h hh).1, hone h hh, one_mul]
  refine ⟨fun Λ hΛ => ⟨(hc Λ hΛ).1, (hc Λ hΛ).2, fun h hh => ?_⟩, ?_⟩
  · unfold Frames.mu
    rw [volSt_inf_stab_smul S.St hh Λ]
    exact hinv _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh
  rintro C ⟨n, hn, n', hn', hC⟩
  obtain ⟨Λ, hΛ, e1, e2, e3⟩ := GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S n hn n' hn'
  rw [← hC] at e2 e3
  obtain ⟨⟨K, hKm, hKi, -⟩, -⟩ := GlobalTheory.T.congruence_subgroup_lattice_stabilizer L S.ϖ S.ϖ_irr Λ hΛ 1
  have a1 : S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 :=
    fun h0 => (hc Λ hΛ).1 (Subgroup.relIndex_eq_zero_of_le_right e2 h0)
  have b1 : K.relIndex (S.St ⊓ stabL L Λ) ≠ 0 :=
    fun h0 => hKi (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  have b2 : (K ⊓ (S.St ⊓ stabL L Λ)) ≤ S.St ⊓ MulAction.stabilizer S.GLV C :=
    fun g hg => ⟨hg.2.1, e3 g hg.2 ((hKm g).1 hg.1).2⟩
  have b3 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex (S.St ⊓ stabL L Λ) ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_eq_zero_of_le_left b2 h0
    rw [Subgroup.inf_relIndex_right] at this
    exact b1 this
  have a2 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans b3 (hc Λ hΛ).2
  refine ⟨a1, a2, ?_, fun h hh => ?_⟩
  · obtain ⟨h, hh, hw, -⟩ := GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup L r k S n hn
    have c1 : S.St ⊓ MulAction.stabilizer S.GLV C ≤ MulAut.conj h • S.K0 :=
      e2.trans (e1.le.trans (inf_le_left.trans hw))
    have c2 := (invVol_mul_pos_le_conj S.K0 (MulAut.conj h • S.K0) _ (hconj h hh).1 (hconj h hh).2
      a1 a2).2.2.1 c1
    have c3 := Subgroup.relIndex_ne_zero_trans a2 (hconj h hh).1
    unfold Frames.wC
    rw [c2, hone h hh, one_mul]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 c3
  · unfold Frames.wC
    rw [volSt_inf_stab_smul S.St hh C]
    exact hinv _ a1 a2 h hh

end GlobalTheory.HL
end

section

namespace GlobalTheory.Diag.PG

theorem rankNums_first_half : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x →
    ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * m ^ 5 * f * x ^ eps ≤ k ∧
      Real.log f ≤ Real.sqrt (m / 2 - 1) ∧ C * x ^ eps ≤ f * Real.log k ∧ C * (m ^ 2 * x ^ eps) ≤ k ∧ C ≤ m ∧
      C * x ^ eps ≤ m - 1 ∧ C ≤ k ∧ 1 < x ^ eps := by
  intro eps CD heps heps' _ C
  set C1 : ℝ := max C 2 with hC1
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hC12 : 2 ≤ C1 := le_max_right _ _
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, C1 ≤ x ^ (eps / 2) :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop C1
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, C1 + 1 ≤ x ^ ((1 : ℝ) / 52) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop (C1 + 1)
  have e3 : ∀ᶠ x : ℝ in Filter.atTop, (200 : ℝ) ≤ x ^ ((1 : ℝ) / 16) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 200
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x := Filter.eventually_ge_atTop 2
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and e4)))
  refine ⟨x0, fun x hx m f k lrd Del h => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hx0 x hx
  have hx0' : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  set A := x ^ eps with hA
  have hA1 : 1 < A := Real.one_lt_rpow hx1 heps
  set y := x ^ ((1 : ℝ) / 52) with hy
  have hAy : A ≤ y := Real.rpow_le_rpow_of_exponent_le hx1.le heps'.le
  set q := x ^ ((1 : ℝ) / 4) with hq
  have hqy : q = y ^ (13 : ℕ) := by
    rw [hq, hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
  have hy1 : 1 ≤ y := by linarith
  have hy13 : y ^ 2 ≤ y ^ (13 : ℕ) := pow_le_pow_right₀ hy1 (by norm_num)
  have hq_big : C1 * A + 1 ≤ q := by
    rw [hqy]; nlinarith
  have hm : C1 * A + 1 ≤ m := le_trans hq_big h.m_lo
  have hm1 : 1 ≤ m := by nlinarith
  have hm3 : 3 ≤ m := by nlinarith
  have hm4 : m ≤ m ^ 4 := by
    calc m = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hf : m ≤ f := le_trans hm4 h.mf
  have hf1 : 1 ≤ f := by linarith
  have hk : m ≤ k := le_trans hf h.fk
  have hCA : C * A ≤ C1 * A := mul_le_mul_of_nonneg_right hCC1 (by linarith)
  have hB0 : 0 ≤ m ^ 5 * f * A := by positivity
  have hk1 : C1 * (m ^ 5 * f * A) ≤ k :=
    le_trans (mul_le_mul_of_nonneg_right h1 hB0) h.k_lo
  have hm25 : m ^ 2 ≤ m ^ 5 * f := by
    have : m ^ 2 ≤ m ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
    nlinarith
  have hlogk : 1 ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hC1A : C1 ≤ C1 * A := by
    have := mul_le_mul_of_nonneg_left hA1.le (by linarith : (0:ℝ) ≤ C1)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hA1⟩
  · have : C * (m ^ 5 * f * A) ≤ C1 * (m ^ 5 * f * A) := mul_le_mul_of_nonneg_right hCC1 hB0
    calc C * m ^ 5 * f * A = C * (m ^ 5 * f * A) := by ring
      _ ≤ k := le_trans this hk1
  ·
    set t := x ^ ((1 : ℝ) / 16) with ht
    have hqt : q = t ^ (4 : ℕ) := by
      rw [hq, ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0']; norm_num
    have hf0 : 0 < f := by linarith
    have hlf : Real.log f ≤ 5 * Real.log x := by
      have : Real.log f ≤ Real.log (x ^ (5 : ℝ)) :=
        Real.log_le_log hf0 (le_trans h.fk h.k_hi)
      rw [Real.log_rpow (by linarith)] at this
      exact this
    have hlx : Real.log x ≤ t / (1 / 16) := Real.log_le_rpow_div hx0' (by norm_num)
    have h80 : 80 * t ≤ Real.sqrt (m / 2 - 1) := by
      rw [Real.le_sqrt (by linarith)]
      have hmq : t ^ (4 : ℕ) ≤ m := hqt ▸ h.m_lo
      have ht2 : 40000 ≤ t ^ 2 := by nlinarith
      have ht4 : t ^ (4 : ℕ) = t ^ 2 * t ^ 2 := by ring
      have : (80 * t) ^ 2 = 6400 * t ^ 2 := by ring
      nlinarith
      all_goals linarith
    have : 5 * Real.log x ≤ 80 * t := by
      have : t / (1 / 16) = 16 * t := by ring
      linarith
    linarith
  · calc C * A ≤ C1 * A := hCA
      _ ≤ m := by linarith
      _ ≤ f := hf
      _ = f * 1 := (mul_one f).symm
      _ ≤ f * Real.log k := mul_le_mul_of_nonneg_left hlogk (by linarith)
  · have hB2 : 0 ≤ m ^ 2 * A := by positivity
    calc C * (m ^ 2 * A) ≤ C1 * (m ^ 2 * A) := mul_le_mul_of_nonneg_right hCC1 hB2
      _ ≤ C1 * (m ^ 5 * f * A) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_right hm25 (by linarith)
      _ ≤ k := hk1
  · linarith
  · linarith
  · linarith

end GlobalTheory.Diag.PG
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.HypPrimVec

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem hconj (x y : S.V) : star (S.hT x y) = S.hT y x :=
  LinearMap.isSymm_def.mp S.herm x y

theorem mem_dual_iff (Λ : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ ↔ ∀ y ∈ Λ, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]

theorem mem_of_dual {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x : S.V}
    (h : ∀ y ∈ Λ, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x) : x ∈ Λ := by
  have hx : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := (mem_dual_iff Λ x).2 h
  rwa [hU] at hx

theorem pair_mem {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x y : S.V}
    (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x := by
  have hx' : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU]; exact hx
  exact (mem_dual_iff Λ x).1 hx' y hy

end

theorem exists_primitive_norm_neg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], CMData F E → ∀ (S : HSpace E) (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∃ x : 𝓞 E, (x : E) + star (x : E) = 1) → ∀ (e f : S.V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → S.hT e e = 0 → S.hT f f = 0 → S.hT e f = 1 → (∀ x ∈ c, x • e ∈ Λ) → (∀ y ∈ Λ, S.hT f y ∈ c) → ∀ T : ℕ, T ≠ 0 → ∃ z : S.V, z ∈ Submodule.span E {e, f} ∧ z ∈ Λ ∧ S.hT z z = -((T : ℕ) : E) ∧ ∀ γ : E, γ • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = γ := by
  intro F E _ _ _ _ _ _ hcm S Λ hU hx e f c hc hee hff hef hce hfc T hT
  obtain ⟨x, hx⟩ := hx

  have hσ : ∀ r : 𝓞 E, ((RingOfIntegers.mapRingHom (starRingEnd E) r : 𝓞 E) : E) = star (r : E) :=
    fun r => rfl
  have hTne : (T : 𝓞 E) ≠ 0 := by
    intro h
    apply hT
    have h' := congrArg (fun r : 𝓞 E => (r : E)) h
    simpa using h'

  obtain ⟨P, hP0, hPP, ⟨t, p0, hp0, htp⟩, α, hα⟩ := GlobalTheory.T.exists_ideal_coprime_conj_mul_eq_spanSingleton' F E hcm c hc (T : 𝓞 E) hTne
  have htpE : (t : E) * (T : E) + (p0 : E) = 1 := by
    have h' := congrArg (fun r : 𝓞 E => (r : E)) htp
    simpa using h'

  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1
    (show (1 : 𝓞 E) ∈ P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) by
      rw [hPP]; exact Submodule.mem_top)
  have hq' : RingOfIntegers.mapRingHom (starRingEnd E) q ∈ P := Ideal.mem_comap.1 hq
  have hpqE : (p : E) + (q : E) = 1 := by
    have h' := congrArg (fun r : 𝓞 E => (r : E)) hpq
    simpa using h'
  set w : 𝓞 E := p * x + RingOfIntegers.mapRingHom (starRingEnd E) q *
    RingOfIntegers.mapRingHom (starRingEnd E) x with hw
  have hwP : w ∈ P := P.add_mem (P.mul_mem_right _ hp) (P.mul_mem_right _ hq')
  have hwE : (w : E) + star (w : E) = 1 := by
    have e1 : (w : E) = (p : E) * x + star (q : E) * star (x : E) := by
      rw [hw]; push_cast; rfl
    have hs : star (p : E) + star (q : E) = 1 := by rw [← star_add, hpqE, star_one]
    rw [e1, star_add, star_mul', star_mul', star_star, star_star]
    linear_combination (x : E) * hpqE + star (x : E) * hs + hx

  have hPc : ∀ r ∈ P, ∀ s ∈ c, ∃ o : 𝓞 E, (o : E) * α = (r : E) * s := by
    intro r hr s hs
    have hm : (r : E) * s ∈ (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c :=
      FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩) hs
    rw [hα, FractionalIdeal.mem_spanSingleton] at hm
    obtain ⟨o, ho⟩ := hm
    exact ⟨o, by rw [← ho, Algebra.smul_def]⟩
  have hαc : α ∈ c := by
    have h1 : α ∈ (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
      rw [hα]; exact FractionalIdeal.mem_spanSingleton_self _ _
    have hle : (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c ≤ c :=
      FractionalIdeal.mul_le.2 fun i hi j hj => by
        obtain ⟨r, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        rw [← Algebra.smul_def]
        exact (c : Submodule (𝓞 E) E).smul_mem r hj
    exact hle h1
  have hα0 : α ≠ 0 := by
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    obtain ⟨s, hs, hs0⟩ : ∃ s ∈ c, s ≠ 0 := by
      by_contra h
      push_neg at h
      apply hc
      ext y
      simp only [FractionalIdeal.mem_zero_iff]
      exact ⟨h y, fun hy => hy ▸ (c : Submodule (𝓞 E) E).zero_mem⟩
    obtain ⟨o, ho⟩ := hPc r hr s hs
    intro h0
    rw [h0, mul_zero] at ho
    have hr0' : (r : E) ≠ 0 := by exact_mod_cast hr0
    exact mul_ne_zero hr0' hs0 ho.symm
  have hfe : S.hT f e = 1 := by rw [← hconj e f, hef, star_one]

  set b : E := star (-(T : E) * (w : E) / α) with hb
  have h1 : star α * b = -(T : E) * star (w : E) := by
    rw [hb, ← star_mul', show α * (-(T : E) * (w : E) / α) = -(T : E) * w by field_simp,
      star_mul', star_neg, star_natCast]
  have h2 : star b * α = -(T : E) * (w : E) := by
    rw [hb, star_star]; field_simp
  refine ⟨α • e + b • f, ?_, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · refine Λ.add_mem (hce α hαc) (mem_of_dual hU fun y hy => ?_)
    obtain ⟨o, ho⟩ := hPc w hwP (S.hT f y) (hfc y hy)
    refine ⟨-(T : 𝓞 E) * RingOfIntegers.mapRingHom (starRingEnd E) o, ?_⟩
    have key : -(T : E) * w / α * S.hT f y = -(T : E) * o := by
      calc -(T : E) * w / α * S.hT f y = -(T : E) * ((w : E) * S.hT f y) / α := by ring
        _ = -(T : E) * ((o : E) * α) / α := by rw [ho]
        _ = -(T : E) * o := by field_simp
    rw [LinearMap.map_smul, ← hconj f y, smul_eq_mul, hb, ← star_mul', key, star_mul', star_neg,
      star_natCast]
    show ((-(T : 𝓞 E) * RingOfIntegers.mapRingHom (starRingEnd E) o : 𝓞 E) : E) = _
    push_cast
    rfl
  · simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.map_smul, smul_eq_mul, hee, hff, hef, hfe, mul_zero, mul_one, zero_add, add_zero,
      starRingEnd_apply]
    linear_combination h1 + h2 - (T : E) * hwE
  · intro γ hγ
    have hfz : S.hT f (γ • (α • e + b • f)) = γ * α := by
      simp only [map_add (f := _), LinearMap.map_smul, smul_eq_mul, hff, hfe, RingHom.id_apply]; ring
    have hγα : γ * α ∈ c := hfz ▸ hfc _ hγ
    obtain ⟨o1, ho1⟩ := hPc p0 hp0 _ hγα
    obtain ⟨o2, ho2⟩ := hPc w hwP _ hγα
    obtain ⟨o3, ho3⟩ := pair_mem hU hγ (hce α hαc)
    have E1 : (o1 : E) = p0 * γ := mul_right_cancel₀ hα0 (by rw [ho1]; ring)
    have E2 : (o2 : E) = w * γ := mul_right_cancel₀ hα0 (by rw [ho2]; ring)
    have E3 : (o3 : E) = -(T : E) * γ * star (w : E) := by
      have hez : S.hT (α • e) (γ • (α • e + b • f)) = γ * (star α * b) := by
        simp only [map_add (f := _), LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul,
          smul_eq_mul, hee, hef, starRingEnd_apply, RingHom.id_apply]; ring
      rw [hez, h1] at ho3
      change (o3 : E) = _ at ho3
      rw [ho3]; ring
    refine ⟨o2 + (-t * o3 + RingOfIntegers.mapRingHom (starRingEnd E) w * o1), ?_⟩
    have hcast : ((o2 + (-t * o3 + RingOfIntegers.mapRingHom (starRingEnd E) w * o1) : 𝓞 E) : E) =
        (o2 : E) + (-(t : E) * o3 + star (w : E) * o1) := by
      push_cast; rfl
    rw [hcast]
    linear_combination E2 - (t : E) * E3 + star (w : E) * E1 + γ * star (w : E) * htpE + γ * hwE

end GlobalTheory.HypPrimVec
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem congruence_normal_finite_index : ∀ (I : AutInst), (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ IsOpen (I.Kg g) ∧ (∀ x ∈ I.Kset, ∀ y ∈ I.Kg g, x * y * x⁻¹ ∈ I.Kg g) ∧ ∃ s : Finset I.Gf, ∀ x ∈ I.Kset, ∃ t ∈ s, t⁻¹ * x ∈ I.Kg g := by
  intro I
  obtain ⟨-, -, -, hKc, -, hK, hg⟩ := GlobalTheory.CongTop.adelic_topology I
  refine ⟨hK, fun g hg1 => ?_⟩
  obtain ⟨hKgo, ⟨H, hH⟩, hnorm⟩ := hg g hg1
  refine ⟨⟨H, hH⟩, hKgo, hnorm, ?_⟩

  have hopen : ∀ t ∈ I.Kset, IsOpen {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := fun t _ =>
    hKgo.preimage (continuous_const_mul t⁻¹)
  have hsub : I.Kset ⊆ ⋃ t ∈ I.Kset, {x : I.Gf | t⁻¹ * x ∈ I.Kg g} := by
    intro x hx
    refine Set.mem_biUnion hx ?_
    show x⁻¹ * x ∈ I.Kg g
    rw [inv_mul_cancel, ← hH]
    exact H.one_mem
  obtain ⟨b, -, hb, hcov⟩ := hKc.elim_finite_subcover_image hopen hsub
  refine ⟨hb.toFinset, fun x hx => ?_⟩
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcov hx)
  exact ⟨t, hb.mem_toFinset.mpr ht, hxt⟩

end GlobalTheory.CongTop
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem adelicStab_isCompact_isOpen :
    ∀ (I : AutInst), IsCompact I.Kset ∧ IsOpen I.Kset ∧ LocallyCompactSpace I.Gf ∧ T2Space I.Gf := by
  intro I
  obtain ⟨h1, h2, -, h4, h5, -⟩ := GlobalTheory.CongTop.adelic_topology I
  exact ⟨h4, h5, h2, h1⟩

end GlobalTheory
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem exists_haar_sigmaFinite :
    ∀ (I : AutInst), ∃ μf : Measure I.Gf, μf.IsHaarMeasure ∧ SigmaFinite μf := by
  intro I
  obtain ⟨_, _, _, -⟩ := GlobalTheory.CongTop.adelic_topology I
  exact ⟨Measure.haar, inferInstance, inferInstance⟩

end GlobalTheory.CongTop
end

section

open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.finiteAdelicUnitary_congruenceTopology : ∀ I : AutInst, T2Space I.Gf ∧ LocallyCompactSpace I.Gf ∧ SecondCountableTopology I.Gf ∧ IsCompact I.Kset ∧ IsOpen I.Kset ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → IsOpen (I.Kg g) ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ ∀ k ∈ I.Kset, ∀ x ∈ I.Kg g, k * x * k⁻¹ ∈ I.Kg g := by
  first | exact @GlobalTheory.CongTop.adelic_topology | exact GlobalTheory.CongTop.adelic_topology | (intros; apply GlobalTheory.CongTop.adelic_topology <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem secondCountable_finiteAdelicPoints : ∀ (I : AutInst), SecondCountableTopology I.Gf :=
  fun I => (adelic_topology I).2.2.1

end GlobalTheory.CongTop
end
