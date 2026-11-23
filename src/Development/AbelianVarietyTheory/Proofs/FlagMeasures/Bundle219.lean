module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle204
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle208
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle141
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle214
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairInnerLatticeIndicesAndGenerators
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RefLatticeStabilizerMiddleBottomLayers
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightGapBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle205
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerSetEqRangeNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoordinatesInverseFirstColumnInfiniteGL
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramEqGramDetProjectionNormalForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableTranslatedLatticeFunctions
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.mirabolicConjInvariant_eq_sum_induced_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (n : ℕ) (F : Gn g n → ℂ), 1 ≤ n → IsMirClass F → ∀ p : Gn g n, InMir (p : Mt g n) → F p = ∑ i ∈ Finset.range n, indR ψ i n (der ψ i F) p := by
  first | exact @GlobalTheory.GLm.MirSum.eq_sum_indR_der | exact GlobalTheory.GLm.MirSum.eq_sum_indR_der | (intros; apply GlobalTheory.GLm.MirSum.eq_sum_indR_der <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Stab

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] in
theorem smul_eq (a : 𝓞 K) (v : V) : a • v = (a : K) • v := (algebraMap_smul K a v).symm

theorem cancel {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) {M : Submodule (𝓞 K) V} {v : V}
    (h : ∀ a ∈ J, a • v ∈ J • M) : v ∈ M := by
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  obtain ⟨J', hJ'⟩ : J ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc)
  have h1 : J • Submodule.span (𝓞 K) {v} ≤ J • M := by
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (h a ha)
  have h2 : Ideal.span {c} • Submodule.span (𝓞 K) {v} ≤ Ideal.span {c} • M := by
    rw [hJ', mul_comm, Submodule.mul_smul, Submodule.mul_smul]
    exact Submodule.smul_mono le_rfl h1
  have h3 := h2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c)
    (Submodule.mem_span_singleton_self v))
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨m, hm, hmv⟩ := h3
  rw [smul_eq, smul_eq] at hmv
  have hc1 : (c : K) ≠ 0 := by exact_mod_cast hc0
  rwa [← smul_right_injective V hc1 hmv]

theorem exists_mul {M : Submodule (𝓞 K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ M := by
  first
  | exact @_root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem
  | exact _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem
  | (apply _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsSmulMemLattice.exists_smul_mem ..)

variable [StarRing K]


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isom_of_mem {H : HermSpace K V} {r : ℕ} {F F' : FlagD H r} {s : V ≃ₗ[K] V}
    (hs : s ∈ Subgroup.closure {s : V ≃ₗ[K] V | F.InN (s : V →ₗ[K] V) ∧ F'.InN (s : V →ₗ[K] V)}) :
    s ∈ isomGrp H :=
  (Subgroup.closure_le (k := {t : V ≃ₗ[K] V | F.InN (t : V →ₗ[K] V) ∧ F'.InN (t : V →ₗ[K] V)}) (isomGrp H)).2 (fun t ht =>
    (mem_isomGrp H t).2 ht.1.1) hs


omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem le_perp_perp (H : HermSpace K V) (S : Submodule K V) : S ≤ perp H (perp H S) := by
  intro x hx
  rw [mem_perp_iff]
  intro y hy
  rw [← H.herm, (mem_perp_iff H S y).1 hy x hx, star_zero]

end GlobalTheory.DegCnt.Stab


open GlobalTheory.DegCnt.Stab in
theorem GlobalTheory.DegCnt.stab_of_deep_congruence : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → ∀ s ∈ N.Rs, (∀ x ∈ N.P0, s x - x ∈ 𝔠 ^ (3 * e + 10) • N.P0) → s • Λ = Λ := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 h0 h1 h2 h3 e hsp hn s hs hcong
  have hkill := (GlobalTheory.T.hermFramePair_ideal_kills_discriminantModules K V H hK r N g Λ hg hΛ 𝔠 h0 h1 h2 h3).1
  have hcompl : IsCompl N.Wt N.Pi := (GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).2.2.1
  have hiso := (mem_isomGrp H s).1 (isom_of_mem hs.1)
  have hfix : ∀ w ∈ N.Wt, s w = w := fun w hw =>
    (mem_fixingSubgroup_iff (V ≃ₗ[K] V)).1 hs.2 w hw
  have hdual : dual H Λ = Λ := hΛ.1.1.2
  have hspan : Submodule.span K (Λ : Set V) = ⊤ := hΛ.1.1.1.2
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := fun x hx =>
    ((mem_dual_iff H Λ x).1 (hdual.symm ▸ hx)).2
  have hIP : II N.F N.F' ≤ N.Pi :=
    (inf_le_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))).trans
      (le_perp_perp H (V0 N.F N.F' ⊔ N.Ist))
  have hle : ∀ x ∈ Λ, s x ∈ Λ := by
    intro x hx
    obtain ⟨w, hw, p, hp, rfl⟩ := Submodule.mem_sup.1
      (hcompl.sup_eq_top ▸ Submodule.mem_top : x ∈ N.Wt ⊔ N.Pi)
    have hpw : ∀ y ∈ N.Wt, H.B p y = 0 := (mem_perp_iff H N.Wt p).1 hp
    have hwd : w ∈ dual H (latTh N.F N.F' Λ) := by
      rw [hsp, mem_dual_iff]
      constructor
      · obtain ⟨d, hd, hdw⟩ := exists_mul (M := Λ) (v := w) (hspan ▸ Submodule.mem_top)
        have hd1 : (d : K) ≠ 0 := by exact_mod_cast hd
        have hw' : w = (d : K)⁻¹ • (d • w) := by rw [smul_eq, smul_smul, inv_mul_cancel₀ hd1, one_smul]
        rw [hw']
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        exact Submodule.mem_sup_left ⟨hdw, (rs (𝓞 K) N.Wt).smul_mem d hw⟩
      · intro y hy
        obtain ⟨θ, hθ, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
        have e1 : H.B w i = 0 := by
          rw [← H.herm, (mem_perp_iff H N.Wt i).1 (hIP hi) w hw, star_zero]
        have e2 := hint _ hx θ hθ.1
        rw [map_add (f := _), LinearMap.add_apply, hpw θ hθ.2, add_zero] at e2
        rw [map_add (f := _), e1, add_zero]
        exact e2
    have hap : ∀ a ∈ 𝔠 ^ 3, a • p ∈ Λ ⊓ rs (𝓞 K) N.Pi := by
      intro a ha
      have := hkill (Submodule.smul_mem_smul ha hwd)
      rw [hsp] at this
      obtain ⟨θ, hθ, i, hi, h⟩ := Submodule.mem_sup.1 this
      have hiW : i ∈ N.Wt := by
        have : i = a • w - θ := by rw [← h]; abel
        rw [this]
        exact (rs (𝓞 K) N.Wt).sub_mem ((rs (𝓞 K) N.Wt).smul_mem a hw) hθ.2
      have hi0 : i = 0 := (Submodule.disjoint_def.1 hcompl.disjoint) i hiW (hIP hi)
      refine ⟨?_, (rs (𝓞 K) N.Pi).smul_mem a hp⟩
      have : a • p = a • (w + p) - θ := by rw [smul_add, ← h, hi0]; abel
      rw [this]
      exact Λ.sub_mem (Λ.smul_mem a hx) hθ.1
    have hbp : ∀ b ∈ 𝔠 ^ (e + 3), b • p ∈ N.P0 := by
      intro b hb
      rw [pow_add] at hb
      refine Submodule.mul_induction_on hb (fun m hm n hn' => ?_) (fun m n hm hn' => ?_)
      · rw [mul_smul]
        exact hn.2 (Submodule.smul_mem_smul hm (hap n hn'))
      · rw [add_smul]; exact N.P0.add_mem hm hn'
    have hsp' : s p - p ∈ 𝔠 ^ e • N.P0 := by
      refine cancel (pow_ne_zero (e + 3) h0) fun b hb => ?_
      have := hcong _ (hbp b hb)
      rw [smul_eq, map_smul, ← smul_sub, ← smul_eq] at this
      rw [← Submodule.mul_smul, ← pow_add]
      exact Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl this
    have : s (w + p) = (w + p) + (s p - p) := by rw [map_add (f := _), hfix w hw]; abel
    rw [this]
    exact Λ.add_mem hx (hn.1 hsp').1
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y s Λ).1 hy
    exact hle x hx
  · intro x hx
    refine (Submodule.mem_smul_pointwise_iff_exists x s Λ).2 ⟨s.symm x, ?_, s.apply_symm_apply x⟩
    rw [← hdual, mem_dual_iff]
    refine ⟨hspan ▸ Submodule.mem_top, fun y hy => ?_⟩
    rw [← hiso, s.apply_symm_apply]
    exact hint x hx _ (hle y hy)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.PairNoFix

theorem encard_le_of_fibres {α β : Type} (S : Set α) (T : Set β) (f : α → β) (hf : ∀ a ∈ S, f a ∈ T)
    (c : ℝ≥0∞) (hc : ∀ b ∈ T, ((({a ∈ S | f a = b}).encard : ℕ∞) : ℝ≥0∞) ≤ c) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ ((T.encard : ℕ∞) : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const,
    ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun a : S => (⟨f a, hf a a.2⟩ : T))]
  refine ENNReal.tsum_le_tsum fun b => ?_
  rw [ENNReal.tsum_set_one]
  refine le_trans ?_ (hc b b.2)
  rw [← (Subtype.val_injective.encard_image _)]
  refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.2, congrArg Subtype.val ha⟩

theorem arith (k f : ℕ) (c e : ℝ) (hc : 0 ≤ c) (x x' D q A : ℝ) (hx : 1 ≤ x) (hx' : 1 ≤ x') (hD : 1 ≤ D)
    (hq : 0 < q) (hA : 0 ≤ A) (h : 1 ≤ q ^ (2 * k * f) * D * x * x') (m : ℕ) (hm : (m : ℝ) = e) :
    (x ^ ((k : ℝ) + c) * (x * D) ^ m) * (x' ^ ((k : ℝ) + c) * (x' * D) ^ m) * A ^ (4 * k * f) ≤
      (x * x') ^ ((k : ℝ) / 2) * (x * x' * D ^ 2) ^ (c + e) * (q ^ (k * f) * A ^ (4 * f) * D * x * x') ^ k := by
  subst hm
  have x0 : 0 < x := by linarith
  have x0' : 0 < x' := by linarith
  have D0 : 0 < D := by linarith
  have h1 : 1 ≤ (x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k := by
    have hs : ((x * x') ^ ((k : ℝ) / 2)) ^ 2 = (x * x') ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1; push_cast; ring
    have h2 : 1 ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) ^ 2 := by
      rw [mul_pow, hs]
      have : (x * x') ^ k * ((q ^ (k * f) * D) ^ k) ^ 2 = (q ^ (2 * k * f) * D * x * x') ^ k * D ^ k := by
        ring
      rw [this]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h) (one_le_pow₀ hD)
    exact (one_le_sq_iff₀ (by positivity)).1 h2
  have h3 : x ^ c * x' ^ c ≤ (x * x' * D ^ 2) ^ c := by
    rw [← Real.mul_rpow x0.le x0'.le]
    refine Real.rpow_le_rpow (by positivity) ?_ hc
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD)
  rw [Real.rpow_add x0, Real.rpow_add x0', Real.rpow_add (by positivity : 0 < x * x' * D ^ 2)]
  simp only [Real.rpow_natCast]
  calc x ^ k * x ^ c * (x * D) ^ m * (x' ^ k * x' ^ c * (x' * D) ^ m) * A ^ (4 * k * f)
      = 1 * (x ^ c * x' ^ c) * ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by ring
    _ ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) * (x * x' * D ^ 2) ^ c *
        ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by gcongr
    _ = _ := by ring

theorem main : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx'
  rcases Set.eq_empty_or_nonempty {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥} with he | ⟨p₀, hp₀, hfix⟩
  · rw [he]; simp
  have h43 := GlobalTheory.T.discriminantOrder_common_fixedLattice_embeddedData K V H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx' p₀ hp₀
  rw [hfix] at h43
  have hone : GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (⊥ : Submodule K V))
      (GlobalTheory.Mass.latIn ⊥ (fixLat p₀.1.2)) = 1 := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN
    rw [AddSubgroup.relIndex_eq_one]
    intro y _
    rw [Subsingleton.elim y 0]
    exact zero_mem _
  rw [hone, finrank_bot, Nat.sub_zero, Nat.cast_one] at h43
  have hD1 : 1 ≤ D₀ := by
    rcases Nat.eq_zero_or_pos D₀ with h | h
    · rw [h] at h43; norm_num at h43
    · exact h
  have hcf : 0 ≤ cf K := by
    unfold cf
    have : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    have := Real.logb_nonneg (b := 2) (by norm_num) this
    linarith
  have hA := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x hx
  have hB := GlobalTheory.T.encard_embedded_hermData_index_le K V H hK hPD L₀ g j D₀ hL hD hG hg x' hx'
  have hcnt := encard_le_of_fibres {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}
    ({d | IsDat H g L₀ j x d} ×ˢ {d | IsDat H g L₀ j x' d}) (fun p => (p.1, p.2.1))
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    (((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)))
    (by
      rintro ⟨d, d'⟩ ⟨hd, hd'⟩
      have h := GlobalTheory.T.card_isometries_fixing_subspace_definite_lattices_le hM K V H hK hPD ⊥ d'.1 d.1 hd'.1.1 hd.1.1
      rw [finrank_bot, Nat.sub_zero] at h
      refine le_trans (ENat.toENNReal_le.2 ?_) h
      refine Set.encard_le_encard_of_injOn (f := fun p => p.2.2) ?_ ?_
      · rintro ⟨a, b, η⟩ ⟨⟨hp, -⟩, he⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨hp.2.2.1, hp.2.2.2.1, ?_⟩
        intro y hy
        rw [(Submodule.mem_bot K).1 hy, map_zero]
      · rintro ⟨a, b, η⟩ ⟨-, he⟩ ⟨a', b', η'⟩ ⟨-, he'⟩ hη
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
        simp only at hη
        rw [hη])
  rw [Set.encard_prod, ENat.toENNReal_mul] at hcnt
  refine hcnt.trans ((mul_le_mul_left (mul_le_mul' hA hB) _).trans ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  exact arith _ _ _ _ hcf _ _ _ _ _ (by exact_mod_cast hx) (by exact_mod_cast hx') (by exact_mod_cast hD1)
    (by positivity) (by positivity) h43 _ (by push_cast; ring)

end GlobalTheory.PairNoFix
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.exists_unimodular_trace_on_middleSpace_lift : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r) (L : Submodule (𝓞 K) V), IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → ∃ HW : HermSpace K N.Wn, (∀ x y : N.Wn, HW.B x y = H.B x y) ∧ Module.finrank K N.Wn + 2 * r = Module.finrank K V ∧ GlobalTheory.HermLat.IsUnimod HW (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.DegCnt.NF.wnUnimod | exact GlobalTheory.DegCnt.NF.wnUnimod | (intros; apply GlobalTheory.DegCnt.NF.wnUnimod <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.flagPairInnerLattice_indices_and_generators : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → (idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) : ℝ) * cardB N.F N.F' Λ = delBar N.F N.F' Λ ∧ idx (latL N.F' N.F Λ) (lamOne N.F N.F' Λ) = idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) ∧ lamOne N.F N.F' Λ ≤ latL N.F N.F' Λ ⊓ latL N.F' N.F Λ ∧ idx (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ) (lamOne N.F N.F' Λ) ≤ cardB N.F N.F' Λ ∧ GenBy (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) N.j := by
  first | exact @GlobalTheory.DegCnt.InnerIndex.main | exact GlobalTheory.DegCnt.InnerIndex.main | (intros; apply GlobalTheory.DegCnt.InnerIndex.main <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.refLatticeStabilizer_middle_bottom_layers : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r), ∀ L : Submodule (𝓞 K) V, IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → N.F.z ∈ L → (∀ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) → ∀ b : Fin r, N.j ≤ b.val → ∃ ρ ∈ ipow N.𝔡 (-((r : ℤ) - b.val)) • (L ⊓ rs (𝓞 K) N.Wn), s (N.ist b) - N.ist b - ρ ∈ II N.F N.F') ∧ (∀ ρ : Fin r → V, (∀ b : Fin r, ρ b ∈ ipow N.𝔡 (-((r : ℤ) - b.val)) • (L ⊓ rs (𝓞 K) N.Wn)) → ∃ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ ∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b - ρ b ∈ II N.F N.F') ∧ (∀ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') → ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → H.B (s (N.ist b)) (N.ist a) ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) ∧ H.B (s (N.ist b)) (N.ist a) + star (H.B (s (N.ist a)) (N.ist b)) = 0) ∧ ∀ S : Fin r → Fin r → K, (∀ a b, S a b ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) ∧ S a b + star (S b a) = 0) → ∃ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ ∀ b : Fin r, N.j ≤ b.val → s (N.ist b) = N.ist b + ∑ a : Fin r, (if N.j ≤ a.val then S a b else 0) • N.F.e a.castSucc := by
  first | exact @GlobalTheory.RowStab.middle_bottom_layers | exact GlobalTheory.RowStab.middle_bottom_layers | (intros; apply GlobalTheory.RowStab.middle_bottom_layers <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.highest_weight_gap_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g₀ : ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g₀ ≤ lam a - lam b) → 2 * (n : ℝ) < g₀ → ∀ F : Matrix (Fin n) (Fin n) ℂ → (H →ₗ[ℂ] H), (∀ g ∈ UJset ε, ∀ x ∈ (kSpan ε E u).map V.subtype, F g x ∈ (kSpan ε E u).map V.subtype ∧ ∀ k₁ ∈ Kset ε, ∀ k₂ ∈ Kset ε, F (k₁ * g * k₂) x = σ k₁ (F g (σ k₂ x))) → (∀ x ∈ (kSpan ε E u).map V.subtype, ∀ y : H, SmoothOnG ε (fun g => ⟪y, F g x⟫_ℂ)) → (∀ G ∈ Vminus ε E (LamOf ε lam) u, ∀ y : H, ∀ᶠ g : UJ ε in nhds 1, ∑ a, ∑ b, Eab ε a b (fun z => ⟪y, F z (at1 G a b : V)⟫_ℂ) (umat g) = 0) → (∀ x ∈ (kSpan ε E u).map V.subtype, F 1 x = 0) → ∀ (w : List (Fin n × Fin n)), ∀ x ∈ (kSpan ε E u).map V.subtype, ∀ y : H, Eword ε w (fun g => ⟪y, F g x⟫_ℂ) 1 = 0 := by
  first | exact @GlobalTheory.Jet.Germ.germ_jet_zero | exact GlobalTheory.Jet.Germ.germ_jet_zero | (intros; apply GlobalTheory.Jet.Germ.germ_jet_zero <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.two_sided_size_function_pos_invariant_continuous : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → (∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a) ∧ (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Sg2 k r z (s * x * κ) = Sg2 k r z x) ∧ ContinuousOn (Sg2 k r z) (GG k r) ∧ ∀ x, 1 ≤ Sg2 k r z x ∧ Sg k r z x ≤ Sg2 k r z x ∧ (∀ a, lA k r z x a ≤ Sg2 k r z x ∧ (lA k r z x a)⁻¹ ≤ Sg2 k r z x) ∧ (Sg2 k r z x = 1 ∨ ∃ a, Sg2 k r z x = max (lA k r z x a) (lA k r z x a)⁻¹) := by
  first | exact @GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds | exact GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds | (intros; apply GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.commonStabilizerSet_eq_range_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → Rset k r g₀ = Set.range (rEl k r j β) ∧ IsClosedSub k r (Rset k r g₀) := by
  first | exact @GlobalTheory.Amp.rset_normal0 | exact GlobalTheory.Amp.rset_normal0 | (intros; apply GlobalTheory.Amp.rset_normal0 <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.T.exists_coordinates_inverseFirstColumn_infiniteGL : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ), 1 ≤ k → ∃ (hh : MatInf E (k + 1) → MatInf E k) (TT : MatInf E (k + 1) → VecInf E k), Measurable hh ∧ Measurable TT ∧ (∀ g, 0 < detNorm E (k + 1) g → detNorm E k (hh g) = detNorm E (k + 1) g) ∧ (∀ g γ : MatInf E (k + 1), 0 < detNorm E (k + 1) g → 0 < detNorm E (k + 1) γ → (∀ w a, γ w a 0 = if a = 0 then 1 else 0) → ∀ β : MatInf E k, (∀ w a b, β w a b = γ w a.succ b.succ) → hh (γ * g) = β * hh g ∧ ∀ w, TT (γ * g) w ᵥ* Matrix.of (β w) = TT g w + fun b => γ w 0 b.succ) ∧ ∀ (F : MatInf E k → ENNReal) (Q : VecInf E k → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable F → Measurable Q → Measurable Φ → ∫⁻ g, F (hh g) * Q (TT g) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0) ∂(haarGL E (k + 1)) = (∫⁻ x, Φ x) * (∫⁻ T, Q T) * ∫⁻ h, F h * ENNReal.ofReal (detNorm E k h) ∂(haarGL E k) := by
  first | exact @GlobalTheory.FirstColumnCoord.coordinates | exact GlobalTheory.FirstColumnCoord.coordinates | (intros; apply GlobalTheory.FirstColumnCoord.coordinates <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.flagGram_eq_gramDetProjection_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), k - 1 ≤ Module.finrank ℂ P₀ ∧ ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yj k r hj z z' g₀ (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := by
  first | exact @GlobalTheory.Amp.NormalGram.Yj_eq_gramProj | exact GlobalTheory.Amp.NormalGram.Yj_eq_gramProj | (intros; apply GlobalTheory.Amp.NormalGram.Yj_eq_gramProj <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.measurable_translatedLattice_functions : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => w (covAt E j (latAt E j Λ g))) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ g ∧ x ≠ 0}, Φ x.1) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ g) ∧ x ≠ 0}, Φ x.1) g) := by
  first
  | exact @GlobalTheory.LatMeasurable.measurable_latFun
  | intro E _ _ hE j w Φ hw hΦ Λ hΛ
    exact GlobalTheory.LatMeasurable.measurable_latFun E hE j w Φ hw hΦ Λ hΛ.toIsLattice
end
