module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle001
public import Mathlib.Combinatorics.Derangements.Finite
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmodule
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.StatementLoc
public import Mathlib.Topology.LocallyConstant.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.PadicH2Separated

theorem toZModPow_eq_iff {l : ℕ} [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    PadicInt.toZModPow r x = PadicInt.toZModPow r y ↔ ‖x - y‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero]

theorem continuous_reduction {l : ℕ} [Fact l.Prime] (r : ℕ) :
    Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 (fun x => ?_) |>.continuous
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(r : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hl] with y hy
  rw [toZModPow_eq_iff]
  simpa [dist_eq_norm] using hy

theorem continuous_of_reductions {l : ℕ} [Fact l.Prime] {X : Type} [TopologicalSpace X]
    (b : X → ℤ_[l]) (hb : ∀ s : ℕ, Continuous fun x => PadicInt.toZModPow (s + 1) (b x)) :
    Continuous b := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  have hk' : (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_le_zpow_right₀ h1 (by push_cast; omega)
  have hlc := ((IsLocallyConstant.iff_continuous _).2 (hb k)).eventually_eq x
  filter_upwards [hlc] with y hy
  rw [toZModPow_eq_iff] at hy
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hy.trans hk') hk

theorem finite_cocycles_compact_ultrametric_rep {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [Finite M] (rho : Representation R G M) [Finite (H1 rho)] : Finite (Z1 rho) := by
  have hB : Finite (B1 rho) :=
    Finite.of_surjective _ (LinearMap.surjective_rangeRestrict (d0 rho))
  have hB' : Finite ((B1 rho).comap (Z1 rho).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 rho)) (fun x y h => by
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun t : B1 rho => (t : G → M)) h)
  have h1 : Finite ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup := hB'
  have h2 : Finite (Z1 rho ⧸ ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup) :=
    inferInstanceAs (Finite (H1 rho))
  exact Finite.of_addSubgroup_quotient ((B1 rho).comap (Z1 rho).subtype).toAddSubgroup

theorem finite_primitives {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [Finite M] (rho : Representation R G M) [Finite (H1 rho)]
    (z : G × G → M) : {β : G → M | Continuous β ∧ d1 rho β = z}.Finite := by
  rcases Set.eq_empty_or_nonempty {β : G → M | Continuous β ∧ d1 rho β = z} with h | ⟨c, hc⟩
  · rw [h]; exact Set.finite_empty
  have hZ : (Z1 rho : Set (G → M)).Finite := finite_cocycles_compact_ultrametric_rep rho
  refine (hZ.image (fun f => f + c)).subset ?_
  rintro β ⟨hβ, hd⟩
  refine ⟨β - c, ⟨hβ.sub hc.1, fun g h => ?_⟩, by simp⟩
  have e : d1 rho (β - c) (g, h) = 0 := by rw [map_sub, hd, hc.2, sub_self]; rfl
  rw [d1_apply] at e
  have : (β - c) g + rho g ((β - c) h) - (β - c) (g * h) = 0 := by rw [← e]; abel
  exact (sub_eq_zero.1 this).symm

theorem mem_coboundaries_of_forall_pow : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]) (ρr : ∀ r : ℕ, Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ r g x, PadicInt.toZModPow r (ρ g x) = ρr r g (PadicInt.toZModPow r x)) → (∀ r, 0 < r → Finite (H1 (ρr r))) → ∀ z ∈ Z2 ρ, (∀ r : ℕ, ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ) → z ∈ B2 ρ := by
  intro l _ Γ _ _ ρ ρr hρ hfin z _ hz
  have hd : ∀ (s : ℕ) (b : Γ → ℤ_[l]), d1 (ρr s) (fun g => PadicInt.toZModPow s (b g)) =
      fun p => PadicInt.toZModPow s (d1 ρ b p) := by
    intro s b
    funext ⟨g, h⟩
    simp only [d1_apply, map_add (f := _), map_sub, hρ]
  let α : ∀ s : ℕ, Set (Γ → ZMod (l ^ s)) := fun s =>
    {β | Continuous β ∧ d1 (ρr s) β = fun p => PadicInt.toZModPow s (z p)}
  have hα : ∀ s, (α (s + 1)).Finite := by
    intro s
    haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    haveI := hfin (s + 1) (Nat.succ_pos s)
    exact finite_primitives (ρr (s + 1)) _
  let T : ℕ → Set (Γ → ℤ_[l]) := fun r =>
    ⋂ s, ⋂ (_ : s ≤ r), (fun (b : Γ → ℤ_[l]) g => PadicInt.toZModPow (s + 1) (b g)) ⁻¹' α (s + 1)
  have hcl : ∀ r, IsClosed (T r) := fun r =>
    isClosed_iInter fun s => isClosed_iInter fun _ => (hα s).isClosed.preimage
      (continuous_pi fun g => (continuous_reduction _).comp (continuous_apply g))
  have hne : ∀ r, (T r).Nonempty := by
    intro r
    obtain ⟨w, -, c, hc, hcd⟩ := hz (r + 1)
    refine ⟨c, Set.mem_iInter₂.2 fun s hs => ⟨(continuous_reduction _).comp hc, ?_⟩⟩
    rw [hd, hcd]
    funext p
    have h0 : PadicInt.toZModPow (s + 1) ((l : ℤ_[l]) ^ (r + 1)) = 0 := by
      rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact pow_dvd_pow _ (by omega)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, h0, zero_mul, sub_zero]
  have hdec : ∀ r, T (r + 1) ⊆ T r := fun r b hb =>
    Set.mem_iInter₂.2 fun s hs => Set.mem_iInter₂.1 hb s (hs.trans (Nat.le_succ r))
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  have hb' : ∀ s, (fun g => PadicInt.toZModPow (s + 1) (b g)) ∈ α (s + 1) := fun s =>
    Set.mem_iInter₂.1 (Set.mem_iInter.1 hb s) s le_rfl
  refine ⟨b, continuous_of_reductions b fun s => (hb' s).1, ?_⟩
  funext p
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have := (hb' n).2
    rw [hd] at this
    exact congrFun this p

end GlobalTheory.PadicH2Separated
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ z ∈ Z2 ρ, (fun p => PadicInt.toZModPow r (z p)) ∈ B2 ρr → ∃ w ∈ Z2 ρ, z - (l : ℤ_[l]) ^ r • w ∈ B2 ρ := by
  intro l _ Γ _ _ _ ρ hρ r ρr hc z hz hB
  obtain ⟨c, hcc, hcd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hB
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := l) r) := ZMod.ringHom_surjective _
  choose s hs using hsurj
  have hsc : Continuous s := continuous_of_discreteTopology
  have hb : d1 ρ (s ∘ c) ∈ B2 ρ := (separated_dvr_second_cohomology_mem _ _).2 ⟨s ∘ c, hsc.comp hcc, rfl⟩
  have hy : z - d1 ρ (s ∘ c) ∈ Z2 ρ := (Z2 ρ).sub_mem hz (coboundaries2_le_cocycles2 ρ hρ hb)
  have hdiv : ∀ p, ∃ a : ℤ_[l], (l : ℤ_[l]) ^ r * a = (z - d1 ρ (s ∘ c)) p := by
    rintro ⟨g, h⟩
    have h1 : (z - d1 ρ (s ∘ c)) (g, h) ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      have h2 := congrFun hcd (g, h)
      rw [d1_apply] at h2
      rw [RingHom.mem_ker, Pi.sub_apply, d1_apply, map_sub, map_add (f := _), map_sub, hc]
      simp only [Function.comp_apply, hs]
      rw [h2, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha.symm⟩
  choose w hw using hdiv
  have hne : (l : ℤ_[l]) ^ r ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hemb : Topology.IsClosedEmbedding (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x) :=
    Continuous.isClosedEmbedding (continuous_const.mul continuous_id)
      (mul_right_injective₀ hne)
  have hw' : (l : ℤ_[l]) ^ r • w = z - d1 ρ (s ∘ c) := funext hw
  refine ⟨w, (mem_cocycles2 _ _).2 ⟨?_, fun g h k => ?_⟩, ?_⟩
  · refine hemb.isInducing.continuous_iff.2 ?_
    have : (fun x : ℤ_[l] => (l : ℤ_[l]) ^ r * x) ∘ w = z - d1 ρ (s ∘ c) := funext hw
    rw [this]
    exact hy.1
  · have e := ((mem_cocycles2 _ _).1 hy).2 g h k
    rw [← hw'] at e
    simp only [Pi.smul_apply, map_smul] at e
    rw [← smul_sub, ← smul_add, ← smul_sub, smul_eq_mul] at e
    exact (mul_eq_zero.1 e).resolve_left hne
  · rw [hw', sub_sub_cancel]
    exact hb

end GlobalTheory
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem finrank_range_le_three (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (P a b : Module.End ℂ M) :
    Module.finrank ℂ (LinearMap.range P) ≤ Module.finrank ℂ (LinearMap.range (a * b * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - a) * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - b) * P)) := by
  have hle : LinearMap.range P ≤ (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P)) ⊔
      (LinearMap.range ((1 - b) * P)).map a := by
    rintro _ ⟨x, rfl⟩
    have hx : P x = ((a * b * P) x + ((1 - a) * P) x) + a (((1 - b) * P) x) := by
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      abel
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x))
      (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P))
    ((LinearMap.range ((1 - b) * P)).map a)
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P)) (LinearMap.range ((1 - a) * P))
  have h4 := Submodule.finrank_map_le a (LinearMap.range ((1 - b) * P))
  omega

end GlobalTheory.BadShare
end

section

open Polynomial Classical GlobalTheory.BadShare

noncomputable section
namespace GlobalTheory.BadShare

theorem trace_compLeft_funLeft {G W : Type} [Fintype G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : W →ₗ[ℂ] W) (f : G → G) :
    LinearMap.trace ℂ (G → W) (A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f) =
      ∑ x, if f x = x then LinearMap.trace ℂ W A else 0 := by
  have h : A.compLeft G ∘ₗ LinearMap.funLeft ℂ W f =
      ∑ x, LinearMap.single ℂ (fun _ : G => W) x ∘ₗ (A ∘ₗ LinearMap.proj (f x)) := by
    refine LinearMap.ext fun φ => funext fun y => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, LinearMap.funLeft_apply]

  rw [h, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [LinearMap.trace_comp_comm']
  split_ifs with hx
  · congr 1
    ext w
    simp [hx]
  · have : (A ∘ₗ LinearMap.proj (f x)) ∘ₗ LinearMap.single ℂ (fun _ : G => W) x = 0 := by
      ext w
      simp [hx]
    rw [this, map_zero]

section
variable {G : Type} [Group G] [Fintype G] {Γ : Type} [Group Γ] [Fintype Γ] (r : Γ →* G)
  {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ Γ W)

def coindSum : (G → W) →ₗ[ℂ] Representation.coindV r σ :=
  LinearMap.codRestrict _
    (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) (by
      intro φ δ x

      simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.compLeft_apply,
      Function.comp_apply, LinearMap.funLeft_apply, map_sum]
      refine Fintype.sum_equiv (Equiv.mulRight δ) _ _ fun γ => ?_
      simp only [Equiv.coe_mulRight, map_mul r, mul_assoc, mul_inv_rev]
      rw [← Module.End.mul_apply, ← map_mul σ, mul_inv_cancel_left])

omit [Fintype G] [FiniteDimensional ℂ W] in
theorem coindSum_apply (φ : G → W) (x : G) :
    (coindSum r σ φ).1 x = ∑ γ : Γ, σ γ⁻¹ (φ (r γ * x)) := by
  change (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) φ x = _
  simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]

theorem trace_coind_mul_card (g : G) :
    LinearMap.trace ℂ _ (Representation.coind r σ g) * (Fintype.card Γ : ℂ) =
      ∑ γ : Γ, ∑ x : G, if r γ * (x * g) = x then LinearMap.trace ℂ W (σ γ⁻¹) else 0 := by
  have h1 : (Fintype.card Γ : ℂ) • (Representation.coind r σ g : _ →ₗ[ℂ] _) =
      coindSum r σ ∘ₗ (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
    rw [LinearMap.comp_apply, coindSum_apply]
    have : ∀ γ : Γ, σ γ⁻¹ ((LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) φ (r γ * x))
        = φ.1 (x * g) := by
      intro γ
      change σ γ⁻¹ (φ.1 (r γ * x * g)) = _
      rw [mul_assoc, φ.2 γ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [Finset.sum_congr rfl fun γ _ => this γ, Finset.sum_const, Finset.card_univ]
    change (Fintype.card Γ : ℂ) • φ.1 (x * g) = _
    rw [Nat.cast_smul_eq_nsmul]
  have h2 : (LinearMap.funLeft ℂ W (fun x => x * g) ∘ₗ (Representation.coindV r σ).subtype) ∘ₗ coindSum r σ =
      ∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * (x * g) := by
    refine LinearMap.ext fun φ => funext fun x => ?_
    change (coindSum r σ φ).1 (x * g) = _
    rw [coindSum_apply]
    simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]

  rw [mul_comm, ← smul_eq_mul, ← map_smul, h1, LinearMap.trace_comp_comm', h2, map_sum]
  exact Finset.sum_congr rfl fun γ _ => trace_compLeft_funLeft _ _

end

end GlobalTheory.BadShare
end
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem eq_zero_of_sum_joint_eigenvectors {ι κ M : Type} [AddCommGroup M] [Module ℂ M]
    (T : κ → M →ₗ[ℂ] M) (l : ι → κ → ℂ) (hl : ∀ i j, i ≠ j → ∃ k, l i k ≠ l j k)
    (s : Finset ι) : ∀ u : ι → M, (∀ i k, T k (u i) = l i k • u i) → ∑ i ∈ s, u i = 0 →
      ∀ i ∈ s, u i = 0 := by
  first
  | exact @_root_.GlobalTheory.ComplexValueBound.main
  | exact _root_.GlobalTheory.ComplexValueBound.main
  | (apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ComplexValueBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ComplexValueBound.main ..)

theorem root_exchange : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (B X Y : Subgroup G) (χ : G → ℂ), (∀ x ∈ X, x ∈ B → x = 1) → (∀ b ∈ B, ∀ x ∈ X, ∃ x' ∈ X, ∃ b' ∈ B, b * x = x' * b' ∧ χ b' = χ b) → (∀ x ∈ X, ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ B) → (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ∃ y ∈ Y, χ (y⁻¹ * x⁻¹ * y * x) ≠ χ (y⁻¹ * x'⁻¹ * y * x')) → ∀ (n : ℕ) (v : Fin n → M), LinearIndependent ℂ v → (∀ i, (∀ b ∈ B, ρ b (v i) = χ b • v i) ∧ ∀ y ∈ Y, ρ y (v i) = v i) → ∃ w : Fin n → M, LinearIndependent ℂ w ∧ ∀ i, (∀ b ∈ B, ρ b (w i) = χ b • w i) ∧ ∀ x ∈ X, ρ x (w i) = w i := by
  intro G _ _ M _ _ _ ρ B X Y χ hXB hBX hc hsep n v hv hvi
  have hmul : ∀ (g h : G) (m : M), ρ (g * h) m = ρ g (ρ h m) := fun g h m => by
    rw [map_mul]; rfl
  let S : M →ₗ[ℂ] M := ∑ x : X, ρ (x : G)
  have hS : ∀ m, S m = ∑ x : X, ρ (x : G) m := fun m => by
    simp only [S, LinearMap.sum_apply]
  have hinj : ∀ m : M, (∀ b ∈ B, ρ b m = χ b • m) → (∀ y ∈ Y, ρ y m = m) → S m = 0 → m = 0 := by
    intro m hb hy h0
    rw [hS] at h0
    have := eq_zero_of_sum_joint_eigenvectors (ι := X) (κ := Y) (fun y => ρ (y : G))
      (fun x y => χ ((y : G)⁻¹ * (x : G)⁻¹ * y * x))
      (fun x x' hne => by
        obtain ⟨y, hyY, h⟩ := hsep x x.2 x' x'.2 (fun h => hne (Subtype.ext h))
        exact ⟨⟨y, hyY⟩, h⟩) Finset.univ (fun x => ρ (x : G) m)
      (fun x y => by
        have e : (y : G) * x = x * (y * ((y : G)⁻¹ * (x : G)⁻¹ * y * x)) := by group
        show ρ (y : G) (ρ (x : G) m) = _
        rw [← hmul, e, hmul, hmul, hb _ (hc x x.2 y y.2), map_smul, hy y y.2, map_smul]) h0
      1 (Finset.mem_univ _)
    simpa using this
  refine ⟨fun i => S (v i), ?_, fun i => ⟨fun b hb => ?_, fun x hx => ?_⟩⟩
  · rw [Fintype.linearIndependent_iff] at hv ⊢
    intro g hg
    apply hv g
    apply hinj
    · intro b hb

      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).1 b hb, smul_comm]
    · intro y hy

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).2 y hy]

    simpa only [map_sum, map_smul] using hg
  · choose f hf g hg hfg hχ using hBX b hb
    let F : X → X := fun x => ⟨f x x.2, hf x x.2⟩
    have hF : Function.Injective F := by
      intro x1 x2 h
      have h' : f x1 x1.2 = f x2 x2.2 := congrArg Subtype.val h
      have e1 := hfg x1 x1.2
      have e2 := hfg x2 x2.2
      rw [← h'] at e2
      have e : (x1 : G)⁻¹ * x2 = (g x1 x1.2)⁻¹ * g x2 x2.2 := by
        calc (x1 : G)⁻¹ * x2 = (b * x1)⁻¹ * (b * x2) := by group
          _ = _ := by rw [e1, e2]; group
      have := hXB _ (X.mul_mem (X.inv_mem x1.2) x2.2)
        (e ▸ B.mul_mem (B.inv_mem (hg x1 x1.2)) (hg x2 x2.2))
      exact Subtype.ext (inv_mul_eq_one.1 this)
    have hB : Function.Bijective F := Finite.injective_iff_bijective.1 hF
    show ρ b (S (v i)) = χ b • S (v i)

    rw [hS, map_sum, Finset.smul_sum]
    refine Fintype.sum_bijective F hB _ _ fun x => ?_
    rw [← hmul, hfg x x.2, hmul, (hvi i).1 _ (hg x x.2), hχ, map_smul]
  · show ρ x (S (v i)) = S (v i)

    rw [hS, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : X)) _ _ fun z => ?_
    rw [← hmul]; rfl

end GlobalTheory.BadShare
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem two_mul_numDerangements_succ_le (n : ℕ) :
    2 * numDerangements (n + 1) ≤ (n + 1).factorial := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [numDerangements]
  | more n h1 h2 =>
    have e : numDerangements (n + 2 + 1)
        = (n + 1 + 1) * (numDerangements (n + 1) + numDerangements (n + 1 + 1)) :=
      numDerangements_add_two (n + 1)
    have f1 : (n + 2 + 1).factorial = (n + 2 + 1) * (n + 1 + 1).factorial :=
      Nat.factorial_succ _
    have f2 : (n + 1 + 1).factorial = (n + 1 + 1) * (n + 1).factorial :=
      Nat.factorial_succ _
    rw [e, f1]
    have := Nat.mul_le_mul_left (n + 1 + 1) (Nat.add_le_add h1 h2)
    nlinarith

theorem factorial_le_two_mul_card_perm_fixed :
    ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α →
      (Fintype.card α).factorial ≤
        2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  intro α _ _ hne
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Equiv.Perm α)))
    (fun σ : Equiv.Perm α => ∃ i, σ i = i)
  rw [Finset.card_univ, Fintype.card_perm] at hsum
  have hd : (Finset.univ.filter fun σ : Equiv.Perm α => ¬ ∃ i, σ i = i).card
      = numDerangements (Fintype.card α) := by
    rw [← card_derangements_eq_numDerangements α, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    simp [derangements]
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h := two_mul_numDerangements_succ_le n
  rw [← hn] at h
  omega

end GlobalTheory.BadShare
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.divisor_descent_mod_unramified_galois_submodule : ∀ (A₀ R K₀ L : Type) [CommRing A₀] [IsDedekindDomain A₀] [CommRing R] [IsDedekindDomain R] [Field K₀] [Field L]
  [Algebra A₀ K₀] [IsFractionRing A₀ K₀] [Algebra R L] [IsFractionRing R L] [Algebra A₀ R] [Algebra K₀ L] [Algebra A₀ L]
  [IsScalarTower A₀ R L] [IsScalarTower A₀ K₀ L] [IsIntegralClosure R A₀ L] [FiniteDimensional K₀ L] [IsGalois K₀ L]
  (N : ℕ), 0 < N →
  (∀ Q : Ideal R, Q.IsPrime → Q ≠ ⊥ → ¬ Ideal.map (algebraMap A₀ R) (Q.comap (algebraMap A₀ R)) ≤ Q ^ 2) →
  (∀ c : ClassGroup A₀, ∃ d, c = d ^ N) →
  ∀ w : L, w ≠ 0 → (∀ σ : L ≃ₐ[K₀] L, ∃ u : L, u ≠ 0 ∧ σ w = w * u ^ N) →
  ∃ (f : K₀) (J : Submodule R L), f ≠ 0 ∧ J ^ N = Submodule.span R {w / algebraMap K₀ L f} := by
  first | exact @GlobalTheory.DivisorDescent.descent_submodule | exact GlobalTheory.DivisorDescent.descent_submodule | (intros; apply GlobalTheory.DivisorDescent.descent_submodule <;> assumption)
end
