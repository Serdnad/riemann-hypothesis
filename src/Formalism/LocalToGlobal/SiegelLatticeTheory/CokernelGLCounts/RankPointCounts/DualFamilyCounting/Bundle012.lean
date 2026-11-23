module

public import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartRightInverse
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle025
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle032
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle030
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

def ExpChart : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1 =
    ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) •
      (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map (fun t => WlocSk.NB.phi0 t.1 t.2)

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G2

open Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem jK_ι (t : 𝓞 F) : jK (ι t) = algebraMap F K (t : F) := rfl

theorem jK_ι_ne_zero {t : 𝓞 F} (ht : t ≠ 0) : jK (ι t) ≠ 0 := by
  rw [jK_ι]
  exact (map_ne_zero_iff _ (algebraMap F K).injective).2 (RingOfIntegers.coe_ne_zero_iff.2 ht)

theorem ne_zero_of_notMem {𝔭 : Ideal (𝓞 F)} {t : 𝓞 F} (ht : t ∉ 𝔭) : t ≠ 0 := by
  rintro rfl
  exact ht 𝔭.zero_mem

theorem exists_inv_mod {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) (e : ℕ) :
    ∃ u : 𝓞 F, 1 - t * u ∈ 𝔭 ^ e := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨y * ∑ k ∈ Finset.range e, i ^ k, ?_⟩
  have h1 : t * (y * ∑ k ∈ Finset.range e, i ^ k) = 1 - i ^ e := by
    rw [← mul_neg_geom_sum, ← hyi]
    ring
  rw [h1, sub_sub_cancel]
  exact Ideal.pow_mem_pow hi e

theorem exists_mul_mem_span {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ x ∈ 𝔭 ^ vF 𝔭 a, t * x ∈ Ideal.span {a} := by
  have hle : Ideal.span {a} ≤ 𝔭 ^ vF 𝔭 a :=
    (Ideal.span_singleton_le_iff_mem _).2 (localValuationFiltration.mem_pow_vF h𝔭 ha)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJp : ¬ J ≤ 𝔭 := by
    intro hJ𝔭
    apply localValuationFiltration.notMem_pow_vF h𝔭 ha
    have : Ideal.span {a} ≤ 𝔭 ^ (vF 𝔭 a + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hJ𝔭
    exact this (Ideal.mem_span_singleton_self a)
  obtain ⟨t, htJ, ht𝔭⟩ := IsConcreteLE.not_le_iff_exists.1 hJp
  refine ⟨t, ht𝔭, fun x hx => ?_⟩
  rw [hJ, mul_comm t x]
  exact Ideal.mul_mem_mul hx htJ

theorem div_mem_SP_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) (z : 𝓞 K) :
    haveI := h𝔭.isPrime
    jK z / jK (ι a) ∈ HU.SP K 𝔭 ↔ z ∈ extP K 𝔭 ^ vF 𝔭 a := by
  have := h𝔭.isPrime
  have ha' := jK_ι_ne_zero (K := K) ha
  rw [HU.mem_SP]
  constructor
  · rintro ⟨t, ht, w, hw⟩
    have e1 : ι t * z = w * ι a := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_mul, map_mul, hw, mul_assoc, div_mul_cancel₀ _ ha']
    obtain ⟨u, hu⟩ := exists_inv_mod h𝔭 ht (vF 𝔭 a)
    have hA : ι a ∈ extP K 𝔭 ^ vF 𝔭 a := localizedQuotients.ι_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 ha)
    have e2 : z = ι u * (ι t * z) + ι (1 - t * u) * z := by
      rw [map_sub, map_mul, map_one]
      ring
    rw [e2, e1]
    exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hA))
      (Ideal.mul_mem_right _ _ (localizedQuotients.ι_mem_pow hu))
  · intro hz
    obtain ⟨t, ht, htx⟩ := exists_mul_mem_span h𝔭 ha
    refine ⟨t, ht, ?_⟩
    have hle : Ideal.span {ι t} * extP K 𝔭 ^ vF 𝔭 a ≤ Ideal.span {ι a} := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro y hy
      unfold extP at hy
      rw [← Ideal.map_pow] at hy
      refine Submodule.span_induction (p := fun y _ => ι t * y ∈ Ideal.span {ι a}) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (htx x hx)
        rw [← map_mul, ← hc, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · simp
      · intro x y _ _ hx hy
        rw [mul_add]
        exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [smul_eq_mul, mul_left_comm]
        exact Ideal.mul_mem_left _ _ hx
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1
      (hle (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz))
    refine ⟨w, ?_⟩
    rw [← mul_div_assoc]
    exact (eq_div_iff ha').2 (by simpa only [map_mul] using congrArg jK hw)

theorem exists_sub_div_mem_SP {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {a : 𝓞 F} (ha : a ≠ 0) {r : K}
    (hr : haveI := h𝔭.isPrime; r ∈ HU.SP K 𝔭) :
    haveI := h𝔭.isPrime
    ∃ z : 𝓞 K, (r - jK z) / jK (ι a) ∈ HU.SP K 𝔭 := by
  have := h𝔭.isPrime
  obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 hr
  obtain ⟨u, hu⟩ := exists_inv_mod h𝔭 ht (vF 𝔭 a)
  refine ⟨ι u * w, ?_⟩
  have h1 : jK (ι (1 - t * u)) / jK (ι a) ∈ HU.SP K 𝔭 :=
    (div_mem_SP_iff h𝔭 ha _).2 (localizedQuotients.ι_mem_pow hu)
  have e : (r - jK (ι u * w)) / jK (ι a) = r * (jK (ι (1 - t * u)) / jK (ι a)) := by
    rw [map_mul, hw, map_sub, map_mul, map_one, map_sub, map_mul, map_one]
    ring
  rw [e]
  exact Subring.mul_mem _ hr h1

theorem star_jK (w : 𝓞 K) : ∃ w' : 𝓞 K, jK w' = star (jK w) := StandardSymmetricSums.star_int w

theorem star_jK_ι (hF : IsFixF K F) (t : 𝓞 F) : star (jK (ι t)) = jK (ι t) :=
  (hF _).2 ⟨(t : F), rfl⟩

end Formalism.L2.SG.Pf.G2
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.ProjectionDiscriminantModule

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_of_isLatIn {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : IsLatIn X L) :
    ∀ x ∈ L, x ∈ X := fun x hx => hL.2 ▸ Submodule.subset_span hx

theorem isLattice_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : IsLatIn X A) (hB : IsLatIn Y B) : Submodule.IsLattice K (A ⊔ B) :=
  Submodule.IsLattice.of_fg K (hA.1.sup hB.1)

theorem prO_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ y ∈ B, y ∈ Y) {z : V} (hz : z ∈ A ⊔ B) : prO hc z ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
  rw [map_add (f := _), prO_apply, prO_apply, Submodule.projection_apply_of_mem_left hc (hA a ha),
    (Submodule.projection_apply_eq_zero_iff hc).2 (hB b hb), add_zero]
  exact ha

theorem prO_locF {X Y : Submodule K V} (hc : IsCompl X Y) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime)
    {A B : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ y ∈ B, y ∈ Y) {z : V}
    (hz : z ∈ locF 𝔭 (A ⊔ B)) : prO hc z ∈ locF 𝔭 A := by
  obtain ⟨t, ht, htz⟩ := (LocF.mem_locF_iff hp _ z).1 hz
  refine (LocF.mem_locF_iff hp _ _).2 ⟨t, ht, ?_⟩
  rw [← LinearMap.map_smul]
  exact prO_sup hc hA hB htz

theorem discMod_finite [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    (hc : IsCompl U (orthK h U)) {M T Λ₀ N₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M) (hT : IsLatIn (orthK h U) T)
    (hN₀ : Submodule.IsLattice K N₀) (hΛ₀ : locF 𝔭 N₀ = Λ₀)
    (hW : Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T)
    (hiW : ∀ x ∈ Λ₀, prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T))
    (hpr : ∀ v ∈ locF 𝔭 (dualIn h (orthK h U) T), ∃ x ∈ Λ₀, prO hc.symm x = v) :
    Finite (DiscMod h (orthK h U) T 𝔭) := by
  subst hΛ₀
  have hp := h𝔭.isPrime
  have hTM : Submodule.IsFullLattice K (T ⊔ M) := by
    refine { toIsLattice := isLattice_sup hc.symm hT hM, span_eq_top := ?_ }
    rw [eq_top_iff, ← hc.symm.sup_eq_top, ← hT.2, ← hM.2]
    exact sup_le
      (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
      (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right))
  obtain ⟨r, hr⟩ := LIOrb.exists_pow_smul_le hN₀ hTM h𝔭
  have hsurj := toDisc_surj h hc.symm T (locF 𝔭 N₀) 𝔭 hiW hpr
  have hker : ((extP K 𝔭) ^ r • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 N₀)) ≤
      LinearMap.ker (toDisc h hc.symm T (locF 𝔭 N₀) 𝔭 hiW) := by
    rw [Submodule.smul_le]
    intro a ha y _
    rw [mem_ker_toDisc]
    have h1 : a • (y : V) ∈ locF 𝔭 (T ⊔ M) := hr (Submodule.smul_mem_smul ha y.2)
    exact prO_locF hc.symm hp (mem_of_isLatIn hT) (mem_of_isLatIn hM) h1
  haveI := LIOrb.finite_quot hN₀ h𝔭 r
  refine Finite.of_surjective (((extP K 𝔭) ^ r • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 N₀)).liftQ
    (toDisc h hc.symm T (locF 𝔭 N₀) 𝔭 hiW) hker) ?_
  intro d
  obtain ⟨y, rfl⟩ := hsurj d
  exact ⟨Submodule.Quotient.mk y, Submodule.liftQ_apply _ _ _⟩

theorem exists_lattice_locF {Λ L₁ L₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hL₁ : Submodule.IsFullLattice K L₁) (hL₂ : L₂.FG) (hΛ : locF 𝔭 Λ = Λ) (h1 : L₁ ≤ Λ)
    (h2 : Λ ≤ locF 𝔭 L₂) : ∃ Λ', Submodule.IsLattice K Λ' ∧ locF 𝔭 Λ' = Λ := by
  refine ⟨(L₁ ⊔ L₂) ⊓ Λ, ⟨(hL₁.fg.sup hL₂).of_le inf_le_left, ?_⟩, ?_⟩
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · have e := LIOrb.IA.locF_inf 𝔭 h𝔭.isPrime (L₁ ⊔ L₂) Λ
    rw [hΛ] at e
    rw [e]
    exact le_antisymm inf_le_right (le_inf (h2.trans (LocF.locF_mono 𝔭 le_sup_right)) le_rfl)

end Formalism.L2.SG.Pf.ProjectionDiscriminantModule
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_splitting_exists : JordanExists := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs
  exact ⟨fun X L hnd hL hLi 𝔭 h𝔭 => G1.jordan_exists hK hF hs X L hnd hL hLi 𝔭 h𝔭,
    fun L _ 𝔭 h𝔭 b a hJ => G1.vd_eq_vJof hK hF L 𝔭 h𝔭 b a hJ⟩

end Formalism.L2.SG.Pf.Cnt
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def ProjInto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ x ∈ Λ, X.projection Y hc x ∈ locF 𝔭 (dualIn h X L)

def ProjOnto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ v ∈ locF 𝔭 (dualIn h X L), ∃ x ∈ Λ, X.projection Y hc x = v

def FibCount : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M T : Submodule (𝓞 K) V, IsLatIn U M → IsLatIn (orthK h U) T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      fibP h U 𝔭 M T ≠ 0 → fibP h U 𝔭 M T = discAut h (orthK h U) T 𝔭

end Formalism.L2.SG.Pf.G6

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6

theorem glueLoc_of (hi : ProjInto) (ho : ProjOnto) (hn : FibCount) : GlueLoc := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭
  refine ⟨fun hne => ⟨?_, hn K F V hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭 hne⟩,
    fun g hg => fibP_gmap hM 𝔭 T hg⟩
  obtain ⟨⟨Λ, hΛ0, hΛd, hΛU, hΛW⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have oU : ∀ x ∈ U, ∀ y ∈ orthK h U, h x y = 0 := fun x hx y hy => mem_orthK.mp hy x hx
  have oW : ∀ x ∈ orthK h U, ∀ y ∈ U, h x y = 0 := by
    intro x hx y hy
    have e := hs.eq x y
    rw [oU y hy x hx] at e
    simpa using e
  exact discIso_of_proj h hcU hΛU hΛW
    (hi K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (ho K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (hi K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)
    (ho K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)

end Formalism.L2.SG.Pf.Cnt
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def IsGlueDataPre {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) {n m : ℕ} (a : Fin n → 𝓞 F)
    (π : 𝓞 F) (w : Fin m → V) (c : Fin m → F) (τ : Fin n → Fin m) : Prop :=
  (∀ j, w j ∈ orthK h U) ∧ (∀ j k, j ≠ k → h (w j) (w k) = 0) ∧
  (∀ j, h (w j) (w j) = algebraMap F K (c j) ∧ c j ≠ 0) ∧
  (∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) ∧
  (∃ s₀ : 𝓞 F, IsUnif0 𝔭 π s₀) ∧
  (∀ i, vF 𝔭 (a i) ≠ 0 →
    InP 𝔭 (2 * vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i)))) ∧
  (∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m) ∧
  (∀ j : Fin m, (j : ℕ) + 1 < m → (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) →
    InP 𝔭 0 (algebraMap F K (c j)) ∧ InP 𝔭 0 (algebraMap F K (c j)⁻¹))

def GlueVecsPre : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
      ∃ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
        (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ

def LastRescale : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ →
      ∃ (w' : Fin (finrank K (orthK h U)) → V) (c' : Fin (finrank K (orthK h U)) → F),
        IsGlueData h U 𝔭 a π w' c' τ

theorem glueVecs_of (h1 : GlueVecsPre) (h2 : LastRescale) : GlueVecs := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  obtain ⟨π, w, c, τ, hg⟩ := h1 K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  obtain ⟨w', c', hg'⟩ := h2 K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg
  exact ⟨π, w', c', τ, hg'⟩

end Formalism.L2.SG.Pf.GluingBases
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def aaLbS (b : Fin D.R.rS) : Submodule (𝓞 D.host.E) (VS D).V :=
  Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}

def TrDetUnimod : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (b : Fin D.R.rS) {N : ℕ}
    (m : Module.Basis (Fin N) ℤ ((aaLbS X b).restrictScalars ℤ)),
    N = Module.finrank ℚ D.host.E * (D.R.k + 1) →
    |(Matrix.of fun i j => Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V))).det| =
      |(discr D.host.E : ℚ)| ^ (D.R.k + 1) * (FractionalIdeal.absNorm (aaD D b) : ℚ) ^ (2 * (D.R.k + 1))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end
