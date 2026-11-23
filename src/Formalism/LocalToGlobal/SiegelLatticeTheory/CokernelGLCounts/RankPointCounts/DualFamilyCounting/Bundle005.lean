module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomScale
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

section Transport

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def resF (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : W →ₗ⋆[K] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y)
    (fun x x' y => by simp) (fun c x y => by simp) (fun x y y' => by simp) (fun c x y => by simp)

@[simp] theorem resF_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) (x y : W) :
    resF h W x y = h x y := rfl

abbrev incO (W : Submodule K V) : W →ₗ[𝓞 K] V := W.subtype.restrictScalars (𝓞 K)

abbrev latW (W : Submodule K V) (T : Submodule (𝓞 K) V) : Submodule (𝓞 K) W := T.comap (incO W)

theorem map_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) :
    (latW W T).map (incO W) = T := by
  rw [Submodule.map_comap_eq, inf_eq_right]
  intro x hx
  exact ⟨⟨x, hT.2 ▸ Submodule.subset_span hx⟩, rfl⟩

theorem incO_injective (W : Submodule K V) : Function.Injective (incO W) := Subtype.val_injective

theorem isLattice_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) :
    Submodule.IsFullLattice K (latW W T) := by
  have hfg : (latW W T).FG :=
    Submodule.fg_of_fg_map_injective _ (incO_injective W) (by rw [map_latW hT]; exact hT.1)
  refine { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := ?_ }
  apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
  have himg : (Subtype.val '' ((latW W T : Submodule (𝓞 K) W) : Set W)) = (T : Set V) := by
    have e := congrArg (fun S : Submodule (𝓞 K) V => (S : Set V)) (map_latW hT)
    simpa [Submodule.map_coe] using e
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Submodule.coe_subtype, himg, hT.2]

private lemma mem_of_algebraMap_smul_mem (W : Submodule K V) {t : 𝓞 F} (ht : t ≠ 0) {x : V}
    (h : algebraMap (𝓞 F) (𝓞 K) t • x ∈ W) : x ∈ W := by
  have hs : algebraMap (𝓞 F) (𝓞 K) t ≠ 0 := fun h0 =>
    ht (NumberField.RingOfIntegers.algebraMap.injective F K (h0.trans (map_zero _).symm))
  have hsK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact_mod_cast hs
  rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x] at h
  have h2 := W.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hsK, one_smul] at h2

private lemma map_incO_locF (W : Submodule K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime]
    (A : Submodule (𝓞 K) W) : (locF 𝔭 A).map (incO W) = locF 𝔭 (A.map (incO W)) := by
  ext x
  simp only [Submodule.mem_map, Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]
  constructor
  · rintro ⟨y, ⟨t, ht, hy⟩, rfl⟩
    exact ⟨t, ht, _, hy, by simp⟩
  · rintro ⟨t, ht, z, hz, hzx⟩
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have hxW : x ∈ W := by
      apply mem_of_algebraMap_smul_mem W ht0
      rw [← hzx]
      exact z.2
    refine ⟨⟨x, hxW⟩, ⟨t, ht, ?_⟩, rfl⟩
    convert hz using 1
    exact Subtype.ext hzx.symm

theorem locF_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) (𝔭 : Ideal (𝓞 F))
    [𝔭.IsPrime] : (locF 𝔭 (latW W T)).map (incO W) = locF 𝔭 T := by
  rw [map_incO_locF, map_latW hT]

theorem isJordanIn_res {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {T : Submodule (𝓞 K) V}
    (hT : IsLatIn W T) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {b : Fin (finrank K W) → V} {a : Fin (finrank K W) → 𝓞 F}
    (hb : IsJordanIn h W T 𝔭 b a) :
    IsJordanIn (resF h W) ⊤ (latW W T) 𝔭
      (fun i => ⟨b (finCongr (finrank_top K W) i), hb.1 _⟩) (fun i => a (finCongr (finrank_top K W) i)) := by
  obtain ⟨hbW, hloc, horth, hdiag, hne⟩ := hb
  refine ⟨fun i => Submodule.mem_top, ?_, ?_, ?_, fun i => hne _⟩
  · apply Submodule.map_injective_of_injective (incO_injective W)
    have himg : ⇑(incO W) '' Set.range (fun i : Fin (finrank K (⊤ : Submodule K W)) =>
        (⟨b (finCongr (finrank_top K W) i), hbW _⟩ : W)) = Set.range b := by
      ext v
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨_, ⟨(finCongr (finrank_top K W)).symm i, rfl⟩, by simp⟩
    rw [map_incO_locF, locF_latW hT, Submodule.map_span, himg, hloc]
  · intro i j hij
    simp only [resF_apply]
    exact horth _ _ ((finCongr (finrank_top K W)).injective.ne hij)
  · intro i
    simp only [resF_apply]
    exact hdiag _

end Transport

end Formalism.L2.SG.Pf.G8
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

private lemma mem_locF_lemma {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F))
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma star_fix_lemma_2 (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    star (algebraMap (𝓞 K) K s) = algebraMap (𝓞 K) K s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, -, rfl⟩ := hx
    exact (hF _).mpr ⟨(t : F), rfl⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, star_mul', hx, hy]

private lemma smul_smul_lemma_3 (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {𝔭 : Ideal (𝓞 F)} {s t : 𝓞 K}
    (ht : t ∈ Submonoid.closure {s : 𝓞 K | ∃ u : 𝓞 F, u ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) u = s})
    (x y : V) : h (t • y) (s • x) = (t * s) • h y x := by
  rw [← algebraMap_smul K t y, ← algebraMap_smul K s x]
  simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, starRingEnd_apply]
  rw [star_fix_lemma_2 hF ht, Algebra.smul_def, map_mul]
  ring

theorem locF_dual_le (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) ≤ dualF h 𝔭 (locF 𝔭 L) := by
  intro x hx
  change ∀ y ∈ locF 𝔭 L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
  obtain ⟨t, ht, hty⟩ := (mem_locF_lemma 𝔭 _ y).mp hy
  refine (mem_locF_lemma 𝔭 _ _).mpr ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [← smul_smul_lemma_3 hF h ht x y]
  exact (mem_dual_iff h L (s • x)).mp hsx (t • y) hty

theorem dualF_locF_le (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : L.FG)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : dualF h 𝔭 (locF 𝔭 L) ≤ locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) := by
  classical
  intro x hx
  have hx' : ∀ y ∈ locF 𝔭 L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  obtain ⟨G, rfl⟩ := hL
  have hg : ∀ g ∈ G, ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      s • h g x ∈ (1 : Submodule (𝓞 K) K) := fun g hg =>
    (mem_locF_lemma 𝔭 _ _).mp (hx' g ((mem_locF_lemma 𝔭 _ g).mpr
      ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span hg⟩))
  choose! sg hsg hsgx using hg
  refine (mem_locF_lemma 𝔭 _ _).mpr
    ⟨∏ g ∈ G, sg g, Submonoid.prod_mem _ fun g hg => hsg g hg, ?_⟩
  rw [mem_dual_iff]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [← algebraMap_smul K (∏ g ∈ G, sg g) x, LinearMap.map_smul, smul_eq_mul]
    have e : algebraMap (𝓞 K) K (∏ g ∈ G, sg g) * h y x =
        (∏ g ∈ G.erase y, sg g) • (sg y • h y x) := by
      rw [← Finset.mul_prod_erase G sg hy, Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (hsgx y hy)
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
    rw [← algebraMap_smul K c y, map_smulₛₗ h (algebraMap (𝓞 K) K c) y, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, ← hr, ← smul_eq_mul, algebraMap_smul]
    exact Submodule.smul_mem _ r hy

theorem locF_dual (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : L.FG)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) = dualF h 𝔭 (locF 𝔭 L) := le_antisymm (locF_dual_le hF h L hp) (dualF_locF_le h hL hp)

private lemma ne_zero_lemma_4 {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
    rw [e]
    exact (map_ne_zero _).mpr (by simpa using ht0)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_ne_zero hx hy

theorem locF_subspace (U : Submodule K V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    locF 𝔭 (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) := by
  ext x
  rw [mem_locF_lemma]
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := ne_zero_lemma_4 hs
    have e : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
      rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e]
    exact U.smul_mem _ hsx
  · intro hx
    exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

private lemma mem_image_lemma_5 {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, (Ideal.ne_top_iff_one 𝔭).mp hp.ne_top, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a * b, fun hab => (hp.mem_or_mem hab).elim ha hb, map_mul _ _ _⟩

private lemma le_of_locF_lemma_6 (A B : Submodule (𝓞 K) V)
    (hAB : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → locF 𝔭 A = locF 𝔭 B) : A ≤ B := by
  intro x hx
  let J : Ideal (𝓞 F) :=
    Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (B.comap (LinearMap.toSpanSingleton (𝓞 K) V x))
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, hmax, hle⟩ := Ideal.exists_le_maximal J hne
    have hxA : x ∈ locF 𝔭 A :=
      (mem_locF_lemma 𝔭 A x).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
    rw [hAB 𝔭 hmax] at hxA
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 B x).mp hxA
    obtain ⟨t, ht, rfl⟩ := mem_image_lemma_5 hmax.isPrime hs
    exact ht (hle (show t ∈ J from hsx))
  have h1 : (1 : 𝓞 F) ∈ J := by rw [hJ]; exact Submodule.mem_top
  simpa [J] using h1

theorem eq_of_locF (A B : Submodule (𝓞 K) V)
    (hAB : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → locF 𝔭 A = locF 𝔭 B) : A = B := le_antisymm (le_of_locF_lemma_6 A B hAB) (le_of_locF_lemma_6 B A fun 𝔭 h => (hAB 𝔭 h).symm)

end Formalism.L2.SG.Pf.G7
end
end

section

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem unit_ne {a : K} {k : ℕ} (hu : IsUnitIn S (a * (π ^ k)⁻¹)) : a ≠ 0 := by
  intro ha
  apply hu.1
  rw [ha, zero_mul]

private theorem mem_iff_lemma {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i := Iff.rfl

theorem spanS_empty {ι : Type} [Fintype ι] [IsEmpty ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ v = 0 := by
  rw [mem_iff_lemma]
  constructor
  · rintro ⟨c, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨0, fun _ => S.zero_mem, by simp⟩

theorem mem_spanS_self {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → V) (i : ι) :
    b i ∈ spanS S b := by
  refine (mem_iff_lemma b (b i)).2 ⟨fun j => if j = i then 1 else 0, fun j => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · simp [ite_smul]

theorem core_empty {ι : Type} [Fintype ι] [IsEmpty ι] (b b' : ι → V) {φ : V ≃ₗ[K] V}
    (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ Submodule.span K (Set.range b), h w v = 0) → g v = φ v) ∧
      ∀ v, v ∈ spanS S b ↔ g v ∈ spanS S b' := by
  refine ⟨φ, hφ, fun v _ => rfl, fun v => ?_⟩
  rw [spanS_empty b v, spanS_empty b' (φ v)]
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    apply φ.injective
    rw [h0, map_zero]

private theorem span_ne_eq_cutW_of_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι] {f : ι → V}
    (ho : ∀ i j, i ≠ j → h (f i) (f j) = 0) {i₀ : ι} (hf0 : h (f i₀) (f i₀) ≠ 0) :
    Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => f i)) =
      cutW h (Submodule.span K (Set.range f)) (f i₀) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show f i ∈ Submodule.span K (Set.range f) ⊓ LinearMap.ker (h (f i₀))
    exact Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨i, rfl⟩,
      LinearMap.mem_ker.2 (ho i₀ i (Ne.symm i.2))⟩
  · intro v hv
    have hv' : v ∈ Submodule.span K (Set.range f) ⊓ LinearMap.ker (h (f i₀)) := hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv'
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv1
    have ha0 : a i₀ = 0 := by

      rw [LinearMap.mem_ker, map_sum, Finset.sum_eq_single i₀] at hv2
      · rw [map_smul, smul_eq_mul] at hv2
        exact (mul_eq_zero.1 hv2).resolve_right hf0
      · intro i _ hi
        rw [map_smul, ho i₀ i (Ne.symm hi), smul_zero]
      · intro h'
        exact absurd (Finset.mem_univ i₀) h'
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, ha0, zero_smul, zero_add]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem mem_spanS_iff_smul_add_mem_spanS_ne {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → V) (i₀ : ι)
    (v : V) : v ∈ spanS S f ↔
      ∃ a ∈ S, ∃ w ∈ spanS S (fun i : {i // i ≠ i₀} => f i), v = a • f i₀ + w := by
  rw [mem_iff_lemma]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c i₀, hc i₀, ∑ i : {i // i ≠ i₀}, c i • f i,
      (mem_iff_lemma _ _).2 ⟨fun i => c i, fun i => hc i, rfl⟩, ?_⟩
    exact Fintype.sum_eq_add_sum_subtype_ne _ i₀
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [mem_iff_lemma] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    refine ⟨fun i => if hi : i = i₀ then a else d ⟨i, hi⟩, fun i => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact ha
      · exact hd _
    · rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
      dsimp only
      rw [dite_eq_left rfl]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dite_eq_right i.2]

theorem core_of_split (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hsp : SplitAt S π h) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ n →
    ∀ (b b' : ι → V) (e : ι → ℕ) (φ : V ≃ₗ[K] V),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i j, i ≠ j → h (b' i) (b' j) = 0) →
    (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, IsUnitIn S (h (b' i) (b' i) * (π ^ e i)⁻¹)) → φ ∈ Formalism.HermitianLatticesTheory.isom h →
    (∀ v, v ∈ Submodule.span K (Set.range b) ↔ φ v ∈ Submodule.span K (Set.range b')) →
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ Submodule.span K (Set.range b), h w v = 0) → g v = φ v) ∧
      ∀ v, v ∈ spanS S b ↔ g v ∈ spanS S b' := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hcard b b' e φ _ _ _ _ hφ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (Nat.le_zero.1 hcard)
    exact core_empty b b' hφ
  | succ n ih =>
    intro ι _ _ hcard b b' e φ ho ho' hu hu' hφ hW
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact core_empty b b' hφ
    obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
    have hb0 : b i₀ ∈ Submodule.span K (Set.range b) := Submodule.subset_span ⟨i₀, rfl⟩
    have hξ : φ (b i₀) ∈ Submodule.span K (Set.range b') := (hW _).1 hb0
    have hφn : h (φ (b i₀)) (φ (b i₀)) = h (b i₀) (b i₀) := hφ (b i₀) (b i₀)
    obtain ⟨c, hoc, huc, hcc, hspc, hiffc⟩ := hsp ι b' e i₀ ho' hu'
      (fun i => hmin i (Finset.mem_univ i)) (φ (b i₀)) hξ (by rw [hφn]; exact hu i₀)
    have hWc : ∀ v, v ∈ Submodule.span K (Set.range b) ↔
        φ v ∈ Submodule.span K (Set.range c) := by
      intro v
      rw [hspc]
      exact hW v
    obtain ⟨φ', hφ', hφ'0, hcut, hagree⟩ := exists_prep hs hd hφ hWc hb0
      (Submodule.subset_span ⟨i₀, rfl⟩) (by rw [hcc, hφn])
    have hA : h (b i₀) (b i₀) ≠ 0 := unit_ne (hu i₀)
    have hC : h (c i₀) (c i₀) ≠ 0 := unit_ne (huc i₀)
    have hcardS : Fintype.card {i // i ≠ i₀} ≤ n := by
      have := Fintype.card_subtype_lt (p := fun i => i ≠ i₀) (x := i₀) (by simp)
      omega
    have hWbb : ∀ v, v ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)) ↔
        φ' v ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => c i)) := by
      intro v
      rw [span_ne_eq_cutW_of_orthogonal ho hA, span_ne_eq_cutW_of_orthogonal hoc hC]
      exact hcut v
    obtain ⟨g, hg, hgagree, hgiff⟩ := ih {i // i ≠ i₀} hcardS (fun i => b i) (fun i => c i)
      (fun i => e i) φ' (fun i j hij => ho i j (fun h' => hij (Subtype.ext h')))
      (fun i j hij => hoc i j (fun h' => hij (Subtype.ext h'))) (fun i => hu i) (fun i => huc i)
      hφ' hWbb
    have hperp : ∀ w ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)),
        h w (b i₀) = 0 := by
      intro w hw
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw

      rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun i _ => by
        rw [map_smulₛₗ, LinearMap.smul_apply, ho i i₀ i.2, smul_zero]
    have hg0 : g (b i₀) = c i₀ := by rw [hgagree _ hperp, hφ'0]
    refine ⟨g, hg, fun v hv => ?_, fun v => ?_⟩
    · have hv' : ∀ w ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)), h w v = 0 :=
        fun w hw => hv w (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩) hw)
      rw [hgagree v hv', hagree v hv]
    · rw [← hiffc, mem_spanS_iff_smul_add_mem_spanS_ne b i₀, mem_spanS_iff_smul_add_mem_spanS_ne c i₀]
      constructor
      · rintro ⟨a, ha, w, hw, rfl⟩
        refine ⟨a, ha, g w, (hgiff w).1 hw, ?_⟩
        rw [map_add (f := _), map_smul, hg0]
      · rintro ⟨a, ha, u, hu2, huv⟩
        refine ⟨a, ha, g.symm u, (hgiff _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hu2), ?_⟩
        apply g.injective
        rw [huv, map_add (f := _), map_smul, hg0, LinearEquiv.apply_symm_apply]

end

end Formalism.L2.SG.Pf.G3
end
end
