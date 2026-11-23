module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HermitianCoefficientIdentityOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle002
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFracOfFixed
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle022
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle013
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsIsomScale
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AdelicThetaPoissonSummation

@[expose] public section

section

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

private theorem unit_mul_lemma {a c : K} (ha : IsUnitIn S a) (hc : IsUnitIn S c) :
    IsUnitIn S (a * c) :=
  And.intro (mul_ne_zero ha.1 hc.1)
    (And.intro (S.mul_mem ha.2.1 hc.2.1) (by rw [mul_inv]; exact S.mul_mem ha.2.2 hc.2.2))

theorem absorb (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {ι : Type} [Fintype ι]
    [DecidableEq ι] {e : ι → ℕ} {i₀ : ι} (x : ι → K) (hx : ∀ i, x i ∈ S) :
    ∀ T : Finset ι, i₀ ∉ T → (∀ j ∈ T, e i₀ < e j) → ∀ b : ι → V,
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = b i₀ + ∑ j ∈ T, x j • b j ∧
      (∀ k, k ≠ i₀ → k ∉ T → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro _ _ b ho hu
    exact ⟨b, ho, hu, by simp, fun _ _ _ => rfl, rfl, fun _ => Iff.rfl⟩
  · intro a T haT ih hi₀ hlt b ho hu
    have hi₀T : i₀ ∉ T := fun hm => hi₀ (Finset.mem_insert_of_mem hm)
    have hai₀ : i₀ ≠ a := by
      intro h'
      apply hi₀
      rw [h']
      exact Finset.mem_insert_self a T
    obtain ⟨c', ho', hu', hc'0, hc'k, hsp', hiff'⟩ :=
      ih hi₀T (fun j hj => hlt j (Finset.mem_insert_of_mem hj)) b ho hu
    have hc'a : c' a = b a := hc'k a (Ne.symm hai₀) haT
    have hlta : e i₀ < e a := hlt a (Finset.mem_insert_self a T)
    have hu0 : h (c' i₀) (c' i₀) ≠ 0 := unit_ne (hu' i₀)
    have hπ0 : π ≠ 0 := hπ.ne
    obtain ⟨d, hd⟩ : ∃ d, e a = e i₀ + d + 1 := ⟨e a - e i₀ - 1, by omega⟩
    have hs0 : (h (c' i₀) (c' i₀) * (π ^ e i₀)⁻¹)⁻¹
        * (star (x a) * x a * (h (c' a) (c' a) * (π ^ e a)⁻¹) * π ^ d) ∈ S :=
      S.mul_mem (hu' i₀).2.2 (S.mul_mem (S.mul_mem (S.mul_mem (hS.star_mem _ (hx a)) (hx a))
        (hu' a).2.1) (S.pow_mem hπ.mem d))
    have hY : IsUnitIn S (h ((1 : K) • c' i₀ + x a • c' a) ((1 : K) • c' i₀ + x a • c' a)
        * (π ^ e i₀)⁻¹) := by
      rw [form_pair (c' i₀) (c' a) (ho' i₀ a hai₀) (ho' a i₀ (Ne.symm hai₀))]
      have eq : (star (1 : K) * 1 * h (c' i₀) (c' i₀) + star (x a) * x a * h (c' a) (c' a))
          * (π ^ e i₀)⁻¹ = (h (c' i₀) (c' i₀) * (π ^ e i₀)⁻¹) * (1 + π * ((h (c' i₀) (c' i₀)
          * (π ^ e i₀)⁻¹)⁻¹ * (star (x a) * x a * (h (c' a) (c' a) * (π ^ e a)⁻¹) * π ^ d))) := by
        rw [hd, star_one]
        field_simp
        ring
      rw [eq]
      exact unit_mul_lemma (hu' i₀) (hπ.rad _ hs0)
    obtain ⟨c, ho2, hu2, hc0, hck, hsp2, hiff2⟩ :=
      rot2 hS hπ hs ho' hu' hai₀ hlta.le S.one_mem (hx a) hY
    refine ⟨c, ho2, hu2, ?_, ?_, hsp2.trans hsp', fun v => (hiff2 v).trans (hiff' v)⟩
    · rw [hc0, hc'0, hc'a, one_smul, Finset.sum_insert haT]
      abel
    · intro k hk0 hkT
      have hka : k ≠ a := by
        intro h'
        apply hkT
        rw [h']
        exact Finset.mem_insert_self a T
      have hkT' : k ∉ T := fun h' => hkT (Finset.mem_insert_of_mem h')
      rw [hck k hk0 hka, hc'k k hk0 hkT']

end

end Formalism.L2.SG.Pf.G3
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcWeil

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.UnusedSlot34 Formalism.L2.SG.Volumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def SWc1W : Prop :=
  ∀ (n : ℕ), 2 * n < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → RapidDecay b Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) n) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ n → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
      meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) =
        ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)

def VolStabW : Prop :=
  IsHermND σ J → ∀ (a : ℕ), 1 ≤ a → 2 * a < M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j),
    (gramE σ J X0).det ≠ 0 → VolStabAt F E σ M J X0 hT

end Ext

end Formalism.L2.SG.Pf.NcWeil
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open NumberField Formalism.HermitianLattices.Ext.L3

theorem local_unimodular_holds : Formalism.MainNotions.BridgeRowsGenus.LocUnimod := by
  intro F E _ _ _ _ _ _ hc S L M hL hM p hp huL huM
  classical
  have full (N : Submodule (𝓞 E) S.V) (hN : Submodule.IsLattice E N)
      (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt S.hT p N) :
      Submodule.IsFullLattice E N := by
    let D := Formalism.HermitianLatticesTheory.dual S.hT N
    have hd : Submodule.span E (D : Set S.V) = ⊤ := by
      obtain ⟨T, hT⟩ := hN.fg
      subst N
      apply eq_top_iff.mpr
      intro x _
      obtain ⟨n, hn, hint⟩ :=
        exists_integral_multiples ℤ ℚ (L := E) (T.image fun y => S.hT y x)
      have hx : n • x ∈ Formalism.HermitianLatticesTheory.dual S.hT
          (Submodule.span (𝓞 E) (T : Set S.V)) := by
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          rw [map_zsmul]
          exact Submodule.mem_one.mpr ⟨⟨_, hint _ (Finset.mem_image_of_mem _ hy)⟩, rfl⟩
        | zero => simp
        | add y z _ _ hy hz =>
          rw [map_add, LinearMap.add_apply]
          exact Submodule.add_mem _ hy hz
        | smul c y _ hy =>
          obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
          rw [← algebraMap_smul E c y, map_smulₛₗ S.hT (algebraMap (𝓞 E) E c) y,
            LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, ← hr, ← smul_eq_mul,
            algebraMap_smul]
          exact Submodule.smul_mem _ r hy
      refine (Submodule.smul_mem_iff _ (Int.cast_ne_zero.mpr hn : (n : E) ≠ 0)).mp ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.subset_span hx
    have hle : D ≤ Formalism.HermitianLatticesTheory.loc (K := E) p N := by
      have h1 := Formalism.HermitianLatticesTheory.locDual_loc_dual_le S.hT p N
      rw [← Formalism.HermitianLatticesTheory.locDual_dualAt_loc S.hT
        (RingOfIntegers.coe_injective)
        (Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range) p N, hu] at h1
      exact (Formalism.HermitianLatticesTheory.locBasic_le_locS _ D).trans h1
    refine { toIsLattice := hN, span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro x _
    have hx : x ∈ Submodule.span E (D : Set S.V) := hd ▸ Submodule.mem_top
    apply (Submodule.span_le.mpr ?_) hx
    intro y hy
    obtain ⟨s, hs, hsy⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp (hle hy)
    have hs0 := WA.algebraMap_ne_zero_of_mem_hcompl hp.isPrime hs
    apply (Submodule.smul_mem_iff _ hs0).mp
    rw [algebraMap_smul]
    exact Submodule.subset_span hsy
  have hF : IsFixF E F := fun a => by rw [hc.fixed a, RingHom.mem_range, Set.mem_range]
  obtain ⟨π, hπ, -, -⟩ := U0.exists_isUnif hF hp
  have hnd : G4.NondegOn S.hT ⊤ := by
    intro ξ _ hξ0
    by_contra hcon
    push Not at hcon
    exact hξ0 (S.nondeg.2 ξ fun w => hcon w Submodule.mem_top)
  obtain ⟨g, hg, -, hgM⟩ := G4.sd_main' (WA.isHermSemilocal_locRing hc.cmUnram hp) hπ S.herm
    two_ne_zero _ ⊤ ⊤ _ _ 1 le_rfl hnd (U0.isSD_loc (full L hL huL) hp.isPrime huL) (U0.isSD_loc (full M hM huM) hp.isPrime huM)
    (one_mem _) (fun _ => ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  exact ⟨g, hg, U0.gmap_eq_of_iff hgM⟩

end Formalism.L2.SG.Pf.Cnt
end
end
