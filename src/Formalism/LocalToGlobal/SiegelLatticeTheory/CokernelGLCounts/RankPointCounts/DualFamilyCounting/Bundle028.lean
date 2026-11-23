module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle024
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapesTer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def fibS (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T : Submodule (𝓞 K) V) :
    Set (Submodule (𝓞 K) V) :=
  {Λ | (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T}

theorem fibP_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T : Submodule (𝓞 K) V) :
    fibP h U 𝔭 M T = Nat.card (fibS h U 𝔭 M T) := rfl

theorem isLattice_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : IsLatIn X A) (hB : IsLatIn Y B) : Submodule.IsLattice K (A ⊔ B) := by
  refine ⟨hA.1.sup hB.1, ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem exists_locF_eq {A B : Submodule (𝓞 K) V} (hA : Submodule.IsFullLattice K A)
    (hB : Submodule.IsFullLattice K B) :
    ∃ s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∀ 𝔭 ∉ s, locF 𝔭.1 A = locF 𝔭.1 B := by
  obtain ⟨n, hn, hnA⟩ := LocF.exists_zsmul_le hA.toIsLattice hB
  obtain ⟨m, hm, hmB⟩ := LocF.exists_zsmul_le hB.toIsLattice hA
  have hc : ((n * m : ℤ) : 𝓞 F) ≠ 0 := by
    exact_mod_cast mul_ne_zero hn hm
  obtain ⟨s, hs⟩ := (LocalFactorEquality.finite_vF_ne_zero hc).exists_finset
  refine ⟨s, fun 𝔭 h𝔭 => ?_⟩
  have hv : vF 𝔭.1 ((n * m : ℤ) : 𝓞 F) = 0 := by
    by_contra hne
    exact h𝔭 ((hs 𝔭).2 hne)
  have hnm := LocalizedFibreSets.notMem_of_vF_zero 𝔭.2 hc hv
  have hp := 𝔭.2.isPrime
  have hn' : ((n : ℤ) : 𝓞 F) ∉ 𝔭.1 := fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_right _ h1)
  have hm' : ((m : ℤ) : 𝓞 F) ∉ 𝔭.1 := fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_left _ h1)
  have key : ∀ {A B : Submodule (𝓞 K) V} (k : ℤ), ((k : ℤ) : 𝓞 F) ∉ 𝔭.1 → (∀ x ∈ A, k • x ∈ B) →
      locF 𝔭.1 A ≤ locF 𝔭.1 B := by
    intro A B k hk hkA x hx
    obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
    refine (LocF.mem_locF_iff hp B x).2 ⟨(k : 𝓞 F) * t, fun h1 => (hp.mem_or_mem h1).elim hk ht, ?_⟩
    rw [map_mul, mul_smul, LocF.algebraMap_intCast_smul]
    exact hkA _ htx
  exact le_antisymm (key n hn' hnA) (key m hm' hmB)

private lemma mem_locF_lemma {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F))
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma algebraMap_ne_zero_of_mem_closure_prime_compl {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
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

theorem locF_sup_inf {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ x ∈ B, x ∈ Y) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    locF 𝔭 (A ⊔ B) ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 A := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx1
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsx
    have hxX : x ∈ X := hx2
    have hsX : s • x ∈ X := by
      rw [← algebraMap_smul K s x]; exact X.smul_mem _ hxX
    have hbX : b ∈ X := by
      have : b = s • x - a := by rw [← hab]; abel
      rw [this]; exact X.sub_mem hsX (hA a ha)
    have hb0 : b = 0 := by
      have := hc.inf_eq_bot
      have hmem : b ∈ X ⊓ Y := ⟨hbX, hB b hb⟩
      rw [this] at hmem
      exact (Submodule.mem_bot K).mp hmem
    refine (mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, ?_⟩
    rw [← hab, hb0, add_zero]; exact ha
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
    refine ⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, Submodule.mem_sup_left hsx⟩, ?_⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := algebraMap_ne_zero_of_mem_closure_prime_compl hs
    have e : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
      rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    show x ∈ X
    rw [e]
    exact X.smul_mem _ (hA _ hsx)

theorem dualF_anti (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) {A B : Submodule (𝓞 K) V} (hAB : A ≤ B) :
    dualF h 𝔭 B ≤ dualF h 𝔭 A := by
  intro x hx
  have hx' : ∀ y ∈ B, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  change ∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  exact fun y hy => hx' y (hAB hy)

end Formalism.L2.SG.Pf.G8
end
end

section

namespace Formalism.L2.SG.Pf.Cnt

theorem alpha_discriminant_holds : AlphaDisc :=
  Formalism.L2.SG.Pf.G5.alphaDisc_of_discOnto
    (Formalism.L2.SG.Pf.discriminantNormShapes.discOnto_of_uDModel Formalism.L2.SG.Pf.Cnt.unitary_discriminant_model)

end Formalism.L2.SG.Pf.Cnt
end

section

namespace Formalism.L2.SG.Pf.GluingBases

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueVecs_of_last (hL : LastUnit) : GlueVecs :=
  glueVecs_of gluing_vectors_exist (lastRescale_of hL)

end Formalism.L2.SG.Pf.GluingBases

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_of_last_dual (hL : Formalism.L2.SG.Pf.GluingBases.LastUnit) (hD : Formalism.L2.SG.Pf.GluingBases.FamDual) :
    GlueExists :=
  glueExists_of_fam jordan_splitting_exists (Formalism.L2.SG.Pf.GluingBases.glueVecs_of_last hL)
    Formalism.L2.SG.Pf.GluingBases.family_top_holds Formalism.L2.SG.Pf.GluingBases.family_gram_holds hD

end Formalism.L2.SG.Pf.Cnt
end

section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt.DualityBasisChange

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_integer_iff_vle {K : Type} [Field K] [ValuativeRel K] (x : K) : x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (v := valuation K)).symm

theorem mem_OF_of_loc (D : Formalism.BasicNotions.D7) (s : D.host.F)
    (hs : ∀ p : PlF D, (D.s.atP p).ιE (algebraMap D.host.F D.host.E s) ∈ (D.s.atP p).O) :
    s ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.F s fun p => ?_
  have h1 := hs p
  rw [(D.s.atP p).compat] at h1
  have hint := ((D.s.atP p).O_def _).1 h1
  have hnt : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hinj : Function.Injective (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) := by
    haveI := hnt; exact (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
  have h2 : (D.s.atP p).ιF s ∈ 𝒪[(D.s.atP p).Fp] :=
    PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral ((isIntegral_algebraMap_iff ).1 hint)
  rw [mem_integer_iff_vle, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one] at h2
  exact h2

theorem locGlobIntE : LocGlobIntE := by
  intro D x hx
  have hstar : star x = D.conjF x := by
    rw [D.conjF_eq]
    have := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm
  have hcjO : ∀ p : PlF D, (D.s.atP p).ιE (star x) ∈ (D.s.atP p).O := fun p => by
    rw [hstar, ← (D.s.atP p).cj_ιE, (D.s.atP p).O_def]
    exact ((D.s.atP p).O_def _).1 (hx p) |>.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])
  obtain ⟨t, ht⟩ := (D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := (D.sp.cm.fixed (x * star x)).1 (by rw [star_mul, star_star, mul_comm])
  obtain ⟨t', ht'⟩ := mem_OF_of_loc D t fun p => by
    rw [ht, map_add (f := _)]; exact (D.s.atP p).O.add_mem (hx p) (hcjO p)
  obtain ⟨n', hn'⟩ := mem_OF_of_loc D n fun p => by
    rw [hn, map_mul]; exact (D.s.atP p).O.mul_mem (hx p) (hcjO p)

  have hT : IsIntegral ℤ (x + star x) := by
    rw [← ht, ← ht']
    exact map_isIntegral_int (algebraMap D.host.F D.host.E) (map_isIntegral_int _ (RingOfIntegers.isIntegral t'))
  have hN : IsIntegral ℤ (x * star x) := by
    rw [← hn, ← hn']
    exact map_isIntegral_int (algebraMap D.host.F D.host.E) (map_isIntegral_int _ (RingOfIntegers.isIntegral n'))
  set a : 𝓞 D.host.E := ⟨x + star x, hT⟩
  set b : 𝓞 D.host.E := ⟨x * star x, hN⟩
  have hx' : IsIntegral (𝓞 D.host.E) x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C b, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    show x ^ 2 - (x + star x) * x + x * star x = 0
    ring
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  exact Submodule.mem_one.2 ⟨y, hy⟩

theorem not_integral_density_of_self_dual (h1 : LocSelfDual) (hF : FrameBasisL) : NotIntDens :=
  notIntDens_of_steps h1 hF locGlobIntE

end Formalism.L2.SG.Pf.Cnt.DualityBasisChange
end
end
