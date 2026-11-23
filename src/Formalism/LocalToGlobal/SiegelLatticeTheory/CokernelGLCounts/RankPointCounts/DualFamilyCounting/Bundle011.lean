module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlmostEverywhereSpherical
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle004
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NeZeroOfNotMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniPart
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem vd_eq_vJof (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal)
    (b : Fin (finrank K (⊤ : Submodule K V)) → V) (a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F)
    (hJ : Cnt.IsJordanIn h ⊤ L 𝔭 b a) : vd h L 𝔭 = Cnt.vJof 𝔭 a := by
  classical
  obtain ⟨P, hP, hPc⟩ := exists_over (K := K) 𝔭 h𝔭
  haveI := h𝔭.isPrime
  have e : Fin (finrank K (⊤ : Submodule K V)) ≃ Fin (finrank K V) := finCongr (finrank_top K V)
  have hmap : ∀ x : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap F K (x : F) := fun x => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  have hA0 : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hJ.2.2.2.2 i
  have horth : ∀ i j, i ≠ j → h (b (e.symm i)) (b (e.symm j)) = 0 :=
    fun i j hij => hJ.2.2.1 _ _ fun h' => hij (e.symm.injective h')
  have hrange : Set.range (fun j => b (e.symm j)) = Set.range b := e.symm.surjective.range_comp b

  have hgb : (U0.gram h fun j => b (e.symm j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (∏ i, a i)) := by
    rw [gram_det_orth horth]
    have hp : ∏ j, h (b (e.symm j)) (b (e.symm j)) = ∏ i, h (b i) (b i) :=
      Fintype.prod_equiv e.symm _ _ fun _ => rfl
    rw [hp, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [hJ.2.2.2.1 i, hmap]
  have key : ∀ m : ℕ, discrIdeal h L ≤ extP K 𝔭 ^ m ↔ m ≤ vF 𝔭 (∏ i, a i) := by
    intro m
    constructor
    · intro hle
      have ht : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b i ∈ L := fun i => by
        have hb : b i ∈ locF 𝔭 L := by
          rw [← hJ.2.1]
          exact LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
        exact (LocalSpans.mem_locF 𝔭 L (b i)).1 hb
      choose t ht1 ht2 using ht
      have ht0 : ∀ i, t i ≠ 0 := fun i h0 => ht1 i (h0 ▸ 𝔭.zero_mem)
      have hT0 : (∏ i, t i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht0 i
      have hvT : vF 𝔭 (∏ i, t i) = 0 := by
        rw [vF_prod h𝔭 Finset.univ t ht0]
        exact Finset.sum_eq_zero fun i _ => vF_of_notMem h𝔭 (ht1 i)
      have hst : ∀ u : F, star (algebraMap F K u) = algebraMap F K u := fun u => (hF _).2 ⟨u, rfl⟩
      have hx : (U0.gram h fun j => algebraMap F K (t (e.symm j) : F) • b (e.symm j)).det =
          algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) ((∏ i, t i) * (∏ i, t i) * ∏ i, a i)) := by
        rw [gram_det_smul_orth horth]
        have hp1 : ∏ j, star (algebraMap F K (t (e.symm j) : F)) * algebraMap F K (t (e.symm j) : F) =
            ∏ i, algebraMap F K (t i : F) * algebraMap F K (t i : F) :=
          Fintype.prod_equiv e.symm _ _ fun j => by rw [hst]
        have hp2 : ∏ j, h (b (e.symm j)) (b (e.symm j)) = ∏ i, h (b i) (b i) :=
          Fintype.prod_equiv e.symm _ _ fun _ => rfl
        rw [hp1, hp2, map_mul, map_mul, map_mul, map_mul, map_prod, map_prod, map_prod, map_prod,
          Finset.prod_mul_distrib]
        simp only [hmap, hJ.2.2.2.1]
      have hxL : ∀ j, algebraMap F K (t (e.symm j) : F) • b (e.symm j) ∈ L := fun j => by
        rw [← hmap, algebraMap_smul]
        exact ht2 _
      have hmem : algebraMap (𝓞 F) (𝓞 K) ((∏ i, t i) * (∏ i, t i) * ∏ i, a i) ∈ discrIdeal h L :=
        Ideal.subset_span ⟨_, hxL, hx.symm⟩
      have h2 := hle hmem
      have h3 : (∏ i, t i) * (∏ i, t i) * ∏ i, a i ∈ 𝔭 ^ m := by
        rw [← MeanB.comap_extP_pow (K := K) 𝔭 m]
        exact h2
      rw [mem_pow_iff h𝔭 (mul_ne_zero (mul_ne_zero hT0 hT0) hA0), vF_mul h𝔭 (mul_ne_zero hT0 hT0) hA0,
        vF_mul h𝔭 hT0 hT0, hvT] at h3
      simpa using h3
    · intro hv
      unfold discrIdeal
      rw [Ideal.span_le]
      rintro z ⟨x, hxL, hz⟩
      have hx' : ∀ i, x i ∈ spanS (locRing P) fun j => b (e.symm j) := fun i => by
        have hxi : x i ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range fun j => b (e.symm j))) := by
          rw [hrange, hJ.2.1]
          exact LocF.le_locF 𝔭 L (hxL i)
        rw [← hPc] at hxi
        exact (mem_locF_span_iff hK hF hP _ (x i)).1 hxi
      obtain ⟨c, hc, hdet⟩ := gram_det_of_le (h := h) (isHermSemilocal_locRing hK hP) hx'
      obtain ⟨r, s, hs, hcr⟩ := (mem_locR_iff hP.isPrime c).1 hc
      have hsne := algebraMap_ne_zero_of_mem_hcompl hP.isPrime hs
      have hsz : s * z = r * algebraMap (𝓞 F) (𝓞 K) (∏ i, a i) := by
        apply IsFractionRing.injective (𝓞 K) K
        rw [map_mul, map_mul, hz]
        change _ * (U0.gram h x).det = _
        rw [hdet, hgb, hcr]
        field_simp
      have hAm : algebraMap (𝓞 F) (𝓞 K) (∏ i, a i) ∈ extP K 𝔭 ^ m := by
        rw [extP, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ ((mem_pow_iff h𝔭 hA0 m).2 hv)
      have hcop := OrthogonalBases.sup_eq_top_of_mem_hcompl hK hF hP hs
      rw [hPc] at hcop
      exact mem_pow_of_coprime hcop m (hsz ▸ Ideal.mul_mem_left _ r hAm)
  have hv : Cnt.vJof 𝔭 a = vF 𝔭 (∏ i, a i) := (vF_prod h𝔭 Finset.univ a hJ.2.2.2.2).symm
  rw [hv]
  unfold vd
  simp_rw [key]
  exact csSup_Iic

end Formalism.L2.SG.Pf.G1
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (g : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} :
    Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap g B ↔ A = B := by
  constructor
  · intro e
    rw [← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g A, ← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g B, e]
  · rintro rfl
    rfl

theorem gmap_inf (g : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (A ⊓ B) = Formalism.HermitianLatticesTheory.gmap g A ⊓ Formalism.HermitianLatticesTheory.gmap g B := by
  ext x
  simp only [Submodule.mem_inf, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]

theorem gmap_eq_self_of_fix (g : V ≃ₗ[K] V) {A : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, g x = x) :
    Formalism.HermitianLatticesTheory.gmap g A = A := by
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  constructor
  · intro hx
    have e := hA _ hx
    rw [LinearEquiv.apply_symm_apply] at e
    rw [e]
    exact hx
  · intro hx
    have e := hA _ hx
    have : g.symm x = x := by
      conv_lhs => rw [← e]
      simp
    rw [this]
    exact hx

theorem mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {v : V} :
    v ∈ orthK h U ↔ ∀ u ∈ U, h u v = 0 := by
  simp [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem map_mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) {v : V} (hv : v ∈ orthK h U) : g v ∈ orthK h U := by
  rw [mem_orthK] at hv ⊢
  intro u hu
  have e1 : h (g u) (g v) = h u v := hg.1 u v
  rw [hg.2 u hu] at e1
  rw [e1, hv u hu]

theorem gmap_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    Formalism.HermitianLatticesTheory.gmap g ((orthK h U).restrictScalars (𝓞 K)) = (orthK h U).restrictScalars (𝓞 K) := by
  have hgi : g⁻¹ ∈ isomFix h U := (isomFix h U).inv_mem hg
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Submodule.restrictScalars_mem, Submodule.restrictScalars_mem]
  constructor
  · intro hx
    have := map_mem_orthK hg hx
    simpa using this
  · intro hx
    exact map_mem_orthK hgi hx

theorem gmap_U {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    Formalism.HermitianLatticesTheory.gmap g (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) :=
  gmap_eq_self_of_fix g fun x hx => hg.2 x hx

theorem dualF_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) :
    dualF h 𝔭 (Formalism.HermitianLatticesTheory.gmap g Λ) = Formalism.HermitianLatticesTheory.gmap g (dualF h 𝔭 Λ) := by
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  change (∀ y ∈ Formalism.HermitianLatticesTheory.gmap g Λ, h y x ∈ _) ↔ ∀ y ∈ Λ, h y (g.symm x) ∈ _
  constructor
  · intro H y hy
    have := H (g y) (by rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; simpa using hy)
    have e : h (g y) (g (g.symm x)) = h y (g.symm x) := hg y (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at e
    rwa [e] at this
  · intro H y hy
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hy
    have := H _ hy
    have e : h (g (g.symm y)) (g (g.symm x)) = h (g.symm y) (g.symm x) := hg _ _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    rwa [e]

theorem le_of_isLatIn {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : IsLatIn X L) :
    ∀ x ∈ L, x ∈ X := by
  intro x hx
  rw [← hL.2]
  exact Submodule.subset_span hx

theorem fibP_gmap [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hM : IsLatIn U M) (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V) {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T) = fibP h U 𝔭 M T := by
  have hMg : Formalism.HermitianLatticesTheory.gmap g M = M := gmap_eq_self_of_fix g fun x hx => hg.2 x (le_of_isLatIn hM x hx)
  let e : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V :=
    { toFun := Formalism.HermitianLatticesTheory.gmap g
      invFun := Formalism.HermitianLatticesTheory.gmap g.symm
      left_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm _ Λ
      right_inv := fun Λ => by
        have := Formalism.HermitianLatticesTheory.isomAct_gmap_symm g.symm Λ
        simpa using this }
  unfold fibP
  refine (Nat.card_congr (Equiv.subtypeEquiv e ?_)).symm
  intro Λ
  change _ ↔ ((∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Formalism.HermitianLatticesTheory.gmap g Λ) ∧
    dualF h 𝔭 (Formalism.HermitianLatticesTheory.gmap g Λ) = Formalism.HermitianLatticesTheory.gmap g Λ ∧
    Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g T))
  have e1 : Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ U.restrictScalars (𝓞 K)) := by rw [gmap_inf, gmap_U hg]
  have e2 : locF 𝔭 M = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 M) := by rw [LocalizedFibreSets.gmap_locF, hMg]
  have e3 : Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) := by rw [gmap_inf, gmap_orthK hg]
  have e4 : locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g T) = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) := (LocalizedFibreSets.gmap_locF g 𝔭 T).symm
  rw [dualF_gmap hg.1, gmap_eq_iff, e1, e3, e4, gmap_eq_iff]
  conv_rhs => rw [e2, gmap_eq_iff]
  refine and_congr_left fun _ => ?_
  have lattice_gmap (a : V ≃ₗ[K] V) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
      Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap a L) :=
    Submodule.IsLattice.of_fg K (hL.fg.map _)
  constructor
  · rintro ⟨Λ₀, h0, e0⟩
    exact ⟨Formalism.HermitianLatticesTheory.gmap g Λ₀, lattice_gmap g h0, by rw [← LocalizedFibreSets.gmap_locF, e0]⟩
  · rintro ⟨Λ₀, h0, e0⟩
    refine ⟨Formalism.HermitianLatticesTheory.gmap g.symm Λ₀, lattice_gmap g.symm h0, ?_⟩
    rw [← LocalizedFibreSets.gmap_locF, e0, Formalism.HermitianLatticesTheory.isomAct_gmap_symm]

end Formalism.L2.SG.Pf.G6
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans

def IsGlueData {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) {n m : ℕ} (a : Fin n → 𝓞 F)
    (π : 𝓞 F) (w : Fin m → V) (c : Fin m → F) (τ : Fin n → Fin m) : Prop :=
  (∀ j, w j ∈ orthK h U) ∧ (∀ j k, j ≠ k → h (w j) (w k) = 0) ∧
  (∀ j, h (w j) (w j) = algebraMap F K (c j) ∧ c j ≠ 0) ∧
  (∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) ∧
  (∃ s₀ : 𝓞 F, IsUnif0 𝔭 π s₀) ∧
  (∀ i, vF 𝔭 (a i) ≠ 0 →
    InP 𝔭 (2 * vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i)))) ∧
  (∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) →
    InP 𝔭 0 (algebraMap F K (c j)) ∧ InP 𝔭 0 (algebraMap F K (c j)⁻¹))

def GlueVecs : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
      ∃ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
        (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ

def GlueAssemble : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      ∃ T : Submodule (𝓞 K) V, (∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧ locF 𝔭 A = T) ∧
        dualF h 𝔭 T = T ∧ T ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem nondegOn_of_compl {h : V →ₗ⋆[K] V →ₗ[K] K} (hnd : Nondeg h) {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) : NondegOn h U := by
  intro x hx hxU
  apply hnd
  intro y
  have hy : y ∈ U ⊔ orthK h U := by rw [hUc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
  have hz' : h x z = 0 := by
    have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz x) hx
    exact LinearMap.mem_ker.1 this
  rw [map_add (f := _), hxU u hu, hz', add_zero]

theorem glueLocal_of_of (hJ : JordanExists) (hV : GlueVecs) (hA : GlueAssemble) :
    Formalism.L2.SG.Pf.G7.GlueLocal := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 hc
  have hne : {c | ∃ b a, IsJordanIn h U M 𝔭 b a ∧ c = cJof 𝔭 a}.Nonempty := by
    obtain ⟨b, a, hba⟩ := (hJ K F V hK hF h hs).1 U M (nondegOn_of_compl hnd hUc) hM hMi 𝔭 h𝔭
    exact ⟨_, b, a, hba, rfl⟩
  obtain ⟨b, a, hba, hca⟩ := Nat.sInf_mem hne
  have hc' : cJof 𝔭 a < finrank K (orthK h U) := by
    rw [← hca]; exact hc
  obtain ⟨π, w, c, τ, hg⟩ := hV K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc'
  exact hA K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg

end Formalism.L2.SG.Pf.GluingBases
end
end

section

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem rebasing_holds : G3.Rebase := by
  intro K V _ _ _ _ _ S π h hS hπ hs hd
  exact rebaseAt_of hS hπ
    (fun J _ _ b e i₀ ho hu x hx hX => G3.uni_part hS hπ hs hd ho hu x hx hX)
    (fun J _ _ e i₀ x hx T hT hlt b ho hu => G3.absorb hS hπ hs x hx T hT hlt b ho hu)

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end
