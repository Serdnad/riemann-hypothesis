module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle025
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFLeSpanK
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle007
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle012
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle011
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP

@[expose] public section

section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def crd (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F) (x : V) (j : Fin m) : K :=
  h (b j) x / jK (ι (a j))

def gmap (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) : V →ₗ[𝓞 K] V where
  toFun x := ∑ i, (∑ j, jK (Y i j) * crd h b a x j) • b i
  map_add' x y := by
    simp only [crd, map_add (f := _), add_div, mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' c x := by
    simp only [crd, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algebra_compatible_smul K c x, algebra_compatible_smul K c, smul_smul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul]; ring

section

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}

theorem crd_sub (x y : V) (j : Fin m) : crd h b a (x - y) j = crd h b a x j - crd h b a y j := by
  simp only [crd, map_sub, sub_div]

theorem crd_smul (c : 𝓞 K) (x : V) (j : Fin m) : crd h b a (c • x) j = jK c * crd h b a x j := by
  unfold crd
  rw [algebra_compatible_smul K c x, LinearMap.map_smul, smul_eq_mul, mul_div_assoc]

variable (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include horth hdiag ha

theorem crd_sum (c : Fin m → K) (k : Fin m) : crd h b a (∑ i, c i • b i) k = c k := by
  have e : ∀ j, jK (ι (a j)) = algebraMap F K ((a j : 𝓞 F) : F) := fun j =>
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K (a j)).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K (a j))
  unfold crd

  rw [map_sum, Finset.sum_eq_single k]
  · have hne : jK (ι (a k)) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr
      ((map_ne_zero_iff ι (RingOfIntegers.algebraMap.injective F K)).mpr (ha k))
    rw [LinearMap.map_smul, hdiag k, smul_eq_mul, ← e k, mul_div_assoc, div_self hne, mul_one]
  · intro i _ hik
    rw [LinearMap.map_smul, horth k i (Ne.symm hik), smul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem crd_gmap (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (k : Fin m) :
    crd h b a (gmap h b a Y x) k = ∑ j, jK (Y k j) * crd h b a x j := by
  rw [show gmap h b a Y x = ∑ i, (∑ j, jK (Y i j) * crd h b a x j) • b i from rfl]
  exact crd_sum horth hdiag ha _ k

theorem h_b (x : V) (k : Fin m) : h (b k) x = jK (ι (a k)) * crd h b a x k := by
  have hne : jK (ι (a k)) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr
    ((map_ne_zero_iff ι (RingOfIntegers.algebraMap.injective F K)).mpr (ha k))
  unfold crd
  rw [mul_div_assoc', eq_div_iff hne, mul_comm]

variable (hbX : ∀ i, b i ∈ (⊤ : Submodule K V))
  (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
include hbX hloc

theorem coordsT (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x : V) : x = ∑ i, crd h b a x i • b i := by
  have hxs : x ∈ Submodule.span K (Set.range b) := by
    have hx : x ∈ (⊤ : Submodule K V) := Submodule.mem_top
    rw [← hL.2] at hx
    refine Submodule.span_le.mpr ?_ hx
    intro y hy
    have hyLoc := localizedQuotients.le_locF 𝔭 L hy
    rw [← hloc] at hyLoc
    exact G2.locF_le_spanK h𝔭 hyLoc
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxs
  simp only [crd_sum horth hdiag ha]

theorem h_expand (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x y : V) :
    h x y = ∑ i, star (crd h b a x i) * jK (ι (a i)) * crd h b a y i := by
  have e : ∀ j, jK (ι (a j)) = algebraMap F K ((a j : 𝓞 F) : F) := fun j =>
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K (a j)).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K (a j))
  have e1 : ∀ j, h x (b j) = star (crd h b a x j) * jK (ι (a j)) := by
    intro j
    have hx := coordsT horth hdiag ha hbX hloc h𝔭 hL x
    conv_lhs => rw [hx]

    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
    · rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hdiag j, smul_eq_mul, starRingEnd_apply, ← e j]
    · intro i _ hij
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, horth i j hij, smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hy := coordsT horth hdiag ha hbX hloc h𝔭 hL y
  conv_lhs => rw [hy]

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul, e1 j, smul_eq_mul]
  ring

theorem mem_B (h𝔭 : 𝔭.IsPrime) (hL : IsLatIn ⊤ L) (x : V) :
    x ∈ locF 𝔭 L ↔ ∀ i, crd h b a x i ∈ HU.SP K 𝔭 := by
  have := h𝔭
  rw [← hloc]
  constructor
  · rintro ⟨s, hs, hsx⟩ i
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsx
    have hz' : s • x = ∑ j, jK (z j) • b j := by
      exact hz.symm.trans (Finset.sum_congr rfl fun j _ => algebra_compatible_smul K (z j) (b j))
    rw [HU.mem_SP_iff_locF]
    refine ⟨s, hs, ?_⟩
    rw [Algebra.smul_def, ← crd_smul, hz', crd_sum horth hdiag ha]
    exact Submodule.mem_one.mpr ⟨z i, rfl⟩
  · intro hx
    rw [coordsT horth hdiag ha hbX hloc h𝔭 hL x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨s, hs, hsc⟩ := HU.mem_SP_iff_locF.mp (hx i)
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp hsc
    refine ⟨s, hs, ?_⟩
    rw [← smul_assoc, ← hz, algebraMap_smul K]
    exact Submodule.smul_mem _ z (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_A (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn ⊤ L) (x : V) :
    x ∈ locF 𝔭 (dualIn h ⊤ L) ↔ ∀ i, jK (ι (a i)) * crd h b a x i ∈ HU.SP K 𝔭 := by
  rw [G2.mem_locF_dualIn_iff (hbX := hbX) (hloc := hloc) (horth := horth) (hdiag := hdiag) (ha := ha)
    hF h𝔭 hL x]
  refine ⟨fun hx i => ?_, fun hx => ⟨Submodule.mem_top, fun i => ?_⟩⟩
  · rw [← h_b horth hdiag ha x i]
    exact hx.2 i
  · rw [h_b horth hdiag ha x i]
    exact hx i

end

end Formalism.L2.SG.Pf.fibreCountingData
end
end

section

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
  Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem det_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) :
    G.det ∈ SP K 𝔭 := by
  have e : G.det = (SP K 𝔭).subtype
      (Matrix.det (Matrix.of fun i j => (⟨G i j, hG i j⟩ : SP K 𝔭))) := by
    rw [RingHom.map_det]; rfl
  rw [e]
  exact SetLike.coe_mem _

theorem gram_det_ne_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) (β : Basis κ K V) :
    (gramK h β).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hy : ∀ x, h x (β.equivFun.symm v) = 0 := by
    intro x
    rw [form_repr h β, LinearEquiv.apply_symm_apply, hGv]
    simp
  have h0 : β.equivFun.symm v = 0 := by
    apply hnd
    intro y
    have := hs.eq y (β.equivFun.symm v)
    rw [← this, hy y, map_zero]
  exact β.equivFun.symm.injective (by rw [h0, map_zero])

private lemma mem_locF_lemma (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) K) (x : K) :
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

private lemma star_mem_SP' (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K}
    (ha : a ∈ SP K 𝔭) : star a ∈ SP K 𝔭 := by
  rw [mem_SP_iff_locF] at ha ⊢
  obtain ⟨s, hs', hsa⟩ := (mem_locF_lemma 𝔭 _ a).mp ha
  obtain ⟨z, hz⟩ := Submodule.mem_one.mp hsa
  obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range z
  refine (mem_locF_lemma 𝔭 _ _).mpr ⟨s, hs', Submodule.mem_one.mpr ⟨r, ?_⟩⟩
  rw [hr, hz, Algebra.smul_def, Algebra.smul_def, star_mul', star_fix_lemma_2 hF hs']

theorem det_unit_of_selfdual (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) (β : Basis κ K V) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]
    (hsd : dualF h 𝔭 (locF 𝔭 (spanO β)) = locF 𝔭 (spanO β)) :
    (gramK h β).det ∈ SP K 𝔭 ∧ (gramK h β).det⁻¹ ∈ SP K 𝔭 := by
  have hdet := gram_det_ne_zero hs hnd β
  have hunit : IsUnit (gramK h β).det := isUnit_iff_ne_zero.mpr hdet
  have hmemL : ∀ x, x ∈ locF 𝔭 (spanO β) ↔ ∀ i, β.equivFun x i ∈ SP K 𝔭 :=
    fun x => mem_locF_iff_repr β x
  have hβ : ∀ i, β i ∈ locF 𝔭 (spanO β) := fun i => by
    simpa using smul_basis_mem β (SP K 𝔭).one_mem i
  have hdual : ∀ x ∈ locF 𝔭 (spanO β), ∀ y ∈ locF 𝔭 (spanO β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hsd] at hx
    exact hx
  have hG : Ent (SP K 𝔭) (gramK h β) := fun i j =>
    mem_SP_iff_locF.mpr (hdual _ (hβ j) _ (hβ i))
  have hinv : gramK h β * (gramK h β)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hcol : ∀ k l, (gramK h β)⁻¹ l k ∈ SP K 𝔭 := by
    intro k l
    obtain ⟨x, hxdef⟩ : ∃ x : V, β.equivFun x = (gramK h β)⁻¹ *ᵥ Pi.single k (1 : K) :=
      ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    have hx : x ∈ locF 𝔭 (spanO β) := by
      rw [← hsd]
      change ∀ y ∈ locF 𝔭 (spanO β), h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
      intro y hy
      rw [← mem_SP_iff_locF, form_repr h β, hxdef, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      convert star_mem_SP' hF ((hmemL y).mp hy k) using 1
      simp [dotProduct, Pi.single_apply]
    have hc := (hmemL x).mp hx l
    rw [hxdef] at hc
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hc
  have hdi : ((gramK h β)⁻¹).det = (gramK h β).det⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  refine ⟨det_mem_SP hG, ?_⟩
  rw [← hdi]
  exact det_mem_SP fun l k => hcol k l

theorem gram_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    gramK h γ = (β.toMatrix γ)ᴴ * gramK h β * β.toMatrix γ := by
  ext i j
  have e : gramK h γ i j = h (γ i) (γ j) := rfl
  rw [e, form_repr h β, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Basis.toMatrix_apply, Basis.equivFun_apply, Pi.star_apply]

theorem gram_det_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    (gramK h γ).det = star (β.toMatrix γ).det * (gramK h β).det * (β.toMatrix γ).det := by
  rw [gram_change h β γ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]

theorem gram_det_orth (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : Basis κ K V)
    (ho : ∀ s t, s ≠ t → h (γ s) (γ t) = 0) : (gramK h γ).det = ∏ s, h (γ s) (γ s) := by
  have e : gramK h γ = Matrix.diagonal fun s => h (γ s) (γ s) := by
    ext s t
    by_cases hst : s = t
    · subst hst; simp [gramK]
    · simp [gramK, Matrix.diagonal_apply_ne _ hst, ho s t hst]
  rw [e, Matrix.det_diagonal]

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped ENNReal
open Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def eV (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) : Fin X.B.I.n → ℂ := rv X.B.I v (X.eR a)
def fV (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) : Fin X.B.I.n → ℂ := rv X.B.I v (X.fR a)
def zV (v : InfinitePlace X.B.I.F) : Fin X.B.I.n → ℂ := rv X.B.I v (X.zR u)

def xMat (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b a => hJ (X.B.I.ε v) (fV X v b) (uMat (s v) *ᵥ eV X v a)

def yVec (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Fin D.R.rS → ℂ :=
  fun b => hJ (X.B.I.ε v) (fV X v b) (uMat (s v) *ᵥ zV X u v)

def phiMat (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Matrix (Fin D.R.rS) (Fin D.R.k) ℂ :=
  fun b j => hJ (X.B.I.ε v) (fV X v b) (uMat (s v) *ᵥ X.wfr u v j)

def aMat (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b a => hJ (X.B.I.ε v) (fV X v b) (uMat (s v) *ᵥ fV X v a)

def mMat (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  (xMat X v s)⁻¹ * aMat X v s

def InUnit (t : ℝ) : Prop := 0 ≤ t ∧ t < 1

def InBox (c : ℂ) : Prop := InUnit c.re ∧ InUnit c.im

def boxN : Set X.B.I.Ginf :=
  X.NinfU u ∩ {s | ∀ v,
    (∀ b a : Fin D.R.rS, b < a → InBox (xMat X v s b a)) ∧ (∀ b, InBox (yVec X u v s b)) ∧
    (∀ b j, InBox (phiMat X u v s b j)) ∧
    (∀ b a : Fin D.R.rS, b < a → InBox ((mMat X v s b a - star (mMat X v s a b)) / 2)) ∧
    ∀ a, InUnit (mMat X v s a a).im}

def covolumeExponent (r k : ℕ) : ℝ := -((8 * (r : ℝ) ^ 3 + 6 * (r : ℝ) ^ 2 + 6 * (k : ℝ) * (r : ℝ) ^ 2 + r) / 6)

def covolN : ℝ :=
  (((D.mem u).A.T : ℕ) : ℝ) ^ (D.R.rS * Fintype.card (InfinitePlace X.B.I.F)) *
    (2 : ℝ) ^ (-((Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * D.R.k + D.R.rS * (D.R.rS - 1) / 2) : ℕ) : ℝ)) *
    |(NumberField.discr X.B.I.F : ℝ)| ^ covolumeExponent D.R.rS D.R.k

def CovolN : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (μ : Measure X.B.I.Ginf) (FdN : Set X.B.I.Ginf),
    IsHaarOnSet X.B.I (X.NinfU u) μ →
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    μ FdN = ENNReal.ofReal (covolN X u /
      (2 : ℝ) ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * (D.R.rS + 1) / 2))) * μ (boxN X u)

end Formalism.L2.SG.Pf.LsNc5
end
end
