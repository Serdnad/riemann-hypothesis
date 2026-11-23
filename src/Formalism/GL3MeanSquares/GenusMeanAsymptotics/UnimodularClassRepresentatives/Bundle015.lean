module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle014
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle009
public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Lemmata.GeneralBFactSecondForm.Imports
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsOrthTuple
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsPrimitiveNorm
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LinearIndependentOfGramDetNeZero
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace StabilizerLattices

section One

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hp := hd x hx
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := h x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hp σ.toRingHom)
      ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom, Finset.mem_univ _⟩
  rw [← hre] at hpos
  have : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    simp
  rw [this] at hpos
  exact_mod_cast hpos

theorem exists_smul_mem {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsFullLattice K Λ) (v : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • v ∈ Λ :=
  Bl.general_b_fact_second_form.goal1 hΛ v

scoped instance latAct (h : V →ₗ⋆[K] V →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h) (Submodule (𝓞 K) V) where
  smul g Λ := Formalism.HermitianLatticesTheory.gmap g.1 Λ
  one_smul := autSub_gmap_one
  mul_smul a b Λ := autSub_gmap_mul a.1 b.1 Λ

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem smul_pair (g : Formalism.HermitianLatticesTheory.isom h) (p : Submodule (𝓞 K) V × V) :
    g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, g.1 p.2) := rfl

def stabLatEquiv (Λ : Submodule (𝓞 K) V) :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) Λ ≃ Formalism.ThetaLiftIndependence.autL h Λ where
  toFun a := ⟨a.1.1, a.1.2, MulAction.mem_stabilizer_iff.mp a.2⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, MulAction.mem_stabilizer_iff.mpr b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pairs (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (n : K) :
    Set (Submodule (𝓞 K) V × V) :=
  {p | p.1 ∈ Formalism.HermitianLatticesTheory.genus h L ∧ p.2 ∈ p.1 ∧ h p.2 p.2 = n}

theorem apply_mem_gmap (g : V ≃ₗ[K] V) {Λ : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Λ) :
    g x ∈ Formalism.HermitianLatticesTheory.gmap g Λ := by
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
  exact hx

theorem pairs_stable (hs : h.IsSymm) (L : Submodule (𝓞 K) V) (n : K) (g : Formalism.HermitianLatticesTheory.isom h)
    (p : Submodule (𝓞 K) V × V) (hp : p ∈ pairs h L n) : g • p ∈ pairs h L n :=
  ⟨OrbitRepresentatives.gmap_mem_genus hs hp.1 g.2, apply_mem_gmap g.1 hp.2.1, (g.2 p.2 p.2).trans hp.2.2⟩

def perpO (h : V →ₗ⋆[K] V →ₗ[K] K) (x : V) : Submodule (𝓞 K) V :=
  (LinearMap.ker (h x)).restrictScalars (𝓞 K)

theorem mem_perpO (x v : V) : v ∈ perpO h x ↔ h x v = 0 := Iff.rfl

def proj (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Submodule (𝓞 K) V × V) : Submodule (𝓞 K) V × V :=
  (p.1 ⊓ perpO h p.2, p.2)

theorem proj_smul (g : Formalism.HermitianLatticesTheory.isom h) (p : Submodule (𝓞 K) V × V) :
    proj h (g • p) = g • proj h p := by
  refine Prod.ext ?_ rfl
  ext v
  change v ∈ Formalism.HermitianLatticesTheory.gmap g.1 p.1 ⊓ perpO h (g.1 p.2) ↔
    v ∈ Formalism.HermitianLatticesTheory.gmap g.1 (p.1 ⊓ perpO h p.2)
  rw [Submodule.mem_inf, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Submodule.mem_inf,
    mem_perpO, mem_perpO]
  have : h (g.1 p.2) v = h p.2 (g.1.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply g.1 v]
    exact g.2 _ _
  rw [this]

end One

section Two

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open SplitBAux

theorem isLattice_cut (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Submodule.IsLattice K Λ) : Submodule.IsLattice K (S.cut Λ) := by
  refine ⟨?_, ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    have hle : (S.cut Λ).map (S.ι.restrictScalars (𝓞 K)) ≤ Λ := Submodule.map_comap_le _ _
    exact Submodule.fg_of_fg_map_injective (S.ι.restrictScalars (𝓞 K)) S.inj
      (Submodule.FG.of_le_of_isNoetherian hle)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

theorem isFullLattice_cut (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) : Submodule.IsFullLattice K (S.cut L) := by
  refine { toIsLattice := isLattice_cut S hL.toIsLattice, span_eq_top := ?_ }
  rw [eq_top_iff]
  intro a _
  have ha : S.ι a ∈ Submodule.span K (L : Set V) := by
    rw [hL.span_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hy, r, hya⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 K))).mp ha
  rw [Submodule.span_eq] at hy
  have hr : (r : 𝓞 K) • a ∈ S.cut L := by
    rw [S.mem_cut_iff, ← algebraMap_smul K (r : 𝓞 K), map_smul, hya, smul_smul,
      IsLocalization.mk'_spec', map_one, one_smul]
    exact hy
  have hmul := Submodule.smul_mem (Submodule.span K (S.cut L : Set V'))
    (IsLocalization.mk' K 1 r) (Submodule.subset_span hr)
  rwa [← algebraMap_smul K (r : 𝓞 K), smul_smul, IsLocalization.mk'_spec, map_one, one_smul] at hmul

def emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : Submodule (𝓞 K) V :=
  Λ'.map (S.ι.restrictScalars (𝓞 K))

theorem cut_emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : S.cut (emb S Λ') = Λ' :=
  Submodule.comap_map_eq_of_injective (f := S.ι.restrictScalars (𝓞 K)) S.inj Λ'

theorem emb_injective (S : VecSplit h h') : Function.Injective (emb S) := fun A B e => by
  rw [← cut_emb S A, e, cut_emb]

theorem inf_perpO (S : VecSplit h h') (Λ : Submodule (𝓞 K) V) :
    Λ ⊓ perpO h S.x₀ = emb S (S.cut Λ) := by
  ext v
  constructor
  · rintro ⟨hv, hv0⟩
    obtain ⟨a, rfl⟩ := exists_of_orth S hv0
    exact Submodule.mem_map.mpr ⟨a, hv, rfl⟩
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨ha, S.orth a⟩

theorem gmap_extOf_emb (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (C : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') (emb S C) = emb S (Formalism.HermitianLatticesTheory.gmap g' C) := by
  unfold Formalism.HermitianLatticesTheory.gmap emb
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext a
  exact extOf_ι S g' a

theorem cut_gmap_extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (Λ : Submodule (𝓞 K) V) :
    S.cut (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = Formalism.HermitianLatticesTheory.gmap g' (S.cut Λ) := by
  ext a
  rw [VecSplit.mem_cut_iff, mem_gmap_iff, mem_gmap_iff, VecSplit.mem_cut_iff, eq_decomp_ι S a,
    extOf_symm_apply, ← eq_decomp_ι]

theorem stab_pair_iff (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') (g : Formalism.HermitianLatticesTheory.isom h) :
    g ∈ MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ↔
      Formalism.HermitianLatticesTheory.gmap g.1 (emb S Λ') = emb S Λ' ∧ g.1 S.x₀ = S.x₀ := by
  rw [MulAction.mem_stabilizer_iff, smul_pair, Prod.ext_iff]

def stabPairEquiv (hs : h.IsSymm) (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ≃
      Formalism.ThetaLiftIndependence.autL h' Λ' where
  toFun a := ⟨res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2,
    res_mem_isom S _ _ _, by
      have := gmap_res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2
        ((stab_pair_iff S Λ' a.1).mp a.2).1
      rwa [cut_emb] at this⟩
  invFun b := ⟨⟨extOf S b.1, extOf_mem_isom hs S b.2.1⟩, (stab_pair_iff S Λ' _).mpr
    ⟨by rw [gmap_extOf_emb, b.2.2], extOf_x₀ S _⟩⟩
  left_inv a := Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective
    (linearMap_ext S (by simp [extOf_x₀, ((stab_pair_iff S Λ' a.1).mp a.2).2])
      (fun v => by simp [extOf_ι, res_spec]))))
  right_inv b := Subtype.ext (LinearEquiv.ext fun v => S.inj (by simp [res_spec, extOf_ι]))

end Two

end StabilizerLattices

end Formalism.HermitianLattices.Ext.L3
end
end

section

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA Module

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem gram_det_smul_orth {n : ℕ} {y : Fin n → V} (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0)
    (d : Fin n → K) :
    (gram h fun i => d i • y i).det = (∏ i, star (d i) * d i) * ∏ i, h (y i) (y i) := by
  have hg : (gram h fun i => d i • y i) =
      Matrix.diagonal fun i => star (d i) * d i * h (y i) (y i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [gram]
      simp only [starRingEnd_apply]
      ring
    · simp [gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [hg, Matrix.det_diagonal, Finset.prod_mul_distrib]

theorem gram_det_orth {n : ℕ} {y : Fin n → V} (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) :
    (gram h y).det = ∏ i, h (y i) (y i) := by
  have hg : gram h y = Matrix.diagonal fun i => h (y i) (y i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [gram]
    · simp [gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [hg, Matrix.det_diagonal]

theorem expand_orth [FiniteDimensional K V] {y : Fin (finrank K V) → V}
    (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) (hne : ∀ i, h (y i) (y i) ≠ 0) (v : V) :
    v = ∑ i, (h (y i) v * (h (y i) (y i))⁻¹) • y i := by
  have hli : LinearIndependent K y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hj := congrArg (h (y j)) hg

    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact (mul_eq_zero.mp hj).resolve_right (hne j)
  by_cases h0 : finrank K V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact Subsingleton.elim _ _
  have : Nonempty (Fin (finrank K V)) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
  set b := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _) with hb
  have hbi : ∀ i, b i = y i := fun i => by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hv : ∑ i, b.repr v i • y i = v := by
    simp_rw [← hbi]
    exact b.sum_repr v
  have hc : ∀ j, b.repr v j = h (y j) v * (h (y j) (y j))⁻¹ := by
    intro j
    rw [eq_mul_inv_iff_mul_eq₀ (hne j)]
    have hj := congrArg (h (y j)) hv

    simp only [map_sum, map_smul, smul_eq_mul] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact hj
  calc v = ∑ i, b.repr v i • y i := hv.symm
    _ = _ := Finset.sum_congr rfl fun i _ => by rw [hc i]

theorem exists_isASD_of_tuple [FiniteDimensional K V] (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {M : AddSubgroup V} (hM : IsLatIn S h ⊤ M)
    (x : Fin (finrank K V) → V) (hx : ∀ i, x i ∈ M)
    (hdet : ¬ Dv S π ((gram h x).det * π⁻¹))
    (hall : ∀ t : Fin (finrank K V) → V, (∀ i, t i ∈ M) → (∀ i j, i ≠ j → h (t i) (t j) = 0) →
      Dv S π (gram h t).det) :
    ∃ z, IsASD S π h ⊤ M z := by
  obtain ⟨y, horth, hspan⟩ := exists_orth_tuple hS hπ hs _ x
    (fun i j => hM.int _ (hx i) _ (hx j)) hdet
  have hyM : ∀ i, y i ∈ M := by
    intro i
    have h1 : y i ∈ spanS S x := by rw [← hspan]; exact mem_spanS y i
    exact spanS_induction (p := fun v => v ∈ M) M.zero_mem (fun a b => M.add_mem)
      (fun c hc a ha => hM.smul_mem c hc a ha) hx _ h1
  have haS : ∀ i, h (y i) (y i) ∈ S := fun i => hM.int _ (hyM i) _ (hyM i)
  obtain ⟨c, hcS, hcdet⟩ := gram_det_of_le (h := h) hS
    (fun i => by rw [hspan]; exact mem_spanS x i : ∀ i, x i ∈ spanS S y)
  rw [gram_det_orth horth] at hcdet
  have hPd : Dv S π (∏ i, h (y i) (y i)) := by
    rw [← gram_det_orth horth]; exact hall y hyM horth
  have hPn : ¬ Dv S π ((∏ i, h (y i) (y i)) * π⁻¹) := by
    intro hdv
    apply hdet
    rw [hcdet, mul_assoc]
    exact hdv.mul_left hcS
  have hPf : star ((∏ i, h (y i) (y i)) * π⁻¹) = (∏ i, h (y i) (y i)) * π⁻¹ := by
    rw [star_mul', star_inv₀, hπ.fix, ← starRingEnd_apply, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun i _ => hs.eq _ _
  have hPu : IsUnitIn S ((∏ i, h (y i) (y i)) * π⁻¹) := unit_of_not_dv hπ hPd hPf hPn
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, ¬ IsUnitIn S (h (y i₁) (y i₁)) := by
    by_contra hcon
    push Not at hcon
    exact unit_not_dv hπ (LocF.isUnitIn_prod Finset.univ _ fun i _ => hcon i) hPd
  have hd₁ : Dv S π (h (y i₁) (y i₁)) := dv_of_not_unit hπ (haS i₁) (hs.eq _ _) hi₁
  have hQS : ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i) ∈ S := S.prod_mem fun i _ => haS i
  have hsplit : (∏ i, h (y i) (y i)) * π⁻¹ =
      h (y i₁) (y i₁) * π⁻¹ * ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₁)]
    ring
  have hQu : IsUnitIn S (∏ i ∈ Finset.univ.erase i₁, h (y i) (y i)) :=
    isUnitIn_of_mul hd₁ hQS (hsplit ▸ hPu)
  have hzu : IsUnitIn S (h (y i₁) (y i₁) * π⁻¹) :=
    isUnitIn_of_mul hQS hd₁ (by rw [mul_comm, ← hsplit]; exact hPu)
  have hau : ∀ i, i ≠ i₁ → IsUnitIn S (h (y i) (y i)) := by
    intro i hi
    have hmem : i ∈ Finset.univ.erase i₁ := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have e := Finset.mul_prod_erase (Finset.univ.erase i₁) (fun i => h (y i) (y i)) hmem
    refine isUnitIn_of_mul (S.prod_mem fun j _ => haS j :
      ∏ j ∈ (Finset.univ.erase i₁).erase i, h (y j) (y j) ∈ S) (haS i) ?_
    rw [mul_comm, e]
    exact hQu
  have hne : ∀ i, h (y i) (y i) ≠ 0 := by
    intro i
    by_cases hi : i = i₁
    · rw [hi]; exact left_ne_zero_of_mul hzu.1
    · exact (hau i hi).1
  have hexp := expand_orth horth hne

  have hprim : ∀ c : K, c • y i₁ ∈ M → c ∈ S := by
    have hy0 : y i₁ ≠ 0 := by
      intro h0
      apply hne i₁
      rw [h0]; simp
    obtain ⟨l, hl0, hl, hdiv⟩ := exists_primitive hS hd hM (Submodule.mem_top : y i₁ ∈ ⊤) hy0
    have hli : l⁻¹ ∈ S := by
      have := hdiv 1 (by rw [one_smul]; exact hyM i₁)
      rwa [one_mul] at this
    have hNl : star l * l ∈ S := by
      have h1 := hall (fun i => (if i = i₁ then l else 1) • y i) (by
        intro i
        by_cases hi : i = i₁
        · simp only [hi, ite_true]; exact hl
        · simp only [hi, ite_false, one_smul]; exact hyM i) (by
        intro i j hij
        simp only [map_smulₛₗ, LinearMap.smul_apply, horth i j hij, smul_zero])
      rw [gram_det_smul_orth horth] at h1
      have e : (∏ i, star (if i = i₁ then l else 1) * (if i = i₁ then l else 1)) = star l * l := by
        rw [Finset.prod_eq_single i₁]
        · simp
        · intro j _ hj; simp [hj]
        · intro hi; exact absurd (Finset.mem_univ i₁) hi
      rw [e] at h1
      unfold Dv at h1
      have h2 := S.mul_mem h1 hPu.2.2
      have h0 := hPu.1
      have e2 : star l * l * (∏ i, h (y i) (y i)) * π⁻¹ * ((∏ i, h (y i) (y i)) * π⁻¹)⁻¹ =
          star l * l := by
        rw [mul_assoc (star l * l), mul_assoc, mul_inv_cancel₀ h0, mul_one]
      rwa [e2] at h2
    have hlS : l ∈ S := by
      have hu : IsUnitIn S (star l⁻¹ * l⁻¹) := by
        refine ⟨mul_ne_zero (star_ne_zero.mpr (inv_ne_zero hl0)) (inv_ne_zero hl0),
          S.mul_mem (hS.star_mem _ hli) hli, ?_⟩
        rw [star_inv₀, mul_inv, inv_inv, inv_inv]
        exact hNl
      have := (isUnitIn_of_mul (hS.star_mem _ hli) hli hu).2.2
      rwa [inv_inv] at this
    intro c hc
    have := S.mul_mem (hdiv c hc) hlS
    rwa [mul_assoc, inv_mul_cancel₀ hl0, mul_one] at this
  refine ⟨y i₁, hM, hyM i₁, hzu, ?_, ?_⟩
  · intro m hm
    have hcS : ∀ i, i ≠ i₁ → h (y i) m * (h (y i) (y i))⁻¹ ∈ S := fun i hi =>
      S.mul_mem (hM.int _ (hyM i) _ hm) (hau i hi).2.2
    have h1 : (h (y i₁) m * (h (y i₁) (y i₁))⁻¹) • y i₁ ∈ M := by
      have e := Finset.add_sum_erase Finset.univ
        (fun i => (h (y i) m * (h (y i) (y i))⁻¹) • y i) (Finset.mem_univ i₁)
      rw [← hexp m] at e
      rw [eq_sub_of_add_eq e]
      exact M.sub_mem hm (M.sum_mem fun i hi =>
        hM.smul_mem _ (hcS i (Finset.mem_erase.mp hi).1) _ (hyM i))
    have h2 := hd₁.mul_left (hprim _ h1)
    rwa [mul_assoc, inv_mul_cancel₀ (hne i₁), mul_one] at h2
  · intro v _ hzv hv
    rw [hexp v]
    refine M.sum_mem fun i _ => ?_
    by_cases hi : i = i₁
    · rw [hi, hzv, zero_mul, zero_smul]; exact M.zero_mem
    · exact hM.smul_mem _ (S.mul_mem (hv _ (hyM i)) (hau i hi).2.2) _ (hyM i)

end Formalism.HermitianLattices.Ext.L3.U0
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

def starFixed (K : Type) [Field K] [CharZero K] [StarRing K] : IntermediateField ℚ K where
  carrier := {a : K | star a = a}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [star_mul', ha, hb]
  one_mem' := star_one K
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [star_add, ha, hb]
  zero_mem' := star_zero K
  algebraMap_mem' := by
    intro q
    exact map_ratCast (starRingEnd K) q
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [star_inv₀, ha]

theorem exists_fixF (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra F K), IsFixF K F := by
  haveI : FiniteDimensional ℚ (starFixed K) := IntermediateField.finiteDimensional_left (starFixed K)
  haveI : NumberField (starFixed K) := ⟨⟩
  refine ⟨starFixed K, inferInstance, inferInstance, inferInstance, fun a => ?_⟩
  constructor
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact b.2

end Formalism.HermitianLattices.Ext.L3
end
end
