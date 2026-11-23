module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle039
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtHomInjective
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle041
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle042
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldFurther
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle040
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def aLoc (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (n : 𝓞 F) : ℝ :=
  alphaN h L 𝔭.1 n / eFac K (finrank K V) 𝔭.1


open scoped Classical in
def roL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (j : ℕ) : ℝ :=
  if 𝔭 ∈ S then 1 else aLoc h L 𝔭 (exists_vF_eq 𝔭.2 j).choose

variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
  {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
  (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
  {S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}}
  (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S)

include hK hF hs hd hL hLi hS

theorem aLoc_eq_roL {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (h𝔭 : 𝔭 ∉ S) {n : 𝓞 F} (hn : n ≠ 0) :
    aLoc h L 𝔭 n = roL h L S 𝔭 (valF n 𝔭) := by
  have hv : vd h L 𝔭.1 = 0 := by
    by_contra hne
    exact h𝔭 (hS 𝔭 hne)
  obtain ⟨hn', hvn'⟩ := (exists_vF_eq 𝔭.2 (valF n 𝔭)).choose_spec
  rw [roL, if_neg h𝔭]
  unfold aLoc
  rw [alphaN_eq_of_vF_eq hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi 𝔭.2 hv hn hn' (by rw [hvn', valF_apply hn])]

include hm

theorem roL_zero (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) : roL h L S 𝔭 0 = 1 := by
  by_cases h𝔭 : 𝔭 ∈ S
  · rw [roL, if_pos h𝔭]
  · have hv : vd h L 𝔭.1 = 0 := by
      by_contra hne
      exact h𝔭 (hS 𝔭 hne)
    obtain ⟨hn', hvn'⟩ := (exists_vF_eq 𝔭.2 0).choose_spec
    have hn𝔭 : (exists_vF_eq 𝔭.2 0).choose ∉ 𝔭.1 := by
      intro hmem
      have := (mem_pow_iff_le_vF 𝔭.2 hn' 1).mp (by rw [pow_one]; exact hmem)
      omega
    rw [roL, if_neg h𝔭]
    unfold aLoc
    rw [unitaryAbsoluteValueBounds.alphaN_unit hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi 𝔭.2 hv (by omega) hn𝔭]
    have he := eFac_pos (K := K) 𝔭.2 (m := finrank K V) (by omega)
    unfold eFac at he ⊢
    exact div_self he.ne'

theorem roL_diff (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (j : ℕ) :
    |roL h L S 𝔭 (j + 1) - roL h L S 𝔭 j| ≤
      8 * ((j : ℝ) + 2) ^ 2 / (Ideal.absNorm 𝔭.1 : ℝ) := by
  by_cases h𝔭 : 𝔭 ∈ S
  · have h1 : ∀ i, roL h L S 𝔭 i = 1 := fun i => by rw [roL, if_pos h𝔭]
    rw [h1, h1, sub_self, abs_zero]
    positivity
  · have hv : vd h L 𝔭.1 = 0 := by
      by_contra hne
      exact h𝔭 (hS 𝔭 hne)
    have hro : ∀ i, roL h L S 𝔭 i = aLoc h L 𝔭 (exists_vF_eq 𝔭.2 i).choose := fun i => by
      rw [roL, if_neg h𝔭]
    obtain ⟨hn1, hv1⟩ := (exists_vF_eq 𝔭.2 (j + 1)).choose_spec
    obtain ⟨hn0, hv0⟩ := (exists_vF_eq 𝔭.2 j).choose_spec
    rw [hro, hro]
    unfold aLoc eFac
    have hb := alphaN_rho_diff_bound hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi hm 𝔭.2 hv hn1 hn0 (by rw [hv1, hv0])
    refine hb.trans ?_
    rw [hv1]

    have key : ∀ e : ℕ, 1 ≤ e → 8 * (((j + 1 : ℕ) : ℝ) + 1) ^ 2 *
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(e : ℤ)) ≤ 8 * ((j : ℝ) + 2) ^ 2 / (Ideal.absNorm 𝔭.1 : ℝ) := by
      intro e he
      have hj : (((j + 1 : ℕ) : ℝ) + 1) = (j : ℝ) + 2 := by push_cast; ring
      rw [hj, div_eq_mul_inv]
      rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔭.1) with h0 | hpos
      · rw [h0, Nat.cast_zero, zero_zpow _ (by omega), inv_zero]
      · have hx : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by exact_mod_cast hpos
        have hz : (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(e : ℤ)) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ hx (by omega)
        rw [zpow_neg_one] at hz
        exact mul_le_mul_of_nonneg_left hz (by positivity)
    exact key _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))

omit hm in
theorem prod_aLoc {U : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (hU : S ⊆ U) {n : 𝓞 F}
    (hn : n ≠ 0) :
    ∏ 𝔭 ∈ U, aLoc h L 𝔭 n = (∏ 𝔭 ∈ S, aLoc h L 𝔭 n) * ∏ 𝔭 ∈ U, roL h L S 𝔭 (valF n 𝔭) := by
  rw [← Finset.prod_sdiff hU (f := fun 𝔭 => aLoc h L 𝔭 n),
    ← Finset.prod_sdiff hU (f := fun 𝔭 => roL h L S 𝔭 (valF n 𝔭))]
  have h1 : ∏ 𝔭 ∈ S, roL h L S 𝔭 (valF n 𝔭) = 1 :=
    Finset.prod_eq_one fun 𝔭 h𝔭 => by rw [roL, if_pos h𝔭]
  have h2 : ∏ 𝔭 ∈ U \ S, aLoc h L 𝔭 n = ∏ 𝔭 ∈ U \ S, roL h L S 𝔭 (valF n 𝔭) :=
    Finset.prod_congr rfl fun 𝔭 h𝔭 =>
      aLoc_eq_roL (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) (Finset.mem_sdiff.mp h𝔭).2 hn
  rw [h1, h2, mul_one, mul_comm]

theorem singS_eq {n : 𝓞 F} (hn : n ≠ 0) :
    singS F h L n = (∏ 𝔭 ∈ S, aLoc h L 𝔭 n) * (valF n).prod (roL h L S) := by
  classical
  have hz : ∀ 𝔭, roL h L S 𝔭 0 = 1 := fun 𝔭 => roL_zero (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hm := hm) (hS := hS) 𝔭
  have e1 : singS F h L n = ∏' 𝔭, aLoc h L 𝔭 n := rfl
  have hsup : (valF n).support ⊆ S ∪ (valF n).support := Finset.subset_union_right
  rw [e1, tprod_eq_prod (s := S ∪ (valF n).support) ?_,
    prod_aLoc (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) Finset.subset_union_left hn,
    Finsupp.prod_of_support_subset _ hsup _ (fun 𝔭 _ => hz 𝔭)]
  intro 𝔭 h𝔭
  rw [Finset.mem_union, not_or] at h𝔭
  have h0 : valF n 𝔭 = 0 := by
    by_contra hne
    exact h𝔭.2 (Finsupp.mem_support_iff.mpr hne)
  rw [aLoc_eq_roL (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) h𝔭.1 hn, h0, hz]

omit hS in
theorem prodS_bound (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ C : ℝ, ∀ n : 𝓞 F, n ≠ 0 →
      0 ≤ ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ∧ ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ≤ C := by
  have hm1 : 1 ≤ finrank K V := by omega
  choose C hC using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    alphaN_bound hK hF hs hd hL hLi hm 𝔭.2
  refine ⟨∏ 𝔭 ∈ S, C 𝔭 / eFac K (finrank K V) 𝔭.1, fun n hn => ?_⟩
  have hpos : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 0 < eFac K (finrank K V) 𝔭.1 :=
    fun 𝔭 => eFac_pos 𝔭.2 hm1
  have h0 : ∀ 𝔭 ∈ S, 0 ≤ aLoc h L 𝔭 n := fun 𝔭 _ => div_nonneg (hC 𝔭 n hn).1 (hpos 𝔭).le
  refine ⟨Finset.prod_nonneg h0, Finset.prod_le_prod₀ h0 fun 𝔭 _ => ?_⟩
  exact div_le_div_of_nonneg_right (hC 𝔭 n hn).2 (hpos 𝔭).le

end Formalism.HermitianLattices.Ext.L3.A5
end
end

section

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF

theorem exists_reps {X : Type*} (r : X → X → Prop) (hr : Equivalence r) (A X₀ : Set X)
    (hfin : X₀.Finite) (hcov : ∀ x ∈ A, ∃ t ∈ X₀, r t x) :
    ∃ R : Finset X, (∀ t ∈ R, t ∈ X₀) ∧ ∀ x ∈ A, ∃! t, t ∈ R ∧ r t x := by
  classical
  let s : Setoid X := ⟨r, hr⟩
  let pick : Quotient s → X := fun c =>
    if H : ∃ t ∈ X₀, Quotient.mk s t = c then H.choose else Quotient.out c
  have hp1 : ∀ x ∈ X₀, pick (Quotient.mk s x) ∈ X₀ ∧
      Quotient.mk s (pick (Quotient.mk s x)) = Quotient.mk s x := by
    intro x hx
    have H : ∃ t ∈ X₀, Quotient.mk s t = Quotient.mk s x := ⟨x, hx, rfl⟩
    simp only [pick, dif_pos H]
    exact H.choose_spec
  refine ⟨hfin.toFinset.image (fun x => pick (Quotient.mk s x)), ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact (hp1 x (hfin.mem_toFinset.mp hx)).1
  · intro x hx
    obtain ⟨t₀, ht₀, h0⟩ := hcov x hx
    refine ⟨pick (Quotient.mk s t₀),
      ⟨Finset.mem_image.mpr ⟨t₀, hfin.mem_toFinset.mpr ht₀, rfl⟩, ?_⟩, ?_⟩
    · exact hr.trans (Quotient.exact (hp1 t₀ ht₀).2) h0
    · rintro t' ⟨ht', h1⟩
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp ht'
      have e1 := (hp1 x' (hfin.mem_toFinset.mp hx')).2
      have e2 : Quotient.mk s x' = Quotient.mk s t₀ := by
        rw [← e1]
        exact Quotient.sound (hr.trans h1 (hr.symm h0))
      rw [e2]

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

@[reducible] def actV (S : VecSplit h h') : MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V) where
  smul g M := Formalism.HermitianLatticesTheory.gmap (extHom S g.1) M
  one_smul M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S 1) M = M
    rw [map_one]
    exact autSub_gmap_one M
  mul_smul a b M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S (a.1 * b.1)) M = _
    rw [map_mul]
    exact autSub_gmap_mul _ _ _

@[reducible] def actV' (h' : V' →ₗ⋆[K] V' →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V') where
  smul g T := Formalism.HermitianLatticesTheory.gmap g.1 T
  one_smul T := autSub_gmap_one T
  mul_smul _ _ _ := autSub_gmap_mul _ _ _

theorem stab_actV (hs : h.IsSymm) (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    @MulAction.stabilizer _ _ _ (actV S) M = (autExt S M).subgroupOf (Formalism.HermitianLatticesTheory.isom h') := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro e
    exact ⟨SplitBAux.extOf_mem_isom hs S g.2, e⟩
  · intro e
    exact e.2

theorem stab_actV' (T : Submodule (𝓞 K) V') :
    @MulAction.stabilizer _ _ _ (actV' h') T = (autSub h' T).subgroupOf (Formalism.HermitianLatticesTheory.isom h') := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

theorem autSub_le_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) :
    autSub h A ≤ Formalism.HermitianLatticesTheory.isom h := fun _ hg => hg.1

theorem relIndex_stab (hs : h.IsSymm) (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    (@MulAction.stabilizer _ _ _ (actV S) M).relIndex
      (@MulAction.stabilizer _ _ _ (actV' h') (S.cut M)) = oM S M := by
  rw [stab_actV hs, stab_actV', Subgroup.relIndex_subgroupOf (autSub_le_isom h' _)]
  rfl

theorem extOf_res (S : VecSplit h h') {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) : SplitBAux.extOf S (SplitBAux.res S g hg hx) = g := by
  apply LinearEquiv.toLinearMap_injective
  apply SplitBAux.linearMap_ext S
  · change SplitBAux.extOf S _ S.x₀ = g S.x₀
    rw [SplitBAux.extOf_x₀, hx]
  · intro a
    change SplitBAux.extOf S _ (S.ι a) = g (S.ι a)
    rw [SplitBAux.extOf_ι, SplitBAux.res_spec]

theorem gmap_smul (g : V ≃ₗ[K] V) (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (I • A) = I • Formalism.HermitianLatticesTheory.gmap g A := Submodule.map_smul'' _ _ _

theorem conj_mem_autSub {g u : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {A : Submodule (𝓞 K) V}
    (hu : u ∈ autSub h A) : g * u * g⁻¹ ∈ autSub h (Formalism.HermitianLatticesTheory.gmap g A) := by
  refine ⟨mul_mem (mul_mem hg hu.1) (inv_mem hg), ?_⟩
  rw [autSub_gmap_mul, autSub_gmap_mul, ← autSub_gmap_mul g⁻¹ g, inv_mul_cancel, autSub_gmap_one, hu.2]

theorem conj_mem_autSub' {g u : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {A : Submodule (𝓞 K) V}
    (hu : u ∈ autSub h (Formalism.HermitianLatticesTheory.gmap g A)) : g⁻¹ * u * g ∈ autSub h A := by
  refine ⟨mul_mem (mul_mem (inv_mem hg) hu.1) hg, ?_⟩
  rw [autSub_gmap_mul, autSub_gmap_mul, hu.2, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem mem_tube_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (A : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x y : V) :
    g y ∈ tube (autSub h (Formalism.HermitianLatticesTheory.gmap g A)) (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 J x ↔
      y ∈ tube (autSub h A) A 𝔭 J (g.symm x) := by
  constructor
  · rintro ⟨u, hu, hm⟩
    refine ⟨g⁻¹ * u * g, conj_mem_autSub' hg hu, ?_⟩
    rw [← gmap_smul, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, map_sub, g.symm_apply_apply] at hm
    change y - g.symm (u (g (g.symm x))) ∈ _
    rwa [g.apply_symm_apply]
  · rintro ⟨u, hu, hm⟩
    refine ⟨g * u * g⁻¹, conj_mem_autSub hg hu, ?_⟩
    rw [← gmap_smul, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
    change g.symm (g y - g (u (g.symm x))) ∈ _
    rwa [← map_sub, g.symm_apply_apply]

theorem image_tube {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (A : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x : V) :
    g '' tube (autSub h A) A 𝔭 J (g.symm x) =
      tube (autSub h (Formalism.HermitianLatticesTheory.gmap g A)) (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 J x := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_tube_gmap hg A 𝔭 J x y).2 hy
  · intro hz
    refine ⟨g.symm z, (mem_tube_gmap hg A 𝔭 J x _).1 ?_, g.apply_symm_apply z⟩
    rwa [g.apply_symm_apply]

theorem cut_props (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) :
    locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) = S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) ∧
      IsIntegralAt 𝔭 h' (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) ∧
      fibLoc S L 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) ≠ 0 := by
  rw [LocalizedFibreSets.gmap_locF] at hx ⊢
  rw [LocalizedFibreSets.cut_locF]
  refine ⟨LocalizedFibreSets.locF_idem _ _, GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF
    (UnimodularLocalization.isIntegralLat_cut S (UnimodularLocalization.isIntegralLat_gmap hg hLi)), ?_⟩
  rw [UnimodularLocalization.fibLoc_locF]
  obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).mp hx
  have hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro e
    have e1 : algebraMap (𝓞 F) (𝓞 K) t = 0 := Formalism.HermitianLatticesTheory.genusCovol_hinj (by rw [e, map_zero])
    have e2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [e1, map_zero])
    exact ht (e2 ▸ 𝔭.zero_mem)
  have hmap : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
    refine { toIsLattice := LocalizedFibreSets.isLattice_gmap g hL, span_eq_top := ?_ }
    change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective
  have hgood := BrB.good_cut (F := F) hK hF hs hd (BrB.scaleSplit S _ hc)
    hmap (UnimodularLocalization.isIntegralLat_gmap hg hLi)
    (by change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ _
        rw [algebraMap_smul]; exact hx)
  have h1 := hgood.2 ⟨𝔭, h𝔭⟩
  rw [BrB.fibLoc_scale S L h𝔭.isPrime hg ht hc] at h1
  exact h1

end Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem exists_locReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ s, IsLocReps S L 𝔭 s :=
  BrB.exists_locReps' hK hF hs hd S hL hLi h𝔭

theorem psiP_eq_sum (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 :=
  BrB.psiP_eq_sum' hs S L 𝔭 hsr

end Formalism.HermitianLattices.Ext.L3
end
end
