module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle001
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoCechComplexMapPresheafCubeRes
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle045
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InductionInStagesTwoFactorsEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle046
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem trDR_projection : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], ∀ (α : DR k K) (β : DR k L),
    trDR k K L (mapDR k K L α * β) = α * trDR k K L β ∧ trDR k K L (β * mapDR k K L α) = trDR k K L β * α := by
  intro k K L _ _ _ _ _ _ _ _ _ α β
  obtain ⟨m, b, ω, rfl⟩ := (GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L).1 β
  have hT := (GlobalTheory.T.deRhamFormTrace_exists_unique k K L).1
  constructor

  · rw [Finset.mul_sum, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, ← map_mul, hT, hT, mul_smul_comm]

  · rw [Finset.sum_mul, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, ← map_mul, hT, hT, smul_mul_assoc]

end GlobalTheory.W1
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.PullMap

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

theorem prod_prod_erase (g : κ → κ → ℤ) {t : Finset κ} {i : κ} (hi : i ∈ t) (hg : g i i = 1) :
    ∏ a ∈ t, ∏ b ∈ t, g a b =
      (∏ a ∈ t.erase i, ∏ b ∈ t.erase i, g a b) * ∏ a ∈ t.erase i, (g a i * g i a) := by
  have row : ∀ a, ∏ b ∈ t, g a b = g a i * ∏ b ∈ t.erase i, g a b :=
    fun a => (Finset.mul_prod_erase t (g a) hi).symm
  have h1 := Finset.mul_prod_erase t (fun a => ∏ b ∈ t, g a b) hi
  rw [← h1, row i, hg, one_mul, Finset.prod_congr rfl (fun a _ => row a)]
  simp only [Finset.prod_mul_distrib]
  ring

theorem cubeSign_eq_prod (t : Finset κ) (i : κ) :
    cubeSign t i = ∏ a ∈ t, (if a < i then (-1 : ℤ) else 1) := by
  rw [cubeSign, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem cubeSign_image {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) (i : κ) :
    cubeSign (t.image τ) (τ i) = ∏ a ∈ t, (if τ a < τ i then (-1 : ℤ) else 1) := by
  rw [cubeSign_eq_prod, Finset.prod_image (by intro x hx y hy hxy; exact h hx hy hxy)]

theorem pair_sign {τ : κ → ι} {x i : κ} (hx : x ≠ i) (hτ : τ x ≠ τ i) :
    (if x < i ∧ τ i < τ x then (-1 : ℤ) else 1) * (if i < x ∧ τ x < τ i then (-1 : ℤ) else 1) =
      (if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1) := by
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_or_gt_of_ne hτ with h' | h' <;>
    simp [h, h', lt_asymm h, lt_asymm h']

theorem sortSign_eq_erase {τ : κ → ι} {s : Finset κ} {i : κ} (hi : i ∈ s)
    (hne : ∀ x ∈ s.erase i, τ x ≠ τ i) :
    sortSign τ s = sortSign τ (s.erase i) *
      ∏ x ∈ s.erase i, ((if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1)) := by
  have := prod_prod_erase (fun x y => if x < y ∧ τ y < τ x then (-1 : ℤ) else 1) hi (by simp)
  beta_reduce at this
  unfold sortSign
  rw [this]
  congr 1
  exact Finset.prod_congr rfl fun x hx => pair_sign (Finset.ne_of_mem_erase hx) (hne x hx)

theorem sign_inj {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    sortSign τ t * cubeSign (t.image τ) (τ i) = cubeSign t i * sortSign τ (t.erase i) := by
  have e1 := sortSign_eq_erase (τ := τ) hi (fun x hx e =>
    Finset.ne_of_mem_erase hx (h (Finset.mem_of_mem_erase hx) hi e))
  rw [Finset.prod_mul_distrib] at e1
  have e2 : cubeSign t i = ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hi]
    simp
  have e3 : cubeSign (t.image τ) (τ i) = ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) := by
    rw [cubeSign_image h, ← Finset.mul_prod_erase t _ hi]
    simp
  have hQ : (∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1)) *
      ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => by split_ifs <;> norm_num
  rw [e1, e2, e3]
  linear_combination (sortSign τ (t.erase i) * ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1)) * hQ

theorem sign_pair {τ : κ → ι} {t : Finset κ} {a b : κ} (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) :
    cubeSign t a * sortSign τ (t.erase a) = -(cubeSign t b * sortSign τ (t.erase b)) := by
  have hb' : b ∈ t.erase a := Finset.mem_erase.2 ⟨hab.symm, hb⟩
  have ha' : a ∈ t.erase b := Finset.mem_erase.2 ⟨hab, ha⟩
  have hu' : (t.erase b).erase a = (t.erase a).erase b := Finset.erase_right_comm
  have mem : ∀ x ∈ (t.erase a).erase b, τ x ≠ τ b := by
    intro x hx e
    have hx1 := Finset.mem_erase.1 hx
    exact hx1.1 (h hx1.2 hb' e)
  have e1 := sortSign_eq_erase (τ := τ) hb' mem
  have e2 := sortSign_eq_erase (τ := τ) ha' (by rw [hu', he]; exact mem)
  rw [hu', he] at e2
  have c1 : cubeSign t a = (if b < a then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < a then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hb, ← Finset.mul_prod_erase (t.erase b) _ ha', hu']
    simp only [lt_self_iff_false, if_false, one_mul]
  have c2 : cubeSign t b = (if a < b then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < b then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ ha, ← Finset.mul_prod_erase (t.erase a) _ hb']
    simp only [lt_self_iff_false, if_false, one_mul]
  have hs : (if b < a then (-1 : ℤ) else 1) = -(if a < b then (-1 : ℤ) else 1) := by
    rcases lt_or_gt_of_ne hab with h' | h' <;> simp [h', lt_asymm h']
  rw [e1, e2, c1, c2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hs]
  ring

theorem image_erase_of_injOn {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    (t.image τ).erase (τ i) = (t.erase i).image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    exact ⟨x, ⟨fun e => hy (congrArg τ e), hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxi, hx⟩, rfl⟩
    exact ⟨fun e => hxi (h hx hi e), x, hx, rfl⟩

theorem image_erase_eq {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b) (he : τ a = τ b) :
    (t.erase a).image τ = t.image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨_, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    by_cases hxa : x = a
    · exact ⟨b, ⟨hab.symm, hb⟩, by rw [hxa]; exact he.symm⟩
    · exact ⟨x, ⟨hxa, hx⟩, rfl⟩

theorem injOn_erase_swap {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) : Set.InjOn τ (t.erase b) := by
  intro x hx y hy hxy
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx hy
  have hb' : b ∈ (↑(t.erase a) : Set κ) := by simp [hab.symm, hb]
  by_cases hxa : x = a <;> by_cases hya : y = a
  · rw [hxa, hya]
  · exact absurd (h (by simp [hya, hy.1]) hb' (by rw [← hxy, hxa, he])) hy.2
  · exact absurd (h (by simp [hxa, hx.1]) hb' (by rw [hxy, hya, he])) hx.2
  · exact h (by simp [hxa, hx.1]) (by simp [hya, hy.1]) hxy

variable {k : Type} [Field k] {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']


open Classical in
theorem pullC_apply (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) (s : Finset κ) :
    pullC τ φ c s = if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0 := rfl

theorem pullC_delta (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) :
    pullC τ φ (GlobalTheory.DI.delta c) = GlobalTheory.DI.delta (pullC τ φ c) := by
  funext t
  rw [pullC_apply]
  simp only [GlobalTheory.DI.delta]
  by_cases h : Set.InjOn τ t

  · rw [if_pos h, Finset.sum_image (by intro x hx y hy hxy; exact h hx hy hxy), map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [pullC_apply, if_pos (h.mono (Finset.coe_subset.2 (Finset.erase_subset i t))), map_zsmul,
      ← image_erase_of_injOn h hi, smul_smul, smul_smul, sign_inj h hi]
  · rw [if_neg h]
    have h' : ∃ a ∈ t, ∃ b ∈ t, τ a = τ b ∧ a ≠ b := by
      by_contra hc
      push_neg at hc
      exact h (by intro x hx y hy hxy; exact hc x hx y hy hxy)
    obtain ⟨a, ha, b, hb, he, hab⟩ := h'
    have zero_of : ∀ s : Finset κ, a ∈ s → b ∈ s → pullC τ φ c s = 0 := fun s has hbs => by
      rw [pullC_apply, if_neg]
      intro hs
      exact hab (hs has hbs he)
    rw [Finset.sum_eq_add_of_mem a b ha hb hab (fun x _ hne => by
      rw [zero_of _ (Finset.mem_erase.2 ⟨hne.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hne.2.symm, hb⟩), smul_zero])]
    by_cases hia : Set.InjOn τ (t.erase a)
    · have hib := injOn_erase_swap hb hab he hia
      rw [pullC_apply, pullC_apply, if_pos hia, if_pos hib, image_erase_eq hb hab he,
        image_erase_eq ha hab.symm he.symm, smul_smul, smul_smul, ← add_smul, sign_pair ha hb hab he hia,
        neg_add_cancel, zero_smul]
    · have hib : ¬ Set.InjOn τ (t.erase b) := fun hib => hia (injOn_erase_swap ha hab.symm he.symm hib)
      rw [pullC_apply, pullC_apply, if_neg hia, if_neg hib, smul_zero, smul_zero, add_zero]

theorem pullC_mem (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (τ : κ → ι) (φ : E →ₗ[k] E')
    (hφ : ∀ s : Finset κ, s.Nonempty → ∀ y ∈ A (s.image τ), φ y ∈ B s) (n : ℤ) (c : Finset ι → E)
    (hc : c ∈ cechC A n) : pullC τ φ c ∈ cechC B n := by
  simp only [cechC, Submodule.mem_pi, Set.mem_univ, true_implies, forall_const] at hc ⊢
  intro s
  rw [pullC_apply]
  split_ifs with hs hinj
  · have hcard := Finset.card_image_of_injOn hinj
    have hc' := hc (s.image τ)
    rw [if_pos ⟨hs.1.image τ, by rw [hcard]; exact hs.2⟩] at hc'
    exact zsmul_mem (hφ s hs.1 _ hc') _
  · exact Submodule.zero_mem _
  · rename_i hinj
    have hc' := hc (s.image τ)
    rw [if_neg (fun h' => hs ⟨Finset.image_nonempty.1 h'.1, by
      rw [← Finset.card_image_of_injOn hinj]; exact h'.2⟩), Submodule.mem_bot] at hc'
    rw [hc', map_zero, smul_zero]
    exact Submodule.zero_mem _
  · exact Submodule.zero_mem _

end GlobalTheory.PD.PullMap

namespace GlobalTheory.PD

theorem pullC_isMap : ∀ (k : Type) [Field k] (ι κ : Type) [LinearOrder ι] [LinearOrder κ] (E E' : Type)
    [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (τ : κ → ι) (φ : E →ₗ[k] E'),
    (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) →
    (∀ s : Finset κ, s.Nonempty → ∀ y ∈ A (s.image τ), φ y ∈ B s) →
    IsMap (GlobalTheory.PD.cech A) (GlobalTheory.PD.cech B) (pullC τ φ) := by
  intro k _ ι κ _ _ E E' _ _ _ _ A B τ φ _ _ hφ n c hc
  exact ⟨PullMap.pullC_mem A B τ φ hφ n c hc, PullMap.pullC_delta τ φ c⟩

end GlobalTheory.PD
end
end

section

noncomputable section

namespace GlobalTheory.ParUpRoad

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem spehLoc_twist (hL : ParamLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  obtain ⟨hsum, hzero, htw, -, -⟩ := hL w
  have hχ := A.locG_dim χ w
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact (hzero _ hχ).symm
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, hsum _ _ _ hχ, htw _ _ _ hχ, A.locG_tw]

theorem isoLoc_twist (hL : ParamLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w).2.1 _ hχ).symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, spehLoc_twist N A hL, (hL w).1 _ _ _ hχ]

theorem isoLoc_append_singleton (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil =>
    change A.lpSum (spehLoc N A q w) (A.lpZero w) = A.lpSum (A.lpZero w) (spehLoc N A q w)
    exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

theorem isoLoc_lift (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by
  rw [isoLoc_twist N A hL, isoLoc_append_singleton]
  rfl

theorem ptV_of_thetaOf (hL : ParamLaws N A) {i : N.Loc} (hS : SplitLift N A i) (hP : PtOfLoc N A i)
    {x : N.X i} {Sig : List (Part A.CG)} (hx : HasParamX N A i x Sig) {σ : what₂.FT}
    (hσ : ∀ w, SplitOut N i w → isoLoc N A Sig w = A.locW i σ w) {P : A.AV i}
    (hθ : thetaOf N A i σ P) : A.ptV i P = some x := by
  obtain ⟨P', hP', hbc⟩ := hx
  refine hP P P' x hP' fun w hw => ?_
  rw [hS σ P hθ w hw.1, ← hσ w hw, ← isoLoc_lift N A hL, hbc.2.2.2.1 w hw.1]

theorem thetaTMapsIntoEigOut (hθ : EachRowHasThetaLift N A) (hL : ParamLaws N A)
    (hS : ∀ i, SplitLift N A i) (hP : ∀ i, PtOfLoc N A i) : ThetaTMapsIntoEigOut N A := by
  intro i x Sig _ hx
  have key : MjSigOut N A i Sig ≤ (eigC N A i x).comap (what₂.thetaT (N.mu i) (N.j i)) := by
    unfold MjSigOut
    refine iSup₂_le fun σ hσ => ?_
    by_cases h0 : what₂.isot (N.j i) σ = ⊥
    · rw [h0]; exact bot_le
    obtain ⟨P, hPθ⟩ := hθ i σ h0
    have hpt : A.ptV i P = some x := ptV_of_thetaOf N A hL (hS i) (hP i) hx hσ hPθ
    rw [← Submodule.map_le_iff_le_comap]
    refine hPθ.2.trans ?_
    unfold eigC
    exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | A.ptV i P = some x}) => A.typeV i P) P hpt le_rfl
  exact fun f hf => key hf

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    EachRowHasThetaLift N A → ParamLaws N A → (∀ i, SplitLift N A i) → (∀ i, PtOfLoc N A i) →
      ThetaTMapsIntoEig N A :=
  fun _ _ _ N A hθ hL hS hP => thetaTMapsIntoEig_of_out N A (thetaTMapsIntoEigOut N A hθ hL hS hP)

end GlobalTheory.ParUpRoad
end
end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe v v' u u'

noncomputable section

namespace GlobalTheory

structure Cube.PullHom {ι κ : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
    (σ : R →+* S) (τ : κ → ι) (A : Cube.{v} ι R) (B : Cube.{v'} κ S) where

  app : ∀ s : Finset κ, A.obj (s.image τ) →ₛₗ[σ] B.obj s

  app_res : ∀ {s t : Finset κ} (h : s ⊆ t) (x : A.obj (s.image τ)),
    app t (Cube.res A (Finset.image_subset_image h) x) = Cube.res B h (app s x)

namespace Cube.PullHom

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R] {S : Type u'} [Ring S]
  {σ : R →+* S} {τ : κ → ι} {A : Cube.{v} ι R} {B : Cube.{v'} κ S} (ψ : Cube.PullHom σ τ A B)

theorem card_image {p : ℕ} (t : {s : Finset κ // s.card = p}) (h : Set.InjOn τ (t.1 : Set κ)) :
    (t.1.image τ).card = p := by
  rw [Finset.card_image_of_injOn h, t.2]


open Classical in
def term (p : ℕ) : Cube.Term A p →ₛₗ[σ] Cube.Term B p where
  toFun x t := if h : Set.InjOn τ (t.1 : Set κ) then
      PD.sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, card_image t h⟩) else 0
  map_add' x y := by
    funext t
    by_cases h : Set.InjOn τ (t.1 : Set κ)
    · simp only [dif_pos h, Pi.add_apply, map_add (f := _), smul_add]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' r x := by
    funext t
    by_cases h : Set.InjOn τ (t.1 : Set κ)
    · simp only [dif_pos h, Pi.smul_apply, map_smulₛₗ, smul_comm (PD.sortSign τ t.1) (σ r)]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero]

theorem term_apply_of_injOn {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : Set.InjOn τ (t.1 : Set κ)) :
    ψ.term p x t = PD.sortSign τ t.1 • ψ.app t.1 (x ⟨t.1.image τ, card_image t h⟩) := by
  unfold term
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]

theorem term_apply_of_not_injOn {p : ℕ} (x : Cube.Term A p) (t : {s : Finset κ // s.card = p})
    (h : ¬ Set.InjOn τ (t.1 : Set κ)) : ψ.term p x t = 0 := by
  unfold term
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg h]

end Cube.PullHom

section Sheaf

open SheafPull

variable {T T' : TopCat.{u}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {V : Opens T}
  {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'} (τ : κ → ι)
  (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
  {F : AbSheaf T} {G : AbSheaf T'}

def cechAbPull (φ : F ⟶ (push f).obj G) :
    Cube.PullHom (RingHom.id ℤ) τ (cechAbCube F.obj V U) (cechAbCube G.obj V' U') where
  app s := (G.obj.map (homOfLE (hτ s)).op).hom.toIntLinearMap ∘ₗ
    (φ.hom.app (op (cechOpen V U (s.image τ)))).hom.toIntLinearMap
  app_res {s t} h x := by
    have e : φ.hom.app (op (cechOpen V U (t.image τ)))
        (F.obj.map (homOfLE (cechOpen_anti V U (Finset.image_subset_image (f := τ) h))).op x) =
        G.obj.map ((Opens.map f).map
          (homOfLE (cechOpen_anti V U (Finset.image_subset_image (f := τ) h)))).op
          (φ.hom.app (op (cechOpen V U (s.image τ))) x) :=
      ConcreteCategory.congr_hom (φ.hom.naturality _) x
    refine (congrArg (G.obj.map (homOfLE (hτ t)).op) e).trans ?_
    refine (ConcreteCategory.congr_hom (G.obj.map_comp _ _) _).symm.trans
      (Eq.trans ?_ (ConcreteCategory.congr_hom (G.obj.map_comp (homOfLE (hτ s)).op
        (homOfLE (cechOpen_anti V' U' h)).op) _))
    rfl

end Sheaf

end GlobalTheory
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.parabolicInductionProduct_equiv_of_no_blocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α α' n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype α'] [LinearOrder α'] [IsEmpty α'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {m' : α' → Type} [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)] (e : (Σ a, m a) ≃ n) (e' : (Σ a, m' a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] {X' : α' → Type} [∀ a, AddCommGroup (X' a)] [∀ a, Module ℂ (X' a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (σ' : ∀ a, Representation ℂ (GL (m' a) k) (X' a)), Nonempty ((multiProd e σ).Equiv (multiProd e' σ')) := by
  first | exact @GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty | exact GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty | (intros; apply GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {γ γ' n : Type} [Fintype γ] [LinearOrder γ] [Fintype γ'] [LinearOrder γ'] [Fintype n] [DecidableEq n] (f : γ' → γ), StrictMono f → Function.Surjective f → ∀ {m : γ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (e : (Σ c, m c) ≃ n) (e₂ : (Σ c', m (f c')) ≃ n), (∀ c' x, e₂ ⟨c', x⟩ = e ⟨f c', x⟩) → ∀ {X : γ → Type} [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (σ : ∀ c, Representation ℂ (GL (m c) k) (X c)), Nonempty ((multiProd e σ).Equiv (multiProd e₂ fun c' => σ (f c'))) := by
  first | exact @GlobalTheory.SmGL.BlockRename.multiProd_rename | exact GlobalTheory.SmGL.BlockRename.multiProd_rename | (intros; apply GlobalTheory.SmGL.BlockRename.multiProd_rename <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inductionInStages_twoFactors_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {β₀ β₁ a b n V W U : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a) (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b), (∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩) → (∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) → ∀ (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V) (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U) (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U), (∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i))) (ρ₁ fun j => g (toLex (.inr j))) x)) → Nonempty ((ind₂ h (extTensor (parInd ψ₀ ρ₀) (parInd ψ₁ ρ₁))).Equiv (parInd E σ)) := by
  first | exact @GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv | exact GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv | (intros; apply GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.splittingSieve_mem_etaleTopology : ∀ {Z X S : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (x : S ⟶ X), GlobalTheory.EtC.Tr.splitSieve f x ∈ Scheme.etaleTopology S := by
  first | exact @GlobalTheory.EtC.Tr.splitSieve_mem | exact GlobalTheory.EtC.Tr.splitSieve_mem | (intros; apply GlobalTheory.EtC.Tr.splitSieve_mem <;> assumption)
end
