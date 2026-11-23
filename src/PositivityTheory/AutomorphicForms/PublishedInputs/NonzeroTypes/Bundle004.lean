module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

abbrev red (n r : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r) :=
  Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ r))


variable (k) in
def H (n r : ℕ) : Subgroup (GL (Fin n) k) := (red (k := k) n r).ker.map (incl n)

theorem inPow_algebraMap (r : ℕ) (y : 𝒪[k]) :
    InPow r (algebraMap 𝒪[k] k y) ↔ y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  constructor
  · rintro ⟨z, hz, e⟩
    have : z = y := Subtype.val_injective e
    exact this ▸ hz
  · intro h
    exact ⟨y, h, rfl⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem entry_sub (n : ℕ) (u : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (((incl n u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) =
      algebraMap 𝒪[k] k ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) := by
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map]

theorem red_eq_one_iff (n r : ℕ) (u : GL (Fin n) 𝒪[k]) :
    red (k := k) n r u = 1 ↔ ∀ i j, ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) ∈
      IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  rw [Units.ext_iff]
  constructor
  · intro h i j
    have h' := congrFun (congrFun h i) j
    rw [← Ideal.Quotient.eq]
    split_ifs with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
  · intro h
    ext i j
    have h' := Ideal.Quotient.eq.2 (h i j)
    split_ifs at h' with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'

theorem mem_KC_iff (n r : ℕ) (g : GL (Fin n) k) : g ∈ KC k n r ↔ g ∈ H k n r := by
  constructor
  · rintro ⟨⟨u, rfl⟩, hP⟩
    refine ⟨u, (red_eq_one_iff n r u).2 fun i j => ?_, rfl⟩
    have := hP i j
    rwa [entry_sub, inPow_algebraMap] at this
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [entry_sub, inPow_algebraMap]
    exact (red_eq_one_iff n r u).1 hu i j

theorem coe_H (n r : ℕ) : (H k n r : Set (GL (Fin n) k)) = KC k n r :=
  Set.ext fun g => (mem_KC_iff n r g).symm

theorem isOpen_inPow (r : ℕ) : IsOpen {x : k | InPow r x} := by
  let A : AddSubgroup k :=
    (IsLocalRing.maximalIdeal 𝒪[k] ^ r).toAddSubgroup.map (algebraMap 𝒪[k] k).toAddMonoidHom
  have hA : (A : Set k) = {x : k | InPow r x} := by
    ext x
    simp only [A, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq, InPow]
    rfl
  rw [← hA]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (IsDiscreteValuationRing.not_a_field 𝒪[k])
  have hc : (algebraMap 𝒪[k] k w) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h
    exact hw0 (Subtype.val_injective h)
  refine A.isOpen_of_mem_nhds (g := 0) ?_
  rw [mem_nhds_iff]
  refine ⟨(fun x => (algebraMap 𝒪[k] k w) ^ r * x) '' (𝒪[k] : Set k), ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨w ^ r * ⟨y, hy⟩, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw r), ?_⟩
    show algebraMap 𝒪[k] k (w ^ r * ⟨y, hy⟩) = algebraMap 𝒪[k] k w ^ r * y
    rw [map_mul, map_pow]
    rfl
  · have := (Homeomorph.mulLeft₀ _ hc).isOpenMap _ (Valuation.isOpen_integer (v := valuation k))
    simpa using this
  · exact ⟨0, zero_mem _, mul_zero _⟩

theorem isOpen_KC (n r : ℕ) : IsOpen (KC k n r) := by
  have e : KC k n r = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) ⁻¹'
        {x : k | InPow r x} := by
    ext g
    simp only [KC, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_inPow r).preimage ?_)
  have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
  fun_prop

end UpperTheory.TNZ.Grp.P_KC

namespace UpperTheory.TNZ.Grp

open P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_KC {n : ℕ} (G : Grp k n) : CompactOpenKernelProp G := by
  intro hB r
  refine ⟨?_, ?_, isOpen_KC n r, fun g hg => hg.1, ?_⟩
  · show ((Subgroup.closure (KC k n r) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = KC k n r
    rw [← coe_H, Subgroup.closure_eq]
  · intro g hg u hu
    obtain ⟨v, rfl⟩ := hg
    obtain ⟨w, hw, rfl⟩ := (mem_KC_iff n r u).1 hu
    refine (mem_KC_iff n r _).2 ⟨v * w * v⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hw ⊢
    simp [hw]
  · intro hr g hg
    refine ⟨hg.1, fun i j hij => ?_⟩
    have hne : i ≠ j := fun h => (ne_of_lt hij) (h ▸ rfl)
    obtain ⟨y, hy, e⟩ := hg.2 i j
    rw [if_neg hne, sub_zero] at e
    have hc : cc G.μ (G.bl j) (G.bl i) ≤ r := (hB.2.1 (G.bl j) (G.bl i)).le.trans hr
    exact ⟨y, Ideal.pow_le_pow_right hc hy, e⟩

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace P_PJ

variable {n : ℕ} (G : Grp k n)

theorem inPow_mono {a b : ℕ} (hab : a ≤ b) {x : k} (hx : InPow b x) : InPow a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩

theorem KC_mono {a b : ℕ} (hab : a ≤ b) : KC k n b ⊆ KC k n a := fun _ hg =>
  ⟨hg.1, fun i j => inPow_mono hab (hg.2 i j)⟩

def Jsub (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) : Subgroup (GL (Fin n) k) where
  carrier := G.JSet
  one_mem' := h1
  mul_mem' := fun ha hb => hmul _ ha _ hb
  inv_mem' := fun ha => hinv _ ha

theorem Jg_sub (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) {g : GL (Fin n) k} (hg : g ∈ G.Jg) : g ∈ G.JSet :=
  (Subgroup.closure_le (K := Jsub G h1 hmul hinv)).2 (fun _ hx => hx) hg

theorem Jg_le_KO (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) : G.Jg ≤ KO k (Fin n) := fun _ hg =>
  (Jg_sub G h1 hmul hinv hg).1

theorem core (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    (hlM : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, G.lam (g * h) = G.lam g * G.lam h)
    (hlB : G.lam 1 = 1 ∧ (∀ g, G.lam g ≠ 0) ∧ ∀ g ∈ KC k n G.lev, G.lam g = 1)
    (hKC : ∀ r : ℕ, ((KCg k n r : Set (GL (Fin n) k)) = KC k n r) ∧
      (∀ g ∈ KO k (Fin n), ∀ u ∈ KC k n r, g * u * g⁻¹ ∈ KC k n r) ∧ IsOpen (KC k n r) ∧
        KC k n r ⊆ (KO k (Fin n) : Set _) ∧ (G.lev ≤ r → KC k n r ⊆ G.JSet))
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ) (hr : G.lev ≤ r) :
    Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) ∧
    ∀ v : V, (∀ u ∈ KC k n r, π u v = v) →
      G.PJ π r v ∈ G.Eig π ∧ (∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v) ∧
      (v ∈ G.Eig π → G.PJ π r v = (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) • v) := by
  obtain ⟨hKCeq, hKCn, hKCo, -, -⟩ := hKC r
  have hJ : ∀ {g : GL (Fin n) k}, g ∈ G.Jg → g ∈ G.JSet := fun hg => Jg_sub G h1 hmul hinv hg
  have hJK := Jg_le_KO G h1 hmul hinv
  have hKCmem : ∀ {u : GL (Fin n) k}, u ∈ KCg k n r → u ∈ KC k n r := fun hu => by
    rw [← hKCeq]; exact hu

  have hfin : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := by
    have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO
    have : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 hc
    have ho : IsOpen (((KCg k n r).subgroupOf (KO k (Fin n)) : Subgroup (KO k (Fin n))) : Set (KO k (Fin n))) := by
      have : IsOpen (KCg k n r : Set (GL (Fin n) k)) := by rw [hKCeq]; exact hKCo
      exact this.preimage continuous_subtype_val
    have : Finite (KO k (Fin n) ⧸ (KCg k n r).subgroupOf (KO k (Fin n))) := Subgroup.quotient_finite_of_isOpen _ ho
    have h0 : (KCg k n r).relIndex (KO k (Fin n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h0' : (KCg k n r).relIndex G.Jg ≠ 0 := fun h => h0 (Subgroup.relIndex_eq_zero_of_le_right hJK h)
    have : ((KCg k n r).subgroupOf G.Jg).FiniteIndex := ⟨h0'⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  refine ⟨hfin, fun v hv => ?_⟩
  let _ : Fintype (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := Fintype.ofFinite _
  have hN : ((KCg k n r).subgroupOf G.Jg).Normal := ⟨fun h hh g => by
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.subset_closure (hKCn _ (hJK g.2) _ (hKCmem hh))⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ↥G.Jg → V, ∀ x, f x = (G.lam x)⁻¹ • π x v := ⟨_, fun _ => rfl⟩
  have hlamH : ∀ h : ↥G.Jg, h ∈ (KCg k n r).subgroupOf G.Jg → G.lam h = 1 := fun h hh =>
    hlB.2.2 _ (KC_mono hr (hKCmem (Subgroup.mem_subgroupOf.1 hh)))
  have hπH : ∀ h : ↥G.Jg, h ∈ (KCg k n r).subgroupOf G.Jg → π h v = v := fun h hh =>
    hv _ (hKCmem (Subgroup.mem_subgroupOf.1 hh))
  have hf : ∀ x y : ↥G.Jg, (x : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) = y → f x = f y := by
    intro x y hxy
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ (KCg k n r).subgroupOf G.Jg, y = x * h :=
      ⟨x⁻¹ * y, QuotientGroup.eq.1 hxy, by group⟩
    rw [hfdef, hfdef, Subgroup.coe_mul, hlM _ (hJ x.2) _ (hJ h.2), hlamH h hh, mul_one, map_mul,
      Module.End.mul_apply, hπH h hh]
  have hPJ : ∀ w : V, G.PJ π r w = ∑ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
      (G.lam ((Quotient.out c : ↥G.Jg) : GL (Fin n) k))⁻¹ • π ((Quotient.out c : ↥G.Jg) : GL (Fin n) k) w :=
    fun w => finsum_eq_sum_of_fintype _
  have hPJv : G.PJ π r v = ∑ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg, f (Quotient.out c) := by
    rw [hPJ]; simp only [hfdef]
  have hA : ∀ g ∈ G.JSet, π g (G.PJ π r v) = G.lam g • G.PJ π r v := by
    intro g hg
    have hg0 := hlB.2.1 g
    have hterm : ∀ x : ↥G.Jg, π g (f x) = G.lam g • f (⟨g, Subgroup.subset_closure hg⟩ * x) := by
      intro x
      rw [hfdef, hfdef, Subgroup.coe_mul, Subgroup.coe_mk, hlM g hg _ (hJ x.2), map_smul, map_mul,
        Module.End.mul_apply, smul_smul]
      congr 1
      field_simp
    have hmv : ∀ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
        f (⟨g, Subgroup.subset_closure hg⟩ * Quotient.out c) =
          f (Quotient.out ((QuotientGroup.mk ⟨g, Subgroup.subset_closure hg⟩ : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) * c)) := by
      intro c
      apply hf
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']

    rw [hPJv, map_sum, Finset.smul_sum]
    simp_rw [hterm, hmv]
    exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk ⟨g, Subgroup.subset_closure hg⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)) _ _ (fun c => rfl)
  refine ⟨fun g hg => hA g hg, fun j hj => ?_, fun hEv => ?_⟩
  · have hjinv := hinv j hj
    have h1' : G.lam j⁻¹ * G.lam j = 1 := by rw [← hlM _ hjinv _ hj, inv_mul_cancel, hlB.1]
    have hterm : ∀ x : ↥G.Jg, (G.lam x)⁻¹ • π x (π j v) =
        π j (f ((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩)) := by
      intro x
      have hx := hJ x.2
      have e : (((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg) :
          GL (Fin n) k) = j⁻¹ * x * j := rfl
      have hl : G.lam (((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg) :
          GL (Fin n) k) = G.lam x := by
        rw [e, hlM _ (hmul _ hjinv _ hx) _ hj, hlM _ hjinv _ hx]
        linear_combination G.lam x * h1'
      rw [hfdef, hl, map_smul, e, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 3
      group
    have hmv : ∀ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
        f ((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * Quotient.out c * ⟨j, Subgroup.subset_closure hj⟩) =
          f (Quotient.out ((QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)⁻¹ * c *
            QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩)) := by
      intro c
      apply hf
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq']
    rw [hPJ (π j v)]
    simp_rw [hterm, hmv]

    rw [← map_sum, ← hA j hj, hPJv]
    congr 1
    exact Fintype.sum_equiv ((Equiv.mulLeft (QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)⁻¹).trans (Equiv.mulRight (QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg))) _ _ (fun c => rfl)
  · have hfv : ∀ x : ↥G.Jg, f x = v := fun x => by
      rw [hfdef, hEv _ (hJ x.2), smul_smul, inv_mul_cancel₀ (hlB.2.1 _), one_smul]
    rw [hPJv]
    simp_rw [hfv]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

end P_PJ

theorem step_PJ {n : ℕ} (G : Grp k n) : ParabolicJacquetProp G := by
  intro hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  exact P_PJ.core G hJone.1 (hJmul hcb hccB) (hJinv hcb hccB) (hlM hcb hΔU hΔM hccB) (hlB hccB) (hKC hccB)

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open ValuativeRel

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Uniformizer₂

lemma algebraMap_ne_zero {w : 𝒪[k]} (hw : w ≠ 0) : algebraMap 𝒪[k] k w ≠ 0 := by
  intro h
  apply hw
  exact Subtype.ext h

end Uniformizer₂

theorem step_unif : UniformizerProp (k := k) := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  exact ⟨Units.mk0 _ (Uniformizer₂.algebraMap_ne_zero hw.ne_zero), w, hw, rfl⟩

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_lamUnip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_eq_one_of_blockTri {ι β : Type} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (M : Matrix ι ι k) (b : ι → β) (hT : M.BlockTriangular b)
    (hD : ∀ i j, b i = b j → M i j = if i = j then 1 else 0) : M.det = 1 := by
  rw [hT.det]
  refine Finset.prod_eq_one fun c _ => ?_
  have h1 : M.toSquareBlock b c = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    change M i j = (1 : Matrix {a' // b a' = c} {a' // b a' = c} k) ⟨i, hi⟩ ⟨j, hj⟩
    rw [Matrix.one_apply, hD i j (hi.trans hj.symm)]
    simp [Subtype.ext_iff]
  rw [h1, det_one]

theorem delta_eq_one {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) {β : Type} [LinearOrder β]
    (b : Fin G.s → β)
    (hT : ∀ i j, b (G.bl j) < b (G.bl i) → (g : Matrix (Fin n) (Fin n) k) i j = 0)
    (hD : ∀ i j, b (G.bl i) = b (G.bl j) → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0)
    (a : Fin G.s) : G.Δ a g = 1 := by
  unfold Grp.Δ
  refine det_eq_one_of_blockTri _ (fun i : {i : Fin n // G.bl i ≤ a} => b (G.bl i.1)) ?_ ?_
  · intro i j h
    exact hT i.1 j.1 h
  · intro i j h
    change (g : Matrix (Fin n) (Fin n) k) i.1 j.1 = _
    rw [hD i.1 j.1 h]
    simp [Subtype.ext_iff]

theorem chk_one (μ : kˣ →* ℂˣ) : Grp.chk μ (1 : k) = 1 := by
  unfold Grp.chk
  rw [dite_eq_right one_ne_zero]
  have h : Units.mk0 (1 : k) one_ne_zero = 1 := Units.ext rfl
  rw [h, map_one, Units.val_one]

theorem lam_eq_one {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) {β : Type} [LinearOrder β]
    (b : Fin G.s → β)
    (hT : ∀ i j, b (G.bl j) < b (G.bl i) → (g : Matrix (Fin n) (Fin n) k) i j = 0)
    (hD : ∀ i j, b (G.bl i) = b (G.bl j) → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0) :
    G.lam g = 1 := by
  unfold Grp.lam
  refine Finset.prod_eq_one fun a _ => ?_
  rw [delta_eq_one G g b hT hD a, chk_one]

theorem diag_of_unipRad {n : ℕ} (G : Grp k n) (g : GL (Fin n) k) (hg : g ∈ unipRad k G.e) :
    ∀ i j, G.bl i = G.bl j → (g : Matrix (Fin n) (Fin n) k) i j = if i = j then 1 else 0 := by
  have hD := (mem_unipRad.1 hg).2
  intro i j h
  obtain ⟨⟨a, i'⟩, rfl⟩ := G.e.surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := G.e.surjective j
  have hab : a = b := by simpa [Grp.bl] using h
  subst hab
  rw [hD a i' j', Matrix.one_apply]
  by_cases hij : i' = j'
  · subst hij; simp
  · rw [if_neg hij, if_neg]
    intro he
    have := G.e.injective he
    simp at this
    exact hij this

end UpperTheory.TNZ.Grp.P_lamUnip

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_lamUnip {n : ℕ} (G : Grp k n) : G.LambdaUnipotentProp := by
  refine ⟨fun u hu => ?_, fun u hu _ => ?_⟩
  · obtain ⟨hN, hK⟩ := Subgroup.mem_inf.1 hu
    have hP := (mem_unipRad.1 hN).1
    have hT : ∀ i j, G.bl j < G.bl i → ((u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 :=
      fun i j h => mem_parab.1 hP i j h
    refine ⟨⟨hK, fun i j hij => ?_⟩, P_lamUnip.lam_eq_one G u (fun a => a) hT
      (P_lamUnip.diag_of_unipRad G u hN)⟩
    rw [hT i j hij]
    exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  · exact P_lamUnip.lam_eq_one G u (fun a => OrderDual.toDual a) (fun i j h => (hu i j).1 h)
      (fun i j h => (hu i j).2 h)

end UpperTheory.TNZ.Grp
end
end

section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace JacquetImage

variable {n : ℕ} (G : Grp k n)

theorem leviEmb_mem_PO (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) : leviEmb k G.e m ∈ G.PO :=
  ⟨leviEmb_mem_KO (k := k) G.e hm, leviEmb_mem_parab k G.e m⟩

theorem lam_leviEmb (hL : LeviSubgroupRestriction) (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) :
    G.lam (leviEmb k G.e m) = G.eta m := by
  have h := hL k n G ⟨leviEmb k G.e m, leviEmb_mem_parab k G.e m⟩ (leviEmb_mem_PO G m hm).1
  rw [leviProj_leviEmb] at h
  exact h

end JacquetImage

theorem step_jacImage {n : ℕ} (G : Grp k n) : JacquetImageProp G := by
  intro hL hJ V _ _ π x hx m hm
  show (Submodule.Quotient.mk (π (leviEmb k G.e m) x) : Jacquet π (unipRad k G.e)) = _
  rw [hx _ (hJ.2 (JacquetImage.leviEmb_mem_PO G m hm)), JacquetImage.lam_leviEmb G hL m hm,
    Submodule.Quotient.mk_smul]

end UpperTheory.TNZ.Grp
end
end
