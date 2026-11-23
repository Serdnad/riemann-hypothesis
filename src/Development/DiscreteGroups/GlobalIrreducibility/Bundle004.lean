module

public import Development.DiscreteGroups.GlobalIrreducibility.Bundle001
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle003
import Development.DiscreteGroups.GlobalIrreducibility.Bundle002
public import GroundTheory.AutomorphicForms.SmoothRep
public import Mathlib.RepresentationTheory.Irreducible
public import GroundTheory.AutomorphicForms.HeckeIrreducible
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.BurnsideSurjectivity.Burnside

@[expose] public section

section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) {c : kˣ} (hc : HasConductor ψ c)

include hc in
theorem exists_avg_notMem (W : Submodule ℂ V) {s t : kˣ} {x : V} (hx : ∀ h ∈ ball s, σ h x = x)
    (hxW : x ∉ W) : ∃ ξ ∈ ball (c * s⁻¹), avg ψ σ s t ξ x ∉ W := by
  by_contra hall
  push Not at hall
  apply hxW
  have hsum := sum_avg ψ σ (c := c) hc (t := t) hx
  have hm : ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x ∈ W := by
    rw [← hsum]
    exact W.sum_mem fun f _ => hall _ (out_mem f)
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm

include hc in
theorem avg_shift {s t : kˣ} {ξ h : k} (hh : h ∈ ball (c * t⁻¹)) : avg ψ σ s t (ξ + h) = avg ψ σ s t ξ := by
  simp only [avg]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh (out_mem q), Circle.coe_one, mul_one]

include hc in
theorem isClosed_notMem (W : Submodule ℂ V) (s t : kˣ) (x : V) :
    IsClosed {ξ : k | avg ψ σ s t ξ x ∉ W} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro ξ hξ
  have hU : (fun η => η - ξ) ⁻¹' ((ball (c * t⁻¹) : AddSubgroup k) : Set k) ∈ nhds ξ :=
    ((isOpen_ball _).preimage (continuous_sub_right ξ)).mem_nhds (by simp [(ball _).zero_mem])
  refine Filter.mem_of_superset hU fun η hη => ?_
  have : η = ξ + (η - ξ) := by ring
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hξ ⊢
  rw [this, avg_shift ψ σ hc hη]
  exact hξ

variable (hadd : ∀ a b, σ (a + b) = σ a * σ b)

include hadd in
theorem key_step (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) {s : kˣ} {x : V} (hs : ∀ h ∈ ball s, σ h x = x) {ξ : k}
    (hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    (hx : x ∈ W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y}) :
    ∃ t' : kˣ, valuation k (s : k) ≤ valuation k (t' : k) ∧ avg ψ σ s t' ξ x ∈ W := by
  let P : V → Prop := fun z => ∃ s' t' : kˣ, valuation k (s' : k) ≤ valuation k (s : k) ∧
    valuation k (s : k) ≤ valuation k (t' : k) ∧ ∀ s'' t'' : kˣ, valuation k (s'' : k) ≤ valuation k (s' : k) →
      valuation k (t' : k) ≤ valuation k (t'' : k) → avg ψ σ s'' t'' ξ z ∈ W
  have Padd : ∀ z1 z2, P z1 → P z2 → P (z1 + z2) := by
    rintro z1 z2 ⟨s1, t1, hs1, ht1, h1⟩ ⟨s2, t2, hs2, ht2, h2⟩
    obtain ⟨s', a1, a2⟩ := exists_min s1 s2
    obtain ⟨t', b1, b2⟩ := exists_max t1 t2
    refine ⟨s', t', a1.trans hs1, ht1.trans b1, fun s'' t'' h1' h2' => ?_⟩
    rw [map_add (f := _)]
    exact W.add_mem (h1 _ _ (h1'.trans a1) (b1.trans h2')) (h2 _ _ (h1'.trans a2) (b2.trans h2'))
  have PW : ∀ w ∈ W, P w := fun w hw => ⟨s, s, le_rfl, le_rfl, fun _ _ _ _ => avg_mem ψ σ W hW _ _ _ hw⟩
  have Pspan : ∀ z ∈ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y},
      P z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, y, rfl⟩ := hz
      obtain ⟨sy, hsy⟩ := hsm y
      obtain ⟨ta, hta⟩ := exists_ball_mem a
      obtain ⟨s', a1, a2⟩ := exists_min s sy
      obtain ⟨t', b1, b2⟩ := exists_max s ta
      refine ⟨s', t', a1, b1, fun s'' t'' h1 h2 => ?_⟩
      have hy'' : ∀ h ∈ ball s'', σ h y = y := fun h hh => hsy h (ball_mono (h1.trans a2) hh)
      have hξ'' : ∀ h ∈ ball s'', ψ (ξ * h) = 1 := fun h hh => hξs h (ball_mono (h1.trans a1) hh)
      have ha : a ∈ ball t'' := ball_mono (b2.trans h2) hta
      rw [map_sub, map_smul, ← Module.End.mul_apply, avg_comm ψ σ hadd, Module.End.mul_apply,
        avg_eigen ψ σ hadd hξ'' hy'' ha, sub_self]
      exact W.zero_mem
    | zero => exact PW 0 W.zero_mem
    | add z1 z2 _ _ h1 h2 => exact Padd z1 z2 h1 h2
    | smul r z _ h =>
      obtain ⟨s', t', a1, b1, hz⟩ := h
      exact ⟨s', t', a1, b1, fun s'' t'' h1 h2 => by rw [map_smul]; exact W.smul_mem r (hz _ _ h1 h2)⟩
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s', t', hs', ht', h⟩ := Padd w y (PW w hw) (Pspan y hy)
  refine ⟨t', ht', ?_⟩
  have h1 := h s' t' le_rfl le_rfl
  have e := avg_level ψ σ hadd (t := t') hs' hξs hs
  have hm : ((Fintype.card (Q s' t') : ℕ) : ℂ) • avg ψ σ s t' ξ (w + y) ∈ W := by
    rw [← e]; exact W.smul_mem _ h1
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm


include hc hadd in
theorem exists_character_sup_ne_top (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) (hne : W ≠ ⊤) :
    ∃ ξ : k, W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y} ≠ ⊤ := by
  obtain ⟨x, hxW⟩ : ∃ x, x ∉ W := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨s, hs⟩ := hsm x
  let ι := {t : kˣ // valuation k (s : k) ≤ valuation k (t : k)}
  haveI : Nonempty ι := ⟨⟨s, le_rfl⟩⟩
  let C : ι → Set k := fun t => ((ball (c * s⁻¹) : AddSubgroup k) : Set k) ∩ {ξ | avg ψ σ s t.1 ξ x ∉ W}
  have hdir : Directed (· ⊇ ·) C := by
    intro t1 t2
    rcases le_total (valuation k (t1.1 : k)) (valuation k (t2.1 : k)) with h | h
    · exact ⟨t2, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩,
        le_rfl⟩
    · exact ⟨t1, le_rfl, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩⟩
  have hnon : ∀ t, (C t).Nonempty := fun t => by
    obtain ⟨ξ, h1, h2⟩ := exists_avg_notMem ψ σ hc W (t := t.1) hs hxW
    exact ⟨ξ, h1, h2⟩
  have hcl : ∀ t, IsClosed (C t) := fun t =>
    ((ball _).isClosed_of_isOpen (isOpen_ball _)).inter (isClosed_notMem ψ σ hc W s t.1 x)
  have hcpt : ∀ t, IsCompact (C t) := fun t => (isCompact_cball _).inter_right (isClosed_notMem ψ σ hc W s t.1 x)
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hnon hcpt hcl
  rw [Set.mem_iInter] at hξ
  have hξs := psi_triv hc (hξ ⟨s, le_rfl⟩).1
  refine ⟨ξ, fun htop => ?_⟩
  obtain ⟨t', ht', hm⟩ := key_step ψ σ hadd W hW hsm hs hξs (x := x) (by rw [htop]; exact Submodule.mem_top)
  exact (hξ ⟨t', ht'⟩).2 hm

end DiscreteGroups.sglob.LConvGenF
end
end

section

noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

include hρ hKc hKo

theorem fixedProj_eq_avg {L : Subgroup G} (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) :
    ∃ (N : ℕ) (r : Fin N → G), 0 < N ∧ (∀ i, r i ∈ K) ∧
      ∀ v : V, v ∈ fixedVectors ρ L →
        (fixedProj ρ hρ hKc hKo v : V) = (N : ℂ)⁻¹ • ∑ i, ρ (r i) v := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hHo : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) := hLo.preimage continuous_subtype_val
  have : Finite (K ⧸ L.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hHo
  let _ : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  have hNpos : 0 < Fintype.card (K ⧸ L.subgroupOf K) :=
    Fintype.card_pos_iff.mpr ⟨QuotientGroup.mk (1 : K)⟩
  let eQ := Fintype.equivFin (K ⧸ L.subgroupOf K)
  refine ⟨Fintype.card (K ⧸ L.subgroupOf K), fun i => ((Quotient.out (eQ.symm i) : K) : G), hNpos,
    fun i => (Quotient.out (eQ.symm i)).2, ?_⟩
  intro v hv
  obtain ⟨s, hs⟩ : ∃ s : V, s = ∑ q : K ⧸ L.subgroupOf K, ρ ((Quotient.out q : K) : G) v := ⟨_, rfl⟩
  have hreidx : ∑ i, ρ ((Quotient.out (eQ.symm i) : K) : G) v = s := by
    rw [hs]
    exact Fintype.sum_equiv eQ.symm _ _ (fun _ => rfl)
  have hsK : s ∈ fixedVectors ρ K := by
    intro k hk
    have key : ∀ q : K ⧸ L.subgroupOf K, ρ k (ρ ((Quotient.out q : K) : G) v) =
        ρ ((Quotient.out ((⟨k, hk⟩ : K) • q) : K) : G) v := by
      intro q
      rw [← Module.End.mul_apply, ← map_mul]
      have h1 : (((⟨k, hk⟩ : K) * Quotient.out q : K) : G) = k * ((Quotient.out q : K) : G) := rfl
      rw [← h1]
      apply act_eq_of_mk_eq ρ hv
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]

    rw [hs, map_sum, Finset.sum_congr rfl (fun q _ => key q)]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun _ => rfl)
  have hsub : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v ∈ coinvariantsKer ρ K := by
    have h1 : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v =
        ∑ q : K ⧸ L.subgroupOf K, (ρ ((Quotient.out q : K) : G) v - v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, hs]
    rw [h1]
    exact Submodule.sum_mem _ fun q _ => sub_mem_coinvariantsKer (Quotient.out q).2 v
  have h1 : (fixedProj ρ hρ hKc hKo s : V) = s := fixedProj_apply_of_mem hρ hKc hKo hsK
  have h2 := fixedProj_apply_of_mem_coinvariantsKer hρ hKc hKo hsub
  rw [map_sub, map_smul, sub_eq_zero] at h2
  have h3 : ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • (fixedProj ρ hρ hKc hKo v : V) = s := by
    rw [← h1, h2, Submodule.coe_smul]
  rw [hreidx, ← h3, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hNpos.ne'), one_smul]

theorem map_fixedProj_of_invariant {U : Type*} [AddCommGroup U] [Module ℂ U] (f : V →ₗ[ℂ] U)
    (v : V) (hf : ∀ k ∈ K, f (ρ k v) = f v) : f (fixedProj ρ hρ hKc hKo v : V) = f v := by
  have hLo : IsOpen ((K ⊓ stabilizerOf ρ v : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter (hρ v)
  obtain ⟨N, r, hN, hr, h⟩ := fixedProj_eq_avg hρ hKc hKo (L := K ⊓ stabilizerOf ρ v) inf_le_left hLo

  rw [h v (fun l hl => hl.2), map_smul, map_sum, Finset.sum_congr rfl (fun i _ => hf (r i) (hr i)),
  Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
  inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]


variable (ρ) in
def hop (g : G) : Module.End ℂ (fixedVectors ρ K) :=
  (fixedProj ρ hρ hKc hKo) ∘ₗ (ρ g) ∘ₗ (fixedVectors ρ K).subtype

theorem hop_apply (g : G) (w : fixedVectors ρ K) :
    hop ρ hρ hKc hKo g w = fixedProj ρ hρ hKc hKo (ρ g w) := rfl

theorem hop_of_mem {κ : G} (hκ : κ ∈ K) : hop ρ hρ hKc hKo κ = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [hop_apply, fixedProj_apply_act hρ hKc hKo hκ, Module.End.one_apply,
    fixedProj_apply_of_mem hρ hKc hKo w.2]

theorem hop_one : hop ρ hρ hKc hKo 1 = 1 := hop_of_mem hρ hKc hKo K.one_mem

theorem hop_mul {g h : G}
    (H : ∀ w ∈ fixedVectors ρ K, ∀ κ ∈ K,
      fixedProj ρ hρ hKc hKo (ρ (g * κ * h) w) = fixedProj ρ hρ hKc hKo (ρ (g * h) w)) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h = hop ρ hρ hKc hKo (g * h) := by
  refine LinearMap.ext fun w => ?_
  show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) =
    fixedProj ρ hρ hKc hKo (ρ (g * h) w)
  have key := map_fixedProj_of_invariant hρ hKc hKo ((fixedProj ρ hρ hKc hKo) ∘ₗ ρ g) (ρ h w)
    (fun κ hκ => by
      simp only [LinearMap.comp_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, H w w.2 κ hκ,
        map_mul, Module.End.mul_apply])
  simp only [LinearMap.comp_apply] at key
  rw [key, map_mul, Module.End.mul_apply]

theorem hop_mul_mem_span (g h : G) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  let L : Subgroup G := K ⊓ K.comap (MulAut.conj h⁻¹).toMonoidHom
  have hLo : IsOpen (L : Set G) := by
    have hc : Continuous fun x : G => h⁻¹ * x * h⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hKo.inter (hKo.preimage hc)
  obtain ⟨N, r, hN, -, hav⟩ := fixedProj_eq_avg hρ hKc hKo (L := L) inf_le_left hLo
  have hfix : ∀ w : fixedVectors ρ K, ρ h (w : V) ∈ fixedVectors ρ L := by
    intro w l hl
    have hl2 : h⁻¹ * l * h ∈ K := by
      have := hl.2
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
    calc ρ l (ρ h w) = ρ h (ρ (h⁻¹ * l * h) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]; congr 2; group
      _ = ρ h w := by rw [w.2 _ hl2]
  have heq : hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h =
      (N : ℂ)⁻¹ • ∑ i, hop ρ hρ hKc hKo (g * r i * h) := by
    refine LinearMap.ext fun w => ?_
    show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) = _

    rw [hav _ (hfix w), map_smul, map_smul, map_sum, map_sum, LinearMap.smul_apply,
    LinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = fixedProj ρ hρ hKc hKo (ρ (g * r i * h) w)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩)

theorem span_hop_mul_mem {a b : Module.End ℂ (fixedVectors ρ K)}
    (ha : a ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)))
    (hb : b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo))) :
    a * b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      exact hop_mul_mem_span hρ hKc hKo g h
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem span_hop_eq_top [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    [Nontrivial (fixedVectors ρ K)] :
    Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) = ⊤ := by
  have hone : (1 : Module.End ℂ (fixedVectors ρ K)) ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
    rw [← hop_one hρ hKc hKo]; exact Submodule.subset_span ⟨1, rfl⟩
  let A : Subalgebra ℂ (Module.End ℂ (fixedVectors ρ K)) :=
    Submodule.toSubalgebra _ hone (fun a b ha hb => span_hop_mul_mem hρ hKc hKo ha hb)
  have hirr : ∀ U : Submodule ℂ (fixedVectors ρ K),
      (∀ a : A, ∀ w ∈ U, A.val a w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hT : ∀ g, hop ρ hρ hKc hKo g u ∈ U := fun g =>
      hU ⟨hop ρ hρ hKc hKo g, Submodule.subset_span ⟨g, rfl⟩⟩ u huU
    rw [eq_top_iff]
    intro w _
    have hu0' : (u : V) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have hw := HeckeAlgebra.mem_span_orbit (ρ := ρ) hu0' (w : V)
    have hww : w = fixedProj ρ hρ hKc hKo (w : V) :=
      Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo w.2).symm
    rw [hww]
    have hle : Submodule.map (fixedProj ρ hρ hKc hKo)
        (Submodule.span ℂ (Set.range fun g => ρ g (u : V))) ≤ U := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hT g
    exact hle ⟨_, hw, rfl⟩
  have hsurj := ReciprocityTheory.GC.burnside_surj_of_irred (k := ℂ) A.val hirr
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := hsurj x
  rw [← ha]
  exact a.2

end DiscreteGroups.sglob.LConvU
end
end
