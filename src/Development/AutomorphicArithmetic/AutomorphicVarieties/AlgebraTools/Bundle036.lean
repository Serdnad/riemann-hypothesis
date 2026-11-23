module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.Algebra.Field.ZMod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle035
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle026
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle032
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle034
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem count_step (l : ℕ) [hl : Fact l.Prime] (G : Type) [Group G] :
    ∀ (h : ℕ) (S : Subgroup (G →* Multiplicative (ZMod l))), Finite S → Nat.card S ≤ l ^ h →
      ∃ x : Fin h → G, ∀ f ∈ S, (∀ i, f (x i) = 1) → f = 1 := by
  intro h
  induction h with
  | zero =>
    intro S _ hS
    refine ⟨Fin.elim0, fun f hf _ => ?_⟩
    have hbot : S = ⊥ := Subgroup.eq_bot_of_card_le S (by simpa using hS)
    rw [hbot, Subgroup.mem_bot] at hf
    exact hf
  | succ h ih =>
    intro S hfin hS
    by_cases htriv : ∀ f ∈ S, f = 1
    · exact ⟨fun _ => 1, fun f hf _ => htriv f hf⟩
    push_neg at htriv
    obtain ⟨f₀, hf₀, hne⟩ := htriv
    obtain ⟨g, hg⟩ : ∃ g, f₀ g ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hne (MonoidHom.ext hc)
    let ev : S →* Multiplicative (ZMod l) :=
      { toFun := fun f => (f : G →* Multiplicative (ZMod l)) g
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hrange : Nat.card ev.range = l := by
      have hdvd : Nat.card ev.range ∣ l := by
        have := Subgroup.card_subgroup_dvd_card ev.range
        simpa [Nat.card_zmod] using this
      rcases (Nat.dvd_prime hl.out).mp hdvd with h1 | h1
      · exfalso
        have hbot : ev.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
        have hmem : ev ⟨f₀, hf₀⟩ ∈ ev.range := ⟨_, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hg hmem
      · exact h1
    have hcardS : Nat.card ev.ker * l = Nat.card S := by
      have := Subgroup.card_mul_index ev.ker
      rw [Subgroup.index_ker, hrange] at this
      exact this
    let S' : Subgroup (G →* Multiplicative (ZMod l)) := ev.ker.map S.subtype
    have hS' : Nat.card S' = Nat.card ev.ker := Subgroup.card_map_of_injective S.subtype_injective
    have hfin' : Finite S' := Nat.finite_of_card_ne_zero (by
      rw [hS']
      intro h0
      have : Nat.card S = 0 := by rw [← hcardS, h0, zero_mul]
      exact (Nat.card_pos (α := S)).ne' this)
    have hle : Nat.card S' ≤ l ^ h := by
      rw [hS']
      have hlpos : 0 < l := hl.out.pos
      have : Nat.card ev.ker * l ≤ l ^ h * l := by
        rw [hcardS, ← pow_succ]
        exact hS
      exact Nat.le_of_mul_le_mul_right this hlpos
    obtain ⟨x', hx'⟩ := ih S' hfin' hle
    refine ⟨Fin.cons g x', fun f hf hall => ?_⟩
    have hfg : f g = 1 := by simpa using hall 0
    have hmem : f ∈ S' := ⟨⟨f, hf⟩, hfg, rfl⟩
    exact hx' f hmem fun i => by simpa using hall i.succ

theorem UpperTheory.V.AlgebraTools.topGen_of_hom :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G], IsProL l G →
      (∀ s : Set G, (∀ f : G →* Multiplicative (ZMod l), IsOpen (f.ker : Set G) → (∀ g ∈ s, f g = 1) → f = 1) → TopGen s) ∧
      (∀ h : ℕ, {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.Finite →
        {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.ncard ≤ l ^ h → ∃ x : Fin h → G, TopGen (Set.range x)) := by
  intro l _ G _ _ _ _ _ hpro
  have partA : ∀ s : Set G, (∀ f : G →* Multiplicative (ZMod l), IsOpen (f.ker : Set G) →
      (∀ g ∈ s, f g = 1) → f = 1) → TopGen s := by
    intro s hs
    let H := (Subgroup.closure s).topologicalClosure
    have hHc : IsClosed (H : Set G) := Subgroup.isClosed_topologicalClosure _
    show Dense (Subgroup.closure s : Set G)
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro g
    by_contra hg
    have hg' : g ∉ (H : Set G) := by
      rw [Subgroup.topologicalClosure_coe]
      exact hg
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (U := (fun n => g * n) ⁻¹' (H : Set G)ᶜ)
      (hHc.isOpen_compl.preimage (continuous_const_mul g))
      (by simp only [Set.mem_preimage, Set.mem_compl_iff, mul_one]; exact hg')
    let Ns : Subgroup G := N.toOpenSubgroup
    haveI : Ns.Normal := N.isNormal'
    haveI : Finite (G ⧸ Ns) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
    let K := H.map (QuotientGroup.mk' Ns)
    have hK : K = ⊤ := by
      refine UpperTheory.V.CF.burnsideHom l (G ⧸ Ns) (hpro N) K (fun f hf => ?_)
      let F := f.comp (QuotientGroup.mk' Ns)
      have hFo : IsOpen (F.ker : Set G) := by
        refine Subgroup.isOpen_mono (H₁ := Ns) (fun x hx => ?_) N.isOpen'
        rw [MonoidHom.mem_ker]
        simp [F, (QuotientGroup.eq_one_iff x).mpr hx]
      have hF : F = 1 := hs F hFo (fun x hx => by
        have hxH : x ∈ H := Subgroup.le_topologicalClosure _ (Subgroup.subset_closure hx)
        exact hf ⟨x, hxH, rfl⟩)
      ext q
      simpa [F] using DFunLike.congr_fun hF q
    have hgK : (QuotientGroup.mk' Ns g) ∈ K := by
      rw [hK]
      exact Subgroup.mem_top _
    obtain ⟨y, hyH, hy⟩ := hgK
    have hyg : y⁻¹ * g ∈ Ns := QuotientGroup.eq.mp hy
    have hn : g⁻¹ * y ∈ Ns := by
      have := Ns.inv_mem hyg
      simpa using this
    have hU := hN hn
    simp only [Set.mem_preimage, Set.mem_compl_iff, mul_inv_cancel_left] at hU
    exact hU hyH
  refine ⟨partA, fun h hfin hcard => ?_⟩
  let S : Subgroup (G →* Multiplicative (ZMod l)) :=
    { carrier := {f | IsOpen (f.ker : Set G)}
      one_mem' := by
        show IsOpen ((1 : G →* Multiplicative (ZMod l)).ker : Set G)
        rw [MonoidHom.ker_one]
        exact isOpen_univ
      mul_mem' := fun {a b} ha hb => by
        show IsOpen ((a * b).ker : Set G)
        refine Subgroup.isOpen_mono (H₁ := a.ker ⊓ b.ker) (fun x hx => ?_) ?_
        · rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
          rw [MonoidHom.mem_ker, MonoidHom.mul_apply, hx.1, hx.2, one_mul]
        · rw [Subgroup.coe_inf]
          exact IsOpen.inter ha hb
      inv_mem' := fun {a} ha => by
        show IsOpen ((a⁻¹).ker : Set G)
        have : (a⁻¹).ker = a.ker := by
          ext x
          simp [MonoidHom.mem_ker]
        rw [this]
        exact ha }
  haveI : Finite S := hfin.to_subtype
  have hle : Nat.card S ≤ l ^ h := by
    have : Nat.card S = {f : G →* Multiplicative (ZMod l) | IsOpen (f.ker : Set G)}.ncard :=
      Nat.card_coe_set_eq _
    rw [this]
    exact hcard
  obtain ⟨x, hx⟩ := count_step l G h S inferInstance hle
  exact ⟨x, partA _ fun f hf hv => hx f hf fun i => hv _ ⟨i, rfl⟩⟩
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

private theorem exists_algHom_of_comm {σ A H : Type} [CommRing A] [Ring H] [Algebra A H] (y : σ → H)
    (hy : ∀ i j, y i * y j = y j * y i) :
    ∃ th : MvPolynomial σ A →ₐ[A] H, ∀ i, th (MvPolynomial.X i) = y i := by
  have hc : ∀ a ∈ Set.range y, ∀ b ∈ Set.range y, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hy i j
  have : IsMulCommutative (Algebra.adjoin A (Set.range y)) :=
    Algebra.isMulCommutative_adjoin A (fun a ha b hb _ => hc a ha b hb)
  letI : CommRing (Algebra.adjoin A (Set.range y)) :=
    { (inferInstance : Ring (Algebra.adjoin A (Set.range y))) with mul_comm := fun a b => this.is_comm.comm a b }
  refine ⟨(Algebra.adjoin A (Set.range y)).val.comp
    (MvPolynomial.aeval fun i => ⟨y i, Algebra.subset_adjoin ⟨i, rfl⟩⟩), fun i => ?_⟩
  simp

private theorem anti_fund' (n m : ℕ) : Antitone (fund n m) := by
  intro i j hij
  have : (i : ℕ) ≤ j := hij
  simp only [fund]
  split_ifs <;> omega

private theorem dom_pw' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {x : kˣ} (hx : IsUnif x) {c : Fin n → ℤ} (hc : Antitone c) : Dom fun i => x ^ c i := by
  obtain ⟨p, -, hp⟩ := hx
  intro i j hij
  have h1 : valuation k (x : k) ≤ 1 := by rw [← hp]; exact p.2
  have h0 : 0 < valuation k (x : k) := by simp [zero_lt_iff]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_zpow_right_of_le_one₀ h0 h1 (hc hij)

private theorem single_mul_fund {G : Type} [CommGroup G] {n : ℕ} (x : G) (i : Fin n) :
    (Pi.mulSingle i x * fun l => x ^ fund n i l : Fin n → G) = fun l => x ^ fund n ((i : ℕ) + 1) l := by
  ext l
  by_cases h : l = i
  · subst h
    simp [fund]
  · have h' : (l : ℕ) ≠ i := fun e => h (Fin.ext e)
    have : fund n ((i : ℕ) + 1) l = fund n i l := by
      simp only [fund]
      split_ifs <;> omega
    simp [Pi.mulSingle_eq_of_ne h, this]

private theorem abs_bern {n : ℕ} {A E G : Type} [CommRing A] [Ring E] [Algebra A E] [CommGroup G] (S : Subalgebra A E)
    (q : A) (hq : IsUnit q) (T : Equiv.Perm (Fin n) → S) (D : ℕ → S) (θ : G →* Eˣ) (s : Fin n → G) (d : ℕ → G)
    (hsd : ∀ i : Fin n, s i * d i = d ((i : ℕ) + 1)) (hval : ∀ m, (D m : E) = θ (d m)) (hD : ∀ m, IsUnit (D m))
    (h1 : (T 1 : E) = 1)
    (hmul : ∀ a b : Fin n, a.val + 1 = b.val → ∀ w : Equiv.Perm (Fin n), w⁻¹ a < w⁻¹ b →
      (T (Equiv.swap a b) : E) * T w = T (Equiv.swap a b * w))
    (hsq : ∀ a b : Fin n, a.val + 1 = b.val →
      (T (Equiv.swap a b) : E) * T (Equiv.swap a b) = (q - 1) • (T (Equiv.swap a b) : E) + q • 1)
    (hb : ∀ a b : Fin n, a.val + 1 = b.val →
      (θ (s a) : E) = T (Equiv.swap a b) * (θ (s b) : E) * T (Equiv.swap a b) ∧
        ∀ l : Fin n, l ≠ a → l ≠ b → Commute (T (Equiv.swap a b) : E) (θ (s l) : E)) :
    ∃ b : Hk.Bern n q S, (∀ w, b.T w = T w) ∧
      ∀ i : Fin n, b.th (MvPolynomial.X i) * D i = (q ^ (i : ℕ)) • D ((i : ℕ) + 1) := by
  have hy : ∀ i : Fin n, ∃ y : S, (y : E) = θ (s i) := by
    intro i
    obtain ⟨u, hu⟩ := hD i
    refine ⟨D ((i : ℕ) + 1) * (u⁻¹ : Sˣ), ?_⟩
    apply (θ (d i)).isUnit.mul_right_cancel
    rw [← Units.val_mul, ← map_mul, hsd, ← hval, ← hval, ← hu, ← MulMemClass.coe_mul, mul_assoc,
      Units.inv_mul, mul_one]
  choose y hy using hy
  obtain ⟨th, hth⟩ := exists_algHom_of_comm (A := A) (fun i : Fin n => (q ^ (i : ℕ)) • y i) (by
    intro i j
    have : y i * y j = y j * y i := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hy, hy, ← Units.val_mul, ← map_mul, mul_comm, map_mul, Units.val_mul]
    simp only [smul_mul_assoc, mul_smul_comm, this]
    rw [smul_comm])
  have hsq' : ∀ a b : Fin n, a.val + 1 = b.val →
      T (Equiv.swap a b) * T (Equiv.swap a b) = (q - 1) • T (Equiv.swap a b) + q • 1 := fun a b hab =>
    Subtype.ext (hsq a b hab)
  have hrel : ∀ a b : Fin n, a.val + 1 = b.val →
      T (Equiv.swap a b) * th (MvPolynomial.X b) * T (Equiv.swap a b) = q • th (MvPolynomial.X a) := by
    intro a b hab
    have h : T (Equiv.swap a b) * y b * T (Equiv.swap a b) = y a := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hy, hy]
      exact (hb a b hab).1.symm
    rw [hth, hth, mul_smul_comm, smul_mul_assoc, h, smul_smul, ← hab, pow_succ']
  refine ⟨{ th := th
            T := T
            T_one := Subtype.ext h1
            T_mul := fun a b hab w hw => Subtype.ext (hmul a b hab w hw).symm
            T_sq := hsq'
            comm := fun a b hab j ha hb' => ?_
            relA := fun a b hab => (Hk.Bern.rel_of_quad hq _ _ _ (hsq' a b hab) (hrel a b hab)).1
            relB := fun a b hab => (Hk.Bern.rel_of_quad hq _ _ _ (hsq' a b hab) (hrel a b hab)).2 },
    fun w => rfl, fun i => ?_⟩
  · have h : T (Equiv.swap a b) * y j = y j * T (Equiv.swap a b) := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hy]
      exact ((hb a b hab).2 j ha hb').eq
    rw [hth, mul_smul_comm, smul_mul_assoc, h]
  · change th _ * _ = _
    rw [hth, smul_mul_assoc]
    congr 1
    apply Subtype.ext
    rw [MulMemClass.coe_mul, hy, hval, hval, ← Units.val_mul, ← map_mul, hsd]

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.bernHk :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : Type) [CommRing A] (x : kˣ), IsUnif x → IsUnit (resCard k : A) → ∃ b : UpperTheory.V.AlgebraTools.Hk.Bern n (resCard k : A) (HkAlg A (iwC k n ⊤)), (∀ w, b.T w = hT A (iwC k n ⊤) (pm k n w)) ∧ ∀ i : Fin n, b.th (MvPolynomial.X i) * hT A (iwC k n ⊤) (pw x (fund n i)) = ((resCard k : A) ^ (i : ℕ)) • hT A (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1))) := by
  intro k _ _ _ _ n A _ x hx hq
  refine (thetaEx k n ⊤ A _ (permRep A (iwC k n ⊤)) hq).exists.elim fun θ hθ => ?_
  have hd : ∀ m, Dom fun i : Fin n => x ^ fund n m i := fun m => dom_pw' hx (anti_fund' n m)
  have h1 : hk (permRep A (iwC k n ⊤)) (iwC k n ⊤) (pm k n 1) = 1 := by
    rw [map_one]
    exact (hkNorm A _ _ (permRep A (iwC k n ⊤)) _ 1 (heckePairIwC k n ⊤).1 (one_mem _)).2.1
  have h := abs_bern (HkAlg A (iwC k n ⊤)) (resCard k : A) hq (fun w => hT A (iwC k n ⊤) (pm k n w))
    (fun m => hT A (iwC k n ⊤) (pw x (fund n m))) θ (fun i => Pi.mulSingle i x) (fun m i => x ^ fund n m i)
    (single_mul_fund x) (fun m => (hθ _ (hd m)).symm) (fun m => (unitHk k n A hq).2 _ (hd m)) h1
    (fun a b hab w hw => permMul k n ⊤ A _ (permRep A (iwC k n ⊤)) w a b hab.symm hw)
    (fun a b hab => (simpleQuad k n ⊤ A _ (permRep A (iwC k n ⊤)) a b hab.symm).2 rfl)
    (fun a b hab => bernRel k n A _ (permRep A (iwC k n ⊤)) x hx hq θ hθ a b hab.symm)
  exact h
end
