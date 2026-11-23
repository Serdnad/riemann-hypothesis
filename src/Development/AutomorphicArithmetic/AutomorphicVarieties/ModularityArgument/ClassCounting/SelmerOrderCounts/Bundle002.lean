module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem selInj_delI_inj {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I)
    (v : I) (hv : D.delI v = 0) : v = 0 := by
  have h1 : D.gI v = (D.a : ℤ) • v := by
    have h := hv
    simp only [Dat.delI, LinearMap.sub_apply, sub_eq_zero] at h
    rw [h]
    simp
  have hp : ∀ k : ℕ, (D.gI ^ k) v = ((D.a : ℤ) ^ k) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_zsmul, ih, smul_smul, pow_succ, mul_comm]
  have hn := hp D.n
  rw [D.gI_pow] at hn
  change v = _ at hn
  apply D.tf ((D.a : ℤ) ^ D.n - 1) v
  · have h2 : (1 : ℤ) < (D.a : ℤ) ^ D.n := one_lt_pow₀ (by have := D.two_le; omega) D.n_pos.ne'
    omega
  · rw [sub_smul, one_smul, ← hn, sub_self]

private theorem selInj_tors_iff {Y : Type} [AddCommGroup Y] (t : Y) :
    t ∈ Submodule.torsion ℤ Y ↔ ∃ m : ℤ, m ≠ 0 ∧ m • t = 0 := by
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨m, hm⟩, h⟩
    exact ⟨m, nonZeroDivisors.ne_zero hm, h⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, h⟩

private theorem selInj_mem_mt {Y : Type} [AddCommGroup Y] (l : ℕ) (x : Y) :
    x ∈ mt Y l ↔ ∃ z : Y, ∃ t ∈ Submodule.torsion ℤ Y, (l : ℤ) • z + t = x := by
  simp only [Ct.mt, Submodule.mem_sup, LinearMap.mem_range]
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, t, ht, h⟩
    exact ⟨z, t, ht, by simpa using h⟩
  · rintro ⟨z, t, ht, h⟩
    exact ⟨_, ⟨z, rfl⟩, t, ht, by simpa using h⟩

theorem UpperTheory.V.ZK.Ct.selInj :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), ∀ l : ℕ, (l : ℤ) ∣ (D.a : ℤ) - 1 → 0 < l → Finite (D.SelInv l) → Nat.card {w : D.W // (l : ℤ) • w = 0} ≤ Nat.card (D.SelInv l) := by
  intro Y I _ _ D l hl hl0 hfin
  have hdel_apply : ∀ y, D.del y = D.g y - (D.a : ℤ) • y := by
    intro y
    simp [Dat.del]
  have hdelI_apply : ∀ v, D.delI v = D.gI v - (D.a : ℤ) • v := by
    intro v
    simp [Dat.delI]
  have htor : ∀ {y : Y} (m : ℤ), m ≠ 0 → m • y ∈ Submodule.torsion ℤ Y → y ∈ Submodule.torsion ℤ Y := by
    intro y m hm h
    obtain ⟨m', hm', h'⟩ := (selInj_tors_iff _).1 h
    exact (selInj_tors_iff y).2 ⟨m' * m, mul_ne_zero hm' hm, by rw [mul_smul, h']⟩
  have hdt : ∀ t ∈ Submodule.torsion ℤ Y, D.d t = 0 := by
    intro t ht
    obtain ⟨m, hm, h⟩ := (selInj_tors_iff t).1 ht
    exact D.tf m _ hm (by rw [← map_zsmul, h, map_zero])
  have hdd : ∀ y, D.d (D.del y) = D.delI (D.d y) := by
    intro y
    rw [hdel_apply, hdelI_apply, map_sub, map_zsmul, D.comm]
  have hdelt : ∀ t ∈ Submodule.torsion ℤ Y, D.del t ∈ Submodule.torsion ℤ Y := by
    intro t ht
    obtain ⟨m, hm, h⟩ := (selInj_tors_iff t).1 ht
    exact (selInj_tors_iff _).2 ⟨m, hm, by rw [← map_zsmul, h, map_zero]⟩
  have key : ∀ w : {w : D.W // (l : ℤ) • w = 0}, ∃ u : D.U, Submodule.Quotient.mk u = w.1 ∧
      ∃ y : Y, ∃ t ∈ Submodule.torsion ℤ Y, (l : ℤ) • (u : Y) = D.del y + t := by
    rintro ⟨w, hw⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    refine ⟨u, rfl, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hw
    have hw' : (l : ℤ) • (u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y := hw
    obtain ⟨a', ⟨y, rfl⟩, t, ht, h⟩ := Submodule.mem_sup.1 hw'
    exact ⟨y, t, ht, h.symm⟩
  choose u hu y t ht hyt using key
  have hsel : ∀ w, (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) ∈ D.SelInv l := by
    intro w
    obtain ⟨c, hc⟩ := hl
    refine ⟨y w, rfl, ?_, ?_⟩
    · rw [selInj_mem_mt]
      refine ⟨(u w : Y) + c • y w, -t w, neg_mem (ht w), ?_⟩
      rw [smul_add, hyt w, hdel_apply, smul_smul, ← hc, sub_smul, one_smul]
      abel
    · obtain ⟨i, hi⟩ := (u w).2
      refine ⟨i, ?_⟩
      have e := congrArg D.d (hyt w)
      rw [map_zsmul, map_add (f := _), hdt _ (ht w), add_zero, hdd, ← hi] at e
      rw [← sub_eq_zero]
      apply selInj_delI_inj D
      rw [map_sub, map_zsmul, ← e, sub_self]
  let f : {w : D.W // (l : ℤ) • w = 0} → D.SelInv l := fun w => ⟨_, hsel w⟩
  apply Nat.card_le_card_of_injective f
  intro w w' hww
  have hq : (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) = Submodule.Quotient.mk (y w') :=
    congrArg Subtype.val hww
  rw [Submodule.Quotient.eq, selInj_mem_mt] at hq
  obtain ⟨z, t0, ht0, hz⟩ := hq
  apply Subtype.ext
  rw [← hu w, ← hu w', Submodule.Quotient.eq]
  show ((u w : Y) - (u w' : Y)) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y
  have e2 : D.del (y w) - D.del (y w') = (l : ℤ) • D.del z + D.del t0 := by
    rw [← map_sub, ← hz, map_add (f := _), map_zsmul]
  have hs : (u w : Y) - u w' - D.del z ∈ Submodule.torsion ℤ Y := by
    refine htor (l : ℤ) (by exact_mod_cast hl0.ne') ?_
    have e : (l : ℤ) • ((u w : Y) - u w' - D.del z) = D.del t0 + (t w - t w') := by
      rw [smul_sub, smul_sub, hyt w, hyt w',
        show D.del (y w) = (l : ℤ) • D.del z + D.del t0 + D.del (y w') by rw [← e2]; abel]
      abel
    rw [e]
    exact add_mem (hdelt t0 ht0) (sub_mem (ht w) (ht w'))
  rw [show (u w : Y) - u w' = D.del z + ((u w : Y) - u w' - D.del z) by abel]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) hs
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

section SlopeTestRemainingChoices

variable {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I)

private theorem delI_inj : Function.Injective D.delI := by
  refine (injective_iff_map_eq_zero D.delI).2 fun z hz => ?_
  have hg : D.gI z = D.a • z := by
    simp [Dat.delI, sub_eq_zero] at hz
    exact hz
  have hk : ∀ k : ℕ, (D.gI ^ k) z = (D.a ^ k) • z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_nsmul, hg, smul_smul, ← pow_succ]
  have h1 := hk D.n
  rw [D.gI_pow, Module.End.one_apply] at h1
  have ha : (2 : ℤ) ≤ D.a := by exact_mod_cast D.two_le
  have hp : (2 : ℤ) ^ 1 ≤ (D.a : ℤ) ^ D.n :=
    le_trans (pow_le_pow_right₀ (by norm_num) D.n_pos) (pow_le_pow_left₀ (by norm_num) ha _)
  have hne : (D.a : ℤ) ^ D.n - 1 ≠ 0 := by
    norm_num at hp
    omega
  have hc : ((D.a : ℤ) ^ D.n) • z = (D.a ^ D.n) • z := by
    rw [← Nat.cast_pow, natCast_zsmul]
  refine D.tf _ z hne ?_
  rw [sub_smul, one_smul, hc, ← h1, sub_self]

private theorem d_del (y : Y) : D.d (D.del y) = D.delI (D.d y) := by
  simp [Dat.del, Dat.delI, D.comm]

private theorem d_tors {t : Y} (ht : t ∈ Submodule.torsion ℤ Y) : D.d t = 0 := by
  obtain ⟨m, hm⟩ := (Submodule.mem_torsion_iff t).1 ht
  have hm' : (m : ℤ) • t = 0 := hm
  refine D.tf m _ (nonZeroDivisors.coe_ne_zero m) ?_
  rw [← map_zsmul, hm', map_zero]

private theorem card_ker_eq_coker {C : Type} [AddCommGroup C] [Finite C] (f : C →ₗ[ℤ] C) :
    Nat.card (LinearMap.ker f) = Nat.card (C ⧸ LinearMap.range f) := by
  have h1 : Nat.card C = Nat.card (C ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup
  have h2 : Nat.card C = Nat.card (C ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range f).toAddSubgroup
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (h2.trans (mul_comm _ _)))

private theorem exists_psi : ∃ ψ : D.U →ₗ[ℤ] I, ∀ u : D.U, D.delI (ψ u) = D.d u := by
  let e := LinearEquiv.ofInjective D.delI (delI_inj D)
  let c : D.U →ₗ[ℤ] LinearMap.range D.delI :=
    (D.d ∘ₗ D.U.subtype).codRestrict (LinearMap.range D.delI) (fun u => u.2)
  refine ⟨e.symm.toLinearMap ∘ₗ c, fun u => ?_⟩
  have h := LinearEquiv.ofInjective_apply D.delI (h := delI_inj D) (e.symm (c u))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end SlopeTestRemainingChoices

theorem UpperTheory.V.ZK.Ct.cardW :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), Finite (I ⧸ LinearMap.range D.d) → Finite D.EQ → Finite D.ClQ ∧ Finite D.W ∧ Nat.card D.W = Nat.card D.EQ * Nat.card D.ClQ := by
  intro Y I _ _ D hC hE
  obtain ⟨ψ, hψ⟩ := exists_psi D
  have hψ0 : ∀ u : D.U, D.d u = 0 → ψ u = 0 := fun u hu =>
    delI_inj D (by rw [hψ, hu, map_zero])
  let S := (LinearMap.range D.del ⊔ Submodule.torsion ℤ Y).submoduleOf D.U
  let p := LinearMap.range D.d
  have hpf : p ≤ p.comap D.delI := by
    rintro _ ⟨y, rfl⟩
    exact ⟨D.del y, d_del D y⟩
  let f : (I ⧸ p) →ₗ[ℤ] (I ⧸ p) := p.mapQ p D.delI hpf
  let φ : D.U →ₗ[ℤ] I ⧸ p := p.mkQ ∘ₗ ψ
  have hSφ : S ≤ LinearMap.ker φ := by
    intro u hu
    change (u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y at hu
    obtain ⟨a, ⟨y, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 hu
    have hy : ψ u = D.d y :=
      delI_inj D (by rw [hψ, ← hat, map_add (f := _), d_tors D ht, add_zero, d_del])
    change p.mkQ (ψ u) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hy]
    exact LinearMap.mem_range_self _ _
  let φb : D.W →ₗ[ℤ] I ⧸ p := S.liftQ φ hSφ
  have hkU : LinearMap.ker D.d ≤ D.U := fun y hy => by
    change D.d y ∈ LinearMap.range D.delI
    rw [LinearMap.mem_ker.1 hy]
    exact zero_mem _
  let ι : LinearMap.ker D.d →ₗ[ℤ] D.W := S.mkQ ∘ₗ Submodule.inclusion hkU
  have hrange : LinearMap.range φb = LinearMap.ker f := by
    show LinearMap.range (S.liftQ φ hSφ) = LinearMap.ker f
    rw [Submodule.range_liftQ]
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      change (Submodule.Quotient.mk (D.delI (ψ u)) : I ⧸ p) = 0
      rw [hψ, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self _ _
    · intro hx
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p x
      rw [LinearMap.mem_ker] at hx
      change (Submodule.Quotient.mk (D.delI x) : I ⧸ p) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy⟩ := hx
      have hyU : y ∈ D.U := ⟨x, hy.symm⟩
      have hψy : ψ ⟨y, hyU⟩ = x := delI_inj D (by rw [hψ]; exact hy)
      refine ⟨⟨y, hyU⟩, ?_⟩
      show p.mkQ (ψ ⟨y, hyU⟩) = p.mkQ x
      rw [hψy]
  have hker : LinearMap.ker φb = LinearMap.range ι := by
    ext w
    obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective S w
    constructor
    · intro hu
      rw [LinearMap.mem_ker] at hu
      change p.mkQ (ψ u) = 0 at hu
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu
      obtain ⟨y, hy⟩ := hu
      have hk : (u : Y) - D.del y ∈ LinearMap.ker D.d := by
        rw [LinearMap.mem_ker, map_sub, d_del, hy, ← hψ, sub_self]
      refine ⟨⟨_, hk⟩, ?_⟩
      change S.mkQ (Submodule.inclusion hkU ⟨_, hk⟩) = S.mkQ u
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      change ((u : Y) - D.del y - u) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y
      rw [sub_sub_cancel_left]
      exact Submodule.mem_sup_left (Submodule.neg_mem _ (LinearMap.mem_range_self _ _))
    · rintro ⟨k, hk⟩
      rw [LinearMap.mem_ker, ← hk]
      have hk0 : ψ (Submodule.inclusion hkU k) = 0 := hψ0 _ k.2
      change p.mkQ (ψ (Submodule.inclusion hkU k)) = 0
      rw [hk0, map_zero]
  have hkerι : LinearMap.ker ι = (Submodule.map D.del (LinearMap.ker D.d) ⊔
      Submodule.torsion ℤ Y).submoduleOf (LinearMap.ker D.d) := by
    ext k
    rw [LinearMap.mem_ker]
    change S.mkQ (Submodule.inclusion hkU k) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (k : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y ↔
      (k : Y) ∈ Submodule.map D.del (LinearMap.ker D.d) ⊔ Submodule.torsion ℤ Y
    constructor
    · intro h
      obtain ⟨a, ⟨y, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 h
      have hy : D.d y = 0 := by
        apply delI_inj D
        rw [map_zero, ← d_del]
        have hk := k.2
        rw [LinearMap.mem_ker, ← hat, map_add (f := _), d_tors D ht, add_zero] at hk
        exact hk
      exact Submodule.mem_sup.2 ⟨D.del y, ⟨y, hy, rfl⟩, t, ht, hat⟩
    · intro h
      obtain ⟨a, ⟨y, -, rfl⟩, t, ht, hat⟩ := Submodule.mem_sup.1 h
      exact Submodule.mem_sup.2 ⟨D.del y, LinearMap.mem_range_self _ _, t, ht, hat⟩
  haveI : Finite (I ⧸ p) := hC
  haveI : Finite D.EQ := hE
  have hr : LinearMap.range f = Submodule.map p.mkQ (LinearMap.range D.delI) :=
    calc LinearMap.range f = LinearMap.range (f ∘ₗ p.mkQ) :=
          (LinearMap.range_comp_of_range_eq_top f (Submodule.range_mkQ p)).symm
      _ = LinearMap.range (p.mkQ ∘ₗ D.delI) := by rw [Submodule.mapQ_mkQ]
      _ = Submodule.map p.mkQ (LinearMap.range D.delI) := LinearMap.range_comp _ _
  have hQ : Finite ((I ⧸ p) ⧸ Submodule.map p.mkQ (LinearMap.range D.delI)) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hClQ : Finite D.ClQ :=
    Finite.of_equiv _ (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv
  have hcoker : Nat.card D.ClQ = Nat.card ((I ⧸ p) ⧸ LinearMap.range f) := by
    rw [hr]
    exact Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup p (LinearMap.range D.delI)).toEquiv.symm
  have hkf := card_ker_eq_coker f
  have hEQ : Nat.card D.EQ = Nat.card (LinearMap.range ι) :=
    Nat.card_congr ((Submodule.quotEquivOfEq _ _ hkerι.symm).trans ι.quotKerEquivRange).toEquiv
  have hW : Nat.card D.W = Nat.card (D.W ⧸ LinearMap.ker φb) * Nat.card (LinearMap.ker φb) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker φb).toAddSubgroup
  have hmain : Nat.card D.W = Nat.card D.EQ * Nat.card D.ClQ := by
    rw [hW, Nat.card_congr φb.quotKerEquivRange.toEquiv, hrange, hkf, ← hcoker, hker, ← hEQ]
    exact mul_comm _ _
  have hne : Nat.card D.W ≠ 0 := by
    rw [hmain]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  exact ⟨hClQ, Nat.finite_of_card_ne_zero hne, hmain⟩
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem UpperTheory.V.ZK.Ct.kerF_tele {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I) :
    ∑ j ∈ Finset.range D.n, (((D.a : ℤ) ^ j) • D.g ^ (D.n - j + 1) - ((D.a : ℤ) ^ (j + 1)) • D.g ^ (D.n - j))
      = (1 - (D.a : ℤ) ^ D.n) • D.g := by
  have key : ∀ j ∈ Finset.range D.n,
      ((D.a : ℤ) ^ j • D.g ^ (D.n - j + 1) - (D.a : ℤ) ^ (j + 1) • D.g ^ (D.n - j))
        = (fun k => (D.a : ℤ) ^ k • D.g ^ (D.n - k + 1)) j
          - (fun k => (D.a : ℤ) ^ k • D.g ^ (D.n - k + 1)) (j + 1) := by
    intro j hj
    have hj' : j < D.n := Finset.mem_range.mp hj
    have e : D.n - (j + 1) + 1 = D.n - j := by omega
    simp only [e]
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub']
  simp only [pow_zero, one_smul, Nat.sub_zero, Nat.sub_self, zero_add, pow_one]
  rw [pow_succ, D.g_pow, one_mul, sub_smul, one_smul]

private theorem UpperTheory.V.ZK.Ct.kerF_nm_del {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I) :
    D.nm * D.del = (1 - (D.a : ℤ) ^ D.n) • D.g := by
  rw [← kerF_tele D]
  simp only [Dat.nm, Dat.del, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_mul_assoc, mul_sub, mul_smul_comm, mul_one, smul_sub, smul_smul, ← pow_succ, ← pow_succ]

private theorem UpperTheory.V.ZK.Ct.kerF_del_nm {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I) :
    D.del * D.nm = (1 - (D.a : ℤ) ^ D.n) • D.g := by
  rw [← kerF_tele D]
  simp only [Dat.nm, Dat.del, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_smul_comm, sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul, ← pow_succ, ← pow_succ']

private theorem UpperTheory.V.ZK.Ct.kerF_tors {Y : Type} [AddCommGroup Y] (φ : Module.End ℤ Y) {t : Y}
    (ht : t ∈ Submodule.torsion ℤ Y) : φ t ∈ Submodule.torsion ℤ Y := by
  obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff t).mp ht
  refine (Submodule.mem_torsion_iff _).mpr ⟨c, ?_⟩
  rw [Submonoid.smul_def] at hc ⊢
  rw [← φ.map_smul, hc, map_zero]

private theorem UpperTheory.V.ZK.Ct.kerF_tors' {Y : Type} [AddCommGroup Y] {q : ℤ} (hq : q ≠ 0) {t : Y}
    (ht : q • t ∈ Submodule.torsion ℤ Y) : t ∈ Submodule.torsion ℤ Y := by
  obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff _).mp ht
  rw [Submonoid.smul_def, smul_smul] at hc
  have hne : (c : ℤ) * q ≠ 0 := mul_ne_zero (nonZeroDivisors.coe_ne_zero c) hq
  exact (Submodule.mem_torsion_iff _).mpr ⟨⟨(c : ℤ) * q, mem_nonZeroDivisors_of_ne_zero hne⟩, hc⟩

theorem UpperTheory.V.ZK.Ct.kerF :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), ∀ (q s : ℕ) (u : ℤ), (D.a : ℤ) ^ D.n - 1 = q * u → ∃ f : D.W →ₗ[ℤ] Y ⧸ mt Y q, (∀ y : D.U, f (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((s : ℤ) • D.nm y)) ∧ ∀ w, f w = 0 → (u * s) • w = 0 := by
  intro Y I _ _ D q s u h
  set R : Submodule ℤ Y := LinearMap.range D.del ⊔ Submodule.torsion ℤ Y with hRdef
  have hq0 : (q : ℤ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, sub_eq_zero] at h
    have h2 : (2 : ℤ) ≤ (D.a : ℤ) := by exact_mod_cast D.two_le
    have : (2 : ℤ) ≤ (D.a : ℤ) ^ D.n := le_trans h2 (le_self_pow₀ (by linarith) D.n_pos.ne')
    linarith
  have hnd : ∀ z : Y, D.nm (D.del z) = ((q : ℤ) * (-u)) • D.g z := by
    intro z
    have e : ((q : ℤ) * (-u)) = 1 - (D.a : ℤ) ^ D.n := by linarith
    rw [e, ← LinearMap.smul_apply, ← kerF_nm_del D, Module.End.mul_apply]
  have hdn : ∀ z : Y, D.del (D.nm z) = ((q : ℤ) * (-u)) • D.g z := by
    intro z
    have e : ((q : ℤ) * (-u)) = 1 - (D.a : ℤ) ^ D.n := by linarith
    rw [e, ← LinearMap.smul_apply, ← kerF_del_nm D, Module.End.mul_apply]
  let φ : D.U →ₗ[ℤ] Y ⧸ mt Y q := (mt Y q).mkQ ∘ₗ ((s : ℤ) • D.nm) ∘ₗ D.U.subtype
  have hker : R.submoduleOf D.U ≤ LinearMap.ker φ := by
    have hle : R ≤ (mt Y q).comap ((s : ℤ) • D.nm) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨z, rfl⟩
        rw [Submodule.mem_comap, LinearMap.smul_apply, hnd]
        refine Submodule.mem_sup_left ⟨(s : ℤ) • (-u) • D.g z, ?_⟩
        simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
        congr 1
        ring
      · intro x hx
        rw [Submodule.mem_comap, LinearMap.smul_apply]
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (kerF_tors _ hx))
    intro y hy
    rw [LinearMap.mem_ker]
    have := hle hy
    rw [Submodule.mem_comap] at this
    simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact this
  refine ⟨(R.submoduleOf D.U).liftQ φ hker, ?_, ?_⟩
  · intro y
    rfl
  · intro w hw
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hw' : (s : ℤ) • D.nm (y : Y) ∈ mt Y q := by
      have := hw
      simp only [Submodule.liftQ_apply, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply, Submodule.coe_subtype] at this
      exact this
    set v : Y := (s : ℤ) • (y : Y) with hv
    have hnv : D.nm v = (s : ℤ) • D.nm (y : Y) := by rw [hv, map_smul]
    rw [← hnv] at hw'
    obtain ⟨a, ⟨z, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hw'
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hab
    have hdel : (q : ℤ) • ((-u) • D.g v - D.del z) = D.del b := by
      have e1 := congrArg D.del hab
      rw [map_add (f := _), map_smul, hdn] at e1
      rw [smul_sub, smul_smul, ← e1]
      abel
    have htor : (-u) • D.g v - D.del z ∈ Submodule.torsion ℤ Y :=
      kerF_tors' hq0 (by rw [hdel]; exact kerF_tors _ hb)
    have hR : (u : ℤ) • D.g v ∈ R := by
      have e : (u : ℤ) • D.g v = -(D.del z + ((-u) • D.g v - D.del z)) := by
        rw [neg_smul]
        abel
      rw [e]
      exact R.neg_mem (R.add_mem (Submodule.mem_sup_left ⟨z, rfl⟩) (Submodule.mem_sup_right htor))
    have hcomm : Commute (D.g ^ (D.n - 1)) D.del := by
      show Commute _ (D.g - (D.a : ℤ) • 1)
      exact ((Commute.refl D.g).pow_left _).sub_right ((Commute.one_right _).smul_right _)
    have hstab : ∀ x ∈ R, (D.g ^ (D.n - 1)) x ∈ R := by
      intro x hx
      obtain ⟨c, ⟨z', rfl⟩, e, he, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add (f := _), ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
      exact R.add_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right (kerF_tors _ he))
    have hgv : (D.g ^ (D.n - 1)) ((u : ℤ) • D.g v) = (u : ℤ) • v := by
      rw [map_smul, ← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel D.n_pos, D.g_pow,
        Module.End.one_apply]
    have hfin : ((u * s : ℤ) • (y : Y)) ∈ R := by
      rw [mul_smul, ← hv, ← hgv]
      exact hstab _ hR
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hfin
end
