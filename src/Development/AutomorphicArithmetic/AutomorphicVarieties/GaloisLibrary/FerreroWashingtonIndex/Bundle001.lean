module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

section

open UpperTheory.V.FW

private theorem card_dual (K A : Type) [Field K] [AddCommGroup A] [Module K A] [Finite A] :
    Nat.card (Module.Dual K A) = Nat.card A := by
  exact Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv

private theorem card_addHom_mod (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Finite A]
    [Module (ZMod l) A] : Nat.card (A →+ ZMod l) = Nat.card A := by
  rw [← card_dual (ZMod l) A]
  exact Nat.card_congr
    { toFun := fun f => f.toZModLinearMap l
      invFun := fun g => g.toAddMonoidHom
      left_inv := fun f => by ext; rfl
      right_inv := fun g => by ext; rfl }

private theorem card_addHom_zmod (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Finite A]
    (h : ∀ x : A, l • x = 0) : Nat.card (A →+ ZMod l) = Nat.card A :=
  @card_addHom_mod l _ A _ _ (AddCommGroup.zmodModule h)

theorem UpperTheory.V.FW.cardTors :
    ∀ (C : Type) [CommGroup C] [Finite C], (∀ n : ℕ, (powR (C := C) n).index = Nat.card (torK (C := C) n)) ∧ ∀ (l : ℕ) [Fact l.Prime], Nat.card (C →* Multiplicative (ZMod l)) = (powR (C := C) l).index := by
  intro C _ _
  refine ⟨fun n => ?_, fun l _ => ?_⟩
  · have h1 := Subgroup.card_mul_index (powR (C := C) n)
    have h2 := Subgroup.card_mul_index (torK (C := C) n)
    have h3 : (torK (C := C) n).index = Nat.card (powR (C := C) n) := Subgroup.index_ker _
    rw [h3] at h2
    have hpos : 0 < Nat.card (powR (C := C) n) := Nat.card_pos
    have h4 : Nat.card (powR (C := C) n) * (powR (C := C) n).index
        = Nat.card (powR (C := C) n) * Nat.card (torK (C := C) n) := by
      rw [h1, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  · set N := powR (C := C) l
    have hle : ∀ f : C →* Multiplicative (ZMod l), N ≤ f.ker := by
      intro f x hx
      change x ∈ (powMonoidHom l : C →* C).range at hx
      rcases MonoidHom.mem_range.mp hx with ⟨c, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow]
    have e : (C ⧸ N →* Multiplicative (ZMod l)) ≃ (C →* Multiplicative (ZMod l)) :=
      { toFun := fun g => g.comp (QuotientGroup.mk' N)
        invFun := fun f => QuotientGroup.lift N f (hle f)
        left_inv := fun g => by
          apply QuotientGroup.monoidHom_ext
          ext
          rfl
        right_inv := fun f => by
          ext
          rfl }
    rw [← Nat.card_congr e, Nat.card_congr MonoidHom.toAdditiveLeft]
    have ht : ∀ x : Additive (C ⧸ N), l • x = 0 := by
      intro x
      obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective N (Additive.toMul x)
      apply Additive.toMul.injective
      rw [toMul_nsmul, ← hc, toMul_zero, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow,
        QuotientGroup.eq_one_iff]
      change c ^ l ∈ (powMonoidHom l : C →* C).range
      exact MonoidHom.mem_range.mpr ⟨c, by simp [powMonoidHom_apply]⟩
    rw [card_addHom_zmod l (Additive (C ⧸ N)) ht]
    rfl
end

section

open UpperTheory.V.FW

private theorem norm_index_count_bound (M a c : ℕ) :
    (((a + c) / M : ℕ) : ℤ) = ((a / M : ℕ) : ℤ) +
      ∑ j ∈ Finset.range c, if (j : ZMod M) = ((a + c : ℕ) : ZMod M) then 1 else 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    have e : a + (c + 1) = (a + c) + 1 := by omega
    have h1 : ∀ j : ℕ, (((j + 1 : ℕ) : ZMod M) = (((a + c + 1 : ℕ)) : ZMod M)) ↔
        ((j : ZMod M) = ((a + c : ℕ) : ZMod M)) := by
      intro j
      push_cast
      exact add_left_inj 1
    have h2 : ((0 : ℕ) : ZMod M) = ((a + c + 1 : ℕ) : ZMod M) ↔ M ∣ a + c + 1 := by
      rw [Nat.cast_zero, eq_comm]
      exact CharP.cast_eq_zero_iff (ZMod M) M _
    rw [e, Nat.succ_div, Finset.sum_range_succ']
    simp only [h1, h2]
    rw [Nat.cast_add, ih]
    split_ifs <;> push_cast <;> ring

theorem UpperTheory.V.FW.gcDiff :
    ∀ (M c : ℕ) [NeZero M] (s : ZMod M), c.Coprime M → gc M c s - gc M c (s - c) = (∑ j ∈ Finset.range c, if (j : ZMod M) = s then 1 else 0) - if s = 0 then (c : ℤ) else 0 := by
  intro M c _ s hc
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hinv : (c : ZMod M)⁻¹ * (c : ZMod M) = 1 := by
    rw [mul_comm]
    exact ZMod.coe_mul_inv_eq_one c hc
  have hts : (c : ZMod M)⁻¹ * (s - c) = (c : ZMod M)⁻¹ * s - 1 := by
    rw [mul_sub, hinv]
  unfold UpperTheory.V.FW.gc
  rw [hts]
  set t : ZMod M := (c : ZMod M)⁻¹ * s with ht
  have hs : s = (c : ZMod M) * t := by
    rw [ht, ← mul_assoc, ZMod.coe_mul_inv_eq_one c hc, one_mul]
  set w := (t - 1).val with hw
  have htw : t = ((w + 1 : ℕ) : ZMod M) := by
    rw [Nat.cast_add, Nat.cast_one, hw, ZMod.natCast_zmod_val]
    ring
  have key := norm_index_count_bound M (c * w) c
  have hcast : ((c * w + c : ℕ) : ZMod M) = s := by
    rw [hs, htw]
    push_cast
    ring
  rw [hcast] at key
  rcases Nat.lt_or_ge (w + 1) M with h | h
  · have hvt : t.val = w + 1 := by
      rw [htw, ZMod.val_natCast, Nat.mod_eq_of_lt h]
    have hs0 : s ≠ 0 := by
      intro h0
      have t0 : t = 0 := by rw [ht, h0, mul_zero]
      rw [t0, ZMod.val_zero] at hvt
      omega
    rw [hvt, if_neg hs0, sub_zero]
    have e : c * (w + 1) = c * w + c := by ring
    rw [e, key]
    ring
  · have hwe : w + 1 = M := by
      have := ZMod.val_lt (t - 1)
      omega
    have ht0 : t = 0 := by rw [htw, hwe, ZMod.natCast_self]
    have hs0 : s = 0 := by rw [hs, ht0, mul_zero]
    rw [ht0, ZMod.val_zero, if_pos hs0]
    have e : c * w + c = c * M := by rw [← hwe]; ring
    rw [e, Nat.mul_div_cancel _ hM] at key
    simp only [mul_zero, Nat.zero_div, Nat.cast_zero]
    linarith
end

section

open UpperTheory.V.FW

private theorem div_sub_add_div_add_one_eq (c M a : ℕ) (hM : 0 < M) (hr : a % M ≠ 0) (ha : a < c * M) :
    (c * M - a) / M + a / M + 1 = c := by
  have hdm := Nat.div_add_mod a M
  have hrl := Nat.mod_lt a hM
  generalize a / M = k at hdm ⊢
  generalize a % M = r at hdm hrl hr
  subst hdm
  have hkc : k < c := by
    by_contra hck
    push_neg at hck
    have : M * c ≤ M * k := Nat.mul_le_mul_left M hck
    nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, c = k + 1 + j := ⟨c - k - 1, by omega⟩
  have e1 : (k + 1 + j) * M = M * k + M + j * M := by ring
  have hq : ((k + 1 + j) * M - (M * k + r)) / M = j := by
    apply Nat.div_eq_of_lt_le
    · rw [e1]
      omega
    · rw [e1, Nat.add_mul, Nat.one_mul]
      omega
  rw [hq]
  omega

theorem UpperTheory.V.FW.gcNeg :
    ∀ (M c : ℕ) [NeZero M] (s : ZMod M), c.Coprime M → Odd c → s ≠ 0 → gc M c (-s) = -gc M c s := by
  intro M c _ s hc hodd hs
  unfold gc
  have hcu : IsUnit (c : ZMod M) := (ZMod.isUnit_iff_coprime c M).mpr hc
  have ht : (c : ZMod M)⁻¹ * -s = -((c : ZMod M)⁻¹ * s) := by ring
  have ht0 : (c : ZMod M)⁻¹ * s ≠ 0 := by
    intro h0
    apply hs
    calc s = ((c : ZMod M) * (c : ZMod M)⁻¹) * s := by rw [ZMod.mul_inv_of_unit _ hcu, one_mul]
      _ = (c : ZMod M) * ((c : ZMod M)⁻¹ * s) := by ring
      _ = 0 := by rw [h0, mul_zero]
  haveI : NeZero ((c : ZMod M)⁻¹ * s) := ⟨ht0⟩
  rw [ht, ZMod.val_neg_of_ne_zero]
  have hv0 : 0 < ((c : ZMod M)⁻¹ * s).val := ZMod.val_pos.mpr ht0
  have hvM : ((c : ZMod M)⁻¹ * s).val < M := ZMod.val_lt _
  generalize ((c : ZMod M)⁻¹ * s).val = v at hv0 hvM ⊢
  have hMpos : 0 < M := by omega
  have hcpos : 0 < c := hodd.pos
  have hndvd : (c * v) % M ≠ 0 := by
    intro h0
    have h1 : M ∣ c * v := Nat.dvd_of_mod_eq_zero h0
    have h2 : M ∣ v := (Nat.Coprime.dvd_mul_left hc.symm).mp h1
    have := Nat.le_of_dvd hv0 h2
    omega
  have hlt : c * v < c * M := Nat.mul_lt_mul_of_pos_left hvM hcpos
  have key := div_sub_add_div_add_one_eq c M (c * v) hMpos hndvd hlt
  rw [mul_tsub]
  obtain ⟨m, rfl⟩ := hodd
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm]
  generalize ((2 * m + 1) * M - (2 * m + 1) * v) / M = P at key ⊢
  generalize (2 * m + 1) * v / M = Q at key ⊢
  push_cast
  omega
end

section

open UpperTheory.V.FW

private theorem UpperTheory.V.FW.descZ_retr (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] :
    ∃ ϖ : k →+ ZMod l, ϖ 1 = 1 := by
  letI := ZMod.algebra k l
  have hinj : LinearMap.ker (LinearMap.toSpanSingleton (ZMod l) k 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b h
    simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one] at h
    exact (algebraMap (ZMod l) k).injective h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨g.toAddMonoidHom, ?_⟩
  have h1 := LinearMap.congr_fun hg 1
  simpa using h1

private theorem UpperTheory.V.FW.descZ_mul {k F G : Type} [CommRing k] [CommRing F] [CommGroup G] (ϖ : k →+ F)
    (u : MonoidAlgebra k G) (a : MonoidAlgebra ℤ G) :
    MonoidAlgebra.map ϖ (u * toK k G a) = MonoidAlgebra.map ϖ u * toK F G a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), mul_add, MonoidAlgebra.map_add (f := _), hx, hy, map_add (f := _), mul_add]
  | single g n =>
    ext h
    simp only [toK, MonoidAlgebra.mapRingHom_single, eq_intCast, MonoidAlgebra.coeff_map,
      Finsupp.mapRange_apply, MonoidAlgebra.mul_single_apply, AddMonoidHom.coe_coe]
    rw [← zsmul_eq_mul', map_zsmul, zsmul_eq_mul']

private theorem UpperTheory.V.FW.descZ_ker (l : ℕ) {G : Type} [CommGroup G] (y : MonoidAlgebra ℤ G)
    (hy : toK (ZMod l) G y = 0) : ∃ z, y = z * (l : MonoidAlgebra ℤ G) := by
  classical
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun n : ℤ => n / (l : ℤ)) (by simp) y.coeff), ?_⟩
  ext g
  have hg : (l : ℤ) ∣ y.coeff g := by
    have h0 := congrArg (fun w => w.coeff g) hy
    simp only [toK, MonoidAlgebra.coeff_mapRingHom, eq_intCast, MonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h0
    exact (CharP.intCast_eq_zero_iff (ZMod l) l _).mp h0
  rw [MonoidAlgebra.natCast_def, MonoidAlgebra.mul_single_apply, inv_one, mul_one,
    MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, Int.ediv_mul_cancel hg]

theorem UpperTheory.V.FW.descZ :
    ∀ (l : ℕ) [Fact l.Prime] (k G : Type) [Field k] [CharP k l] [CommGroup G] (x a b : MonoidAlgebra ℤ G), toK k G x ∈ Ideal.span {toK k G a, toK k G b} → x ∈ Ideal.span {a, b, (l : MonoidAlgebra ℤ G)} := by
  intro l _ k G _ _ _ x a b hx
  obtain ⟨ϖ, hϖ⟩ := descZ_retr l k
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hx
  have h1 : MonoidAlgebra.map ϖ (1 : MonoidAlgebra k G) = 1 := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.map_single, hϖ, MonoidAlgebra.one_def]
  have h2 := descZ_mul ϖ 1 x
  rw [one_mul, h1, one_mul, ← huv, MonoidAlgebra.map_add (f := _), descZ_mul, descZ_mul] at h2
  have hs : Function.Surjective (toK (ZMod l) G) :=
    MonoidAlgebra.map_surjective (Int.castRingHom (ZMod l) : ℤ →+ ZMod l) ZMod.intCast_surjective
  obtain ⟨u', hu⟩ := hs (MonoidAlgebra.map ϖ u)
  obtain ⟨v', hv⟩ := hs (MonoidAlgebra.map ϖ v)
  obtain ⟨z, hz⟩ := descZ_ker l (x - (u' * a + v' * b)) (by
    rw [map_sub, map_add (f := _), map_mul, map_mul, hu, hv, h2, sub_self])
  have hx' : x = u' * a + v' * b + z * (l : MonoidAlgebra ℤ G) := by rw [← hz]; ring
  rw [hx']
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
end

section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.frobEig :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) (k G A : Type) [Field k] [CharP k l] [CommGroup G] [CommRing A] [Algebra k A] (r : MonoidAlgebra k G →ₐ[k] A) (p : G →* G) (χ : G →* kˣ) (e : A) (θ : MonoidAlgebra k G), (∀ g, r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ l ^ a)) * e = ((χ g : k) ^ l ^ a) • e) → r θ ^ l ^ a * e = r (tw χ p θ) ^ l ^ a * e := by
  intro l _ a k G A _ _ _ _ _ r p χ e θ h
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  haveI : CharP A l := charP_of_injective_algebraMap (algebraMap k A).injective l
  set q := l ^ a with hq
  have frob_add : ∀ x y : A, (x + y) ^ q = x ^ q + y ^ q := fun x y => by
    rw [hq]
    exact add_pow_char_pow x y l a
  have hs : ∀ (x : G) (b : k), r (MonoidAlgebra.single x b) ^ q = b ^ q • r (MonoidAlgebra.of k G (x ^ q)) := by
    intro x b
    have e1 : MonoidAlgebra.single x b = b • MonoidAlgebra.of k G x := by
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']
    rw [e1, map_smul, smul_pow, map_pow (MonoidAlgebra.of k G), map_pow r]
  induction θ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add (f := _), frob_add, add_mul, hf, hg]
  | single g c =>
    rw [tw_single, hs, hs]
    have hg : g ^ q = (g * (p g)⁻¹) ^ q * (p g) ^ q := by
      rw [mul_pow, inv_pow, inv_mul_cancel_right]
    rw [hg, map_mul, map_mul, smul_mul_assoc, smul_mul_assoc,
      mul_comm (r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ q))), mul_assoc, h g, mul_smul_comm,
      smul_smul, mul_pow]
end

section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.pTwo :
    ∀ (C : Type) [CommGroup C] [Finite C] (J : C →* C), (∀ x, J (J x) = x) →
      (powR (C := C) 2).index ≤
        ((difR J).relIndex (minK J) * Nat.card (difR J ⊓ torK (C := C) 2 : Subgroup C)) ^ 2 := by
  intro C _ _ J hJ
  classical
  have hcard : ∀ {G H : Type} [Group G] [Group H] (f : G →* H),
      Nat.card G = Nat.card f.ker * Nat.card f.range := by
    intro G H _ _ f
    rw [← f.ker.card_mul_index, Subgroup.index_ker]
  set T := torK (C := C) 2 with hT
  set D := difR J with hD
  set K := minK J with hK
  have memT : ∀ x : C, x ∈ T ↔ x ^ 2 = 1 := fun x => by simp [hT, torK]
  have memK : ∀ x : C, x ∈ K ↔ J x * x = 1 := fun x => by simp [hK, minK]
  have memD : ∀ x : C, x ∈ D ↔ ∃ y, y / J y = x := fun x => by simp [hD, difR]
  have hDK : D ≤ K := by
    intro x hx
    obtain ⟨y, rfl⟩ := (memD x).1 hx
    rw [memK, map_div, hJ, div_mul_div_comm, mul_comm (J y) y, div_self']
  have h1 : (powR (C := C) 2).index = Nat.card T := by
    have e1 := hcard (powMonoidHom 2 : C →* C)
    have e2 := (powR (C := C) 2).card_mul_index
    have hpos : 0 < Nat.card (powR (C := C) 2) := Nat.card_pos
    have e3 : Nat.card (powR (C := C) 2) * (powR (C := C) 2).index =
        Nat.card (powR (C := C) 2) * Nat.card T := by
      rw [e2, mul_comm]
      exact e1
    exact Nat.eq_of_mul_eq_mul_left hpos e3
  let g : T →* C := (MonoidHom.id C / J).comp T.subtype
  have e4 := hcard g
  have r1 : Nat.card g.range ≤ Nat.card (D ⊓ T : Subgroup C) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨t, rfl⟩
    have gt : g t = t.1 / J t.1 := rfl
    rw [gt, Subgroup.mem_inf]
    refine ⟨(memD _).2 ⟨t.1, rfl⟩, ?_⟩
    rw [memT, div_pow, ← map_pow, (memT _).1 t.2, map_one, div_one]
  have r2 : Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := by
    have hm : ∀ x : g.ker, (x.1.1 : C) ∈ K ⊓ T := by
      intro x
      have hx : g x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hT' : x.1.1 ^ 2 = 1 := (memT _).1 x.1.2
      have hd : x.1.1 / J x.1.1 = 1 := hx
      have hJx : J x.1.1 = x.1.1 := (div_eq_one.1 hd).symm
      refine Subgroup.mem_inf.2 ⟨(memK _).2 ?_, x.1.2⟩
      rw [hJx, ← pow_two, hT']
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (K ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  let incl : (K ⊓ T : Subgroup C) →* K := Subgroup.inclusion inf_le_left
  let h : (K ⊓ T : Subgroup C) →* K ⧸ D.subgroupOf K := (QuotientGroup.mk' (D.subgroupOf K)).comp incl
  have e5 := hcard h
  have r3 : Nat.card h.range ≤ D.relIndex K :=
    le_of_le_of_eq (Subgroup.card_le_card_group _) rfl
  have r4 : Nat.card h.ker ≤ Nat.card (D ⊓ T : Subgroup C) := by
    have hm : ∀ x : h.ker, (x.1.1 : C) ∈ D ⊓ T := by
      intro x
      have hx : h x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hx2 : incl x.1 ∈ D.subgroupOf K := (QuotientGroup.eq_one_iff _).1 hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hx2, (Subgroup.mem_inf.1 x.1.2).2⟩
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (D ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  rw [h1]
  set r := D.relIndex K
  set d := Nat.card (D ⊓ T : Subgroup C)
  have s1 : Nat.card T ≤ (r * d) * d := by
    rw [e4]
    apply Nat.mul_le_mul _ r1
    calc Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := r2
      _ = Nat.card h.ker * Nat.card h.range := e5
      _ ≤ d * r := Nat.mul_le_mul r4 r3
      _ = r * d := mul_comm _ _
  have s2 : (r * d) * d ≤ (r * d) ^ 2 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · simp [hr]
    · rw [pow_two]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left d hr)
  exact s1.trans s2
end

section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.pushDiff :
    ∀ (k : Type) [CommRing k] (M m : ℕ) [NeZero M] (h : m ∣ M) (N : ℕ) (P : ℕ → k) (g : ZMod M → k), (∀ s, g s - g (s - N) = ∑ j ∈ Finset.range N, if (j : ZMod M) = s then P j else 0) → ∀ y : ZMod m, push h g y - push h g (y - N) = ∑ j ∈ Finset.range N, if (j : ZMod m) = y then P j else 0 := by
  intro k _ M m _ h N P g hg y
  simp only [push]
  have shift : (∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y - N), g s)
      = ∑ s ∈ Finset.univ.filter (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y), g (s - N) := by
    apply Finset.sum_nbij' (fun s : ZMod M => s + (N : ZMod M)) (fun s : ZMod M => s - (N : ZMod M))
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_add (f := _), hs, map_natCast]
      ring
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      rw [map_sub, hs, map_natCast]
    · intro s _
      ring
    · intro s _
      ring
    · intro s _
      congr 1
      ring
  rw [shift, ← Finset.sum_sub_distrib]
  simp_rw [hg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_ite_eq]
  have key : (j : ZMod M) ∈ Finset.univ.filter
      (fun s : ZMod M => ZMod.castHom h (ZMod m) s = y) ↔ (j : ZMod m) = y := by
    rw [Finset.mem_filter, ZMod.castHom_apply, ZMod.cast_natCast h]
    simp
  by_cases hj : (j : ZMod m) = y
  · rw [if_pos (key.mpr hj), if_pos hj]
  · rw [if_neg (fun t => hj (key.mp t)), if_neg hj]
end
