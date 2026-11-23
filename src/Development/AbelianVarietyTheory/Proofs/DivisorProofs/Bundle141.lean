module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Smooth.Basic
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Data.ZMod.QuotientRing

@[expose] public section

section

namespace GlobalTheory

open CommRing

theorem natCast_mul_mem_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    (n : ℕ) (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range)
    (I : (Submodule B B')ˣ) (x : B') : (n : B') * x ∈ (I : Submodule B B') := by
  have h1 : (1 : B') ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B') := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Submodule.one_le.mp le_rfl
  have key : ∀ y ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B'),
      ((n : B') * x) * y ∈ (I : Submodule B B') := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun j _ i hi => ?_) (fun y z hy hz => ?_)
    · obtain ⟨b, hb⟩ := hn (x * j)
      have : (n : B') * x * (j * i) = b • i := by
        rw [Algebra.smul_def, hb]; ring
      rw [this]; exact Submodule.smul_mem _ b hi
    · rw [mul_add]; exact Submodule.add_mem _ hy hz
  simpa using key 1 h1

theorem finite_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Finite ℤ B'] (n : ℕ) (hn0 : n ≠ 0)
    (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range) :
    Finite (Submodule B B')ˣ := by
  set C : Submodule ℤ B' := (Ideal.span {(n : ℤ)}) • (⊤ : Submodule ℤ B') with hCdef
  haveI : NeZero n := ⟨hn0⟩
  haveI : Finite (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod n).symm.toEquiv
  haveI : Finite (B' ⧸ C) := Submodule.finite_quotient_smul _ Module.Finite.fg_top
  haveI : Finite (Submodule ℤ (B' ⧸ C)) :=
    Finite.of_injective (fun N => (N : Set (B' ⧸ C))) SetLike.coe_injective
  have hC : ∀ I : (Submodule B B')ˣ, C ≤ (I : Submodule B B').restrictScalars ℤ := by
    intro I
    refine Submodule.smul_le.mpr fun r hr x _ => ?_
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have : (k * n : ℤ) • x = (n : B') * (k • x) := by
      rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring
    rw [Submodule.restrictScalars_mem, this]
    exact natCast_mul_mem_units_submodule n hn I _
  let f : (Submodule B B')ˣ → Submodule ℤ (B' ⧸ C) := fun I =>
    Submodule.map C.mkQ ((I : Submodule B B').restrictScalars ℤ)
  refine Finite.of_injective f fun I J h => ?_
  have hIJ : (I : Submodule B B').restrictScalars ℤ = (J : Submodule B B').restrictScalars ℤ := by
    have := congrArg (Submodule.comap C.mkQ) h
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.mpr (hC I), sup_eq_right.mpr (hC J)] at this
  exact Units.ext (Submodule.restrictScalars_injective ℤ _ _ hIJ)

theorem isOfFinOrder_of_isOfFinOrder_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B']
    [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 →
    (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B,
    IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by
  intro B B' _ _ _ φ n hφ hn0 hn M hM
  letI : Algebra B B' := φ.toAlgebra
  haveI : FaithfulSMul B B' := (faithfulSMul_iff_algebraMap_injective B B').mpr hφ
  haveI := finite_units_submodule (B := B) (B' := B') n hn0 (fun b' => hn b')
  obtain ⟨k, hk, hpow⟩ := hM.exists_pow_eq_one
  have e : CommRing.Pic.mapRingHom φ = CommRing.Pic.mapAlgebra B B' :=
    CommRing.Pic.mapRingHom_algebraMap
  have hmem : M ^ k ∈ CommRing.relPic B B' := by
    rw [CommRing.relPic, MonoidHom.mem_ker, map_pow, ← e]; exact hpow
  rw [← Submodule.range_unitsToPic] at hmem
  obtain ⟨I, hI⟩ := hmem
  have hfo : IsOfFinOrder (M ^ k) := by
    rw [← hI]; exact (Submodule.unitsToPic B B').isOfFinOrder (isOfFinOrder_of_finite I)
  obtain ⟨m, hm, hm1⟩ := hfo.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul]; exact hm1⟩

end GlobalTheory
end

section

open scoped TensorProduct
open CommRing Module

variable {B : Type} [CommRing B] in
private theorem exists_local_generator (M : Type) [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (p : Ideal B) [p.IsPrime] : ∃ e : M, ∀ x : M, ∃ w a : B, w ∉ p ∧ w • x = a • e := by
  have ⟨f⟩ := Invertible.free_iff_linearEquiv.mp
    (inferInstance : Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
  obtain ⟨e, s, he⟩ : ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = f.symm 1 :=
    LocalizedModule.induction_on (β := fun y => ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = y)
      (fun e s => ⟨e, s, rfl⟩) (f.symm 1)
  refine ⟨e, fun x => ?_⟩
  obtain ⟨a, t, ht⟩ : ∃ (a : B) (t : p.primeCompl), Localization.mk a t = f (LocalizedModule.mk x 1) :=
    Localization.induction_on (f (LocalizedModule.mk x 1)) fun z => ⟨z.1, z.2, rfl⟩
  have key : LocalizedModule.mk x (1 : p.primeCompl) = LocalizedModule.mk (a • e) (t * s) := by
    rw [← f.symm_apply_apply (LocalizedModule.mk x 1), ← ht, ← mul_one (Localization.mk a t),
      ← smul_eq_mul, map_smul, ← he, LocalizedModule.mk_smul_mk]
  obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq).mp key
  refine ⟨(u : B) * ((t : B) * s), u * a, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem t.2 s.2)
  · simpa only [Submonoid.smul_def, Submonoid.coe_mul, OneMemClass.coe_one, one_smul, smul_smul] using hu

variable {B : Type} [CommRing B] in
private theorem tensorPow_equiv (c : Pic B) (n : ℕ) :
    Nonempty (Pic.AsModule (c ^ n) ≃ₗ[B] ⨂[B] _ : Fin n, Pic.AsModule c) := by
  induction n with
  | zero =>
    have ⟨e⟩ := Pic.ext_iff.mp (pow_zero c)
    have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
    exact ⟨e ≪≫ₗ g ≪≫ₗ (PiTensorProduct.isEmptyEquiv (Fin 0)).symm⟩
  | succ n ih =>
    obtain ⟨ih⟩ := ih
    have ⟨e1⟩ := Pic.ext_iff.mp (pow_succ c n)
    have ⟨e2⟩ := Pic.ext_iff.mp (Pic.mul_eq_tensor (c ^ n) c)
    exact ⟨e1 ≪≫ₗ e2 ≪≫ₗ Pic.mk.linearEquiv B _ ≪≫ₗ TensorProduct.congr ih
      (PiTensorProduct.subsingletonEquiv (R := B) (s := fun _ : Fin 1 => Pic.AsModule c) 0).symm ≪≫ₗ
      PiTensorProduct.tmulEquiv B (Pic.AsModule c) ≪≫ₗ PiTensorProduct.reindex B _ finSumFinEquiv⟩


theorem _root_.GlobalTheory.T.exists_multilinear_form_of_pic_torsion :
    ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 →
      ∃ φ : (Π _ : Fin q, CommRing.Pic.AsModule c) →ₘₗ[B] B,
        ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := by
  intro B _ q c hc
  obtain ⟨T⟩ := tensorPow_equiv c q
  have ⟨e1⟩ := Pic.ext_iff.mp hc
  have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
  let ψ : (⨂[B] _ : Fin q, Pic.AsModule c) ≃ₗ[B] B := T.symm ≪≫ₗ e1 ≪≫ₗ g
  refine ⟨ψ.toLinearMap.compMultilinearMap (PiTensorProduct.tprod B), fun p hp => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin q → Pic.AsModule c, ψ (PiTensorProduct.tprod B x) ∉ p := by
    by_contra! h
    have hall : ∀ t, ψ t ∈ p := fun t => by
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r x => rw [map_smul, smul_eq_mul]; exact p.mul_mem_left r (h x)
      | add a b ha hb => rw [map_add (f := _)]; exact p.add_mem ha hb
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (by simpa using hall (ψ.symm 1)))
  obtain ⟨e, he⟩ := exists_local_generator (Pic.AsModule c) p
  choose w a hw hwa using fun i => he (x i)
  refine ⟨e, fun hmem => ?_⟩
  have hmem' : ψ (PiTensorProduct.tprod B fun _ => e) ∈ p := hmem
  have h1 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, w i) * ψ (PiTensorProduct.tprod B x) := by
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply, map_smul, smul_eq_mul]
  have h2 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, a i) * ψ (PiTensorProduct.tprod B (fun _ => e)) := by
    simp_rw [hwa]
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply, map_smul, smul_eq_mul]
  have hin : (∏ i, w i) * ψ (PiTensorProduct.tprod B x) ∈ p := by
    rw [← h1, h2]; exact p.mul_mem_left _ hmem'
  rcases hp.mem_or_mem hin with h | h
  · exact (p.primeCompl.prod_mem fun i _ => hw i) h
  · exact hx h
end

section

open PrimeSpectrum

namespace GlobalTheory

variable {R : Type} [CommRing R]

theorem exists_mul_pow_eq_zero_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) {p : Ideal R} [hp : p.IsPrime] {a : R}
    (ha : a ∈ p) : ∃ t ∉ p, ∃ n : ℕ, t * a ^ n = 0 := by
  by_contra! H
  have hdis : Disjoint ((⊥ : Ideal R) : Set R)
      ((p.primeCompl ⊔ Submonoid.powers a : Submonoid R) : Set R) := by
    rw [Set.disjoint_left]
    rintro x hx hxS
    rw [SetLike.mem_coe, Ideal.mem_bot] at hx
    subst hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submonoid.mem_sup.mp hxS
    obtain ⟨n, rfl⟩ := hz
    exact H y hy n hyz
  obtain ⟨q, hq, -, hqd⟩ := Ideal.exists_le_prime_disjoint ⊥ _ hdis
  have hqp : q ≤ p := by
    intro x hx
    by_contra hxp
    exact Set.disjoint_left.mp hqd hx
      (Submonoid.mem_sup_left (show x ∈ p.primeCompl from hxp))
  have hqp' := (hR q hq).eq_of_le hp.ne_top hqp
  have haq : a ∉ q := fun h => Set.disjoint_left.mp hqd h
    (Submonoid.mem_sup_right (Submonoid.mem_powers a))
  exact haq (hqp' ▸ ha)

theorem isClopen_basicOpen_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (a : R) :
    IsClopen ((basicOpen a : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
  refine ⟨?_, (basicOpen a).isOpen⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  have hax : a ∈ x.asIdeal := by
    simpa [Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] using hx
  obtain ⟨t, ht, n, htn⟩ := exists_mul_pow_eq_zero_of_forall_isMaximal hR hax
  refine ⟨(basicOpen t : Set (PrimeSpectrum R)), ?_, (basicOpen t).isOpen, ht⟩
  intro y hy hya
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hy hya
  have : t * a ^ n ∈ y.asIdeal := htn ▸ y.asIdeal.zero_mem
  rcases y.isPrime.mem_or_mem this with h | h
  · exact hy h
  · exact hya (y.isPrime.mem_of_pow_mem n h)

theorem exists_isIdempotentElem_mul_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (a : R) :
    ∃ e b : R, IsIdempotentElem e ∧ a * b = e ∧ ∀ p : Ideal R, p.IsPrime → a ∉ p → e ∉ p := by
  let c : TopologicalSpace.Clopens (PrimeSpectrum R) :=
    ⟨(basicOpen a : Set (PrimeSpectrum R)), isClopen_basicOpen_of_forall_isMaximal hR a⟩
  let e := (isIdempotentElemEquivClopens (R := R)).symm c
  have he : basicOpen e.1 = basicOpen a := by
    rw [basicOpen_isIdempotentElemEquivClopens_symm]; rfl
  obtain ⟨k, hk⟩ := (basicOpen_le_basicOpen_iff _ _).mp he.le
  have hmem : e.1 ∈ Ideal.span {a} := by
    rw [← e.2.pow_succ_eq k, pow_succ']
    exact Ideal.mul_mem_left _ _ hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨e.1, b, e.2, by rw [mul_comm, hb], fun p hp hap => ?_⟩
  have h1 : (⟨p, hp⟩ : PrimeSpectrum R) ∈ basicOpen a := hap
  rw [← he] at h1
  exact h1

theorem free_of_invertible_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (M : Type) [AddCommGroup M] [Module R M]
    (hM : Module.Invertible R M) : Module.Free R M := by
  classical
  obtain ⟨S, hS⟩ := ((Module.Invertible.linearEquiv R M).symm 1).exists_finset
  replace hS : 1 = ∑ i ∈ S, i.1 i.2 := by
    simpa [LinearEquiv.symm_apply_eq, Module.Invertible.linearEquiv] using hS
  letI : LinearOrder (Module.Dual R M × M) := IsWellOrder.linearOrder WellOrderingRel
  choose e b he hab hep using
    fun i : Module.Dual R M × M => exists_isIdempotentElem_mul_of_forall_isMaximal hR (i.1 i.2)

  let Q : Module.Dual R M × M → R := fun l => ∏ j ∈ S with j < l, (1 - e j)
  let e' : Module.Dual R M × M → R := fun l => e l * Q l
  have hQi : ∀ l, IsIdempotentElem (Q l) := fun l =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ h1 h2 => h1.mul h2)
      IsIdempotentElem.one (fun j _ => (he j).one_sub)
  have he'i : ∀ l, IsIdempotentElem (e' l) := fun l => (he l).mul (hQi l)
  have hlt : ∀ k ∈ S, ∀ l ∈ S, k < l → e k * e' l = 0 := by
    intro k hk l _ hkl
    have hmem : k ∈ S.filter (· < l) := Finset.mem_filter.mpr ⟨hk, hkl⟩
    simp only [e', Q]
    rw [← Finset.mul_prod_erase _ _ hmem]
    linear_combination (-(e l * ∏ x ∈ (S.filter (· < l)).erase k, (1 - e x))) * (he k).eq
  have horth : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → e' k * e' l = 0 := by
    intro k hk l hl hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · have := hlt k hk l hl h
      simp only [e'] at this ⊢
      linear_combination Q k * this
    · have := hlt l hl k hk h
      simp only [e'] at this ⊢
      linear_combination Q l * this

  let x : M := ∑ k ∈ S, e' k • k.2
  let φ : Module.Dual R M := ∑ l ∈ S, (b l * e' l) • l.1
  have hφx : φ x = ∑ l ∈ S, e' l := by

    simp only [φ, x, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_eq_single l]
    · have h1 := (he'i l).eq
      have h2 := hab l
      have h3 : e' l * e l = e' l := by
        simp only [e']; linear_combination Q l * (he l).eq
      linear_combination (b l * l.1 l.2) * h1 + e' l * h2 + h3
    · intro k hk hkl
      have := horth l hl k hk (Ne.symm hkl)
      linear_combination (b k * k.1 l.2) * this
    · intro h; exact absurd hl h
  have hsum : ∑ l ∈ S, e' l = 1 - ∏ i ∈ S, (1 - e i) := by
    rw [Finset.prod_one_sub_ordered S e]; ring
  have hunit : IsUnit (1 - ∏ i ∈ S, (1 - e i)) := by
    by_contra hnu
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hnu
    obtain ⟨i, hi, him⟩ : ∃ i ∈ S, i.1 i.2 ∉ m := by
      by_contra! hall
      exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (hS ▸ Ideal.sum_mem _ hall))
    have hei := hep i m hm.isPrime him
    have h1 : 1 - e i ∈ m := by
      have : e i * (1 - e i) ∈ m := by
        rw [mul_sub, mul_one, (he i).eq, sub_self]; exact m.zero_mem
      exact (hm.isPrime.mem_or_mem this).resolve_left hei
    have hP : ∏ i ∈ S, (1 - e i) ∈ m := by
      rw [← Finset.mul_prod_erase _ _ hi]; exact m.mul_mem_right _ h1
    exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using m.add_mem hxm hP))
  rw [← hsum, ← hφx] at hunit
  exact .of_equiv <| .symm <| .ofBijective φ (Module.Invertible.bijective_of_surjective <|
    LinearMap.range_eq_top.mp <| Ideal.eq_top_of_isUnit_mem _ ⟨x, rfl⟩ hunit)

theorem pic_eq_one_of_forall_isMaximal :
    ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) →
      ∀ c : CommRing.Pic R, c = 1 := by
  intro R _ hR c
  have : Subsingleton (CommRing.Pic R) := CommRing.Pic.subsingleton_iff.mpr
    fun M _ _ hM => free_of_invertible_of_forall_isMaximal hR M hM
  exact Subsingleton.elim _ _

end GlobalTheory
end

section

namespace GlobalTheory

open Polynomial in
theorem no_order_l_of_cyclotomic_irreducible :
    ∀ (E : Type) [Field E] [CharZero E] (l N : ℕ) (g : Matrix (Fin N) (Fin N) E),
      l.Prime → Irreducible (Polynomial.cyclotomic l E) → N + 1 < l → g ^ l = 1 → g = 1 := by
  intro E _ _ l N g hl hirr hN hg
  haveI : Fact l.Prime := ⟨hl⟩
  have hmon : g.charpoly.Monic := Matrix.charpoly_monic g
  have hdeg : g.charpoly.natDegree = N := by
    simpa using Matrix.charpoly_natDegree_eq_dim g
  have hndvd : ¬ cyclotomic l E ∣ g.charpoly := by
    intro h
    have h1 := Polynomial.natDegree_le_of_dvd h hmon.ne_zero
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl, hdeg] at h1
    omega
  obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).2 hndvd
  have hev := congrArg (aeval g) hab
  simp only [map_add (f := _), map_mul, map_one, Matrix.aeval_self_charpoly, mul_zero, add_zero] at hev
  have hcyc : aeval g (cyclotomic l E) * (g - 1) = 0 := by
    have := congrArg (aeval g) (Polynomial.cyclotomic_prime_mul_X_sub_one E l)
    simp only [map_mul, map_sub, aeval_X, map_one, map_pow] at this
    rw [this, hg, sub_self]
  have : g - 1 = 0 := by
    calc g - 1 = (aeval g a * aeval g (cyclotomic l E)) * (g - 1) := by rw [hev, one_mul]
      _ = aeval g a * (aeval g (cyclotomic l E) * (g - 1)) := by rw [mul_assoc]
      _ = 0 := by rw [hcyc, mul_zero]
  exact sub_eq_zero.1 this

end GlobalTheory
end

section

namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

noncomputable def hasse (l : ℕ) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun φ := PowerSeries.mk fun n => ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ
  map_add' φ ψ := by ext n; simp [mul_add]
  map_smul' c φ := by ext n; simp [mul_left_comm]

theorem coeff_hasse (l n : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff n (hasse l φ) = ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ := by
  simp [hasse]

theorem constantCoeff_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.constantCoeff (hasse l φ) = PowerSeries.coeff l φ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_hasse]; simp

theorem coeff_one_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff 1 (hasse l φ) = ((l + 1 : ℕ) : R) * PowerSeries.coeff (l + 1) φ := by
  rw [coeff_hasse, add_comm 1 l, Nat.choose_succ_self_right]

theorem hasse_zero (φ : PowerSeries R) : hasse 0 φ = φ := by
  ext n; simp [coeff_hasse]

end GlobalTheory.PicDiv
end

section

open IsDedekindDomain

namespace GlobalTheory.InertiaDVR

theorem perfectField_residueField_maximalIdeal (R : Type) [CommRing R] [IsLocalRing R]
    [PerfectField (IsLocalRing.ResidueField R)] (p : Ideal R) [p.IsPrime] (hp : p = IsLocalRing.maximalIdeal R) :
    PerfectField p.ResidueField := by
  subst hp
  have hb := Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R)
  let e : IsLocalRing.ResidueField R ≃+* (IsLocalRing.maximalIdeal R).ResidueField :=
    RingEquiv.ofBijective _ hb
  letI : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).ResidueField :=
    e.toRingHom.toAlgebra
  have : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).ResidueField :=
    ⟨fun x => by obtain ⟨y, rfl⟩ := e.surjective x; exact isIntegral_algebraMap⟩
  exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField R)

theorem card_inertia_eq_ramificationIdx : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L]
    [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)]
    [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)),
    Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) = P.asIdeal.ramificationIdx R := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  have : IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have : FaithfulSMul R (integralClosure R L) :=
    (faithfulSMul_iff_algebraMap_injective R _).2 (fun a b h => hinj (congrArg Subtype.val h))
  have : Module.Flat R (integralClosure R L) :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have := P.isPrime
  have hp0 : P.asIdeal.under R ≠ ⊥ := Ideal.under_ne_bot R P.ne_bot
  have hpm : P.asIdeal.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal ((Ideal.IsPrime.under R P.asIdeal).isMaximal hp0)
  have : PerfectField (P.asIdeal.under R).ResidueField :=
    perfectField_residueField_maximalIdeal R _ hpm
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.asIdeal.under R) P.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.asIdeal.under R) P.asIdeal (L ≃ₐ[K] L)]

end GlobalTheory.InertiaDVR
end

section

open KaehlerDifferential
namespace GlobalTheory
theorem bertini_derivation_split : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A], ∃ (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l := by
  intro k A _ _ _ _
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A (KaehlerDifferential k A)
  refine ⟨n, fun l => (LinearMap.proj l ∘ₗ g).compDer (KaehlerDifferential.D k A), fun l => f (Pi.single l 1), ?_⟩
  intro a
  have h := LinearMap.congr_fun hfg (KaehlerDifferential.D k A a)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_lhs => rw [← h]
  conv_lhs => rw [pi_eq_sum_univ (g (KaehlerDifferential.D k A a))]

  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]
end GlobalTheory
end
