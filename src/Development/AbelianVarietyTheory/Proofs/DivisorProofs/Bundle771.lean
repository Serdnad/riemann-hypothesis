module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle738
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing Polynomial

namespace GlobalTheory.NormalStrictHens

theorem exists_mem_finset {S : Type} [CommRing S] {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)]
    [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R) (hcov : ∀ x : S, ∃ i, x ∈ R i)
    (s : Finset S) : ∃ i, ∀ x ∈ s, x ∈ R i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert x s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hcov x
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hmono hjk hj
    · exact hmono hik (hi y hy)

theorem isDomain_of_directed {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i)) : IsDomain S := by
  classical
  haveI : NoZeroDivisors S := ⟨fun {x y} hxy => by
    obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov {x, y}
    haveI := hdom k
    have hx : x ∈ R k := hk x (by simp)
    have hy : y ∈ R k := hk y (by simp)
    have h : (⟨x, hx⟩ : R k) * ⟨y, hy⟩ = 0 := Subtype.ext hxy
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)⟩
  exact NoZeroDivisors.to_isDomain S

theorem isIntegrallyClosed_of_directed {S : Type} [CommRing S] [IsDomain S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S) (hmono : Monotone R)
    (hcov : ∀ x : S, ∃ i, x ∈ R i) (hdom : ∀ i, IsDomain (R i))
    (hic : ∀ i, IsIntegrallyClosed (R i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨f, hfm, hf⟩ := hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors S) x
  obtain ⟨k, hk⟩ := exists_mem_finset R hmono hcov (insert a (insert (b : S) f.coeffs))
  haveI := hdom k
  haveI := hic k
  have ha : a ∈ R k := hk a (by simp)
  have hb : (b : S) ∈ R k := hk b (by simp)
  have hcf : (f.coeffs : Set S) ⊆ R k := fun c hc =>
    hk c (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc))
  have hgm : (f.toSubring (R k) hcf).Monic := (monic_toSubring f (R k) hcf).2 hfm
  have hgf : (f.toSubring (R k) hcf).map (R k).subtype = f := map_toSubring f (R k) hcf
  have hinj : Function.Injective ((algebraMap S (FractionRing S)).comp (R k).subtype) :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (R k) →+* FractionRing S := IsFractionRing.lift hinj
  have hφ : ∀ r : R k, φ (algebraMap (R k) (FractionRing (R k)) r) = algebraMap S (FractionRing S) r :=
    fun r => IsFractionRing.lift_algebraMap hinj r
  have hb0 : (⟨b, hb⟩ : R k) ∈ nonZeroDivisors (R k) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero b (congrArg Subtype.val h)
  have hφy : φ (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) =
      IsLocalization.mk' (FractionRing S) a b := by
    rw [IsFractionRing.lift_mk', IsFractionRing.mk'_eq_div]
    rfl
  have hcomp : φ.comp (algebraMap (R k) (FractionRing (R k))) =
      (algebraMap S (FractionRing S)).comp (R k).subtype := by
    ext r
    exact hφ r
  have hy : IsIntegral (R k) (IsLocalization.mk' (FractionRing (R k)) (⟨a, ha⟩ : R k) ⟨⟨b, hb⟩, hb0⟩) := by
    refine ⟨f.toSubring (R k) hcf, hgm, ?_⟩
    apply φ.injective
    rw [map_zero, hom_eval₂, hφy, hcomp, ← eval₂_map, hgf]
    exact hf
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (R k))).1 inferInstance hy
  refine ⟨c, ?_⟩
  rw [← hφ, hc, hφy]

end GlobalTheory.NormalStrictHens

namespace GlobalTheory


open GlobalTheory.NormalStrictHens in
theorem exists_strictlyHenselian_normal_between : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T],
    GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  intro T _ _ _ hT A _ _ _ _ _ i hi
  haveI := hi
  obtain ⟨hThens, hTac, -⟩ :=
    GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩
  haveI := hThens
  haveI := hTac
  obtain ⟨S, _, _, _, hloc, hsc, -, hmax, -, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.exists_strictHenselisation A (SeparableClosure (ResidueField A))
  haveI := hsc
  have hind : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S) :=
    GlobalTheory.StrictHensUnion.indEtale_of_directed_union A S ι Si hmono hcov fun k => by
      obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
      exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
        (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale A B q.primeCompl)
  have hsh : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation (algebraMap A S) :=
    ⟨inferInstance, hsc, hloc, hind⟩
  haveI : IsNoetherianRing S := GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt A S hind
  have hdi : ∀ k, IsDomain (Si k).toSubring ∧ IsIntegrallyClosed (Si k).toSubring := fun k => by
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi k
    obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A B q
    let e' : Localization.AtPrime q ≃+* (Si k).toSubring :=
      e.toRingEquiv.trans
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x.1, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl
          map_add' := fun _ _ => rfl }
    exact ⟨e'.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e'⟩
  have hmono' : Monotone fun k => (Si k).toSubring := fun _ _ h => hmono h
  haveI : IsDomain S := isDomain_of_directed _ hmono' hcov fun k => (hdi k).1
  have hic : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_directed _ hmono' hcov (fun k => (hdi k).1) fun k => (hdi k).2
  obtain ⟨α, hα⟩ :=
    GlobalTheory.NCyc.StrictLocLift.exists_ringHom_of_isStrictHenselisation (algebraMap A S) hsh i
  have hle : maximalIdeal S ≤ (maximalIdeal T).comap α := by
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hα]
    intro a ha
    exact map_nonunit i a ha
  refine ⟨S, inferInstance, inferInstance, inferInstance, hsc, inferInstance, hic,
    algebraMap A S, α, hα, ⟨fun s hs => ?_⟩⟩
  by_contra h
  exact (mem_maximalIdeal _).1 (hle ((mem_maximalIdeal s).2 h)) hs

end GlobalTheory
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

set_option autoImplicit false

namespace GlobalTheory.Nef.LineBound

theorem le_ordVec {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v : Place k F) (x : Fin n → F)
    (hx : x ≠ 0) (m : ℤ) (h : ∀ i, v.1 (x i) ≤ WithZero.exp (-m)) : m ≤ ordVec v x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have h0 : v.1 (x i) ≠ 0 := (Valuation.ne_zero_iff _).2 hi
  have h1 : v.1 (x i) ≤ nrm v x := Finset.le_sup (f := fun j => v.1 (x j)) (Finset.mem_univ i)
  have h2 : nrm v x ≠ 0 := fun h' => h0 (le_antisymm (h' ▸ h1) zero_le)
  have h3 : nrm v x ≤ WithZero.exp (-m) := Finset.sup_le fun j _ => h j
  have h4 := (WithZero.log_le_log h2 WithZero.exp_ne_zero).2 h3
  rw [WithZero.log_exp] at h4
  unfold ordVec
  omega

end GlobalTheory.Nef.LineBound

theorem GlobalTheory.Nef.degLine_ge_of_twist : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ (n : ℕ) (h : Place k F → Matrix (Fin n) (Fin n) F), admitted h → ∀ (v₀ : Place k F) (π : F), π ≠ 0 → ord v₀ π = 1 → ∀ (e : ℤ) (p : Fin n → F), p ≠ 0 → (∀ (v : Place k F) (i : Fin n), v.1 ((twistAt v₀ (π ^ (-e)) h v).mulVec p i) ≤ 1) → e ≤ degLine h p := by
  intro k F _ _ _ _ _ hF n h hA v₀ π hπ hord e p hp hle
  classical
  obtain ⟨-, hw⟩ := GlobalTheory.T.admissibleAdelicMatrixFamily_orders_finite k F hF n h hA
  obtain ⟨hfin, hne⟩ := hw p hp
  set d : Place k F → ℤ := fun v => ordVec v ((h v).mulVec p) with hd
  have hsupp : Function.support d ⊆ {v : Place k F | nrm v ((h v).mulVec p) ≠ 1} := fun v hv => by
    intro h1
    apply hv
    simp only [hd, ordVec, h1, WithZero.log_one, neg_zero]
  have hnn : ∀ v, v ≠ v₀ → 0 ≤ d v := fun v hv => by
    refine GlobalTheory.Nef.LineBound.le_ordVec v _ (hne v) 0 fun i => ?_
    have := hle v i
    rw [twistAt_of_ne _ _ _ _ hv] at this
    simpa using this
  have hv₀ : e ≤ d v₀ := by
    refine GlobalTheory.Nef.LineBound.le_ordVec v₀ _ (hne v₀) e fun i => ?_
    have h1 := hle v₀ i
    rw [twistAt_self, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_zpow₀] at h1
    have hπ0 : v₀.1 π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ
    have hπv : v₀.1 π = WithZero.exp (-1) := by
      rw [← WithZero.exp_log hπ0]
      congr 1
      unfold ord at hord
      omega
    rw [hπv, ← WithZero.exp_zsmul, smul_eq_mul] at h1
    set y := v₀.1 ((h v₀).mulVec p i)
    have : y = WithZero.exp (-e) * (WithZero.exp (-e * -1) * y) := by
      rw [← mul_assoc, ← WithZero.exp_add]
      ring_nf
      simp
    rw [this]
    calc WithZero.exp (-e) * (WithZero.exp (-e * -1) * y) ≤ WithZero.exp (-e) * 1 := by gcongr
      _ = WithZero.exp (-e) := mul_one _
  have hs : Function.support d ⊆ ↑(hfin.toFinset ∪ {v₀}) := fun v hv => by
    simp only [Finset.coe_union, Set.Finite.coe_toFinset, Finset.coe_singleton]
    exact Or.inl (hsupp hv)
  show e ≤ ∑ᶠ v, d v
  rw [finsum_eq_sum_of_support_subset _ hs, ← Finset.add_sum_erase _ _ (show v₀ ∈ hfin.toFinset ∪ {v₀} by simp)]
  have : 0 ≤ ∑ x ∈ (hfin.toFinset ∪ {v₀}).erase v₀, d x :=
    Finset.sum_nonneg fun v hv => hnn v (Finset.ne_of_mem_erase hv)
  omega
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens {A B : Type} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    (maximalIdeal B).comap f = maximalIdeal A := by
  ext x
  simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

open IsLocalRing Polynomial in
open scoped TensorProduct in
private lemma locPiecesEtale_localization_atPrime {R A : Type} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] :
    _root_.GlobalTheory.LocAcyc.LocPiecesEtale R (Localization.AtPrime q) := by
  unfold _root_.GlobalTheory.LocAcyc.LocPiecesEtale
  exact ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
    fun _ => ⟨(), Algebra.mem_top⟩, fun _ => ⟨A, inferInstance, inferInstance, inferInstance, q,
      inferInstance, ⟨Subalgebra.topEquiv.symm⟩⟩⟩


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.strictHenselisation_etale_over_polynomial : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S)
      (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  intro T E _ _ _ _ _ _ _ _ y _
  obtain ⟨S, _, _, _, _, hsep, hflat, -, -, hpieces⟩ := _root_.GlobalTheory.exists_strictHenselisation
    (Localization.AtPrime y) (SeparableClosure (ResidueField (Localization.AtPrime y)))
  haveI := hsep
  have hP : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Localization.AtPrime y) S := hpieces
  letI : Algebra E S :=
    ((algebraMap (Localization.AtPrime y) S).comp (algebraMap E (Localization.AtPrime y))).toAlgebra
  letI : Algebra T S := ((algebraMap E S).comp (algebraMap T E)).toAlgebra
  letI : Algebra (Polynomial T) S := ((algebraMap E S).comp (algebraMap (Polynomial T) E)).toAlgebra
  haveI : IsScalarTower E (Localization.AtPrime y) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (Polynomial T) E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T (Polynomial T) S := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E S (algebraMap T E x) =
      algebraMap E S (algebraMap (Polynomial T) E (algebraMap T (Polynomial T) x))
    exact congrArg _ (IsScalarTower.algebraMap_apply T (Polynomial T) E x)
  haveI : IsScalarTower (Polynomial T) (Localization.AtPrime y) S :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap (Localization.AtPrime y) S (algebraMap E (Localization.AtPrime y)
          (algebraMap (Polynomial T) E x)) =
        algebraMap (Localization.AtPrime y) S (algebraMap (Polynomial T) (Localization.AtPrime y) x)
      exact congrArg _ (IsScalarTower.algebraMap_apply (Polynomial T) E (Localization.AtPrime y) x).symm
  have hcomap : (maximalIdeal S).comap (algebraMap E S) = y := by
    rw [IsScalarTower.algebraMap_eq E (Localization.AtPrime y) S, ← Ideal.comap_comap,
      _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
    exact Localization.AtPrime.under_maximalIdeal ..
  haveI : Module.Flat E (Localization.AtPrime y) := IsLocalization.flat _ y.primeCompl
  haveI := hflat
  have hflatE : Module.Flat E S := Module.Flat.trans E (Localization.AtPrime y) S
  have hpiecesE : _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S :=
    _root_.GlobalTheory.indEtale_localPieces_trans E (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := E) (A := E) y) hP
  have hpiecesT : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Polynomial T) S :=
    _root_.GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := Polynomial T) (A := E) y) hP
  obtain ⟨P, _, φ, hφc, hφs⟩ := _root_.GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T S hpiecesT
  have hPy : P = y.comap (algebraMap (Polynomial T) E) := by
    haveI : IsLocalHom φ := hφs.2.2.1
    calc P = ((maximalIdeal S).comap φ).comap (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
          rw [_root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
          exact (Localization.AtPrime.under_maximalIdeal ..).symm
      _ = (maximalIdeal S).comap (algebraMap (Polynomial T) S) := by
          rw [Ideal.comap_comap, hφc]
      _ = y.comap (algebraMap (Polynomial T) E) := by
          rw [IsScalarTower.algebraMap_eq (Polynomial T) E S, ← Ideal.comap_comap, hcomap]
  subst hPy
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcomap, hflatE, hpiecesE, φ, hφc, hφs⟩

end GlobalTheory
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_baseChange_fittingDatum_retraction : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁))
      (ρ₁ : Localization.AtPrime QA₁ →+* A₁),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))
        (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β ∧
        ∀ σ : DA →+* FractionRing A₁,
          (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).comp
              (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
            (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
          ∃ σ₁ : DA₁ →+* FractionRing A₁,
            (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)).comp
                (algebraMap (Localization.AtPrime QA₁) (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))) =
              (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (exact GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits) | (intros; apply GlobalTheory.KeyOriginEnlarge.exists_baseChange_fits <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.enlarge_strictHenselisation_retract_mod : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ True) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.enlarge_retract) | (exact GlobalTheory.KeyOriginEnlarge.enlarge_retract) | (intros; apply GlobalTheory.KeyOriginEnlarge.enlarge_retract  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

theorem _root_.GlobalTheory.T.kummerCocycle_sub_chernClass_coboundary : ∀ (q : ℕ) [NeZero q] (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v) → ∀ (C : Shv ℤ) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1) (w : Cocycle (sgl C) (res ℤ (twZ q)) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → Sec.map (w.1.v 0 1 (zero_add 1)) (ev a.1 1 0 (by simp) U x) = Sec.map ((res ℤ (twZ q)).d 0 1) (Sec.map φ (unitSec v))) → CohomologyClass.mk (zcomp a w rfl) = restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  first
  | exact @GlobalTheory.EtC.KumPic.Cobd.cobd
  | exact GlobalTheory.EtC.KumPic.Cobd.cobd
  | (intros; apply GlobalTheory.EtC.KumPic.Cobd.cobd <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
  (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  first | (exact @GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (exact GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (intros; apply GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.level_vanish) | (exact GlobalTheory.EtC.GmStep.level_vanish) | (intros; apply GlobalTheory.EtC.GmStep.level_vanish  <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

theorem _root_.GlobalTheory.T.fock_action_commutes_with_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inr b)) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inr b) G) := by
  first | exact @GlobalTheory.CharPair.fockAct1_Eab_inl_inr_embR | exact GlobalTheory.CharPair.fockAct1_Eab_inl_inr_embR | (intros; apply GlobalTheory.CharPair.fockAct1_Eab_inl_inr_embR <;> assumption)
end
