module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle024
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDvrPs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle005
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
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_injective_roots_in_integral_closure {A L : Type} [CommRing A] [Field L] [Algebra A L] {n : ℕ} (p : Polynomial A)
    (hm : p.Monic) (hn : (p.map (algebraMap A L)).natDegree = n) (hsep : (p.map (algebraMap A L)).Separable)
    (hs : (p.map (algebraMap A L)).Splits) :
    ∃ al : Fin n → integralClosure A L, Function.Injective al ∧
      p.map (algebraMap A (integralClosure A L)) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
  classical
  set pL := p.map (algebraMap A L) with hpL
  have hmL : pL.Monic := hm.map _
  have hroots : pL = (pL.roots.map fun x => Polynomial.X - Polynomial.C x).prod :=
    hs.eq_prod_roots_of_monic hmL
  have hnd : pL.roots.Nodup := Polynomial.nodup_roots hsep
  set s := pL.roots.toFinset with hsdef
  have hcard : s.card = n := by
    rw [hsdef, Multiset.toFinset_card_of_nodup hnd, ← hs.natDegree_eq_card_roots, hn]
  have hint : ∀ x ∈ s, x ∈ integralClosure A L := by
    intro x hx
    rw [hsdef, Multiset.mem_toFinset, Polynomial.mem_roots hmL.ne_zero, Polynomial.IsRoot,
      hpL, Polynomial.eval_map] at hx
    exact ⟨p, hm, hx⟩
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hcard)).symm
  refine ⟨fun b => ⟨(e b : L), hint _ (e b).2⟩, ?_, ?_⟩
  · intro b b' h
    have h2 := congrArg Subtype.val h
    exact e.injective (Subtype.ext h2)
  · apply Polynomial.map_injective (integralClosure A L).val.toRingHom Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_prod]
    have h1 : ((integralClosure A L).val.toRingHom).comp (algebraMap A (integralClosure A L)) =
        algebraMap A L := by
      ext a
      rfl
    rw [h1]
    change pL = _
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hroots]
    have h3 : ∏ b : Fin n, (Polynomial.X - Polynomial.C ((e b : L))) =
        ∏ x ∈ s, (Polynomial.X - Polynomial.C x) := by
      rw [Equiv.prod_comp e (fun x : s => Polynomial.X - Polynomial.C (x : L))]
      exact Finset.prod_coe_sort s (fun x => Polynomial.X - Polynomial.C x)
    convert h3.symm using 1
    · rw [Finset.prod_eq_multiset_prod, hsdef, Multiset.toFinset_val, hnd.dedup]
    · rfl

theorem UpperTheory.V.Pa.Det.splitEx :
    ∀ (l : ℕ) [Fact l.Prime] {K : Type} [Field K] [Finite K] [CharP K l] {q n : ℕ} (P : Fin q → Polynomial (PowerSeries K)), (∀ a, (P a).Monic ∧ (P a).natDegree = n ∧ ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).Separable) → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : IsEqDVR l A') (j : PowerSeries K →+* A') (al : Fin q → Fin n → A'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ ∀ a, Function.Injective (al a) ∧ (P a).map j = ∏ b, (Polynomial.X - Polynomial.C (al a b)) := by
  intro l _ K _ _ _ q n P hP
  classical
  have hQ0 : (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => ((hP a).1.map _).ne_zero
  haveI hsepE : Algebra.IsSeparable (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) := by
    rw [← IntermediateField.isSeparable_top,
      ← (isSplittingField_iff_intermediateField.mp
        (inferInstance : Polynomial.IsSplittingField (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).2,
      IntermediateField.isSeparable_adjoin_iff_isSeparable]
    intro x hx
    have h0 := Polynomial.aeval_eq_zero_of_mem_rootSet hx
    rw [map_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨a, _, ha⟩ := h0
    exact (hP a).2.2.of_dvd (minpoly.dvd (FractionRing (PowerSeries K)) x ha)
  haveI hcA : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hfinA : Finite (IsLocalRing.ResidueField (PowerSeries K)) :=
    Finite.of_equiv K (PowerSeries.residueFieldOfPowerSeries).symm.toEquiv

  obtain ⟨hfin, _, _, hdvr, hcB, hloc, hres⟩ :=
    UpperTheory.V.AlgebraTools.integralClosure_complete_dvr (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))
  have hinjAE : Function.Injective (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
    rw [IsScalarTower.algebraMap_eq (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))]
    exact (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).injective.comp (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hj : Function.Injective (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) := by
    intro x y h
    apply hinjAE
    exact congrArg Subtype.val h
  haveI hcharA : CharP (PowerSeries K) l := charP_of_injective_ringHom (PowerSeries.C (R := K)).injective l
  haveI hcharB : CharP ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) l := charP_of_injective_ringHom hj l
  have hal : ∀ a, ∃ al : Fin n → ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), Function.Injective al ∧
      (P a).map (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
    intro a
    have hdeg : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).natDegree = n := by
      rw [(hP a).1.natDegree_map]
      exact (hP a).2.1
    have hmapE : (P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) =
        ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).map (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hsepa : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Separable := by
      rw [hmapE]
      exact (hP a).2.2.map
    have hspl : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Splits := by
      rw [hmapE]
      refine Polynomial.Splits.of_dvd (Polynomial.SplittingField.splits (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))
        (Polynomial.map_ne_zero hQ0) ?_
      exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ a))
    exact exists_injective_roots_in_integral_closure (P a) (hP a).1 hdeg hsepa hspl
  choose al hal1 hal2 using hal
  exact ⟨↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), inferInstance, inferInstance, hdvr, ⟨hcB, hres hfinA, hcharB⟩, algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), al,
    hj, hloc, RingHom.finite_algebraMap.mpr hfin, fun a => ⟨hal1 a, hal2 a⟩⟩
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem padic_hom_unique {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (hl : (l : R) = 0)
    (f g : ℤ_[l] →+* R) : f = g := by
  ext z
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 z)
  have hz : z = y * (l : ℤ_[l]) + (z.appr 1 : ℤ_[l]) := by
    rw [pow_one] at hy; rw [hy]; ring
  rw [hz]
  simp [hl]

private theorem adic_push {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (f : R →+* R')
    [IsLocalHom f] {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap f := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact map_nonunit f y hy
  exact (ha N).comp (Ideal.quotientMap _ f hle)

private theorem span_push {K K' : Type} [Field K] [Field K'] {n a : ℕ} (j : PowerSeries K →+* PowerSeries K')
    (hj : Function.Injective j) (S : Set (Matrix (Fin n) (Fin n) (PowerSeries K)))
    (h : ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ,
      (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) S) :
    ∀ Z ∈ Ev (PowerSeries K') (PowerSeries K') n a, ∃ s : ℕ,
      (PowerSeries.X : PowerSeries K') ^ s • Z ∈ Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
  have hmap : ∀ M ∈ Submodule.span (PowerSeries K) S,
      M.map j ∈ Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM => exact Submodule.subset_span ⟨M, hM, rfl⟩
    | zero => simp
    | add M N _ _ h1 h2 => rw [Matrix.map_add _ (map_add j)]; exact add_mem h1 h2
    | smul c M _ h1 =>
      have : (c • M).map j = j c • M.map j := by ext1 p q; simp
      rw [this]; exact Submodule.smul_mem _ _ h1
  have hX : j PowerSeries.X ≠ 0 := fun e => PowerSeries.X_ne_zero (hj (e.trans (map_zero j).symm))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hX (PowerSeries.X_irreducible (R := K'))
  obtain ⟨u, hu⟩ := hm.dvd
  intro Z hZ
  have key : ∀ p q : Fin n, ∃ s : ℕ, (PowerSeries.X : PowerSeries K') ^ s • Matrix.single p q (Z p q) ∈
      Submodule.span (PowerSeries K') ((fun M => M.map j) '' S) := by
    intro p q
    by_cases hpq : ((p : ℕ) < a) ↔ ((q : ℕ) < a)
    · have hE : Matrix.single p q (1 : PowerSeries K) ∈ Ev (PowerSeries K) (PowerSeries K) n a := by
        intro p' q'
        refine ⟨fun _ => trivial, fun e => ?_⟩
        rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
        rintro ⟨rfl, rfl⟩
        exact e hpq
      obtain ⟨s, hs⟩ := h _ hE
      refine ⟨m * s, ?_⟩
      have : (PowerSeries.X : PowerSeries K') ^ (m * s) • Matrix.single p q (Z p q) =
          (u ^ s * Z p q) • ((PowerSeries.X : PowerSeries K) ^ s • Matrix.single p q (1 : PowerSeries K)).map j := by
        ext1 p' q'
        rw [pow_mul, hu]
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
        split_ifs
        · simp only [mul_one, map_pow]; ring
        · simp
      rw [this]
      exact Submodule.smul_mem _ _ (hmap _ hs)
    · have : Z p q = 0 := (Submodule.mem_bot _).1 ((hZ p q).2 hpq)
      exact ⟨0, by simp [this]⟩
  choose s hs using key
  refine ⟨∑ p, ∑ q, s p q, ?_⟩
  rw [Matrix.matrix_eq_sum_single Z, Finset.smul_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  have hle : s p q ≤ ∑ p, ∑ q, s p q :=
    le_trans (Finset.single_le_sum (f := fun q => s p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q))
      (Finset.single_le_sum (f := fun p => ∑ q, s p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hle
  rw [hd, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ (hs p q)

private theorem pushCh_inj {H A B : Type} [Group H] [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Injective f) {χ χ' : H →* Aˣ} (h : pushCh f χ = pushCh f χ') : χ = χ' := by
  ext g
  exact hf (congrArg Units.val (DFunLike.congr_fun h g))

private noncomputable def pushNP {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (K' : Type) [Field K'] [Finite K']
    [Algebra ℤ_[l] K'] (j : x.A →+* PowerSeries K') (hj : Function.Injective j) [IsLocalHom j]
    (he : pushCh j (F.eps ℤ_[l] x.A) = F.eps ℤ_[l] (PowerSeries K')) : NP F n where
  K := K'
  ρ := pushRep j x.ρ
  cont p q := adic_push j (x.cont p q)
  form g := by
    have h := congrArg (fun M => M.map j) (x.form g)
    have h1 : mat (pushRep j x.ρ) g = (mat x.ρ g).map j := rfl
    have h2 : mat (pushRep j x.ρ) (F.conj g) = (mat x.ρ (F.conj g)).map j := rfl
    have h3 : ((F.eps ℤ_[l] (PowerSeries K') g ^ (1 - (n : ℤ)) : (PowerSeries K')ˣ) : PowerSeries K') =
        j ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) := by
      rw [← he]
      exact (congrArg Units.val (map_zpow (Units.map (j : x.A →* PowerSeries K')) _ _)).symm
    rw [h1, h2, h3]
    simp only [Units.val_one, mul_one, Matrix.map_mul] at h ⊢
    rw [← Matrix.transpose_map, h]
    ext1 p q
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  a := x.a
  a_pos := x.a_pos
  a_le := x.a_le
  blk g p q := ⟨fun _ => trivial, fun e => by
    have : mat x.ρ g p q = 0 := (x.blk g p q).2 e
    show j (mat x.ρ g p q) = 0
    rw [this, map_zero]⟩
  span Z hZ := by
    have := span_push j hj _ x.span Z hZ
    rwa [Set.image_image] at this
  ine u g hg := by
    show GeneralLinearGroup.map j (x.ρ g) = 1
    rw [x.ine u g hg, map_one]
  ψ v i := pushCh j (x.ψ v i)
  ψ_mu v i g hg := by
    show Units.map _ (x.ψ v i g) = 1
    rw [x.ψ_mu v i g hg, map_one]
  w v := GeneralLinearGroup.map j (x.w v)
  ty := x.ty
  w_blk v p q e := by
    show j (x.w v p q) = 0
    rw [x.w_blk v p q e, map_zero]
  tri v g := by
    have e : (GeneralLinearGroup.map j (x.w v))⁻¹ * pushRep j x.ρ (F.φ v g) * GeneralLinearGroup.map j (x.w v) =
        GeneralLinearGroup.map j ((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v) := by
      rw [map_mul, map_mul, map_inv]; rfl
    rw [e]
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · show j (((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) x.A) p q) = 0
      rw [(x.tri v g).1 p q hpq, map_zero]
    · show j (((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) x.A) p p) = j _
      rw [(x.tri v g).2 p]
  N1 v := by
    refine ⟨fun p q hpq e => (x.N1 v).1 p q hpq (pushCh_inj hj e), fun p q hpq e => (x.N1 v).2 p q hpq (pushCh_inj hj ?_)⟩
    rw [e, ← he]
    ext g
    simp

theorem UpperTheory.V.Pa.Det.extEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (A' : Type) [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [IsEqDVR l A'] (j₀ : x.A →+* A'), Function.Injective j₀ → IsLocalHom j₀ → j₀.Finite → ∃ (x' : NP F n) (j : x.A →+* x'.A) (e : x'.A ≃+* A'), x.Ext2 x' j ∧ (∀ a, e (j a) = j₀ a) ∧ Nat.card x'.K = Nat.card (ResidueField A') := by
  intro l _ F n x A' _ _ _ hA j₀ hinj hloc hfin
  haveI := hA.complete
  haveI := hA.finite
  haveI := hA.char
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A'
  obtain ⟨e, -, -⟩ := UpperTheory.V.AlgebraTools.powerSeries_equiv_of_complete_dvr A' l t ht
  letI : Algebra ℤ_[l] (ResidueField A') := ((residue A').comp (j₀.comp (algebraMap ℤ_[l] x.A))).toAlgebra
  let j : x.A →+* PowerSeries (ResidueField A') := (e.symm : A' →+* _).comp j₀
  have hj : Function.Injective j := e.symm.injective.comp hinj
  haveI hl : IsLocalHom j := ⟨fun a ha => hloc.1 a (by simpa using ha.map e)⟩
  have hjf : j.Finite := RingHom.Finite.comp (RingHom.Finite.of_surjective _ e.symm.surjective) hfin
  have h0 : (l : PowerSeries (ResidueField A')) = 0 := e.injective (by simp)
  have he : pushCh j (F.eps ℤ_[l] x.A) = F.eps ℤ_[l] (PowerSeries (ResidueField A')) := by
    have := padic_hom_unique h0 (j.comp ((algebraMap ℤ_[l] x.A).comp (algebraMap ℤ_[l] ℤ_[l])))
      ((algebraMap ℤ_[l] _).comp (algebraMap ℤ_[l] ℤ_[l]))
    unfold GFrame.eps
    rw [← this]
    rfl
  exact ⟨pushNP x (ResidueField A') j hj he, j, e, ⟨⟨hj, hl, hjf, rfl, rfl, fun _ _ => rfl⟩, fun _ => rfl, rfl⟩,
    fun a => e.apply_symm_apply _, rfl⟩
end

section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mapL {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (M.map j * Z).map p = M * Z.map p := by
  ext a b

  simp [Matrix.mul_apply, map_sum, hp]

private theorem mapR {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (Z * M.map j).map p = Z.map p * M := by
  ext a b

  simp only [Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm, hp, mul_comm]

private def ddJ {A B : Type} [CommRing A] [CommRing B] (g : ℕ) (j : A →+* B) : DD A g →+* DD B g where
  toFun d := ⟨j d.a, fun i => j (d.ep i), fun i => j (d.ep' i), j d.eta⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private def ddP {A B : Type} [CommRing A] [CommRing B] (g : ℕ) (p : B →+ A) : DD B g →+ DD A g where
  toFun d := ⟨p d.a, fun i => p (d.ep i), fun i => p (d.ep' i), p d.eta⟩
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private theorem map_additive_mem_symmetric_deformation {A B : Type} [CommRing A] [CommRing B] {g n a : ℕ} (p : B →+ A)
    (Z : Matrix (Fin n) (Fin n) (DD B g)) (hZ : Z ∈ pairedDualFirstOrderDualMatrixSpace n B B g a) : Z.map (ddP g p) ∈ pairedDualFirstOrderDualMatrixSpace n A A g a := by
  have key : ∀ (b1 b2 b3 b4 : Bool) (y : DD B g), y ∈ ddPart B B g b1 b2 b3 b4 →
      ddP g p y ∈ ddPart A A g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 y ⟨h1, h2, h3, h4⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · change p y.a = 0
      rw [h1 e, map_zero]
    · funext i
      change p (y.ep i) = 0
      rw [h2 e]; exact map_zero p
    · funext i
      change p (y.ep' i) = 0
      rw [h3 e]; exact map_zero p
    · change p y.eta = 0
      rw [h4 e, map_zero]
  exact fun r s => ⟨fun e => key _ _ _ _ _ ((hZ r s).1 e), fun e => key _ _ _ _ _ ((hZ r s).2 e)⟩

private theorem sum_dd {X ι : Type} [CommRing X] {g : ℕ} (s : Finset ι) (f : ι → DD X g) :
    ∑ i ∈ s, f i = ⟨∑ i ∈ s, (f i).a, fun j => ∑ i ∈ s, (f i).ep j, fun j => ∑ i ∈ s, (f i).ep' j,
      ∑ i ∈ s, (f i).eta⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty => ext <;> simp
  | insert i s hi ih => ext <;> simp [Finset.sum_insert hi, ih]

private theorem exJP {A B : Type} [CommRing A] [CommRing B] {g g' n a m : ℕ} (e : g' = g) (j : A →+* B)
    (b : Fin m → B) (p : Fin m → B →+ A) (hb : ∀ y, y = ∑ i, j (p i y) * b i)
    (hp : ∀ i a y, p i (j a * y) = a * p i y) :
    ∃ (J : DD A g →+* DD B g') (P : Fin m → DD B g' →+ DD A g),
      (∀ c, J (DD.C c) = DD.C (j c)) ∧
      (∀ K : Fin g → Matrix (Fin n) (Fin n) A, (DD.epM K).map J = DD.epM fun i => (K (Fin.cast e i)).map j) ∧
      (∀ i a y, P i (J a * y) = a * P i y) ∧ (∀ y, y = ∑ i, J (P i y) * DD.C (b i)) ∧
      (∀ i y, (P i y).eta = p i y.eta) ∧
      (∀ i Z, Z ∈ pairedDualFirstOrderDualMatrixSpace n B B g' a → Z.map (P i) ∈ pairedDualFirstOrderDualMatrixSpace n A A g a) ∧
      ∀ Z, Z ∈ pairedDualFirstOrderDualMatrixSpace n A A g a → Z.map J ∈ pairedDualFirstOrderDualMatrixSpace n B B g' a := by
  subst e
  refine ⟨ddJ _ j, fun i => ddP _ (p i), fun c => ?_, fun K => ?_, fun i a y => ?_, fun y => ?_, fun _ _ => rfl,
    fun i Z h => map_additive_mem_symmetric_deformation (p i) Z h, fun Z h => map_additive_mem_symmetric_deformation j.toAddMonoidHom Z h⟩
  · ext <;> simp [ddJ]
  · ext <;> simp [ddJ, DD.epM]
  · ext <;> simp [ddJ, ddP, hp]
  · rw [sum_dd]
    ext <;> simp [ddJ, ddP, ← hb]

theorem UpperTheory.V.Pa.Det.detPush :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ (k : Kap x) (k' : Kap x') (e : k'.g = k.g), (∀ i g, k'.κ i g = (k.κ (Fin.cast e i) g).map j) → ∀ S : Set F.G₀, Detects k S → Detects k' S := by
  intro l _ F n x x' j hE k k' e hκ S hD z hz hell
  obtain ⟨⟨hinj, hloc, hfin, hρ, ha, -⟩, -⟩ := hE
  obtain ⟨m, b, p, -, hb, hp, -, -, r, u, -, hu⟩ := UpperTheory.V.Pa.Det.extFree j hinj hloc hfin
  obtain ⟨J, P, JC, Jep, hP, hB, Peta, PW, JW⟩ := exJP (n := n) (a := x.a) e j b p hb hp
  have hl : (l : x'.A) = 0 := by
    haveI := (UpperTheory.V.Pa.Det.zlUniq l).1 (algebraMap ℤ_[l] x'.K)
    have := congrArg (algebraMap x'.K x'.A) (CharP.cast_eq_zero x'.K l)
    rwa [map_natCast, map_zero] at this
  have he : ∀ g, epsD k' x'.A g = J (epsD k x.A g) := by
    intro g
    have := ((UpperTheory.V.Pa.Det.zlUniq l).2 (algebraMap ℤ_[l] x'.A) (j.comp (algebraMap ℤ_[l] x.A)) hl).1
    exact (congrArg DD.C (DFunLike.congr_fun this ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]))).trans (JC _).symm
  have hr : ∀ g, k'.ρ1 x'.A g = (k.ρ1 x.A g).map J := by
    intro g
    have h1 : x'.ρX (DD x'.A k'.g) g = (x.ρX (DD x.A k.g) g).map J := by
      ext1 a c
      simp only [NP.ρX, hρ, Matrix.map_apply]
      exact (JC _).symm
    rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul, ← h1, Matrix.map_add _ (map_add J), Jep, Matrix.map_one _ (map_zero J) (map_one J)]
    simp only [hκ]
    rfl
  have h3 : (u : x'.A) * ((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) = 1 := u.mul_inv
  have hpow : ∀ N, (DD.C x'.t : DD x'.A k'.g) ^ (r * N) =
      J (DD.C x.t ^ N) * DD.C (((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) ^ N) := by
    intro N
    rw [map_pow J, JC, ← map_pow, ← map_pow, ← map_mul, hu, ← mul_pow, mul_right_comm, h3, one_mul, pow_mul]
  obtain ⟨z1, z2, z3, z4⟩ := hz
  have hsm : ∀ i (c : DD x.A k.g) (Z : Matrix (Fin n) (Fin n) (DD x'.A k'.g)), (J c • Z).map (P i) = c • Z.map (P i) := by
    intro i c Z
    ext1 a c
    exact hP _ _ _
  have hzi : ∀ i, (fun g => (z g).map (P i)) ∈ TwZ k x.A := by
    intro i
    refine ⟨fun g => PW i _ (ha ▸ z1 g), fun a c N => ?_, fun g h => ?_, fun g => ?_⟩
    · have := z2 a c (r * N)
      rw [IsLocallyConstant.iff_eventually_eq] at this ⊢
      intro g
      filter_upwards [this g] with h hh
      rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hh ⊢
      obtain ⟨w, hw⟩ := hh
      change _ = (DD.C x'.t : DD x'.A k'.g) ^ (r * N) * w at hw
      refine ⟨P i (DD.C (((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) ^ N) * w), ?_⟩
      change P i (z h a c) - P i (z g a c) = (DD.C x.t : DD x.A k.g) ^ N * _
      rw [← map_sub, hw, hpow, mul_assoc, hP]
    · simp only
      rw [z3, Matrix.map_add _ (map_add (P i)), he, hsm, hr, hr, mapR J (P i) (hP i), mapL J (P i) (hP i)]
    · simp only
      rw [z4, Matrix.map_neg _ (map_neg (P i)), he, hsm, Matrix.transpose_map]
  have hli : ∀ i, ∀ σ ∈ S, ell k x.A σ (fun g => (z g).map (P i)) = 0 := by
    intro i σ hσ
    have h0 := hell σ hσ
    simp only [ell] at h0 ⊢
    rw [← mapR J (P i) (hP i), ← hr, ← AddMonoidHom.map_trace, Peta, h0, map_zero]
  choose s Y hY hT hs using fun i => hD _ (hzi i) (hli i)
  have hle : ∀ i, s i ≤ ∑ i, s i := fun i =>
    Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  set N := ∑ i, s i with hN
  let d : Fin m → x'.A := fun i => ((u⁻¹ : (PowerSeries x'.K)ˣ) : x'.A) ^ N * b i * j (x.t ^ (N - s i))
  have key : ∀ y : DD x'.A k'.g, ∑ i, d i • J (x.t ^ s i • P i y) = x'.t ^ (r * N) • y := by
    intro y
    conv_rhs => rw [hB y, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change DD.C (d i) * J (DD.C (x.t ^ s i) * P i y) = DD.C (x'.t ^ (r * N)) * _
    have h4 : J ((DD.C x.t : DD x.A k.g) ^ N) = DD.C (j (x.t ^ (N - s i))) * J (DD.C (x.t ^ s i)) := by
      rw [← JC, ← map_mul, ← map_mul, ← pow_add, Nat.sub_add_cancel (hle i), map_pow DD.C]
    rw [map_pow DD.C x'.t, hpow, h4]
    simp only [d, map_mul]
    ring
  have hJs : ∀ (c : DD x.A k.g) (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)), (c • Z).map J = J c • Z.map J := by
    intro c Z
    ext1 a c
    exact map_mul J _ _
  refine ⟨r * N, ∑ i, d i • (Y i).map J, ?_, ?_, ?_⟩
  · exact sum_mem fun i _ => Submodule.smul_mem _ _ (ha ▸ JW _ (hY i))
  · rw [Matrix.transpose_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← hT i]
    rw [Matrix.map_neg _ (map_neg J), hJs, ← he, Matrix.transpose_smul, Matrix.transpose_map, smul_neg, smul_comm]
  · funext g
    have h5 : (x'.t ^ (r * N) • z) g = ∑ i, d i • ((x.t ^ s i • fun g => (z g).map (P i)) g).map J := by
      ext1 a c
      rw [Matrix.sum_apply]
      exact (key _).symm
    rw [h5, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i]
    simp only
    rw [Matrix.map_sub _ (map_sub J), hJs, Matrix.map_mul, Matrix.map_mul, ← he, ← hr, ← hr, smul_sub,
      Matrix.mul_smul, Matrix.smul_mul, smul_comm]
end
