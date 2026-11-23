module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle032
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RepresentationTheory.Invariants
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle035
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle034
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004

@[expose] public section

section

open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem sum_alt_card_subElem_ge : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (n : ℕ)
    (L M : Lat O K r), 1 ≤ n → M ∈ subIdx n L →
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) *
      (({M' | M' ∈ subElem k L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) = 0 := by
  intro O K _ _ _ _ _ _ _ r n L M hn hM
  classical
  set m := IsLocalRing.maximalIdeal O with hm
  set A : Submodule O (Fin r → K) := M.1 ⊔ m • L.1 with hA
  have hML : M.1 ≤ L.1 := hM.1
  have hAL : A ≤ L.1 := sup_le hML Submodule.smul_le_right
  set P : Submodule O L.1 := A.comap L.1.subtype with hP
  have hPA : P.map L.1.subtype = A := by rw [Submodule.map_comap_subtype, inf_eq_right.2 hAL]
  have htor : Module.IsTorsionBySet O (L.1 ⧸ P) (m : Set O) := by
    intro x a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact Submodule.mem_sup_right (Submodule.smul_mem_smul a.2 y.2)
  letI : Module (IsLocalRing.ResidueField O) (L.1 ⧸ P) := htor.module
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (L.1 ⧸ P) := htor.isScalarTower
  have hq2 : 2 ≤ qRes O := two_le_qRes
  have hqn : 0 < qRes O ^ n := pow_pos (by omega) _
  have hcardV : Nat.card (L.1 ⧸ P) = A.toAddSubgroup.relIndex L.1.toAddSubgroup := rfl
  have hmul := AddSubgroup.relIndex_mul_relIndex M.1.toAddSubgroup A.toAddSubgroup L.1.toAddSubgroup
    ((Submodule.toAddSubgroup_le _ _).2 le_sup_left) ((Submodule.toAddSubgroup_le _ _).2 hAL)
  have hdvd : Nat.card (L.1 ⧸ P) ∣ qRes O ^ n := ⟨M.1.toAddSubgroup.relIndex A.toAddSubgroup, by
    rw [hcardV, mul_comm, hmul, hM.2]⟩
  haveI : Finite (L.1 ⧸ P) := Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos hdvd hqn).ne'
  haveI : FiniteDimensional (IsLocalRing.ResidueField O) (L.1 ⧸ P) := Module.Finite.of_finite
  set d := Module.finrank (IsLocalRing.ResidueField O) (L.1 ⧸ P) with hd
  have hcardq : Nat.card (L.1 ⧸ P) = qRes O ^ d :=
    Module.natCard_eq_pow_finrank (K := IsLocalRing.ResidueField O)
  have hdn : d ≤ n := (Nat.pow_dvd_pow_iff_le_right (by omega)).1 (hcardq ▸ hdvd)
  have hd1 : 1 ≤ d := by
    by_contra h0
    have h0' : d = 0 := by omega
    have h1 : A.toAddSubgroup.relIndex L.1.toAddSubgroup = 1 := by
      rw [← hcardV, hcardq, h0', pow_zero]
    have h2 : L.1 ≤ M.1 ⊔ m • L.1 := (Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 h1)
    have h3 : L.1 ≤ M.1 := Submodule.le_of_le_smul_of_le_jacobson_bot L.2.fg
      (by rw [hm, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) h2
    have h4 : M.1.toAddSubgroup.relIndex L.1.toAddSubgroup = 1 :=
      AddSubgroup.relIndex_eq_one.2 ((Submodule.toAddSubgroup_le _ _).2 h3)
    rw [hM.2] at h4
    have := Nat.one_lt_pow (by omega : n ≠ 0) (by omega : 1 < qRes O)
    omega

  set k := IsLocalRing.ResidueField O
  set V := L.1 ⧸ P
  have hdV : Module.finrank k V = d := rfl
  let Φ : Submodule k V → Submodule O (Fin r → K) := fun W =>
    ((W.restrictScalars O).comap P.mkQ).map L.1.subtype
  have hPC : ∀ W : Submodule k V, P ≤ (W.restrictScalars O).comap P.mkQ := fun W x hx => by
    rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hx]
    exact zero_mem _
  have hΦA : ∀ W, A ≤ Φ W := fun W => hPA ▸ Submodule.map_mono (hPC W)
  have hΦL : ∀ W, Φ W ≤ L.1 := fun W => Submodule.map_subtype_le _ _
  have hlat : ∀ W, (Φ W).IsFullLattice K := fun W => by
    haveI := (maxMul L).2
    exact Submodule.IsLattice.of_le_of_isLattice_of_fg K
      (show (maxMul L).1 ≤ Φ W from le_trans le_sup_right (hΦA W)) (L.2.fg.of_le (hΦL W))
  let f : Submodule k V → Lat O K r := fun W => ⟨Φ W, hlat W⟩
  have hinj : Function.Injective f := by
    intro W W' h
    have h1 : Φ W = Φ W' := congrArg Subtype.val h
    have h2 := Submodule.map_injective_of_injective L.1.injective_subtype h1
    have h3 := Submodule.comap_injective_of_surjective (Submodule.mkQ_surjective P) h2
    exact Submodule.restrictScalars_injective O k V h3
  have hidx : ∀ W : Submodule k V,
      (Φ W).toAddSubgroup.relIndex L.1.toAddSubgroup = qRes O ^ Module.finrank k (V ⧸ W) := by
    intro W
    change Nat.card (L.1 ⧸ (Φ W).comap L.1.subtype) = _
    rw [Submodule.comap_map_eq_of_injective L.1.injective_subtype,
      ← Nat.card_congr (Submodule.quotientQuotientEquivQuotient P _ (hPC W)).toEquiv,
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective P),
      Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv O W).toEquiv,
      Module.natCard_eq_pow_finrank (K := k)]
    rfl
  have hset : ∀ j, ({M' | M' ∈ subElem j L ∧ M.1 ≤ M'.1} : Set (Lat O K r)) =
      f '' {W | Module.finrank k (V ⧸ W) = j} := by
    intro j
    ext M'
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨⟨hle, hi⟩, hmL⟩, hMM⟩
      set C := M'.1.comap L.1.subtype
      have hPC' : P ≤ C := Submodule.comap_mono (sup_le hMM hmL)
      let Wk : Submodule k V :=
        { (C.map P.mkQ).toAddSubmonoid with
          smul_mem' := fun c x hx => by
            obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
            have e : (IsLocalRing.residue O a) • x = a • x := htor.mk_smul a x
            rw [e]
            exact (C.map P.mkQ).smul_mem a hx }
      have hWr : Wk.restrictScalars O = C.map P.mkQ := rfl
      have heq : Φ Wk = M'.1 := by
        change ((Wk.restrictScalars O).comap P.mkQ).map L.1.subtype = M'.1
        rw [hWr, Submodule.comap_map_mkQ, sup_eq_right.2 hPC', Submodule.map_comap_subtype,
          inf_eq_right.2 hle]
      refine ⟨Wk, ?_, Subtype.ext heq⟩
      have h := hidx Wk
      rw [heq, hi] at h
      exact (Nat.pow_right_injective hq2 h).symm
    · rintro ⟨W, hW, rfl⟩
      exact ⟨⟨⟨hΦL W, (hidx W).trans (by rw [hW])⟩, le_trans le_sup_right (hΦA W)⟩,
        le_trans le_sup_left (hΦA W)⟩
  have hcount : ∀ j, (({M' | M' ∈ subElem j L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) =
      (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) := by
    intro j
    rw [hset j, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
    rfl
  have hI := GlobalTheory.T.qBinomial_sum_card_quotient_subspaces k V 1
  rw [Finset.prod_eq_zero (Finset.mem_range.2 (by rw [hdV]; omega : 0 < Module.finrank k V)) (by simp)] at hI
  have hqk : (Nat.card k : ℂ) = (qRes O : ℂ) := rfl
  simp only [one_pow, mul_one, hqk, hdV] at hI
  have hzero : ∀ x ∈ Finset.range (n + 1), x ∉ Finset.range (d + 1) →
      (-1 : ℂ) ^ x * (qRes O : ℂ) ^ (x * (x - 1) / 2) *
        (({M' | M' ∈ subElem x L ∧ M.1 ≤ M'.1} : Set (Lat O K r)).ncard : ℂ) = 0 := by
    intro x _ hx
    rw [Finset.mem_range] at hx
    haveI : IsEmpty {W : Submodule k V // Module.finrank k (V ⧸ W) = x} :=
      ⟨fun ⟨W, hW⟩ => by have := Submodule.finrank_quotient_le W; rw [hdV] at this; omega⟩
    rw [hcount, Nat.card_of_isEmpty]
    simp
  rw [← Finset.sum_subset (fun x hx => Finset.mem_range.2 (by have := Finset.mem_range.1 hx; omega)) hzero]
  simp only [hcount]
  exact hI

end GlobalTheory.LatHecke
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splits_of_splits_pullback_snd {Z X S V : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) (v : V ⟶ S) :
    GlobalTheory.EtC.Tr.Splits (pullback.snd f x) v → GlobalTheory.EtC.Tr.Splits f (v ≫ x) := by
  rintro ⟨m, s, hs, hiso⟩
  refine ⟨m, fun j => s j ≫ pullback.fst f x, fun j => ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs j]
  · have heq : (Sigma.desc (fun j => pullback.lift (s j ≫ pullback.fst f x) (𝟙 V)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, hs j, Category.id_comp])) :
          ∐ (fun _ : Fin m => V) ⟶ pullback f (v ≫ x)) =
        (Sigma.desc (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])) :
          ∐ (fun _ : Fin m => V) ⟶ pullback (pullback.snd f x) v) ≫
          (pullbackLeftPullbackSndIso f x v).hom := by
      apply Sigma.hom_ext
      intro j
      rw [Sigma.ι_desc, Sigma.ι_desc_assoc]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc]
      · rw [pullback.lift_snd, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd]
    rw [heq]
    infer_instance

end GlobalTheory.EtC.Tr
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr.SumEq

end GlobalTheory.EtC.Tr.SumEq

namespace GlobalTheory.EtC.Tr

open CategoryTheory Limits AlgebraicGeometry in
private lemma exists_sigma_ι_apply_eq_of_finite_coprod {σ : Type} [Finite σ] (g : σ → Scheme.{0}) (q : ↥(∐ g)) :
    ∃ k a, (Sigma.ι g k) a = q :=
  (sigmaOpenCover g).exists_eq q

open CategoryTheory Limits AlgebraicGeometry in
private lemma exists_pullback_lift_apply_eq_of_isIso_sigmaDesc {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    (p : ↥(pullback f y)) : ∃ k a, pullback.lift (s k) (𝟙 V) (by simp [hc k]) a = p := by
  obtain ⟨q, rfl⟩ := Scheme.Hom.surjective
    (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) p
  obtain ⟨k, a, rfl⟩ := exists_sigma_ι_apply_eq_of_finite_coprod _ q
  exact ⟨k, a, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩

open CategoryTheory Limits AlgebraicGeometry in
private lemma isOpenImmersion_pullback_lift_of_isIso_sigmaDesc {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)] (k : Fin m) :
    IsOpenImmersion (pullback.lift (s k) (𝟙 V) (by simp [hc k]) : V ⟶ pullback f y) := by
  rw [← Sigma.ι_desc (fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
    (j : Fin m) → V ⟶ pullback f y) k]
  infer_instance

open CategoryTheory Limits AlgebraicGeometry in
private lemma pullback_snd_lift_id_apply {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} (t : V ⟶ Z)
    (h : t ≫ f = 𝟙 V ≫ y) (a : ↥V) : pullback.snd f y (pullback.lift t (𝟙 V) h a) = a := by
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

open CategoryTheory Limits AlgebraicGeometry in
private lemma index_eq_of_pullback_lift_apply_eq {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    {j j' : Fin m} (a b : ↥V)
    (h : (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) a =
      (pullback.lift (s j') (𝟙 V) (by simp [hc j']) : V ⟶ pullback f y) b) :
    j = j' := by
  have h1 : (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) (Sigma.ι (fun _ : Fin m => V) j a) =
      (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) (Sigma.ι (fun _ : Fin m => V) j' b) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Sigma.ι_desc]
    exact h
  have h2 : (Sigma.ι (fun _ : Fin m => V) j) a = (Sigma.ι (fun _ : Fin m => V) j') b :=
    Scheme.Hom.injective _ h1
  exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => V) j j' a b).mp (by convert h2))

open CategoryTheory Limits AlgebraicGeometry in
private lemma injective_of_pullback_lift_apply_eq_of_isIso {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m m' : ℕ}
    {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y) (hc' : ∀ j, s' j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    (x : ↥V) (K : Fin m → Fin m') (A : Fin m → ↥V)
    (hKA : ∀ j, (pullback.lift (s' (K j)) (𝟙 V) (by simp [hc' (K j)]) : V ⟶ pullback f y) (A j) =
      (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) x) : Function.Injective K := by
  intro j j' hjj
  have hA : ∀ i, A i = x := fun i => by
    have := congrArg (pullback.snd f y) (hKA i)
    rwa [pullback_snd_lift_id_apply, pullback_snd_lift_id_apply] at this
  refine index_eq_of_pullback_lift_apply_eq hc x x ?_
  rw [← hKA j, ← hKA j', hA, hA]
  have key : ∀ k k' : Fin m', k = k' →
      (pullback.lift (s' k) (𝟙 V) (by simp [hc' k]) : V ⟶ pullback f y) x =
      (pullback.lift (s' k') (𝟙 V) (by simp [hc' k']) : V ⟶ pullback f y) x := by
    rintro k _ rfl
    rfl
  exact key _ _ hjj


open CategoryTheory Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings : ∀ (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X}
    {m m' : ℕ} {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)}, _root_.GlobalTheory.EtC.Tr.SplitBy f y s → _root_.GlobalTheory.EtC.Tr.SplitBy f y s' →
    ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s j)) = ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s' j)) := by
  intro R _ Z X V f y m m' s s' hs hs'
  obtain ⟨hc, hi⟩ := hs
  obtain ⟨hc', hi'⟩ := hs'
  let T : Sieve V :=
    { arrows := fun W v => (_root_.GlobalTheory.EtC.free R).map (yoneda.map v) ≫
          ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s j)) =
        (_root_.GlobalTheory.EtC.free R).map (yoneda.map v) ≫
          ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s' j))
      downward_closed := by
        intro W W' v hv g
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hv] }
  refine _root_.GlobalTheory.EtC.Tr.free_hom_ext_of_covering R (_root_.GlobalTheory.EtC.Tr.freeSch R Z) _ _ T ?_ (fun W v hv => hv)
  apply Scheme.zariskiTopology_le_etaleTopology
  choose K A hKA using fun (x : ↥V) (j : Fin m) =>
    exists_pullback_lift_apply_eq_of_isIso_sigmaDesc hc' ((pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) x)
  choose K' A' hKA' using fun (x : ↥V) (k : Fin m') =>
    exists_pullback_lift_apply_eq_of_isIso_sigmaDesc hc ((pullback.lift (s' k) (𝟙 V) (by simp [hc' k]) : V ⟶ pullback f y) x)
  have hopen := isOpenImmersion_pullback_lift_of_isIso_sigmaDesc hc'
  let U : ↥V → V.Opens := fun x =>
    ⟨⋂ j, (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) ⁻¹'
        Set.range (pullback.lift (s' (K x j)) (𝟙 V) (by simp [hc' (K x j)]) : V ⟶ pullback f y),
      isOpen_iInter_of_finite fun j =>
        (Scheme.Hom.isOpenEmbedding _).isOpen_range.preimage (Scheme.Hom.continuous _)⟩
  have hxU : ∀ x, x ∈ U x := fun x => Set.mem_iInter.mpr fun j => ⟨A x j, hKA x j⟩
  have hagree : ∀ x, T ((U x).ι) := by
    intro x
    have hinj := injective_of_pullback_lift_apply_eq_of_isIso hc hc' x (K x) (A x) (hKA x)
    have hinj' := injective_of_pullback_lift_apply_eq_of_isIso hc' hc x (K' x) (A' x) (hKA' x)
    have hbij : Function.Bijective (K x) := (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) (Fintype.card_le_of_injective _ hinj')⟩
    have hsec : ∀ j, (U x).ι ≫ s j = (U x).ι ≫ s' (K x j) := by
      intro j
      have hr : Set.range ⇑((U x).ι ≫ (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y)) ⊆
          Set.range (pullback.lift (s' (K x j)) (𝟙 V) (by simp [hc' (K x j)]) : V ⟶ pullback f y) := by
        rintro _ ⟨w, rfl⟩
        have hw : (U x).ι w ∈ U x := by
          have hw' : (U x).ι w ∈ Set.range (U x).ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at hw'
        rw [Scheme.Hom.comp_apply]
        exact Set.mem_iInter.mp hw j
      have hg := IsOpenImmersion.lift_fac _ _ hr
      have hgι : IsOpenImmersion.lift _ _ hr = (U x).ι := by
        have := congrArg (· ≫ pullback.snd f y) hg
        simp only [Category.assoc, pullback.lift_snd, Category.comp_id] at this
        exact this
      rw [hgι] at hg
      have := congrArg (· ≫ pullback.fst f y) hg
      simp only [Category.assoc, pullback.lift_fst] at this
      exact this.symm
    show (_root_.GlobalTheory.EtC.free R).map (yoneda.map (U x).ι) ≫ _ =
      (_root_.GlobalTheory.EtC.free R).map (yoneda.map (U x).ι) ≫ _
    rw [Preadditive.comp_sum, Preadditive.comp_sum]
    refine Fintype.sum_equiv (Equiv.ofBijective _ hbij) _ _ fun j => ?_
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      Equiv.ofBijective_apply, hsec j]
  rw [show Scheme.zariskiTopology = Scheme.grothendieckTopology @IsOpenImmersion from rfl,
    Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers V (fun x => (U x : Scheme.{0})) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hxU x⟩, rfl⟩), ?_⟩
  rintro W _ ⟨x⟩
  exact hagree x

end GlobalTheory.EtC.Tr
end

section

open GlobalTheory GlobalTheory.CMCurves

namespace GlobalTheory.ThLoc

theorem cm1 : Formalism.L2.Th1.CM.JInvariantIntegrality := by
  intro d L _ hd hL
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [Formalism.L2.Th1.CM.jInv, g₂_cube_div_eq_modularJ ha h]
  refine isIntegral_modularJ_of_mul_mem (α := Formalism.L2.Th1.CM.omegaK d) (fun m hm => ?_) fun x hx ↦ ?_
  · have := congrArg Complex.im hm
    have h0 : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    simp [Formalism.L2.Th1.CM.omegaK] at this
    omega
  · have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
      rw [h, Submodule.mem_span_pair]
      simp [mul_right_inj' ha]
    rw [key] at hx ⊢
    simpa [mul_left_comm] using hL _ hx

end GlobalTheory.ThLoc
end

section


theorem _root_.GlobalTheory.T.phaseCondition_sub_integral_matrix : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) →
    Valued.v δ = 1 → σ δ = -δ → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    ∀ x l : Matrix (Fin n') (Fin n) L, (∀ i j, l i j ∈ Formalism.UG.intL L) →
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (x - l)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))) + σ (δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))))) / 2) = 1) := by
  first | exact @GlobalTheory.Hk3.ShiftPhase.shift | exact GlobalTheory.Hk3.ShiftPhase.shift | (intros; apply GlobalTheory.Hk3.ShiftPhase.shift <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.smithNormalForm_discreteValuationField : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (M : Matrix (Fin m) (Fin n) L),
    ∃ (P P' : Matrix (Fin m) (Fin m) L) (Q Q' : Matrix (Fin n) (Fin n) L) (d : Fin m → L),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧ Q * Q' = 1 ∧
      M = P * Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) * Q := by
  first | exact @GlobalTheory.SmithValued.smith_valued | exact GlobalTheory.SmithValued.smith_valued | (intros; apply GlobalTheory.SmithValued.smith_valued <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.integral_preimage_add_image_eq_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (y : Matrix (Fin n) (Fin n') L),
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + y *ᵥ w) ↔
        ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  first | exact @GlobalTheory.Hk3.HoweG.latA_basis | exact GlobalTheory.Hk3.HoweG.latA_basis | (intros; apply GlobalTheory.Hk3.HoweG.latA_basis <;> assumption)
end

section

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

theorem _root_.GlobalTheory.T.length_integral_cocycles_rational_coboundaries_le : ∀ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (Z : Submodule O (G → V)), (∀ c ∈ Z, ∀ g, c g ∈ L.T) → Module.length O (↥(Z ⊓ (B1 ρ).restrictScalars O) ⧸ (latticeCoboundaries L).comap (Z ⊓ (B1 ρ).restrictScalars O).subtype) ≤ Module.length O ↥(Representation.invariants (repD L)) := by
  first | exact @GlobalTheory.cocycle_bound_length_le | exact GlobalTheory.cocycle_bound_length_le | (intros; apply GlobalTheory.cocycle_bound_length_le <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by
  first | exact @GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X | exact GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X | (intros; apply GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℂ) [Smooth s] (U : Z.Opens), IsAffineOpen U → genericPoint Z ∈ U → IsIntegrallyClosed Γ(Z, U) := by
  first | (exact @GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (exact GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex) | (intros; apply GlobalTheory.isIntegrallyClosed_sections_of_smooth_complex  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.endomorphismFamily_direct_summand_cancellation : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V'] [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V) (b : ι → Module.End k V') (c : ι → Module.End k U), (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) → ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by
  first | exact @GlobalTheory.endFamily_cancel | exact GlobalTheory.endFamily_cancel | (intros; apply GlobalTheory.endFamily_cancel <;> assumption)
end
