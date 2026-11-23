module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.CharacterGerms.Bundle021
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle068
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem exists_isPullback_spec_of_isFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (D : CommRingCat.{0})
    (e : Spec D ⟶ Y) :
    ∃ (H : CommRingCat.{0}) (φ : D ⟶ H) (y : Spec H ⟶ X), φ.hom.Finite ∧ IsPullback y (Spec.map φ) f e := by
  have : IsAffine (pullback f e) := isAffine_of_isAffineHom (pullback.snd f e)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback f e).isoSpec.inv ≫ pullback.snd f e)
  refine ⟨_, φ, (pullback f e).isoSpec.inv ≫ pullback.fst f e, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  · rw [hφ]
    exact (IsPullback.of_hasPullback f e).of_iso (pullback f e).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

theorem eq_of_forall_nilpotent_aug {Ω O : Type} [Field Ω] [IsAlgClosed Ω] [CommRing O] [Algebra Ω O]
    [Module.Finite Ω O] {a b : O}
    (h : ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
      ∀ g : O →ₐ[Ω] A, g a = g b) : a = b := by
  have : IsArtinianRing O := IsArtinianRing.of_finite Ω O
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun q hq => ?_)
  rw [map_sub, sub_eq_zero]
  let A := Localization.AtPrime q
  let g : O →ₐ[Ω] A := IsScalarTower.toAlgHom Ω O A
  have hg : Function.Surjective g := IsArtinianRing.localization_surjective q.primeCompl A
  have : Module.Finite Ω A := Module.Finite.of_surjective g.toLinearMap hg
  have : IsArtinianRing A := IsArtinianRing.of_finite Ω A
  let r : A →ₐ[Ω] ResidueField A := IsScalarTower.toAlgHom Ω A (ResidueField A)
  have : Module.Finite Ω (ResidueField A) := Module.Finite.of_surjective r.toLinearMap residue_surjective
  let e : Ω ≃ₐ[Ω] ResidueField A :=
    AlgEquiv.ofBijective (Algebra.ofId Ω _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine h A (e.symm.toAlgHom.comp r) ?_ g
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  refine ⟨N, le_bot_iff.1 (le_trans (Ideal.pow_right_mono ?_ N) hN.le)⟩
  rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  intro t ht
  have : e.symm (r t) = 0 := ht
  exact (residue_eq_zero_iff t).1 ((map_eq_zero_iff _ e.symm.injective).1 this)

theorem cubWeil_one_of_local_artinian : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (n : ℕ), IsFinite ((𝟙 G) ^ n : G ⟶ G).left → ∀ (D : Type) [CommRing D] [Algebra Ω D] [Module.Finite Ω D] (x : overAt s D ⟶ G), x ^ n = 1 → (∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ (f : D →ₐ[Ω] A) (y : overAt s A ⟶ G), y ^ n = 1 → CubWeil c n (homAt s f ≫ x) y 1) → ∀ (T' : Over S) (ρ : T' ⟶ overAt s D) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1 := by
  intro Ω _ _ S s G _ _ L c n hfin D _ _ _ x hx h T' ρ y hy
  obtain ⟨H, φ, y₀, hφ, hpb⟩ := exists_isPullback_spec_of_isFinite ((𝟙 G) ^ n : G ⟶ G).left (CommRingCat.of D)
    (1 : overAt s D ⟶ G).left
  let : Algebra D H := φ.hom.toAlgebra
  let : Algebra Ω H := (φ.hom.comp (algebraMap Ω D)).toAlgebra
  have : IsScalarTower Ω D H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite D H := hφ
  have : Module.Finite Ω H := Module.Finite.trans D H
  let j : D →ₐ[Ω] H := IsScalarTower.toAlgHom Ω D H
  have hj : (homAt s j).left = Spec.map φ := rfl
  have hpow : ∀ {T : Over S} (z : T ⟶ G), z.left ≫ ((𝟙 G) ^ n : G ⟶ G).left = (z ^ n).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {T : Over S} (r : T ⟶ overAt s D), r.left ≫ (1 : overAt s D ⟶ G).left = (1 : T ⟶ G).left := by
    intro T r
    rw [← Over.comp_left, MonObj.comp_one]
  have hw : y₀ ≫ G.hom = (overAt s H).hom := by
    rw [← Over.w ((𝟙 G) ^ n : G ⟶ G), ← Category.assoc, hpb.w, Category.assoc, Over.w (1 : overAt s D ⟶ G)]
    exact Over.w (homAt s j)
  let u : overAt s H ⟶ G := Over.homMk y₀ hw
  have hu : u ^ n = 1 := Over.OverMorphism.ext (by rw [← hpow, ← hone (homAt s j)]; exact hpb.w)
  have hx' : (homAt s j ≫ x) ^ n = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c hx' hu
  have hζ1 : ζ = 1 := by
    refine Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of H)).hom).1 ?_)
    refine eq_of_forall_nilpotent_aug (Ω := Ω) fun A _ _ π hπ g => ?_
    have h₁ := h A π hπ (g.comp j) (homAt s g ≫ u) (by rw [← MonObj.comp_pow, hu, MonObj.comp_one])
    rw [← hom_comp, Category.assoc] at h₁
    have e : (homAt s g).left.appTop.hom ζ.val = (homAt s g).left.appTop.hom (1 : Γ((overAt s H).left, ⊤)ˣ).val :=
      (congrArg Units.val ((hζ.comp (homAt s g)).unique h₁)).trans (map_one _).symm
    have nat := fun t => congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (g : H →+* A)))
    exact (nat _).symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom e).trans (nat _))
  subst hζ1
  have hl : y.left ≫ ((𝟙 G) ^ n : G ⟶ G).left = ρ.left ≫ (1 : overAt s D ⟶ G).left := by rw [hpow, hy, hone]
  let l : T' ⟶ overAt s H := Over.homMk (hpb.lift _ _ hl) (by
    rw [← Over.w (homAt s j), hj, ← Over.w ρ]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hpb.lift_snd _ _ hl)))
  have e₁ : l ≫ homAt s j = ρ := Over.OverMorphism.ext (hpb.lift_snd _ _ hl)
  have e₂ : l ≫ u = y := Over.OverMorphism.ext (hpb.lift_fst _ _ hl)
  have := hζ.comp l
  rwa [← Category.assoc, e₁, e₂, map_one] at this

end GlobalTheory.AlphaPair
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem prod_pow_of_mul_eq_zero {A κ : Type} [CommRing A] [Fintype κ] [DecidableEq κ] (x : κ → A)
    (hx : ∀ i j, x i * x j = 0) (k : κ → ℕ) :
    ∏ i, x i ^ k i = ∏ i, (0 : A) ^ k i + ∑ i, if k = Pi.single i 1 then x i else 0 := by
  by_cases h0 : k = 0
  · subst h0
    rw [Finset.sum_eq_zero fun i _ => if_neg fun h => by simpa using congrFun h i]
    simp
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
  have hi : k i ≠ 0 := hi
  rw [Finset.prod_eq_zero (f := fun i => (0 : A) ^ k i) (Finset.mem_univ i) (zero_pow hi), zero_add,
    Finset.sum_eq_single i (fun j _ hj => if_neg fun h => hi (by rw [h]; simp [hj.symm])) (by simp)]
  split_ifs with h
  · subst h
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  · by_cases h1 : k i = 1
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
      have hji : j ≠ i := by rintro rfl; simp [h1] at hj
      have hj0 : k j ≠ 0 := by simpa [hji] using hj
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩), h1, pow_one]
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      rw [hm, pow_succ', mul_assoc (x j), ← mul_assoc (x i), hx, zero_mul]
    · refine Finset.prod_eq_zero (Finset.mem_univ i) (pow_eq_zero_of_le (m := 2) (by omega) ?_)
      rw [pow_two, hx]

theorem evalPoints_first_order_of_sq_eq_zero {R : Type} [CommRing R] {d : ℕ} (ph : PS R 3 d) {A : Type} [CommRing A] [Algebra R A]
    (e : A) (he : e ^ 2 = 0) (u : Fin d → R) (b b' : Fin d → A) (hb : ∀ j, IsNilpotent (b j))
    (hb' : ∀ j, IsNilpotent (b' j)) :
    evP ![fun j => u j • e, b, b'] ph = evP ![0, b, b'] ph + e * evP ![b, b'] (c2 ph u) := by
  have hx : ∀ i j, (u i • e) * (u j • e) = 0 := fun i j => by
    rw [smul_mul_smul_comm, ← pow_two, he, smul_zero]
  obtain ⟨N₁, -, h₁⟩ := evBasic_exists_pow b hb
  obtain ⟨N₂, -, h₂⟩ := evBasic_exists_pow b' hb'
  obtain ⟨N, hN, h₁, h₂⟩ : ∃ N, 2 ≤ N ∧ (∀ j, b j ^ N = 0) ∧ ∀ j, b' j ^ N = 0 :=
    ⟨N₁ + N₂ + 2, by omega, fun j => pow_eq_zero_of_le (by omega) (h₁ j),
      fun j => pow_eq_zero_of_le (by omega) (h₂ j)⟩
  have h3 : ∀ x : Fin d → A, (∀ j, x j ^ N = 0) →
      ∀ q : Fin 3 × Fin d, (![x, b, b'] : Fin 3 → Fin d → A) q.1 q.2 ^ N = 0 := by
    rintro x hx ⟨i, j⟩
    fin_cases i
    exacts [hx j, h₁ j, h₂ j]
  have h2 : ∀ q : Fin 2 × Fin d, (![b, b'] : Fin 2 → Fin d → A) q.1 q.2 ^ N = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [h₁ j, h₂ j]
  have hp : ∀ (x : Fin d → A) (n : Fin 3 × Fin d → ℕ),
      ∏ q : Fin 3 × Fin d, (![x, b, b'] : Fin 3 → Fin d → A) q.1 q.2 ^ n q = (∏ j, x j ^ n (0, j)) *
        ∏ q : Fin 2 × Fin d, (![b, b'] : Fin 2 → Fin d → A) q.1 q.2 ^ n (q.1.succ, q.2) := by
    intro x n
    rw [Fintype.prod_prod_type, Fin.prod_univ_succ, Fintype.prod_prod_type]
    rfl
  unfold evP
  rw [evBasic_nEval_eq_tEval _ _ N (h3 _ fun j => pow_eq_zero_of_le hN (by rw [pow_two, hx])),
    evBasic_nEval_eq_tEval _ _ N (h3 0 fun j => zero_pow (by omega)),
    evBasic_nEval_eq_tEval _ _ N h2, evBasic_tEval_eq_sum, evBasic_tEval_eq_sum, evBasic_tEval_eq_sum]
  simp only [hp, prod_pow_of_mul_eq_zero _ hx, add_mul, mul_add, Finset.sum_add_distrib, Pi.zero_apply,
    add_right_inj]
  have hc : ∀ mu, MvPowerSeries.coeff mu (c2 ph u) = ∑ i, u i * MvPowerSeries.coeff
    (mu.mapDomain (fun q : Fin 2 × Fin d => (q.1.succ, q.2)) + Finsupp.single ((0 : Fin 3), i) 1) ph :=
    fun _ => rfl

  simp only [hc, map_sum, Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, zero_mul, mul_zero]
  rw [Finset.sum_comm, Finset.sum_comm (t := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  have hinj : Function.Injective (fun q : Fin 2 × Fin d => ((q.1.succ, q.2) : Fin 3 × Fin d)) :=
    fun q q' h => by
      simp only [Prod.mk.injEq, Fin.succ_inj] at h
      exact Prod.ext h.1 h.2
  refine Finset.sum_nbij' (fun n q => n (q.1.succ, q.2))
    (fun m q => (Fin.cons (Pi.single i 1) (fun a j => m (a, j)) : Fin 3 → Fin d → ℕ) q.1 q.2) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hn ⊢
    exact fun q => hn.1 _
  · intro m hm
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hm ⊢
    refine ⟨?_, rfl⟩
    rintro ⟨a, j⟩
    refine Fin.cases ?_ (fun a => hm (a, j)) a
    simp only [Fin.cons_zero, Finset.mem_range, Pi.single_apply]
    split_ifs <;> omega
  · intro n hn
    funext ⟨a, j⟩
    exact Fin.cases (congrFun (Finset.mem_filter.1 hn).2 j).symm (fun _ => rfl) a
  · intro m _
    rfl
  · intro n hn
    have hn0 : ∀ j, n (0, j) = (Pi.single i 1 : Fin d → ℕ) j := congrFun (Finset.mem_filter.1 hn).2
    have : (Finsupp.equivFunOnFinite.symm fun q : Fin 2 × Fin d => n (q.1.succ, q.2)).mapDomain
        (fun q : Fin 2 × Fin d => ((q.1.succ, q.2) : Fin 3 × Fin d)) + Finsupp.single ((0 : Fin 3), i) 1 =
        Finsupp.equivFunOnFinite.symm n := by
      ext ⟨a, j⟩
      refine Fin.cases ?_ (fun a => ?_) a
      · rw [Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _
          (by rintro ⟨q, hq⟩; exact Fin.succ_ne_zero _ (congrArg Prod.fst hq))]
        simp [hn0, Finsupp.single_apply, Pi.single_apply, eq_comm]
      · rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective hinj _ (a, j),
          Finsupp.single_eq_of_ne (fun h => Fin.succ_ne_zero _ (congrArg Prod.fst h))]
        simp
    rw [this, map_mul, Algebra.smul_def]
    ring

theorem evalPoints_first_order_of_eq_one : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ (u : Fin d → R) (b b' : Fin d → A), (∀ j, IsNilpotent (b j)) → (∀ j, IsNilpotent (b' j)) → evP ![fun j => u j • e, b, b'] ph = 1 + e * evP ![b, b'] (c2 ph u) := by
  intro R _ d ph hph A _ _ e he u b b' hb hb'
  rw [evalPoints_first_order_of_sq_eq_zero ph e he u b b' hb hb']
  congr 1
  have hn : ∀ q : Fin 2 × Fin d, IsNilpotent ((![b, b'] : Fin 2 → Fin d → A) q.1 q.2) := by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [hb j, hb' j]
  have h := congrArg (fun f => nEval f fun q : Fin 2 × Fin d => (![b, b'] : Fin 2 → Fin d → A) q.1 q.2) hph
  beta_reduce at h
  rw [nEval_one hn, ev, ChartCompare.nEval_subst _ _ _ _ hn] at h
  · rw [← h, evP]
    congr 1
    funext ⟨i, j⟩
    fin_cases i
    · exact (ChartCompare.nEval_zero _ hn).symm
    · exact (ChartCompare.nEval_X _ hn (0, j)).symm
    · exact (ChartCompare.nEval_X _ hn (1, j)).symm
  · rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]

end GlobalTheory.AlphaPair
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem nEval_cvAt {Ω A : Type} [Field Ω] [CommRing A] [Algebra Ω A] (s : MvPowerSeries (Fin 2) Ω)
    (hs : MvPowerSeries.constantCoeff s = 0) (f : PowerSeries Ω) (v : Fin 2 → A) (hv : ∀ i, IsNilpotent (v i)) :
    nEval (cvAt s f) v = nEval (σ := Unit) f (fun _ => nEval s v) :=
  ChartCompare.nEval_subst (σ := Unit) (fun _ => s) (fun _ => hs) f v hv

theorem formalAdd_cv_of_addMod :
    ∀ (Ω : Type) [Field Ω] (p d : ℕ) (F : Fin d → PS Ω 2 d) (ga : Fin d → PowerSeries Ω), (∀ j, PowerSeries.constantCoeff (ga j) = 0) → AddMod p F ga → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → addP F (cv ga a) (cv ga a') = cv ga (a + a') := by
  intro Ω _ p d F ga h0 hadd A _ _ a a' ha ha'
  funext i
  have hp : ∀ k : Fin 2, (![a, a'] : Fin 2 → A) k ^ p = 0 := fun k => by
    fin_cases k
    · exact ha
    · exact ha'
  have hv : ∀ k : Fin 2, IsNilpotent ((![a, a'] : Fin 2 → A) k) := fun k => ⟨p, hp k⟩
  have hz : nEval (MvPowerSeries.subst (fun q : Fin 2 × Fin d => cvAt (MvPowerSeries.X q.1) (ga q.2)) (F i) -
      cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (ga i)) (![a, a'] : Fin 2 → A) = 0 := by
    rw [evBasic_nEval_eq_tEval _ _ p hp, evBasic_tEval_eq_sum]
    refine Finset.sum_eq_zero fun e he => ?_
    rw [Fintype.mem_piFinset] at he
    rw [hadd i _ (Finset.mem_range.1 (he 0)) (Finset.mem_range.1 (he 1)), map_zero, zero_mul]
  have hc : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) Ω) (ga q.2)) = 0 := fun q =>
    MvPowerSeries.constantCoeff_subst_eq_zero (a := fun _ : Unit => (MvPowerSeries.X q.1 : MvPowerSeries (Fin 2) Ω))
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _)
      (fun _ => MvPowerSeries.constantCoeff_X _) (h0 q.2)
  rw [nEval_sub hv, sub_eq_zero, ChartCompare.nEval_subst _ hc _ _ hv, nEval_cvAt _ (by simp) _ _ hv,
    nEval_add hv, ChartCompare.nEval_X _ hv, ChartCompare.nEval_X _ hv] at hz
  refine Eq.trans ?_ hz
  unfold addP evP
  congr 1
  funext q
  rw [nEval_cvAt _ (MvPowerSeries.constantCoeff_X _) _ _ hv, ChartCompare.nEval_X _ hv]
  obtain ⟨k, j⟩ := q
  fin_cases k <;> rfl

end GlobalTheory.AlphaPair
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AlphaPair

section TwoAxes

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}

theorem axes_monomial_sub_mem (I : Ideal A) (a : Fin d → A) (ha : ∀ j, a j ∈ I) (m : Fin d → ℕ) :
    (∏ j, a j ^ m j) - ∏ j, (0 : A) ^ m j ∈ I := by
  rw [← Ideal.Quotient.eq]
  simp only [map_prod, map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (ha _), map_zero]

theorem axes_mul_eq_zero {e x y : A} (he : e ^ 2 = 0) (hx : x ∈ Ideal.span {e}) (hy : y ∈ Ideal.span {e}) :
    x * y = 0 := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  linear_combination (u * v) * he

theorem evalPoints_second_difference (f : PS R 3 d) {e : A} (he : e ^ 2 = 0) (a a' b : Fin d → A)
    (ha : ∀ j, a j ∈ Ideal.span {e}) (ha' : ∀ j, a' j ∈ Ideal.span {e}) (hb : ∀ j, IsNilpotent (b j)) :
    evP ![a, a', b] f + evP ![0, 0, b] f = evP ![0, a', b] f + evP ![a, 0, b] f := by
  obtain ⟨N, hN0, hN⟩ := evBasic_exists_pow b hb
  have sq : ∀ x ∈ Ideal.span {e}, x ^ (N + 2) = 0 := fun x hx => by
    rw [pow_add, sq, axes_mul_eq_zero he hx hx, mul_zero]
  have key : ∀ c c' : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → (∀ j, c' j ∈ Ideal.span {e}) →
      evP ![c, c', b] f = ReciprocityTheory.PGsh.Be2.tEval (N + 2) f
        (fun q : Fin 3 × Fin d => ![c, c', b] q.1 q.2) := fun c c' hc hc' => by
    refine evBasic_nEval_eq_tEval f _ (N + 2) ?_
    rintro ⟨i, j⟩
    fin_cases i
    · exact sq _ (hc j)
    · exact sq _ (hc' j)
    · show b j ^ (N + 2) = 0
      rw [pow_add, hN, zero_mul]
  have h0 : ∀ j, (0 : Fin d → A) j ∈ Ideal.span {e} := fun _ => Ideal.zero_mem _
  rw [key a a' ha ha', key 0 0 h0 h0, key 0 a' h0 ha', key a 0 ha h0]
  unfold ReciprocityTheory.PGsh.Be2.tEval
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Fintype.prod_prod_type, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply]
  have h := axes_mul_eq_zero he (axes_monomial_sub_mem _ a ha fun j => m (0, j))
    (axes_monomial_sub_mem _ a' ha' fun j => m (1, j))
  rw [← mul_add, ← mul_add]
  congr 1
  linear_combination (∏ j, b j ^ (m (2, j) : ℕ)) * h

theorem evalPoints_eval_axis {u v : Fin d → PS R 2 d} {f : PS R 3 d}
    (hu : ∀ j, MvPowerSeries.constantCoeff (u j) = 0) (hv : ∀ j, MvPowerSeries.constantCoeff (v j) = 0)
    (h : ev (n := 2) ![u, v, pt R d 1] f = 1) (c b : Fin d → A)
    (hc : ∀ j, IsNilpotent (c j)) (hb : ∀ j, IsNilpotent (b j)) (x y : Fin d → A)
    (hx : ∀ j, evP ![c, b] (u j) = x j) (hy : ∀ j, evP ![c, b] (v j) = y j) :
    evP ![x, y, b] f = 1 := by
  have hn : ∀ q : Fin 2 × Fin d, IsNilpotent (![c, b] q.1 q.2) := by
    rintro ⟨i, j⟩
    fin_cases i
    · exact hc j
    · exact hb j
  have h1 := congrArg (evP ![c, b]) h
  unfold evP ev at h1
  rw [nEval_one hn, ChartCompare.nEval_subst _ _ _ _ hn] at h1
  · rw [← h1]
    unfold evP
    congr 1
    funext ⟨i, j⟩
    fin_cases i
    · exact (hx j).symm
    · exact (hy j).symm
    · exact (ChartCompare.nEval_X (R₀ := R) _ hn ((1 : Fin 2), j)).symm
  · rintro ⟨i, j⟩
    fin_cases i
    · exact hu j
    · exact hv j
    · exact MvPowerSeries.constantCoeff_X _

end TwoAxes

theorem evalPoints_eq_one_of_two_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ a a' b : Fin d → A, (∀ j, a j ∈ Ideal.span {e}) → (∀ j, a' j ∈ Ideal.span {e}) → (∀ j, IsNilpotent (b j)) → evP ![a, a', b] ph = 1 := by
  intro R _ d ph h₁ h₂ A _ _ e he a a' b ha ha' hb
  have nil : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → ∀ j, IsNilpotent (c j) := fun c hc j =>
    ⟨2, by rw [sq, axes_mul_eq_zero he (hc j) (hc j)]⟩
  have hn : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) →
      ∀ q : Fin 2 × Fin d, IsNilpotent (![c, b] q.1 q.2) := by
    rintro c hc ⟨i, j⟩
    fin_cases i
    · exact nil c hc j
    · exact hb j
  have e₁ : ∀ c : Fin d → A, (∀ j, c j ∈ Ideal.span {e}) → evP ![0, c, b] ph = 1 := fun c hc =>
    evalPoints_eval_axis (fun _ => map_zero _) (fun _ => MvPowerSeries.constantCoeff_X _) h₁ c b (nil c hc) hb 0 c
      (fun _ => ChartCompare.nEval_zero _ (hn c hc))
      (fun j => ChartCompare.nEval_X (R₀ := R) _ (hn c hc) ((0 : Fin 2), j))
  have e₂ : evP ![a, 0, b] ph = 1 :=
    evalPoints_eval_axis (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => map_zero _) h₂ a b (nil a ha) hb a 0
      (fun j => ChartCompare.nEval_X (R₀ := R) _ (hn a ha) ((0 : Fin 2), j))
      (fun _ => ChartCompare.nEval_zero _ (hn a ha))
  have h := evalPoints_second_difference ph he a a' b ha ha' hb
  rw [e₁ a' ha', e₂, e₁ 0 fun _ => Ideal.zero_mem _] at h
  exact add_right_cancel h

end GlobalTheory.AlphaPair
end
end

section

open Formalism.L2.FormalSeriesBounds

theorem _root_.GlobalTheory.T.oddLevelBlock_bound_attained : BiSupply ∧ RF.BiSupply := by
  first | exact @GlobalTheory.oddBlock_supply | exact GlobalTheory.oddBlock_supply | (intros; apply GlobalTheory.oddBlock_supply <;> assumption)
end
