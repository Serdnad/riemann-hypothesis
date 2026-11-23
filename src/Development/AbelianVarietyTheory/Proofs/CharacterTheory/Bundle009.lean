module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem psi_of_finrank_eq_zero {F : Type} [Field F] (s : F[X] → ℂ) (hs : IsAdditive s)
    (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V)
    (h : Module.finrank F V = 0) : psi s V g = 0 := by
  have hsub : Subsingleton V := Module.finrank_zero_iff.mp h
  have h1 : LinearMap.charpoly g = 1 := by
    apply (LinearMap.charpoly_monic g).natDegree_eq_zero.mp
    rw [LinearMap.charpoly_natDegree, h]
  have h0 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    rw [one_mul] at this
    linear_combination -this
  have : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} :=
    ⟨fun W => W.2.1 (Subsingleton.elim _ _)⟩
  rw [psi_eq, h1, h0, finsum_of_isEmpty, sub_zero]

theorem coe_aeval_restrict_apply {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : F[X]) (x : W) :
    ((aeval (g.restrict hW : Module.End F W) p x : W) : V) = aeval g p x := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval g), aeval_X, aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

theorem finrank_eq_zero_of_irreducible_charpoly {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V) (hg : Irreducible (LinearMap.charpoly g))
    (W : Submodule F V) (hne : W ≠ ⊤) (hW : ∀ x ∈ W, g x ∈ W) : Module.finrank F W = 0 := by
  by_contra h0
  have hnt : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (Nat.pos_of_ne_zero h0)
  set f : Module.End F W := g.restrict hW with hf
  have hz : aeval f (LinearMap.charpoly g) = 0 := by
    ext x
    rw [hf, coe_aeval_restrict_apply, LinearMap.aeval_self_charpoly]
    simp
  have hd : minpoly F f ∣ LinearMap.charpoly g := minpoly.dvd F f hz
  have hnu : ¬ IsUnit (minpoly F f) := minpoly.not_isUnit F f
  have hd' : LinearMap.charpoly g ∣ minpoly F f := ((hg.dvd_iff.mp hd).resolve_left hnu).dvd
  have hd'' : LinearMap.charpoly g ∣ LinearMap.charpoly f := hd'.trans (LinearMap.minpoly_dvd_charpoly f)
  have hle := natDegree_le_of_dvd hd'' (LinearMap.charpoly_monic f).ne_zero
  rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree] at hle
  have := Submodule.finrank_lt hne
  omega

theorem psi_of_irreducible_charpoly : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ g : Module.End F V, Irreducible (LinearMap.charpoly g) → psi s V g = s (LinearMap.charpoly g) := by
  intro F _ _ V _ _ _ s hs g hg
  rw [psi_eq, finsum_eq_zero_of_forall_eq_zero, sub_zero]
  intro W
  exact psi_of_finrank_eq_zero s hs _ _ (finrank_eq_zero_of_irreducible_charpoly g hg W.1 W.2.1 W.2.2)

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL


open Polynomial in
theorem _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj {F : Type} [Field F]
    (s : F[X] → ℂ) (n : ℕ) :
    ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V']
      [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V),
      _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V' (e.conj g) =
        _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n V g := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro V V' _ _ _ _ _ _ e g
    rw [_root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ, _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_succ,
      e.charpoly_conj]
    congr 1
    let σ : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} ≃
        {W : Submodule F V' // W ≠ ⊤ ∧ ∀ x ∈ W, e.conj g x ∈ W} :=
      (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv fun W => by
        change _ ↔ (Submodule.orderIsoMapComap e W ≠ ⊤ ∧
          ∀ y ∈ W.map (e : V →ₗ[F] V'), e.conj g y ∈ W.map (e : V →ₗ[F] V'))
        refine and_congr ?_ ⟨fun h y hy => ?_, fun h x hx => ?_⟩
        · exact ((Submodule.orderIsoMapComap e).injective.ne_iff' (map_top _)).symm
        · obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
          simpa [LinearEquiv.conj_apply] using
            Submodule.mem_map_of_mem (f := (e : V →ₗ[F] V')) (h x hx)
        · have := h (e x) (Submodule.mem_map_of_mem hx)
          simpa [LinearEquiv.conj_apply, Submodule.mem_map_equiv] using this
    rw [← finsum_comp_equiv σ]
    refine finsum_congr fun W => ?_
    rw [← ih W.1 (W.1.map (e : V →ₗ[F] V')) (e.submoduleMap W.1)]
    show _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec s n (W.1.map (e : V →ₗ[F] V')) _ = _
    congr 1


open Polynomial in
theorem _root_.GlobalTheory.CuspGL.psi_conj (F : Type) [Field F]
    (s : F[X] → ℂ) (V V' : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
    (e : V ≃ₗ[F] V') (g : Module.End F V) :
    _root_.GlobalTheory.CuspGL.psi s V' (e.conj g) =
      _root_.GlobalTheory.CuspGL.psi s V g := by
  unfold _root_.GlobalTheory.CuspGL.psi
  rw [← e.finrank_eq]
  exact _root_.GlobalTheory.CuspGL.invariantSubspaceMobiusInverseRec_linearEquiv_conj s _ V V' e g

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

private theorem torus_iff {F : Type} [Field F] [Finite F] (n : ℕ) (α : AlgebraicClosure F) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ n - 1) = 1 ↔ (minpoly F α).natDegree ∣ n := by
  have hi : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  rw [(minpoly.irreducible hi).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  have hq : 0 < Nat.card F ^ n := pow_pos Nat.card_pos _
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F ^ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  constructor
  · intro h; rw [h, one_mul]
  · intro h; exact mul_right_cancel₀ h0 (h.trans (one_mul α).symm)

private theorem finite_monic_natDegree {F : Type} [Field F] [Finite F] (n : ℕ) :
    {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}.Finite := by
  have : Finite (Polynomial.degreeLT F (n + 1)) := Finite.of_equiv _ (degreeLTEquiv F (n + 1)).symm.toEquiv
  have h : (Polynomial.degreeLT F (n + 1) : Set F[X]).Finite := Set.toFinite _
  refine h.subset fun P hP => ?_
  simp only [SetLike.mem_coe, mem_degreeLT]
  exact (degree_le_of_natDegree_le hP.2.1.le).trans_lt (by exact_mod_cast Nat.lt_succ_self n)

private theorem finite_torus {F : Type} [Field F] [Finite F] (n : ℕ) (hn : 0 < n) :
    {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}.Finite := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  refine (Polynomial.nthRootsFinset (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset
    fun α hα => ?_
  exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset (by omega) _).2 hα)

theorem sum_poly_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n → ∀ (c : F[X] → ℂ) (l : ℕ), (∀ P : F[X], P.Monic → P.natDegree = n → (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) → c P = 0) → ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}, c P * star (rootSum θ l P) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((n / (minpoly F α).natDegree : ℕ) : ℂ) * c (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  intro F _ _ θ n hn c l hc
  classical
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have hi : ∀ α : AlgebraicClosure F, IsIntegral F α := fun α => Algebra.IsIntegral.isIntegral α
  have hne : ∀ α : AlgebraicClosure F, α ^ (Nat.card F ^ n - 1) = 1 → α ≠ 0 := by
    rintro α h rfl
    rw [zero_pow (by omega)] at h
    exact zero_ne_one h
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_monic_natDegree n),
    finsum_mem_eq_finite_toFinset_sum _ (finite_torus n hn),
    ← Finset.sum_fiberwise_of_maps_to (s := (finite_torus (F := F) n hn).toFinset) (t := (finite_monic_natDegree (F := F) n).toFinset)
      (g := fun α => minpoly F α ^ (n / (minpoly F α).natDegree))]
  swap
  · intro α hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα ⊢
    have hm := minpoly.monic (hi α)
    refine ⟨hm.pow _, ?_, ?_⟩
    · rw [hm.natDegree_pow, Nat.div_mul_cancel ((torus_iff n α (hne α hα)).1 hα)]
    · rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
      exact pow_ne_zero _ (minpoly.coeff_zero_ne_zero (hi α) (hne α hα))
  refine Finset.sum_congr rfl fun P hP => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hP, hd, h0⟩ := hP
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
  swap
  · rw [hc P hP hd hex, zero_mul]
    refine (Finset.sum_eq_zero fun α hα => ?_).symm
    rw [(Finset.mem_filter.1 hα).2, hc P hP hd hex, mul_zero, zero_mul]
  obtain ⟨f, m, hf, hirr, hm, rfl⟩ := hex
  rw [hf.natDegree_pow] at hd
  have hdiv : n / f.natDegree = m := by
    rw [← hd, Nat.mul_div_cancel _ hirr.natDegree_pos]
  have hmp : ∀ α : AlgebraicClosure F, aeval α f = 0 → minpoly F α = f := fun α h =>
    (minpoly.eq_of_irreducible_of_monic hirr h hf).symm
  have hfib : Finset.filter (fun α : AlgebraicClosure F => minpoly F α ^ (n / (minpoly F α).natDegree) = f ^ m)
      (finite_torus (F := F) n hn).toFinset = (f.map (algebraMap F (AlgebraicClosure F))).roots.toFinset := by
    ext α
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset]
    rw [mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : n / (minpoly F α).natDegree ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hn ((torus_iff n α (hne α h1)).1 h1)) (minpoly.natDegree_pos (hi α))).ne'
      have h4 := congrArg (aeval α) h2
      rw [map_pow, map_pow, minpoly.aeval, zero_pow h3] at h4
      exact pow_eq_zero_iff hm.ne' |>.1 h4.symm
    · intro h
      have hα : α ≠ 0 := by
        rintro rfl
        apply h0
        rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
        rw [aeval_def, eval₂_at_zero, map_eq_zero] at h
        rw [h, zero_pow hm.ne']
      rw [torus_iff n α hα, hmp α h, hdiv]
      exact ⟨Dvd.intro_left _ hd, rfl⟩
  have hsep : f.Separable := PerfectField.separable_of_irreducible hirr
  have hnd : (f.map (algebraMap F (AlgebraicClosure F))).roots.Nodup := nodup_roots hsep.map
  rw [hfib, rootSum, Polynomial.map_pow, roots_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    ← Multiset.dedup_eq_self.2 hnd, ← Multiset.toFinset_val, ← Finset.sum_eq_multiset_sum,
    Finset.val_toFinset, Finset.smul_sum, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap] at hα
  rw [hmp α hα, hdiv, star_nsmul, nsmul_eq_mul]
  ring

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.CyclicMass

variable {F : Type} [Field F]

theorem charpoly_mulLeft_root (D : F[X]) (hD : D.Monic) [FiniteDimensional F (AdjoinRoot D)] :
    LinearMap.charpoly (LinearMap.mulLeft F (AdjoinRoot.root D)) = D := by
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hD)
  rw [AdjoinRoot.powerBasis'_gen] at h
  have h2 : minpoly F (AdjoinRoot.root D) = D := by
    rw [AdjoinRoot.minpoly_root hD.ne_zero, hD.leadingCoeff]; simp
  rw [h2] at h
  rw [← LinearMap.charpoly_toMatrix _ (AdjoinRoot.powerBasis' hD).basis]
  exact h

theorem map_mk {V : Type} [AddCommGroup V] [Module F V] (D : F[X]) (f : AdjoinRoot D →ₗ[F] V)
    (g : Module.End F V) (h : ∀ a, f (AdjoinRoot.root D * a) = g (f a)) (p : F[X]) :
    f (AdjoinRoot.mk D p) = aeval g p (f 1) := by
  induction p using Polynomial.induction_on with
  | C a =>
    have : AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this, map_smul]; simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this, map_mul, AdjoinRoot.mk_X, h, ih, map_mul (aeval g) X, aeval_X, Module.End.mul_apply]

theorem cyclic_one (D : F[X]) (U : Submodule F (AdjoinRoot D))
    (hU : ∀ a ∈ U, AdjoinRoot.root D * a ∈ U) (h1 : (1 : AdjoinRoot D) ∈ U) : U = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C a =>
    have : AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]; exact U.smul_mem _ h1
  | add p q hp hq => rw [map_add (f := _)]; exact U.add_mem (hp trivial) (hq trivial)
  | monomial n a ih =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this, map_mul, AdjoinRoot.mk_X]
    exact hU _ (ih trivial)

theorem card_pairs {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (D : F[X]) (hD : D.Monic)
    (hV : Module.finrank F V = D.natDegree) :
    Nat.card (AdjoinRoot D ≃ₗ[F] V) =
      Nat.card (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := by
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  let Φ : (AdjoinRoot D ≃ₗ[F] V) → (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := fun e =>
    ⟨⟨e.conj (LinearMap.mulLeft F (AdjoinRoot.root D)), by
        rw [LinearEquiv.charpoly_conj, charpoly_mulLeft_root D hD]⟩,
      ⟨e 1, fun U hU h1 => by
        have := cyclic_one D (U.comap e.toLinearMap) (fun a ha => by
          have := hU _ ha
          simpa [LinearEquiv.conj_apply] using this) h1
        rw [eq_top_iff]
        intro v _
        have h2 : e.symm v ∈ U.comap e.toLinearMap := this ▸ Submodule.mem_top
        simpa using h2⟩⟩
  have hΦ : ∀ (e : AdjoinRoot D ≃ₗ[F] V) (p : F[X]),
      e (AdjoinRoot.mk D p) = aeval (Φ e).1.1 p (Φ e).2.1 := fun e p =>
    map_mk D e.toLinearMap _ (fun a => by simp [Φ, LinearEquiv.conj_apply]) p
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨?_, ?_⟩)
  · intro e e' h
    ext a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hΦ, hΦ, h]
  · rintro ⟨⟨g, hg⟩, ⟨v, hv⟩⟩
    have h0 : aeval g D = 0 := hg ▸ LinearMap.aeval_self_charpoly g
    let f : AdjoinRoot D →ₗ[F] V :=
      (LinearMap.applyₗ v) ∘ₗ (aeval g).toLinearMap ∘ₗ AdjoinRoot.modByMonicHom hD
    have hf : ∀ p, f (AdjoinRoot.mk D p) = aeval g p v := fun p => by
      simp [f, AdjoinRoot.modByMonicHom_mk, Polynomial.aeval_modByMonic_eq_self_of_root h0]
    have hf1 : f 1 = v := by simpa using hf 1
    have hfx : ∀ a, f (AdjoinRoot.root D * a) = g (f a) := fun a => by
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
      rw [← AdjoinRoot.mk_X, ← map_mul, hf, hf]; simp
    have hs : Function.Surjective f := by
      rw [← LinearMap.range_eq_top]
      refine hv _ ?_ ⟨1, hf1⟩
      rintro _ ⟨a, rfl⟩
      exact ⟨_, hfx a⟩
    have hi : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hA.trans hV.symm)).2 hs
    refine ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, ?_⟩
    have hg' : (Φ (LinearEquiv.ofBijective f ⟨hi, hs⟩)).1 = ⟨g, hg⟩ := by
      apply Subtype.ext
      ext w
      obtain ⟨a, rfl⟩ := (LinearEquiv.ofBijective f ⟨hi, hs⟩).surjective w
      simp only [Φ, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      exact hfx a
    refine Sigma.ext hg' ?_
    refine (Subtype.heq_iff_coe_eq ?_).2 hf1
    intro w
    rw [hg']

end GlobalTheory.CuspGL.CyclicMass

namespace GlobalTheory.CuspGL

theorem mass_card_cyclic (F : Type) [Field F] [Finite F] (D : F[X]) (hD : D.Monic) :
    mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by
  classical
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  have h := CyclicMass.card_pairs (V := Fin D.natDegree → F) D hD (by simp)
  haveI : Finite (Module.End F (Fin D.natDegree → F)) :=
    Finite.of_injective _ DFunLike.coe_injective
  haveI := Fintype.ofFinite {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}
  rw [Nat.card_sigma] at h
  let e0 : AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hA])
  have h2 : Nat.card (AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F)) = Nat.card (GL (Fin D.natDegree) F) := by
    refine Nat.card_congr (Equiv.trans ?_ (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F _)).toEquiv.symm)
    exact ⟨fun e => e0.symm.trans e, fun e => e0.trans e, fun e => by ext; simp, fun e => by ext; simp⟩
  rw [glCard, ← h2, h, mass, ← finsum_set_coe_eq_finsum_mem, Nat.cast_sum]
  exact finsum_eq_sum_of_fintype (α := {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}) _

end GlobalTheory.CuspGL
end
end
