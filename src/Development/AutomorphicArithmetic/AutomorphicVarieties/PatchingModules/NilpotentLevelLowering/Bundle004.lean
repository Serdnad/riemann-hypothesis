module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LevelModule
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ExistsGroupRingSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ResPull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Separation.Connected

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mul_prod_le_of_le_one_of_le_of_mul_le_one {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a b : Fin n → G) (hb1 : ∀ l, b l ≤ 1) (hba : ∀ l, b l ≤ a l) (hab : ∀ l, a l * b l ≤ 1) :
    ∀ i j : Fin n, i < j → a i * ∏ l, b l ≤ a j := by
  classical
  intro i j hij
  have hne : j ≠ i := ne_of_gt hij
  have hsplit : ∏ l, b l = b i * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩),
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  calc a i * ∏ l, b l = (a i * b i) * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
        rw [hsplit, mul_assoc]
    _ ≤ 1 * (b j * 1) := mul_le_mul' (hab i) (mul_le_mul' le_rfl (Finset.prod_le_one' (fun l _ => hb1 l)))
    _ ≤ a j := by rw [one_mul, mul_one]; exact hba j

private theorem mul_pow_sub_le_of_mul_le_of_le_of_le_one {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a : Fin n → G) (c : G) (hc1 : c ≤ 1) (hc : ∀ i j : Fin n, i < j → a i * c ≤ a j) (i j : Fin n)
    (hij : i ≤ j) : a i * c ^ (n - (i : ℕ)) ≤ a j * c ^ (n - (j : ℕ)) := by
  rcases lt_or_eq_of_le hij with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n - (i : ℕ) = (n - (j : ℕ)) + d + 1 :=
      ⟨(j : ℕ) - i - 1, by have := j.isLt; have := Fin.lt_iff_val_lt_val.mp h; omega⟩
    calc a i * c ^ (n - (i : ℕ)) = (a i * c) * c ^ d * c ^ (n - (j : ℕ)) := by
          rw [hd, pow_add, pow_add, pow_one]; ac_rfl
      _ ≤ a j * 1 * c ^ (n - (j : ℕ)) := mul_le_mul' (mul_le_mul' (hc i j h) (pow_le_one' hc1 d)) le_rfl
      _ = a j * c ^ (n - (j : ℕ)) := by rw [mul_one]
  · rw [h]

private theorem thetaLoc_split {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (t : Fin n → kˣ) : ∃ b : Fin n → kˣ, Dom b ∧ Dom (t * b) := by
  classical
  let φ : kˣ →* (ValueGroupWithZero k)ˣ := Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom
  have hφ : ∀ u : kˣ, valuation k (u : k) = ((φ u : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) :=
    fun u => rfl
  let w : Fin n → kˣ := fun l => if φ (t l) ≤ 1 then t l else (t l)⁻¹
  have hw1 : ∀ l, φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact h
    · rw [map_inv]; exact inv_le_one'.mpr (le_of_lt (not_le.mp h))
  have hwa : ∀ l, φ (w l) ≤ φ (t l) := fun l => by
    simp only [w]
    split_ifs with h
    · exact le_rfl
    · rw [map_inv]
      exact (inv_le_one'.mpr (le_of_lt (not_le.mp h))).trans (le_of_lt (not_le.mp h))
  have hwab : ∀ l, φ (t l) * φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact mul_le_one' h h
    · rw [map_inv, mul_inv_cancel]
  have hC : φ (∏ l, w l) = ∏ l, φ (w l) := map_prod φ _ _
  have hc1 : ∏ l, φ (w l) ≤ 1 := Finset.prod_le_one' (fun l _ => hw1 l)
  refine ⟨fun i => (∏ l, w l) ^ (n - (i : ℕ)), ?_, ?_⟩
  · intro i j hij
    dsimp only
    rw [hφ, hφ, Units.val_le_val, map_pow, map_pow, hC]
    simpa using mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun _ => (1 : (ValueGroupWithZero k)ˣ)) _ hc1
      (fun _ _ _ => by rw [one_mul]; exact hc1) i j hij
  · intro i j hij
    rw [Pi.mul_apply, Pi.mul_apply]
    rw [hφ, hφ, Units.val_le_val, map_mul, map_mul, map_pow, map_pow, hC]
    exact mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun l => φ (t l)) _ hc1
      (mul_prod_le_of_le_one_of_le_of_mul_le_one (fun l => φ (t l)) (fun l => φ (w l)) hw1 hwa hwab) i j hij

private theorem thetaLoc_ext {T A M₁ M₂ : Type} [CommGroup T] [CommRing A] [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] (Θ : T →* (Module.End A M₁)ˣ) (θ : T →* (Module.End A M₂)ˣ) (ι : M₁ → M₂)
    (t b : T) (hb : ∀ m, (θ b).val (ι m) = ι ((Θ b).val m))
    (htb : ∀ m, (θ (t * b)).val (ι m) = ι ((Θ (t * b)).val m)) (m : M₁) :
    (θ t).val (ι m) = ι ((Θ t).val m) := by
  have key : ∀ y, ((θ b)⁻¹).val ((θ b).val y) = y := fun y => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  have h1 := htb m
  rw [mul_comm t b] at h1
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h1
  rw [← hb] at h1
  rw [← key ((θ t).val (ι m)), h1, key]

theorem UpperTheory.V.Pa.Lev.thetaLoc :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ), IsThetaQ ρ C Θ → ∀ j θ, IsTheta (ρ.comp (atJ n w j)) (C j) θ → ∀ t (m : fixd ρ (UC n w C)) (m' : fixd (ρ.comp (atJ n w j)) (iwC _ n (C j))), (m' : M) = m → ((θ t).val m').val = ((Θ j t).val m).val := by
  intro L _ _ n q w A M _ _ _ ρ C Θ hΘ j θ hθ t m m' hm
  have hmem : ∀ u ∈ iwC _ n (C j), atJ n w j u ∈ UC n w C := by
    intro u hu
    simp only [UC, Subgroup.mem_pi]
    intro i _
    by_cases h : i = j
    · subst h
      simpa [atJ] using hu
    · simp [atJ, Pi.mulSingle_eq_of_ne h, Subgroup.one_mem]
  let ι : fixd ρ (UC n w C) → fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) := fun x =>
    ⟨x, show ∀ u ∈ iwC _ n (C j), (ρ.comp (atJ n w j)) u x = x from fun u hu =>
      (show ∀ u ∈ UC n w C, ρ u x = x from x.2) _ (hmem u hu)⟩
  have hdom : ∀ s, Dom s → ∀ x, (θ s).val (ι x) = ι ((Θ j s).val x) := by
    intro s hs x
    apply Subtype.ext
    rw [hθ s hs]
    unfold hk
    rw [(hkApply _ _ _ _ _ _ _ ((heckePairIwC _ n (C j)).1 _)).1]
    exact (hΘ.1 j s hs x).symm
  obtain ⟨b, hb, htb⟩ := thetaLoc_split t
  have key := thetaLoc_ext (Θ j) θ ι t b (hdom b hb) (hdom (t * b) htb) m
  have hm' : m' = ι m := Subtype.ext hm
  rw [hm', key]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def fsSub {Λ R M P : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [AddCommGroup M] [Module Λ M]
    [AddCommGroup P] [Module R P] (θ : R →ₐ[Λ] Module.End Λ M) (E : P ≃+ M) (hE : ∀ (r : R) x, E (r • x) = θ r (E x))
    (N : Submodule Λ M) (hN : ∀ r, ∀ m ∈ N, θ r m ∈ N) : Submodule R P where
  carrier := {x | E x ∈ N}
  add_mem' := fun {x y} hx hy => by
    change E (x + y) ∈ N
    rw [map_add (f := _)]; exact N.add_mem hx hy
  zero_mem' := by
    change E 0 ∈ N
    rw [map_zero]; exact N.zero_mem
  smul_mem' := fun r x hx => by
    change E (r • x) ∈ N
    rw [hE]; exact hN r _ hx

private theorem fs_abs {Λ R M P : Type} [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R] [AddCommGroup M] [Module Λ M]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (θ : R →ₐ[Λ] Module.End Λ M) (E : P ≃+ M) (hE : ∀ (r : R) x, E (r • x) = θ r (E x))
    (N C : Submodule Λ M) (hN : ∀ r, ∀ m ∈ N, θ r m ∈ N) (hC : ∀ r, ∀ m ∈ C, θ r m ∈ C) (h : _root_.IsCompl N C) :
    ∃ (rk : ℕ) (e : N ≃+ (Fin rk → R)), ∀ (r : R) (m m' : N), (m' : M) = θ r m → e m' = r • e m := by
  set P' := fsSub θ E hE N hN with hP'
  set Q' := fsSub θ E hE C hC with hQ'
  have hc : _root_.IsCompl P' Q' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx1 hx2
      have h0 : E x = 0 := (Submodule.disjoint_def.mp h.disjoint) _ hx1 hx2
      exact E.injective (h0.trans (map_zero E).symm)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : E x ∈ N ⊔ C := by rw [h.sup_eq_top]; trivial
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
      rw [Submodule.mem_sup]
      refine ⟨E.symm y, (show E (E.symm y) ∈ N by simpa using hy), E.symm z,
        (show E (E.symm z) ∈ C by simpa using hz), ?_⟩
      apply E.injective
      rw [map_add (f := _), E.apply_symm_apply, E.apply_symm_apply, hyz]
  haveI : Module.Projective R P' :=
    Module.Projective.of_split P'.subtype (Submodule.linearProjOfIsCompl P' Q' hc)
      (Submodule.linearProjOfIsCompl_comp_subtype hc)
  haveI : Module.Finite R P' :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl P' Q' hc)
      (Submodule.linearProjOfIsCompl_surjective hc)
  haveI : Module.Free R P' := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis R P'
  let f : N ≃+ P' :=
    { toFun := fun m => ⟨E.symm m, (show E (E.symm m) ∈ N by simp)⟩
      invFun := fun p => ⟨E p, p.2⟩
      left_inv := fun m => by ext; simp
      right_inv := fun p => by ext; simp
      map_add' := fun m m' => by ext; simp }
  refine ⟨Module.finrank R P', f.trans b.equivFun.toAddEquiv, fun r m m' hm => ?_⟩
  have hf : f m' = r • f m := by
    ext
    apply E.injective
    simp only [f, AddEquiv.coe_mk, Equiv.coe_fn_mk, Submodule.coe_smul, hE, E.apply_symm_apply]
    exact hm
  show b.equivFun (f m') = r • b.equivFun (f m)
  rw [hf, LinearEquiv.map_smul]

private theorem fs_gen {σ : Type} [Fintype σ] [DecidableEq σ] (n : σ → ℕ) [∀ s, NeZero (n s)]
    (S : Submonoid (∀ s, Multiplicative (ZMod (n s))))
    (h : ∀ s : σ, (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ∈ S)
    (g : ∀ s, Multiplicative (ZMod (n s))) : g ∈ S := by
  have key : ∀ s, Pi.mulSingle s (g s) ∈ S := by
    intro s
    have : Pi.mulSingle s (g s) = (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ^ (Multiplicative.toAdd (g s)).val := by
      rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
    rw [this]
    exact S.pow_mem (h s) _
  rw [← Finset.univ_prod_mulSingle g]
  exact S.prod_mem fun s _ => key s

private def fsAgree {Λ S M : Type} [CommRing Λ] [CommRing S] [Algebra Λ S] [AddCommGroup M] [Module Λ M]
    (N : Submodule Λ M) (act : S →ₐ[Λ] Module.End Λ N) (θ : S →ₐ[Λ] Module.End Λ M) : Subalgebra Λ S where
  carrier := {z | ∀ m : N, (act z m : M) = θ z m}
  mul_mem' := fun {x y} hx hy m => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx, hy]
  add_mem' := fun {x y} hx hy m => by
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hx, hy]
  algebraMap_mem' := fun r m => by
    simp

theorem UpperTheory.V.Pa.Lev.freeSummand :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (l : ℕ) (q n : ℕ) (a : Fin q → ℕ) (M : Type) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] (ρ : Representation Λ (Del l n a) M) (N C : Submodule Λ M), l.Prime → (l : Λ) ∈ maximalIdeal Λ → Module.Projective (MonoidAlgebra Λ (Del l n a)) ρ.asModule → _root_.IsCompl N C → (∀ g, ∀ m ∈ N, ρ g m ∈ N) → (∀ g, ∀ m ∈ C, ρ g m ∈ C) → ∀ act : MvPowerSeries (Fin q × Fin n) Λ →ₐ[Λ] Module.End Λ N, (∀ (p : Fin q × Fin n) (m : N), (act (1 + MvPowerSeries.X p) m : M) = ρ (Pi.mulSingle p (Multiplicative.ofAdd 1)) m) → ∃ (rk : ℕ) (e : N ≃+ (Fin rk → MvPowerSeries (Fin q × Fin n) Λ ⧸ delIdeal l Λ n a)), ∀ z m, e (act z m) = z • e m := by
  intro Λ _ _ _ _ l q n a M _ _ _ ρ N C hl hlm hproj hNC hN hC act hact
  obtain ⟨φ, hφX, hφs, hloc, -⟩ := exists_groupRing_surj Λ l hl hlm (Fin q × Fin n) (fun p => a p.1)
  have hker : RingHom.ker φ = delIdeal l Λ n a := groupRing_ker Λ l hl hlm (Fin q × Fin n) (fun p => a p.1) φ hφX hφs
  haveI := hloc
  have hθN : ∀ r, ∀ m ∈ N, ρ.asAlgebraHom r m ∈ N := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g => intro m hm; rw [Representation.asAlgebraHom_of]; exact hN g m hm
    | add x y hx hy => intro m hm; rw [map_add (f := _), LinearMap.add_apply]; exact N.add_mem (hx m hm) (hy m hm)
    | smul c x hx => intro m hm; rw [map_smul, LinearMap.smul_apply]; exact N.smul_mem c (hx m hm)
  have hθC : ∀ r, ∀ m ∈ C, ρ.asAlgebraHom r m ∈ C := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g => intro m hm; rw [Representation.asAlgebraHom_of]; exact hC g m hm
    | add x y hx hy => intro m hm; rw [map_add (f := _), LinearMap.add_apply]; exact C.add_mem (hx m hm) (hy m hm)
    | smul c x hx => intro m hm; rw [map_smul, LinearMap.smul_apply]; exact C.smul_mem c (hx m hm)
  haveI : Module.Finite Λ ρ.asModule := Module.Finite.equiv ρ.asModuleEquiv.symm
  haveI : Module.Finite (MonoidAlgebra Λ (Del l n a)) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  obtain ⟨rk, e0, he0⟩ := fs_abs ρ.asAlgebraHom ρ.asModuleEquiv.toAddEquiv
    (fun r x => ρ.asModuleEquiv_map_smul r x) N C hθN hθC hNC
  let A := fsAgree N act (ρ.asAlgebraHom.comp φ)
  have hgen : ∀ p, (1 + MvPowerSeries.X p : MvPowerSeries (Fin q × Fin n) Λ) ∈ A := by
    intro p m
    show (act (1 + MvPowerSeries.X p) m : M) = ρ.asAlgebraHom (φ (1 + MvPowerSeries.X p)) m
    rw [hφX p, Representation.asAlgebraHom_of]
    exact hact p m
  have hgrp : ∀ g : Del l n a, ∃ w ∈ A, φ w = MonoidAlgebra.of Λ (Del l n a) g := by
    haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun p => ⟨pow_ne_zero _ hl.ne_zero⟩
    let T : Submonoid (Del l n a) :=
      { carrier := {g | ∃ w ∈ A, φ w = MonoidAlgebra.of Λ (Del l n a) g}
        mul_mem' := fun {x y} hx hy => by
          obtain ⟨w, hw, hwx⟩ := hx
          obtain ⟨w', hw', hwy⟩ := hy
          exact ⟨w * w', A.mul_mem hw hw', by rw [map_mul, hwx, hwy, map_mul]⟩
        one_mem' := ⟨1, A.one_mem, by rw [map_one, map_one]⟩ }
    intro g
    exact fs_gen (fun p : Fin q × Fin n => l ^ a p.1) T (fun p => ⟨_, hgen p, hφX p⟩) g
  have hsurjA : ∀ y, ∃ w ∈ A, φ w = y := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g => exact hgrp g
    | add x y hx hy =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', rfl⟩ := hy
      exact ⟨w + w', A.add_mem hw hw', map_add _ _ _⟩
    | smul c x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨c • w, A.smul_mem hw c, map_smul _ _ _⟩
  have hkill : delIdeal l Λ n a ≤ RingHom.ker act := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    have hw0 : ((1 + MvPowerSeries.X p) ^ l ^ a p.1 - 1 : MvPowerSeries (Fin q × Fin n) Λ) ∈ A :=
      A.sub_mem (A.pow_mem (hgen p) _) A.one_mem
    have hφ0 : φ ((1 + MvPowerSeries.X p) ^ l ^ a p.1 - 1) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.subset_span ⟨p, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    ext m
    rw [hw0 m]
    simp [hφ0]
  have hagree : ∀ z (m : N), (act z m : M) = ρ.asAlgebraHom (φ z) m := by
    intro z m
    obtain ⟨w, hwA, hw⟩ := hsurjA (φ z)
    have hzw : z - w ∈ RingHom.ker act := hkill (by rw [← hker, RingHom.mem_ker, map_sub, hw, sub_self])
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hzw
    rw [hzw, ← hw]
    exact hwA m
  let ψ : MonoidAlgebra Λ (Del l n a) ≃ₐ[Λ] MvPowerSeries (Fin q × Fin n) Λ ⧸ delIdeal l Λ n a :=
    (Ideal.quotientKerAlgEquivOfSurjective hφs).symm.trans (Ideal.quotientEquivAlgOfEq Λ hker)
  have hψ : ∀ z, ψ (φ z) = Ideal.Quotient.mk (delIdeal l Λ n a) z := by
    intro z
    apply ψ.symm.injective
    rw [AlgEquiv.symm_apply_apply]
    simp [ψ, Ideal.quotientKerAlgEquivOfSurjective_apply]
  refine ⟨rk, e0.trans (AddEquiv.piCongrRight fun _ => ψ.toRingEquiv.toAddEquiv), fun z m => ?_⟩
  have h1 := he0 (φ z) m (act z m) (hagree z m)
  funext i
  show ψ (e0 (act z m) i) = z • ψ (e0 m i)
  rw [h1, Pi.smul_apply, smul_eq_mul, map_mul, hψ, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ot_inv {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (e : G.Hom G') (hi : Function.Injective e.p) :
    ∃ k : G'.Hom G, ∀ g, k.p (e.p g) = g := by
  let eq : G.Γ ≃* G'.Γ := MulEquiv.ofBijective e.p ⟨hi, e.surj⟩
  have hk : ∀ x, e.p (eq.symm x) = x := fun x => eq.apply_symm_apply x
  have hcont : Continuous (eq.symm : G'.Γ → G.Γ) :=
    (Continuous.homeoOfEquivCompactToT2 (f := eq.toEquiv) e.cont).symm.continuous
  refine ⟨Glob.Hom.mk eq.symm.toMonoidHom hcont eq.symm.surjective (fun g => ?_) ?_ (fun g => ?_)
    (fun v g => ?_) (fun v g => ?_), fun g => eq.symm_apply_apply g⟩
  · show G.η (eq.symm g) = G'.η g
    rw [← e.η, hk]
  · show eq.symm G'.c = G.c
    apply hi
    rw [hk, e.c]
  · show G.ε (eq.symm g) = G'.ε g
    rw [← e.ε, hk]
  · show eq.symm _ = _
    apply hi
    rw [hk, e.φ]
  · show eq.symm _ = _
    apply hi
    rw [hk, e.φu]

private theorem ot_tr_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (y : MonoidAlgebra A H) : (D.comap φ).tr y = D.tr (MonoidAlgebra.mapDomainRingHom A φ y) := by
  have key : ∀ z : MonoidAlgebra A H, MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.mapRingHom H Polynomial.C z) =
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom A φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | single m r => simp [MonoidAlgebra.mapRingHom_single]
  show (-1) ^ 1 * ((D.D (Polynomial A)) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C y))).coeff (n - 1) =
    (-1) ^ 1 * ((D.D (Polynomial A)) (MonoidAlgebra.single 1 Polynomial.X -
      MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom A φ y))).coeff (n - 1)
  rw [map_sub, key]
  simp

private theorem ot_comap_comap {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [Group K] (D : GDet n A G)
    (φ : H →* G) (ψ : K →* H) : (D.comap φ).comap ψ = D.comap (φ.comp ψ) := by
  apply GDet.ext
  intro B _ _ x
  show (D.D B) (MonoidAlgebra.mapDomainRingHom B φ (MonoidAlgebra.mapDomainRingHom B ψ x)) =
    (D.D B) (MonoidAlgebra.mapDomainRingHom B (φ.comp ψ) x)
  rw [MonoidAlgebra.mapDomainRingHom_comp, RingHom.comp_apply]

private theorem ot_single {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g : H) (a : A) :
    MonoidAlgebra.mapDomainRingHom A φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (φ g) a := by simp

private theorem mapDomain_charpoly_element {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g : H) (u : Fin n → A) :
    MonoidAlgebra.mapDomainRingHom A φ (q1El g u) = q1El (φ g) u := by
  simp only [q1El, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, ot_single, map_one]

private theorem mapDomain_partial_charpoly_element {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g t : H) (u : Fin n → A)
    (i : Fin n) (y : A) : MonoidAlgebra.mapDomainRingHom A φ (q2El g t u i y) = q2El (φ g) (φ t) u i y := by
  simp only [q2El, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, ot_single, apply_ite,
    map_one]

private theorem ot_pair {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (k : G'.Hom G) {O : Type} [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid G.frame O n} {r' : Resid G'.frame O n} (hc : Glob.Compat k r' r)
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) :
    ∃ p' : Pair r' R, p'.D = p.D.comap k.p₀ ∧ p'.ψ = p.ψ := by
  let fh : FHom G'.frame G.frame :=
    { π := k.p, π_cont := k.cont, hη := k.η, hc := k.c, hε := k.ε, vl := id,
      gv := fun _ => MonoidHom.id _, gv_cont := fun _ => continuous_id,
      hφ := fun v g => (k.φ v g).symm, hI := fun _ _ hg => hg }
  have hπ : fh.π₀ = k.p₀ := rfl
  obtain ⟨h1, h2, h3⟩ := hc
  have hfc : fh.Compat r' r := by
    refine ⟨fun i => by rw [hπ]; exact h1 i, fun v i => ?_, fun v i g hg => ?_, fun u g hg => ?_⟩
    · rw [h2]
      rfl
    · rw [h3]
      rfl
    · right
      refine ⟨u, ?_⟩
      obtain ⟨hgI, hgk⟩ := Subgroup.mem_inf.mp hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hgI
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        exact Subtype.ext (k.φu u x).symm
      · rw [Subgroup.mem_iInf] at hgk ⊢
        intro i
        have := hgk i
        rw [MonoidHom.mem_ker, h1 i] at this
        rw [MonoidHom.mem_ker, hπ]
        exact this
  obtain ⟨p', hD, hψ⟩ := exists_determinantPair_pullback l G'.frame G.frame fh O n r' r hfc
    (fun h0 => (p.isEmpty_of_zero h0).1) R p
  exact ⟨p', hD, funext fun v => funext fun i => by rw [hψ]; rfl⟩

theorem UpperTheory.V.Pa.Lev.opTransport :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (G G' : Glob l L) (e : G.Hom G') (h : G.Hom G0) (h' : G'.Hom G0) (q N : ℕ) (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ), Function.Injective e.p → (∀ g, h'.p (e.p g) = h.p g) → OpRel A Nq ph ta ex → ∃ A' : OpMod b h' q N, OpRel A' Nq (fun j => e.p₀ (ph j)) (fun j => e.p₀ (ta j)) ex := by
  intro l _ L G0 O _ _ _ _ _ n r B _ _ _ u J D b G G' e h h' q N A Nq ph ta ex hi hh hR
  obtain ⟨k, hk⟩ := ot_inv e hi
  have hek : ∀ x, e.p (k.p x) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surj x
    rw [hk]
  have hcomp : h.p₀.comp k.p₀ = h'.p₀ := MonoidHom.ext fun g => Subtype.ext (by
    show h.p (k.p (g : G'.Γ)) = h'.p (g : G'.Γ)
    rw [← hh, hek])
  have hpe : ∀ x, h'.p₀ (e.p₀ x) = h.p₀ x := fun x => Subtype.ext (hh (x : G.Γ))
  have hke : ∀ x, k.p₀ (e.p₀ x) = x := fun x => Subtype.ext (hk (x : G.Γ))
  obtain ⟨rN', hc'⟩ := Core.resPull l L G' G0 h' n O r
  have hck : Glob.Compat k rN' A.rN := by
    obtain ⟨h1, h2, h3⟩ := hc'
    obtain ⟨a1, a2, a3⟩ := A.compat
    refine ⟨fun i => ?_, h2.trans a2.symm, h3.trans a3.symm⟩
    rw [h1 i, a1 i, MonoidHom.comp_assoc, hcomp]
  obtain ⟨p', hpD, hpψ⟩ := ot_pair k hck A.p
  have hmc : ∀ {S : Type} [CommRing S] (f : A.R →+* S), (A.p.D.comap k.p₀).map f = (A.p.D.map f).comap k.p₀ :=
    fun _ => rfl
  have hlam : ∀ j : Fin D, (algebraMap (abelian₂ O Empty D) A.R) (MvPowerSeries.X (Sum.inr j)) =
      (algebraMap O A.R) (b.wt.c j) * ↑((p'.ψ (b.wt.v j) (b.wt.i j)) (b.wt.γ j)) - 1 := by
    intro j
    rw [hpψ]
    exact A.segmentWeightExponent j
  have hβ : p'.Maps A.β.toRingHom (u.D.comap h'.p₀) u.ψ := by
    refine ⟨?_, fun v i => ?_⟩
    · rw [hpD, hmc, A.β_pair.1, ot_comap_comap, hcomp]
    · rw [hpψ]
      exact A.β_pair.2 v i
  refine ⟨{ A with
              rN := rN'
              compat := hc'
              p := p'
              segmentWeightExponent := hlam
              β_pair := hβ }, ?_⟩
  refine ⟨?_, fun j g => ?_, fun j i g => ?_⟩
  · dsimp only
    simp only [hpe]
    exact hR.two
  · dsimp only
    rw [hpD, hmc, ot_tr_comap, map_mul, ot_single, mapDomain_charpoly_element]
    simp only [hke]
    exact hR.rel1 j (k.p₀ g)
  · dsimp only
    rw [hpD, hmc, ot_tr_comap, map_mul, ot_single, mapDomain_partial_charpoly_element]
    simp only [hke]
    exact hR.rel2 j i (k.p₀ g)
end
