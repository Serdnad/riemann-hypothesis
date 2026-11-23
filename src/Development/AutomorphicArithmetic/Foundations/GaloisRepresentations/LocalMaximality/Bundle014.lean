module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {A : Type} [Field A] [Algebra ℂ A]

end

end UpperTheory.Gal.productCup_of_system

private theorem stab_lemma {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (q : ℕ) :
    Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) := by
  intro b hb m hm
  change b • m ∈ omB ℂ L B q
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    exact ⟨b * a, B.mul_mem hb ha, v, hv, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

private theorem kos_Z_mono_of_le {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) {κ : Type} [LinearOrder κ] {M M' : Submodule ℂ E}
    (h : M ≤ M') (r : κ → S) (m : ℤ) : (kos act M r).Z m ≤ (kos act M' r).Z m := by
  intro c hc
  simp only [GlobalTheory.PD.Cx.Z, kos, acx, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ,
    forall_const, true_implies, LinearMap.mem_ker] at hc ⊢
  refine ⟨fun s => ?_, hc.2⟩
  have hs := hc.1 s
  split_ifs at hs ⊢ with hcard
  · exact h hs
  · exact hs

theorem UpperTheory.Gal.productCup_of_system.yKE_of :
    LG → OmLoc → RYFT → Htpy → K1 → LocReg → ValBasic → RYBasic → YKE := by
  intro hLG hOm hFT hH hK1 hLR hVB hRB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY κ _ _ r I J hI hr
  have hact : (sysY x j2 d).act = Algebra.lsmul ℂ ℂ (DR ℂ K') := rfl
  have hM : (sysY x j2 d).M I J = omB ℂ K' (RY (xv x) j2 I J) d := rfl
  rw [hact, hM]
  haveI : Algebra.FiniteType ℂ ↥(RY (xv x) j2 I J) := hFT F K K' d x j2 hY I J hI
  set B := RY (xv x) j2 I J with hB
  have hglob : ∀ (m : ℤ) (c : Finset κ → DR ℂ K'),
      (∀ e : ↥B →ₐ[ℂ] ℂ, c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) r).B m) →
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' B d) r).B m := by
    intro m c hc
    refine (hLG K' B (DR ℂ K') κ (fun _ => omB ℂ K' B d) r (fun _ => stab_lemma B d)).1 m c
      (fun e => ?_)
    simp only [(hOm K' B e d).1]
    exact hc e
  have hloc : ∀ e : ↥B →ₐ[ℂ] ℂ, ¬ (∀ l, Val B e (r l) 0) → ∃ l, r l ≠ 0 ∧ (r l)⁻¹ ∈ loc B e := by
    intro e h
    push_neg at h
    obtain ⟨l, hl⟩ := h
    obtain ⟨-, -, hval, hinv⟩ := hVB K' B e
    have hv := hval ⟨r l, hr l⟩
    have hc0 : e ⟨r l, hr l⟩ ≠ 0 := by
      intro h0
      rw [h0] at hv
      exact hl hv
    exact ⟨l, hinv _ _ hv hc0⟩
  have hle : ∀ e : ↥B →ₐ[ℂ] ℂ, omB ℂ K' B d ≤ omB ℂ K' (loc B e) d :=
    fun e => (hOm K' B e d).2.2 _ (hVB K' B e).1
  have hbad : ∀ (m : ℤ) (c : Finset κ → DR ℂ K'),
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' B d) r).Z m →
      ∀ e : ↥B →ₐ[ℂ] ℂ, ¬ (∀ l, Val B e (r l) 0) →
      c ∈ (kos (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) r).B m := by
    intro m c hc e h
    obtain ⟨l, hl0, hlinv⟩ := hloc e h
    have hIn : InSp (loc B e) r 1 := by
      refine ⟨fun l' => if l' = l then (r l)⁻¹ else 0, fun l' => ?_, ?_⟩
      · dsimp only
        split_ifs
        · exact hlinv
        · exact (loc B e).zero_mem
      · simp [ite_mul, hl0]
    have := hH K' (DR ℂ K') (Algebra.lsmul ℂ ℂ (DR ℂ K')) κ (loc B e)
      (omB ℂ K' (loc B e) d) r (stab_lemma _ d) m c (kos_Z_mono_of_le _ (hle e) r m hc) 1 hIn
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · intro hyp m hm c hc
    apply hglob m c
    intro e
    by_cases h : ∀ l, Val B e (r l) 0
    · obtain ⟨e0, hOv, hIn⟩ := hyp e h
      have hlocEq : loc B e = loc (rB ℂ K' (xv x) {0}) e0.1 := hOv.2.1
      have hReg : Reg (Algebra.lsmul ℂ ℂ (DR ℂ K')) (omB ℂ K' (loc B e) d) (tt K' x) := by
        rw [hlocEq]
        exact hLR F K' d x hY.covY hY.red e0
      have hKE := hK1 K' (DR ℂ K') (Algebra.lsmul ℂ ℂ (DR ℂ K')) κ (loc B e)
        (omB ℂ K' (loc B e) d) r d (tt K' x) (stab_lemma _ d) (fun l => (hVB K' B e).1 (hr l))
        hReg (fun j => by rw [hlocEq]; exact hIn j)
      exact hKE m hm (kos_Z_mono_of_le _ (hle e) r m hc)
    · exact hbad m c hc e h
  · intro m c hc hyp
    apply hglob m c
    intro e
    by_cases h : ∀ l, Val B e (r l) 0
    · exact hyp e h
    · exact hbad m c hc e h
  · intro y hy hyp
    refine (hLG K' B (DR ℂ K') κ (fun _ => omB ℂ K' B d) r (fun _ => stab_lemma B d)).2 y
      (fun e => ?_)
    simp only [(hOm K' B e d).1]
    by_cases h : ∀ l, Val B e (r l) 0
    · exact hyp e h
    · obtain ⟨l, hl0, hlinv⟩ := hloc e h
      unfold sm
      refine Submodule.mem_iSup_of_mem (r l) (Submodule.mem_iSup_of_mem (Set.mem_range_self l) ?_)
      refine Submodule.mem_map.mpr ⟨_, stab_lemma (loc B e) d _ hlinv y (hle e hy), ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel₀ hl0, map_one, Module.End.one_apply]
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem alt_expand {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {d q : ℕ} (f : M [⋀^Fin q]→ₗ[R] N) (a : Fin q → Fin d → R) (v : Fin d → M) :
    f (fun i => ∑ l, a i l • v l) =
      ∑ S : {S : Finset (Fin d) // S.card = q},
        (Matrix.of fun i j => a i (S.1.orderEmbOfFin S.2 j)).det •
          f (fun j => v (S.1.orderEmbOfFin S.2 j)) := by
  classical
  have h1 : f (fun i => ∑ l, a i l • v l) =
      ∑ φ : Fin q → Fin d, (∏ i, a i (φ i)) • f (fun i => v (φ i)) := by
    have h := f.toMultilinearMap.map_sum (fun i l => a i l • v l)
    refine h.trans (Finset.sum_congr rfl fun φ _ => ?_)
    exact f.toMultilinearMap.map_smul_univ _ _
  let e : {S : Finset (Fin d) // S.card = q} → Fin q → Fin d := fun S j => S.1.orderEmbOfFin S.2 j
  have he : ∀ S, Function.Injective (e S) := fun S => (S.1.orderEmbOfFin S.2).injective
  have hr : ∀ S, Set.range (e S) = S.1 := fun S => Finset.range_orderEmbOfFin S.1 S.2
  let Φ : (Σ _ : {S : Finset (Fin d) // S.card = q}, Equiv.Perm (Fin q)) →
      {φ : Fin q → Fin d // Function.Injective φ} :=
    fun p => ⟨e p.1 ∘ p.2, (he p.1).comp p.2.injective⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨S, σ⟩ ⟨S', σ'⟩ h
      have h' : e S ∘ σ = e S' ∘ σ' := congrArg Subtype.val h
      have hS : S = S' := by
        apply Subtype.ext
        apply Finset.coe_injective
        rw [← hr S, ← hr S', ← σ.surjective.range_comp (e S), ← σ'.surjective.range_comp (e S'), h']
      subst hS
      have : σ = σ' := by
        ext i
        exact congrArg _ (he S (congrFun h' i))
      rw [this]
    · rintro ⟨φ, hφ⟩
      have hc : (Finset.univ.image φ).card = q := by
        rw [Finset.card_image_of_injective _ hφ]; simp
      let S : {S : Finset (Fin d) // S.card = q} := ⟨_, hc⟩
      have hm : ∀ i, ∃ j, e S j = φ i := fun i => by
        have : φ i ∈ Set.range (e S) := by rw [hr]; simp [S]
        exact this
      choose s hs using hm
      have hsi : Function.Injective s := fun i i' h => hφ (by rw [← hs, ← hs, h])
      refine ⟨⟨S, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hsi)⟩, ?_⟩
      apply Subtype.ext
      funext i
      exact hs i
  rw [h1, ← Fintype.sum_subtype_add_sum_subtype (fun φ : Fin q → Fin d => Function.Injective φ)]
  have h0 : ∑ φ : {φ : Fin q → Fin d // ¬ Function.Injective φ},
      (∏ i, a i (φ.1 i)) • f (fun i => v (φ.1 i)) = 0 := by
    refine Finset.sum_eq_zero fun φ _ => ?_
    have : ¬ Function.Injective (fun i => v (φ.1 i)) := fun h => φ.2 fun i i' hi => h (by simp [hi])
    rw [f.map_eq_zero_of_not_injective _ this, smul_zero]
  rw [h0, add_zero, ← hΦ.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Matrix.det_transpose, Matrix.det_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hp := f.map_perm (fun j => v (e S j)) σ
  have hp' : f (fun i => v (e S (σ i))) = Equiv.Perm.sign σ • f (fun j => v (e S j)) := hp
  change (∏ i, a i (e S (σ i))) • f (fun i => v (e S (σ i))) = _
  rw [hp']
  have hq : ∏ i, (Matrix.of fun i j => a i (S.1.orderEmbOfFin S.2 j)).transpose (σ i) i =
      ∏ i, a i (e S (σ i)) := by
    rfl
  rw [hq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, e]

private theorem mapDR_iM (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (n : ℕ) (v : Fin n → K) :
    mapDR ℂ K L (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (algebraMap K L (v a)) := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext a
  simp [mapDR, map1, KaehlerDifferential.map_D]

private theorem pullback_kahler_iMulti {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (j2 : K →ₐ[ℂ] L)
    (n : ℕ) (v : Fin n → K) :
    pr2L j2 (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (j2 (v a)) := by
  letI : Algebra K L := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_iM K L n v

private theorem iM_cast {L : Type} [Field L] [Algebra ℂ L] {d : ℕ} (S : Finset (Fin d)) (q : ℕ)
    (h : S.card = q) (w : Fin d → Ω[L⁄ℂ]) :
    ExteriorAlgebra.ιMulti L q (fun j => w (S.orderEmbOfFin h j)) =
      ExteriorAlgebra.ιMulti L S.card (fun j => w (S.orderEmbOfFin rfl j)) := by
  subst h; rfl

theorem UpperTheory.Gal.productCup_of_system.dtPull_of :
    LocOne → ValBasic → DtPull := by
  intro hLO hVB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY e he T
  refine ⟨?_, ?_⟩
  · refine (mapDR_iM K K' _ _).trans ?_
    unfold dtS
    congr 1
    funext a
    rw [tt, tt, IsScalarTower.algebraMap_apply F K K']
  · obtain ⟨hle, ⟨ev, hev⟩, hbv, -⟩ := hVB K' (rB ℂ K' (xv x) {0}) e.1
    have hLoc := hLO F K' d x hY.covY hY.red e
    have htB : ∀ l, tt K' x l ∈ rB ℂ K' (xv x) {0} := fun l => tco_mem ℂ K' (xv x) l
    have ht0 : ∀ l, ev ⟨tt K' x l, hle (htB l)⟩ = 0 := fun l => by
      obtain ⟨h, hh⟩ := (hev _ _).1 (hbv ⟨tt K' x l, htB l⟩)
      exact hh.trans (e.2 l)
    choose g hgv hgt using hY.tan e he
    have hg : ∀ m l, ∃ h : g m l ∈ loc (rB ℂ K' (xv x) {0}) e.1, ev ⟨g m l, h⟩ = A e m l :=
      fun m l => (hev _ _).1 (hgv m l)
    choose hgl hge using hg
    choose c hcl hcD using fun m l => hLoc (g m l) (hgl m l)
    let ah : Matrix (Fin d) (Fin d) (loc (rB ℂ K' (xv x) {0}) e.1) := fun m l =>
      ⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩
    have hah : ∀ m l, (ah m l : K') = g m l + ∑ l', tt K' x l' * c m l' l := fun m l => by
      simp [ah]
    have hAh : ev.mapMatrix ah = A e := by
      ext m l
      change ev (⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩) = A e m l

      rw [map_add (f := _), map_sum, hge]
      simp only [map_mul, ht0, zero_mul, Finset.sum_const_zero, add_zero]
    have hD : ∀ m, D ℂ K' (j2 (tt K x m)) = ∑ l, (ah m l : K') • D ℂ K' (tt K' x l) := by
      intro m

      rw [hgt m, map_sum]
      simp_rw [hah, add_smul, Finset.sum_add_distrib, Derivation.leibniz, hcD, Finset.smul_sum,
        Finset.sum_smul, smul_smul]
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    refine ⟨fun S => if hS : S.card = T.card then
      (((ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det :
        loc (rB ℂ K' (xv x) {0}) e.1) : K') else 0, ?_, ?_⟩
    · have h1 : pr2L j2 (dtS K x T) = ExteriorAlgebra.ιMulti K' T.card (fun a =>
          ∑ l, (ah (T.orderEmbOfFin rfl a) l : K') • D ℂ K' (tt K' x l)) := by
        unfold dtS
        rw [pullback_kahler_iMulti]
        congr 1
        funext a
        exact hD _
      rw [h1, alt_expand (ExteriorAlgebra.ιMulti K' T.card)
        (fun a l => (ah (T.orderEmbOfFin rfl a) l : K')) (fun l => D ℂ K' (tt K' x l)),
        Finset.sum_subtype (Finset.univ.powersetCard T.card) (p := fun S => S.card = T.card)
          (by simp [Finset.mem_powersetCard])]
      refine Finset.sum_congr rfl fun S _ => ?_
      simp only [dif_pos S.2]
      rw [iM_cast S.1 T.card S.2 (fun l => D ℂ K' (tt K' x l))]
      unfold dtS
      congr 1
      exact ((loc (rB ℂ K' (xv x) {0}) e.1).val.map_det
        (ah.submatrix (T.orderEmbOfFin rfl) (S.1.orderEmbOfFin S.2))).symm
    · intro S hS
      simp only [dif_pos hS]
      refine (hev _ _).2 ⟨SetLike.coe_mem _, ?_⟩
      change ev (ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det = _
      rw [AlgHom.map_det, ← hAh]
      rfl
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma pk_mem' {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  rw [pk, dite_eq_left h]
  exact Finset.min'_mem I h

private lemma pk_zero' {d : ℕ} : pk ({0} : Finset (Fin (d + 1))) = 0 := by
  simp [pk]

private lemma inSp_sub {S κ κ' : Type} [CommRing S] [Algebra ℂ S] [Fintype κ] [Fintype κ']
    (R : Subalgebra ℂ S) (r : κ → S) (f : κ' → κ) {g : S} (h : InSp R (fun a => r (f a)) g) : InSp R r g := by
  classical
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨fun l => ∑ b ∈ Finset.univ.filter (fun b => f b = l), a b, fun l => R.sum_mem fun b _ => ha b, ?_⟩
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := f) (f := fun b => a b * r (f b))]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b hb => ?_
  rw [(Finset.mem_filter.mp hb).2]

private lemma inSp_self {S κ : Type} [CommRing S] [Algebra ℂ S] [Fintype κ]
    (R : Subalgebra ℂ S) (r : κ → S) (l : κ) : InSp R r (r l) := by
  classical
  refine ⟨fun l' => if l' = l then 1 else 0, fun l' => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · simp

private lemma col_of_kos (hRS : RS) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S) (I J : Finset (Fin (d + 1))) (m : ℤ)
    (h : (kos T.act (T.M I J) (T.r n z (pk I) (pk J))).Z m ≤ (kos T.act (T.M I J) (T.r n z (pk I) (pk J))).B m) :
    (T.colCx n z I J).Z m ≤ (T.colCx n z I J).B m := by
  intro c hc
  have H := hRS S E T.act κ (T.M I J) (T.u n (pk I) (pk J)) (T.r n z (pk I) (pk J)) z (fun l => rfl) m c
  exact H.2.2.1.2 (h (H.2.1.1 hc))

private lemma admissible_append {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ κ' : Type} [LinearOrder κ] [LinearOrder κ'] (n : κ → ℕ × ℕ) (z : κ → S)
    (n' : κ' → ℕ × ℕ) (z' : κ' → S) (h : T.admitted n z) (h' : T.admitted n' z') : T.admitted (app n n') (app z z') := by
  intro i j l
  rcases hl : ofLex l with a | a
  · have := h i j a
    simpa [Sys.r, Sys.u, app, hl] using this
  · have := h' i j a
    simpa [Sys.r, Sys.u, app, hl] using this

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private lemma gS_X (i : Fin (d + 1)) :
    Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K') ((sysZ K x 0).X i) = (sysY x j2 d).X i := by
  ext
  simp [sysZ, sysY, gS, ← IsScalarTower.algebraMap_apply]

private lemma gS_Y (i : Fin (d + 1)) :
    Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K') ((sysZ K x 0).Y i) = (sysY x j2 d).Y i := by
  ext
  simp [sysZ, sysY, gS]

private lemma gS_r {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) (i j : Fin (d + 1)) (k : κ) :
    gS j2 ((sysZ K x 0).r n z i j k) = (sysY x j2 d).r n (fun l => gS j2 (z l)) i j k := by
  simp only [Sys.r, Sys.u, map_mul]
  congr 1
  have := congrArg (fun v : K'ˣ => ((v⁻¹ : K'ˣ) : K'))
    (show Units.map ((gS j2 : K ⊗[ℂ] K →ₐ[ℂ] K') : K ⊗[ℂ] K →* K')
        ((sysZ K x 0).X i ^ (n k).1 * (sysZ K x 0).Y j ^ (n k).2) =
        (sysY x j2 d).X i ^ (n k).1 * (sysY x j2 d).Y j ^ (n k).2 by
      rw [map_mul, map_pow, map_pow, gS_X x j2, gS_Y x j2])
  simpa [Units.coe_map_inv] using this

private lemma rT (i j : Fin (d + 1)) (l : Fin d) (hi : i = 0) :
    (sysY x j2 d).r n10 (gT x j2) i j l = tt K' x l := by
  subst hi
  simp [Sys.r, Sys.u, n10, gT, sysY, tt, div_eq_mul_inv]

private lemma cols_gen (hKE : YKE) (hOk : SysOk) (hRS : RS) (h0 : Y0 x j2) (hG : (sysY x j2 d).Good)
    {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K') (ha : (sysY x j2 d).admitted n z)
    (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) :
    ((∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n z (pk I) (pk J) l) 0) →
        ∃ e0, Over x j2 e e0 ∧ ∀ l, InSp (loc (rB ℂ K' (xv x) {0}) e0.1) ((sysY x j2 d).r n z (pk I) (pk J)) (tt K' x l)) →
      KE ((sysY x j2 d).colCx n z I J) d) ∧
    ((∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, ¬ ∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n z (pk I) (pk J) l) 0) →
      ∀ m, ((sysY x j2 d).colCx n z I J).Z m ≤ ((sysY x j2 d).colCx n z I J).B m) := by
  have hr : ∀ l, (sysY x j2 d).r n z (pk I) (pk J) l ∈ RY (xv x) j2 I J :=
    ((hOk d K' (DR ℂ K') (sysY x j2 d) κ n z hG ha).2.1 I J _ (pk_mem' hI) _ (pk_mem' hJ)).1
  have hk := hKE F K K' d x j2 h0 κ ((sysY x j2 d).r n z (pk I) (pk J)) I J hI hr
  exact ⟨fun h m hm => col_of_kos hRS _ n z I J m (hk.1 h m hm),
    fun h m => col_of_kos hRS _ n z I J m fun c hc => hk.2.1 m c hc fun e he => absurd he (h e)⟩

end

theorem UpperTheory.Gal.productCup_of_system.yCols_of :
    YKE → PtG → PtT → FixLoc → GMap → ThMuLat → SysOk → RS → RYBasic → YCols := by
  intro hKE hPtG hPtT hFix hGM hTh hOk hRS hRY F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY κ _ _ n z hZ
  have h0 : Y0 x j2 := hY.toY0
  have hG : (sysY x j2 d).Good := (hRY F K K' d x j2 h0).2.1 d
  have hA0 : (sysY x j2 d).admitted n11 (sysY x j2 d).mu := (hTh d K' (DR ℂ K') (sysY x j2 d) hG).1
  have hAz : (sysY x j2 d).admitted n (fun l => gS j2 (z l)) := fun i j k => by
    have h2 := (hGM F K K' d x j2 h0 0 (Nat.zero_le _)).2.2.1 {i} {j} _ (hZ.adm i j k)
    rw [gS_r] at h2
    exact h2
  have hA1 : (sysY x j2 d).admitted (app n11 n) (gG x j2 z) := admissible_append _ _ _ _ _ hA0 hAz
  have hA2 : (sysY x j2 d).admitted n10 (gT x j2) := fun i j l => by
    have := hG.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) l.succ
    simpa [Sys.r, Sys.u, n10, gT] using this
  have hA3 : (sysY x j2 d).admitted (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) := admissible_append _ _ _ _ _ hA1 hA2
  refine ⟨hA1, hA2, hA3, fun I J hI hJ => ?_⟩
  have c1 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA1 I J hI hJ
  have c2 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA2 I J hI hJ
  have c3 := cols_gen x j2 hKE hOk hRS h0 hG _ _ hA3 I J hI hJ
  have hi := pk_mem' hI
  have hj := pk_mem' hJ
  have pG : ∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ,
      (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r (app n11 n) (gG x j2 z) (pk I) (pk J) l) 0) →
      J = {0} ∧ ∃ e0 ∈ Fx, Over x j2 e e0 :=
    fun e he => hPtG F K K' d x j2 Fx A hY κ n z hZ I J _ hi _ hj e he
  have pT : ∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ,
      (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J) l) 0) →
      ∃ e0, Over x j2 e e0 :=
    fun e he => hPtT F K K' d x j2 h0 I J _ hi _ hj e he
  refine ⟨c1.1 ?_, c2.1 ?_, c3.1 ?_, fun hne m => ⟨c1.2 ?_ m, c3.2 ?_ m⟩⟩
  · intro e he
    obtain ⟨hJ0, e0, he0, hO⟩ := pG e he
    refine ⟨e0, hO, fun l => ?_⟩
    rw [hO.1, hJ0, pk_zero']
    obtain ⟨N, -, -, -, hN⟩ := hFix F K K' d x j2 Fx A hY e0 he0
    exact inSp_sub _ ((sysY x j2 d).r (app n11 n) (gG x j2 z) 0 0) (fun a => toLex (Sum.inl (dj 0 a))) (hN l)
  · intro e he
    obtain ⟨e0, hO⟩ := pT e he
    refine ⟨e0, hO, fun l => ?_⟩
    rw [← rT x j2 (pk I) (pk J) l (by rw [hO.1, pk_zero'])]
    exact inSp_self _ _ l
  · intro e he
    obtain ⟨e0, hO⟩ := pT e fun l => he (toLex (Sum.inr l))
    refine ⟨e0, hO, fun l => ?_⟩
    rw [← rT x j2 (pk I) (pk J) l (by rw [hO.1, pk_zero'])]
    exact inSp_sub _ ((sysY x j2 d).r (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) (pk I) (pk J))
      (fun a => toLex (Sum.inr a)) (inSp_self _ ((sysY x j2 d).r n10 (gT x j2) (pk I) (pk J)) l)
  · intro e he
    obtain ⟨hJ0, e0, -, hO⟩ := pG e he
    exact hne.elim (fun h => h hO.1) (fun h => h hJ0)
  · intro e he
    obtain ⟨hJ0, e0, -, hO⟩ := pG e fun l => he (toLex (Sum.inl l))
    exact hne.elim (fun h => h hO.1) (fun h => h hJ0)
end
