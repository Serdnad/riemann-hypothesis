module

public import Mathlib.RingTheory.Ideal.Height
public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim

@[expose] public section

namespace ReciprocityTheory.CA

open IsLocalRing

private theorem height_eq_order_height_lemma {R : Type*} [CommRing R] (I : Ideal R)
    [hI : I.IsPrime] : I.height = Order.height (⟨I, hI⟩ : PrimeSpectrum R) := by
  exact PrimeSpectrum.height_eq_orderHeight ⟨I, hI⟩

private theorem comap_map_mk_lemma_4 {R : Type*} [CommRing R] (I J : Ideal R) (h : I ≤ J) :
    Ideal.comap (Ideal.Quotient.mk I) (J.map (Ideal.Quotient.mk I)) = J := by
  ext z
  rw [Ideal.mem_comap]
  first
  | exact Ideal.mem_quotient_iff_mem h

private theorem height_le_height_Iic_lemma_2 {α β : Type*} [PartialOrder α] [Preorder β] (a : α)
    (f : Set.Iic a → β) (hf : StrictMono f) : Order.height a ≤ Order.height (f ⟨a, le_rfl⟩) := by
  have hmono : ∀ s : LTSeries α, Monotone s := fun s => by
    first
    | exact s.monotone
  have H : ∀ s : LTSeries α, s.last ≤ a → (s.length : ℕ∞) ≤ Order.height (f ⟨a, le_rfl⟩) := by
    intro s hs
    let t : LTSeries β :=
      { length := s.length
        toFun := fun i => f ⟨s i, (hmono s (Fin.le_last i)).trans hs⟩
        step := fun i => hf (Subtype.mk_lt_mk.mpr (s.step i)) }
    have ht : t.last ≤ f ⟨a, le_rfl⟩ := by
      show f ⟨s (Fin.last s.length), _⟩ ≤ f ⟨a, le_rfl⟩
      exact hf.monotone (show s (Fin.last s.length) ≤ a from hs)
    exact Order.length_le_height ht
  first
  | exact Order.height_le fun s hs => H s hs.le

private theorem krullDim_le_height_lemma_3 {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (hf : StrictMono f) (b : β) (hb : ∀ x, f x ≤ b) :
    Order.krullDim α ≤ (Order.height b : WithBot ℕ∞) := by
  unfold Order.krullDim
  refine iSup_le fun s => ?_
  have h := Order.length_le_height (p := s.map f hf) (x := b) (hb s.last)
  exact_mod_cast h

private theorem height_le_krullDim_lemma_6 {α : Type*} [Preorder α] (a : α) :
    (Order.height a : WithBot ℕ∞) ≤ Order.krullDim α := Order.height_le_krullDim a

theorem ringKrullDim_localization_quotient_eq_height {P : Type*} [CommRing P] (p q : Ideal P)
    [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))) =
      ((q.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) := by
  -- Quotienting the localization at q localizes P ⧸ p at the image of q.
  let Q := q.map (Ideal.Quotient.mk p)
  have : Q.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hcompl : Algebra.algebraMapSubmonoid (P ⧸ p) q.primeCompl = Q.primeCompl := by
    change q.primeCompl.map (Ideal.Quotient.mk p) = Q.primeCompl
    have hq : (Q.comap (Ideal.Quotient.mk p)).primeCompl = q.primeCompl := by
      ext x
      simp only [Ideal.mem_primeCompl_iff, Q, Ideal.comap_map_mk hpq]
    rw [← hq]
    exact Q.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective
  let R := Localization.AtPrime q ⧸ p.map (algebraMap P (Localization.AtPrime q))
  have : IsLocalization.AtPrime R Q := by
    change IsLocalization Q.primeCompl R
    rw [← hcompl]
    infer_instance
  exact IsLocalization.AtPrime.ringKrullDim_eq_height Q R

private theorem height_map_atPrime_lemma_5 {R : Type*} [CommRing R] (p q : Ideal R) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) [hp' : (p.map (algebraMap R (Localization.AtPrime q))).IsPrime] :
    (p.map (algebraMap R (Localization.AtPrime q))).height = p.height := by
  have hdisj : ∀ I : Ideal R, I ≤ q → Disjoint (q.primeCompl : Set R) (I : Set R) := fun I hI =>
    Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)
  rw [height_eq_order_height_lemma (p.map (algebraMap R (Localization.AtPrime q))),
    height_eq_order_height_lemma p]
  apply le_antisymm
  · let f : PrimeSpectrum (Localization.AtPrime q) → PrimeSpectrum R := fun x =>
      ⟨Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal, inferInstance⟩
    have hf : StrictMono f := by
      intro x y hxy
      show Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal <
        Ideal.comap (algebraMap R (Localization.AtPrime q)) y.asIdeal
      refine lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.map (algebraMap R (Localization.AtPrime q))) e
      rw [IsLocalization.map_under (M := q.primeCompl) (S := Localization.AtPrime q),
        IsLocalization.map_under (M := q.primeCompl) (S := Localization.AtPrime q)] at e2
      exact PrimeSpectrum.ext e2
    have hfp : f ⟨_, hp'⟩ = ⟨p, ‹p.IsPrime›⟩ := PrimeSpectrum.ext (by
      show Ideal.under R (p.map (algebraMap R (Localization.AtPrime q))) = p
      exact IsLocalization.under_map_of_isPrime_disjoint (M := q.primeCompl)
        (S := Localization.AtPrime q) ‹p.IsPrime› (hdisj p hpq))
    have h := Order.height_le_height_apply_of_strictMono f hf ⟨_, hp'⟩
    rwa [hfp] at h
  · let g : Set.Iic (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) → PrimeSpectrum (Localization.AtPrime q) :=
      fun x => ⟨x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)),
        IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq))⟩
    have hg : StrictMono g := by
      intro x y hxy
      show x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) <
        y.1.asIdeal.map (algebraMap R (Localization.AtPrime q))
      refine lt_of_le_of_ne (Ideal.map_mono (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.under R) e
      rw [IsLocalization.under_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq)),
        IsLocalization.under_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show y.1.asIdeal ≤ p from y.2).trans hpq))] at e2
      exact Subtype.ext (PrimeSpectrum.ext e2)
    exact height_le_height_Iic_lemma_2 _ g hg

theorem IsCM.height_eq_height_add_height_map_quotient {P : Type*} [CommRing P] [IsLocalRing P]
    (h : IsCM P) (p q : Ideal P) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  have hL := h.localization_atPrime q
  have hdisj : Disjoint (q.primeCompl : Set P) (p : Set P) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  have e := hL.height_add_ringKrullDim_quotient (p.map (algebraMap P (Localization.AtPrime q)))
  have e1 : (p.map (algebraMap P (Localization.AtPrime q))).height = p.height :=
    height_map_atPrime_lemma_5 p q hpq
  have e2 : ringKrullDim (Localization.AtPrime q) = q.height := by
    first
    | exact IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)
  rw [ringKrullDim_localization_quotient_eq_height p q hpq, e1, e2] at e
  exact_mod_cast e.symm

end ReciprocityTheory.CA
