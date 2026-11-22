import Mathlib

open Algebra

namespace ReciprocityTheory.CA

universe u

private theorem polynomial_maximalHeight (K : Type*) [Field K] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal] : m.height = n := by
  induction n with
  | zero =>
    let e := MvPolynomial.isEmptyRingEquiv K (Fin 0)
    rw [← e.height_map]
    have : (m.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [((m.map e).eq_bot_or_top.resolve_right
      (Ideal.IsMaximal.ne_top inferInstance)), Ideal.height_bot, Nat.cast_zero]
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let M := m.map e
    have : M.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q := M.under (MvPolynomial (Fin n) K)
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M
    have : M.LiesOver q := ⟨rfl⟩
    rw [← e.height_map, Polynomial.height_eq_height_add_one q M, ih q, Nat.cast_succ]

private theorem height_eq_under_of_integral {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  let p := P.under R
  have hmono : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
    intro q q' hqq'
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hqq' ⊢
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hqq'
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff hqq'.le ⟨hx, hx'⟩
      (Algebra.IsIntegral.isIntegral x)
  apply le_antisymm
  · obtain ⟨l, hlast, hlen⟩ := P.exists_ltSeries_length_eq_height
    let lifted := l.map (PrimeSpectrum.comap (algebraMap R S)) hmono
    have heq : lifted.last.asIdeal = p := by simp [lifted, hlast, p, Ideal.under_def]
    change P.height ≤ p.height
    rw [← heq, PrimeSpectrum.height_eq_orderHeight, ← hlen]
    exact Order.length_le_height_last (p := lifted)
  · obtain ⟨l, hlast, hlen⟩ := p.exists_ltSeries_length_eq_height
    have : P.LiesOver l.last.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hlast⟩
    obtain ⟨lifted, hlen', hlast', _⟩ := P.exists_ltSeries_of_hasGoingDown l
    have h := Order.length_le_height_last (p := lifted)
    rwa [hlen', hlen, ← PrimeSpectrum.height_eq_orderHeight, hlast'] at h

/-- A maximal ideal in a finite type domain over a field has height equal to
the transcendence degree. Noether normalization preserves the height by
incomparability and going down. -/
theorem height_eq_of_isMaximal_of_trdeg_eq
    {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (n : ℕ) (h : Algebra.trdeg K A = n) (m : Ideal A)
    [m.IsMaximal] : m.height = n := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  let B := MvPolynomial (Fin s) K
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hfin
  have : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hdeg := trdeg_add_eq K B (A := A)
  rw [trdeg_eq_zero (R := B) (A := A), add_zero, MvPolynomial.trdeg_of_isDomain] at hdeg
  have heq : s = n := by
    have he : (s : Cardinal.{u}) = n := by simpa using hdeg.trans h
    exact_mod_cast he
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have : (m.under B).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  rw [height_eq_under_of_integral (R := B), polynomial_maximalHeight, heq]

end ReciprocityTheory.CA
