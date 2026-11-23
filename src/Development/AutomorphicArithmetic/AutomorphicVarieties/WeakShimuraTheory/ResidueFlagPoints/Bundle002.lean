module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeMemDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.IrrOfStab
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem eq_one_of_res {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {x : R} {m : ℕ} (hm : IsUnit (m : R))
    (h1 : residue R x = 1) (hx : x ^ m = 1) : x = 1 := by
  have hs : IsUnit (∑ i ∈ Finset.range m, x ^ i) := by
    have h0 : residue R (∑ i ∈ Finset.range m, x ^ i) = residue R (m : R) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_pow, h1]
    by_contra hn
    have hmem : (∑ i ∈ Finset.range m, x ^ i) ∈ maximalIdeal R := hn
    rw [← residue_eq_zero_iff, h0] at hmem
    exact (residue_eq_zero_iff _).mp hmem hm
  have hg := geom_sum_mul x m
  rw [hx, sub_self] at hg
  exact sub_eq_zero.mp ((hs.mul_right_eq_zero).mp hg)

private theorem res_one_of_map {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (f : R →+* S) {x : R}
    (h : residue S (f x) = 1) : residue R x = 1 := by
  by_contra hn
  have hu : IsUnit (x - 1) := by
    by_contra hu
    exact hn (sub_eq_zero.mp (by rw [← map_one (residue R), ← map_sub]; exact (residue_eq_zero_iff _).mpr hu))
  have hfu := hu.map f
  rw [map_sub, map_one] at hfu
  have hz : residue S (f x - 1) = 0 := by rw [map_sub, h, map_one, sub_self]
  exact ((residue_eq_zero_iff _).mp hz) hfu

private theorem not_valuation_natCast_prime_lt_one_link {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) : ¬ (K.s.A K.s.v0).valuation (l : Ω) < 1 := by
  intro hv
  have hmem : (l : 𝓞 (W.Lp T.L)) ∈ K.s.v0.asIdeal := by
    rw [← K.s.hA K.s.v0 (l : 𝓞 (W.Lp T.L))]
    simpa using hv
  have hmax := K.s.v0.isMaximal
  letI : Field (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) := Ideal.Quotient.field _
  have hcard : Nat.card (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = K.s.p := K.s.norm_v0_eq_one
  have hfin : Finite (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact K.s.p_prime.ne_zero
  letI := Fintype.ofFinite (𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal)
  have hp0 : ((K.s.p : ℕ) : 𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hl0 : ((l : ℕ) : 𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    simpa using this
  have h1 := Nat.dvd_gcd (ringChar.dvd hp0) (ringChar.dvd hl0)
  rw [(Nat.coprime_primes K.s.p_prime (Fact.out)).mpr K.s.p_ne] at h1
  have h0 : ((1 : ℕ) : 𝓞 (W.Lp T.L) ⧸ K.s.v0.asIdeal) = 0 := (ringChar.spec _ 1).mpr h1
  simp at h0

theorem UpperTheory.V.Ws.Pt.ptUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g ∈ (T.fr ∅).N, r g = 1) → ∀ g ∈ Ine (F := T.L) (K.s.A K.s.v0), K.rhoQ n r g = 1 := by
  intro Ω _ _ _ l _ c D T c' h K n r hr g hg
  have hv := not_valuation_natCast_prime_lt_one_link K
  have hβ : K.β g = 1 := K.β_t (K.t_unr _ hv hg)
  obtain ⟨m, hcop, hm⟩ := K.tame
  have hchib : ∀ i, (K.r.chib i) (K.V.pr g) = 1 := fun i => K.v0.1 i (Subgroup.mem_map_of_mem K.V.pr hg)
  have hres : ∀ i, residue c'.O ((K.κ g : c'.O) * inc h ((chi D T.pr i) (resQ T.L g) : c.O)) = 1 := by
    intro i
    rw [← K.chib i g, hchib i, Units.val_one]
  have hi3 : ∃ i, lab T.pr i = 3 := by
    unfold lab
    split
    · exact ⟨1, rfl⟩
    · exact ⟨3, rfl⟩
  have hsurj : ∀ j, ∃ i, lab T.pr i = j := by
    unfold lab
    split
    · decide
    · intro j
      exact ⟨j, rfl⟩
  obtain ⟨i3, hi3⟩ := hi3
  have hκr : residue c'.O (K.κ g : c'.O) = 1 := by
    have h3 := hres i3
    have hc : (chi D T.pr i3) (resQ T.L g) = 1 := by
      simp [chi, hi3, Raw.ps]
    rw [hc, Units.val_one, map_one, mul_one] at h3
    exact h3
  have hκ : K.κ g = 1 := by
    apply Units.ext
    rw [Units.val_one]
    apply eq_one_of_res ((dvrFacts l c'.O).2.2.2.2.2.2.2.2 m ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)) hκr
    rw [← Units.val_pow_eq_pow_val, hm _ hv g hg, Units.val_one]
  have hps : ∀ j, residue c.O ((D.ps j) (resQ T.L g) : c.O) = 1 := by
    intro j
    obtain ⟨i, hi⟩ := hsurj j
    apply res_one_of_map (inc h)
    have h4 := hres i
    rw [map_mul, hκr, one_mul] at h4
    rw [← hi]
    exact h4
  have hrbar : D.rbar (resQ T.L g) = 1 := by
    unfold Raw.rbar Raw.r0
    ext a b
    simp only [GradeZeroInterpolatingElement.mapRep, GradeZeroInterpolatingElement.diagRep, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.one_apply]
    split_ifs with hab
    · subst hab
      show ((residue c.O).mapMatrix _) a a = 1
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq]
      exact hps a
    · show ((residue c.O).mapMatrix _) a b = 0
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hab, map_zero]
  have hN : resLe T.F_le g ∈ (T.fr ∅).N := by
    refine ⟨K.s.A K.s.v0, ?_, (resLe_mem_Ine T.F_le).mpr hg, hrbar⟩
    intro q hq
    have hq' : q = l := by simpa using hq
    subst hq'
    exact hv
  apply Units.ext
  rw [Link.rho_val, hr _ hN, Units.val_one]
  have htw : ((K.twc n) g : PadicAlgCl l) = 1 := by
    rw [Link.twc_val, hκ, hβ]
    simp
  rw [htw, one_smul]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem exists_resLe {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (g : G T.F Ω) (hg : g ∈ T.GalL) : ∃ s : G T.L Ω, resLe T.F_le s = g := by
  have h1 : resQ T.F g ∈ T.K.fixingSubgroup := hg
  have h2 : resQ T.F g ∈ T.F.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩
  have h3 : resQ T.F g ∈ T.L.fixingSubgroup := by
    have e : T.L.fixingSubgroup = T.F.fixingSubgroup ⊓ T.K.fixingSubgroup := by
      rw [T.hL]; exact IntermediateField.fixingSubgroup_sup
    rw [e]
    exact ⟨h2, h1⟩
  have h4 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h3
  exact ⟨{ g.toRingEquiv with commutes' := fun x => h4 x.1 x.2 }, AlgEquiv.ext fun _ => rfl⟩

theorem UpperTheory.V.Ws.Pt.ptIrr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (r : G T.F Ω →* M4 (PadicAlgCl l)), Irr (r.comp T.G'.subtype) → Irr r ∧ Af.IsIrr ((K.rhoQ n r).comp (cycBar T.L Ω l).ker.subtype) := by
  intro Ω _ _ _ l _ c D T c' h K n r hr
  constructor
  · have h1 : Submodule.span (PadicAlgCl l) (Set.range (r.comp T.G'.subtype)) = ⊤ := hr
    change Submodule.span (PadicAlgCl l) (Set.range r) = ⊤
    refine eq_top_iff.2 (h1.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨g, rfl⟩
    exact ⟨g.1, rfl⟩
  · have h2 := (auIrr (r.comp T.G'.subtype) ((r.comp (resLe T.F_le)).comp (cycBar T.L Ω l).ker.subtype) hr ?_).2
      ((K.twc n).comp (cycBar T.L Ω l).ker.subtype)
    · have e : (K.rhoQ n r).comp (cycBar T.L Ω l).ker.subtype =
          Af.tw ((r.comp (resLe T.F_le)).comp (cycBar T.L Ω l).ker.subtype).toHomUnits
            ((K.twc n).comp (cycBar T.L Ω l).ker.subtype) := by
        refine MonoidHom.ext fun g => Units.ext ?_
        rw [Af.tw_val]
        exact K.rho_val n r g
      rw [e]
      exact h2
    · intro g
      obtain ⟨s, hs⟩ := exists_resLe T g.1 g.2.1
      have hz : cycZ T.F Ω l g.1 = 1 := g.2.2
      have hk : s ∈ (cycBar T.L Ω l).ker := by
        rw [MonoidHom.mem_ker, ← cycBar_resLe T.F_le, hs, cycBar, MonoidHom.comp_apply, hz, map_one]
      refine ⟨⟨s, hk⟩, ?_⟩
      change r (resLe T.F_le s) = r g.1
      rw [hs]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

private theorem ptFlag_adj_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (u : M4 R) :
    adj (u.map f) = (adj u).map f := by
  ext i j
  simp only [Matrix.map_apply, adj_apply]
  rw [map_zsmul]

theorem UpperTheory.V.Ws.Pt.ptFlag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, ∀ v : W.Vl l T.L, W.HasFlag ((K.rhoQ n (X.P.map (y : X.A →+* PadicAlgCl l)).r).comp (Dec (F := T.L) (K.s.A v)).subtype) ((Link.pt φ y).psi v) := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y v
  have hpair := X.pair
  have hlow := hpair.low (K.e v)
  have hadj : adj (X.P.n (K.e v)) * X.P.n (K.e v) = 1 := Pp.adj_mul_self hlow.1
  have hr : ∀ t, (X.P.map (y : X.A →+* PadicAlgCl l)).r t = (X.P.r t).map (y : X.A →+* PadicAlgCl l) :=
    fun t => rfl
  have hu : adj ((X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) *
      (X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l) = 1 := by
    rw [ptFlag_adj_map, ← Matrix.map_mul, hadj,
      Matrix.map_one _ (map_zero (y : X.A →+* PadicAlgCl l)) (map_one (y : X.A →+* PadicAlgCl l))]
  have hu' := mul_eq_one_comm.mp hu
  have hM : ∀ t, adj ((X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) *
      (X.P.r t).map (y : X.A →+* PadicAlgCl l) * (X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)
      = (adj (X.P.n (K.e v)) * X.P.r t * X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l) := by
    intro t
    rw [ptFlag_adj_map, Matrix.map_mul, Matrix.map_mul]
  refine ⟨⟨_, _, hu, hu'⟩, fun s => ?_⟩
  have hs : resLe T.F_le (s : G T.L Ω) ∈ Dec (T.pl (K.e v)) := by
    rw [resLe_mem_Dec, ← K.hA v]
    exact s.2
  have hval : (((⟨_, _, hu, hu'⟩ * ((K.rhoQ n (X.P.map (y : X.A →+* PadicAlgCl l)).r).comp
      (Dec (F := T.L) (K.s.A v)).subtype) s * (⟨_, _, hu, hu'⟩)⁻¹ : GL (Fin 4) (PadicAlgCl l))) :
        Matrix (Fin 4) (Fin 4) (PadicAlgCl l))
      = (((K.twc n) (s : G T.L Ω) : (PadicAlgCl l)ˣ) : PadicAlgCl l) •
        (adj ((X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) *
          (X.P.r (resLe T.F_le (s : G T.L Ω))).map (y : X.A →+* PadicAlgCl l) *
          (X.P.n (K.e v)).map (y : X.A →+* PadicAlgCl l)) := by
    rw [Units.val_mul, Units.val_mul, MonoidHom.comp_apply, Subgroup.coe_subtype, Link.rho_val, hr]
    simp only [Units.inv_mk, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hval, Matrix.smul_apply, hM, Matrix.map_apply, hpair.flag (K.e v) _ hs i j hij, map_zero, smul_zero]
  · rw [hval, Matrix.smul_apply, hφ.psi_val y v i s hs, smul_eq_mul]
    rfl
end
