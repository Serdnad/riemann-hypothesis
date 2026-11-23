module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CotDer
public import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsNontrivialCharacterPgroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle001
public import Mathlib.Algebra.DualNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Connected.Separation
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA
public import Lean.Meta.ExprDefEq

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem dual_der (O R K : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra O R] [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K]
    (y : R →ₐ[O] K) (hy : ∀ a ∈ maximalIdeal R, y a = 0) :
    ∃ (D : Fin (maximalIdeal R).spanFinrank → R →ₗ[O] K) (r : Fin (maximalIdeal R).spanFinrank → R),
      (∀ i, D i ∈ PtDer y K) ∧ ∀ i j, D i (r j) = if j = i then 1 else 0 := by
  classical
  let yb : ResidueField R →+* K :=
    Ideal.Quotient.lift (maximalIdeal R) y.toRingHom (fun a ha => hy a ha)
  have hyb : ∀ f : R, yb (algebraMap R (ResidueField R) f) = y f := fun f => rfl
  have h1 : ∀ c : O, yb (algebraMap O (ResidueField R) c) = algebraMap O K c := by
    intro c
    rw [← y.commutes c]
    rfl
  let ya : ResidueField R →ₐ[O] K := { yb with commutes' := h1 }
  have hyinj : Function.Injective yb := yb.injective
  have hinj : Function.Injective (algebraMap O (ResidueField R)) := by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective O K
    rw [← h1, ← h1, hab]
  have halg : Algebra.IsAlgebraic O (ResidueField R) :=
    Algebra.IsAlgebraic.of_injective ya hyinj
  obtain ⟨d, hd⟩ := UpperTheory.V.Ws.Eb.cotDer O R hinj halg
  have hn : Module.finrank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanFinrank :=
    (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm
  let b := Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R) hn
  have hsurj : ∀ j, ∃ a : maximalIdeal R, (maximalIdeal R).toCotangent a = b j :=
    fun j => (maximalIdeal R).toCotangent_surjective (b j)
  choose a ha using hsurj
  have hsm : ∀ (r : R) (v : CotangentSpace R) i,
      yb (b.coord i (r • v)) = y r * yb (b.coord i v) := by
    intro r v i
    rw [← algebraMap_smul (ResidueField R) r v, map_smul, smul_eq_mul, map_mul, hyb]
  let D : Fin (maximalIdeal R).spanFinrank → R →ₗ[O] K := fun i =>
    { toFun := fun f => yb (b.coord i (d f))
      map_add' := by
        intro f g
        simp only [map_add (f := _)]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz, Derivation.map_algebraMap,
          smul_zero, add_zero, hsm, y.commutes, Algebra.smul_def] }
  refine ⟨D, fun j => (a j : R), ?_, ?_⟩
  · intro i
    intro f g
    show yb (b.coord i (d (f * g))) = y f • yb (b.coord i (d g)) + y g • yb (b.coord i (d f))
    rw [Derivation.leibniz, map_add (f := _), map_add (f := _), hsm, hsm, smul_eq_mul, smul_eq_mul]
  · intro i j
    show yb (b.coord i (d (a j : R))) = _
    rw [hd, ha, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Ws.Eb.tanEmb :
    ∀ (O B K : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing B] [IsNoetherianRing B] [Algebra O B] [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (x : B →ₐ[O] K) (p : Ideal B) [p.IsPrime], p = RingHom.ker x →
        ∀ N : ℕ, Module.rank K (PtDer x K) ≤ N → (maximalIdeal (Localization.AtPrime p)).spanFinrank ≤ N := by
  intro O B K _ _ _ _ _ _ _ _ _ _ x p _ hp N hN
  classical
  let R := Localization.AtPrime p
  have hker : ∀ b : B, b ∈ p ↔ x b = 0 := by
    intro b
    rw [hp]
    exact Iff.rfl
  have hunit : ∀ s : p.primeCompl, IsUnit (x s) := by
    intro s
    apply IsUnit.mk0
    intro h0
    exact s.2 ((hker s).2 h0)
  let y : R →ₐ[O] K := IsLocalization.liftAlgHom (M := p.primeCompl) (f := x) hunit
  have hyx : ∀ b : B, y (algebraMap B R b) = x b := fun b => IsLocalization.lift_eq _ _
  have hy : ∀ a ∈ maximalIdeal R, y a = 0 := by
    intro a ha
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
    have hb : b ∈ p := by
      rwa [IsLocalization.AtPrime.mk'_mem_maximal_iff R p] at ha
    have h1 := congrArg y (IsLocalization.mk'_spec R b s)
    rw [map_mul, hyx, hyx, (hker b).1 hb] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hunit s).ne_zero
  obtain ⟨D, r, hD, hDr⟩ := dual_der O R K y hy
  have hDl : ∀ i (u w : R), D i (u * w) = y u * D i w + y w * D i u := by
    intro i u w
    have := hD i u w
    rwa [smul_eq_mul, smul_eq_mul] at this
  let L : B →ₗ[O] R := (IsScalarTower.toAlgHom O B R).toLinearMap
  have hL : ∀ b, L b = algebraMap B R b := fun b => rfl
  have hmem : ∀ i, (D i).comp L ∈ PtDer x K := by
    intro i f g
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hL, hL, hL, map_mul,
      hDl, hyx, hyx, smul_eq_mul, smul_eq_mul]
  let v : Fin (maximalIdeal R).spanFinrank → PtDer x K := fun i => ⟨(D i).comp L, hmem i⟩
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let E : R → K := fun a => ∑ i, g i * D i a
    have hE : ∀ u w : R, E (u * w) = y u * E w + y w * E u := by
      intro u w
      simp only [E, hDl, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> ring
    have hB : ∀ b : B, E (algebraMap B R b) = 0 := by
      intro b
      have := congrArg (fun w : PtDer x K => (w : B →ₗ[O] K) b) hg
      simpa [v, E, hL] using this
    have hR : ∀ a : R, E a = 0 := by
      intro a
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
      have h1 := hB b
      rw [← IsLocalization.mk'_spec R b s, hE, hB, mul_zero, zero_add, hyx] at h1
      exact (mul_eq_zero.mp h1).resolve_left (hunit s).ne_zero
    intro j
    have := hR (r j)
    simpa [E, hDr] using this
  have hc := hli.cardinal_le_rank
  rw [Cardinal.mk_fintype, Fintype.card_fin] at hc
  exact_mod_cast hc.trans hN
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem vb_coeff {K : Type} [NormedField K] [IsUltrametricDist K] (a : K) (ha : ‖a‖ ≤ 1) (s : Multiset K)
    (hs : ∀ t ∈ s, ‖t - a‖ < 1) :
    ∀ i, ‖((s.map fun t => X - C t).prod - (X - C a) ^ s.card).coeff i‖ < 1 ∧ ‖((X - C a) ^ s.card).coeff i‖ ≤ 1 := by
  have step : ∀ (P : K[X]) (b : K) (r : ℝ → Prop), (∀ x y, x ≤ max y y → r y → r x) → r 0 → (∀ x y, r x → r y → r (max x y)) →
      ‖b‖ ≤ 1 → (∀ i, r ‖P.coeff i‖) → ∀ i, r ‖((X - C b) * P).coeff i‖ := by
    intro P b r h1 h0 h2 hb hP i
    have h3 : r ‖(X * P).coeff i‖ := by
      cases i with
      | zero => simpa using h0
      | succ i => simpa using hP i
    have h4 : r ‖b * P.coeff i‖ := h1 _ _ (by
      rw [max_self, norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hb) (hP i)
    rw [sub_mul, coeff_sub, coeff_C_mul]
    refine h1 _ _ ?_ (h2 _ _ h3 h4)
    rw [max_self, sub_eq_add_neg]
    simpa using IsUltrametricDist.norm_add_le_max ((X * P).coeff i) (-(b * P.coeff i))
  induction s using Multiset.induction_on with
  | empty =>
    intro i
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, sub_self, coeff_zero, norm_zero,
      zero_lt_one, true_and, coeff_one]
    split_ifs <;> simp
  | cons t s ih =>
    have ih' := ih fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    have hta := hs t (Multiset.mem_cons_self _ _)
    have ht : ‖t‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (t - a) a
      rw [sub_add_cancel] at this
      exact this.trans (max_le hta.le ha)
    intro i
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    refine ⟨?_, step _ a (· ≤ 1) (fun x y h h' => h.trans (by simpa using h')) zero_le_one
      (fun x y => max_le) ha (fun j => (ih' j).2) i⟩
    have e : (X - C t) * (s.map fun t => X - C t).prod - (X - C a) * (X - C a) ^ s.card =
        (X - C t) * ((s.map fun t => X - C t).prod - (X - C a) ^ s.card) + C (a - t) * (X - C a) ^ s.card := by
      rw [map_sub]; ring
    rw [e, coeff_add, coeff_C_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · exact step _ t (· < 1) (fun x y h h' => h.trans_lt (by simpa using h')) zero_lt_one
        (fun x y => max_lt) ht (fun j => (ih' j).1) i
    · rw [norm_mul, norm_sub_rev]
      exact (mul_le_of_le_one_right (norm_nonneg _) (ih' i).2).trans_lt hta

attribute [-instance] UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing in
theorem UpperTheory.V.Ws.Eb.inertia_trivial_of_charpoly_roots_near_character :
    ∀ {p l : ℕ} [Fact p.Prime] [Fact l.Prime], p ≠ l → ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] (φ : H →* Formalism.BasicNotions.Loc.GQ p), Topology.IsOpenEmbedding φ → ∀ (c : Coef l) (κ : H →* (ResidueField c.O)ˣ), (∀ g, φ g ∈ Loc.Iq p → κ g = 1) → (∃ g, residue c.O (Loc.cycA p l c.O (φ g) : c.O) ≠ 1) →
        ∀ {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ → (∀ g (a : c.O), residue c.O a = κ g → ∀ t ∈ (W.mat ρ g).charpoly.roots, ‖t - (a : PadicAlgCl l)‖ < 1) → ∀ g, φ g ∈ Loc.Iq p → ρ g = 1 := by
  intro p l _ hl hpl H _ _ _ _ φ hφ c κ hκ hω n ρ hρ hroot
  haveI : T2Space H := hφ.isEmbedding.t2Space
  obtain ⟨c', Q, r₀, hle, hQ, hcont⟩ := UpperTheory.V.Ws.Eb.intModel c ρ hρ
  obtain ⟨hcpl, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c'.O
  haveI : Finite (ResidueField c'.O) := hfin
  haveI : CharP (ResidueField c'.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c'.O), residue_eq_zero_iff]
    exact hlm
  let y : c.O →+* c'.O := (Subalgebra.inclusion hle : c.O →+* c'.O)
  haveI : IsLocalHom y := ⟨fun x hx => by
    by_contra hn
    have h3 : y x ∈ maximalIdeal c'.O :=
      (UpperTheory.V.Fr.sc_norm l c' (y x)).2.2 ((UpperTheory.V.Fr.sc_norm l c x).2.1 hn)
    exact h3 hx⟩
  let f : ResidueField c.O →+* ResidueField c'.O := ResidueField.map y
  have hf : ∀ x, f (residue c.O x) = residue c'.O (y x) := fun x => ResidueField.map_residue y x
  have hQ' : ∀ g, W.pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = Q⁻¹ * ρ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  have main := (UpperTheory.V.Loc.v0b hpl φ hφ c'.O (W.pushCh f κ) (fun g hg => by simp [hκ g hg]) ?_ r₀
    (fun N i j => hcont i j N) ?_).1
  · intro g hg
    have h3 := hQ g
    rw [MonoidHom.comp_apply, main g hg, map_one, mul_one] at h3
    exact mul_right_cancel (h3.trans (one_mul Q).symm)
  · obtain ⟨g, hg⟩ := hω
    refine ⟨g, fun h => hg (f.injective ?_)⟩
    rw [map_one, ← h, hf]
    rfl
  · intro g
    obtain ⟨a, ha⟩ := residue_surjective (R := c.O) (κ g : ResidueField c.O)
    have e1 : (r₀ g).val.charpoly.map (algebraMap c'.O (PadicAlgCl l)) =
        (W.mat ρ g).charpoly := by
      rw [← Matrix.charpoly_map]
      have e2 : (r₀ g).val.map (algebraMap c'.O (PadicAlgCl l)) =
          (Q⁻¹ * ρ g * Q : GL (Fin n) (PadicAlgCl l)).val := by
        rw [← hQ']
        rfl
      rw [e2, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]
      rfl
    have hsp : (W.mat ρ g).charpoly.Splits := IsAlgClosed.splits _
    have hcard : (W.mat ρ g).charpoly.roots.card = n := by
      rw [← hsp.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hprod := hsp.eq_prod_roots_of_monic (Matrix.charpoly_monic _)
    have key := vb_coeff (a : PadicAlgCl l) (UpperTheory.V.Fr.sc_norm l c a).1 _ (hroot g a ha)
    rw [← hprod, hcard, ← e1] at key
    have e3 : ((W.pushCh f κ g : (ResidueField c'.O)ˣ) : ResidueField c'.O) = residue c'.O (y a) := by
      rw [← hf, ha]; rfl
    have e4 : (X - C (residue c'.O (y a))) ^ n = ((X - C (y a)) ^ n).map (residue c'.O) := by simp
    rw [Matrix.charpoly_map, e3, e4, ← sub_eq_zero, ← Polynomial.map_sub]
    ext i
    rw [coeff_map, coeff_zero, residue_eq_zero_iff, (UpperTheory.V.Fr.sc_norm l c' _).2]
    have e5 : (X - C (a : PadicAlgCl l)) ^ n = ((X - C (y a)) ^ n).map (algebraMap c'.O (PadicAlgCl l)) := by
      rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]; rfl
    have h6 := (key i).1
    rw [e5, ← Polynomial.map_sub, coeff_map] at h6
    exact h6
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem rn_root {K : Type} [NormedField K] [IsUltrametricDist K] (p : K[X]) (hp : p.Monic)
    (hc : ∀ i < p.natDegree, ‖p.coeff i‖ < 1) (s : K) (hs : p.eval s = 0) : ‖s‖ < 1 := by
  by_contra hlt
  push_neg at hlt
  have sumlt : ∀ (t : Finset ℕ) (f : ℕ → K) (r : ℝ), 0 < r → (∀ i ∈ t, ‖f i‖ < r) → ‖∑ i ∈ t, f i‖ < r := by
    intro t f r hr
    induction t using Finset.induction_on with
    | empty => intro _; simpa using hr
    | insert j t hj ih =>
      intro hf
      rw [Finset.sum_insert hj]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hf j (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))
  have hsum : p.eval s = s ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i := by
    conv_lhs => rw [hp.as_sum]
    simp [eval_finsetSum]
  have hpos : 0 < ‖s‖ := lt_of_lt_of_le one_pos hlt
  have hlt2 : ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i‖ < ‖s‖ ^ p.natDegree := by
    apply sumlt _ _ _ (pow_pos hpos _)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    calc ‖p.coeff i‖ * ‖s‖ ^ i < 1 * ‖s‖ ^ i :=
          mul_lt_mul_of_pos_right (hc i hi) (pow_pos hpos _)
      _ = ‖s‖ ^ i := one_mul _
      _ ≤ ‖s‖ ^ p.natDegree := pow_le_pow_right₀ hlt hi.le
  have heq : s ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i * s ^ i := by
    rw [hs] at hsum
    exact eq_neg_of_add_eq_zero_left hsum.symm
  have h3 := congrArg norm heq
  rw [norm_neg, norm_pow] at h3
  rw [h3] at hlt2
  exact lt_irrefl _ hlt2

theorem UpperTheory.V.Ws.Eb.rootsNear :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.B →ₐ[c.O] PadicAlgCl l) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)), B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ) →
        ∀ g (a : c.O), (∀ i, residue c.O a = r.chib i g) → ∀ t ∈ (W.mat ρ g).charpoly.roots, ‖t - (a : PadicAlgCl l)‖ < 1 := by
  intro l _ F c n r B x ρ hD g a ha t ht
  have hsing : ∀ {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A'),
      MonoidAlgebra.mapRingHom F.G₀ f (MonoidAlgebra.single g 1) = MonoidAlgebra.single g 1 := by
    intro A A' _ _ f
    simp [MonoidAlgebra.mapRingHom]
  set Q := B.u.D.chi (MonoidAlgebra.single g 1) with hQ
  have hx : (W.mat ρ g).charpoly = Q.map (x : B.B →+* PadicAlgCl l) := by
    have h1 := (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* PadicAlgCl l)).1 (MonoidAlgebra.single g 1)
    rw [hsing, hD, (AlgebraTools.Det.repApi (W.mat ρ)).2.1] at h1
    exact h1
  have hred : Q.map (res c.O B.B : B.B →+* ResidueField c.O) = (X - C (residue c.O a)) ^ n := by
    have h1 := (AlgebraTools.Det.mapApi B.u.D (res c.O B.B : B.B →+* ResidueField c.O)).1 (MonoidAlgebra.single g 1)
    rw [hsing, B.u.red, W.Resid.Dbar, (AlgebraTools.Det.repApi _).2.1] at h1
    rw [← h1]
    show (Matrix.diagonal _).charpoly = _
    rw [Matrix.charpoly_diagonal]
    simp [← ha]
  set Q' := Q.comp (X + C (algebraMap c.O B.B a)) with hQ'
  set p := (W.mat ρ g).charpoly.comp (X + C (a : PadicAlgCl l)) with hp
  have hpQ : p = Q'.map (x : B.B →+* PadicAlgCl l) := by
    rw [hp, hQ', hx, Polynomial.map_comp]
    simp
  have hQm : ∀ i < n, Q'.coeff i ∈ maximalIdeal B.B := by
    intro i hi
    rw [← res_eq_zero_iff c.O B.B, ← RingHom.coe_coe (res c.O B.B), ← Polynomial.coeff_map, hQ',
      Polynomial.map_comp, hred]
    simp [ResidueField.algebraMap_eq, Polynomial.coeff_X_pow, hi.ne]
  obtain ⟨_, a0, ha1, _, hb⟩ := (coPt c B.B).1 x
  have hmon : p.Monic := (Matrix.charpoly_monic _).comp_X_add_C _
  have hdeg : p.natDegree = n := by
    rw [hp, Polynomial.natDegree_comp, Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_X_add_C]
    simp
  have hc : ∀ i < p.natDegree, ‖p.coeff i‖ < 1 := by
    intro i hi
    rw [hdeg] at hi
    rw [hpQ, Polynomial.coeff_map]
    have := hb 1 _ (by rw [pow_one]; exact hQm i hi)
    rw [pow_one] at this
    exact this.trans_lt ha1
  have hroot : p.eval (t - (a : PadicAlgCl l)) = 0 := by
    rw [hp, Polynomial.eval_comp]
    simp only [eval_add, eval_X, eval_C, sub_add_cancel]
    exact (Polynomial.mem_roots'.mp ht).2
  exact rn_root p hmon hc _ hroot
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.dimLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] B) (J : Ideal B), ((Ideal.Quotient.mk J).comp (f : MvPowerSeries (Fin N) c.O →+* B)).Finite → (∀ a, a ≠ 0 → ∀ b, f a * b ∈ J → b ∈ J) →
        ∀ (x : B →ₐ[c.O] PadicAlgCl l) (p : Ideal B) [p.IsPrime], p = RingHom.ker x → J ≤ p → (N : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p ⧸ J.map (algebraMap B (Localization.AtPrime p))) := by
  intro l _ c N B _ _ _ f J hfin hreg x p _ hpx hJp
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_minimalPrimes_le hJp
  haveI hPprime : P.IsPrime := hP.1.1
  have hJP : J ≤ P := hP.1.2
  haveI : IsCO c.O (B ⧸ P) :=
    co_quot c.O B (B ⧸ P) (Ideal.Quotient.mkₐ c.O P) Ideal.Quotient.mk_surjective
  set g : MvPowerSeries (Fin N) c.O →ₐ[c.O] B ⧸ P := (Ideal.Quotient.mkₐ c.O P).comp f with hg
  have hinj : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    have hmem : f a ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    obtain ⟨y, hyJ, hy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hmem
    exact hyJ (hreg a hne y hy)
  have hfinP : (g : MvPowerSeries (Fin N) c.O →+* B ⧸ P).Finite := by
    have h2 := (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJP)).comp hfin
    convert h2 using 1
    exact RingHom.ext fun a => rfl
  have hxP : ∀ a ∈ P, x a = 0 := fun a ha => by
    have h3 : a ∈ RingHom.ker x := hpx ▸ hPp ha
    exact h3
  set xb : B ⧸ P →ₐ[c.O] PadicAlgCl l := Ideal.Quotient.liftₐ P x hxP with hxb
  have hxbmk : ∀ b, xb (Ideal.Quotient.mk P b) = x b := fun b => rfl
  have hht := htLow c N (B ⧸ P) g hinj hfinP xb
  set q : Ideal (B ⧸ P) := RingHom.ker xb with hq
  haveI : q.IsPrime := RingHom.ker_isPrime _
  have hpq : p = Ideal.comap (Ideal.Quotient.mk P) q := by
    ext b
    rw [hpx, Ideal.mem_comap, hq, RingHom.mem_ker, RingHom.mem_ker, hxbmk]
  let φ := Localization.localRingHom p q (Ideal.Quotient.mk P) hpq
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : B ⧸ P)
    have hs'p : s' ∈ p.primeCompl := by
      intro h
      apply s.2
      rw [hpq] at h
      rw [← hs']
      exact h
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) r' ⟨s', hs'p⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  have hker : ∀ a ∈ J.map (algebraMap B (Localization.AtPrime p)), φ a = 0 := by
    intro a ha
    have hle : J.map (algebraMap B (Localization.AtPrime p)) ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [Localization.localRingHom_to_map]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJP hb), map_zero]
    exact hle ha
  have hψ := Ideal.Quotient.lift_surjective_of_surjective _ hker hφ
  have hdim := ringKrullDim_le_of_surjective _ hψ
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at hdim
  calc (N : WithBot ℕ∞) ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ ≤ _ := hdim
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.derZero :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (x' : R →ₐ[c.O] DualNumber (PadicAlgCl l)) (S : Set R), (∀ (N : ℕ) (a : R), ∃ b ∈ Algebra.adjoin c.O S, a - b ∈ maximalIdeal R ^ N) → (∀ a ∈ S, (x' a).snd = 0) → ∀ a, (x' a).snd = 0 := by
  intro l _ c R _ _ _ x' S hdense hS a
  have hadj : ∀ b ∈ Algebra.adjoin c.O S, (x' b).snd = 0 := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS x hx
    | algebraMap r =>
      rw [AlgHom.commutes]
      first
        | rfl
        | simp [TrivSqZeroExt.algebraMap_eq_inl']
    | add x y _ _ hx hy => rw [map_add (f := _), TrivSqZeroExt.snd_add, hx, hy, add_zero]
    | mul x y _ _ hx hy => simp [map_mul, TrivSqZeroExt.snd_mul, hx, hy]
  have hcont := ((coPt c R).2 x').2
  by_contra h
  have hpos : 0 < ‖(x' a).snd‖ := norm_pos_iff.mpr h
  obtain ⟨n, hn⟩ := hcont _ (half_pos hpos)
  obtain ⟨b, hb, hab⟩ := hdense n a
  have key := hn _ hab
  rw [map_sub, TrivSqZeroExt.snd_sub, hadj b hb, sub_zero] at key
  linarith
end
