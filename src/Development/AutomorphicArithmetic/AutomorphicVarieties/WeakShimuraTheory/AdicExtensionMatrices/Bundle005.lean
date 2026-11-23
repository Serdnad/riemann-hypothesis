module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ResLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicMat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle004
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
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem near_of_adjoin {P L : Type} [CommRing P] [CommRing L] [Algebra P L] (G : Set L)
    (hG : ∀ g ∈ G, IsNilpotent g) (x : L) (hx : x ∈ Algebra.adjoin P G) :
    ∃ p : P, IsNilpotent (x - algebraMap P L p) :=
  _root_.UpperTheory.Reformulated.B.Qg2.near_of_adjoin G hG x hx

private theorem unit_of_near {S : Type} [CommRing S] {x u : S} (h : IsNilpotent (x - u)) (hu : IsUnit u) :
    IsUnit x := by
  have := h.isUnit_add_right_of_commute hu (Commute.all _ _)
  simpa using this

private theorem local_of_near {P S : Type} [CommRing P] [IsLocalRing P] [CommRing S] [Nontrivial S] [Algebra P S]
    (h : ∀ x : S, ∃ p : P, IsNilpotent (x - algebraMap P S p)) : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨p, hp⟩ := h x
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self p with hu | hu
  · exact Or.inl (unit_of_near hp (hu.map _))
  · refine Or.inr (unit_of_near (u := algebraMap P S (1 - p)) ?_ (hu.map _))
    have := hp.neg
    convert this using 1
    rw [map_sub, map_one]; ring

private theorem nil_mem_max {S : Type} [CommRing S] [IsLocalRing S] {x : S} (h : IsNilpotent x) :
    x ∈ maximalIdeal S := fun hu => by
  obtain ⟨n, hn⟩ := h
  exact not_isUnit_zero (hn ▸ hu.pow n)

private theorem bound_fin {R : Type} [CommRing R] (S : Subalgebra (PowerSeries R) (LaurentSeries R))
    [Module.Finite (PowerSeries R) S] :
    ∃ N : ℕ, ∀ y ∈ S, ∃ q : PowerSeries R,
      algebraMap (PowerSeries R) (LaurentSeries R) q = (PowerSeries.X : PowerSeries R) ^ N • y := by
  have hfg : S.toSubmodule.FG := Module.Finite.iff_fg.1 ‹_›
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨⟨b, N, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (Submonoid.powers (PowerSeries.X : PowerSeries R)) t
  refine ⟨N, fun y hy => ?_⟩
  have hy' : y ∈ Submodule.span (PowerSeries R) (t : Set (LaurentSeries R)) := by
    rw [ht]; exact hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem g hg => exact hb g hg
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, by rw [map_add (f := _), hp, hq, smul_add]⟩
  | smul r a _ ha =>
    obtain ⟨p, hp⟩ := ha
    exact ⟨r * p, by rw [map_mul, hp, ← Algebra.smul_def, smul_comm]⟩

private theorem alg_monomial {R : Type} [CommRing R] (n : ℕ) (x : R) :
    algebraMap (PowerSeries R) (LaurentSeries R) (PowerSeries.C x * PowerSeries.X ^ n)
      = HahnSeries.single (n : ℤ) x := by
  show HahnSeries.ofPowerSeries ℤ R _ = _
  rw [map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

theorem UpperTheory.V.Ws.sxLaur :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R], IsNilpotent (maximalIdeal R) → ∀ c : ℕ, ∃ (S : Type) (_ : CommRing S) (_ : Algebra Λ S) (_ : IsCO Λ S) (e : S →+* LaurentSeries R), Laur (Λ := Λ) c e := by
  intro Λ _ _ R _ _ hR hnil c
  haveI hP : IsCO Λ (PowerSeries R) := co_mvps Λ R Unit
  have hnilx : ∀ x ∈ maximalIdeal R, IsNilpotent x := fun x hx => by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    have := Ideal.pow_mem_pow hx k
    rw [hk] at this
    simpa using this
  have hnils : ∀ (n : ℤ), ∀ x ∈ maximalIdeal R, IsNilpotent (HahnSeries.single n x : LaurentSeries R) :=
    fun n x hx => by
      obtain ⟨k, hk⟩ := hnilx x hx
      exact ⟨k, by rw [HahnSeries.single_pow, hk, map_zero]⟩
  obtain ⟨s, hs⟩ : (maximalIdeal R).FG := IsNoetherian.noetherian _
  let G : Set (LaurentSeries R) := (fun x => HahnSeries.single (-(c : ℤ)) x) '' (s : Set R)
  have hGfin : G.Finite := s.finite_toSet.image _
  have hG : ∀ g ∈ G, IsNilpotent g := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnils _ x (hs ▸ Ideal.subset_span hx)
  let S := Algebra.adjoin (PowerSeries R) G
  haveI hfin : Module.Finite (PowerSeries R) S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hGfin fun g hg => by
      obtain ⟨k, hk⟩ := hG g hg
      exact ⟨X ^ k, monic_X_pow k, by simp [hk]⟩
  have hnear : ∀ x : S, ∃ p : PowerSeries R, IsNilpotent (x - algebraMap _ S p) := fun x => by
    obtain ⟨p, k, hk⟩ := near_of_adjoin G hG x.1 x.2
    exact ⟨p, k, Subtype.ext hk⟩
  haveI : IsLocalRing S := local_of_near hnear
  letI : Algebra Λ S := ((algebraMap (PowerSeries R) S).comp (algebraMap Λ (PowerSeries R))).toAlgebra
  haveI : IsScalarTower Λ (PowerSeries R) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcomap : (maximalIdeal S).comap (algebraMap (PowerSeries R) S) = maximalIdeal (PowerSeries R) :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal S))
  have hin : ∀ p ∈ maximalIdeal (PowerSeries R), algebraMap _ S p ∈ maximalIdeal S := fun p hp => by
    rw [← hcomap] at hp; exact hp
  haveI hS : IsCO Λ S := co_finite Λ (PowerSeries R) S fun x => by
    obtain ⟨p, hp⟩ := hnear x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := Λ) p
    refine ⟨a, ?_⟩
    have := (maximalIdeal S).add_mem (nil_mem_max hp) (hin _ ha)
    convert this using 1
    rw [map_sub, ← IsScalarTower.algebraMap_apply]; ring
  have hXmax : (PowerSeries.X : PowerSeries R) ∈ maximalIdeal (PowerSeries R) := fun hu => by
    have := PowerSeries.isUnit_constantCoeff _ hu
    simp at this
  refine ⟨S, inferInstance, inferInstance, hS, S.val.toRingHom, Subtype.val_injective, fun x => ?_, ?_, ?_⟩
  · have := alg_monomial 0 (algebraMap Λ R x)
    rw [pow_zero, mul_one, ← PowerSeries.algebraMap_apply] at this
    exact this
  · rintro n x (hn | ⟨hn, hx⟩)
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
      refine ⟨algebraMap _ S (PowerSeries.C x * PowerSeries.X ^ k), hin _ ?_, alg_monomial k x⟩
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hXmax k (by exact_mod_cast hn))
    · have h1 : ∀ x ∈ Ideal.span (s : Set R), (HahnSeries.single (-(c : ℤ)) x : LaurentSeries R) ∈ S := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem g hg => exact Algebra.subset_adjoin ⟨g, hg, rfl⟩
        | zero => rw [map_zero]; exact S.zero_mem
        | add a b _ _ ha hb => rw [HahnSeries.single_add]; exact S.add_mem ha hb
        | smul r a _ ha =>
          have := S.mul_mem (S.algebraMap_mem (PowerSeries.C r * PowerSeries.X ^ 0)) ha
          rw [alg_monomial, HahnSeries.single_mul_single] at this
          simpa using this
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (a := n + c) (by omega)
      have h2 := S.mul_mem (S.algebraMap_mem (PowerSeries.C 1 * PowerSeries.X ^ k)) (h1 x (hs ▸ hx))
      rw [alg_monomial, HahnSeries.single_mul_single, one_mul, ← hk, add_neg_cancel_right] at h2
      obtain ⟨j, hj⟩ := hnils n x hx
      exact ⟨⟨_, h2⟩, nil_mem_max ⟨j, Subtype.ext hj⟩, rfl⟩
  · intro n
    obtain ⟨N, hN⟩ := bound_fin S
    have hrad : maximalIdeal S ≤ (Ideal.span {algebraMap (PowerSeries R) S PowerSeries.X}).radical := by
      intro y hy
      obtain ⟨p, hp⟩ := hnear y
      have hp0 : PowerSeries.constantCoeff p ∈ maximalIdeal R := fun hu =>
        hy (unit_of_near hp ((PowerSeries.isUnit_iff_constantCoeff.2 hu).map _))
      obtain ⟨q, hq⟩ : (PowerSeries.X : PowerSeries R) ∣ p - PowerSeries.C (PowerSeries.constantCoeff p) :=
        PowerSeries.X_dvd_iff.2 (by simp)
      have e1 : y = (y - algebraMap _ S p) + algebraMap _ S (PowerSeries.C (PowerSeries.constantCoeff p))
          + algebraMap (PowerSeries R) S PowerSeries.X * algebraMap _ S q := by
        rw [← map_mul, ← hq, map_sub]; ring
      have hz : ∀ z : S, IsNilpotent z →
          z ∈ (Ideal.span {algebraMap (PowerSeries R) S PowerSeries.X}).radical := fun z ⟨k, hk⟩ =>
        ⟨k, hk ▸ Ideal.zero_mem _⟩
      rw [e1]
      refine Ideal.add_mem _ (Ideal.add_mem _ (hz _ hp) (hz _ (((hnilx _ hp0).map _).map _))) ?_
      exact Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    refine ⟨e * (n.natAbs + 1 + N), fun y hy => ?_⟩
    rw [pow_mul] at hy
    have hy2 := Ideal.pow_right_mono he _ hy
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy2
    obtain ⟨z, rfl⟩ := hy2
    obtain ⟨q, hq⟩ := hN z.1 z.2
    have e2 : S.val.toRingHom (algebraMap (PowerSeries R) S PowerSeries.X ^ (n.natAbs + 1 + N) * z)
        = algebraMap (PowerSeries R) (LaurentSeries R) (PowerSeries.X ^ (n.natAbs + 1) * q) := by
      rw [map_mul (algebraMap (PowerSeries R) (LaurentSeries R)), hq, Algebra.smul_def, ← mul_assoc, ← map_mul,
        ← pow_add, ← map_pow]
      rfl
    rw [e2]
    show ((PowerSeries.X ^ (n.natAbs + 1) * q : PowerSeries R) : LaurentSeries R).coeff n = 0
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_X_pow_mul']
    simp
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem preLine_desc {Λ A T S : Type} [CommRing Λ] [CommRing A] [CommRing T] [CommRing S] [Algebra Λ A]
    [Algebra Λ T] [Algebra Λ S] (f : A →ₐ[Λ] S) (j : T →ₐ[Λ] S) (hj : Function.Injective j)
    (h : ∀ x, f x ∈ j.range) : ∃ g : A →ₐ[Λ] T, ∀ x, j (g x) = f x := by
  refine ⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (f.codRestrict j.range h), fun x => ?_⟩
  have := congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨f x, h x⟩)
  exact this

theorem UpperTheory.V.Ws.sxPreLine :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a), Y.Line := by
  intro O Γ _ _ _ Φ Λ _ _ a Y Q hQ
  haveI h0 : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  haveI hS : IsCO Λ (PowerSeries (ResidueField Λ)) := co_mvps Λ (ResidueField Λ) Unit
  obtain ⟨h1, h2⟩ := sxResLift Q hQ
  obtain ⟨f, hf⟩ := Y.univ _ _ _ h1 h2
  let j : (ResidueField Λ)[X] →ₐ[Λ] PowerSeries (ResidueField Λ) :=
    { (Polynomial.coeToPowerSeries.ringHom : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) with
      commutes' := fun x => by
        simp [Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply] }
  have hj : Function.Injective j := Polynomial.coe_injective _
  have hf' : Y.P.map (f : Y.A →+* PowerSeries (ResidueField Λ)) = Q.map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := hf
  have hr : ∀ g i l, f (Y.P.r g i l) = j (Q.r g i l) := fun g i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.r g i l) hf'
  have hn : ∀ v i l, f (Y.P.n v i l) = j (Q.n v i l) := fun v i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.n v i l) hf'
  have hB : f.comp (IsScalarTower.toAlgHom Λ Y.B Y.A) = (j.comp Polynomial.CAlgHom).comp (res Λ Y.B) := by
    refine Y.genB _ _ _ (fun g n => ?_) (fun v i s hs => ?_)
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) =
        (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) ((C : ResidueField Λ →+* (ResidueField Λ)[X]) ((res Λ Y.B : Y.B →+* ResidueField Λ) _))
      rw [← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, Y.cp_map, Y.cp_red,
        ← Matrix.charpoly_map]
      have e : (Y.P.r g).map (f : Y.A →+* PowerSeries (ResidueField Λ)) = (Q.r g).map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := by
        ext1 i l
        exact hr g i l
      rw [e, Matrix.charpoly_map, sxCpRes _ Q hQ.res g]
      simp [Polynomial.map_prod]
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) = (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) (C (res Λ Y.B _))
      rw [Y.ψ_map v i s hs, Y.ψ_red v i s hs, ← (sxPdMap ((algebraMap Λ Y.A).comp a) _ Y.P).1, hf',
        (sxPdMap (C.comp ((residue Λ).comp a)) _ Q).1, hQ.res.char v s hs]
      rfl
  have hB' : ∀ b, f (algebraMap Y.B Y.A b) = j (C (res Λ Y.B b)) := fun b => DFunLike.congr_fun hB b
  have hrange : ∀ x, f x ∈ j.range := by
    intro x
    have hx : x ∈ Algebra.adjoin Y.B _ := Y.gen ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨_, (hr _ _ _).symm⟩
      · exact ⟨_, (hn _ _ _).symm⟩
    | algebraMap b => exact ⟨_, (hB' b).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨g, hg⟩ := preLine_desc f j hj hrange
  refine ⟨g, ?_, fun b hb => hj ?_⟩
  · refine PD.ext (MonoidHom.ext fun s => Matrix.ext fun i l => hj ?_) (funext fun v => Matrix.ext fun i l => hj ?_)
    · exact (hg _).trans (hr s i l)
    · exact (hg _).trans (hn v i l)
  · rw [hg, hB', (res_eq_zero_iff Λ Y.B b).2 hb, map_zero]
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxCoreCp :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R} [IsCO Λ (W.gr 0)], Φ.Near a 0 D → RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∃ cp : Γ → (W.gr 0)[X], (∀ g, (cp g).map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly) ∧ (∀ n, AdicCont (maximalIdeal (W.gr 0)) fun g => (cp g).coeff n) ∧ ∀ g, (cp g).map (res Λ (W.gr 0) : W.gr 0 →+* ResidueField Λ) = ∏ i, (X - C (residue Λ (a (Φ.χ i g)))) := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W _ hN hG D' hD
  have hr : ∀ g, D.r g = (D'.r g).map (W.A.val : W.A →+* R) := fun g => by
    rw [← hD]; rfl
  have hent : ∀ g i j, D'.r g i j ∈ W.gr (wt i j) := fun g i j => by
    have := hG.ent g i j
    rw [hr] at this
    exact this
  have hc : ∀ g n, (D'.r g).charpoly.coeff n ∈ W.gr 0 := fun g => sxCpZero W.gr (D'.r g) (hent g)
  have hl : ∀ g, ∃ p : (W.gr 0)[X], p.map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly := fun g => by
    have : (D'.r g).charpoly ∈ Polynomial.lifts (algebraMap (W.gr 0) W.A) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hc g n⟩, rfl⟩
    exact (Polynomial.mem_lifts _).1 this
  choose cp hcp using hl
  have hco : ∀ g n, (((cp g).coeff n : W.A) : R) = (D.r g).charpoly.coeff n := fun g n => by
    rw [hr, Matrix.charpoly_map, coeff_map, ← hcp, coeff_map]
    rfl
  refine ⟨cp, hcp, fun n => ?_, fun g => ?_⟩
  · refine (sxContGr W hG.max).2 _ ?_
    simp only [hco]
    exact (sxAdicMat (maximalIdeal R) (fun g => D.r g) hN.cont).1 n
  · let f : W.gr 0 →ₐ[Λ] R :=
      { (W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A) with
        commutes' := fun _ => rfl }
    have hd : (D.r g).map (res Λ R : R →+* ResidueField Λ) =
        Matrix.diagonal fun i => residue Λ (a (Φ.χ i g)) := by
      ext i j
      by_cases h : i = j
      · subst h
        rw [Matrix.diagonal_apply_eq]
        exact hN.diag g i
      · rw [Matrix.diagonal_apply_ne _ h]
        exact (res_eq_zero_iff Λ R _).2 (hN.off g i j h le_rfl)
    rw [← Matrix.charpoly_diagonal, ← hd, Matrix.charpoly_map]
    ext n
    rw [coeff_map, coeff_map, ← hco]
    exact (res_map f _).symm
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isGSp_map' {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {X : M4 R}
    (h : IsGSp ν X) : IsGSp (f ν) (X.map f) := by
  unfold IsGSp at *
  ext i j
  have := congrArg f (congrFun (congrFun h i) j)

  simpa [Matrix.mul_apply, adj_apply, Matrix.one_apply, map_sum, apply_ite f] using this

open Classical in
theorem UpperTheory.V.Ws.sxPreOfCore :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ}, (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) → Core Φ a → Nonempty (Pre Φ a) := by
  intro O Γ _ _ _ Φ Λ _ _ a hMu X
  obtain ⟨A, cA, aA, n, hft, hgen, hfl, huniv⟩ := sxChart X.D
  letI aBA : Algebra X.B A := ((algebraMap X.A A).comp (algebraMap X.B X.A)).toAlgebra
  letI aLA : Algebra Λ A := ((algebraMap X.A A).comp (algebraMap Λ X.A)).toAlgebra
  have hB : ∀ b, algebraMap X.B A b = algebraMap X.A A (algebraMap X.B X.A b) := fun _ => rfl
  have hL : ∀ b, algebraMap Λ A b = algebraMap X.A A (algebraMap Λ X.A b) := fun _ => rfl
  haveI t1 : IsScalarTower X.B X.A A := IsScalarTower.of_algebraMap_eq hB
  haveI t2 : IsScalarTower Λ X.B A := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hB, hL, ← IsScalarTower.algebraMap_apply Λ X.B X.A]
  let P : PD Φ.ι Γ A := ⟨mapRep (algebraMap X.A A) X.D.r, n⟩
  have hr : ∀ g, P.r g = (X.D.r g).map (algebraMap X.A A) := fun _ => rfl
  have hψ : ∀ v i (s : Φ.Gv v), P.ψ v i s = algebraMap X.A A (X.D.ψ v i s) := fun v i s => hfl.char v i s
  refine ⟨{ A := A, B := X.B, ft := X.ft.trans hft, P := P, pair := ?_, cont := ?_, gen := ?_, cp := X.cp,
            cp_map := ?_, cp_cont := X.cp_cont, cp_red := X.cp_red,
            ψ := fun v i s => if h : s ∈ Φ.Gv v then X.ψ v i ⟨s, h⟩ else 0,
            ψ_map := ?_, ψ_cont := ?_, ψ_red := ?_, genB := ?_, univ := ?_ }⟩
  · refine ⟨fun g => isGSp_map' (algebraMap X.A A) (X.rep.mult g), fun g hg => ?_, ?_, hfl.low, hfl.flag,
      fun v s hs i => ?_⟩
    · rw [hr, X.rep.kill g hg, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [hr]
      exact X.rep.nrm.map (map_zero _)
    · exact (hfl.char v i ⟨s, hMu v s hs⟩).trans (hfl.mu v i ⟨s, hMu v s hs⟩ hs)
  · intro i j
    refine adicCont_map (algebraMap X.A A) ?_ (X.cont i j)
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact Ideal.mem_map_of_mem (algebraMap X.B A) hb
  · rw [eq_top_iff]
    set S := Algebra.adjoin X.B ((Set.range fun x : Γ × Fin 4 × Fin 4 => P.r x.1 x.2.1 x.2.2) ∪
      Set.range fun x : Φ.ι × Fin 4 × Fin 4 => P.n x.1 x.2.1 x.2.2) with hS
    have h0 : ∀ x : X.A, algebraMap X.A A x ∈ S := by
      intro x
      have hx : x ∈ Algebra.adjoin X.B (Set.range fun x : Γ × Fin 4 × Fin 4 => X.D.r x.1 x.2.1 x.2.2) := by
        rw [X.gen]; trivial
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        exact Algebra.subset_adjoin (Or.inl ⟨y, rfl⟩)
      | algebraMap b => exact S.algebraMap_mem b
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact S.mul_mem hx hy
    rintro x -
    have hx : x ∈ Algebra.adjoin X.A (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) := by
      rw [hgen]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inr hx)
    | algebraMap b => exact h0 b
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | mul x y _ _ hx hy => exact S.mul_mem hx hy
  · intro g
    rw [hr, Matrix.charpoly_map, ← X.cp_map, Polynomial.map_map]
    rfl
  · intro v i s hs
    rw [dite_eq_left hs, hB, X.ψ_map]
    exact (hψ v i ⟨s, hs⟩).symm
  · intro v i
    simpa using X.ψ_cont v i
  · intro v i s hs
    rw [dite_eq_left hs]
    exact X.ψ_red v i ⟨s, hs⟩
  · intro R _ _ _ f f' h1 h2
    refine X.genB R f f' h1 fun v i s => ?_
    simpa using h2 v i s s.2
  · intro R _ _ _ c Q hc hQ
    obtain ⟨τ, D', hN, hDr, hF⟩ := sxPairNear c Q hc hQ
    obtain ⟨f, hf⟩ := X.univ R τ D' hN
    obtain ⟨F, hF1, hF2⟩ := huniv R (f : X.A →+* R) Q.n (hf ▸ hF)
    have hF3 : ∀ x, F (algebraMap X.A A x) = f x := fun x => RingHom.congr_fun hF1 x
    refine ⟨{ F with commutes' := fun x => ?_ }, ?_⟩
    · exact (hF3 _).trans (f.commutes x)
    · refine PD.ext ?_ (funext hF2)
      rw [← hDr, ← hf]
      ext g i j
      exact hF3 _
end
