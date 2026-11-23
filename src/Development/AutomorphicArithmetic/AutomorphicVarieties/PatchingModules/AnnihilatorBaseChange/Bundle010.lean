module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle004
public import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle003
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mem_iff {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (y : R) :
    f y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem surj_of_gen {O : Type} [CommRing O] [IsLocalRing O] {R B C : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing B] [Algebra O B] [IsCO O B] [CommRing C] [Algebra O C] [IsCO O C] [Algebra B C] [IsScalarTower O B C]
    (f : R →ₐ[O] C) (S : Set B) (U : Set C) (hS : GenBy O S) (hU : Algebra.adjoin B U = ⊤)
    (h1 : ∀ b ∈ S, algebraMap B C b ∈ f.range) (h2 : ∀ c ∈ U, c ∈ f.range) : Function.Surjective f := by
  have hmB : ∀ y : B, algebraMap B C y ∈ maximalIdeal C ↔ y ∈ maximalIdeal B := fun y => by
    simpa using mem_iff (IsScalarTower.toAlgHom O B C) y
  have hpow : ∀ N (y : B), y ∈ maximalIdeal B ^ N → algebraMap B C y ∈ maximalIdeal C ^ N := by
    intro N y hy
    have hle : Ideal.map (algebraMap B C) (maximalIdeal B) ≤ maximalIdeal C := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      exact (hmB z).2 hz
    have h1' : algebraMap B C y ∈ Ideal.map (algebraMap B C) (maximalIdeal B ^ N) :=
      Ideal.mem_map_of_mem _ hy
    rw [Ideal.map_pow] at h1'
    exact Ideal.pow_right_mono hle N h1'
  have hadj : Algebra.adjoin O S ≤ (f.range).comap (IsScalarTower.toAlgHom O B C) := by
    rw [Algebra.adjoin_le_iff]
    intro b hb
    simpa using h1 b hb
  let P : Subalgebra B C :=
    { carrier := {c | ∀ N, ∃ r, c - f r ∈ maximalIdeal C ^ N}
      mul_mem' := by
        intro a b ha hb N
        obtain ⟨r1, hr1⟩ := ha N
        obtain ⟨r2, hr2⟩ := hb N
        refine ⟨r1 * r2, ?_⟩
        have e : a * b - f (r1 * r2) = (a - f r1) * b + f r1 * (b - f r2) := by
          rw [map_mul]
          ring
        rw [e]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hr1) (Ideal.mul_mem_left _ _ hr2)
      add_mem' := by
        intro a b ha hb N
        obtain ⟨r1, hr1⟩ := ha N
        obtain ⟨r2, hr2⟩ := hb N
        refine ⟨r1 + r2, ?_⟩
        have e : a + b - f (r1 + r2) = (a - f r1) + (b - f r2) := by
          rw [map_add (f := _)]
          ring
        rw [e]
        exact Ideal.add_mem _ hr1 hr2
      algebraMap_mem' := by
        intro b N
        obtain ⟨a, ha, hba⟩ := hS N b
        have ha' := hadj ha
        rw [Subalgebra.mem_comap, AlgHom.mem_range] at ha'
        obtain ⟨r, hr⟩ := ha'
        refine ⟨r, ?_⟩
        have hr' : f r = algebraMap B C a := by simpa using hr
        rw [hr', ← map_sub]
        exact hpow N _ hba }
  have hUP : Algebra.adjoin B U ≤ P := by
    rw [Algebra.adjoin_le_iff]
    intro c hc N
    obtain ⟨r, hr⟩ := (AlgHom.mem_range f).1 (h2 c hc)
    exact ⟨r, by rw [hr, sub_self]; exact Ideal.zero_mem _⟩
  have hall : ∀ c : C, ∀ N, ∃ r, c - f r ∈ maximalIdeal C ^ N := by
    intro c
    have hc : c ∈ Algebra.adjoin B U := by
      rw [hU]
      exact Algebra.mem_top
    exact hUP hc
  apply co_surj O R C f
  intro m hm
  obtain ⟨r, hr⟩ := hall m 2
  have hfr : f r ∈ maximalIdeal C := by
    have e : m - (m - f r) = f r := by ring
    rw [← e]
    exact Ideal.sub_mem _ hm (Ideal.pow_le_self two_ne_zero hr)
  have hrm : r ∈ maximalIdeal R := (mem_iff f r).1 hfr
  have e : m = f r + (m - f r) := by ring
  rw [e]
  exact Submodule.add_mem_sup (Ideal.mem_map_of_mem f hrm) hr

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have e : (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ)
      (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom H Polynomial.C) (MonoidAlgebra.single g 1))
      = MonoidAlgebra.single 1 Polynomial.X
        - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.single (φ g) 1) := by
    rw [map_sub]
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  simp only [GDet.lam, GDet.chi, GDet.comap, MonoidHom.coe_comp, Function.comp_apply]
  exact congrArg (fun y => (-1) ^ i * ((D.D (Polynomial A)) y).coeff (n - i)) e

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this

theorem UpperTheory.V.Pa.Core.piSurj :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → GenBy O (pairVals u ∪ {(A.b.lam (MvPowerSeries.X (.inl ())))}) → Function.Surjective m.π := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hAd hgen
  letI := W.ring
  letI := W.alg
  haveI := W.co
  obtain ⟨⟨hco, -, -, hadj⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hAd
  haveI := hco
  obtain ⟨hD, hψ, -, hU, -⟩ := m.π_maps
  have hsurj : Function.Surjective (Λ.h.p₀.comp (πo0 Λ)) :=
    (Glob.Hom.p₀_surj Λ.h).comp (Lim.πo0_surj Λ)
  refine surj_of_gen (O := O) m.π _ _ hgen hadj ?_ ?_
  · intro b hb
    rcases hb with (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩) | hb
    · obtain ⟨h, rfl⟩ := hsurj g
      refine (AlgHom.mem_range _).2 ⟨W.t.D.lam i (MonoidAlgebra.single h 1), ?_⟩
      have e := congrArg (fun E => E.lam i (MonoidAlgebra.single h 1)) hD
      simp only [lam_map, lam_comap] at e
      exact e
    · refine (AlgHom.mem_range _).2 ⟨↑(W.t.ψ v i g), ?_⟩
      have e := congrArg (fun χ => ((χ g : (Spo A)ˣ) : Spo A)) (hψ v i)
      simpa using e
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      refine (AlgHom.mem_range _).2 ⟨m.s (MvPowerSeries.C (MvPowerSeries.X (Sum.inl ()))), ?_⟩
      rw [m.π_s]
      simp
  · rintro c ⟨p, rfl⟩
    exact (AlgHom.mem_range _).2 ⟨W.t.U p.1 p.2, hU p.1 p.2⟩
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem rm_ext {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    {D q n : ℕ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    (s : Sinf O Unit D q n →ₐ[O] R) (ρ : R →ₐ[O] R') (g : Sinf O Unit D q n →ₐ[O] R')
    (ha : ∀ k, s (MvPowerSeries.C (MvPowerSeries.X k)) ∈ maximalIdeal R) (hy : ∀ p, s (MvPowerSeries.X p) ∈ maximalIdeal R)
    (ea : ∀ k, g (MvPowerSeries.C (MvPowerSeries.X k)) = ρ (s (MvPowerSeries.C (MvPowerSeries.X k))))
    (ey : ∀ p, g (MvPowerSeries.X p) = ρ (s (MvPowerSeries.X p))) (z : Sinf O Unit D q n) : ρ (s z) = g z := by
  have hm : ∀ x ∈ maximalIdeal R, ρ x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff O R]
    exact hx
  obtain ⟨f, -, huniq⟩ := sinfExt O D q n R' (fun k => g (MvPowerSeries.C (MvPowerSeries.X k)))
    (fun p => g (MvPowerSeries.X p))
    (fun k => by rw [ea]; exact hm _ (ha k)) (fun p => by rw [ey]; exact hm _ (hy p))
  have h1 : ρ.comp s = f := huniq _ ⟨fun k => (ea k).symm, fun p => (ey p).symm⟩
  have h2 : g = f := huniq _ ⟨fun _ => rfl, fun _ => rfl⟩
  exact (DFunLike.congr_fun (h1.trans h2.symm) z : _)

private noncomputable def rm_cc (O : Type) [CommRing O] (D q n : ℕ) : Sinf O Unit D q n →ₐ[O] abelian₂ O Unit D :=
  { (MvPowerSeries.constantCoeff : Sinf O Unit D q n →+* abelian₂ O Unit D) with
    commutes' := fun c => by
      rw [MvPowerSeries.algebraMap_apply]
      exact MvPowerSeries.constantCoeff_C _ }

theorem UpperTheory.V.Pa.Core.rmapsEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A), Adapted T (r := r) → Nonempty (RMaps W) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W hT
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  have hw : ∀ k : Fin D, (algebraMap O W.R) (A.b.wt.c k) *
      ↑((W.t.ψ (A.b.wt.v k) (A.b.wt.i k)) (A.b.wt.γ k)) - 1 ∈ maximalIdeal W.R := by
    intro k
    rw [← res_eq_zero_iff O W.R, map_sub, map_mul, AlgHom.commutes, map_one,
      (W.t.psi _ _).red, ResidueField.algebraMap_eq, A.b.wt_res, sub_self]
  obtain ⟨s, ⟨hsa, hsy⟩, -⟩ := sinfExt O D T.q n W.R
    (Sum.elim (fun _ => W.t.s) (fun k => (algebraMap O W.R) (A.b.wt.c k) *
      ↑((W.t.ψ (A.b.wt.v k) (A.b.wt.i k)) (A.b.wt.γ k)) - 1))
    (fun p => W.t.y p.1 p.2)
    (by rintro (_ | k); exacts [W.t.s_mem, hw k]) (fun p => W.t.y_mem _ _)
  have hsm : ∀ k, s (MvPowerSeries.C (MvPowerSeries.X k)) ∈ maximalIdeal W.R := by
    rintro (_ | k)
    · rw [hsa]; exact W.t.s_mem
    · rw [hsa]; exact hw k
  have hym : ∀ p, s (MvPowerSeries.X p) ∈ maximalIdeal W.R := fun p => by
    rw [hsy]; exact W.t.y_mem _ _
  have hρ : ∀ N, ∃ f : W.R →ₐ[O] (A.A N).R, W.t.Maps f.toRingHom ((A.A N).p.D.comap (πN0 Λ N))
      (A.A N).p.ψ ((A.A N).s (MvPowerSeries.C (MvPowerSeries.X (Sum.inl ())))) (A.A N).U
      (fun j i => (A.A N).s (MvPowerSeries.X (j, i))) := by
    intro N
    obtain ⟨t, hD, hψ, hs, hU, hy⟩ := tupN l L G0 T Λ n O r B u J D A hT N
    obtain ⟨f, hf, -⟩ := W.univ _ t
    rw [hD, hψ, hs, hU, hy] at hf
    exact ⟨f, hf⟩
  choose ρ hρ using hρ
  haveI : IsCO O (Spo A) := (spoCo l L G0 T Λ n O r B u J D A hT).1.1
  obtain ⟨t, hD, hψ, hs, hU, hy⟩ := tupPi l L G0 T Λ n O r B u J D A
  obtain ⟨π, hπ, -⟩ := W.univ _ t
  rw [hD, hψ, hs, hU, hy] at hπ
  refine ⟨⟨s, hsa (Sum.inl ()), fun k => hsa (Sum.inr k), fun j i => hsy (j, i), ρ, hρ, ?_, π, hπ, ?_⟩⟩
  · intro N z
    refine rm_ext s (ρ N) (A.A N).s hsm hym ?_ ?_ z
    · rintro (_ | k)
      · rw [hsa]; exact (hρ N).2.2.1.symm
      · rw [hsa, Sum.elim_inr, (A.A N).s_w k, map_sub, map_mul, AlgHom.commutes, map_one]
        have := congrArg (fun χ => ((χ (A.b.wt.γ k) : (A.A N).Rˣ) : (A.A N).R))
          ((hρ N).2.1 (A.b.wt.v k) (A.b.wt.i k))
        simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at this
        rw [← this]
        rfl
    · intro p
      rw [hsy]
      exact ((hρ N).2.2.2.2 p.1 p.2).symm
  · intro z
    refine rm_ext s π ((IsScalarTower.toAlgHom O B (Spo A)).comp (A.b.lam.comp (rm_cc O D T.q n)))
      hsm hym ?_ ?_ z
    · rintro (_ | k)
      · rw [hsa]
        refine Eq.trans ?_ hπ.2.2.1.symm
        simp [rm_cc, MvPowerSeries.constantCoeff_C]
      · rw [hsa, Sum.elim_inr, map_sub, map_mul, AlgHom.commutes, map_one]
        have := congrArg (fun χ => ((χ (A.b.wt.γ k) : (Spo A)ˣ) : Spo A))
          (hπ.2.1 (A.b.wt.v k) (A.b.wt.i k))
        simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at this
        change algebraMap B (Spo A) (A.b.lam (MvPowerSeries.constantCoeff
          (MvPowerSeries.C (MvPowerSeries.X (Sum.inr k))))) = _
        rw [MvPowerSeries.constantCoeff_C, A.b.segmentWeightExponent, map_sub, map_mul, map_one,
          ← IsScalarTower.algebraMap_apply]
        erw [this]
    · intro p
      rw [hsy]
      refine Eq.trans ?_ (hπ.2.2.2.2 p.1 p.2).symm
      simp [rm_cc, MvPowerSeries.constantCoeff_X]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tens_free {Λ B S M X : Type} [CommRing Λ] [CommRing B] [CommRing S] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module Λ M] [Module.Free B S] [Module.Finite B S]
    [Module.Free Λ M] [Module.Finite Λ M] [Nontrivial B] [AddCommGroup X] [Module Λ X]
    (lam : Λ → B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (e : X ≃+ S ⊗[B] M)
    (he : ∀ (a : Λ) (x : X), e (a • x) = algebraMap B S (lam a) • e x) :
    Module.Free Λ X ∧ Module.Finite Λ X := by
  classical
  let φ : S ⊗[B] M ≃ₗ[B] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    (TensorProduct.congr (Module.Free.chooseBasis B S).repr (LinearEquiv.refl B M)).trans
      (TensorProduct.finsuppScalarLeft B M _)
  have key : ∀ (a : Λ) (x : X), φ (e (a • x)) = a • φ (e x) := by
    intro a x
    rw [he, algebraMap_smul, map_smul]
    ext i
    simp only [Finsupp.smul_apply, hl]
  let ψ : X ≃ₗ[Λ] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    { toFun := fun x => φ (e x)
      invFun := fun f => e.symm (φ.symm f)
      map_add' := fun x y => by simp
      map_smul' := key
      left_inv := fun x => by simp
      right_inv := fun f => by simp }
  exact ⟨Module.Free.of_equiv ψ.symm, Module.Finite.equiv ψ.symm⟩

theorem UpperTheory.V.Pa.Core.patchedModule_free_finite_over_iwasawaAlgebra :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → Module.Free (abelian₂ O Unit D) (X0 m) ∧ Module.Finite (abelian₂ O Unit D) (X0 m) ∧ (∀ (a : abelian₂ O Unit D) (x : X0 m), a • x = m.s.toRingHom (MvPowerSeries.C a) • x) ∧ ∀ p (x : X0 m), m.s.toRingHom (MvPowerSeries.X p) • x = 0 := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT
  obtain ⟨⟨hco, hfree, hfin, -⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hT
  haveI := A.b.free
  haveI := A.b.fin
  haveI := hfree
  haveI := hfin
  have hs : ∀ (t : W.R) (x : X0 m), t • x = m.π t • x := fun _ _ => rfl
  obtain ⟨h1, h2⟩ := tens_free (Λ := abelian₂ O Unit D) (X := X0 m) A.b.lam A.b.smul_lam (AddEquiv.refl _)
    (fun a x => X0.lam_smul_def m a x)
  refine ⟨h1, h2, fun a x => ?_, fun p x => ?_⟩
  · rw [X0.lam_smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs, m.π_s,
      MvPowerSeries.constantCoeff_C]
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hs, m.π_s, MvPowerSeries.constantCoeff_X,
      map_zero, map_zero, zero_smul]
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem gDet_chi_map_mapRingHom {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G]
    (D : GDet n R G) (f : R →+* R') (x : MonoidAlgebra R G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f x) = (D.chi x).map f := by
  unfold GDet.chi GDet.map
  dsimp only
  letI : Algebra R (Polynomial R') := ((algebraMap R' (Polynomial R')).comp f).toAlgebra
  let g : Polynomial R →ₐ[R] Polynomial R' :=
    { Polynomial.mapRingHom f with
      commutes' := fun c => by
        simp [RingHom.algebraMap_toAlgebra, Polynomial.algebraMap_apply] }
  have h := D.nat (Polynomial R) (Polynomial R') g
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C x)
  refine Eq.trans ?_ h
  congr 1
  rw [map_sub]
  congr 1
  · ext a
    simp [g, MonoidAlgebra.mapRingHom, Polynomial.mapRingHom]
  · ext a
    simp [g, MonoidAlgebra.mapRingHom, Polynomial.mapRingHom]

private theorem gDet_tr_map_mapRingHom {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G]
    (D : GDet n R G) (f : R →+* R') (x : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.mapRingHom G f x) = f (D.tr x) := by
  unfold GDet.tr GDet.lam
  rw [gDet_chi_map_mapRingHom, Polynomial.coeff_map]
  simp

private theorem gDet_tr_comap_eq_tr_mapDomainRingHom {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H]
    (D : GDet n R G) (φ : H →* G) (x : MonoidAlgebra R H) :
    (D.comap φ).tr x = D.tr (MonoidAlgebra.mapDomainRingHom R φ x) := by
  unfold GDet.tr GDet.lam GDet.chi GDet.comap
  dsimp only
  rw [MonoidHom.comp_apply]
  congr 3
  congr 1
  show MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _ = _
  rw [map_sub]
  congr 1
  · simp [MonoidAlgebra.mapDomainRingHom_apply]
  · ext a
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom]
    rw [Finsupp.mapDomain_mapRange _ _ _ _ (fun a b => Polynomial.C_add)]
    simp

theorem UpperTheory.V.Pa.Core.patched_trace_local_charPoly_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (v : L.Vl) (g : Fin n → L.Gv v) (ga : Fin n → Ph0 Λ) (h : Ph0 Λ), (∀ i, πo0 Λ (ga i) = Λ.G.φ v (g i)) → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (List.ofFn fun i => MonoidAlgebra.single (ga i) (1 : W.R) - MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.Rˣ) : W.R)).prod) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT v g ga h hga j
  obtain ⟨V, hVle, hsees⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.φ_lim V] with N hker hφ
  have hπo : ∀ i, Λ.πo (ga i) = ((Λ.G.φ v (g i) : Λ.G.G₀) : Λ.G.Γ) := fun i =>
    congrArg Subtype.val (hga i)
  have lift : ∀ i, ∃ x : Λ.Ph, Λ.π N x = (((T.GN N).φ v (g i) : (T.GN N).G₀) : (T.GN N).Γ) ∧
      (ga i : Λ.Ph)⁻¹ * x ∈ (V.toOpenSubgroup : Subgroup Λ.Ph) := fun i =>
    (closeLift _ _ _ (Λ.π N) Λ.πo _ hker).1 _ _ (ga i) (hφ v (g i)) (hπo i)
  choose x hx1 hx2 using lift
  have hmem : ∀ i, x i ∈ Ph0 Λ := fun i => by
    have := (Ph0 Λ).mul_mem (ga i).2 (hVle (hx2 i))
    simpa using this
  let gb : Fin n → Ph0 Λ := fun i => ⟨x i, hmem i⟩
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (List.ofFn fun i =>
    MonoidAlgebra.single (gb i) (1 : W.R) - MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.Rˣ) : W.R)).prod), ?_, Or.inl ?_⟩
  · refine hsees 1 _ _ ?_
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    congr 2
    congr 1
    funext i
    congr 2
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hx2 i
  · show (m.ρ N).toRingHom _ = 0
    rw [← gDet_tr_map_mapRingHom, (m.ρ_maps N).1, gDet_tr_comap_eq_tr_mapDomainRingHom]
    refine Eq.trans ?_ ((A.A N).p.Ord v g (πN0 Λ N h))
    congr 1
    unfold GFrame.oEl
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, map_one]
    congr 2
    congr 1
    funext i
    rw [← (m.ρ_maps N).2.1 v i]
    congr 2
    exact Subtype.ext (hx1 i)
end
