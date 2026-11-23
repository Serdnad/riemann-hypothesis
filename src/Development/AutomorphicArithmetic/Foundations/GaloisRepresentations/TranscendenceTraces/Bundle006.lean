module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma ring_eq {Ω B L : Type} [Field Ω] [IsAlgClosed Ω] [CommRing B] [Algebra Ω B] [Module.Finite Ω B] [Field L]
    (f f' : B →+* L) (h : f.comp (algebraMap Ω B) = f'.comp (algebraMap Ω B))
    (hk : RingHom.ker f = RingHom.ker f') : f = f' := by
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  haveI : IsDomain (B ⧸ RingHom.ker f) := Ideal.Quotient.isDomain _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := B ⧸ RingHom.ker f)
  ext b
  obtain ⟨c, hc⟩ := hb.2 (Ideal.Quotient.mk _ b)
  have hm : b - algebraMap Ω B c ∈ RingHom.ker f := by
    rw [← Ideal.Quotient.eq]
    rw [← hc]
    rfl
  have h1 : f b = f (algebraMap Ω B c) := by
    have := RingHom.mem_ker.mp hm
    rw [map_sub, sub_eq_zero] at this
    exact this
  have h2 : f' b = f' (algebraMap Ω B c) := by
    have := RingHom.mem_ker.mp (hk ▸ hm)
    rw [map_sub, sub_eq_zero] at this
    exact this
  rw [h1, h2]
  exact congrArg (fun g : Ω →+* L => g c) h

private lemma pt_spec {B L : Type} [CommRing B] [Field L] (f : CommRingCat.of B ⟶ CommRingCat.of L) :
    (pt (Spec.map f) : Spec (CommRingCat.of B)).asIdeal = RingHom.ker f.hom := by
  ext b
  change f.hom b ∈ (IsLocalRing.closedPoint L).asIdeal ↔ _
  simp [RingHom.mem_ker, IsLocalRing.closedPoint]

theorem UpperTheory.Gal.TranscendenceTraces.ptOne_of :
    Chart → PtOne := by
  intro hC V Ω _ _ r _ L _ a z z' hz hz' hp
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC r Ω (𝟙 _)
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  have hs : inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = r := by
    have := hpb.w
    rw [Category.comp_id] at this
    rw [← this, IsIso.inv_hom_id_assoc]
  obtain ⟨f, hf⟩ := Spec.map_surjective (z ≫ inv v)
  obtain ⟨f', hf'⟩ := Spec.map_surjective (z' ≫ inv v)
  have e1 : Spec.map f ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = a := by
    rw [hf, Category.assoc, hs, hz]
  have e2 : Spec.map f' ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = a := by
    rw [hf', Category.assoc, hs, hz']
  have e3 : CommRingCat.ofHom (algebraMap Ω B) ≫ f = CommRingCat.ofHom (algebraMap Ω B) ≫ f' := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, e1, e2]
  have e4 : pt (Spec.map f) = pt (Spec.map f') := by
    rw [hf, hf', pt_comp, pt_comp, hp]
  have e5 : RingHom.ker f.hom = RingHom.ker f'.hom := by
    rw [← pt_spec f, ← pt_spec f', e4]
  have e6 : f.hom = f'.hom := ring_eq f.hom f'.hom (congrArg CommRingCat.Hom.hom e3) e5
  have e7 : f = f' := CommRingCat.hom_ext e6
  have e8 : z ≫ inv v = z' ≫ inv v := by rw [← hf, ← hf', e7]
  exact (cancel_mono (inv v)).mp e8
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma exists_hom {R Ω : Type} [CommRing R] [Field Ω] (x : gp Ω ⟶ Spec (CommRingCat.of R)) :
    ∃ φ : R →+* Ω, x = Spec.map (CommRingCat.ofHom φ) := by
  refine ⟨(Spec.preimage x).hom, ?_⟩
  simp [Spec.map_preimage]

private lemma map_comp' {R S Ω : Type} [CommRing R] [CommRing S] [CommRing Ω] (a : R →+* S) (φ : S →+* Ω) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom (φ.comp a)) := by
  rw [← Spec.map_comp]
  rfl

private lemma map_inj' {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  simpa using congrArg CommRingCat.Hom.hom this

private lemma pt_map {R Ω : Type} [CommRing R] [Field Ω] (f : R →+* Ω) :
    (pt (Spec.map (CommRingCat.ofHom f))).asIdeal = RingHom.ker f := by
  ext a
  simp only [pt]
  show a ∈ (Ideal.comap f (IsLocalRing.closedPoint Ω).asIdeal) ↔ _
  simp [IsLocalRing.closedPoint, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem UpperTheory.Gal.TranscendenceTraces.splitCover_of :
    SplitField → GalTrans → SplitCover := by
  intro hsf hgt A B _ _ _ _ _ _
  obtain ⟨L, _, _, _, _, _, _, hfin, hsp⟩ := hsf A B
  set C := integralClosure A L
  have hinj : Function.Injective (algebraMap A C) := by
    intro a b hab
    have h1 : algebraMap A L a = algebraMap A L b := by
      have := congrArg (fun c : C => (c : L)) hab
      simpa using this
    rw [IsScalarTower.algebraMap_apply A (FractionRing A) L a,
      IsScalarTower.algebraMap_apply A (FractionRing A) L b] at h1
    exact IsFractionRing.injective A (FractionRing A) ((algebraMap (FractionRing A) L).injective h1)
  have key : ∀ {Ω : Type} [Field Ω] (φ : C →+* Ω),
      RingHom.ker (φ.comp (algebraMap A C)) = ⊥ → RingHom.ker φ = ⊥ := by
    intro Ω _ φ h
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    change Ideal.comap (algebraMap A C) (RingHom.ker φ) = ⊥
    rw [RingHom.comap_ker]
    exact h
  refine ⟨Spec (CommRingCat.of C), Spec.map (CommRingCat.ofHom (algebraMap A C)), (B →ₐ[A] C),
    fun j => Spec.map (CommRingCat.ofHom (j : B →+* C)),
    fun j => (⟨RingHom.ker (j : B →+* C), RingHom.ker_isPrime _⟩ : PrimeSpectrum B),
    ?_, ?_, hfin, ?_, ?_, ?_⟩
  · exact IsIntegralHom.SpecMap_iff.mpr (fun x => Algebra.IsIntegral.isIntegral x)
  · refine ⟨fun p => ?_⟩
    have hp : p.asIdeal.IsPrime := p.isPrime
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := C) p.asIdeal ⊥ (by
      rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
      exact bot_le)
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩
  · intro j
    rw [map_comp']
    congr 2
    exact j.comp_algebraMap
  · intro Ω _ x x' hxx
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨φ', rfl⟩ := exists_hom x'
    simp only [map_comp'] at hxx
    obtain ⟨g, hg⟩ := hgt A L Ω φ φ' (map_inj' hxx)
    let e : (B →ₐ[A] C) ≃ (B →ₐ[A] C) :=
      { toFun := fun j => (g.symm : C →ₐ[A] C).comp j
        invFun := fun j => (g : C →ₐ[A] C).comp j
        left_inv := fun j => by
          ext b
          simp
        right_inv := fun j => by
          ext b
          simp }
    refine ⟨e, fun j => ⟨?_, ?_⟩⟩
    · simp only [map_comp']
      congr 2
      ext b
      simp [e, hg]
    · apply PrimeSpectrum.ext
      ext b
      simp [e]
  · intro Ω _ x z hz hbot
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨ζ, rfl⟩ := exists_hom z
    simp only [map_comp'] at hz
    rw [map_comp', pt_map] at hbot
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr (key φ hbot)
    have hiff : ∀ j : B →ₐ[A] C, Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (j : B →+* C)) = Spec.map (CommRingCat.ofHom ζ) ↔
        φ.comp (j : B →+* C) = ζ := by
      intro j
      rw [map_comp']
      exact ⟨map_inj', fun h => by rw [h]⟩
    obtain ⟨j0, hj0, hu⟩ := hsp Ω φ ζ ((RingHom.injective_iff_ker_eq_bot _).mpr hbot) (map_inj' hz)
    refine ⟨⟨j0, (hiff j0).2 hj0, fun j hj => hu j ((hiff j).1 hj)⟩, fun j hj => ?_⟩
    rw [hiff] at hj
    apply PrimeSpectrum.ext
    rw [pt_map, ← hj]
    ext b
    simp [map_eq_zero_iff _ hφ]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem exists_fac {Ω : Type} [Field Ω] {S : Scheme.{0}} (x : gp Ω ⟶ S) (s : S) (h : pt x = s) :
    ∃ a : gp Ω ⟶ Spec (S.residueField s), a ≫ S.fromSpecResidueField s = x := by
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective x
  have hx : (Scheme.SpecToEquivOfField Ω S).symm ⟨t, a⟩ = Spec.map a ≫ S.fromSpecResidueField t := by
    simp [Scheme.SpecToEquivOfField]
  rw [hx] at h ⊢
  have hs : s ∈ Set.range (S.fromSpecResidueField t) := ⟨pt (Spec.map a), by rw [← pt_comp, h]⟩
  rw [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at hs
  subst hs
  exact ⟨Spec.map a, rfl⟩

theorem UpperTheory.Gal.TranscendenceTraces.multPt_of :
    WtFlat → WtPt → MultBC → MultPt := by
  intro hflat hpt hbc Z S p _ Ω Ω' _ _ _ _ z z' hzz
  obtain ⟨s, hs⟩ : ∃ s, p (pt z) = s := ⟨_, rfl⟩
  have hpb := IsPullback.of_hasPullback p (S.fromSpecResidueField s)
  have hw := hpt (pullback.snd p (S.fromSpecResidueField s))
    (mult (pullback.snd p (S.fromSpecResidueField s))) (hflat _)
  have hm := hbc _ _ _ _ hpb
  obtain ⟨a, ha⟩ := exists_fac (z ≫ p) s (by rw [pt_comp, hs])
  obtain ⟨a', ha'⟩ := exists_fac (z' ≫ p) s (by rw [pt_comp, ← hzz, hs])
  obtain ⟨z1, e1⟩ : ∃ z1 : gp Ω ⟶ pullback p (S.fromSpecResidueField s),
      z1 ≫ pullback.fst _ _ = z := ⟨pullback.lift z a ha.symm, pullback.lift_fst _ _ _⟩
  obtain ⟨z1', e1'⟩ : ∃ z1' : gp Ω' ⟶ pullback p (S.fromSpecResidueField s),
      z1' ≫ pullback.fst _ _ = z' := ⟨pullback.lift z' a' ha'.symm, pullback.lift_fst _ _ _⟩
  have hp1 : pt z1 = pt z1' := by
    apply (IsPreimmersion.isEmbedding (pullback.fst p (S.fromSpecResidueField s))).injective
    rw [← pt_comp z1, ← pt_comp z1', e1, e1']
    exact hzz
  have key := hw Ω Ω' z1 z1' hp1
  rw [hm] at key
  simpa [Wt.comap, e1, e1'] using key
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multSum_of :
    MultSumPt → MultBC → MultSum := by
  intro hPt hBC Z S p _ _ Ω _ _ x
  have hpb : IsPullback (pullback.fst p x) (pullback.snd p x) p x := IsPullback.of_hasPullback p x
  have hfin := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb (IsLocalRing.closedPoint Ω)
  have h1 := hPt Ω (pullback.snd p x)
  rw [hBC _ _ _ _ hpb] at h1
  rw [show pt x = x (IsLocalRing.closedPoint Ω) from rfl, ← hfin, ← h1]
  simp only [Wt.push, Wt.comap]
  have hb := fib_bijOn hpb (Ω := Ω) (𝟙 _)
  rw [Category.id_comp] at hb
  exact (finsum_mem_eq_of_bijOn _ hb (fun _ _ => rfl)).symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_congr {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a b => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)

theorem UpperTheory.Gal.TranscendenceTraces.stalkSum_of :
    Chart → ArtSum → StalkSum := by
  intro hC hA V Ω _ _ r _
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC r Ω (𝟙 (gp Ω))
  have hv : IsIso v := hpb.isIso_fst_of_isIso
  have hr : r = inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    rw [IsIso.eq_inv_comp, hpb.w, Category.comp_id]
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [Flat.SpecMap_iff]
    simpa [RingHom.flat_algebraMap_iff] using (inferInstance : Module.Flat Ω B)
  have hfi : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [IsFinite.SpecMap_iff]
    simpa [RingHom.finite_algebraMap] using hfin
  have hR : Scheme.Hom.finrank r (IsLocalRing.closedPoint Ω) = Module.finrank Ω B := by
    rw [hr, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hs : ∀ P : PrimeSpectrum B, IsIso (v.stalkMap P) :=
    (IsOpenImmersion.iff_isIso_stalkMap (f := v)).mp inferInstance |>.2
  have e2 : ∀ P : PrimeSpectrum B,
      V.presheaf.stalk (v P) ≃+* Localization.AtPrime P.asIdeal := fun P =>
    ((asIso (v.stalkMap P)) ≪≫ Spec.stalkIso (CommRingCat.of B) P).commRingCatIsoToRingEquiv
  rw [hR, ← hA Ω B, ← finsum_comp_equiv v.homeomorph.toEquiv]
  refine finsum_congr fun P => ?_
  change (Module.length (V.presheaf.stalk (v P)) (V.presheaf.stalk (v P))).toNat = _
  rw [length_congr (e2 P)]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.ptCommon_of :
    PtCommon := by
  intro X Ω Ω' _ _ z z' h
  have key : ∀ (K : Type) [Field K] (w : gp K ⟶ X) (y : X), pt w = y →
      ∃ ψ : X.residueField y ⟶ CommRingCat.of K, w = Spec.map ψ ≫ X.fromSpecResidueField y := by
    intro K _ w y hy
    subst hy
    exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X w).symm⟩
  obtain ⟨x, hx⟩ : ∃ x, pt z = x := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ := key Ω z x hx
  obtain ⟨φ', hφ'⟩ := key Ω' z' x (h.symm.trans hx)
  have i1 : Function.Injective φ.hom := φ.hom.injective
  have i2 : Function.Injective φ'.hom := φ'.hom.injective
  letI := φ.hom.toAlgebra
  letI := φ'.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) Ω Ω') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ i1 i2
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) Ω Ω')
  letI := Ideal.Quotient.field M
  let ψ : TensorProduct (X.residueField x) Ω Ω' →+* AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk M)
  have e1 : ∀ c, (φ.hom c ⊗ₜ[X.residueField x] (1 : Ω') : TensorProduct (X.residueField x) Ω Ω') =
      (1 : Ω) ⊗ₜ (φ'.hom c) := by
    intro c
    change algebraMap _ Ω c ⊗ₜ _ = _ ⊗ₜ algebraMap _ Ω' c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine ⟨AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (ψ.comp Algebra.TensorProduct.includeLeftRingHom)),
    Spec.map (CommRingCat.ofHom (ψ.comp (Algebra.TensorProduct.includeRight :
      Ω' →ₐ[X.residueField x] TensorProduct (X.residueField x) Ω Ω').toRingHom)), ?_⟩
  rw [hφ, hφ', ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext c
  simp [e1]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtVanish_of :
    Isolate → WtPt → PtEx → PtLift → FibFin → WtVanish := by
  intro hIso hPt hEx hLift hFin Z S p _ w hw D hD hzero
  funext Ω _ _ z
  show w Ω z = 0
  obtain ⟨A, W, v, hEt, hW, hvW, hvz, huniq⟩ := hIso p (pt z)
  haveI : IsFinite A.r := A.finite
  classical
  let φ : A.V → ℤ := fun y => if y ∈ W then 1 else 0
  have hφ : IsLocallyConstant φ := by
    refine IsLocallyConstant.iff_isOpen_fiber.2 ?_
    intro n
    by_cases h1 : n = 1
    · subst h1
      convert hW.isOpen using 1
      ext y
      by_cases hy : y ∈ W <;> simp [φ, hy]
    · by_cases h0 : n = 0
      · subst h0
        convert hW.compl.isOpen using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy]
      · convert isOpen_empty using 1
        ext y
        by_cases hy : y ∈ W <;> simp [φ, hy] <;> omega
  obtain ⟨ψ, hψ, hψeq⟩ := hw A φ hφ
  have hsum : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      ψ (A.r v) = w Ω z * ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    rw [← hx1, hψeq Ω1 x1, mul_finsum_mem]
    apply finsum_mem_congr rfl
    intro z' hz'
    have hz'' : z' ≫ A.r = x1 := hz'
    by_cases hW' : pt z' ∈ W
    · have hr : A.r (pt z') = A.r v := by
        rw [← pt_comp, hz'']
        exact hx1
      have hv : pt z' = v := huniq _ hW' hr
      have hwz : w Ω1 (z' ≫ A.v) = w Ω z :=
        hPt p w hw Ω1 Ω (z' ≫ A.v) z (by rw [pt_comp, hv, hvz])
      simp [φ, hW', hwz]
    · simp [φ, hW']
  have hpos : ∀ (Ω1 : Type) [Field Ω1] [IsAlgClosed Ω1] (x1 : gp Ω1 ⟶ A.U), pt x1 = A.r v →
      0 < ∑ᶠ z' ∈ fib A.r x1, φ (pt z') := by
    intro Ω1 _ _ x1 hx1
    obtain ⟨z1, hz1, hpz1⟩ := hLift A.r Ω1 x1 v hx1.symm
    have hf := hFin A.r Ω1 x1
    rw [finsum_mem_eq_finite_toFinset_sum _ hf]
    have hmem : z1 ∈ hf.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hz1
    calc (0:ℤ) < φ (pt z1) := by simp [φ, hpz1, hvW]
      _ ≤ _ := Finset.single_le_sum (f := fun z' => φ (pt z'))
          (fun i _ => by by_cases hi : pt i ∈ W <;> simp [φ, hi]) hmem
  obtain ⟨Ω0, _, _, x0, hx0⟩ := hEx A.U (A.r v)
  have hO : IsOpen (ψ ⁻¹' {ψ (A.r v)}) := hψ.isOpen_fiber _
  have hopen := A.u.isOpenMap _ hO
  obtain ⟨y, ⟨u1, hu1, rfl⟩, hyD⟩ :=
    hD.inter_open_nonempty _ hopen ⟨A.u (A.r v), A.r v, rfl, rfl⟩
  obtain ⟨Ω2, _, _, x2, hx2⟩ := hEx A.U u1
  have hψ1 : ψ u1 = 0 := by
    rw [← hx2, hψeq Ω2 x2]
    apply finsum_mem_of_eqOn_zero
    intro z' hz'
    have hz'' : z' ≫ A.r = x2 := hz'
    have hw0 : w Ω2 (z' ≫ A.v) = 0 := by
      apply hzero Ω2
      have hc : (z' ≫ A.v) ≫ p = x2 ≫ A.u := by
        rw [Category.assoc, A.pb.w, ← Category.assoc, hz'']
      rw [hc, pt_comp, hx2]
      exact hyD
    simp [hw0]
  have hu1' : ψ u1 = ψ (A.r v) := hu1
  have h1 := hsum Ω0 x0 hx0
  have h2 := hpos Ω0 x0 hx0
  rw [← hu1', hψ1] at h1
  rcases mul_eq_zero.mp h1.symm with h | h
  · exact h
  · exact absurd h h2.ne'
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma length_self_eq {R R' : Type} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Module.length R R = Module.length R' R' := by
  have h : ((Module.length R R : ℕ∞) : WithBot ℕ∞) = (Module.length R' R' : ℕ∞) := by
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm
  exact_mod_cast h

private lemma length_stalk_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (hy : f x = y) :
    Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  subst hy
  exact length_self_eq (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.multBC_of :
    MultBC := by
  intro Z' S' Z S v p' p g h
  funext Ω _ _ z
  have hw : (z ≫ p') ≫ g = (z ≫ v) ≫ p := by
    simp only [Category.assoc, h.w]
  have hP : IsPullback (pullback.fst p' (z ≫ p') ≫ v) (pullback.snd p' (z ≫ p')) p ((z ≫ v) ≫ p) := by
    rw [← hw]
    exact (IsPullback.of_hasPullback p' (z ≫ p')).paste_horiz h
  have hl : (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p')) ≫ hP.isoPullback.hom =
      pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm := by
    apply pullback.hom_ext
    · rw [Category.assoc, hP.isoPullback_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc, hP.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]
  have hpt : hP.isoPullback.hom (pt (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p'))) =
      pt (pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p ((z ≫ v) ≫ p)) := by
    rw [← pt_comp, hl]
  simp only [Wt.comap, mult]
  rw [length_stalk_eq hP.isoPullback.hom _ _ hpt]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nmlLoc_of :
    NmlInt → NmlNoeth → NmlLoc := by
  intro hI hN S hS h
  rcases h with h | h
  · haveI := h
    exact hI S hS
  · haveI := h
    exact hN S hS
end
