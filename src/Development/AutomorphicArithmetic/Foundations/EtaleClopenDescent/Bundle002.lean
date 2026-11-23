module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.EtaleCohomology.EtaleSheaves.Bundle012
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.MV

variable {R : Type} [CommRing R]

private theorem cpull_comp' {K L M I : Cx R} (a : K ⟶ L) (b : L ⟶ M) (n : ℤ)
    (x : CohomologyClass M I n) : cpull (a ≫ b) I n x = cpull a I n (cpull b I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem cpull_add' {K L I : Cx R} (a b : K ⟶ L) (n : ℤ)
    (x : CohomologyClass L I n) : cpull (a + b) I n x = cpull a I n x + cpull b I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add]

private theorem cpull_neg' {K L I : Cx R} (a : K ⟶ L) (n : ℤ)
    (x : CohomologyClass L I n) : cpull (-a) I n x = - cpull a I n x := by
  have h : cpull (-a + a) I n x = 0 := by
    rw [neg_add_cancel]
    obtain ⟨x, rfl⟩ := x.mk_surjective
    rw [cpre_mk]
    have : zcomp (Cocycle.ofHom (0 : K ⟶ L)) x (zero_add n) = 0 := by
      refine Cocycle.ext ?_
      simp [zcomp]
    rw [this]
    exact CohomologyClass.mk_zero _ _ _
  rw [cpull_add'] at h
  exact eq_neg_of_add_eq_zero_left h

private noncomputable def mvS {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : ShortComplex (Cx R) :=
  ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) (by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
        pullback.condition, add_neg_cancel])

private theorem mvS_exact {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) :
    (mvS (R := R) f g).ShortExact := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
  exact hw

private noncomputable def mvMap {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
    (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') :
    mvS (R := R) f g ⟶ mvS f' g' where
  τ₁ := (chains R).map (pullback.map f g f' g' u v p hu hv)
  τ₂ := biprod.map ((chains R).map u) ((chains R).map v)
  τ₃ := (chains R).map p
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [mvS, Category.assoc, biprod.map_fst, biprod.lift_fst, biprod.lift_fst_assoc,
        ← Functor.map_comp, pullback.lift_fst, pullback.map]
    · simp only [mvS, Category.assoc, biprod.map_snd, biprod.lift_snd, biprod.lift_snd_assoc,
        Preadditive.neg_comp, Preadditive.comp_neg, ← Functor.map_comp, pullback.lift_snd, pullback.map]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [mvS, biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc, ← Functor.map_comp, hu]
    · simp only [mvS, biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, ← Functor.map_comp, hv]

private theorem cpull_inl_desc {K L M I : Cx R} (a : K ⟶ M) (b : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (biprod.inl : K ⟶ K ⊞ L) I n (cpull (biprod.desc a b) I n x) = cpull a I n x := by
  rw [← cpull_comp', biprod.inl_desc]

private theorem cpull_inr_desc {K L M I : Cx R} (a : K ⟶ M) (b : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (biprod.inr : L ⟶ K ⊞ L) I n (cpull (biprod.desc a b) I n x) = cpull b I n x := by
  rw [← cpull_comp', biprod.inr_desc]

private theorem cpull_lift {K L P I : Cx R} (a : P ⟶ K) (b : P ⟶ L) (n : ℤ) (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a b) I n y =
      cpull a I n (cpull (biprod.inl : K ⟶ K ⊞ L) I n y) + cpull b I n (cpull (biprod.inr : L ⟶ K ⊞ L) I n y) := by
  rw [biprod.lift_eq, cpull_add', cpull_comp', cpull_comp']

end UpperTheory.Cb.MV

theorem UpperTheory.Cb.exists_mayerVietoris_connecting_exact :
    ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1), (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ), (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧ (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧ ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧ ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c, pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c) := by
  intro R _ F
  obtain ⟨D, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (fun n => by dsimp only [res]; infer_instance)
  have hbij := fun (K L : Cx R) (n : ℤ) => GlobalTheory.T.hypercohomologyPullback_biprod_inl_inr_bijective R K L (res R F) n

  have hf : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (n : ℤ) (y : CohomologyClass (((chains R).obj U) ⊞ ((chains R).obj V)) (res R F) n),
      cpull (UpperTheory.Cb.MV.mvS (R := R) f g).f (res R F) n y =
        pull R (pullback.fst f g) F n (cpull biprod.inl (res R F) n y) -
          pull R (pullback.snd f g) F n (cpull biprod.inr (res R F) n y) := by
    intro U V E f g n y
    refine (UpperTheory.Cb.MV.cpull_lift (I := res R F) ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) n y).trans ?_
    rw [UpperTheory.Cb.MV.cpull_neg', sub_eq_add_neg]
    rfl
  refine ⟨fun {U V E} f g h n => D (UpperTheory.Cb.MV.mvS f g) (UpperTheory.Cb.MV.mvS_exact f g h) n, ?_, ?_⟩
  · intro U V E f g h n
    obtain ⟨e₁, e₂, e₃⟩ := hex (UpperTheory.Cb.MV.mvS f g) (UpperTheory.Cb.MV.mvS_exact f g h) n
    have hi := fun (m : ℤ) (x : H R E F m) => UpperTheory.Cb.MV.cpull_inl_desc (I := res R F) ((chains R).map f) ((chains R).map g) m x
    have hr := fun (m : ℤ) (x : H R E F m) => UpperTheory.Cb.MV.cpull_inr_desc (I := res R F) ((chains R).map f) ((chains R).map g) m x
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      obtain ⟨y, hy⟩ := (hbij ((chains R).obj U) ((chains R).obj V) n).2 (a, b)
      have hya : cpull biprod.inl (res R F) n y = a := congrArg Prod.fst hy
      have hyb : cpull biprod.inr (res R F) n y = b := congrArg Prod.snd hy
      have key := e₁ y
      rw [hf, hya, hyb] at key
      refine (sub_eq_zero.symm.trans key).trans ?_
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hi n x).symm.trans hya, (hr n x).symm.trans hyb⟩
      · rintro ⟨x, hxa, hxb⟩
        refine ⟨x, (hbij ((chains R).obj U) ((chains R).obj V) n).1 ?_⟩
        exact Prod.ext ((hi n x).trans (hxa.trans hya.symm)) ((hr n x).trans (hxb.trans hyb.symm))
    · intro c
      refine (e₂ c).trans ?_
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨_, _, hf f g n y⟩
      · rintro ⟨a, b, rfl⟩
        obtain ⟨y, hy⟩ := (hbij ((chains R).obj U) ((chains R).obj V) n).2 (a, b)
        have hya : cpull biprod.inl (res R F) n y = a := congrArg Prod.fst hy
        have hyb : cpull biprod.inr (res R F) n y = b := congrArg Prod.snd hy
        refine ⟨y, ?_⟩
        rw [hf, hya, hyb]
    · intro x
      constructor
      · rintro ⟨h1, h2⟩
        refine (e₃ x).1 ((hbij ((chains R).obj U) ((chains R).obj V) (n + 1)).1 ?_)
        have z1 : cpull (biprod.inl : (chains R).obj U ⟶ (chains R).obj U ⊞ (chains R).obj V) (res R F) (n + 1) 0 = 0 := map_zero _
        have z2 : cpull (biprod.inr : (chains R).obj V ⟶ (chains R).obj U ⊞ (chains R).obj V) (res R F) (n + 1) 0 = 0 := map_zero _
        exact Prod.ext ((hi (n + 1) x).trans (h1.trans z1.symm)) ((hr (n + 1) x).trans (h2.trans z2.symm))
      · intro hc
        have h0 : cpull (biprod.desc ((chains R).map f) ((chains R).map g)) (res R F) (n + 1) x = 0 := (e₃ x).2 hc
        have h1 := hi (n + 1) x
        have h2 := hr (n + 1) x
        rw [h0, map_zero] at h1 h2
        exact ⟨h1.symm, h2.symm⟩
  · intro U V E U' V' E' f g f' g' p u v hu hv h h' n c
    exact hnat _ _ (UpperTheory.Cb.MV.mvS_exact f g h) (UpperTheory.Cb.MV.mvS_exact f' g' h')
      (UpperTheory.Cb.MV.mvMap f g f' g' p u v hu hv) n c
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace UpperTheory.Cb.EtalePushouts

private theorem etCobase : Et.IsStableUnderCobaseChange :=
  RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange

private theorem etOfPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (s : IsPushout f g u v) (hg : Et g) : Et u :=
  haveI := etCobase
  MorphismProperty.IsStableUnderCobaseChange.of_isPushout s hg

private theorem ieOfPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (s : IsPushout f g u v) (hg : IE g) : IE u :=
  haveI := etCobase
  MorphismProperty.IsStableUnderCobaseChange.of_isPushout (P := MorphismProperty.ind.{0} Et) s hg

private theorem etComp {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : Et f) (hg : Et g) : Et (f ≫ g) := by
  change (f ≫ g).hom.Etale
  rw [CommRingCat.hom_comp]
  exact RingHom.Etale.stableUnderComposition _ _ hf hg

private theorem etRight {R S W : CommRingCat.{0}} {c : R ⟶ S} {f : S ⟶ W} (h1 : Et c) (h2 : Et (c ≫ f)) : Et f := by
  letI := c.hom.toAlgebra
  letI := f.hom.toAlgebra
  letI := (c ≫ f).hom.toAlgebra
  haveI : IsScalarTower R S W := .of_algebraMap_eq' rfl
  haveI : Algebra.Etale R S := h1
  haveI : Algebra.Etale R W := h2
  have h3 : Algebra.Etale S W := {
    formallyEtale := Algebra.FormallyEtale.of_restrictScalars (R := R)
    finitePresentation := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S W }
  exact h3

private theorem polySq {A S : CommRingCat.{0}} (f : A ⟶ S) :
    IsPushout (pC A) f (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) (pC S) := by
  have w : pC A ≫ CommRingCat.ofHom (Polynomial.mapRingHom f.hom) = f ≫ pC S := by
    ext a; simp
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (Polynomial.eval₂RingHom s.inr.hom (s.inl.hom Polynomial.X))) ?_ ?_ ?_⟩⟩
  · intro s
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have := congr($(s.condition).hom a)
      simpa using this.symm
    · simp
  · intro s
    ext a
    simp
  · intro s m h1 h2
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have := congr($(h2).hom a)
      simpa using this
    · have := congr($(h1).hom Polynomial.X)
      simpa using this

private theorem exPrime {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (h : IsPushout f g u v) (r : Ideal B) (s : Ideal C) [hr : r.IsPrime] [hs : s.IsPrime]
    (e : r.comap f.hom = s.comap g.hom) :
    ∃ p : Ideal D, p.IsPrime ∧ p.comap u.hom = r ∧ p.comap v.hom = s := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ h
  let x : Spec B := ⟨r, hr⟩
  let y : Spec C := ⟨s, hs⟩
  have hxy : Spec.map f x = Spec.map g y := PrimeSpectrum.ext e
  obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.map f) (g := Spec.map g) x y hxy
  let z' : Spec D := sq.isoPullback.inv z
  have e1 : Spec.map u z' = x := by
    rw [← h1, ← sq.isoPullback_inv_fst]; rfl
  have e2 : Spec.map v z' = y := by
    rw [← h2, ← sq.isoPullback_inv_snd]; rfl
  exact ⟨z'.asIdeal, z'.isPrime, congrArg PrimeSpectrum.asIdeal e1, congrArg PrimeSpectrum.asIdeal e2⟩

variable {q : ℕ} {i : ℤ}

private theorem bcBack {T K A Y C : CommRingCat.{0}} {k : T ⟶ K} {a : T ⟶ A} {w : K ⟶ Y} {φ : A ⟶ Y}
    (s : IsPushout k a w φ) {c : A ⟶ C} (h : BC q i k (a ≫ c)) : BC q i φ c :=
  fun _ _ _ s' => h _ _ _ (s.paste_vert s')

private theorem bcFwd {T K A Y C : CommRingCat.{0}} {k : T ⟶ K} {a : T ⟶ A} {w : K ⟶ Y} {φ : A ⟶ Y}
    (s : IsPushout k a w φ) {c : A ⟶ C} (h : BC q i φ c) : BC q i k (a ≫ c) :=
  BC.of_one (s.paste_vert (IsPushout.of_hasPushout φ c)) (h _ _ _ (IsPushout.of_hasPushout φ c))

private theorem coh (hLimit : Limit) (hAlg : AlgResProps) (hSHE : SHEqv) (hULA : ULA) (H : Hyp)
    (q : ℕ) [NeZero q] (i : ℤ) {T K A A' X : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A) (hq : IsUnit (q : T))
    (hk : AlgRes k) (hG : Good q i k t) (f : A ⟶ A') (hf : IE f) (hA' : SH A') (hX : SH X)
    (h : CommRingCat.of (Polynomial A') ⟶ X) (hh : IE h) (hl : IsLocalHom (pC A' ≫ h).hom) :
    BC q i k ((t ≫ f) ≫ pC A' ≫ h) := by
  have hqA : IsUnit (q : A) := by simpa using hq.map t.hom
  have hqA' : IsUnit (q : A') := by simpa using hqA.map f.hom
  have s0 := IsPushout.of_hasPushout k t
  have hL := hLimit H q i (pushout.inr k t) hqA (fun C c hc => bcBack s0 (hG C c hc)) A' f hf
  have s1 := IsPushout.of_hasPushout (pushout.inr k t) f
  have rψ := hL _ _ _ s1
  have aψ := hAlg.2.2.1 _ _ _ _ s1 (hAlg.2.2.1 _ _ _ _ s0 hk)
  have hU := hULA H q i h hqA' hA' hX hh hl _ _ aψ
  have s2 := IsPushout.of_hasPushout (pC A' ≫ h) (pushout.inr (pushout.inr k t) f)
  have rθ := hU _ _ _ s2
  have rx := hSHE H q i (pC A' ≫ h) hqA' hA' hX
  have rw₃ := RE.of_comp_left rx (g := pushout.inl (pC A' ≫ h) (pushout.inr (pushout.inr k t) f))
    (by rw [s2.w]; exact rψ.comp rθ)
  exact BC.of_one ((s0.paste_vert s1).paste_vert s2.flip) rw₃

private theorem geo (hSH : SHExists) (hIE : IEComp) {A U : CommRingCat.{0}}
    (c : CommRingCat.of (Polynomial A) ⟶ U) (hc : Et c) (r : Ideal U) (hr : r.IsPrime) :
    ∃ (A' X : CommRingCat.{0}) (f : A ⟶ A') (h : CommRingCat.of (Polynomial A') ⟶ X) (o : U ⟶ X) (Q : Ideal X),
      IE f ∧ SH A' ∧ SH X ∧ IE h ∧ IsLocalHom (pC A' ≫ h).hom ∧ IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
        pC A ≫ c ≫ o = f ≫ pC A' ≫ h := by
  obtain ⟨A', f, hf, hA', hfr⟩ := hSH A (r.comap (pC A ≫ c).hom) inferInstance
  obtain ⟨_, -⟩ := id hA'
  have hsq := IsPushout.of_hasPushout (pC A ≫ c) f
  obtain ⟨r', hr', e₁, e₂⟩ := exPrime hsq r (IsLocalRing.maximalIdeal A') (by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hfr a)
  obtain ⟨X, f₂, hf₂, hX, hfr₂⟩ := hSH _ r' hr'
  obtain ⟨_, -⟩ := id hX
  let u₁ := pushout.inl (pC A ≫ c) f
  let u₂ := pushout.inr (pC A ≫ c) f
  let h₀ : CommRingCat.of (Polynomial A') ⟶ pushout (pC A ≫ c) f :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom u₂.hom (u₁.hom (c.hom Polynomial.X)))
  have e0 : pC A' ≫ h₀ = u₂ := by
    ext a; simp [h₀]
  have e1 : CommRingCat.ofHom (Polynomial.mapRingHom f.hom) ≫ h₀ = c ≫ u₁ := by
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have := congr($(hsq.w).hom a)
      simpa [h₀, u₁, u₂] using this.symm
    · simp [h₀]
  have hpo : IsPushout (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) c h₀ u₁ :=
    IsPushout.of_top (by rw [e0]; exact hsq.flip) e1 (polySq f).flip
  have hh₀ : Et h₀ := etOfPushout hpo hc
  have e3 : (IsLocalRing.maximalIdeal X).comap f₂.hom = r' := by
    ext a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (hfr₂ a).symm
  refine ⟨A', X, f, h₀ ≫ f₂, u₁ ≫ f₂, IsLocalRing.maximalIdeal X, hf, hA', hX,
    hIE _ _ (MorphismProperty.le_ind _ _ hh₀) hf₂, ?_, hIE _ _ (ieOfPushout hsq hf) hf₂, inferInstance, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    by_contra hn
    have hm : a ∈ IsLocalRing.maximalIdeal A' := hn
    rw [← e₂, Ideal.mem_comap] at hm
    refine (hfr₂ _).1 hm ?_
    have e4 : (pC A' ≫ h₀ ≫ f₂) = u₂ ≫ f₂ := by rw [← Category.assoc, e0]
    rw [e4] at ha
    exact ha
  · rw [CommRingCat.hom_comp, ← Ideal.comap_comap, e3]
    exact e₁
  · rw [← Category.assoc (pC A') h₀ f₂, e0, ← Category.assoc f u₂ f₂]
    have e5 : f ≫ u₂ = (pC A ≫ c) ≫ u₁ := hsq.w.symm
    rw [e5]
    simp only [Category.assoc]

end UpperTheory.Cb.EtalePushouts

open UpperTheory.Cb.EtalePushouts in
theorem UpperTheory.Cb.strictHenselization_stalk_equiv_of_colimit_presentation :
    LateralTheory.E.t_E3Cut.Stalk → LateralTheory.E.t_E3Cut.Limit → LateralTheory.E.t_E3Cut.SHExists → LateralTheory.E.t_E3Cut.IEComp → LateralTheory.E.t_E3Cut.AlgResProps → LateralTheory.E.t_E3Cut.SHEqv → LateralTheory.E.t_E3Cut.ULA → LateralTheory.E.t_E3Cut.Step := by
  intro hStalk hLimit hSH hIE hAlg hSHE hULA H q _ i T K A k t hq hk hG B c hc
  have hqP : IsUnit (q : CommRingCat.of (Polynomial A)) := by simpa using hq.map (t ≫ pC A).hom
  have s := IsPushout.of_hasPushout k (t ≫ pC A)
  refine bcFwd s (hStalk H q i (pushout.inr k (t ≫ pC A)) hqP (fun _ c => Et c) ?_ ?_ ?_ B c hc)
  · intro C D E Z c f g u v sq hc hf hg
    rw [← Category.assoc]
    exact etComp hf (etOfPushout sq (etRight hc hg))
  · intro C D c f hc hf
    exact etComp hc hf
  · intro U c hc
    refine ⟨U, 𝟙 U, ?_, fun r hr => ⟨r, hr, Ideal.comap_id r⟩, ?_, fun r hr => ?_⟩
    · exact RingHom.isIntegral_of_surjective _ Function.surjective_id
    · simpa using hc
    · obtain ⟨A', X, f, h, o, Q, hf, hA', hX, hh, hl, ho, hQ, hQr, e⟩ := geo hSH hIE c hc r hr
      refine ⟨X, o, Q, ho, hQ, hQr, bcBack s ?_⟩
      have hb := coh hLimit hAlg hSHE hULA H q i k t hq hk hG f hf hA' hX h hh hl
      have e' : (t ≫ pC A) ≫ c ≫ 𝟙 U ≫ o = (t ≫ f) ≫ pC A' ≫ h := by
        simp only [Category.id_comp, Category.assoc]
        rw [e]
      rw [e']
      exact hb
end
end
