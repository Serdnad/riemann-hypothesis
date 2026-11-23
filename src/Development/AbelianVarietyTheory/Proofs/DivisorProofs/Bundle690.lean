module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle653
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle654
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

lemma isIso_mapCechNerve_app_of_mono {A B C : PSh} (π : A ⟶ B) (ι : B ⟶ C) [Mono ι] (φ : A ⟶ C)
    (h : π ≫ ι = φ) (n : SimplexCategoryᵒᵖ) :
    IsIso ((Arrow.mapCechNerve
      (Arrow.homMk (𝟙 A) ι (by simp [h]) : Arrow.mk π ⟶ Arrow.mk φ)).app n) := by
  subst h
  have e : (Arrow.mapCechNerve
      (Arrow.homMk (𝟙 A) ι (by simp) : Arrow.mk π ⟶ Arrow.mk (π ≫ ι))).app n =
      WidePullback.lift (WidePullback.base (fun _ : Fin (n.unop.len + 1) => π) ≫ ι)
        (fun i => WidePullback.π (fun _ : Fin (n.unop.len + 1) => π) i)
        (fun j => by
          show _ ≫ (π ≫ ι) = _
          rw [← Category.assoc, WidePullback.π_arrow]) := by
    apply WidePullback.hom_ext
    · intro j
      erw [WidePullback.lift_π]
    · erw [WidePullback.lift_base]
  rw [e]
  refine ⟨WidePullback.lift (WidePullback.π _ 0 ≫ π) (fun i => WidePullback.π _ i) ?_, ?_, ?_⟩
  · intro i
    rw [← cancel_mono ι]
    simp only [Category.assoc]
    exact (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) i).trans
      (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) 0).symm
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_base]
      rw [← Category.assoc]
      erw [WidePullback.lift_π]
      exact WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π) 0
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_π, WidePullback.lift_π]
    · rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_base]
      rw [← Category.assoc]
      erw [WidePullback.lift_base]
      rw [Category.assoc]
      exact WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) 0

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_chains_cech_of_locSurj (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q)
    (hφ : ∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, φ.app (op V) x = Q.map g.op y) :
    QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from
      (Arrow.mk φ).augmentedCechNerve.hom)) := by
  let aφ : (Arrow.mk φ).cechNerve ⟶ disc.obj Q := (Arrow.mk φ).augmentedCechNerve.hom
  change QuasiIso ((chains R).map aφ)
  have hπι : Subfunctor.toRange φ ≫ (Subfunctor.range φ).ι = φ := Subfunctor.toRange_ι φ
  set π := Subfunctor.toRange φ with hπ
  set ι := (Subfunctor.range φ).ι with hι
  let F : Arrow.mk π ⟶ Arrow.mk φ := Arrow.homMk (𝟙 P) ι (by simp [hπι])
  let aπ : (Arrow.mk π).cechNerve ⟶ disc.obj _ := (Arrow.mk π).augmentedCechNerve.hom
  have sq : Arrow.mapCechNerve F ≫ aφ = aπ ≫ disc.map ι := by
    ext n : 1
    erw [NatTrans.comp_app, NatTrans.comp_app]
    erw [Arrow.augmentedCechNerve_hom_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
    rfl
  have hsurj : ∀ U, Function.Surjective (π.app U) := fun U =>
    (epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app _).1 (inferInstance : Epi π) U)
  have h1 : QuasiIso ((chains R).map aπ) := GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective R π hsurj
  have hιfree : IsIso ((free R).map ι) := by
    refine (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R ι).2.2 ?_ ?_
    · intro U y
      exact GlobalTheory.EtC.loc_calculus.2.1 U _ _ (hφ U y) fun V g ⟨x, hx⟩ => ⟨π.app (op V) x, hx⟩
    · intro U x x' hxx
      have : x = x' := Subtype.ext hxx
      subst this
      exact GlobalTheory.EtC.loc_calculus.1 U _ fun _ _ => rfl
  have h2 : IsIso ((chains R).map (disc.map ι)) :=
    isIso_chains_map_of_isIso_free R _ fun n => hιfree
  have h3 : IsIso ((chains R).map (Arrow.mapCechNerve F)) :=
    isIso_chains_map_of_isIso_free R _ fun n => by
      have := isIso_mapCechNerve_app_of_mono π ι φ hπι n
      exact Functor.map_isIso _ _
  have key : (chains R).map (Arrow.mapCechNerve F) ≫ (chains R).map aφ =
      (chains R).map aπ ≫ (chains R).map (disc.map ι) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq]
  rw [← quasiIso_iff_comp_left ((chains R).map (Arrow.mapCechNerve F)), key]
  haveI := h1
  haveI := h2
  have h2' : QuasiIso ((chains R).map (disc.map ι)) := inferInstance
  exact quasiIso_comp ((chains R).map aπ) ((chains R).map (disc.map ι)) (hφ := h1) (hφ' := h2')

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cup_supp_chainsMap_mono (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) :
    Mono (((chains R).map f).f p) := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
    have hnat := ((GlobalTheory.EtC.chains_basic R).2.1 f N)
    have hm : Mono ((free R).map (f.app (op (SimplexCategory.mk N)))) :=
      ((GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (f.app (op (SimplexCategory.mk N)))).1 inferInstance)
    have : ((chains R).map f).f (-(N : ℤ)) =
        ((chains R).map f).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom ≫ (chainsXIso R E N).inv := by simp
    rw [this, ← Category.assoc, hnat, Category.assoc]
    infer_instance
  · haveI := (GlobalTheory.EtC.chains_basic R).1 U
    exact IsZero.mono (isZero_of_isStrictlyLE _ 0 p hp) _

theorem cup_supp_extend (R : Type) [CommRing R] {I : Cx R} (hI : ∀ s, Injective (I.X s)) {U E : Spc} (f : U ⟶ E) [Mono f]
    {n : ℤ} (β : Cochain ((chains R).obj U) I n) :
    ∃ β' : Cochain ((chains R).obj E) I n, (Cochain.ofHom ((chains R).map f)).comp β' (zero_add n) = β := by
  refine ⟨Cochain.mk fun p q h => by
    haveI := cup_supp_chainsMap_mono R f p
    haveI := hI q
    exact Injective.factorThru (β.v p q h) (((chains R).map f).f p), ?_⟩
  refine Cochain.ext _ _ fun p q h => ?_
  haveI := cup_supp_chainsMap_mono R f p
  haveI := hI q
  rw [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) h, Cochain.ofHom_v, Cochain.mk_v]
  exact Injective.comp_factorThru (J := I.X q) (β.v p q h) (((chains R).map f).f p)

theorem cup_supp_vanish (R : Type) [CommRing R] {K : Cx R} {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g)
    {k : ℤ} (γ : Cochain ((chains R).obj E) K k)
    (hf : (Cochain.ofHom ((chains R).map f)).comp γ (zero_add k) = 0)
    (hg : (Cochain.ofHom ((chains R).map g)).comp γ (zero_add k) = 0) : γ = 0 := by
  refine Cochain.ext _ _ fun p q h => ?_
  rw [Cochain.zero_v]
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
    have hf' := congrArg (fun z => z.v (-(N : ℤ)) q h) hf
    have hg' := congrArg (fun z => z.v (-(N : ℤ)) q h) hg
    simp only [Cochain.comp_v _ _ (zero_add k) (-(N : ℤ)) (-(N : ℤ)) q (add_zero _) h, Cochain.ofHom_v,
      Cochain.zero_v] at hf' hg'
    have nf := (GlobalTheory.EtC.chains_basic R).2.1 f N
    have ng := (GlobalTheory.EtC.chains_basic R).2.1 g N
    haveI := hc.2.2 (op (SimplexCategory.mk N))
    have key : biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
        ((free R).map (g.app (op (SimplexCategory.mk N)))) ≫ ((chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h) = 0 := by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, comp_zero]
        have : (free R).map (f.app (op (SimplexCategory.mk N))) =
            (chainsXIso R U N).inv ≫ ((chains R).map f).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom := by
          rw [nf]; simp
        rw [this]; simp [hf']
      · rw [biprod.inr_desc_assoc, comp_zero]
        have : (free R).map (g.app (op (SimplexCategory.mk N))) =
            (chainsXIso R V N).inv ≫ ((chains R).map g).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom := by
          rw [ng]; simp
        rw [this]; simp [hg']
    have h0 : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h = 0 := by
      rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
        ((free R).map (g.app (op (SimplexCategory.mk N))))), key, comp_zero]
    have : γ.v (-(N : ℤ)) q h = (chainsXIso R E N).hom ≫ ((chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h) := by simp
    rw [this, h0, comp_zero]
  · haveI := (GlobalTheory.EtC.chains_basic R).1 E
    exact (isZero_of_isStrictlyLE _ 0 p hp).eq_of_src _ _

theorem cup_supp_rep (R : Type) [CommRing R] {I : Cx R} (hI : ∀ s, Injective (I.X s)) {U E : Spc} (f : U ⟶ E) [Mono f]
    {n : ℤ} (a : CohomologyClass ((chains R).obj E) I n) (ha : cpull ((chains R).map f) I n a = 0) :
    ∃ α : Cocycle ((chains R).obj E) I n, CohomologyClass.mk α = a ∧
      (Cochain.ofHom ((chains R).map f)).comp α.1 (zero_add n) = 0 := by
  obtain ⟨α, rfl⟩ := a.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 at ha
  rw [CohomologyClass.mk_eq_zero_iff] at ha
  obtain ⟨n', hn', β, hβ⟩ := ha
  have hβ2 : δ n' n β = (Cochain.ofHom ((chains R).map f)).comp α.1 (zero_add n) := hβ
  obtain ⟨β', hβ'⟩ := cup_supp_extend R hI f β
  let c : Cocycle ((chains R).obj E) I n := Cocycle.mk (δ n' n β') (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', β', rfl⟩
  · change (Cochain.ofHom ((chains R).map f)).comp (α.1 - δ n' n β') (zero_add n) = 0
    rw [Cochain.comp_sub, ← δ_ofHom_comp, hβ', hβ2, sub_self]

theorem cup_supp (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (hI : ∀ s, Injective (I.X s))
    (hJ : ∀ s, Injective (J.X s)) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) {n m k : ℤ}
    (hk : n + m = k) (a : CohomologyClass ((chains R).obj E) I n) (b : CohomologyClass ((chains R).obj E) J m)
    (ha : cpull ((chains R).map f) I n a = 0) (hb : cpull ((chains R).map g) J m b = 0) : μ.cup E hk a b = 0 := by
  haveI := hc.1
  haveI := hc.2.1
  obtain ⟨α, rfl, hα⟩ := cup_supp_rep R hI f a ha
  obtain ⟨β, rfl, hβ⟩ := cup_supp_rep R hJ g b hb
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ hk).2 α β γ hγ, CohomologyClass.mk_eq_zero_iff]
  have evK := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := K) (n := k)
  have evI := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)
  have evJ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := J) (n := m)
  have h1 : (Cochain.ofHom ((chains R).map f)).comp γ.1 (zero_add k) = 0 := by
    have evKU := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := U) (I := K) (n := k)
    have evIU := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := U) (I := I) (n := n)
    apply evKU.2.2.1
    intro N w h U' x
    rw [evK.2.2.2.1 f γ.1 N w h U' x, (evKU.1 0 0 N w h U' x).2.2.1, hγ N w h U' (x.map f)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.2.1 0 i (by omega)).2.1 f,
      ← evI.2.2.2.1 f α.1, hα, (evIU.1 0 0 _ _ rfl U' (x.sub 0 i (by omega))).2.2.1]
    simp
  have h2 : (Cochain.ofHom ((chains R).map g)).comp γ.1 (zero_add k) = 0 := by
    have evKV := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := V) (I := K) (n := k)
    have evJV := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := V) (I := J) (n := m)
    apply evKV.2.2.1
    intro N w h U' x
    rw [evK.2.2.2.1 g γ.1 N w h U' x, (evKV.1 0 0 N w h U' x).2.2.1, hγ N w h U' (x.map g)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.2.1 i (N - i) (by omega)).2.1 g,
      ← evJ.2.2.2.1 g β.1, hβ, (evJV.1 0 0 _ _ rfl U' (x.sub i (N - i) (by omega))).2.2.1]
    simp
  have h0 : γ = 0 := Cocycle.ext (cup_supp_vanish R f g hc γ.1 h1 h2)
  rw [h0]
  exact zero_mem _

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.TwResExt

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (f : F ⟶ G) (g : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem twRes_ext : ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧
    (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
    IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧
    ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u') := by
  intro q _ i
  obtain ⟨hKI, hInj, hGE, hQI, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  refine ⟨⟨hGE, resAug _, hQI, fun _ _ => rfl⟩, fun t => ?_, ?_⟩
  · haveI := hInj t
    exact (GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf q ((res _ (tw q i)).X t)).2
  intro T e ⟨_, ε, hε, he⟩
  have hext := GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) (tw q i) T (res _ (tw q i)) ε
  refine ⟨?_, fun u u' huu => ?_⟩
  · obtain ⟨m, hm⟩ := hext.1 (resAug _)
    refine ⟨m, fun U ζ => ?_⟩
    rw [← he U ζ, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]
    rfl
  · refine hext.2 u u' ?_
    have htw := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2
    obtain ⟨hres, hrel, huniq⟩ := htw
    let ψ : (T ⟶ res _ (tw q i)) → (tw q i ⟶ (res _ (tw q i)).X 0) := fun v => sglι (tw q i) ≫ (ε ≫ v).f 0
    have key : ∀ v : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (ψ v) (twGen i ζ) = Sec.map (v.f 0) (e U ζ) := by
      intro v U ζ
      rw [← he U ζ]
      rfl
    have hnat : ∀ v : T ⟶ res _ (tw q i), ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
        Sec.res g (Sec.map (ψ v) (twGen i ζ)) = Sec.map (ψ v) (twGen i (ζ.map g.appTop.hom)) := by
      intro v V U g ζ
      rw [← hres V U g ζ]
      exact (congrArg (fun f => f.hom (twGen i ζ)) ((ψ v).hom.naturality g.op)).symm
    have hrl : ∀ v : T ⟶ res _ (tw q i), ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ),
        ξ.1 = ζ.1 ^ (a : ZMod q).val →
        Sec.map (ψ v) (twGen i ξ) = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • Sec.map (ψ v) (twGen i ζ) := by
      intro v U ζ ξ a h
      rw [hrel U ζ ξ a h]
      exact map_nsmul _ _ _
    obtain ⟨φ, -, hφ⟩ := huniq ((res _ (tw q i)).X 0) (fun U ζ => Sec.map (ψ u) (twGen i ζ)) (hnat u) (hrl u)
    have h1 := hφ (ψ u) fun U ζ => rfl
    have h2 := hφ (ψ u') fun U ζ => by rw [key, key, huu]
    have h12 : ψ u = ψ u' := h2.symm ▸ h1 ▸ rfl
    apply HomologicalComplex.from_single_hom_ext
    exact (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)) _ _).1 h12

end GlobalTheory.EtC.TwResExt
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing : ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b) := by
  first | (exact @GlobalTheory.cup_natural_in_pairing) | (exact GlobalTheory.cup_natural_in_pairing) | (intros; apply GlobalTheory.cup_natural_in_pairing  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_connecting_cocycle_hypercohomology_les : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1,
    (∀ (K : Cx R) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
      Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))) ∧
    ∃ s : ℤˣ, ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
      S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
      ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w := by
  first | (exact @GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (exact GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (intros; apply GlobalTheory.EtC.LesChar.exists_connecting_cocycle  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_semiMap_of_tensorPairing : ∀ (Q : ℕ) (R : Type) [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J'), ∃ σ : SemiMap T K', ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U), σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
  first | (exact @GlobalTheory.EtC.semiMap_of_tensorPair) | (exact GlobalTheory.EtC.semiMap_of_tensorPair) | (intros; apply GlobalTheory.EtC.semiMap_of_tensorPair  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.sheafCohomologyClass_subsingleton_of_acyclic_boundedBelow : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (a : ℤ) [M.IsStrictlyGE a], M.Acyclic → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.X t)) i)) → ∀ n : ℤ, Subsingleton (CohomologyClass (sgl G) M n) := by
  first | (exact @GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (exact GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (intros; apply GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.unitSection_multiplication_chainMap : ∀ (q : ℕ) [NeZero q] (i k : ℤ) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k))) (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i)), (∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) → ∃ u : D ⟶ res _ (tw q k), ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (s : ℤ) (b : Sec (D.X s) U), Sec.map (u.f s) b = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b) := by
  first
  | exact @GlobalTheory.EtC.unit_mul_chain_map
  | exact GlobalTheory.EtC.unit_mul_chain_map
  | (intros; apply GlobalTheory.EtC.unit_mul_chain_map <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem Sec.res_map_of_sheaf_morphism {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have h := congrArg (fun h => h.hom x) (f.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem Sec.map_nsmul_of_sheaf_morphism {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map f (n • x) = n • Sec.map f x := map_nsmul (f.hom.app (op U)).hom n x

theorem nsmul_eq_of_natCast_eq_zmod_ulift_module {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {m n : ℕ}
    (h : (m : ZMod q) = (n : ZMod q)) (x : M) : m • x = n • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) m x, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) n x]
  congr 1
  apply ULift.ext
  simpa using h

theorem twist_mul_map : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)}
    (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), ∃ φ : tw q k ⟶ K.X 0, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) := by
  intro q _ i j k hk K τ
  obtain ⟨-, -, -, h4i, h5i, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
  obtain ⟨-, -, -, h4j, h5j, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q j
  obtain ⟨-, -, -, -, -, h6⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q k
  let e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (K.X 0) U := fun U ζ =>
    τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))
  have hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    simp only [e]
    rw [τ.nat, Sec.res_map_of_sheaf_morphism, Sec.res_map_of_sheaf_morphism, h4i, h4j]
  have hrel : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ k : (ZMod q)ˣ) : ZMod q).val • e U ζ := by
    intro U ζ ξ a h
    simp only [e]
    rw [h5i U ζ ξ a h, h5j U ζ ξ a h, Sec.map_nsmul_of_sheaf_morphism, Sec.map_nsmul_of_sheaf_morphism, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul]
    apply nsmul_eq_of_natCast_eq_zmod_ulift_module (q := q)
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id,
      ← hk, zpow_add, Units.val_mul, mul_comm]
  obtain ⟨φ, hφ, -⟩ := h6 (K.X 0) e hnat hrel
  exact ⟨φ, hφ⟩

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.mappingCone_terms_sheafExt_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) {C J : Cx R} (u : C ⟶ J), (∀ t, Injective (J.X t)) → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (C.X t)) i)) → ∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R ((mappingCone u).X t)) i) := by
  first | (exact @GlobalTheory.cone_terms_ext_subsingleton) | (exact GlobalTheory.cone_terms_ext_subsingleton) | (intros; apply GlobalTheory.cone_terms_ext_subsingleton  <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem idempotent_split (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k)
    (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (h2 : v ≫ u = 0) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G) (q : G ⟶ K), i ≫ q = 𝟙 K ∧ q ≫ i = v ∧
      ∀ n : ℕ, Function.Surjective (i.app n) ∧ RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  obtain ⟨h₀, hrank⟩ := @kerIdeal_finrank_eq_pow_of_idempotent p _ k _ G u v huv h1 h2
  obtain ⟨K, i, hi⟩ := @KerGrp.exists_kernel p _ k _ G u h₀ hrank
  obtain ⟨hfac, hcan⟩ := factor_closedImmersion p k K G i (fun n => (hi n).1)
  have hvu : v + u = 𝟙 G := by rw [add_comm]; exact huv
  have hker : ∀ n, RingHom.ker (i.app n) = RingHom.ker (v.app n) := fun n => by
    rw [(hi n).2, ker_app_eq_kerIdeal_of_idempotents p k G v u hvu h2 h1 n]
  obtain ⟨q, hq⟩ := hfac G v (fun n => (hker n).le)
  have hiu : i ≫ u = 0 := by
    refine Hom.ext (funext fun n => BialgHom.ext fun b => ?_)
    have h := (kerIdeal_le_ker_iff (u.app n) (i.app n : G.A n →ₐ[k] K.A n)).1 (hi n).2.ge b
    change i.app n (u.app n b) = (1 : WithConv (G.A n →ₐc[k] K.A n)).ofConv b
    refine Eq.trans h ?_
    simp
  have hiv : i ≫ v = i := by
    have e := Preadditive.comp_add _ _ _ i u v
    rw [huv, hiu, zero_add, Category.comp_id] at e
    exact e.symm
  refine ⟨K, i, q, ?_, hq, hi⟩
  apply hcan K
  rw [Category.assoc, hq, hiv, Category.id_comp]

end PDivGroup

end GlobalTheory
end
end
