module

public import Development.EtaleCohomology.KummerTheory.Bundle001
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

lemma lk_aff (X : Scheme.{0}) (x : X) :
    ∃ (B : CommRingCat.{0}) (f : Spec B ⟶ X), IsOpenImmersion f ∧ x ∈ Set.range f :=
  by
  let 𝒰 := X.affineCover
  have h2 : IsOpenImmersion (𝒰.f (𝒰.idx x)) := inferInstance
  exact ⟨_, 𝒰.f (𝒰.idx x), h2, 𝒰.covers x⟩

lemma lk_etale {A B : CommRingCat.{0}} (f : A ⟶ B) (h : f.hom.Etale) : Etale (Spec.map f) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr h

lemma lk_fin {J : Type} [SmallCategory J] [IsFiltered J] (j₀ : J) {ι : Type} [Finite ι]
    (P : ι → ∀ {k : J}, (j₀ ⟶ k) → Prop)
    (hP : ∀ t {k k' : J} (f : j₀ ⟶ k) (g : k ⟶ k'), P t f → P t (f ≫ g))
    (h : ∀ t, ∃ (k : J) (f : j₀ ⟶ k), P t f) : ∃ (k : J) (f : j₀ ⟶ k), ∀ t, P t f := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (k : J) (f : j₀ ⟶ k), ∀ t ∈ s, P t f by
    obtain ⟨k, f, hf⟩ := H Finset.univ
    exact ⟨k, f, fun t => hf t (Finset.mem_univ t)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨j₀, 𝟙 _, by simp⟩
  | insert a s _ ih =>
    obtain ⟨k, f, hf⟩ := ih
    obtain ⟨k', f', hf'⟩ := h a
    obtain ⟨k'', g, g', hg⟩ := IsFiltered.span f f'
    refine ⟨k'', f ≫ g, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · rw [hg]; exact hP _ _ _ hf'
    · exact hP _ _ _ (hf t ht)

lemma lk_pull_spMap {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) {n i : ℤ} {q : ℕ} (x : Ht q (sp A) n i) :
    pull _ (spMap (f ≫ g).hom) _ _ x = pull _ (spMap g.hom) _ _ (pull _ (spMap f.hom) _ _ x) := by
  simp only [spMap, CommRingCat.ofHom_hom]
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

theorem locKer_of (hS : StrictHenselization) (hL : LhNat) : LocKer := by
  intro hA hB q _ X R p hq i r c M N n hiso U u y hy
  obtain ⟨B, ι, hι, b, hb⟩ := lk_aff U.left u
  obtain ⟨J, _, _, D, cc, hc, w, hSH, hw⟩ := hS B b
  obtain ⟨j₀⟩ := IsFiltered.nonempty (C := J)
  let φ : Spec cc.pt ⟶ U.left := Spec.map (w.app j₀ ≫ cc.ι.app j₀) ≫ ι
  let V' : Over (Spec R) := Over.mk (Spec.map (Spec.preimage (φ ≫ U.hom)))
  let g' : V' ⟶ U := Over.homMk φ (Spec.map_preimage (φ ≫ U.hom)).symm
  have h1 := hL hA q p i r c M n g' y
  rw [hy, map_zero] at h1
  have h2 := (hiso cc.pt (Spec.preimage (φ ≫ U.hom)) hSH).1 _ h1.symm
  let ψ : Spec (D.obj j₀) ⟶ U.left := Spec.map (w.app j₀) ≫ ι
  have hunit : ∀ j, IsUnit ((q : ℕ) : D.obj j) := by
    intro j
    have := hq.map (Spec.preimage (Spec.map (w.app j) ≫ ι ≫ U.hom)).hom
    simpa using this
  let z : ∀ t : (Σ a : Fin (M + 1), Fin (r a)), Ht q (sp (D.obj j₀)) (n - ((t.1 : ℕ) : ℤ)) 0 :=
    fun t => N • pull _ (sch.map ψ) _ _ (y t.1 t.2)
  have e1 : spMap (cc.ι.app j₀).hom ≫ sch.map ψ = sch.map φ := by
    simp only [spMap, CommRingCat.ofHom_hom, ψ, φ, ← Functor.map_comp, Spec.map_comp, Category.assoc]
  have hz : ∀ t, pull _ (spMap (cc.ι.app j₀).hom) _ _ (z t) = 0 := by
    intro t
    have := congrFun (congrFun h2 t.1) t.2
    simp only [Pi.smul_apply] at this
    simp only [z, map_nsmul]
    rw [← pull_comp, e1]
    exact this
  have hk : ∀ t, ∃ (k : J) (f : j₀ ⟶ k), pull _ (spMap (D.map f).hom) _ _ (z t) = 0 := fun t =>
    (hB q D cc hc _ _).2 j₀ (z t) (hunit j₀) (hz t)
  obtain ⟨k, F, hF⟩ := lk_fin j₀ (fun t {k} (f : j₀ ⟶ k) => pull _ (spMap (D.map f).hom) _ _ (z t) = 0)
    (fun t k k' f g hf => by simp only [Functor.map_comp, lk_pull_spMap, hf, map_zero]) hk
  let gl : Spec (D.obj k) ⟶ U.left := Spec.map (w.app k) ≫ ι
  have hwk : w.app k = w.app j₀ ≫ D.map F := by simpa using (w.naturality F)
  have := lk_etale _ (hw k).1
  obtain ⟨𝔮, h𝔮⟩ := (hw k).2
  refine ⟨Over.mk (gl ≫ U.hom), Over.homMk gl rfl, ⟨?_, 𝔮, ?_⟩, fun a s => ?_⟩
  · change Etale gl; infer_instance
  · change ι (Spec.map (w.app k) 𝔮) = u
    rw [← hb]; congr 1; exact PrimeSpectrum.ext h𝔮
  · have := hF ⟨a, s⟩
    have e2 : sch.map gl = spMap (D.map F).hom ≫ sch.map ψ := by
      simp only [gl, ψ, hwk, spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Functor.map_comp]
    change N • pull _ (sch.map gl) _ _ (y a s) = 0
    rw [e2, pull_comp, ← map_nsmul]
    exact this

end LateralTheory.KummerTheory.LHCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

def shvHomOf {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (F G : SlShv Λ S)
    (f : ∀ U : Over S, F.obj.obj (op U) →ₗ[ULift.{1} Λ] G.obj.obj (op U))
    (hf : ∀ (V U : Over S) (g : V ⟶ U) x, f V ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom (f U x)) : F ⟶ G :=
  ⟨{ app := fun U => ModuleCat.ofHom (f U.unop)
     naturality := by intro U V g; ext x; exact hf V.unop U.unop g.unop x }⟩

lemma sec_sub {Λ : Type} [CommRing Λ] {F : Shv Λ} (hF : IsZero F) (U : Scheme.{0}) : Subsingleton (Sec F U) := by
  constructor
  intro a b
  have h := hF.eq_of_src (𝟙 F) 0
  have ha : a = Sec.map (𝟙 F) a := rfl
  have hb : b = Sec.map (𝟙 F) b := rfl
  rw [ha, hb, h]
  rfl

lemma isZero_of_sub {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (F : SlShv Λ S)
    (h : ∀ U : Over S, Subsingleton (F.obj.obj (op U))) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact Subsingleton.elim _ _

theorem coneCx_of (h1 : ConeObj) (h2 : ConeAlg) : ConeCx := by
  intro Λ _ I J K μ hJ hK X S p r M γ hγ
  choose T hT e he using fun j : ℤ => h1 Λ J K hJ.1 hK.1 p r M j
  have hA := fun j : ℤ => h2 Λ μ p r M γ hγ j (j + 1) rfl
  let D : ∀ (j : ℤ) (U : Over S), (T j).obj.obj (op U) →ₗ[ULift.{1} Λ] (T (j + 1)).obj.obj (op U) :=
    fun j U => (e (j + 1) U).symm.toLinearMap ∘ₗ IsLinearMap.mk' _ (hA j U).1 ∘ₗ (e j U).toLinearMap
  have hD : ∀ (j : ℤ) (U : Over S) x, e (j + 1) U (D j U x) = cD μ p γ j (j + 1) rfl U (e j U x) := by
    intro j U x
    simp [D]
  let d : ∀ j : ℤ, T j ⟶ T (j + 1) := fun j => shvHomOf (T j) (T (j + 1)) (D j) (by
    intro V U g x
    refine (e (j + 1) V).injective ?_
    rw [hD, he, he, hD, ((hA j U).2.2 V g).2.1])
  have sq : ∀ j : ℤ, d j ≫ d (j + 1) = 0 := by
    intro j
    ext U x
    change D (j + 1) U.unop (D j U.unop x) = 0
    refine (e (j + 1 + 1) U.unop).injective ?_
    rw [hD, hD, (hA j U.unop).2.1, map_zero]
  refine ⟨CochainComplex.of T d sq, fun j => hT j, ?_, fun j U => (e j U).toAddEquiv, fun j V U g x => he j V U g x, ?_⟩
  · intro j hj
    apply isZero_of_sub
    intro U
    have : Subsingleton (Cone J K p r M j U) := by
      have h3 : ∀ (a : Fin (M + 1)) (s : Fin (r a)), Subsingleton (Sec (J.X (j + 1 - ((a : ℕ) : ℤ))) U.left) :=
        fun a s => sec_sub (hJ.2 _ (by omega)) _
      have h4 : Subsingleton (Sec (K.X j) (pullback p U.hom)) := sec_sub (hK.2 _ (by omega)) _
      constructor
      intro x y
      refine Prod.ext ?_ (Subsingleton.elim _ _)
      funext a s
      exact (h3 a s).elim _ _
    exact (e j U).injective.subsingleton
  · intro j j' h U x
    subst h
    have hd : (CochainComplex.of T d sq).d j (j + 1) = d j := CochainComplex.of_d _ _ _
    rw [hd]
    exact hD j U x

end LateralTheory.KummerTheory.LHCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.HomKillPf
open LateralTheory.KummerTheory.LHCut

lemma cover_mem {S : Scheme.{0}} {U : Over S} (V : U.left → Over S) (g : ∀ u, V u ⟶ U)
    (hg : ∀ u, Nbhd (g u) u) : Sieve.ofArrows V g ∈ (Scheme.etaleTopology.over S) U := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => ⟨x, ?_⟩, fun u => (hg u).1⟩
  obtain ⟨v, hv⟩ := (hg x).2
  exact ⟨v, hv⟩

lemma inj_app {Λ : Type} [CommRing Λ] {S : Scheme.{0}} {F G : SlShv Λ S} (f : F ⟶ G) [Mono f]
    (U : Over S) : Function.Injective (f.hom.app (op U)).hom := by
  rw [← ModuleCat.mono_iff_injective]
  have : Mono ((sheafToPresheaf _ _).map f) := inferInstance
  exact (NatTrans.mono_iff_mono_app _).1 this (op U)

variable {Λ : Type} [CommRing Λ] {S : Scheme.{0}}

lemma sec_eq_zero (F : SlShv Λ S) {U : Over S}
    (s : F.obj.obj (op U)) (R : Sieve U) (hR : R ∈ (Scheme.etaleTopology.over S) U)
    (h : ∀ (W : Over S) (f : W ⟶ U), R f → (F.obj.map f.op).hom s = 0) : s = 0 := by
  apply F.isSeparated U R hR s 0
  intro W f hf
  rw [h W f hf, map_zero]

lemma nsmul_app {F G : SlShv Λ S} (f : F ⟶ G) (N : ℕ)
    (U : Over S) (x : F.obj.obj (op U)) :
    ((N • f).hom.app (op U)).hom x = N • (f.hom.app (op U)).hom x := by
  induction N with
  | zero => simp
  | succ N ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl

lemma comp_sec {F G H : SlShv Λ S} (f : F ⟶ G) (g : G ⟶ H) (U : Over S) (x : F.obj.obj (op U)) :
    ((f ≫ g).hom.app (op U)).hom x = (g.hom.app (op U)).hom ((f.hom.app (op U)).hom x) := rfl

lemma nat_sec {F G : SlShv Λ S} (f : F ⟶ G) {U V : Over S} (g : V ⟶ U) (x : F.obj.obj (op U)) :
    (f.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((f.hom.app (op U)).hom x) := by
  have := congrArg (fun φ => φ.hom x) (f.hom.naturality g.op)
  simpa using this

lemma hom_eq_zero {F G : SlShv Λ S} (f : F ⟶ G)
    (h : ∀ (U : Over S) (x : F.obj.obj (op U)), (f.hom.app (op U)).hom x = 0) : f = 0 := by
  apply Sheaf.hom_ext
  ext U x
  exact h U.unop x

theorem homKill_of : HomKill := by
  intro Λ _ S C N j hloc
  rw [← cancel_epi (C.homologyπ j), comp_zero, Preadditive.comp_nsmul, Category.comp_id]
  apply hom_eq_zero
  intro U z
  rw [nsmul_app]
  have hx : ((C.d j (j + 1)).hom.app (op U)).hom ((C.iCycles j).hom.app (op U) |>.hom z) = 0 := by
    rw [← comp_sec, C.iCycles_d]; rfl
  choose V g hg y hy using hloc U _ hx
  apply sec_eq_zero _ _ (Sieve.ofArrows V g) (cover_mem V g hg)
  rintro W f ⟨Y, h, _, ⟨u⟩, rfl⟩
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  convert map_zero ((C.homology j).obj.map h.op).hom
  rw [map_nsmul, ← nat_sec, ← map_nsmul]
  have key : N • ((C.cycles j).obj.map (g u).op).hom z = ((C.toCycles (j - 1) j).hom.app (op (V u))).hom (y u) := by
    apply inj_app (C.iCycles j)
    rw [← comp_sec, C.toCycles_i, hy u, map_nsmul, nat_sec]
  rw [key, ← comp_sec, C.toCycles_comp_homologyπ]; rfl

end LateralTheory.KummerTheory.HomKillPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ConeAlgPf
open LateralTheory.KummerTheory.LHCut

variable {Λ : Type} [CommRing Λ]

theorem sres_comp {F : Shv Λ} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res h (Sec.res g a) = Sec.res (h ≫ g) a := by
  show (F.obj.map h.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (h ≫ g).op).hom a
  rw [op_comp, Functor.map_comp]
  rfl

theorem smap_res {F G : Shv Λ} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) :=
  (congrArg (fun k => k.hom a) (φ.hom.naturality g.op)).symm

theorem smap_comp {F G H : Shv Λ} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map ψ (Sec.map φ a) = Sec.map (φ ≫ ψ) a := rfl

theorem dd {C : Cx Λ} (i j k : ℤ) {U : Scheme.{0}} (a : Sec (C.X i) U) :
    Sec.map (C.d j k) (Sec.map (C.d i j) a) = 0 := by
  rw [smap_comp, HomologicalComplex.d_comp_d]; rfl

theorem leib' {I J K : Cx Λ} (μ : Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U)
    (b : Sec (J.X t) U) (ha : Sec.map (I.d s (s + 1)) a = 0) (t' w' : ℤ) (ht : t + 1 = t') (hw : w + 1 = w') :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = s.negOnePow • μ.mul U s t' w' (by omega) a (Sec.map (J.d t t') b) := by
  subst ht; subst hw
  rw [μ.leibniz, ha, map_zero, LinearMap.zero_apply, zero_add]

theorem rst_fst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    rst p g ≫ pullback.fst p U.hom = pullback.fst p V.hom := by
  simp only [rst, pullback.map]; erw [pullback.lift_fst]; simp

theorem rst_snd {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    rst p g ≫ pullback.snd p U.hom = pullback.snd p V.hom ≫ g.left := by
  simp only [rst, pullback.map]; erw [pullback.lift_snd]

theorem rst_comp {X S : Scheme.{0}} (p : X ⟶ S) {W V U : Over S} (g' : W ⟶ V) (g : V ⟶ U) :
    rst p (g' ≫ g) = rst p g' ≫ rst p g := by
  apply pullback.hom_ext
  · rw [Category.assoc, rst_fst, rst_fst, rst_fst]
  · rw [Category.assoc, rst_snd, rst_snd, ← Category.assoc, rst_snd, Category.assoc, Over.comp_left]

theorem smap_add {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _
theorem smap_sub {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub _ _ _
theorem smap_smul {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (c : ULift.{1} Λ) (a : Sec F U) :
    Sec.map φ (c • a) = c • Sec.map φ a := map_smul _ _ _
theorem smap_sum {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type*} (t : Finset ι) (f : ι → Sec F U) :
    Sec.map φ (∑ i ∈ t, f i) = ∑ i ∈ t, Sec.map φ (f i) := map_sum _ _ _
theorem sres_sub {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _
theorem sres_zero {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _
theorem sres_sum {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) {ι : Type*} (t : Finset ι) (f : ι → Sec F U) :
    Sec.res g (∑ i ∈ t, f i) = ∑ i ∈ t, Sec.res g (f i) := map_sum _ _ _

section Main
variable {I J K : Cx Λ} {r : ℕ → ℕ} {M : ℕ}

theorem usmul_map {F G : Shv Λ} (φ : F ⟶ G) {U : Scheme.{0}} (u : ℤˣ) (a : Sec F U) :
    Sec.map φ (u • a) = u • Sec.map φ a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem usmul_res {F : Shv Λ} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (a : Sec F U) :
    Sec.res g (u • a) = u • Sec.res g a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem dS_add (n m : ℤ) {U : Scheme.{0}} (b b' : FinalTheorems J r M n U) : dS n m (b + b') = dS n m b + dS n m b' := by
  funext a s
  simp only [dS, Pi.add_apply]
  rw [smap_add, smul_add]

theorem dS_smul (n m : ℤ) {U : Scheme.{0}} (c : ULift.{1} Λ) (b : FinalTheorems J r M n U) : dS n m (c • b) = c • dS n m b := by
  funext a s
  simp only [dS, Pi.smul_apply]
  rw [smap_smul, Units.smul_def, Units.smul_def, smul_comm]

theorem dS_dS (n m k : ℤ) {U : Scheme.{0}} (b : FinalTheorems J r M n U) : dS m k (dS n m b) = 0 := by
  funext a s
  simp only [dS, Pi.zero_apply]
  rw [usmul_map, dd, smul_zero, smul_zero]

variable (μ : Pair I J K) {X S : Scheme.{0}} (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem Phi_add (n w : ℤ) (h : n = w) (U : Over S) (b b' : FinalTheorems J r M n U.left) :
    Phi μ p γ n w h U (b + b') = Phi μ p γ n w h U b + Phi μ p γ n w h U b' := by
  simp only [Phi, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]

theorem Phi_smul (n w : ℤ) (h : n = w) (U : Over S) (c : ULift.{1} Λ) (b : FinalTheorems J r M n U.left) :
    Phi μ p γ n w h U (c • b) = c • Phi μ p γ n w h U b := by
  simp only [Phi, Pi.smul_apply, map_smul, Finset.smul_sum]

theorem d_Phi (hγ : Closed γ) (n w : ℤ) (h : n = w) (n' w' : ℤ) (hn : n + 1 = n') (hw : w + 1 = w') (U : Over S)
    (b : FinalTheorems J r M n U.left) :
    Sec.map (K.d w w') (Phi μ p γ n w h U b) = Phi μ p γ n' w' (by omega) U (dS n n' b) := by
  simp only [Phi, dS]
  rw [smap_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [smap_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have ha : Sec.map (I.d ((a : ℕ) : ℤ) ((a : ℕ) + 1)) (Sec.res (pullback.fst p U.hom) (γ a s)) = 0 := by
    rw [← smap_res, hγ]; exact sres_zero _
  rw [leib' μ _ _ _ _ _ _ _ ha (n' - ((a : ℕ) : ℤ)) w' (by omega) hw, usmul_res, smap_res, Units.smul_def,
    Units.smul_def, map_zsmul]

theorem Phi_res (n w : ℤ) (h : n = w) {V U : Over S} (g : V ⟶ U) (b : FinalTheorems J r M n U.left) :
    Sec.res (rst p g) (Phi μ p γ n w h U b) = Phi μ p γ n w h V (fun a s => Sec.res g.left (b a s)) := by
  simp only [Phi]
  rw [sres_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sres_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [μ.nat, sres_comp, sres_comp, sres_comp, rst_fst, rst_snd]

end Main

theorem coneAlg_of : ConeAlg := by
  intro Λ _ I J K μ X S p r M γ hγ j j' h U
  refine ⟨⟨fun x y => ?_, fun c x => ?_⟩, fun j'' h' x => ?_, fun V g => ⟨⟨fun x y => ?_, fun c x => ?_⟩, fun x => ?_,
    fun W g' x => ?_⟩⟩
  · refine Prod.ext (dS_add _ _ _ _) ?_
    show Phi μ p γ _ _ h U (x.1 + y.1) - Sec.map (K.d j j') (x.2 + y.2) = _
    rw [Phi_add, smap_add, add_sub_add_comm]; rfl
  · refine Prod.ext (dS_smul _ _ _ _) ?_
    show Phi μ p γ _ _ h U (c • x.1) - Sec.map (K.d j j') (c • x.2) = _
    rw [Phi_smul, smap_smul, ← smul_sub]; rfl
  · refine Prod.ext (dS_dS _ _ _ _) ?_
    show Phi μ p γ _ _ h' U (dS _ _ x.1) - Sec.map (K.d j' j'') (Phi μ p γ _ _ h U x.1 - Sec.map (K.d j j') x.2) = 0
    rw [smap_sub, d_Phi μ p γ hγ (j + 1) j' h (j' + 1) j'' (by omega) h', dd, sub_zero, sub_self]
  · refine Prod.ext ?_ (map_add _ _ _)
    funext a s; exact map_add _ _ _
  · refine Prod.ext ?_ (map_smul _ _ _)
    funext a s; exact map_smul _ _ _
  · refine Prod.ext ?_ ?_
    · funext a s
      show Sec.res g.left (_ • Sec.map _ _) = _ • Sec.map _ (Sec.res g.left _)
      rw [usmul_res, smap_res]
    · show Sec.res (rst p g) (Phi μ p γ _ _ h U x.1 - Sec.map (K.d j j') x.2) =
        Phi μ p γ _ _ h V (fun a s => Sec.res g.left (x.1 a s)) - Sec.map (K.d j j') (Sec.res (rst p g) x.2)
      rw [sres_sub, Phi_res, smap_res]
  · refine Prod.ext ?_ ?_
    · funext a s
      show Sec.res (g' ≫ g).left _ = Sec.res g'.left (Sec.res g.left _)
      rw [Over.comp_left, sres_comp]
    · show Sec.res (rst p (g' ≫ g)) x.2 = Sec.res (rst p g') (Sec.res (rst p g) x.2)
      rw [rst_comp, sres_comp]

end LateralTheory.KummerTheory.ConeAlgPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LhNatPf

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem rst_fst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    LateralTheory.KummerTheory.LHCut.rst p g ≫ pullback.fst p U.hom = pullback.fst p V.hom := by
  unfold LateralTheory.KummerTheory.LHCut.rst; rw [pullback.lift_fst, Category.comp_id]

theorem rst_snd {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) :
    LateralTheory.KummerTheory.LHCut.rst p g ≫ pullback.snd p U.hom = pullback.snd p V.hom ≫ g.left := by
  unfold LateralTheory.KummerTheory.LHCut.rst; rw [pullback.lift_snd]

theorem pull_pull (q : ℕ) {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {n i : ℤ} (x : Ht q E'' n i) :
    pull _ f _ _ (pull _ g _ _ x) = pull _ (f ≫ g) _ _ x := (pull_comp _ f g _ _ x).symm

theorem lhNat_of : LateralTheory.KummerTheory.LHCut.LhNat := by
  intro hA q _ X S p i r c M n V U g y
  unfold LateralTheory.KummerTheory.lh

  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
  unfold LateralTheory.KummerTheory.ext
  rw [pull_cast, (hA q).1, pull_pull, pull_pull, pull_pull, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, rst_fst, rst_snd]

end LateralTheory.KummerTheory.LhNatPf
end
end
