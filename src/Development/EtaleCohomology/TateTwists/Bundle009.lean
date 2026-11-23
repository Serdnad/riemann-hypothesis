module

public import Development.EtaleCohomology.TateTwists.Bundle003
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MvFree

theorem finsupp_mv {T α β γ M : Type*} [AddCommGroup M] (p1 : T → α) (p2 : T → β) (f : α → γ) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g) (hc : ∀ t, f (p1 t) = g (p2 t))
    (hj : ∀ t t', p1 t = p1 t' ∧ p2 t = p2 t' → t = t')
    (hs : ∀ x y, f x = g y → ∃ t, p1 t = x ∧ p2 t = y) :
    Function.Injective (Finsupp.mapDomain (M := M) p1) ∧
    ∀ (p : α →₀ M) (q : β →₀ M), Finsupp.mapDomain f p + Finsupp.mapDomain g q = 0 →
      ∃ c : T →₀ M, Finsupp.mapDomain p1 c = p ∧ Finsupp.mapDomain p2 c = -q := by
  classical
  have hp1 : Function.Injective p1 := fun t t' h =>
    hj t t' ⟨h, hg (by rw [← hc, ← hc, h])⟩
  have hh : Function.Injective (f ∘ p1) := hf.comp hp1
  refine ⟨Finsupp.mapDomain_injective hp1, fun p q hpq => ?_⟩
  set z := Finsupp.mapDomain f p with hz
  have hz' : z = Finsupp.mapDomain g (-q) := by
    have h0 : Finsupp.mapDomain g q + Finsupp.mapDomain g (-q) = 0 := by
      rw [← Finsupp.mapDomain_add, add_neg_cancel, Finsupp.mapDomain_zero]
    rw [hz]; exact (eq_neg_of_add_eq_zero_left hpq).trans (eq_neg_of_add_eq_zero_right h0).symm
  have hsupp : (z.support : Set γ) ⊆ Set.range (f ∘ p1) := by
    intro x hx
    have h1 : x ∈ Set.range f := by
      have := Finsupp.mapDomain_support (f := f) (s := p) (by rw [← hz]; exact hx)
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 this; exact ⟨a, rfl⟩
    have h2 : x ∈ Set.range g := by
      rw [hz'] at hx
      have := Finsupp.mapDomain_support (f := g) (s := -q) hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 this; exact ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := h1
    obtain ⟨b, hb⟩ := h2
    obtain ⟨t, ht, -⟩ := hs a b hb.symm
    exact ⟨t, by simp [ht]⟩
  refine ⟨Finsupp.comapDomain (f ∘ p1) z hh.injOn, ?_, ?_⟩
  · apply Finsupp.mapDomain_injective hf
    rw [← Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain _ hh _ hsupp]
  · apply Finsupp.mapDomain_injective hg
    have : g ∘ p2 = f ∘ p1 := funext fun t => (hc t).symm
    rw [← Finsupp.mapDomain_comp, this, Finsupp.mapDomain_comapDomain _ hh _ hsupp, hz']

theorem exact_of_eval {C D : Type*} [Category C] [Category D] [Abelian D]
    (S : ShortComplex (C ⥤ D)) (h : ∀ X, (S.map ((evaluation C D).obj X)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply Functor.isZero
  intro X
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (h X)).of_iso (S.mapHomologyIso ((evaluation C D).obj X)).symm

end LateralTheory.EtaleFoundations.MvFree

namespace LateralTheory.EtaleFoundations.MvFree

noncomputable def mvIso {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (G : C ⥤ D) [G.Additive] {X1 A B X3 : C}
    (a : X1 ⟶ A) (b : X1 ⟶ B) (c : A ⟶ X3) (d : B ⟶ X3)
    (w : biprod.lift a (-b) ≫ biprod.desc c d = 0)
    (w' : biprod.lift (G.map a) (-G.map b) ≫ biprod.desc (G.map c) (G.map d) = 0) :
    (ShortComplex.mk _ _ w).map G ≅ ShortComplex.mk _ _ w' := by
  haveI := preservesBinaryBiproducts_of_preservesBiproducts G
  exact ShortComplex.isoMk (Iso.refl _) (G.mapBiprod A B) (Iso.refl _)
    (by show 𝟙 _ ≫ biprod.lift (G.map a) (-G.map b) = G.map (biprod.lift a (-b)) ≫ (G.mapBiprod A B).hom
        rw [biprod.map_lift_mapBiprod, Functor.map_neg, Category.id_comp])
    (by
      show (G.mapBiprod A B).hom ≫ biprod.desc (G.map c) (G.map d) =
        G.map (biprod.desc c d) ≫ 𝟙 _
      rw [Category.comp_id, biprod.mapBiprod_hom_desc])

theorem mono_f_of_iso {C : Type*} [Category C] [HasZeroMorphisms C] {S T : ShortComplex C}
    (e : S ≅ T) [Mono S.f] : Mono T.f := by
  have h : T.f = e.inv.τ₁ ≫ S.f ≫ e.hom.τ₂ := by
    rw [← e.hom.comm₁₂, ← Category.assoc, ← ShortComplex.comp_τ₁, e.inv_hom_id, ShortComplex.id_τ₁,
      Category.id_comp]
  rw [h]; infer_instance

theorem biprod_ext_el {S : Type*} [Ring S] {A B : ModuleCat.{1} S} (z z' : ↑(A ⊞ B))
    (h1 : (biprod.fst : A ⊞ B ⟶ A) z = (biprod.fst : A ⊞ B ⟶ A) z')
    (h2 : (biprod.snd : A ⊞ B ⟶ B) z = (biprod.snd : A ⊞ B ⟶ B) z') :
    z = z' := by
  have e : ∀ w : ↑(A ⊞ B), (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) w) + (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) w) = w :=
    fun w => by
      have h := ConcreteCategory.congr_hom (biprod.total (X := A) (Y := B)) w
      rw [ConcreteCategory.id_apply] at h
      conv_rhs => rw [← h]
      rfl
  rw [← e z, ← e z', h1, h2]

theorem mc_exact {S : Type*} [Ring S] {X1 A B X3 : ModuleCat.{1} S} (u : X1 ⟶ A) (v : X1 ⟶ B)
    (c : A ⟶ X3) (d : B ⟶ X3) (w : biprod.lift u (-v) ≫ biprod.desc c d = 0)
    (hu : Function.Injective u)
    (hex : ∀ p q, c p + d q = 0 → ∃ x, u x = p ∧ v x = -q) :
    Mono (biprod.lift u (-v)) ∧ (ShortComplex.mk (biprod.lift u (-v)) (biprod.desc c d) w).Exact := by
  constructor
  · have : Mono u := (ModuleCat.mono_iff_injective u).2 hu
    have : Mono (biprod.lift u (-v) ≫ biprod.fst) := by rw [biprod.lift_fst]; infer_instance
    exact mono_of_mono _ biprod.fst
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x2 hx2
    have hx2' : c ((biprod.fst : A ⊞ B ⟶ A) x2) + d ((biprod.snd : A ⊞ B ⟶ B) x2) = 0 := by
      have h : (biprod.desc c d : A ⊞ B ⟶ X3) x2 = 0 := hx2
      rw [biprod.desc_eq] at h
      simpa using h
    obtain ⟨x, h1, h2⟩ := hex _ _ hx2'
    refine ⟨x, ?_⟩
    apply biprod_ext_el
    · dsimp; rw [← ConcreteCategory.comp_apply, biprod.lift_fst, h1]
    · dsimp; rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
      simp [h2]

theorem pointwise (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E) [Mono f] [Mono g]
    (X : Scheme.{0}ᵒᵖ) (w) :
    Mono (biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X)) ∧
    (ShortComplex.mk (biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X))
      (biprod.desc (((freeP R).map f).app X) (((freeP R).map g).app X)) w).Exact := by
  have hpb := (IsPullback.of_hasPullback f g).map ((evaluation _ _).obj X)
  rw [Types.isPullback_iff] at hpb
  obtain ⟨hw, hj, hs⟩ := hpb
  dsimp at hw hj hs
  have hf : Function.Injective (f.app X) := (mono_iff_injective (f.app X)).1 inferInstance
  have hg : Function.Injective (g.app X) := (mono_iff_injective (g.app X)).1 inferInstance
  obtain ⟨hinj, hex⟩ := finsupp_mv (M := ULift.{1} R)
    (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.fst f g).app X y.down))
    (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.snd f g).app X y.down))
    (fun y : ULift.{1} (P.obj X) => ULift.up (f.app X y.down))
    (fun y : ULift.{1} (Q.obj X) => ULift.up (g.app X y.down))
    (fun x y h => ULift.ext (hf (congrArg ULift.down h)))
    (fun x y h => ULift.ext (hg (congrArg ULift.down h)))
    (fun t => congrArg ULift.up (by simpa using ConcreteCategory.congr_hom hw t.down))
    (fun t t' h => ULift.ext (hj _ _ ⟨congrArg ULift.down h.1, congrArg ULift.down h.2⟩))
    (fun x y h => by
      obtain ⟨t, h1, h2⟩ := hs x.down y.down (congrArg ULift.down h)
      exact ⟨ULift.up t, congrArg ULift.up h1, congrArg ULift.up h2⟩)
  exact mc_exact _ _ _ _ w hinj (fun p q h => hex p q h)

end LateralTheory.EtaleFoundations.MvFree

namespace LateralTheory.EtaleFoundations

open MvFree in
theorem etale_free_presheaf_mayer_vietoris_short_exact_holds : EtaleFreePresheafMayerVietorisShortExact := by
  intro R _ P Q E f g _ _
  have w0 : biprod.lift ((freeP R).map (pullback.fst f g)) (-(freeP R).map (pullback.snd f g)) ≫
      biprod.desc ((freeP R).map f) ((freeP R).map g) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
      pullback.condition, add_neg_cancel]
  let S := ShortComplex.mk _ _ w0
  have hev : ∀ X, Mono ((S.map ((evaluation _ _).obj X)).f) ∧ (S.map ((evaluation _ _).obj X)).Exact := by
    intro X
    have w1 : biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X) ≫
        biprod.desc (((freeP R).map f).app X) (((freeP R).map g).app X) = 0 := by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
        ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]
    obtain ⟨hm, hx⟩ := pointwise R f g X w1
    let e := mvIso ((evaluation _ _).obj X) _ _ _ _ w0 w1
    exact ⟨@mono_f_of_iso _ _ _ _ _ e.symm hm, ShortComplex.exact_of_iso e.symm hx⟩
  have hSm : Mono S.f := by
    have : ∀ X, Mono (S.f.app X) := fun X => (hev X).1
    exact NatTrans.mono_of_mono_app _
  have hSe : S.Exact := exact_of_eval S (fun X => (hev X).2)
  let G := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  have w2 : biprod.lift (G.map ((freeP R).map (pullback.fst f g))) (-G.map ((freeP R).map (pullback.snd f g))) ≫
      biprod.desc (G.map ((freeP R).map f)) (G.map ((freeP R).map g)) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]
  let e := mvIso G _ _ _ _ w0 w2
  have hGm : Mono ((S.map G).f) := (inferInstance : Mono (G.map S.f))
  exact ⟨mono_f_of_iso e, w2, ShortComplex.exact_of_iso e (hSe.map G)⟩

end LateralTheory.EtaleFoundations
end

section

open Polynomial Finset GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.PrimPf

noncomputable def μ (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

lemma hμ (q : ℕ) [NeZero q] : IsPrimitiveRoot (μ q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma aeval_cyc {n : ℕ} (hn : 0 < n) {ν : ℂ} (h : IsPrimitiveRoot ν n) :
    aeval ν (cyclotomic n ℤ) = 0 := by
  rw [cyclotomic_eq_minpoly h hn]; exact minpoly.aeval _ _

lemma hom_aeval {S T : Type} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (f : S →+* T) (x : S) (p : ℤ[X]) :
    f (aeval x p) = aeval (f x) p := by
  rw [aeval_def, aeval_def, hom_eval₂]; congr 1; exact RingHom.ext_int _ _

abbrev R (q : ℕ) := AdjoinRoot (cyclotomic q ℤ)

noncomputable abbrev θ (q : ℕ) : R q := AdjoinRoot.root (cyclotomic q ℤ)

noncomputable def φ (q : ℕ) [NeZero q] : R q →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℤ ℂ) (μ q) (by rw [← aeval_def]; exact aeval_cyc (NeZero.pos q) (hμ q))

lemma φ_root (q : ℕ) [NeZero q] : φ q (θ q) = μ q := AdjoinRoot.lift_root _

lemma φ_inj (q : ℕ) [NeZero q] : Function.Injective (φ q) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [AdjoinRoot.mk_eq_zero]
  have h : aeval (μ q) p = 0 := by
    rw [φ, AdjoinRoot.lift_mk] at hx; rwa [aeval_def]
  rw [cyclotomic_eq_minpoly (hμ q) (NeZero.pos q)]
  exact minpoly.isIntegrallyClosed_dvd ((hμ q).isIntegral (NeZero.pos q)) h

noncomputable def ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : R q →+* A :=
  AdjoinRoot.lift (algebraMap ℤ A) ζ.1 (by rw [← aeval_def]; exact ζ.2.2)

lemma ψ_root {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ψ ζ (θ q) = ζ.1 :=
  AdjoinRoot.lift_root _

lemma θ_pow (q : ℕ) [NeZero q] : θ q ^ q = 1 :=
  φ_inj q (by rw [map_pow, φ_root, map_one, (hμ q).pow_eq_one])

lemma root_of_prim {q r a : ℕ} [NeZero q] (hr : 0 < r) (h : IsPrimitiveRoot (μ q ^ a) r) :
    aeval (θ q ^ a) (cyclotomic r ℤ) = 0 :=
  φ_inj q (by rw [hom_aeval (φ q), map_pow, φ_root, map_zero]; exact aeval_cyc hr h)

lemma image_range (q : ℕ) [NeZero q] :
    (range q).image (fun a => μ q ^ a) = nthRootsFinset q (1 : ℂ) := by
  ext x
  rw [mem_image, mem_nthRootsFinset (NeZero.pos q)]
  constructor
  · rintro ⟨a, -, rfl⟩; rw [← pow_mul, mul_comm, pow_mul, (hμ q).pow_eq_one, one_pow]
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx
    exact ⟨i, mem_range.2 hi, rfl⟩

lemma image_prim (q : ℕ) [NeZero q] :
    ((range q).filter (fun a => Nat.Coprime a q)).image (fun a => μ q ^ a) = primitiveRoots q ℂ := by
  ext x
  rw [mem_image, mem_primitiveRoots (NeZero.pos q)]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact (hμ q).pow_of_coprime a (mem_filter.1 ha).2
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx.pow_eq_one
    exact ⟨i, mem_filter.2 ⟨mem_range.2 hi, ((hμ q).pow_iff_coprime (NeZero.pos q) i).1 hx⟩, rfl⟩

lemma inj_on (q : ℕ) [NeZero q] (s : Finset ℕ) (hs : s ⊆ range q) :
    Set.InjOn (fun a => μ q ^ a) s := by
  intro i hi j hj h
  exact (hμ q).pow_inj (mem_range.1 (hs hi)) (mem_range.1 (hs hj)) h

lemma C_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (μ q ^ a)) = (X ^ q - 1 : ℂ[X]) := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos q) (hμ q), ← image_range,
    prod_image (inj_on q _ subset_rfl)]

lemma C_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (μ q ^ a)) = cyclotomic q ℂ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (hμ q), ← image_prim,
    prod_image (inj_on q _ (filter_subset _ _))]

lemma mapφ_C_prod (q : ℕ) [NeZero q] (s : Finset ℕ) :
    (∏ a ∈ s, (X - C (θ q ^ a))).map (φ q) = ∏ a ∈ s, (X - C (μ q ^ a)) := by
  simp [Polynomial.map_prod, φ_root]

lemma R_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (θ q ^ a)) = (X ^ q - 1 : (R q)[X]) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_all]; simp

lemma R_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (θ q ^ a))
      = (cyclotomic q ℤ).map (algebraMap ℤ (R q)) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_prim, Polynomial.map_map, ← map_cyclotomic_int]
  congr 1; exact RingHom.ext_int _ _

lemma C_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (μ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : ℂ[X]) := by
  have h := C_prod_all (n + 1)
  rw [prod_range_succ', pow_zero, ← geom_sum_mul, C_1] at h
  have hne : (X - 1 : ℂ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℂ)
  exact mul_right_cancel₀ hne h

lemma R_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (θ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : (R (n + 1))[X]) := by
  apply Polynomial.map_injective _ (φ_inj (n + 1))

  simp only [Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_sub, Polynomial.map_X,
  Polynomial.map_C, map_pow, φ_root, Polynomial.map_pow]
  simpa using C_prod_geom n

lemma eval_prod_ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) (f : ℕ → ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ f a))) = ∏ a ∈ s, (y - ζ.1 ^ f a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma eval_prod_ψ0 {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ a))) = ∏ a ∈ s, (y - ζ.1 ^ a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma unit_prod {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ i ∈ range (q - 1), (1 - ζ.1 ^ (i + 1)) = (q : A) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos q)).symm⟩
  have h := congrArg (eval₂ (ψ ζ) 1) (R_prod_geom n)
  rw [eval_prod_ψ ζ 1 _ (fun i => i + 1)] at h
  simpa [eval₂_finsetSum] using h

theorem cyclotomic_primitive_root_product_identities_of_adjoin_root : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  intro q _ A _
  have hq1 : ∀ ζ : Prim q A, ζ.1 ^ q = 1 := fun ζ => by
    rw [← ψ_root, ← map_pow, θ_pow, map_one]
  have hu : ∀ ζ : Prim q A, IsUnit ζ.1 := fun ζ =>
    IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) (by
      rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q), hq1])
  have hmod : ∀ (ζ : Prim q A) (a : ℕ), ζ.1 ^ a = ζ.1 ^ (a % q) := fun ζ a => by
    conv_lhs => rw [← Nat.mod_add_div a q, pow_add, pow_mul, hq1, one_pow, mul_one]
  have hlt : ∀ (ζ : Prim q A) (c d : ℕ), c < d → d < q → IsUnit (ζ.1 ^ c - ζ.1 ^ d) := by
    intro ζ c d hcd hd
    obtain ⟨i, rfl⟩ : ∃ i, d = c + (i + 1) := ⟨d - c - 1, by omega⟩
    have e : ζ.1 ^ c - ζ.1 ^ (c + (i + 1)) = ζ.1 ^ c * (1 - ζ.1 ^ (i + 1)) := by ring
    rw [e]
    refine ((hu ζ).pow c).mul (isUnit_of_dvd_unit ?_ ζ.2.1)
    have hd := dvd_prod_of_mem (fun j => 1 - ζ.1 ^ (j + 1)) (mem_range.2 (show i < q - 1 by omega))
    rw [unit_prod ζ] at hd
    exact hd
  refine ⟨hq1, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ a ha
    refine ⟨⟨ζ.1 ^ a, ζ.2.1, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim (NeZero.pos q) ((hμ q).pow_of_coprime a ha), map_zero]
  · intro ζ a b hab
    rw [hmod ζ a, hmod ζ b]
    have hne : a % q ≠ b % q := hab
    have ha := Nat.mod_lt a (NeZero.pos q)
    have hb := Nat.mod_lt b (NeZero.pos q)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt ζ _ _ h hb
    · have := (hlt ζ _ _ h ha).neg
      rwa [neg_sub] at this
  · intro ζ x hx
    have h := congrArg (eval₂ (ψ ζ) x) (R_prod_all q)
    rw [eval_prod_ψ0] at h
    simpa [hx] using h
  · intro ζ ξ
    have h := congrArg (eval₂ (ψ ζ) ξ.1) (R_prod_prim q)
    rw [eval_prod_ψ0, eval₂_map] at h
    rw [h]
    have e : (ψ ζ).comp (algebraMap ℤ (R q)) = algebraMap ℤ A := RingHom.ext_int _ _
    rw [e, ← aeval_def]; exact ξ.2.2
  · intro r hr ζ
    have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr (NeZero.pos q)
    have hur : IsUnit (r : A) := by
      obtain ⟨k, hk⟩ := hr
      have := ζ.2.1
      rw [hk, Nat.cast_mul] at this
      exact isUnit_of_mul_isUnit_left this
    refine ⟨⟨ζ.1 ^ (q / r), hur, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim hr0 ((hμ q).pow (NeZero.pos q) (Nat.div_mul_cancel hr).symm), map_zero]

end LateralTheory.EtaleFoundations.PrimPf
end
