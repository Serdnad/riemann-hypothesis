module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle121
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem clopenCond_injective_geom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) := by
  intro p _ D R _ b N w0 r hw S _ s o K κ hKf hKe hκ hrep Z et hZf hZe hadd hlin hvan
  have hkill : ∀ y, ∀ c ∈ w0 ^ r, et y ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro y c hc
    rw [← hlin]
    exact hvan _ (Submodule.subset_span ⟨c, hc, y, rfl⟩)
  have h0 : et 0 = 1 := hvan 0 (Submodule.zero_mem _)
  have hE : ∀ y, GlobalTheory.LevCover.ClopenCond Z fun _ h => h ≫ et y = 1 := by
    intro y
    obtain ⟨u, hu, -⟩ := hrep Z (et y) (hkill y)
    obtain ⟨u0, hu0, -⟩ := hrep Z (et 0) (hkill 0)
    refine (GlobalTheory.LevCover.clopenCond_eq u u0).congr fun T' h => ⟨fun H => ?_, fun H => ?_⟩
    · have hk : ∀ c ∈ w0 ^ r, (h ≫ et y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
        rw [Category.assoc, hkill y c hc, MonObj.comp_one]
      refine (hrep T' (h ≫ et y) hk).unique ?_ ?_
      · rw [Category.assoc, hu]
      · rw [Category.assoc, hu0, h0, MonObj.comp_one, H]
    · rw [← hu, ← Category.assoc, H, Category.assoc, hu0, h0, MonObj.comp_one]
  have hP : ∀ y, GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Sp k ⟶ T'.left),
      (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r := by
    intro y
    by_cases hy : y ∈ wSub D w0 r
    · exact ⟨⊤, isClosed_univ, fun T' h => ⟨fun _ => by simp, fun _ _ _ _ _ _ => hy⟩⟩
    · obtain ⟨U, hU, H⟩ := hE y
      refine ⟨⟨(U : Set Z.left)ᶜ, hU.isOpen_compl⟩, U.isOpen.isClosed_compl, fun T' h =>
        ⟨fun P => ?_, fun hsub k _ _ x hx => ?_⟩⟩
      · rintro _ ⟨t, rfl⟩ ht
        obtain ⟨k, _, _, a, ha⟩ := FinEt.exists_algClosed_point T'.left t
        apply hy
        refine P k a ?_
        rw [← Category.assoc]
        refine (H _ _).2 ?_
        rintro _ ⟨q, rfl⟩
        have haq : a q = t := (ha ▸ Set.mem_range_self q : a q ∈ ({t} : Set T'.left))
        simp only [Over.comp_left, Over.homMk_left, Scheme.Hom.comp_apply, haq]
        exact ht
      · rw [← Category.assoc] at hx
        have hr := (H _ _).1 hx
        obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
        exact (hsub ⟨x q, rfl⟩ (hr ⟨q, by simp⟩)).elim
  haveI := D.freeLa
  haveI := D.finLa
  have hpos : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  obtain ⟨κ', _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod D.La hpos
  have hpr : ∀ c : D.La, (p ^ r) • c ∈ wSub D w0 r := by
    intro c
    refine Submodule.subset_span ⟨(p : 𝓞 D.F) ^ r, Ideal.pow_mem_pow hw.2.1 r, c, ?_⟩
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine (GlobalTheory.LevCover.ClopenCond.forall_of_finite q hP ?_).congr fun T' h => ?_
  · intro i j hij T' h Pi k _ _ x hx
    obtain ⟨c, rfl⟩ := hq i j hij
    have he : et (i + p ^ r • c) = et i := by rw [hadd, hvan _ (hpr c), _root_.mul_one]
    rw [he] at hx
    exact (wSub D w0 r).add_mem (Pi k x hx) (hpr c)
  · exact ⟨fun H y k _ _ x => H k x y, fun H k _ _ x y => H y k x⟩

end GlobalTheory.UPel.HT.EtLev
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev.Onto

theorem range_sp_subset_iff {k : Type} [Field k] {X : Scheme.{0}} (f : Sp k ⟶ X) (U : Set X) :
    Set.range f ⊆ U ↔ ∃ t, f t ∈ U := by
  haveI : Unique (Sp k) := inferInstanceAs (Unique (PrimeSpectrum k))
  constructor
  · intro h
    exact ⟨default, h ⟨default, rfl⟩⟩
  · rintro ⟨t, ht⟩ _ ⟨t', rfl⟩
    rwa [Subsingleton.elim t' t]

theorem range_sp_subset_compl {k : Type} [Field k] {X : Scheme.{0}} (f : Sp k ⟶ X) (U : Set X) :
    Set.range f ⊆ Uᶜ ↔ ¬ Set.range f ⊆ U := by
  haveI : Unique (Sp k) := inferInstanceAs (Unique (PrimeSpectrum k))
  rw [range_sp_subset_iff, range_sp_subset_iff]
  constructor
  · rintro ⟨t, ht⟩ ⟨t', ht'⟩
    rw [Subsingleton.elim t' t] at ht'
    exact ht ht'
  · intro h
    exact ⟨default, fun h' => h ⟨default, h'⟩⟩

end GlobalTheory.UPel.HT.EtLev.Onto

namespace GlobalTheory.UPel.HT.EtLev

open GlobalTheory.UPel.HT.EtLev.Onto

theorem clopenCond_onto : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), ∀ g : Over.mk (x ≫ T'.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = g := by
  intro p _ D R _ b N w0 r hw S _ s o K κ hKf hKe hκ hrep Z et hZf hZe hadd hlin hker
  haveI := hKf; haveI := hKe; haveI := hZf; haveI := hZe
  have hkc : ∀ (T T' : Over S) (f : T ⟶ T') (g : T' ⟶ o.A),
      (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
      ∀ c ∈ w0 ^ r, (f ≫ g) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T T' f g hg c hc
    rw [Category.assoc, hg c hc, MonObj.comp_one]
  have hetk : ∀ a, ∀ c ∈ w0 ^ r, et a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun a c hc => by
    rw [← hlin]
    exact hker _ (Submodule.subset_span ⟨c, hc, a, rfl⟩)
  have huniq : ∀ (T : Over S) (y y' : T ⟶ K), y ≫ κ = y' ≫ κ → y = y' := fun T y y' h =>
    (hrep T (y' ≫ κ) (hkc _ _ y' κ hκ)).unique h rfl
  choose lam hlam using fun a => (hrep Z (et a) (hetk a)).exists
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨J, _, q, hq⟩ := LevCover.exists_finite_mod D.La (pow_pos (Fact.out : p.Prime).pos r)
  have hlamq : ∀ a a', q a = q a' → lam a = lam a' := by
    intro a a' h
    obtain ⟨c, rfl⟩ := hq a a' h
    have hm : p ^ r • c ∈ wSub D w0 r := by
      refine Submodule.subset_span ⟨(p : 𝓞 D.F) ^ r, Ideal.pow_mem_pow hw.2.1 r, c, ?_⟩
      rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    apply huniq
    rw [hlam, hlam, hadd, hker _ hm, _root_.mul_one]
  have hfin : (Set.range lam).Finite := by
    refine (Set.finite_range fun j : Set.range q => lam j.2.choose).subset ?_
    rintro _ ⟨a, rfl⟩
    refine ⟨⟨q a, Set.mem_range_self a⟩, ?_⟩
    exact hlamq _ _ (Classical.choose_spec (Set.mem_range_self (f := q) a))
  obtain ⟨hPf, hPe⟩ := LevCover.finiteEtale_tensor Z K
  haveI := hPf; haveI := hPe
  let U : (Z ⟶ K) → (Z ⊗ K).left.Opens := fun l => (LevCover.clopenCond_eq (snd Z K) (fst Z K ≫ l)).choose
  have hU : ∀ l, IsClosed (U l : Set (Z ⊗ K).left) ∧ ∀ (T' : Over S) (h : T' ⟶ Z ⊗ K),
      h ≫ snd Z K = h ≫ fst Z K ≫ l ↔ Set.range h.left ⊆ U l := fun l =>
    (LevCover.clopenCond_eq (snd Z K) (fst Z K ≫ l)).choose_spec
  let C : Set (Z ⊗ K).left := ⋂ l ∈ Set.range lam, (U l : Set (Z ⊗ K).left)ᶜ
  have hCo : IsOpen C := hfin.isOpen_biInter fun l _ => (hU l).1.isOpen_compl
  have hCc : IsClosed C := isClosed_biInter fun l _ => (U l).isOpen.isClosed_compl
  obtain ⟨V, i, hVf, hVe, -, hV⟩ := LevCover.exists_sub (Z := Z ⊗ K) ⟨C, hCo⟩ hCc
  haveI := hVf; haveI := hVe
  obtain ⟨I, hIc, hI⟩ := LevCover.exists_image (i ≫ fst Z K)
  have hA : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ Z),
      Set.range z.left ⊆ (I : Set Z.left)ᶜ ↔ ∀ g : Over.mk x ⟶ o.A,
        (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ a, z ≫ et a = g := by
    intro k _ _ x z
    rw [range_sp_subset_compl, hI k x z]
    constructor
    · intro hno g hg
      by_contra hne
      push_neg at hne
      obtain ⟨y, hy, -⟩ := hrep _ g hg
      apply hno
      have hmem : Set.range (lift z y).left ⊆ C := by
        refine Set.subset_iInter₂ fun l hl => ?_
        obtain ⟨a, rfl⟩ := hl
        rw [range_sp_subset_compl, ← (hU _).2]
        intro h
        simp only [lift_snd, lift_fst_assoc] at h
        apply hne a
        rw [← hy, h, Category.assoc, hlam]
      obtain ⟨w, hw⟩ := (hV _ (lift z y)).1 hmem
      exact ⟨w, by rw [← Category.assoc, hw, lift_fst]⟩
    · rintro hall ⟨w, hw⟩
      obtain ⟨a, ha⟩ := hall ((w ≫ i) ≫ snd Z K ≫ κ) (hkc _ _ _ _ (hkc _ _ _ _ hκ))
      have hs : (w ≫ i) ≫ snd Z K = (w ≫ i) ≫ fst Z K ≫ lam a := by
        apply huniq
        have := ha
        rw [← hw] at this
        simpa only [Category.assoc, hlam] using this.symm
      have h1 := ((hU (lam a)).2 _ _).1 hs
      have h2 : Set.range (w ≫ i).left ⊆ C := (hV _ _).2 ⟨w, rfl⟩
      haveI : Unique (Over.mk x).left := inferInstanceAs (Unique (PrimeSpectrum k))
      have h3 := h2 ⟨default, rfl⟩
      exact Set.mem_iInter₂.1 h3 (lam a) ⟨a, rfl⟩ (h1 ⟨default, rfl⟩)
  refine ⟨⟨(I : Set Z.left)ᶜ, hIc.isOpen_compl⟩, I.isOpen.isClosed_compl, fun T' h => ?_⟩
  constructor
  · intro H
    apply LevCover.range_subset_of_geom h
    intro k _ _ x y
    have e : (y ≫ h).left = ((Over.homMk y.left rfl : Over.mk (y.left ≫ T'.hom) ⟶ T') ≫ h).left := rfl
    rw [e]
    change _ ⊆ (I : Set Z.left)ᶜ
    rw [hA]
    intro g hg
    obtain ⟨a, ha⟩ := H k y.left g hg
    exact ⟨a, by rw [Category.assoc]; exact ha⟩
  · intro H k _ _ xp g hg
    have hsub : Set.range ((Over.homMk xp rfl : Over.mk (xp ≫ T'.hom) ⟶ T') ≫ h).left ⊆ (I : Set Z.left)ᶜ := by
      rintro _ ⟨t, rfl⟩
      exact H ⟨xp t, by simp⟩
    obtain ⟨a, ha⟩ := (hA k (xp ≫ T'.hom) _).1 hsub g hg
    exact ⟨a, by rw [← Category.assoc]; exact ha⟩

end GlobalTheory.UPel.HT.EtLev
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.ExpCoord

theorem val_spMap_comp {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {X : Scheme.{0}} (y : Sp S ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ y) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom (((spMap φ ≫ y).appLE U ⊤ h').hom f) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((y.appLE U ⊤ h).hom f)) := by
  have e : (spMap φ ≫ y).appLE U ⊤ h' = y.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) y U ⊤ ⊤ h le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((y.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  rw [e]
  exact e2

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h1 : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dite_eq_left h, dite_eq_left h1]
    unfold valAt
    rw [← Scheme.Hom.appLE_comp_appLE x φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h1]
    rfl
  · have h1 : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dite_eq_right h, dite_eq_right h1]

theorem deriv_scale {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) {v : Sp (DualNumber ℂ) ⟶ X}
    {w : Fin g → ℂ} (h : IsDerivAt0 e w v) (s : ℂ) : IsDerivAt0 e (s • w) (spMap (epsScaleR s) ≫ v) := by
  have hsub : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := GlobalTheory.UnifDifferential.subsingleton_primeSpectrum ℂ ℂ
  refine ⟨?_, fun U h' f => ?_⟩
  · have hc : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsScaleR s) = (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := by
      refine RingHom.ext fun x => ?_
      show (TrivSqZeroExt.map _ x).fst = x.fst
      exact TrivSqZeroExt.fst_map _ _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    exact h.1
  · have hv : ⊤ ≤ v ⁻¹ᵁ U := by
      intro x _
      have := h' (Set.mem_univ x)
      have hx : (spMap (epsScaleR s)) x = x := Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
      change v ((spMap (epsScaleR s)) x) ∈ U at this
      rwa [hx] at this
    rw [val_spMap_comp (epsScaleR s) v U hv h' f, map_smul, ← h.2 U hv f]
    simp [epsScaleR]

theorem deriv_comp {g : ℕ} {X Y : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
    (φ : X ⟶ Y) (Rho : Matrix (Fin g) (Fin g) ℂ) (hol : IsHolTo Set.univ e') (hc : ∀ z, e' (Rho *ᵥ z) = e z ≫ φ)
    {v : Sp (DualNumber ℂ) ⟶ X} {w : Fin g → ℂ} (h : IsDerivAt0 e w v) : IsDerivAt0 e' (Rho *ᵥ w) (v ≫ φ) := by
  have h0 : e' 0 = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ φ := by
    rw [← Category.assoc, h.1, ← hc, Matrix.mulVec_zero]
  refine ⟨h0.symm, fun U hU f => ?_⟩
  have h1 : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := hU
  rw [← Scheme.Hom.appLE_comp_appLE v φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h1]
  refine (h.2 (φ ⁻¹ᵁ U) h1 ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f)).trans ?_
  set G : (Fin g → ℂ) → ℂ := fun z => valAt' (e' z) U f with hG
  have hfun : (fun z => valAt' (e z) (φ ⁻¹ᵁ U) ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f)) = fun z => G (Rho *ᵥ z) := by
    funext z
    rw [hG]
    dsimp only
    rw [hc, valAt'_comp]
  rw [hfun]
  have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e' b ⁻¹ᵁ U} := by
    refine ⟨Set.mem_univ _, fun x _ => ?_⟩
    rw [h0]
    exact hU (Set.mem_univ _)
  have hd : DifferentiableAt ℂ G 0 :=
    ((hol U f).2 0 hmem).differentiableAt ((hol U f).1.mem_nhds hmem)
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin Rho)
  have hL0 : L 0 = 0 := map_zero L
  have hG' : HasFDerivAt G (fderiv ℂ G 0) (L 0) := by rw [hL0]; exact hd.hasFDerivAt
  have := hG'.comp (0 : Fin g → ℂ) L.hasFDerivAt
  show (fderiv ℂ (G ∘ ⇑L) 0) w = _
  rw [this.fderiv]
  rfl

def toSp {A : Over (Sp ℂ)} (v : epsPt (𝟙 (Sp ℂ)) ⟶ A) : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ A :=
  Over.homMk v.left (by simpa using Over.w v)

theorem toSp_eq {A : Over (Sp ℂ)} (v : epsPt (𝟙 (Sp ℂ)) ⟶ A) :
    toSp v = (Over.homMk (𝟙 _) (by simp) : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ epsPt (𝟙 (Sp ℂ))) ≫ v := by
  apply Over.OverMorphism.ext
  simp [toSp]

theorem toSp_mul {A : Over (Sp ℂ)} [GrpObj A] (v v' : epsPt (𝟙 (Sp ℂ)) ⟶ A) :
    toSp (v * v') = toSp v * toSp v' := by
  rw [toSp_eq, toSp_eq, toSp_eq, MonObj.comp_mul]

theorem one_left {A : Over (Sp ℂ)} [GrpObj A] : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A).left = η[A].left := by
  have h1 : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A) = toUnit _ ≫ η[A] := rfl
  have h2 : (toUnit (Over.mk (𝟙 (Sp ℂ))) : Over.mk (𝟙 (Sp ℂ)) ⟶ 𝟙_ (Over (Sp ℂ))) = 𝟙 (Over.mk (𝟙 (Sp ℂ))) := toUnit_unique _ _
  rw [h1, h2, Category.id_comp]

theorem pullFn_congr {A : Over (Sp ℂ)} {y y' : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ A} (e : y = y') (U : A.left.Opens)
    (h : ⊤ ≤ y.left ⁻¹ᵁ U) (h' : ⊤ ≤ y'.left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    GlobalTheory.UnifDifferential.pullFn y U h f = GlobalTheory.UnifDifferential.pullFn y' U h' f := by
  subst e; rfl

theorem deriv_mul {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (he : e 0 = 1) {v v' : epsPt (𝟙 (Sp ℂ)) ⟶ A} {w w' : Fin g → ℂ}
    (h : IsDerivAt0 (fun z => (e z).left) w v.left) (h' : IsDerivAt0 (fun z => (e z).left) w' v'.left) :
    IsDerivAt0 (fun z => (e z).left) (w + w') (v * v').left := by
  have ht : ∀ {x : epsPt (𝟙 (Sp ℂ)) ⟶ A},
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ x.left = (e 0).left → Chart.IsTan (toSp x) := by
    intro x hx
    rw [Chart.isTan_iff]
    show spMap _ ≫ x.left = η[A].left
    rw [hx, he, one_left]
  have hv := ht h.1
  have hv' := ht h'.1
  have hm : Chart.IsTan (toSp (v * v')) := by rw [toSp_mul]; exact Chart.isTan_mul hv hv'
  refine ⟨?_, fun U hU f => ?_⟩
  · have := (Chart.isTan_iff _).1 hm
    show spMap _ ≫ (v * v').left = (e 0).left
    rw [he, one_left]
    exact this
  · have hU' : ⊤ ≤ (toSp v * toSp v').left ⁻¹ᵁ U := by rw [← toSp_mul]; exact hU
    obtain ⟨h₁, h₂, hs⟩ := GlobalTheory.UnifDifferential.snd_pullFn_mul hv hv' U hU'
    show (GlobalTheory.UnifDifferential.pullFn (toSp (v * v')) U hU f).snd = _
    rw [pullFn_congr (toSp_mul v v') U hU hU' f, hs, map_add (f := _)]
    exact congrArg₂ (· + ·) (h.2 U h₁ f) (h'.2 U h₂ f)

theorem expCoord : ∀ (g n : ℕ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (x : Sp ℂ ⟶ Sp ℂ) (T : (Fin n → ℂ) → (epsPtR x ⟶ A)), x = 𝟙 _ → IsExp (𝟙 (Sp ℂ)) e → Function.Injective T → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : ℂ) c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin n → ℂ), ∀ (u : A ⟶ A), IsMonHom u → ∀ (Mu : Matrix (Fin n) (Fin n) ℂ) (Rho : Matrix (Fin g) (Fin g) ℂ), (∀ c, T c ≫ u = T (Mu *ᵥ c)) → (∀ z, e (Rho *ᵥ z) = e z ≫ u) → ∀ w, L (Rho *ᵥ w) = Mu *ᵥ L w := by
  intro g n A _ _ e x T hx hE hT hR hM hS
  subst hx
  obtain ⟨hadd, -, hhol, hd, hu⟩ := hE
  have he0 : e 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  choose Φ hΦ hΦu using hd
  have tanΦ : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (Φ w).left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A).left := by
    intro w
    rw [(hΦ w).1]
    show (e 0).left = _
    rw [he0]
  choose Ψ hΨ using fun w => (hR (Φ w)).1 (tanΦ w)
  have key : ∀ w c, IsDerivAt0 (fun z => (e z).left) w (T c).left → Ψ w = c := by
    intro w c h
    apply hT
    rw [hΨ w]
    exact (hΦu w (T c) h).symm
  have inj : Function.Injective Ψ := by
    intro w w' h
    have e1 : Φ w = Φ w' := by rw [← hΨ w, ← hΨ w', h]
    have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (Φ w).left = (e 0).left := (hΦ w).1
    obtain ⟨w'', -, hw''⟩ := hu (Φ w) ht
    have a1 := hw'' w (hΦ w)
    have a2 := hw'' w' (by rw [e1]; exact hΦ w')
    rw [a1, a2]
  have surj : Function.Surjective Ψ := by
    intro c
    have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T c).left = (e 0).left := by
      rw [he0]; exact (hR (T c)).2 ⟨c, rfl⟩
    obtain ⟨w, hw, -⟩ := hu (T c) ht
    exact ⟨w, key w c hw⟩
  let Lin : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := Ψ
      map_add' := fun w w' => key (w + w') (Ψ w + Ψ w') (by
        rw [hM, hΨ, hΨ]
        exact deriv_mul e he0 (hΦ w) (hΦ w'))
      map_smul' := fun s w => key (s • w) (s • Ψ w) (by
        rw [hS, hΨ]
        exact deriv_scale _ (hΦ w) s) }
  refine ⟨LinearEquiv.ofBijective Lin ⟨inj, surj⟩, ?_⟩
  intro u _ Mu Rho hTu hRho w
  show Ψ (Rho *ᵥ w) = Mu *ᵥ Ψ w
  apply key
  rw [← hTu, Over.comp_left, hΨ]
  exact deriv_comp _ _ u.left Rho hhol (fun z => by rw [hRho, Over.comp_left]) (hΦ w)

end GlobalTheory.ExpCoord

end
end

section

open Polynomial ValuativeRel

namespace GlobalTheory.IwahoriRegular

theorem regular_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ),
  ValuativeRel.valuation k (ϖ : k) = ValuativeRel.uniformizer k →
  ∀ ν : Fin N → ℤ, StrictAnti ν → ∀ x ∈ GlobalTheory.SmGL.iwahori k (Fin N), ∀ y ∈ GlobalTheory.SmGL.iwahori k (Fin N),
    let g := x * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * y
    (g : Matrix (Fin N) (Fin N) k).charpoly.Separable ∧ (g : Matrix (Fin N) (Fin N) k).charpoly.Splits := by
  intro k _ _ _ _ N ϖ hϖ ν hν x hx y hy
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  let w : 𝒪[k] := ⟨ϖ, hlt.le⟩
  have hw : Irreducible w := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext z
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
      Ideal.mem_span_singleton, (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
    rfl
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have low : ∀ h : GL (Fin N) 𝒪[k], h ∈ (GlobalTheory.SmGL.borel 𝓀[k] (Fin N)).comap
      (Matrix.GeneralLinearGroup.map (n := Fin N) (IsLocalRing.residue 𝒪[k])) →
      ∀ i j, j < i → (h : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro h hh i j hij
    have := (GlobalTheory.SmGL.mem_borel _).1 hh i j hij
    exact (IsLocalRing.residue_eq_zero_iff _).1 this
  obtain ⟨r, hr, hchar⟩ := GlobalTheory.IwahoriRoots.iwahori_roots 𝒪[k] k w hw N ν hν x' y' (low x' hx') (low y' hy')
  have hinj : Function.Injective r := fun i j h => hν.injective (by rw [← (hr i).2, ← (hr j).2, h])
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x' * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν *
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (x' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) *
        Matrix.diagonal (fun i => algebraMap 𝒪[k] k w ^ ν i) *
        (y' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) := by
    rw [Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt]
    rfl
  show Separable (Matrix.charpoly _) ∧ Splits (Matrix.charpoly _)
  rw [e, hchar]
  exact ⟨separable_prod_X_sub_C_iff.2 hinj, Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _⟩

end GlobalTheory.IwahoriRegular
end
