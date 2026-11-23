module

public import Development.EtaleCohomology.EtaleSheaves.Bundle039
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.EtaleCohomology.EtaleSheaves.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf

namespace LateralTheory.E.SurjStepPf

set_option linter.unusedSimpArgs false

variable {X S : Scheme.{0}}

theorem pc {R : Type} [CommRing R] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (F : Shv R) (n : ℤ) (x : H R (sch.obj C) F n) :
    pull R (sch.map (f ≫ g)) F n x = pull R (sch.map f) F n (pull R (sch.map g) F n x) := by
  rw [Functor.map_comp, pull_comp]

@[reassoc] theorem resO_fst (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : resO p h ≫ pullback.fst p U.ι = pullback.fst p V.ι :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc] theorem resO_snd (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO p h ≫ pullback.snd p U.ι = pullback.snd p V.ι ≫ S.homOfLE h :=
  pullback.lift_snd _ _ _

@[reassoc] theorem fO_fst {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.fst p U.ι = pullback.fst (f ≫ p) U.ι ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc] theorem fO_snd {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.snd p U.ι = pullback.snd (f ≫ p) U.ι :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem resO_comp (p : X ⟶ S) {U V W : S.Opens} (h1 : U ≤ V) (h2 : V ≤ W) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]

theorem resO_refl (p : X ⟶ S) (U : S.Opens) : resO p (le_refl U) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]

instance (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : IsOpenImmersion (resO p h) := by
  have : IsOpenImmersion (resO p h ≫ pullback.fst p U.ι) := by rw [resO_fst]; infer_instance
  exact IsOpenImmersion.of_comp (resO p h) (pullback.fst p U.ι)

theorem range_fst (p : X ⟶ S) (V : S.Opens) : Set.range (pullback.fst p V.ι) = p ⁻¹' (V : Set S) := by
  rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

theorem range_resO (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    Set.range (resO p h) = pullback.fst p U.ι ⁻¹' (p ⁻¹' (V : Set S)) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, resO_fst, ← range_fst]
    exact ⟨w, rfl⟩
  · intro hz
    rw [Set.mem_preimage, ← range_fst] at hz
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, (pullback.fst p U.ι).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, resO_fst, hw]

theorem cover (p : X ⟶ S) (V W : S.Opens) :
    Set.range (resO p (le_sup_left : V ≤ V ⊔ W)) ∪ Set.range (resO p (le_sup_right : W ≤ V ⊔ W)) = Set.univ := by
  rw [range_resO, range_resO, ← Set.preimage_union, ← Set.preimage_union, Set.eq_univ_iff_forall]
  intro z
  have : pullback.fst p (V ⊔ W).ι z ∈ Set.range (pullback.fst p (V ⊔ W).ι) := ⟨z, rfl⟩
  rw [range_fst] at this
  simpa [Set.mem_union] using this

def phi (p : X ⟶ S) (V W : S.Opens) :
    pullback (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) ⟶ overO p (V ⊓ W) :=
  IsOpenImmersion.lift (resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))
    (pullback.fst _ _ ≫ resO p le_sup_left) (by
      rintro _ ⟨z, rfl⟩
      rw [range_resO]
      have h1 : (pullback.fst _ _ ≫ resO p (le_sup_left : V ≤ V ⊔ W)) z ∈ Set.range (resO p (le_sup_left : V ≤ V ⊔ W)) :=
        ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
      have h2 : (pullback.fst _ _ ≫ resO p (le_sup_left : V ≤ V ⊔ W)) z ∈ Set.range (resO p (le_sup_right : W ≤ V ⊔ W)) := by
        rw [pullback.condition]; exact ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
      rw [range_resO] at h1 h2
      exact ⟨h1, h2⟩)

@[reassoc] theorem phi_fac (p : X ⟶ S) (V W : S.Opens) :
    phi p V W ≫ resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W) = pullback.fst _ _ ≫ resO p le_sup_left :=
  IsOpenImmersion.lift_fac _ _ _

theorem phi_fst (p : X ⟶ S) (V W : S.Opens) : phi p V W ≫ resO p inf_le_left = pullback.fst _ _ := by
  rw [← cancel_mono (resO p (le_sup_left : V ≤ V ⊔ W)), Category.assoc, resO_comp, phi_fac]

theorem phi_snd (p : X ⟶ S) (V W : S.Opens) : phi p V W ≫ resO p inf_le_right = pullback.snd _ _ := by
  rw [← cancel_mono (resO p (le_sup_right : W ≤ V ⊔ W)), Category.assoc, resO_comp, ← pullback.condition]
  exact phi_fac p V W

def psi (p : X ⟶ S) (V W : S.Opens) :
    overO p (V ⊓ W) ⟶ pullback (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) :=
  pullback.lift (resO p inf_le_left) (resO p inf_le_right) (by rw [resO_comp, resO_comp])

theorem phi_psi (p : X ⟶ S) (V W : S.Opens) : phi p V W ≫ psi p V W = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, psi, pullback.lift_fst, phi_fst, Category.id_comp]
  · rw [Category.assoc, psi, pullback.lift_snd, phi_snd, Category.id_comp]

theorem fO_res {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]

theorem phi_nat {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (V W : S.Opens) :
    pullback.map _ _ _ _ (fO f p V) (fO f p W) (fO f p (V ⊔ W)) (fO_res f p le_sup_left) (fO_res f p le_sup_right) ≫ phi p V W =
      phi (f ≫ p) V W ≫ fO f p (V ⊓ W) := by
  rw [← cancel_mono (resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W)), Category.assoc, Category.assoc, phi_fac,
    ← fO_res, phi_fac_assoc, fO_res, ← Category.assoc, ← Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

theorem empty_over (p : X ⟶ S) (U : S.Opens) (h : (U : Set S) = ∅) : IsEmpty (overO p U) :=
  ⟨fun z => by
    have : pullback.fst p U.ι z ∈ Set.range (pullback.fst p U.ι) := ⟨z, rfl⟩
    rw [range_fst, h] at this
    exact this⟩

theorem glue (hM : MV) (hH : Hyp) (q : ℕ) {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (i m : ℤ) (V W : S.Opens)
    (hinj : Function.Injective (pull _ (sch.map (fO f p (V ⊓ W))) (tw q i) (m + 1)))
    (hsurj : Function.Surjective (pull _ (sch.map (fO f p (V ⊓ W))) (tw q i) m))
    (y : H (ZMod q) (sch.obj (overO (f ≫ p) (V ⊔ W))) (tw q i) (m + 1))
    (xV : H (ZMod q) (sch.obj (overO p V)) (tw q i) (m + 1)) (xW : H (ZMod q) (sch.obj (overO p W)) (tw q i) (m + 1))
    (hV : pull _ (sch.map (fO f p V)) _ _ xV = pull _ (sch.map (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W))) _ _ y)
    (hW : pull _ (sch.map (fO f p W)) _ _ xW = pull _ (sch.map (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))) _ _ y) :
    ∃ x, pull _ (sch.map (fO f p (V ⊔ W))) _ _ x = y := by
  obtain ⟨δ, hδ, hnat⟩ := hM hH (ZMod q) (tw q i)
  have hX := hδ (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) (cover p V W)
  have hY := hδ (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W)) (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W)) (cover (f ≫ p) V W)
  have e1 : pull _ (sch.map (fO f p (V ⊓ W))) _ _ (pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ xV) =
      pull _ (sch.map (resO (f ≫ p) (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))) _ _ y := by
    rw [← pc, ← fO_res, pc, hV, ← pc, resO_comp]
  have e2 : pull _ (sch.map (fO f p (V ⊓ W))) _ _ (pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ xW) =
      pull _ (sch.map (resO (f ≫ p) (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))) _ _ y := by
    rw [← pc, ← fO_res, pc, hW, ← pc, resO_comp]
  have hI := hinj (e1.trans e2.symm)
  obtain ⟨x0, hx0V, hx0W⟩ := (hX (m + 1)).1 xV xW (by rw [← phi_fst p V W, ← phi_snd p V W, pc, pc, hI])
  have hzV : pull _ (sch.map (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W))) _ _ (pull _ (sch.map (fO f p (V ⊔ W))) _ _ x0 - y) = 0 := by
    rw [map_sub, ← pc, fO_res, pc, hx0V, hV, sub_self]
  have hzW : pull _ (sch.map (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))) _ _ (pull _ (sch.map (fO f p (V ⊔ W))) _ _ x0 - y) = 0 := by
    rw [map_sub, ← pc, fO_res, pc, hx0W, hW, sub_self]
  obtain ⟨w', hw'⟩ := ((hY m).2.2 _).1 ⟨hzV, hzW⟩
  obtain ⟨u, hu⟩ := hsurj (pull _ (sch.map (psi (f ≫ p) V W)) _ _ w')
  have hn := hnat (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W)) (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))
    (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) (cover (f ≫ p) V W) (cover p V W)
    (fO f p V) (fO f p W) (fO f p (V ⊔ W)) (fO_res f p le_sup_left) (fO_res f p le_sup_right) m
    (pull _ (sch.map (phi p V W)) _ _ u)
  rw [← pc, phi_nat, pc, hu, ← pc, phi_psi] at hn
  rw [CategoryTheory.Functor.map_id, pull_id] at hn
  rw [hw'] at hn
  refine ⟨x0 - δ _ _ m (pull _ (sch.map (phi p V W)) _ _ u), ?_⟩
  rw [map_sub, ← hn, sub_sub_cancel]

theorem SurjStep_of : SurjStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb hinj U hU y
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hb' : ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i m f p U := by simpa using hb
  let Good : S.Opens → Prop := fun V => ∃ h : V ≤ U, ∃ x : H (ZMod q) (sch.obj (overO p V)) (tw q i) (m + 1),
    pull _ (sch.map (fO f p V)) _ _ x = pull _ (sch.map (resO (f ≫ p) h)) _ _ y
  have mono : ∀ V V' : S.Opens, V' ≤ V → Good V → Good V' := by
    rintro V V' h ⟨hV, x, hx⟩
    refine ⟨h.trans hV, pull _ (sch.map (resO p h)) _ _ x, ?_⟩
    rw [← pc, ← fO_res, pc, hx, ← pc, resO_comp]
  have union : ∀ V W : S.Opens, IsCompact (V : Set S) → IsCompact (W : Set S) → Good V → Good W → Good (V ⊔ W) := by
    rintro V W hVc hWc ⟨hV, xV, hxV⟩ ⟨hW, xW, hxW⟩
    have hIc : IsCompact ((V ⊓ W : S.Opens) : Set S) :=
      QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hVc W.isOpen hWc
    obtain ⟨x, hx⟩ := glue hM hH q f p i m V W (hinj _ hIc) (hb' _ hIc).2
      (pull _ (sch.map (resO (f ≫ p) (sup_le hV hW))) _ _ y) xV xW
      (by rw [hxV]; first | rfl | rw [← pc, resO_comp]) (by rw [hxW]; first | rfl | rw [← pc, resO_comp])
    exact ⟨sup_le hV hW, x, by rw [hx]⟩
  have P : (U : Set S) = ∅ ∨ ∃ V : S.Opens, IsCompact (V : Set S) ∧ (U : Set S) ⊆ V ∧ Good V := by
    refine hU.induction_on (p := fun T : Set S => T = ∅ ∨ ∃ V : S.Opens, IsCompact (V : Set S) ∧ T ⊆ V ∧ Good V)
      (Or.inl rfl) ?_ ?_ ?_
    · rintro s t hst (h | ⟨V, hVc, htV, hV⟩)
      · exact Or.inl (Set.subset_eq_empty hst h)
      · exact Or.inr ⟨V, hVc, hst.trans htV, hV⟩
    · rintro s t (h | h1) (h' | h2)
      · left; rw [h, h', Set.empty_union]
      · right; rw [h, Set.empty_union]; exact h2
      · right; rw [h', Set.union_empty]; exact h1
      · obtain ⟨V, hVc, hsV, hV⟩ := h1
        obtain ⟨W, hWc, htW, hW⟩ := h2
        exact Or.inr ⟨V ⊔ W, by simpa using hVc.union hWc, Set.union_subset_union hsV htW, union V W hVc hWc hV hW⟩
    · intro s hs
      obtain ⟨V, hVU, hsV, x, hx⟩ := (hg s).2 U hs y
      obtain ⟨V', hV'aff, hsV', hV'V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens S)) hsV
      exact ⟨V', mem_nhdsWithin_of_mem_nhds (V'.isOpen.mem_nhds hsV'),
        Or.inr ⟨V', hV'aff.isCompact, subset_rfl, mono V V' hV'V ⟨hVU, x, hx⟩⟩⟩
  rcases P with h | ⟨V, -, hUV, hVU, x, hx⟩
  · have := empty_over p U h
    exact (pull_bij_of_iso (sch.map (fO f p U)) (tw q i) _).2 y
  · obtain rfl : V = U := le_antisymm hVU hUV
    exact ⟨x, by rw [hx, resO_refl, CategoryTheory.Functor.map_id, pull_id]⟩

end LateralTheory.E.SurjStepPf
end
end

section

namespace LateralTheory.E.SysFMPfAlg

open LateralTheory.E.BuildCut

theorem prime_of_filter {W : Type} [CommRing W] (hW : ProdACF W) (F : Set W) (hF : ∀ e ∈ F, IsIdempotentElem e)
    (h0 : (0 : W) ∉ F) (hu : ∀ e, IsIdempotentElem e → e ∈ F ∨ 1 - e ∈ F) (hm : ∀ e ∈ F, ∀ f ∈ F, e * f ∈ F) :
    ∃ q : PrimeSpectrum W, ∀ e, IsIdempotentElem e → (e ∉ q.asIdeal ↔ e ∈ F) := by
  have h1 : (1 : W) ∈ F := by
    rcases hu 0 IsIdempotentElem.zero with h | h
    · exact absurd h h0
    · simpa using h
  let I : Ideal W :=
    { carrier := {a | ∃ f ∈ F, a * f = 0}
      add_mem' := by
        rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
        exact ⟨f * g, hm f hf g hg, by linear_combination g * ha + f * hb⟩
      zero_mem' := ⟨1, h1, by simp⟩
      smul_mem' := by
        rintro c a ⟨f, hf, ha⟩
        exact ⟨f, hf, by simp only [smul_eq_mul]; linear_combination c * ha⟩ }
  have key : ∀ e, IsIdempotentElem e → (e ∈ I ↔ e ∉ F) := by
    intro e he
    constructor
    · rintro ⟨f, hf, hef⟩ heF
      exact h0 (hef ▸ hm e heF f hf)
    · intro heF
      rcases hu e he with h | h
      · exact absurd h heF
      · exact ⟨1 - e, h, by rw [mul_sub, mul_one, he.eq, sub_self]⟩
  have hI : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      rintro ⟨f, hf, h⟩
      rw [one_mul] at h
      exact h0 (h ▸ hf)
    · intro a b hab
      obtain ⟨e, u, he, hu', rfl⟩ := hW.2 a
      obtain ⟨e', u', he', hu'', rfl⟩ := hW.2 b
      by_contra hn
      push Not at hn
      have ha : e ∈ F := by
        by_contra h
        exact hn.1 ⟨1 - e, (hu e he).resolve_left h, by
          rw [mul_assoc, mul_comm u, ← mul_assoc, mul_sub, mul_one, he.eq, sub_self, zero_mul]⟩
      have hb : e' ∈ F := by
        by_contra h
        exact hn.2 ⟨1 - e', (hu e' he').resolve_left h, by
          rw [mul_assoc, mul_comm u', ← mul_assoc, mul_sub, mul_one, he'.eq, sub_self, zero_mul]⟩
      obtain ⟨f, hf, h⟩ := hab
      have hz : e * e' * f = 0 := by
        obtain ⟨v, hv⟩ := hu'.exists_left_inv
        obtain ⟨v', hv'⟩ := hu''.exists_left_inv
        linear_combination (v * v') * h - (e * e' * f) * hv - (e * e' * f * v * u) * hv'
      exact h0 (hz ▸ hm _ (hm e ha e' hb) f hf)
  refine ⟨⟨I, hI⟩, fun e he => ?_⟩
  rw [show (⟨I, hI⟩ : PrimeSpectrum W).asIdeal = I from rfl, key e he, not_not]


open AlgebraicGeometry in
theorem isClosed_basicOpen_idem {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) :
    IsClosed (X.basicOpen s : Set X) := by
  have : (X.basicOpen s : Set X)ᶜ = (X.basicOpen (1 - s) : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Scheme.mem_basicOpen_top, map_sub, map_one]
    have he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s) := hs.map _
    constructor
    · intro h
      exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h
    · intro h h'
      have hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0 := by
        rw [mul_sub, mul_one, he.eq, sub_self]
      exact not_isUnit_zero (hz ▸ h'.mul h)
  rw [← isOpen_compl_iff, this]
  exact (X.basicOpen (1 - s)).isOpen

open AlgebraicGeometry in
theorem isClosedImmersion_basicOpen_idem {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) :
    IsClosedImmersion (X.basicOpen s).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact isClosed_basicOpen_idem hs)

end LateralTheory.E.SysFMPfAlg
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut

namespace LateralTheory.E.PtsPf

attribute [local instance] PrimeSpectrum.isPrime

lemma prodACF_field (K : Type) [Field K] [IsAlgClosed K] : ProdACF K := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p (by
      rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hd.ne')
    exact ⟨x, hx⟩
  · by_cases ha : a = 0
    · exact ⟨0, 1, IsIdempotentElem.zero, isUnit_one, by simp [ha]⟩
    · exact ⟨1, a, IsIdempotentElem.one, isUnit_iff_ne_zero.mpr ha, by simp⟩

lemma prodACF_pi {ι : Type} (W : ι → Type) [∀ i, CommRing (W i)] (h : ∀ i, ProdACF (W i)) :
    ProdACF (∀ i, W i) := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · have hr : ∀ i, ∃ x, (p.map (Pi.evalRingHom W i)).eval x = 0 := by
      intro i
      rcases subsingleton_or_nontrivial (W i) with hs | hs
      · exact ⟨0, Subsingleton.elim _ _⟩
      · exact (h i).1 _ (hp.map _) (by rw [hp.natDegree_map]; exact hd)
    choose x hx using hr
    refine ⟨x, funext fun i => ?_⟩
    have := Polynomial.hom_eval₂ p (RingHom.id _) (Pi.evalRingHom W i) x
    simp only [RingHom.comp_id] at this
    simp only [Polynomial.eval_map] at hx
    change (Pi.evalRingHom W i) (Polynomial.eval₂ (RingHom.id _) x p) = 0
    rw [this]
    exact hx i
  · have hr := fun i => (h i).2 (a i)
    choose e u he hu hau using hr
    refine ⟨e, u, ?_, Pi.isUnit_iff.mpr hu, funext hau⟩
    exact funext fun i => he i

abbrev WA (R : CommRingCat.{0}) : Type :=
  ∀ p : PrimeSpectrum R, AlgebraicClosure p.asIdeal.ResidueField

def phiA (R : CommRingCat.{0}) : R →+* WA R :=
  RingHom.pi fun p => (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField)

lemma surj_phiA (R : CommRingCat.{0}) : Surjective (Spec.map (CommRingCat.ofHom (phiA R))) := by
  refine ⟨fun p' => ?_⟩
  obtain ⟨p, rfl⟩ : ∃ p : PrimeSpectrum R, (p : Spec R) = p' := ⟨p', rfl⟩
  let ev : WA R →+* AlgebraicClosure p.asIdeal.ResidueField := Pi.evalRingHom _ p
  have hq : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  refine ⟨⟨RingHom.ker ev, hq⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (phiA R) (RingHom.ker ev) = p.asIdeal
  rw [RingHom.comap_ker]
  have : ev.comp (phiA R) = (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField) := rfl
  rw [this, RingHom.ker_comp_of_injective _ (RingHom.injective (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField))), Ideal.ker_algebraMap_residueField]

theorem Pts_of : Pts := by
  intro P _ _
  let 𝒰 := P.affineCover.finiteSubcover
  let I := 𝒰.I₀
  have hA : ∀ i : I, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (P.affineCover.X _); infer_instance
  let R : I → CommRingCat.{0} := fun i => Γ(𝒰.X i, ⊤)
  let f : ∀ i, Spec (R i) ⟶ P := fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  let S : I → CommRingCat.{0} := fun i => CommRingCat.of (WA (R i))
  let g : ∀ i, Spec (S i) ⟶ P := fun i => Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ f i
  refine ⟨∀ i, S i, inferInstance, inv (sigmaSpec S) ≫ Sigma.desc g, ?_, ?_⟩
  · exact prodACF_pi _ fun i => prodACF_pi _ fun p => prodACF_field _
  · have : Surjective (Sigma.desc g) := by
      apply Surjective.sigmaDesc_of_union_range_eq_univ
      have hr : ∀ i, Set.range (g i) = Set.range (𝒰.f i) := fun i => by
        have := surj_phiA (R i)
        rw [range_eq_range_of_surjective (g i) (𝒰.f i) (Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ (𝒰.X i).isoSpec.inv)
          (by simp [g, f])]
      simp_rw [hr]
      exact 𝒰.iUnion_range
    infer_instance

end LateralTheory.E.PtsPf
end
end

section

namespace LateralTheory.E.IdemPartPf

open Finset

theorem prod_erase_mul_prod_erase {A : Type} [CommRing A] {n : ℕ} (y : Fin n → A)
    (h0 : ∏ l, y l = 0) {l m : Fin n} (hlm : l ≠ m) :
    (∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k) = 0 := by
  have hl : l ∈ (univ : Finset (Fin n)).erase m := mem_erase.2 ⟨hlm, mem_univ l⟩
  rw [← mul_prod_erase _ y hl, ← mul_assoc, mul_comm (∏ k ∈ univ.erase l, y k) (y l),
    mul_prod_erase _ y (mem_univ l), h0, zero_mul]

theorem IdemPart_of : LateralTheory.E.HensCut.IdemPart := by
  intro A _ n y h0 hu
  obtain ⟨u, hu⟩ := hu
  let e : Fin n → A := fun l => (↑u⁻¹ : A) * ∏ m ∈ univ.erase l, y m
  have horth : ∀ l m, l ≠ m → e l * e m = 0 := by
    intro l m hlm
    have := prod_erase_mul_prod_erase y h0 hlm
    calc e l * e m = (↑u⁻¹ : A) * ↑u⁻¹ * ((∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k)) := by
          simp only [e]; ring
      _ = 0 := by rw [this, mul_zero]
  have hsum : ∑ l, e l = 1 := by
    simp only [e]
    rw [← mul_sum, ← hu, Units.inv_mul]
  refine ⟨e, ?_, horth, hsum, ?_⟩
  · intro l
    unfold IsIdempotentElem
    calc e l * e l = e l * ∑ m, e m := by
          rw [mul_sum, sum_eq_single l]
          · intro m _ hml; exact horth l m (Ne.symm hml)
          · intro h; exact absurd (mem_univ l) h
      _ = e l := by rw [hsum, mul_one]
  · intro l
    simp only [e]
    rw [mul_assoc, mul_comm (∏ m ∈ univ.erase l, y m) (y l), mul_prod_erase _ y (mem_univ l), h0, mul_zero]

end LateralTheory.E.IdemPartPf
end

section

open Polynomial

namespace LateralTheory.E.MonicSplitsPf

theorem selfDualLattice_projection_mem_of_unit_length (R : Type) [CommRing R] [IsDomain R] (hA : GlobalTheory.EtC.AIC R) :
    ∀ n : ℕ, ∀ p : Polynomial R, p.Monic → p.natDegree = n →
      ∃ s : Multiset R, p = (s.map fun a => X - C a).prod := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    refine ⟨0, ?_⟩
    simpa using hp.natDegree_eq_zero.mp hn
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := hA p hp (by omega)
    have hroot : IsRoot p a := ha
    have hmul := (mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hmul]; exact hp)
    have hqd : q.natDegree = n := by
      rw [hq, natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C, hn]; omega
    obtain ⟨s, hs⟩ := ih q hqm hqd
    refine ⟨a ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

theorem MonicSplits_of : LateralTheory.E.HensCut.MonicSplits := by
  intro R _ _ hA p hp
  exact selfDualLattice_projection_mem_of_unit_length R hA p.natDegree p hp rfl

end LateralTheory.E.MonicSplitsPf
end
