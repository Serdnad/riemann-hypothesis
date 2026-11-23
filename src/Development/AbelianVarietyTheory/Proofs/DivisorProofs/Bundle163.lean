module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle039
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem basicOpen_res_eq {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (b : Γ(Y₁, upOpen i U)) :
    Y₀.basicOpen ((res i U).hom b) = i ⁻¹ᵁ Y₁.basicOpen b := by
  change Y₀.basicOpen (i.appLE (upOpen i U) U (preimage_upOpen i U).ge b) = _
  rw [Scheme.basicOpen_appLE]
  refine inf_eq_right.mpr ?_
  calc i ⁻¹ᵁ Y₁.basicOpen b ≤ i ⁻¹ᵁ upOpen i U := fun x hx => Y₁.basicOpen_le b hx
    _ = U := preimage_upOpen i U

theorem upOpen_basicOpen_res {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (b : Γ(Y₁, upOpen i U)) :
    upOpen i (Y₀.basicOpen ((res i U).hom b)) = Y₁.basicOpen b := by
  rw [basicOpen_res_eq, upOpen_preimage]

theorem basicOpen_fibπ_mem_good {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂] :
    ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U),
      Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a) ∈
        GlobalTheory.FerrandPush.good i₁ i₂ := by
  intro U hU a
  obtain ⟨h0, h1, h2⟩ := hU
  have e1 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₁ U).hom ((cone i₁ i₂ U).fst.hom a) := rfl
  have e2 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₂ U).hom ((cone i₁ i₂ U).snd.hom a) := by
    rw [e1]
    exact congrArg (fun f : (cone i₁ i₂ U).pt ⟶ Γ(Y₀, U) => f.hom a) (cone i₁ i₂ U).condition
  refine ⟨h0.basicOpen _, ?_, ?_⟩
  · rw [e1, upOpen_basicOpen_res]
    exact h1.basicOpen _
  · rw [e2, upOpen_basicOpen_res]
    exact h2.basicOpen _

end GlobalTheory.FerrandPush
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

def transferMap {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ⟶ pullback z g :=
  pullback.map z' g' z g eZ.hom (𝟙 T) eS.hom hsq.symm (by rw [Category.id_comp, hg])

instance {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    IsIso (transferMap z z' eS eZ hsq g' g hg) := by
  unfold transferMap; infer_instance

def transferIso {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ≅ pullback z g :=
  asIso (transferMap z z' eS eZ hsq g' g hg)

lemma transferIso_hom_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).hom ≫ pullback.snd z g = pullback.snd z' g' := by
  simp only [transferIso, asIso_hom, transferMap]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma transferIso_inv_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).inv ≫ pullback.snd z' g' = pullback.snd z g := by
  rw [Iso.inv_comp_eq, transferIso_hom_snd]

lemma transferIso_map {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T H : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g)
    (h' : H ⟶ S') (f : T ⟶ H) (hf' : f ≫ h' = g') (hf : f ≫ (h' ≫ eS.hom) = g) :
    pullback.map z' g' z' h' (𝟙 Z') f (𝟙 S') (by simp) (by rw [Category.comp_id, hf'])
        ≫ (transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl).hom =
      (transferIso z z' eS eZ hsq g' g hg).hom ≫
        pullback.map z g z (h' ≫ eS.hom) (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf]) := by
  simp only [transferIso, asIso_hom, transferMap, pullback.map]
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem isHilbRep_transfer : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z),
    eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  intro S Z S' Z' z z' eS eZ hsq r hrep
  obtain ⟨H, h', U, u', hP, hC, hF, hFl, hR, hU⟩ := hrep
  set ΦH := transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl with hΦH
  have eu : (u' ≫ ΦH.hom) ≫ pullback.snd z (h' ≫ eS.hom) = u' ≫ pullback.snd z' h' := by
    rw [Category.assoc, transferIso_hom_snd]
  refine ⟨H, h' ≫ eS.hom, U, u' ≫ ΦH.hom, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [eu]; exact hF
  · rw [eu]; exact hFl
  · rw [eu]; exact hR
  intro T g V v hv hvF hvFl hvR
  have hg : (g ≫ eS.inv) ≫ eS.hom = g := by simp
  set ΦT := transferIso z z' eS eZ hsq (g ≫ eS.inv) g hg with hΦT
  have ev : (v ≫ ΦT.inv) ≫ pullback.snd z' (g ≫ eS.inv) = v ≫ pullback.snd z g := by
    rw [Category.assoc, transferIso_inv_snd]
  have hv' : IsClosedImmersion (v ≫ ΦT.inv) := inferInstance
  obtain ⟨f, ⟨hf', w, hpb⟩, huniq⟩ := hU T (g ≫ eS.inv) V (v ≫ ΦT.inv) hv' (by rw [ev]; exact hvF)
    (by rw [ev]; exact hvFl) (by rw [ev]; exact hvR)
  have hf : f ≫ (h' ≫ eS.hom) = g := by rw [← Category.assoc, hf', hg]
  refine ⟨f, ⟨hf, w, ?_⟩, ?_⟩
  · refine hpb.of_iso (Iso.refl _) ΦT (Iso.refl _) ΦH ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f hf' hf
    · simp
  · rintro f₂ ⟨hf₂, w₂, hpb₂⟩
    have hf₂' : f₂ ≫ h' = g ≫ eS.inv := by rw [← hf₂]; simp
    apply huniq f₂ ⟨hf₂', w₂, ?_⟩
    refine hpb₂.of_iso (Iso.refl _) ΦT.symm (Iso.refl _) ΦH.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc,
        transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f₂ hf₂' hf₂, Iso.inv_hom_id_assoc]
    · simp [hΦH]

end GlobalTheory.HilbertSch
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem ker_comap_eq_ker_iff {X X' V V' : Scheme.{0}} (m : X' ⟶ X) (v : V ⟶ X) [IsClosedImmersion v]
    (v' : V' ⟶ X') [IsClosedImmersion v'] :
    v.ker.comap m = v'.ker ↔ ∃ w : V' ⟶ V, IsPullback v' w m v := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [comap_eq_ker_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ inv v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso (inv v.toImage)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso v.toImage) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]

variable {S Z : Scheme.{0}} (z : Z ⟶ S) (W : S.Opens)

lemma isPullback_restrict {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    IsPullback (pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι) (pullback.snd (z ∣_ W) b) z (b ≫ W.ι) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback (z ∣_ W) b) (isPullback_morphismRestrict z W).flip

def restrictIso {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) : pullback (z ∣_ W) b ≅ pullback z (b ≫ W.ι) :=
  (isPullback_restrict z W b).isoPullback

@[reassoc (attr := simp)]
lemma restrictIso_hom_fst {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.fst z (b ≫ W.ι) = pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι :=
  (isPullback_restrict z W b).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma restrictIso_hom_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.snd z (b ≫ W.ι) = pullback.snd (z ∣_ W) b :=
  (isPullback_restrict z W b).isoPullback_hom_snd

lemma restrictIso_inv_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).inv ≫ pullback.snd (z ∣_ W) b = pullback.snd z (b ≫ W.ι) := by
  rw [Iso.inv_comp_eq, restrictIso_hom_snd]

lemma restrictIso_natural {Y H : Scheme.{0}} (b : Y ⟶ W.toScheme) (h : H ⟶ W.toScheme) (c : Y ⟶ H)
    (hc : c ≫ h = b) (w : c ≫ h ≫ W.ι = b ≫ W.ι) :
    pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp) (by rw [Category.comp_id, hc]) ≫
      (restrictIso z W h).hom = (restrictIso z W b).hom ≫ bc z c (h ≫ W.ι) (b ≫ W.ι) w := by
  apply pullback.hom_ext
  · simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_fst_assoc, restrictIso_hom_fst]
  · simp only [bc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_snd_assoc, restrictIso_hom_snd]

theorem isHilbRep_restrict_local : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (W : S.Opens),
    GlobalTheory.HilbertSch.IsHilbRep (z ∣_ W) r → ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x := by
  intro S Z z r W hR
  obtain ⟨H, h, U, u, hprop, hcl, hfin, hflat, hrk, huniv⟩ := hR
  haveI := hcl
  have hv : IsFinFlatRk ((u ≫ (restrictIso z W h).hom) ≫ pullback.snd z (h ≫ W.ι)) r := by
    rw [Category.assoc, restrictIso_hom_snd]
    exact ⟨hfin, hflat, hrk⟩
  set y := mkPt (h ≫ W.ι) (u ≫ (restrictIso z W h).hom) hv with hy
  refine ⟨H, y, h, hprop, rfl, ?_⟩
  intro Y x b hx
  obtain ⟨g, J⟩ := x
  change g = b ≫ W.ι at hx
  subst hx
  set v' := J.1.subschemeι ≫ (restrictIso z W b).inv with hv'
  have e : v' ≫ pullback.snd (z ∣_ W) b = J.1.subschemeι ≫ pullback.snd z (b ≫ W.ι) := by
    rw [hv', Category.assoc, restrictIso_inv_snd]
  have key : ∀ c : Y ⟶ H, HPt.map c y = ⟨b ≫ W.ι, J⟩ ↔ ∃ hf : c ≫ h = b, ∃ w : J.1.subscheme ⟶ U,
      IsPullback v' w (pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp)
        (by rw [Category.comp_id, hf])) u := by
    intro c
    constructor
    · intro hc
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := congrArg Sigma.fst hc
      have hf : c ≫ h = b := by
        rw [← cancel_mono W.ι, Category.assoc]
        exact h1
      refine ⟨hf, ?_⟩
      rw [HPt.map_eq_mk_iff c y h1] at hc
      have hc' : (u ≫ (restrictIso z W h).hom).ker.comap (bc z c (h ≫ W.ι) (b ≫ W.ι) h1) =
          J.1.subschemeι.ker := hc.trans (Scheme.IdealSheafData.ker_subschemeι _).symm
      obtain ⟨w, hw⟩ := (ker_comap_eq_ker_iff _ _ _).1 hc'
      refine ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b).symm (Iso.refl _) (restrictIso z W h).symm
        ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · simp only [Iso.symm_hom]
        rw [Iso.comp_inv_eq, Category.assoc, restrictIso_natural z W b h c hf h1, Iso.inv_hom_id_assoc]
      · simp
    · rintro ⟨hf, w, hw⟩
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := by rw [← Category.assoc, hf]
      rw [HPt.map_eq_mk_iff c y h1]
      refine (?_ : _ = J.1.subschemeι.ker).trans (Scheme.IdealSheafData.ker_subschemeι _)
      refine (ker_comap_eq_ker_iff _ (u ≫ (restrictIso z W h).hom) _).2 ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b) (Iso.refl _) (restrictIso z W h) ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · exact restrictIso_natural z W b h c hf h1
      · simp
  have hJ := J.2
  rw [← e] at hJ
  obtain ⟨f, hfP, huniq⟩ := huniv Y b _ v' inferInstance hJ.1 hJ.2.1 hJ.2.2
  exact ⟨f, (key f).2 hfP, fun c hc => huniq c ((key c).1 hc)⟩

end GlobalTheory.HilbGlue
end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

namespace GlobalTheory

theorem exists_hom_spec_prod_self_preimage_eq_clopen :
    ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U →
      ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧
        ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by
  intro O _ T p U hU
  obtain ⟨ε, he, hεU⟩ := exists_idempotent_basicOpen_eq_of_isClopen T U hU
  let φ : O →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop).hom
  let ψ : O × O →+* Γ(T, ⊤) :=
    { toFun := fun x => φ x.1 * ε + φ x.2 * (1 - ε)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination -(φ x.1 * φ y.1 - φ x.1 * φ y.2 - φ x.2 * φ y.1 + φ x.2 * φ y.2) * he
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        ring }
  have hψ : ψ.comp (algebraMap O (O × O)) = φ := by
    ext a
    change φ a * ε + φ a * (1 - ε) = φ a
    ring
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · have : CommRingCat.ofHom φ = (Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop := rfl
    rw [Category.assoc, twoπ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, this, Spec.map_comp,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  · rw [Scheme.preimage_basicOpen_top, ← hεU]
    congr 2
    have h1 : (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).appTop (fst1 O) = ψ ((1, 0) : O × O) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop]
      have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
      have h2 := congrArg (fun f => f.hom (fst1 O)) this
      simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h2
      refine h2.trans ?_
      simp [fst1]
    rw [h1]
    change φ 1 * ε + φ 0 * (1 - ε) = ε
    simp

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlgConn

theorem hom_eq_toSpecΓ_comp {T : Scheme.{0}} {A : CommRingCat.{0}} (h : T ⟶ Spec A) :
    h = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ h.appTop) := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem hom_ext_of_twoπ_of_basicOpen : ∀ (O : Type) [CommRing O] (T : Scheme.{0})
    (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O →
    h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) →
    h = h' := by
  intro O _ T h h' hπ hb
  rw [hom_eq_toSpecΓ_comp h, hom_eq_toSpecΓ_comp h']
  congr 2

  have h1 : ∀ a : O, ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom (algebraMap O (O × O) a) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom (algebraMap O (O × O) a) := by
    intro a
    have key : ∀ g : T ⟶ Spec (.of (O × O)),
        ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ g.appTop).hom (algebraMap O (O × O) a) =
          ((Scheme.ΓSpecIso (.of O)).inv ≫ (g ≫ twoπ O).appTop).hom a := by
      intro g
      rw [Scheme.Hom.comp_appTop, ← Category.assoc]
      have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (O × O)))
      have n' : CommRingCat.ofHom (algebraMap O (O × O)) ≫ (Scheme.ΓSpecIso (.of (O × O))).inv =
          (Scheme.ΓSpecIso (.of O)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))).appTop := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← n']
      rfl
    rw [key h, key h', hπ]

  have h2 : ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom ((1, 0) : O × O) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom ((1, 0) : O × O) := by
    change h.appTop (fst1 O) = h'.appTop (fst1 O)
    have hid : fst1 O * fst1 O = fst1 O := by
      rw [fst1, ← map_mul]; congr 1; ext <;> simp
    apply GlobalTheory.idempotent_eq_of_basicOpen_eq T
    · rw [← map_mul, hid]
    · rw [← map_mul, hid]
    · rw [← Scheme.preimage_basicOpen_top, ← Scheme.preimage_basicOpen_top, hb]

  ext1
  ext x
  obtain ⟨a, b⟩ := x
  have hx : ((a, b) : O × O) = algebraMap O (O × O) a * (1, 0) + algebraMap O (O × O) b * (1 - (1, 0)) := by
    ext <;> simp
  rw [hx, map_add (f := _), map_mul, map_mul, map_sub, map_one, map_add (f := _), map_mul, map_mul, map_sub, map_one, h1 a, h1 b, h2]

end GlobalTheory.AlgConn
end
end

section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem isLocalizationAway_subring {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A')
    (S : Subring A) (S' : Subring A') (hρ : ∀ a ∈ S, ρ a ∈ S') (s : A) (hs : s ∈ S)
    (hloc : letI := ρ.toAlgebra; IsLocalization.Away s A')
    (hu : ∃ v ∈ S', ρ s * v = 1) (hd : ∀ a : A, ρ a ∈ S' → ∃ m : ℕ, s ^ m * a ∈ S) :
    (letI := (ρ.restrict S S' hρ).toAlgebra
     IsLocalization.Away (⟨s, hs⟩ : S) S') := by
  let := ρ.toAlgebra
  let := (ρ.restrict S S' hρ).toAlgebra
  refine .mk _ ?_ (fun z ↦ ?_) fun a b hab ↦ ?_
  · obtain ⟨v, hv, hsv⟩ := hu
    exact .of_mul_eq_one (⟨v, hv⟩ : S') (Subtype.ext hsv)
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := A') s (z : A')
    have ha' : ρ a = (z : A') * ρ s ^ n := ha.symm
    have hmem : ρ a ∈ S' := ha' ▸ S'.mul_mem z.2 (S'.pow_mem (hρ s hs) n)
    obtain ⟨m, hm⟩ := hd a hmem
    refine ⟨n + m, ⟨s ^ m * a, hm⟩, Subtype.ext ?_⟩
    change (z : A') * ρ s ^ (n + m) = ρ (s ^ m * a)
    rw [map_mul, map_pow, ha', pow_add]
    ring
  · have h : ρ a = ρ b := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') s (a := (a : A)) (b := (b : A)) h
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

end GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem coequifibered_subNat (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))
    (hd : ∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) →
      ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) :
    (subNat F α V T).Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  have hloc := Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp hα U f
  have hnat : (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) =
      (α.app (op (X.basicOpen f))).hom ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) := by
    have := congr($(α.naturality (homOfLE (X.basicOpen_le f)).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  have hu : ∃ v ∈ sub F α V T (X.basicOpen f),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) * v = 1 := by
    obtain ⟨w, hw⟩ : ∃ w : Γ(X, X.basicOpen f),
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f * w = 1 :=
      (X.toRingedSpace.isUnit_res_basicOpen f).exists_right_inv
    refine ⟨(α.app (op (X.basicOpen f))).hom w, algebraMap_mem_sub F α V T _ w, ?_⟩
    rw [hnat, ← map_mul, hw, map_one]
  exact isLocalizationAway_subring (F.map (homOfLE (X.basicOpen_le f)).op).hom
    (sub F α V T U.1) (sub F α V T (X.basicOpen f)) (fun a ha ↦ res_mem_sub F α V T _ ha)
    _ (algebraMap_mem_sub F α V T U.1 f) hloc hu (hd U.1 U.2 f)

end GlobalTheory.QcSub
end
