module

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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.AICSHPf

theorem root_near {T : Type} [CommRing T] [IsDomain T] (hA : ∀ p : Polynomial T, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0)
    (P : Ideal T) [P.IsPrime] (a₀ : T) :
    ∀ (n : ℕ) (f : T[X]), f.natDegree = n → f.Monic → f.eval a₀ ∈ P → ∃ a, f.IsRoot a ∧ a - a₀ ∈ P := by
  intro n
  induction n with
  | zero =>
    intro f hd hm hv
    have : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst this
    simp only [eval_one] at hv
    exact absurd ((Ideal.eq_top_iff_one P).2 hv) (Ideal.IsPrime.ne_top inferInstance)
  | succ n ih =>
    intro f hd hm hv
    obtain ⟨r, hr⟩ := hA f hm (by omega)
    have hroot : f.IsRoot r := hr
    set q := f /ₘ (X - C r) with hq
    have hfac : (X - C r) * q = f := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) (by rw [hfac]; exact hm)
    have hdeg : q.natDegree = n := by
      have := (monic_X_sub_C r).natDegree_mul hqm
      rw [hfac, natDegree_X_sub_C] at this; omega
    have hv' : (a₀ - r) * q.eval a₀ ∈ P := by
      rw [← hfac] at hv; simpa [eval_mul] using hv
    rcases (inferInstance : P.IsPrime).mem_or_mem hv' with h | h
    · refine ⟨r, hroot, ?_⟩
      have := P.neg_mem_iff.2 h; simpa using this
    · obtain ⟨a, ha, ha'⟩ := ih q hdeg hqm h
      refine ⟨a, ?_, ha'⟩
      rw [← hfac]; simp [IsRoot, eval_mul, ha.eq_zero]

theorem henselian {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) : HenselianLocalRing T where
  is_henselian f hf a₀ h₀ _ := root_near hA (IsLocalRing.maximalIdeal T) a₀ _ f rfl hf h₀

theorem algClosed {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) :
    IsAlgClosed (IsLocalRing.ResidueField T) := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hirr
  obtain ⟨P, hPl, hPd, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.2 fun n => IsLocalRing.residue_surjective _) hpm
  have hpos : 0 < P.natDegree := by
    rw [Polynomial.natDegree_eq_of_degree_eq hPd]; exact Irreducible.natDegree_pos hirr
  obtain ⟨a, ha⟩ := hA P hPm hpos
  refine ⟨IsLocalRing.residue T a, ?_⟩
  rw [← hPl, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]

end LateralTheory.E.AICSHPf

namespace LateralTheory.E.t_E3Cut

theorem AICSH_of : AICSH := by
  intro T _ _ _ hA
  let _ := LateralTheory.E.AICSHPf.henselian hA
  have := LateralTheory.E.AICSHPf.algClosed hA
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.E.t_E3Cut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.ULAStalkPf

def PolyPO : Prop := ∀ {A B : CommRingCat.{0}} (b : A ⟶ B),
  IsPushout (pC A) b (CommRingCat.ofHom (Polynomial.mapRingHom b.hom)) (pC B)

def IECob : Prop := ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D),
  IsPushout f g u v → IE f → IE v

def FracAIC : Prop := ∀ (T K : Type) [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K], AIC T → AIC K

def FracOf : Prop := ∀ (B C : Type) [CommRing B] [CommRing C] [IsDomain C] (j : B →+* C), Function.Injective j →
  (∀ z : C, ∃ s y : B, s ≠ 0 ∧ j s * z = j y) →
  @IsFractionRing B _ (FractionRing C) _ ((algebraMap C (FractionRing C)).comp j).toAlgebra

theorem ULAStalk_of (hI : IntClos) (hT : SHTensor) (hA : AICSH) (hE : SHEqv) (hC3 : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial)
    (p1 : PolyPO) (p2 : IECob) (p3 : FracAIC) (p4 : FracOf) : ULAStalk := by
  intro H q _ i A X h hq hA' hX hh hloc C c _ _ hCa hCr Y' w φ' sq
  obtain ⟨B, b, j, hbj, hbint, hjinj, hBloc, hBaic, hfr⟩ := hI c hA' hCa hCr
  have : IsDomain B := Function.Injective.isDomain j.hom hjinj
  let K := FractionRing C
  let l : C ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap C K)
  let algBK : Algebra B K := ((algebraMap C K).comp j.hom).toAlgebra
  have : IsFractionRing B K := p4 B C j.hom hjinj hfr
  have hKsh : SH K := hA K (p3 C K hCa)
  have hBsh : SH B := hA B hBaic
  have hCsh : SH C := hA C hCa
  have hqB : IsUnit (q : B) := by simpa using hq.map b.hom
  have hqC : IsUnit (q : C) := by simpa using hq.map c.hom

  let mB : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial B) := CommRingCat.ofHom (Polynomial.mapRingHom b.hom)
  have sB : IsPushout h mB (pushout.inl h mB) (pushout.inr h mB) := IsPushout.of_hasPushout _ _
  have hBIE : IE (pushout.inr h mB) := p2 _ _ _ _ sB hh
  have sBA : IsPushout (pC A ≫ h) b (pushout.inl h mB) (pC B ≫ pushout.inr h mB) := (p1 b).paste_horiz sB
  let ZB : CommRingCat.{0} := pushout h mB
  have hZBsh : SH ZB := hT _ _ _ _ sBA hA' hX hloc hbint hBloc
  have r1 : RE q i (pC B ≫ pushout.inr h mB) := hE H q i _ hqB hBsh hZBsh
  let bl : B ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap B K)
  have sL : IsPushout (pC B ≫ pushout.inr h mB) bl (pushout.inl _ bl) (pushout.inr _ bl) := IsPushout.of_hasPushout _ _
  have r2 : RE q i (pushout.inl (pC B ≫ pushout.inr h mB) bl) :=
    hC3 H q i B K hBaic hqB (pushout h mB) (pushout.inr h mB) hBIE _ _ _ sL.flip
  have r3 : RE q i bl := hE H q i bl hqB hBsh hKsh
  have r4 : RE q i (pushout.inr (pC B ≫ pushout.inr h mB) bl) :=
    RE.of_comp_left r3 (by rw [← pushout.condition]; exact r1.comp r2)

  let mC : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial C) := CommRingCat.ofHom (Polynomial.mapRingHom c.hom)
  let hC : CommRingCat.of (Polynomial C) ⟶ Y' := (p1 c).desc (h ≫ w) φ' (by rw [← Category.assoc]; exact sq.w)
  have e1 : mC ≫ hC = h ≫ w := (p1 c).inl_desc _ _ _
  have e2 : pC C ≫ hC = φ' := (p1 c).inr_desc _ _ _
  have sC : IsPushout h mC w hC := IsPushout.of_left (by rw [e2]; exact sq) e1.symm (p1 c)
  have hCIE : IE hC := p2 _ _ _ _ sC hh
  have sq' : IsPushout l (pC C ≫ hC) (pushout.inr φ' l) (pushout.inl φ' l) := by
    rw [e2]; exact (IsPushout.of_hasPushout φ' l).flip
  have r5 : RE q i (pushout.inl φ' l) := hC3 H q i C K hCa hqC Y' hC hCIE _ _ _ sq'
  have r6 : RE q i l := hE H q i l hqC hCsh hKsh
  have ebl : b ≫ bl = c ≫ l := by rw [← hbj]; rfl
  have PZ : IsPushout (pC A ≫ h) (c ≫ l) (pushout.inl h mB ≫ pushout.inl (pC B ≫ pushout.inr h mB) bl)
      (pushout.inr (pC B ≫ pushout.inr h mB) bl) := by
    rw [← ebl]; exact sBA.paste_vert sL
  have PZ' : IsPushout (pC A ≫ h) (c ≫ l) (w ≫ pushout.inl φ' l) (pushout.inr φ' l) :=
    sq.paste_vert (IsPushout.of_hasPushout φ' l)
  have r7 : RE q i (pushout.inr φ' l) := by
    rw [← PZ.inr_isoIsPushout_hom _ _ PZ']; exact r4.comp (RE.of_isIso q i _)
  exact RE.of_comp_right r5 (by rw [pushout.condition]; exact r6.comp r7)

end LateralTheory.E.ULAStalkPf
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.LocIEPf

variable {A : Type} [CommRing A]

def DivS (S : Submonoid A) : Type := S

def val {S : Submonoid A} (s : DivS S) : A := (show S from s).1

lemma val_mem {S : Submonoid A} (s : DivS S) : val s ∈ S := (show S from s).2

instance (S : Submonoid A) : Preorder (DivS S) where
  le s t := val s ∣ val t
  le_refl s := dvd_refl _
  le_trans _ _ _ h1 h2 := dvd_trans h1 h2

def mkD {S : Submonoid A} (a : A) (h : a ∈ S) : DivS S := (⟨a, h⟩ : S)

instance (S : Submonoid A) : IsDirected (DivS S) (· ≤ ·) :=
  ⟨fun s t => ⟨mkD (val s * val t) (S.mul_mem (val_mem s) (val_mem t)),
    Dvd.intro _ rfl, Dvd.intro_left _ rfl⟩⟩

instance (S : Submonoid A) : Nonempty (DivS S) := ⟨mkD 1 S.one_mem⟩

lemma unit_of_dvd {a b : A} (h : a ∣ b) : IsUnit (algebraMap A (Localization.Away b) a) := by
  obtain ⟨c, rfl⟩ := h
  refine isUnit_of_mul_isUnit_left (y := algebraMap A (Localization.Away (a * c)) c) ?_
  rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _

def mp {a b : A} (h : a ∣ b) : Localization.Away a →+* Localization.Away b :=
  IsLocalization.Away.lift a (unit_of_dvd h)

lemma mp_comp {a b : A} (h : a ∣ b) : (mp h).comp (algebraMap A _) = algebraMap A _ :=
  IsLocalization.lift_comp _

lemma mp_alg {a b : A} (h : a ∣ b) (x : A) : mp h (algebraMap A _ x) = algebraMap A _ x :=
  RingHom.congr_fun (mp_comp h) x

lemma ext_away {a : A} {P : Type} [CommRing P] {j k : Localization.Away a →+* P}
    (h : j.comp (algebraMap A _) = k.comp (algebraMap A _)) : j = k :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h

variable (S : Submonoid A)

def F : DivS S ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (Localization.Away (val s))
  map f := CommRingCat.ofHom (mp (leOfHom f))
  map_id s := by
    ext1; apply ext_away; ext x; exact mp_alg (leOfHom (𝟙 s)) x
  map_comp f g := by
    ext1; apply ext_away; ext x
    exact (by rw [mp_alg, mp_alg, mp_alg] : mp (leOfHom (f ≫ g)) (algebraMap A _ x) =
      mp (leOfHom g) (mp (leOfHom f) (algebraMap A _ x)))

def tN : (Functor.const (DivS S)).obj (CommRingCat.of A) ⟶ F S where
  app s := CommRingCat.ofHom (algebraMap A (Localization.Away (val s)))
  naturality s t f := by
    ext1; apply RingHom.ext; intro x
    exact (mp_alg (leOfHom f) x).symm

variable (B : Type) [CommRing B] [Algebra A B] [IsLocalization S B]

def lB (s : DivS S) : Localization.Away (val s) →+* B :=
  IsLocalization.Away.lift (val s) (IsLocalization.map_units B ⟨val s, val_mem s⟩)

lemma lB_alg (s : DivS S) (x : A) : lB S B s (algebraMap A _ x) = algebraMap A B x :=
  RingHom.congr_fun (IsLocalization.lift_comp _) x

def sN : F S ⟶ (Functor.const (DivS S)).obj (CommRingCat.of B) where
  app s := CommRingCat.ofHom (lB S B s)
  naturality s t f := by
    ext1; apply ext_away; ext x
    exact (by rw [mp_alg, lB_alg, lB_alg] :
      lB S B t (mp (leOfHom f) (algebraMap A _ x)) = lB S B s (algebraMap A _ x))

lemma isColim : Nonempty (IsColimit (Cocone.mk _ (sN S B))) := by
  have : ReflectsColimitsOfShape (DivS S) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)⟩
  · intro (x : B)
    obtain ⟨⟨a, m⟩, hx⟩ := IsLocalization.surj S x
    let s : DivS S := mkD (m : A) m.2
    refine ⟨s, IsLocalization.mk' (Localization.Away (val s)) a
      (⟨val s, Submonoid.mem_powers _⟩ : Submonoid.powers (val s)), ?_⟩
    change x = lB S B s _
    have hu := IsLocalization.map_units B m
    refine hu.mul_right_cancel ?_
    rw [hx]
    have h2 : algebraMap A B (m : A) = lB S B s (algebraMap A _ (val s)) := by rw [lB_alg]; rfl
    rw [h2, ← map_mul, IsLocalization.mk'_spec, lB_alg]
  · intro i (y : Localization.Away (val i)) (y' : Localization.Away (val i)) h
    change lB S B i y = lB S B i y' at h
    obtain ⟨⟨c, m⟩, hd⟩ := IsLocalization.surj (Submonoid.powers (val i)) (y - y')
    have hc : algebraMap A B c = algebraMap A B 0 := by
      have := congrArg (lB S B i) hd
      rw [map_mul, map_sub, h, sub_self, zero_mul, lB_alg] at this
      rw [map_zero]; exact this.symm
    obtain ⟨u, hu⟩ := IsLocalization.exists_of_eq (M := S) hc
    let k : DivS S := mkD (val i * (u : A)) (S.mul_mem (val_mem i) u.2)
    have hik : val i ∣ val k := Dvd.intro _ rfl
    refine ⟨k, homOfLE hik, ?_⟩
    change mp hik y = mp hik y'
    rw [← sub_eq_zero, ← map_sub]
    have hm : IsUnit (algebraMap A (Localization.Away (val k)) (m : A)) := by
      obtain ⟨n, hn⟩ := m.2
      rw [← hn, map_pow]; exact (unit_of_dvd hik).pow n
    have hck : algebraMap A (Localization.Away (val k)) c = 0 := by
      have hu' : IsUnit (algebraMap A (Localization.Away (val k)) (u : A)) :=
        unit_of_dvd (Dvd.intro_left _ rfl)
      have := congrArg (algebraMap A (Localization.Away (val k))) hu
      rw [mul_zero, map_mul, map_zero] at this
      exact (hu'.mul_right_eq_zero).1 this
    refine (hm.mul_left_eq_zero).1 ?_
    rw [← mp_alg hik, ← map_mul, hd, mp_alg, hck]

theorem LocIE_of : LateralTheory.E.t_E3Cut.LocIE := by
  intro A B _ _ _ S _
  obtain ⟨hc⟩ := isColim S B
  refine ⟨DivS S, inferInstance, inferInstance, F S, tN S, sN S B, hc, fun j => ⟨?_, ?_⟩⟩
  · change (algebraMap A (Localization.Away (val j))).Etale
    rw [RingHom.etale_algebraMap]
    exact Algebra.Etale.of_isLocalizationAway (val j)
  · ext1; ext x
    exact lB_alg S B j x

end LateralTheory.E.LocIEPf
end
end

section

noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IntClosPf

theorem intMul {A C : Type} [CommRing A] [CommRing C] [IsDomain C] [Algebra A C] (z : C) (p : Polynomial A)
    (hp : ∃ n, algebraMap A C (p.coeff n) ≠ 0) (hz : Polynomial.aeval z p = 0) :
    ∃ a : A, algebraMap A C a ≠ 0 ∧ IsIntegral A (algebraMap A C a * z) := by
  let A' := (algebraMap A C).range
  letI : Algebra A A' := (algebraMap A C).rangeRestrict.toAlgebra
  have : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hsurj : Function.Surjective (algebraMap A A') := (algebraMap A C).rangeRestrict_surjective
  have : Algebra.IsIntegral A A' := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hsurj x
    exact isIntegral_algebraMap⟩
  set p' := p.map (algebraMap A A') with hp'def
  have h1 : Polynomial.aeval z p' = 0 := by rw [Polynomial.aeval_map_algebraMap]; exact hz
  have hp' : p' ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := hp
    apply hn
    have : p'.coeff n = 0 := by rw [h0]; rfl
    rw [hp'def, Polynomial.coeff_map] at this
    have := congrArg Subtype.val this
    exact this
  have hint := isIntegral_leadingCoeff_smul p' z h1
  obtain ⟨a, ha⟩ := hsurj p'.leadingCoeff
  have hlc : p'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
  have hval : algebraMap A C a = (p'.leadingCoeff : C) := by rw [← ha]; rfl
  refine ⟨a, ?_, ?_⟩
  · rw [hval]; intro h; exact hlc (Subtype.ext h)
  · have h2 : algebraMap A C a * z = p'.leadingCoeff • z := by rw [Algebra.smul_def, hval]; rfl
    rw [h2]
    exact isIntegral_trans _ hint

theorem IntClos_of (hH : HensInt) : IntClos := by
  intro A C c _ hSH hAIC hAR
  obtain ⟨hHA, -⟩ := hSH
  letI : Algebra A C := c.hom.toAlgebra
  let B := integralClosure A C
  refine ⟨CommRingCat.of B, CommRingCat.ofHom (algebraMap A B), CommRingCat.ofHom B.val.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; rfl
  · intro x; exact integralClosure.isIntegral x
  · exact Subtype.val_injective
  · have hne : Nontrivial B := inferInstance
    obtain ⟨h⟩ := hH A B (algebraMap A B) (fun x => integralClosure.isIntegral x) (fun e he => by
      rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (show IsIdempotentElem (e : C) from congrArg Subtype.val he)) with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h)
    exact h.toIsLocalRing
  · intro p hm hdeg
    have hm' : (p.map B.val.toRingHom).Monic := hm.map _
    have hdeg' : 0 < (p.map B.val.toRingHom).natDegree := by
      rw [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective]; exact hdeg
    obtain ⟨r, hr⟩ := hAIC _ hm' hdeg'
    have hrB : IsIntegral B r := ⟨p, hm, by rw [← Polynomial.eval_map]; exact hr⟩
    have hrA : IsIntegral A r := isIntegral_trans _ hrB
    have hrM : r ∈ B := hrA
    refine ⟨⟨r, hrM⟩, Subtype.val_injective ?_⟩
    show B.val.toRingHom (p.eval ⟨r, hrM⟩) = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hr
  · intro z
    have hQ : (⊥ : Ideal C).IsPrime := Ideal.isPrime_bot
    obtain ⟨p, ⟨n, hn⟩, hz⟩ := hAR ⊥ hQ z
    obtain ⟨a, ha, hint⟩ := intMul z p ⟨n, fun h => hn (by rw [Ideal.mem_bot]; exact h)⟩
      (by rw [Ideal.mem_bot] at hz; exact hz)
    refine ⟨algebraMap A B a, ⟨_, hint⟩, fun h => ha (congrArg Subtype.val h), rfl⟩

end LateralTheory.E.IntClosPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.E.t_E3Cut

theorem etale_base_change_fraction_field_of_etale_polynomial_algebra (hC3 : C3) (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (hA : AIC T) (hq : IsUnit (q : T))
    (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C) (hc : Et c) :
    BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c) := by
  letI : Algebra (Polynomial T) C := c.hom.toAlgebra
  haveI : Algebra.Etale (Polynomial T) C := hc
  letI : Algebra T C := (pC (CommRingCat.of T) ≫ c).hom.toAlgebra
  haveI : IsScalarTower T (Polynomial T) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h3 := hC3 q T hA hq C i
  have hsq := CommRingCat.isPushout_tensorProduct T (FractionRing T) C
  let e : CommRingCat.of (FractionRing T) ≅ CommRingCat.of K :=
    (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).toRingEquiv.toCommRingCatIso
  have hsq' : IsPushout (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c)
      (e.inv ≫ CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeRight.toRingHom) := by
    refine hsq.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x
      simp [e]
    · rfl
    · simp
    · rfl
  exact BC.of_one hsq' h3

theorem etale_base_change_polynomial_induction_of_limit (hL : Limit) : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial := by
  intro hH q _ i T K _ _ _ _ _ _ hA hq X h hIE
  have hC3 : C3 := hH.2.2.2.2.2.2.2.2.2.1
  let k := CommRingCat.ofHom (algebraMap T K)
  let φ := pushout.inr k (pC (CommRingCat.of T))
  have P1 : IsPushout k (pC (CommRingCat.of T)) (pushout.inl k (pC (CommRingCat.of T))) φ :=
    IsPushout.of_hasPushout _ _
  have hqX : IsUnit ((q : ℕ) : CommRingCat.of (Polynomial T)) := by
    have := hq.map (Polynomial.C : T →+* Polynomial T)
    simpa using this
  have hEt : ∀ (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C), Et c → BC q i φ c := by
    intro C c hc
    have hb := etale_base_change_fraction_field_of_etale_polynomial_algebra hC3 q i T K hA hq C c hc
    have P2 := IsPushout.of_hasPushout φ c
    exact BC.of_one P2 (hb _ _ _ (P1.paste_vert P2))
  have hB := hL hH q i φ hqX hEt X h hIE
  have P2 := IsPushout.of_hasPushout φ h
  exact BC.of_one (P1.paste_vert P2) (hB _ _ _ P2)

end LateralTheory.E.t_E3Cut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SHExistsPf

def SHLoc : Prop := ∀ (A : CommRingCat.{0}) [IsLocalRing A],
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ IsLocalHom f.hom

def LocAt : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A) [r.IsPrime],
  IE (CommRingCat.ofHom (algebraMap A (Localization.AtPrime r)))

def Comp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

theorem SHExists_of (hL : SHLoc) (hA : LocAt) (hC : Comp) : t_E3Cut.SHExists := by
  intro A r hr
  let L : CommRingCat.{0} := CommRingCat.of (Localization.AtPrime r)
  let g : A ⟶ L := CommRingCat.ofHom (algebraMap A (Localization.AtPrime r))
  haveI : IsLocalRing L := inferInstanceAs (IsLocalRing (Localization.AtPrime r))
  obtain ⟨O, h, hIE, hSH, hloc⟩ := hL L
  refine ⟨O, g ≫ h, hC g h (hA A r) hIE, hSH, fun a => ?_⟩
  have key : IsUnit (algebraMap A (Localization.AtPrime r) a) ↔ a ∈ r.primeCompl :=
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime r) r a
  have e : (g ≫ h).hom a = h.hom (algebraMap A (Localization.AtPrime r) a) := rfl
  rw [e]
  constructor
  · intro ha hu
    have := (key.1 (isUnit_of_map_unit h.hom _ hu))
    exact this ha
  · intro hn
    by_contra ha
    exact hn ((key.2 ha).map h.hom)

end LateralTheory.E.SHExistsPf
end
end
