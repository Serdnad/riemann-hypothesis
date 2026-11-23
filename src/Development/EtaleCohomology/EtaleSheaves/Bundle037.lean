module

public import Development.EtaleCohomology.EtaleSheaves.Bundle022
public import Development.EtaleCohomology.EtaleSheaves.Bundle023
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
open CategoryTheory Limits Polynomial

namespace LateralTheory.E.PushPf
open LateralTheory.E.t_E3Cut

section
variable {C D : Type} [CommRing C] [CommRing D] (v : C →+* D) (Q : Ideal D) [Q.IsPrime]

abbrev phi : C →+* D ⧸ Q := (Ideal.Quotient.mk Q).comp v

lemma phi_comp : (phi v Q).range.subtype.comp (phi v Q).rangeRestrict = phi v Q := by ext; rfl

lemma alg_of (x : D) (p : C[X]) (n : ℕ) (hn : v (p.coeff n) ∉ Q) (hp : p.eval₂ v x ∈ Q) :
    IsAlgebraic (phi v Q).range (Ideal.Quotient.mk Q x) := by
  refine ⟨p.map (phi v Q).rangeRestrict, ?_, ?_⟩
  · intro h0
    have := congrArg (fun q => q.coeff n) h0
    simp only [coeff_map, coeff_zero] at this
    apply hn
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h2 := congrArg Subtype.val this
    simpa using h2
  · rw [aeval_def, eval₂_map]
    have : (algebraMap (phi v Q).range (D ⧸ Q)).comp (phi v Q).rangeRestrict = phi v Q := phi_comp v Q
    rw [this, phi, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hp

lemma of_alg (x : D) (h : IsAlgebraic (phi v Q).range (Ideal.Quotient.mk Q x)) :
    ∃ p : C[X], (∃ n, v (p.coeff n) ∉ Q) ∧ p.eval₂ v x ∈ Q := by
  obtain ⟨q, hq0, hq⟩ := h
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective _ (phi v Q).rangeRestrict_surjective q
  refine ⟨p, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hq0
    ext n
    simp only [coeff_map, coeff_zero]
    simp only [ZeroMemClass.coe_zero]
    change Ideal.Quotient.mk Q (v (p.coeff n)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hall n)
  · rw [aeval_def, eval₂_map] at hq
    have : (algebraMap (phi v Q).range (D ⧸ Q)).comp (phi v Q).rangeRestrict = phi v Q := phi_comp v Q
    rw [this, phi, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem] at hq
    exact hq
end

end LateralTheory.E.PushPf

namespace LateralTheory.E.PushPf
open LateralTheory.E.t_E3Cut TensorProduct

lemma gen {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D)
    (h : IsPushout f g u v) (T : Subring D) (hu : ∀ b, u.hom b ∈ T) (hv : ∀ c, v.hom c ∈ T) (d : D) :
    d ∈ T := by
  algebraize [f.hom, g.hom]
  have ht : IsPushout f g (CommRingCat.ofHom (S := B ⊗[A] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := B ⊗[A] C) Algebra.TensorProduct.includeRight.toRingHom) :=
    CommRingCat.isPushout_tensorProduct A B C
  set e := ht.isoIsPushout _ _ h
  have h1 : ∀ b : B, e.hom.hom (b ⊗ₜ[A] (1 : C)) = u.hom b := fun b => by
    have := congr($(ht.inl_isoIsPushout_hom _ _ h).hom b)
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have h2 : ∀ c : C, e.hom.hom ((1 : B) ⊗ₜ[A] c) = v.hom c := fun c => by
    have := congr($(ht.inr_isoIsPushout_hom _ _ h).hom c)
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hd : d = e.hom.hom (e.inv.hom d) := by
    have := congrArg (fun φ => φ.hom d) e.inv_hom_id
    simpa using this.symm
  rw [hd]
  induction (e.inv.hom d) using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact T.zero_mem
  | tmul b c =>
    have hbc : b ⊗ₜ[A] c = (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hbc, map_mul, h1, h2]
    exact T.mul_mem (hu b) (hv c)
  | add x y hx hy => rw [map_add (f := _)]; exact T.add_mem hx hy

theorem Push_of : LateralTheory.E.AlgResPropsPf.Push := by
  intro A B C D f g u v h hf Q hQ d
  have hw : ∀ a, u.hom (f.hom a) = v.hom (g.hom a) := fun a => by
    have := congrArg (fun φ => φ.hom a) h.w
    simpa using this
  let S := (phi v.hom Q).range
  let T : Subring D :=
    { carrier := {x | IsAlgebraic S (Ideal.Quotient.mk Q x)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul] at *; exact ha.mul hb
      one_mem' := by simp only [Set.mem_ofPred_eq, map_one]; exact isAlgebraic_one
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at *; exact ha.add hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact isAlgebraic_zero
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_neg] at *
        have := (isAlgebraic_algebraMap (R := S) (A := D ⧸ Q) (-1)).mul ha
        simpa using this }
  have hv : ∀ c, v.hom c ∈ T := fun c => by
    refine alg_of v.hom Q (v.hom c) (X - Polynomial.C c) 1 ?_ ?_
    · simp only [coeff_sub, coeff_X_one, coeff_C, one_ne_zero, if_false, sub_zero, map_one]
      exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
    · simp [Q.zero_mem]
  have hu : ∀ b, u.hom b ∈ T := fun b => by
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hf (Q.comap u.hom) (Ideal.comap_isPrime u.hom Q) b
    refine alg_of v.hom Q (u.hom b) (p.map g.hom) n ?_ ?_
    · rw [coeff_map, ← hw]; exact hn
    · have hc : v.hom.comp g.hom = u.hom.comp f.hom := by ext a; exact (hw a).symm
      rw [eval₂_map, hc, ← Polynomial.hom_eval₂]
      exact hp
  exact of_alg v.hom Q d (gen f g u v h T hu hv d)

end LateralTheory.E.PushPf
end
end

section

noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.E.CompPf
open LateralTheory.E.t_E3Cut

section
variable {R D : Type} [CommRing R] [CommRing D] (h : R →+* D)

theorem eval_map_rr (p : R[X]) (x : D) :
    (p.map h.rangeRestrict).eval₂ h.range.subtype x = p.eval₂ h x := by
  rw [eval₂_map]; rfl

theorem alg_of (x : D) (p : R[X]) (n : ℕ) (hn : h (p.coeff n) ≠ 0) (hp : p.eval₂ h x = 0) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra;
    IsAlgebraic h.range x := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  refine ⟨p.map h.rangeRestrict, ?_, ?_⟩
  · intro h0
    apply hn
    have h1 := congrArg (fun q => ((q.coeff n : h.range) : D)) h0
    simpa using h1
  · rw [aeval_def]; exact (eval_map_rr h p x).trans hp

theorem of_alg (x : D) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra;
    IsAlgebraic h.range x → ∃ p : R[X], (∃ n, h (p.coeff n) ≠ 0) ∧ p.eval₂ h x = 0 := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  rintro ⟨q, hq0, hq⟩
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective h.rangeRestrict h.rangeRestrict_surjective q
  refine ⟨p, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    apply hq0
    ext n
    simp only [coeff_map, coeff_zero]
    simpa using hc n
  · rw [aeval_def] at hq; exact (eval_map_rr h p x).symm.trans hq
end

theorem Comp_of : LateralTheory.E.AlgResPropsPf.Comp := by
  intro A B C f g hf hg Q hQ c
  haveI := hQ
  let gB : B →+* C ⧸ Q := (Ideal.Quotient.mk Q).comp g.hom
  let fA : A →+* C ⧸ Q := gB.comp f.hom
  have hle : fA.range ≤ gB.range := by rintro _ ⟨a, rfl⟩; exact ⟨f.hom a, rfl⟩
  letI : Algebra fA.range (C ⧸ Q) := fA.range.subtype.toAlgebra
  letI : Algebra gB.range (C ⧸ Q) := gB.range.subtype.toAlgebra
  letI : Algebra fA.range gB.range := (Subring.inclusion hle).toAlgebra
  haveI : IsScalarTower fA.range gB.range (C ⧸ Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI h1 : Algebra.IsAlgebraic fA.range gB.range := ⟨by
    rintro ⟨_, b, rfl⟩
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hf (Q.comap g.hom) (hQ.comap _) b
    have hb := alg_of fA (gB b) p n (by
        intro h0; apply hn; rw [Ideal.mem_comap]; exact Ideal.Quotient.eq_zero_iff_mem.mp h0)
      (by
        have h5 : (Ideal.Quotient.mk Q) (g.hom (p.eval₂ f.hom b)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂, hom_eval₂] at h5; exact h5)
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom fA.range gB.range (C ⧸ Q)) Subtype.val_injective).mp hb⟩
  haveI h2 : Algebra.IsAlgebraic gB.range (C ⧸ Q) := ⟨by
    intro x
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hg Q hQ c'
    exact alg_of gB _ p n (fun h0 => hn (Ideal.Quotient.eq_zero_iff_mem.mp h0))
      (by
        have h5 : (Ideal.Quotient.mk Q) (p.eval₂ g.hom c') = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂] at h5; exact h5)⟩
  have h3 := (Algebra.IsAlgebraic.trans fA.range gB.range (C ⧸ Q)).1 (Ideal.Quotient.mk Q c)
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := of_alg fA _ h3
  refine ⟨p, ⟨n, fun hm => hn (Ideal.Quotient.eq_zero_iff_mem.mpr hm)⟩, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hom_eval₂]; exact hp

end LateralTheory.E.CompPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescIntPf

def RelZS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {U E : Spc} (u : U ⟶ E) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R u F m)) ∧ Function.Injective (pull R u F n)

theorem relZ_iff (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    RelZ q i n f ↔ RelZS (ZMod q) (tw q i) n (sch.map (Spec.map f)) := Iff.rfl

theorem transfer (R : Type) [CommRing R] (F : Shv R) {U E X' X : Spc} (u : U ⟶ E) (f : X' ⟶ X) (a' : U ⟶ X')
    (a : E ⟶ X) (hsq : u ≫ a = a' ≫ f) (ha : Eqv R a F) (ha' : Eqv R a' F) (n : ℤ) (hu : RelZS R F n u) :
    RelZS R F n f := by
  have key : ∀ m (x : H R X F m), pull R a' F m (pull R f F m x) = pull R u F m (pull R a F m x) := by
    intro m x
    rw [← pull_comp, ← pull_comp, hsq]
  refine ⟨fun m hm y => ?_, fun x x' hxx => ?_⟩
  · obtain ⟨z, hz⟩ := hu.1 m hm (pull R a' F m y)
    obtain ⟨x, rfl⟩ := (ha m).2 z
    refine ⟨x, (ha' m).1 ?_⟩
    rw [key, hz]
  · have h1 := congrArg (pull R a' F n) hxx
    rw [key, key] at h1
    exact (ha n).1 (hu.2 h1)

theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := fun n => by
  have h1 : ∀ x, pull R e.inv F n (pull R e.hom F n x) = x := fun x => by
    rw [← pull_comp, e.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R e.hom F n (pull R e.inv F n x) = x := fun x => by
    rw [← pull_comp, e.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem RelZS.of_iso (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (u : U ⟶ E) (u' : U' ⟶ E') (e₁ : U ≅ U')
    (e₂ : E ≅ E') (hsq : u ≫ e₂.hom = e₁.hom ≫ u') (n : ℤ) (hu : RelZS R F n u) : RelZS R F n u' :=
  transfer R F u u' e₁.hom e₂.hom hsq (eqv_of_iso R F e₂) (eqv_of_iso R F e₁) n hu

def EtaleRelativeIsoTruncationFromLevels : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ (p : ℕ) (m : ℤ), m < n → RelZS R F m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) →
  RelZS R F n (disc.map (u.app (Opposite.op (SimplexCategory.mk 0)))) → RelZS R F n u

def CechSq : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
  ∃ (U E : Spc) (u : U ⟶ E) (a' : U ⟶ sch.obj (Spec Y')) (a : E ⟶ sch.obj (Spec C)),
    u ≫ a = a' ≫ sch.map (Spec.map φ') ∧ Eqv _ a (tw q i) ∧ Eqv _ a' (tw q i) ∧
    (∀ p : ℕ, ∃ (L : CommRingCat.{0}) (l : A ⟶ L) (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : L ⟶ Z),
      P L l ∧ IsPushout φ l wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) ∧
    ∃ (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : D ⟶ Z), IsPushout φ (c ≫ g) wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk 0))))

theorem DescInt_of (hT : EtaleRelativeIsoTruncationFromLevels) (hC : CechSq) : LateralTheory.E.StalkCut.DescInt := by
  intro hH q _ i n A Y φ hq P hpush hbelow C D c g hCc hDc hgi hgs hDn Y' w φ' hpo
  obtain ⟨U, E, u, a', a, hsq, ha, ha', hlev, Z, wz, ψ, hpo0, h0⟩ :=
    hC hH q i φ hq P @hpush c g hCc hDc hgi hgs Y' w φ' hpo
  rw [relZ_iff]
  refine transfer _ _ u _ a' a hsq ha ha' n (hT _ _ u n (fun p m hm => ?_) (h0 n (hDn Z wz ψ hpo0)))
  obtain ⟨L, l, Z', wz', ψ', hL, hpo', hrel⟩ := hlev p
  exact hrel m (hbelow m hm L l hL Z' wz' ψ' hpo')

end LateralTheory.E.DescIntPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.EtAffNbhdPf

theorem EtAffNbhd_of : LateralTheory.E.SHSectionPf.EtAffNbhd := by
  intro A _ V g hg _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let x : Spec A := ⟨m, hm.isPrime⟩
  obtain ⟨v, hv⟩ := g.surjective x
  let 𝒰 := V.affineCover
  obtain ⟨p, hp⟩ := 𝒰.covers v
  let ι := 𝒰.f (𝒰.idx v)
  have : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (𝒰.f (𝒰.idx v)))
  have : Etale ι := inferInstance
  have : Etale (ι ≫ g) := inferInstance
  let f : A ⟶ _ := Spec.preimage (ι ≫ g)
  have hfg : Spec.map f = ι ≫ g := Spec.map_preimage _
  refine ⟨_, f, ι, ?_, hfg.symm, p.asIdeal, p.isPrime, ?_⟩
  · have : Etale (Spec.map f) := by have h := ‹Etale (ι ≫ g)›; rw [← hfg] at h; exact h
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  · have h1 : (Spec.map f).base p = x := by
      rw [hfg]
      change g.base (ι.base p) = x
      rw [hp, hv]
    have h2 : ((Spec.map f).base p).asIdeal = p.asIdeal.comap f.hom := rfl
    rw [← h2, h1]
    exact hm

end LateralTheory.E.EtAffNbhdPf
end
end

section

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.HKCoprodPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {K : ι → CochainComplex C ℤ} (c : Cofan K)
  (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {L : CochainComplex C ℤ}

include hc in
theorem hom_ext_v {p q : ℤ} {a b : c.pt.X p ⟶ L.X q} (h : ∀ j, (c.inj j).f p ≫ a = (c.inj j).f p ≫ b) : a = b :=
  (hc p).hom_ext fun ⟨j⟩ => h j

include hc in
theorem cochain_ext {n : ℤ} {x y : Cochain c.pt L n}
    (h : ∀ j, (Cochain.ofHom (c.inj j)).comp x (zero_add n) = (Cochain.ofHom (c.inj j)).comp y (zero_add n)) : x = y := by
  ext p q hpq
  refine hom_ext_v c hc fun j => ?_
  have := congrArg (fun z => Cochain.v z p q hpq) (h j)
  simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using this

def cof (L : CochainComplex C ℤ) {n : ℤ} (b : ∀ j, Cochain (K j) L n) (p q : ℤ) (hpq : p + n = q) :
    Cocone (Discrete.functor K ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) p) where
  pt := L.X q
  ι := Discrete.natTrans fun k => (b k.as).v p q hpq

def glue (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {n : ℤ}
    (b : ∀ j, Cochain (K j) L n) : Cochain c.pt L n :=
  Cochain.mk fun p q hpq => (hc p).desc (cof L b p q hpq)

theorem restr_glue {n : ℤ} (b : ∀ j, Cochain (K j) L n) (j : ι) :
    (Cochain.ofHom (c.inj j)).comp (glue c hc b) (zero_add n) = b j := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact (hc p).fac (cof L b p q hpq) ⟨j⟩

include hc in
theorem bij (n : ℤ) : Function.Bijective fun (x : CohomologyClass c.pt L n) (j : ι) =>
    cpre (Cocycle.ofHom (c.inj j)) L n n (zero_add n) x := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    have hj : ∀ j, ∃ β : Cochain (K j) L (n - 1),
        δ (n - 1) n β = (Cochain.ofHom (c.inj j)).comp (x - y : Cocycle c.pt L n).1 (zero_add n) := by
      intro j
      have h := congrFun hxy j
      simp only [cpre_mk] at h
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (by omega)] at h
      obtain ⟨β, hβ⟩ := h
      refine ⟨β, ?_⟩
      rw [hβ]
      simp [zcomp, Cochain.comp_sub]
    choose β hβ using hj
    refine ⟨glue c hc β, cochain_ext c hc fun j => ?_⟩
    rw [← δ_ofHom_comp, restr_glue, hβ]
  · intro y
    choose z hz using fun j => (y j).mk_surjective
    have hδ : δ n (n + 1) (glue c hc fun j => (z j).1) = 0 := cochain_ext c hc fun j => by
      rw [← δ_ofHom_comp, restr_glue, Cocycle.δ_eq_zero]; simp
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hδ), funext fun j => ?_⟩
    simp only [cpre_mk]
    rw [← hz j]
    congr 1
    exact Cocycle.ext (restr_glue c hc (fun j => (z j).1) j)

end General


theorem HKCoprod_of : LateralTheory.E.CoprodPf.HKCoprod := by
  intro R _ ι K c hc F n
  have h1 : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits.{1} (Shv R)
  have h0 : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} (Shv R)
  have : HasColimitsOfShape (Discrete ι) (Shv R) := inferInstance
  exact bij c (fun p => isColimitOfPreserves (HomologicalComplex.eval _ _ p) hc) n

end LateralTheory.E.HKCoprodPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescLocPf

def LocPts (q : ℕ) (i : ℤ) {A Y D : CommRingCat.{0}} (φ : A ⟶ Y) (d : A ⟶ D) : Prop :=
  ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)

def CokLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)

def KerLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → LocPts q i φ c →
    ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
    ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  Function.Injective (pull _ (sch.map (Spec.map φ')) (tw q i) n)

theorem DescLoc_of (hC : CokLoc) (hK : KerLoc) : LateralTheory.E.StalkCut.DescLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD hpts Y' w φ' hpo
  exact ⟨hC hH q i n φ hq P hpush het hlow D d hD hpts Y' w φ' hpo,
    hK hH q i n φ hq P hpush het hlow (fun C c hC' hpC => hC hH q i n φ hq P hpush het hlow C c hC' hpC) D d hD hpts Y' w φ' hpo⟩

end LateralTheory.E.DescLocPf
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SepTensorPf

theorem SepTensor_of : LateralTheory.E.SHTensorPf.SepTensor := by
  intro A X B Z x b u v hp _ hX _ hb _ hZ
  obtain ⟨_, hXs⟩ := hX
  have hu : u.hom.IsIntegral := LateralTheory.E.SHTensorPf.intPush hp hb
  let f : X →+* IsLocalRing.ResidueField Z := (IsLocalRing.residue Z).comp u.hom
  have hf : f.IsIntegral := RingHom.IsIntegral.trans u.hom (IsLocalRing.residue Z) hu
    (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective)
  let _ : Algebra X (IsLocalRing.ResidueField Z) := f.toAlgebra
  have : Algebra.IsIntegral X (IsLocalRing.ResidueField Z) := ⟨hf⟩
  have : Algebra.IsIntegral (IsLocalRing.ResidueField X) (IsLocalRing.ResidueField Z) :=
    Algebra.IsIntegral.tower_top X
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField X)

end LateralTheory.E.SepTensorPf
end
end
