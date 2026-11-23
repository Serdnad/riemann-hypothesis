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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ULAPf
open LateralTheory.E.t_E3Cut

theorem spS_of_integral_injective {C D : CommRingCat.{0}} (g : C ⟶ D) (hi : g.hom.IsIntegral)
    (hj : Function.Injective g.hom) : SpS g := by
  intro r hr
  letI := g.hom.toAlgebra
  have : Algebra.IsIntegral C D := ⟨hi⟩
  have hk : RingHom.ker (algebraMap C D) ≤ r := by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap C D)).1 hj]; exact bot_le
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral r ⊥ (by rw [Ideal.under_def C (B := D), ← RingHom.ker_eq_comap_bot (algebraMap C D)]; exact hk)
  exact ⟨Q, hQ, hQc⟩

theorem SpS.comp {C D E : CommRingCat.{0}} {f : C ⟶ D} {g : D ⟶ E} (hf : SpS f) (hg : SpS g) : SpS (f ≫ g) := by
  intro r hr
  obtain ⟨Q0, hQ0, hQ0c⟩ := hf r hr
  obtain ⟨Q, hQ, hQc⟩ := hg Q0 hQ0
  exact ⟨Q, hQ, by rw [CommRingCat.hom_comp, ← Ideal.comap_comap, hQc, hQ0c]⟩

theorem ULA_of (hS : Stalk) (hP : AlgResProps) (hE : AICExt) (hD : DomCover) (hL : LocIE) (hU : ULAStalk) : ULA := by
  intro H q _ i A X h hq hA hX hIE hloc C c hc
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
  refine hS H q i (pC A ≫ h) hq (fun _ c => AlgRes c) ?_ ?_ ?_ C c hc
  · intro C D E Z c f g u v hpo _ hf hg
    have hv : AlgRes v := p3 f g u v hpo (p2 c f hf)
    have := p1 (c ≫ g) v hg hv
    rw [hpo.w, ← Category.assoc]; exact this
  · intro C D c f hc hf
    exact p1 c f hc (p4 f hf)
  · intro C c hc
    obtain ⟨D0, g0, hg0i, hg0j, hg0a⟩ := hE C
    obtain ⟨D, g1, hg1i, hg1s, hg1d⟩ := hD D0 hg0a
    have hgi : (g0 ≫ g1).hom.IsIntegral := by
      rw [CommRingCat.hom_comp]; exact RingHom.IsIntegral.trans _ _ hg0i hg1i
    refine ⟨D, g0 ≫ g1, hgi, SpS.comp (spS_of_integral_injective g0 hg0i hg0j) hg1s,
      p1 c (g0 ≫ g1) hc (p5 _ hgi), ?_⟩
    intro r hr
    have := hr
    obtain ⟨hdom, haic⟩ := hg1d r
    let o : D ⟶ CommRingCat.of (Localization.AtPrime r) := CommRingCat.ofHom (algebraMap D _)
    have ho : AlgRes o := p6 D (Localization.AtPrime r) r.primeCompl
    refine ⟨CommRingCat.of (Localization.AtPrime r), o, IsLocalRing.maximalIdeal _,
      hL D (Localization.AtPrime r) r.primeCompl, inferInstance,
      IsLocalization.AtPrime.under_maximalIdeal _ r, ?_⟩
    haveI : IsDomain (CommRingCat.of (Localization.AtPrime r)) := hdom
    haveI : IsLocalRing (CommRingCat.of (Localization.AtPrime r)) :=
      inferInstanceAs (IsLocalRing (Localization.AtPrime r))
    exact hU H q i h hq hA hX hIE hloc _ (c ≫ (g0 ≫ g1) ≫ o) haic
      (p1 c _ hc (p1 _ o (p5 _ hgi) ho))

end LateralTheory.E.ULAPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.StalkCut

def RelZ (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map f)) (tw q i) m)) ∧
  Function.Injective (pull _ (sch.map (Spec.map f)) (tw q i) n)

def BCn (q : ℕ) (i n : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RelZ q i n φ'

def PushClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)

def EtClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)

theorem relZ_neg (hH : Hyp) (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (hn : n < 0) : RelZ q i n f := by
  have hA9 := (hH.2.2.2.2.2.1 (ZMod q) (tw q i)).1
  refine ⟨fun m hm y => ?_, fun x y _ => ?_⟩
  · haveI := hA9 (sch.obj (Spec B)) m (by omega)
    exact ⟨0, Subsingleton.elim _ _⟩
  · haveI := hA9 (sch.obj (Spec A)) n hn
    exact Subsingleton.elim _ _

theorem re_of_relZ {q : ℕ} {i : ℤ} {A B : CommRingCat.{0}} {f : A ⟶ B} (h : ∀ n, RelZ q i n f) : RE q i f :=
  fun m => ⟨(h m).2, (h (m + 1)).1 m rfl⟩

def DescInt : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  BCn q i n φ (c ≫ g) → BCn q i n φ c

def DescLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  (∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)) →
  BCn q i n φ d

theorem goal_of (hInt : DescInt) (hLoc : DescLoc) : LateralTheory.E.t_E3Cut.Stalk := by
  intro hH q _ i A Y φ hq P hpush het hcov C c hC
  have key : ∀ k : ℕ, ∀ m : ℤ, m < k → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c := by
    intro k
    induction k with
    | zero =>
      intro m hm C c _ Y' w φ' _
      exact relZ_neg hH q i m φ' (by exact_mod_cast hm)
    | succ k ih =>
      intro m hm C c hC
      have hm' : m ≤ (k : ℤ) := by push_cast at hm; omega
      rcases lt_or_eq_of_le hm' with h | h
      · exact ih m h C c hC
      · subst h
        obtain ⟨D, g, hgi, hgs, hD, hpts⟩ := hcov C c hC
        have hDl : BCn q i (k : ℤ) φ (c ≫ g) :=
          hLoc hH q i k φ hq P @hpush @het ih D (c ≫ g) hD (fun r hr => by
            obtain ⟨O, o, Q, h1, h2, h3, h4⟩ := hpts r hr
            exact ⟨O, o, Q, h1, h2, h3, by rwa [Category.assoc]⟩)
        exact hInt hH q i k φ hq P @hpush ih c g hC hD hgi hgs hDl
  intro Y' w φ' hpo
  refine re_of_relZ fun n => ?_
  exact key (n.toNat + 1) n (by omega) C c hC Y' w φ' hpo

end LateralTheory.E.StalkCut
end
end

section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.AlgResPropsPf
open LateralTheory.E.t_E3Cut

theorem cancel {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : AlgRes (f ≫ g)) : AlgRes g := by
  intro Q hQ c
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := h Q hQ c
  refine ⟨p.map f.hom, ⟨n, ?_⟩, ?_⟩
  · rw [Polynomial.coeff_map]; simpa using hn
  · rw [Polynomial.eval₂_map]; simpa using hp

theorem integral {A B : CommRingCat.{0}} (f : A ⟶ B) (h : f.hom.IsIntegral) : AlgRes f := by
  intro Q hQ c
  obtain ⟨p, hm, hp⟩ := h c
  refine ⟨p, ⟨p.natDegree, ?_⟩, ?_⟩
  · rw [← Polynomial.leadingCoeff, hm.leadingCoeff, map_one]
    exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
  · rw [hp]; exact Q.zero_mem

theorem loc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] :
    AlgRes (CommRingCat.ofHom (algebraMap A B)) := by
  intro Q hQ c
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
  refine ⟨Polynomial.C (s : A) * Polynomial.X - Polynomial.C a, ⟨1, ?_⟩, ?_⟩
  · have hu : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
    intro hm
    apply hQ.ne_top
    apply Q.eq_top_of_isUnit_mem hm
    simpa [Polynomial.coeff_C, Polynomial.coeff_X] using hu
  · have := IsLocalization.mk'_spec B a s
    simp only [CommRingCat.hom_ofHom, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [mul_comm, this, sub_self]; exact Q.zero_mem

def Comp : Prop :=
  ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)

def Push : Prop :=
  ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v

def EtAlg : Prop := ∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f

theorem AlgResProps_of (h1 : Comp) (h2 : Push) (h3 : EtAlg) : LateralTheory.E.t_E3Cut.AlgResProps :=
  ⟨fun f g hf hg => h1 f g hf hg, fun f g h => cancel f g h, fun f g u v h hf => h2 f g u v h hf,
    fun f h => h3 f h, fun f h => integral f h, fun A B _ _ _ S _ => loc A B S⟩

end LateralTheory.E.AlgResPropsPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.BasePf

theorem polyPO {A C : CommRingCat.{0}} (f : A ⟶ C) :
    IsPushout (pC A) f (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) (pC C) := by
  algebraize [f.hom, Polynomial.mapRingHom f.hom]
  exact (CommRingCat.isPushout_of_isPushout A C (Polynomial A) (Polynomial C)).flip

theorem et_map {A C : CommRingCat.{0}} (f : A ⟶ C) (hf : Et f) :
    Et (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) := by
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange
  exact (RingHom.toMorphismProperty RingHom.Etale).of_isPushout (polyPO f) hf

theorem Base_of (h : LateralTheory.E.t_E3Cut.EtaleBaseChangeFractionFieldIndEtaleOverPolynomial) : LateralTheory.E.t_E3Cut.Base := by
  intro H q _ i T _ _ _ hT hq B c hc Y' w φ' hpo
  rw [Category.id_comp] at hpo
  have hc4 : C4 := H.2.2.2.2.2.2.2.2.2.2
  have hqB : IsUnit (q : B) := by simpa using hq.map c.hom
  have hqY : IsUnit (q : Y') := by simpa using hqB.map φ'.hom
  have sq := hpo.flip.paste_horiz (polyPO φ')
  have e1 : c ≫ pC B = pC (CommRingCat.of T) ≫ CommRingCat.ofHom (Polynomial.mapRingHom c.hom) := by
    ext x; simp
  rw [e1] at sq
  have hIE : IE (CommRingCat.ofHom (Polynomial.mapRingHom c.hom)) :=
    MorphismProperty.le_ind _ _ (et_map c hc)
  have r2 : RE q i (CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom)) :=
    h H q i T (FractionRing T) hT hq _ _ hIE _ _ _ sq.flip
  have r1 : RE q i (pC B) := hc4 q B hqB i
  have r3 : RE q i (pC Y') := hc4 q Y' hqY i
  have e2 : pC B ≫ CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom) = φ' ≫ pC Y' := by
    ext x; simp
  have r4 : RE q i (φ' ≫ pC Y') := e2 ▸ r1.comp r2
  exact RE.of_comp_right r3 r4

end LateralTheory.E.BasePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.CoprodPf

def FreeCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (X : ι → Scheme.{0}),
  Nonempty (IsColimit (Cofan.mk ((free R).obj (yoneda.obj (∐ X))) fun j => (free R).map (yoneda.map (Sigma.ι X j))))

def ChainsDiscCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q),
  Nonempty (IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))

def HKCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (K : ι → Cx R) (c : Cofan K), IsColimit c →
  ∀ (F : Shv R) (n : ℤ), Function.Bijective fun (x : HK R c.pt F n) (j : ι) => HK.pull R (c.inj j) F n x

theorem Coprod_of (h1 : FreeCoprod) (h2 : ChainsDiscCoprod) (h3 : HKCoprod) : LateralTheory.E.t_E3Cut.Coprod := by
  intro R _ F ι X n
  obtain ⟨hc⟩ := h2 R (fun j => yoneda.obj (X j)) (yoneda.obj (∐ X)) (fun j => yoneda.map (Sigma.ι X j)) (h1 R X)
  exact h3 R _ _ hc F n

end LateralTheory.E.CoprodPf
end
end

section

noncomputable section
open CategoryTheory Limits Opposite

namespace LateralTheory.E.LocDiagPf


open Classical in
def g {S : Type} [CommRing S] (p : PrimeSpectrum S) (s : Finset p.asIdeal.primeCompl) : S :=
  ∏ x ∈ s, (x : S)

variable {S : Type} [CommRing S] (p : PrimeSpectrum S)

theorem g_mem (s : Finset p.asIdeal.primeCompl) : g p s ∈ p.asIdeal.primeCompl := by
  classical
  unfold g
  convert Submonoid.prod_mem _ (fun (x : p.asIdeal.primeCompl) _ => x.2)

theorem g_dvd {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) : g p s ∣ g p t := by
  classical
  unfold g
  convert Finset.prod_dvd_prod_of_subset s t (fun x : p.asIdeal.primeCompl => (x : S)) h

theorem g_single (y : p.asIdeal.primeCompl) : g p {y} = (y : S) := by
  classical
  unfold g
  convert Finset.prod_singleton (fun x : p.asIdeal.primeCompl => (x : S)) y

theorem unitAway {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    IsUnit (algebraMap S (Localization.Away (g p t)) (g p s)) :=
  isUnit_of_dvd_unit (map_dvd _ (g_dvd p h)) (IsLocalization.Away.algebraMap_isUnit _)

def tr {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    Localization.Away (g p s) →+* Localization.Away (g p t) :=
  IsLocalization.Away.lift (g p s) (unitAway p h)

theorem tr_comp {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    (tr p h).comp (algebraMap S _) = algebraMap S _ :=
  IsLocalization.Away.lift_comp _ _

theorem tr_apply {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) (x : S) :
    tr p h (algebraMap S _ x) = algebraMap S _ x :=
  IsLocalization.Away.lift_eq _ _ _

theorem away_ext {s : Finset p.asIdeal.primeCompl} {P : Type} [CommRing P]
    {u v : Localization.Away (g p s) →+* P}
    (h : u.comp (algebraMap S _) = v.comp (algebraMap S _)) : u = v :=
  IsLocalization.ringHom_ext (Submonoid.powers (g p s)) h

def Dg : Finset p.asIdeal.primeCompl ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (Localization.Away (g p s))
  map {s t} h := CommRingCat.ofHom (tr p (leOfHom h))
  map_id s := by
    ext1
    apply away_ext
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, tr_comp]
    rfl
  map_comp {s t u} a b := by
    ext1
    apply away_ext
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    rw [RingHom.comp_assoc, tr_comp, tr_comp, tr_comp]

theorem unitLoc (s : Finset p.asIdeal.primeCompl) :
    IsUnit (algebraMap S (Localization.AtPrime p.asIdeal) (g p s)) :=
  IsLocalization.map_units _ (⟨g p s, g_mem p s⟩ : p.asIdeal.primeCompl)

def toLoc (s : Finset p.asIdeal.primeCompl) :
    Localization.Away (g p s) →+* Localization.AtPrime p.asIdeal :=
  IsLocalization.Away.lift (g p s) (unitLoc p s)

theorem toLoc_comp (s : Finset p.asIdeal.primeCompl) :
    (toLoc p s).comp (algebraMap S _) = algebraMap S _ :=
  IsLocalization.Away.lift_comp _ _

theorem toLoc_apply (s : Finset p.asIdeal.primeCompl) (x : S) :
    toLoc p s (algebraMap S _ x) = algebraMap S _ x :=
  IsLocalization.Away.lift_eq _ _ _

def Cc : Cocone (Dg p) where
  pt := CommRingCat.of (Localization.AtPrime p.asIdeal)
  ι :=
    { app := fun s => (CommRingCat.ofHom (toLoc p s) : (Dg p).obj s ⟶ CommRingCat.of (Localization.AtPrime p.asIdeal))
      naturality := fun s t h => by
        ext1
        apply away_ext
        simp only [Functor.const_obj_map, CommRingCat.hom_comp, CommRingCat.hom_ofHom, Dg]
        rw [RingHom.comp_assoc, tr_comp, toLoc_comp, RingHom.comp_assoc, toLoc_comp]
        rfl }

def phi (c : Cocone (Dg p)) : S →+* c.pt :=
  (c.ι.app ∅).hom.comp (algebraMap S (Localization.Away (g p ∅)))

theorem cocone_comp (c : Cocone (Dg p)) (s : Finset p.asIdeal.primeCompl) :
    (c.ι.app s).hom.comp (algebraMap S (Localization.Away (g p s))) = phi p c := by
  have hw := c.w (homOfLE (Finset.empty_subset s))
  unfold phi
  rw [← hw]
  ext x
  exact congrArg (c.ι.app s).hom (tr_apply p (Finset.empty_subset s) x).symm

theorem phi_unit (c : Cocone (Dg p)) (y : p.asIdeal.primeCompl) : IsUnit (phi p c y) := by
  rw [← DFunLike.congr_fun (cocone_comp p c {y}) (y : S)]
  have hy : IsUnit (algebraMap S (Localization.Away (g p {y})) y) := by
    rw [show (y : S) = g p {y} from (g_single p y).symm]
    exact IsLocalization.Away.algebraMap_isUnit _
  exact IsUnit.map (c.ι.app {y}).hom hy

def isColim : IsColimit (Cc p) where
  desc c := CommRingCat.ofHom (IsLocalization.lift (M := p.asIdeal.primeCompl)
    (S := Localization.AtPrime p.asIdeal) (phi_unit p c))
  fac c s := by
    ext1
    apply away_ext
    ext x
    change (IsLocalization.lift (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal)
      (phi_unit p c)) (toLoc p s (algebraMap S _ x)) =
      (c.ι.app s).hom (algebraMap S (Localization.Away (g p s)) x)
    rw [toLoc_apply, IsLocalization.lift_eq]
    exact (DFunLike.congr_fun (cocone_comp p c s) x).symm
  uniq c m hm := by
    ext1
    refine IsLocalization.ringHom_ext (S := Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl ?_
    ext x
    have hx := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hm ∅))
      (algebraMap S (Localization.Away (g p ∅)) x)
    change m.hom (algebraMap S (Localization.AtPrime p.asIdeal) x) =
      (IsLocalization.lift (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal)
      (phi_unit p c)) (algebraMap S _ x)
    rw [IsLocalization.lift_eq]
    refine Eq.trans ?_ hx
    change _ = m.hom (toLoc p ∅ (algebraMap S _ x))
    rw [toLoc_apply]

theorem LocDiag_of : LateralTheory.E.ZarLocalPf.LocDiag := by
  intro S _ p
  refine ⟨Finset p.asIdeal.primeCompl, inferInstance, inferInstance, Dg p, Cc p,
    ⟨isColim p⟩, id, ∅, algebraMap S (Localization.Away (g p ∅)), ?_⟩
  intro k m
  refine ⟨g p k, g_mem p k, RingHom.id _, ?_⟩
  ext x
  exact tr_apply p (leOfHom m) x

end LateralTheory.E.LocDiagPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHSectionPf

def SHAlgSec : Prop := ∀ (A R : CommRingCat.{0}) (f : A ⟶ R), SH A → f.hom.Etale →
  (∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal) → ∃ σ : R ⟶ A, f ≫ σ = 𝟙 A

def EtAffNbhd : Prop := ∀ (A : CommRingCat.{0}) [Nontrivial A] {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ (R : CommRingCat.{0}) (f : A ⟶ R) (ι : Spec R ⟶ V), f.hom.Etale ∧ ι ≫ g = Spec.map f ∧
    ∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal

theorem SHSection_of (h1 : SHAlgSec) (h2 : EtAffNbhd) : LateralTheory.E.t_E3Cut.SHSection := by
  intro A hA V g _ _
  have : Nontrivial A := by obtain ⟨hH, -⟩ := hA; infer_instance
  obtain ⟨R, f, ι, hf, hι, hQ⟩ := h2 A g
  obtain ⟨σ, hσ⟩ := h1 A R f hA hf hQ
  refine ⟨Spec.map σ ≫ ι, ?_⟩
  rw [Category.assoc, hι, ← Spec.map_comp, hσ, Spec.map_id]

end LateralTheory.E.SHSectionPf
end
end
