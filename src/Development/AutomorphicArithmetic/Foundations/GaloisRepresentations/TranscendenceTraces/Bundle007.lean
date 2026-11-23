module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

open Classical in
private lemma cyc_eq_sum {S Y : Scheme.{0}} (c : Corr S Y) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y) (AF : Finset (gp Ω ⟶ c.Z)) (hAF : ∀ s, s ∈ AF ↔ s ≫ c.p = x) :
    c.cyc Ω x y = ∑ s ∈ AF with s ≫ c.f = y, c.w Ω s := by
  have hs : {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y} = ↑(AF.filter (fun s => s ≫ c.f = y)) := by
    ext z
    simp [hAF]
  show (∑ᶠ (z : gp Ω ⟶ c.Z) (_ : z ∈ {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y}), c.w Ω z) = _
  rw [hs, finsum_mem_coe_finset]

theorem UpperTheory.Gal.TranscendenceTraces.cycComp_of :
    FibFin → CycComp := by
  classical
  intro hF S Y X c d e a b pb hp hf hw Ω _ _ x y
  haveI := c.fin
  haveI := d.fin
  haveI := e.fin
  let A := (hF c.p Ω x).toFinset
  have hAm : ∀ s, s ∈ A ↔ s ≫ c.p = x := fun s => by simp [A, fib]
  let B : (gp Ω ⟶ Y) → Finset (gp Ω ⟶ d.Z) := fun t => (hF d.p Ω t).toFinset
  have hBm : ∀ t u, u ∈ B t ↔ u ≫ d.p = t := fun t u => by simp [B, fib]
  let E := (hF e.p Ω x).toFinset
  have hEm : ∀ z, z ∈ E ↔ z ≫ e.p = x := fun z => by simp [E, fib]
  have hR : (∑ᶠ t : gp Ω ⟶ Y, c.cyc Ω x t * d.cyc Ω t y) =
      ∑ s ∈ A, c.w Ω s * d.cyc Ω (s ≫ c.f) y := by
    rw [finsum_eq_sum_of_support_subset (s := A.image (· ≫ c.f))]
    · rw [← Finset.sum_fiberwise_of_maps_to (s := A) (t := A.image (· ≫ c.f)) (g := (· ≫ c.f))
          (fun s hs => Finset.mem_image_of_mem _ hs)]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [(Finset.mem_filter.1 hs).2]
    · intro t ht
      rw [Function.mem_support] at ht
      by_contra hn
      apply ht
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_eq_zero, zero_mul]
      intro s hs
      exact absurd (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨s, (Finset.mem_filter.1 hs).1, (Finset.mem_filter.1 hs).2⟩)) hn
  have hmaps : ∀ z ∈ E.filter (fun z => z ≫ e.f = y), z ≫ b ∈ A := by
    intro z hz
    rw [hAm, Category.assoc, ← hp]
    exact (hEm z).1 (Finset.mem_filter.1 hz).1
  rw [hR, cyc_eq_sum e Ω x y E hEm, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [cyc_eq_sum d Ω (s ≫ c.f) y (B (s ≫ c.f)) (hBm _), Finset.mul_sum]
  refine Finset.sum_bij' (fun z _ => z ≫ a)
    (fun u hu => pb.lift u s ((hBm _ u).1 (Finset.mem_filter.1 hu).1)) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, hEm, hBm] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pb.w, ← Category.assoc, hz.2]
    · rw [Category.assoc, ← hf, hz.1.2]
  · intro u hu
    have hu' := Finset.mem_filter.1 hu
    simp only [Finset.mem_filter, hEm]
    refine ⟨⟨?_, ?_⟩, pb.lift_snd _ _ _⟩
    · rw [hp, ← Category.assoc, pb.lift_snd]
      exact (hAm s).1 hs
    · rw [hf, ← Category.assoc, pb.lift_fst]
      exact hu'.2
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    apply pb.hom_ext
    · rw [pb.lift_fst]
    · rw [pb.lift_snd, hz'.2]
  · intro u hu
    exact pb.lift_fst _ _ _
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    rw [hw]
    show d.w Ω (z ≫ a) * c.w Ω (z ≫ b) = c.w Ω s * d.w Ω (z ≫ a)
    rw [hz'.2, mul_comm]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

noncomputable section

namespace UpperTheory.Gal.TranscendenceTraces.FamilyComposition

variable {W Z S : Scheme.{0}} (r : W ⟶ Z) (p : Z ⟶ S)

private def cr (A : Sq (r ≫ p)) : A.V ⟶ pullback p A.u :=
  pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w)

private lemma cr_fst (A : Sq (r ≫ p)) : cr r p A ≫ pullback.fst p A.u = A.v ≫ r := pullback.lift_fst _ _ _

private lemma cr_snd (A : Sq (r ≫ p)) : cr r p A ≫ pullback.snd p A.u = A.r := pullback.lift_snd _ _ _

private abbrev sqB (A : Sq (r ≫ p)) : Sq p := Sq.of p A.u

private def sqC (A : Sq (r ≫ p)) : Sq r :=
  ⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, cr r p A,
    IsPullback.of_bot (by rw [cr_snd]; exact A.pb) (cr_fst r p A).symm (IsPullback.of_hasPullback p A.u)⟩

variable {r p}

private def mid {A A' : Sq (r ≫ p)} (t : A.To A') : pullback p A.u ⟶ pullback p A'.u :=
  pullback.lift (pullback.fst p A.u) (pullback.snd p A.u ≫ t.g)
    (by rw [Category.assoc, t.hu]; exact pullback.condition)

private lemma mid_fst {A A' : Sq (r ≫ p)} (t : A.To A') : mid t ≫ pullback.fst p A'.u = pullback.fst p A.u :=
  pullback.lift_fst _ _ _

private lemma mid_snd {A A' : Sq (r ≫ p)} (t : A.To A') :
    mid t ≫ pullback.snd p A'.u = pullback.snd p A.u ≫ t.g := pullback.lift_snd _ _ _

private def toB {A A' : Sq (r ≫ p)} (t : A.To A') : (sqB r p A).To (sqB r p A') :=
  ⟨t.g, mid t, t.hu, mid_fst t, mid_snd t⟩

private def toC {A A' : Sq (r ≫ p)} (t : A.To A') : (sqC r p A).To (sqC r p A') :=
  ⟨mid t, t.k, mid_fst t, by
      have := t.hv
      exact this, by
      change t.k ≫ cr r p A' = cr r p A ≫ mid t
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, cr_fst, mid_fst, cr_fst, ← Category.assoc, t.hv]
      · rw [Category.assoc, Category.assoc, cr_snd, mid_snd, ← Category.assoc, cr_snd, t.hr]⟩

variable (r p)

private def comp0 {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] {F : Shv R₁} {G : Shv R₂} {H : Shv R₃}
    (a : Fam0 r F G) (b : Fam0 p G H) : Fam0 (r ≫ p) F H where
  app A := (b.app (sqB r p A)).comp (a.app (sqC r p A))
  nat {A A'} t x := by
    have h1 := b.nat (toB t) (a.app (sqC r p A') x)
    have h2 := a.nat (toC t) x
    exact h1.trans (congrArg (b.app (sqB r p A)) h2)

private lemma zsmul_finsum_mem {ι M : Type*} [AddCommGroup M] (d : ℤ) {s : Set ι} (f : ι → M) (hs : s.Finite) :
    d • ∑ᶠ i ∈ s, f i = ∑ᶠ i ∈ s, d • f i :=
  (zsmulAddGroupHom d).map_finsum_mem f hs

end UpperTheory.Gal.TranscendenceTraces.FamilyComposition

open UpperTheory.Gal.TranscendenceTraces.FamilyComposition in
theorem UpperTheory.Gal.TranscendenceTraces.famComp_of :
    SumComp → FibFin → FamComp := by
  intro hS hF q i W Z S r p _ _ w' w τ' τ h' h
  refine ⟨⟨fun s => comp0 r p (τ'.deg s) (τ.deg s), fun A s t a => ?_⟩, fun A a => ?_, fun n a => ?_⟩
  · exact ((τ.comm (sqB r p A) s t _).trans
      (congrArg ((τ.deg t).app (sqB r p A)) (τ'.comm (sqC r p A) s t a)))
  · obtain ⟨b1, e1, s1⟩ := h' (sqC r p A) a
    obtain ⟨b2, e2, s2⟩ := h (sqB r p A) b1
    refine ⟨b2, (congrArg ((τ.deg 0).app (sqB r p A)) e1).trans e2, ?_⟩
    intro Ω _ _ x
    haveI fB : IsFinite (pullback.snd p A.u) := Sq.finite (sqB r p A)
    haveI fC : IsFinite (cr r p A) := Sq.finite (sqC r p A)
    have key := hS (cr r p A) (pullback.snd p A.u) Ω x (Sec (tw q i) (gp Ω))
      (fun z => (Wt.mul r w' w) Ω (z ≫ A.v) • Sec.res z a)
    rw [cr_snd] at key
    refine (s2 Ω x).trans (Eq.trans ?_ key.symm)
    refine finsum_mem_congr rfl fun (y : gp Ω ⟶ pullback p A.u) _ => ?_
    have e : (Sec.res y b1 : Sec (tw q i) (gp Ω)) = ∑ᶠ z ∈ fib (cr r p A) y, w' Ω (z ≫ A.v) • Sec.res z a := s1 Ω y
    refine (congrArg (fun m => w Ω (y ≫ pullback.fst p A.u) • m) e).trans ?_
    refine (zsmul_finsum_mem _ _ (hF (cr r p A) Ω y)).trans ?_
    refine finsum_mem_congr rfl fun z hz => ?_
    have hy : (z ≫ A.v) ≫ r = y ≫ pullback.fst p A.u := by
      have hz' : z ≫ cr r p A = y := hz
      rw [← hz', Category.assoc, Category.assoc, cr_fst]
    change _ = (w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r)) • Sec.res z a
    rw [hy, mul_comm, mul_smul]
  · let t1 : (sqB r p (Sq.self (r ≫ p))).To (Sq.self p) :=
      ⟨𝟙 S, pullback.fst p (𝟙 S), Category.comp_id _, Category.comp_id _,
        pullback.condition⟩
    let t2 : (sqC r p (Sq.self (r ≫ p))).To (Sq.self r) :=
      ⟨pullback.fst p (𝟙 S), 𝟙 W, Category.comp_id _, Category.comp_id _, by
        have := cr_fst r p (Sq.self (r ≫ p))
        exact (Eq.trans this.symm rfl : _)⟩
    have n1 := (τ.deg n).nat t1 ((τ'.deg n).app (Sq.self r) a)
    have n2 := (τ'.deg n).nat t2 a
    have e1 : (τ.deg n).app (Sq.self p) ((τ'.deg n).app (Sq.self r) a) =
        (τ.deg n).app (sqB r p (Sq.self (r ≫ p))) (Sec.res (pullback.fst p (𝟙 S)) ((τ'.deg n).app (Sq.self r) a)) :=
      (res_id _).symm.trans n1
    have e2 : Sec.res (pullback.fst p (𝟙 S)) ((τ'.deg n).app (Sq.self r) a) =
        (τ'.deg n).app (sqC r p (Sq.self (r ≫ p))) a :=
      n2.trans (congrArg _ (res_id a))
    exact (e1.trans (congrArg _ e2)).symm
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrCompQ_of :
    CycComp → WtBC → WtComp → TrBCQ → TrCompQ → CorrCompQ := by
  intro hC hBC hWC hTB hTC S Y X c d
  haveI := c.fin
  haveI := d.fin
  have pb := IsPullback.of_hasPullback d.p c.f
  have hbw := hBC _ _ d.p c.f d.w pb d.wt
  have hw := hWC (pullback.snd d.p c.f) c.p (Wt.comap (pullback.fst d.p c.f) d.w) c.w hbw c.wt
  let e : Corr S X := ⟨pullback d.p c.f, pullback.snd d.p c.f ≫ c.p, pullback.fst d.p c.f ≫ d.f,
    Wt.mul (pullback.snd d.p c.f) (Wt.comap (pullback.fst d.p c.f) d.w) c.w, inferInstance, hw⟩
  refine ⟨e, pullback.fst d.p c.f, pullback.snd d.p c.f, pb, rfl, rfl, rfl, ?_, ?_⟩
  · exact hC c d e _ _ pb rfl rfl rfl
  · intro l _ n i hl hl2
    have hpull : pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
        pullHQ l (sch.map (pullback.fst d.p c.f)) n i ∘ₗ pullHQ l (sch.map d.f) n i := by
      simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]
    have key := hTB l n i _ _ d.p c.f d.w pb d.wt hl2
    show trHQ l (pullback.snd d.p c.f ≫ c.p) _ n i ∘ₗ pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
      (trHQ l c.p c.w n i ∘ₗ pullHQ l (sch.map c.f) n i) ∘ₗ (trHQ l d.p d.w n i ∘ₗ pullHQ l (sch.map d.f) n i)
    rw [hTC l n i _ _ _ _ hbw c.wt hl, hpull]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply]
    exact congrArg (trHQ l c.p c.w n i) (LinearMap.congr_fun key _).symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def sqPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) (A : Sq p) : Sq (h ≫ p) :=
  ⟨A.U, pullback h A.v, A.u, pullback.fst h A.v, pullback.snd h A.v ≫ A.r,
    (IsPullback.of_hasPullback h A.v).paste_vert A.pb⟩

private def resHom {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec F U →+ Sec F V :=
  (F.obj.map g.op).hom.toAddMonoidHom

private theorem pushK_w {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pullback.fst h A.v ≫ h = (pullback.snd h A.v ≫ t.k) ≫ B.v := by
  rw [Category.assoc, t.hv]
  exact pullback.condition

private noncomputable def pushK {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pullback h A.v ⟶ pullback h B.v :=
  pullback.lift (pullback.fst h A.v) (pullback.snd h A.v ≫ t.k) (pushK_w h t)

private theorem pushK_fst {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.fst h B.v = pullback.fst h A.v := pullback.lift_fst _ _ _

private theorem pushK_snd {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.snd h B.v = pullback.snd h A.v ≫ t.k := pullback.lift_snd _ _ _

private theorem pushK_r {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.snd h B.v ≫ B.r = (pullback.snd h A.v ≫ A.r) ≫ t.g := by
  rw [← Category.assoc, pushK_snd, Category.assoc, t.hr, Category.assoc]

private noncomputable def toPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {A B : Sq p} (t : A.To B) :
    (sqPush h p A).To (sqPush h p B) :=
  ⟨t.g, pushK h t, t.hu, pushK_fst h t, pushK_r h t⟩

private theorem res_pushK {R : Type} [CommRing R] {F : Shv R} {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S}
    {A B : Sq p} (t : A.To B) (a : Sec F B.V) :
    Sec.res (pushK h t) (Sec.res (pullback.snd h B.v) a) = Sec.res (pullback.snd h A.v) (Sec.res t.k a) := by
  rw [res_res, res_res, pushK_snd]

private noncomputable def familyPushforward {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {R' R : Type} [CommRing R']
    [CommRing R] {F : Shv R'} {G : Shv R} (τ : Fam0 (h ≫ p) F G) : Fam0 p F G where
  app A := (τ.app (sqPush h p A)).comp (resHom F (pullback.snd h A.v))
  nat {A B} t a := (τ.nat (toPush h p t) (Sec.res (pullback.snd h B.v) a)).trans
    (congrArg (τ.app (sqPush h p A)) (res_pushK h t a))

private noncomputable def famPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {R' R : Type} [CommRing R']
    [CommRing R] {I : Cx R'} {J : Cx R} (τ : Fam (h ≫ p) I J) : Fam p I J where
  deg s := familyPushforward h p (τ.deg s)
  comm A s t a := (τ.comm (sqPush h p A) s t (Sec.res (pullback.snd h A.v) a)).trans
    (congrArg ((τ.deg t).app (sqPush h p A)) (map_res (I.d s t) (pullback.snd h A.v) a))

private theorem sum_push (hS : SumComp) (hF : FibFin) {q : ℕ} {i : ℤ} {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S)
    [IsFinite h] [IsFinite p] (w : Wt Z) (A : Sq p) (a : Sec (tw q i) A.V) (b : Sec (tw q i) A.U)
    (hb : IsSum w (sqPush h p A) (Sec.res (pullback.snd h A.v) a) b) : IsSum (w.push h) A a b := by
  intro Ω _ _ x
  haveI := A.finite
  refine (hb Ω x).trans ((hS (pullback.snd h A.v) A.r Ω x _
    (fun z => w Ω (z ≫ pullback.fst h A.v) • Sec.res z (Sec.res (pullback.snd h A.v) a))).trans ?_)
  refine finsum_congr fun y => finsum_congr fun hy => ?_
  have hfin := hF (pullback.snd h A.v) Ω y
  have hbij := fib_bijOn (IsPullback.of_hasPullback h A.v) (Ω := Ω) y
  have hsum := finsum_mem_eq_of_bijOn (f := fun z => w Ω (z ≫ pullback.fst h A.v))
    (g := fun z' => w Ω z') _ hbij (fun _ _ => rfl)
  show _ = (∑ᶠ (z' : gp Ω ⟶ Z) (_ : z' ∈ fib h (y ≫ A.v)), w Ω z') • Sec.res y a
  rw [← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Set.Finite.mem_toFinset] at hz
  rw [res_res]
  congr 2

private theorem self_r {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) :
    pullback.fst h (𝟙 Z') ≫ h ≫ p = (pullback.snd h (𝟙 Z') ≫ p) ≫ 𝟙 S := by
  rw [Category.comp_id, ← Category.assoc, pullback.condition, Category.comp_id]

private theorem res_self {R : Type} [CommRing R] {F : Shv R} {Z Z' : Scheme.{0}} (h : Z ⟶ Z') (a : Sec F Z') :
    Sec.res (pullback.fst h (𝟙 Z')) (Sec.res h a) = Sec.res (pullback.snd h (𝟙 Z')) a := by
  rw [res_res, pullback.condition, Category.comp_id]

theorem UpperTheory.Gal.TranscendenceTraces.famPush_of :
    SumComp → FibFin → FamPush := by
  intro hS hF q i Z Z' S h p _ _ w τ hτ
  refine ⟨famPush h p τ, ?_, ?_⟩
  · intro A a
    obtain ⟨b, hb, hbs⟩ := hτ (sqPush h p A) (Sec.res (pullback.snd h A.v) a)
    refine ⟨b, ?_, sum_push hS hF h p w A a b hbs⟩
    show (τ.deg 0).app (sqPush h p A)
      (Sec.res (pullback.snd h A.v) (Sec.map (resι (ZMod q) (tw q i)) a)) = _
    exact (congrArg ((τ.deg 0).app (sqPush h p A)) (map_res _ _ a)).symm.trans hb
  · intro n a
    let t : (sqPush h p (Sq.self p)).To (Sq.self (h ≫ p)) :=
      ⟨𝟙 S, pullback.fst h (𝟙 Z'), Category.id_comp _, Category.comp_id _, self_r h p⟩
    have hn : Sec.res (𝟙 S) ((τ.deg n).app (Sq.self (h ≫ p)) (Sec.res h a)) =
        (τ.deg n).app (sqPush h p (Sq.self p)) (Sec.res (pullback.fst h (𝟙 Z')) (Sec.res h a)) :=
      (τ.deg n).nat t (Sec.res h a)
    show (τ.deg n).app (sqPush h p (Sq.self p)) (Sec.res (pullback.snd h (𝟙 Z')) a) = _
    exact (congrArg ((τ.deg n).app (sqPush h p (Sq.self p))) (res_self h a).symm).trans
      (hn.symm.trans (res_id _))
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtComp_of :
    SumComp → FibFin → WtComp := by
  intro hsum hfin W Z S r p _ _ w' w hr hp A φ hφ
  obtain ⟨m, hm1, hm2⟩ : ∃ m : A.V ⟶ pullback p A.u,
      m ≫ pullback.fst p A.u = A.v ≫ r ∧ m ≫ pullback.snd p A.u = A.r :=
    ⟨pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsq : IsPullback A.v m r (pullback.fst p A.u) := by
    refine IsPullback.of_bot ?_ hm1.symm (IsPullback.of_hasPullback p A.u)
    rw [hm2]
    exact A.pb
  let C : Sq r := ⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, m, hsq⟩
  haveI : IsFinite m := C.finite
  haveI : IsFinite (pullback.snd p A.u) := (Sq.of p A.u).finite
  obtain ⟨ψ1, hψ1, hψ1s⟩ := hr C φ hφ
  obtain ⟨ψ2, hψ2, hψ2s⟩ := hp (Sq.of p A.u) ψ1 hψ1
  refine ⟨ψ2, hψ2, ?_⟩
  intro Ω _ _ x
  have hsc : ∀ c : (gp Ω ⟶ A.V) → ℤ, ∑ᶠ z ∈ fib (m ≫ pullback.snd p A.u) x, c z =
      ∑ᶠ y ∈ fib (pullback.snd p A.u) x, ∑ᶠ z ∈ fib m y, c z := by
    intro c
    have h := congrArg (AddEquiv.ulift : ULift.{1} ℤ ≃+ ℤ)
      (hsum m (pullback.snd p A.u) Ω x (ULift.{1} ℤ) (fun z => ULift.up (c z)))
    simp only [AddEquiv.map_finsum] at h
    exact h
  refine (hψ2s Ω x).trans ?_
  rw [← hm2, hsc]
  refine finsum_mem_congr rfl ?_
  intro y _
  refine (congrArg (fun t => w Ω (y ≫ pullback.fst p A.u) * t) (hψ1s Ω y)).trans ?_
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl ?_
  intro z hz
  have hz' : z ≫ m = y := hz
  show w Ω (y ≫ pullback.fst p A.u) * (w' Ω (z ≫ A.v) * φ (pt z)) =
    w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r) * φ (pt z)
  rw [Category.assoc, ← hm1, ← Category.assoc, hz']
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtLin_of :
    FibFin → WtLin := by
  intro hF
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' h1 h2
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    obtain ⟨ψ2, hψ2, e2⟩ := h2 A φ hφ
    refine ⟨ψ1 + ψ2, hψ1.add hψ2, ?_⟩
    intro Ω _ _ x
    haveI := A.finite
    have hfin := hF A.r Ω x
    rw [Pi.add_apply, e1, e2, ← finsum_mem_add_distrib hfin]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = (w Ω _ + w' Ω _) * _
    ring
  · intro Z S p _ d w h1
    unfold IsWt at *
    intro A φ hφ
    obtain ⟨ψ1, hψ1, e1⟩ := h1 A φ hφ
    refine ⟨(fun t => d * t) ∘ ψ1, hψ1.comp _, ?_⟩
    intro Ω _ _ x
    rw [Function.comp_apply, e1, mul_finsum_mem]
    refine finsum_congr fun z => finsum_congr fun _ => ?_
    show _ = d * w Ω _ * _
    ring
  · intro Z S p _ d
    unfold IsWt
    intro A φ hφ
    haveI : IsIso A.r := by
      rw [← A.pb.isoPullback_hom_snd]
      infer_instance
    refine ⟨(fun t => d * t) ∘ φ ∘ ⇑(inv A.r), (hφ.comp_continuous (inv A.r).continuous).comp _, ?_⟩
    intro Ω _ _ x
    have hs : fib A.r x = {x ≫ inv A.r} := by
      ext z
      show z ≫ A.r = x ↔ z = x ≫ inv A.r
      constructor
      · rintro rfl
        simp
      · rintro rfl
        simp
    rw [hs, finsum_mem_singleton, pt_comp]
    rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem fib_spec_finite (Ω B : Type) [Field Ω] [CommRing B] [Algebra Ω B] [Module.Finite Ω B] :
    (fib (Ω := Ω) (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) (𝟙 (gp Ω))).Finite := by
  apply (Set.finite_range (fun g : B →ₐ[Ω] Ω => Spec.map (CommRingCat.ofHom (g : B →+* Ω)))).subset
  intro z hz
  have hz' : z ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = 𝟙 _ := hz
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = z := ⟨Spec.preimage z, Spec.map_preimage z⟩
  rw [← Spec.map_comp, ← Spec.map_id] at hz'
  have h2 := Spec.map_injective hz'
  refine ⟨{ φ.hom with commutes' := fun c => ?_ }, ?_⟩
  · have := congrArg (fun g => g.hom c) h2
    simpa using this
  · rfl

theorem UpperTheory.Gal.TranscendenceTraces.fibFin_of :
    Chart → FibFin := by
  intro hC
  unfold Chart at hC
  unfold FibFin
  intro V U r _ Ω _ x
  obtain ⟨B, iB, iAB, v, hfin, hpb⟩ := hC r Ω x
  haveI := hfin
  have h := (fib_bijOn hpb (𝟙 (gp Ω))).image_eq
  rw [Category.id_comp] at h
  rw [← h]
  exact (fib_spec_finite Ω B).image _
end
