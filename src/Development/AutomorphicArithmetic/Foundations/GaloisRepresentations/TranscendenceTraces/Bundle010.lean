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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a b => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

private theorem length_stalk_eq_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (h : f x = y) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) = Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) := by
  subst h
  have : IsIso (f.stalkMap x) := inferInstance
  exact (length_self_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm

theorem UpperTheory.Gal.TranscendenceTraces.multSec_of :
    MultSec := by
  intro V Ω _ _ r z hz
  haveI : IsIso (z ≫ r) := by rw [hz]; infer_instance
  haveI : IsIso (pullback.fst r (z ≫ r)) := inferInstance
  unfold mult
  rw [length_stalk_eq_of_isIso (pullback.fst r (z ≫ r)) _ (pt z)
    (by rw [← pt_comp, pullback.lift_fst])]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

set_option backward.isDefEq.respectTransparency false in
private theorem isFinite_sigma_desc_of_finite (ι : Type) [Finite ι] :
    ∀ {S : Scheme.{0}} (Z : ι → Scheme.{0}) (p : ∀ a, Z a ⟶ S), (∀ a, IsFinite (p a)) →
      IsFinite (Sigma.desc p) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro S Z p hp
    have := ih (fun a => Z (e a)) (fun a => p (e a)) (fun a => hp _)
    let i : (∐ fun a => Z (e a)) ≅ ∐ Z := Sigma.whiskerEquiv e (fun _ => Iso.refl _)
    have h : i.hom ≫ Sigma.desc p = Sigma.desc (fun a => p (e a)) := by
      apply Sigma.hom_ext
      intro a
      simp [i]
    have h' : Sigma.desc p = i.inv ≫ Sigma.desc (fun a => p (e a)) := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [h']
    infer_instance
  | h_empty =>
    intro S Z p hp
    have : IsEmpty (∐ Z : Scheme.{0}) := ⟨fun x => by
      obtain ⟨i, _, _⟩ := (sigmaOpenCover Z).exists_eq x
      exact i.elim⟩
    infer_instance
  | h_option ih =>
    intro S Z p hp
    have h1 := ih (fun a => Z (some a)) (fun a => p (some a)) (fun a => hp _)
    have h0 := hp none
    let i : (Z none ⨿ ∐ fun a => Z (some a)) ≅ ∐ Z :=
      { hom := coprod.desc (Sigma.ι Z none) (Sigma.desc fun a => Sigma.ι Z (some a))
        inv := Sigma.desc fun o => match o with
          | none => coprod.inl
          | some a => Sigma.ι (fun a => Z (some a)) a ≫ coprod.inr
        hom_inv_id := by
          apply coprod.hom_ext
          · simp
          · apply Sigma.hom_ext
            intro a
            simp
        inv_hom_id := by
          apply Sigma.hom_ext
          rintro (_ | a) <;> simp }
    have h : i.hom ≫ Sigma.desc p = coprod.desc (p none) (Sigma.desc fun a => p (some a)) := by
      apply coprod.hom_ext
      · simp [i]
      · apply Sigma.hom_ext
        intro a
        simp [i]
    have h' : Sigma.desc p = i.inv ≫ coprod.desc (p none) (Sigma.desc fun a => p (some a)) := by
      rw [← h, Iso.inv_hom_id_assoc]
    have c : IsFinite (coprod.desc (p none) (Sigma.desc fun a => p (some a))) := inferInstance
    have d0 : IsIso i.inv := ⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩
    have d : IsFinite i.inv := inferInstance
    rw [h']
    infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.Gal.TranscendenceTraces.imageFin_of :
    ImageOne → ImageFin := by
  intro hOne S Y B bS bY _ _ ι _ Z p f hp hf
  have hk : (Sigma.desc fun a => pullback.lift (f a) (p a) (hf a)) ≫ pullback.snd bY bS = Sigma.desc p := by
    apply Sigma.hom_ext
    intro a
    simp
  obtain ⟨k, hkdef⟩ : ∃ k : ∐ Z ⟶ pullback bY bS, k = Sigma.desc fun a => pullback.lift (f a) (p a) (hf a) := ⟨_, rfl⟩
  rw [← hkdef] at hk
  have hι : ∀ a, Sigma.ι Z a ≫ k = pullback.lift (f a) (p a) (hf a) := by
    intro a
    simp [hkdef]
  have hfin : IsFinite (k ≫ pullback.snd bY bS) := by
    rw [hk]
    exact isFinite_sigma_desc_of_finite ι Z p hp
  obtain ⟨h1, h2⟩ := hOne k (pullback.snd bY bS)
  have hh : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι = pullback.lift (f a) (p a) (hf a) := by
    intro a
    rw [Category.assoc, Scheme.Hom.toImage_imageι, hι]
  have hpa : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.snd bY bS = p a := by
    intro a
    rw [← Category.assoc, hh, pullback.lift_snd]
  have hfa : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.fst bY bS = f a := by
    intro a
    rw [← Category.assoc, hh, pullback.lift_fst]
  refine ⟨k.image, k.imageι ≫ pullback.snd bY bS, k.imageι ≫ pullback.fst bY bS,
    fun a => Sigma.ι Z a ≫ k.toImage, h1, fun a => ?_, hpa, hfa, ?_⟩
  · have : IsFinite ((Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.snd bY bS) := by
      rw [hpa]
      exact hp a
    exact IsFinite.of_comp _ (k.imageι ≫ pullback.snd bY bS)
  · intro T x y hs hf'
    rw [← cancel_mono k.imageι]
    apply pullback.hom_ext
    · simpa using hf'
    · simpa using hs
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtOfFlat_of :
    WtFlat → WtUnique → GenBasic → NwtOfFlat := by
  intro hW hU hG Z S p _ _ _
  have hm : IsNwt p (mult p) := ⟨hW p, fun _ _ _ _ _ => rfl⟩
  have hex : ∃ w, IsNwt p w := ⟨mult p, hm⟩
  have hspec : IsNwt p hex.choose := hex.choose_spec
  have hval : nwt p = hex.choose := by
    unfold nwt
    rw [dite_eq_left hex]
  rw [hval]
  refine hU p _ _ hspec.1 hm.1 {s | GenPt s} (hG.1 S) ?_
  intro Ω _ _ z hz
  exact hspec.2 Ω z hz
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtOpen_of :
    WtBC → MultBC → GenBasic → NwtOpen := by
  intro hw hm hg Z S p w A _ hp
  obtain ⟨hwt, hgen⟩ := hp
  refine ⟨hw A.v A.r p A.u w A.pb hwt, ?_⟩
  intro Ω _ _ z hz
  have hsq : (z ≫ A.v) ≫ p = (z ≫ A.r) ≫ A.u := by
    rw [Category.assoc, Category.assoc, A.pb.w]
  have hz' : GenPt (pt ((z ≫ A.v) ≫ p)) := by
    rw [hsq, pt_comp]
    exact (hg.2.1 A.u (pt (z ≫ A.r))).mpr hz
  rw [hm A.v A.r p A.u A.pb]
  exact hgen Ω (z ≫ A.v) hz'
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumNat_of :
    SumNat := by
  intro R _ F Z S p w A B t a b hB Ω _ _ x
  rw [res_res, hB Ω (x ≫ t.g)]
  symm
  refine finsum_mem_eq_of_bijOn (fun z => z ≫ t.k) (fib_bijOn t.isPullback x) ?_
  intro z _
  simp only [res_res, Category.assoc, t.hv]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trChar_of :
    FL → OpEq → TrSum → PtInj → TrChar := by
  intro hFL hOp hTS hPI q _ i Z S p _ w hw hq
  have hOver : (trFam p w q i).Over (tr0 p w q i) := by
    unfold trFam
    exact GlobalTheory.EtC.pick_spec (hFL q p (tw q i) (tw q i) (tr0 p w q i)).1
  refine ⟨hOver, ?_, ?_⟩
  · intro A a
    exact ⟨(tr0 p w q i).app A a, hOver A a, hTS q i p w hw hq A a⟩
  · intro τ hτ n
    have hτo : τ.Over (tr0 p w q i) := by
      intro A a
      obtain ⟨b, hb, hs⟩ := hτ A a
      have hbe : b = (tr0 p w q i).app A a := by
        apply hPI q i A.U
        intro Ω _ _ x
        rw [hs Ω x, hTS q i p w hw hq A a Ω x]
      rw [hb, hbe]
    exact hOp q p (tw q i) (tw q i) (tr0 p w q i) (trFam p w q i) τ hOver hτo n
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem op_add_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {Z S : Scheme.{0}} {p : Z ⟶ S}
    (τ τ' σ : Fam p (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self p) a = (τ.deg n).app (Sq.self p) a + (τ'.deg n).app (Sq.self p) a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj Z)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = τ.op n x + τ'.op n x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z n).1) x
  have h1 := hOp (ZMod q) (ZMod q) τ n x a ha
  have h2 := hOp (ZMod q) (ZMod q) τ' n x a ha
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ h1 h2).2.2.1
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

private theorem op_smul_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {Z S : Scheme.{0}} {p : Z ⟶ S} (d : ℤ)
    (τ σ : Fam p (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self p) a = d • (τ.deg n).app (Sq.self p) a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj Z)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = d • τ.op n x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z n).1) x
  have h1 := hOp (ZMod q) (ZMod q) τ n x a ha
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ h1 h1).2.2.2 d
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

private theorem op_id_of (hRp : RpBasic) (hOp : RpOp) {q : ℕ} {i n : ℤ} {S : Scheme.{0}} (d : ℤ)
    (σ : Fam (𝟙 S) (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)))
    (h : ∀ a, (σ.deg n).app (Sq.self (𝟙 S)) a = d • a)
    (x : CohomologyClass ((chains (ZMod q)).obj (sch.obj S)) (res (ZMod q) (tw q i)) n) :
    σ.op n x = d • x := by
  obtain ⟨a, ha⟩ := ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).1) x
  have h3 := hOp (ZMod q) (ZMod q) σ n x a ha
  have hS := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1
  have h4 := (hS _ _ _ _ ha ha).2.2.2 d
  exact (hS _ _ _ _ h3 h4).2.1 (h a)

theorem UpperTheory.Gal.TranscendenceTraces.trLin_of :
    TrChar → FamLin → WtLin → RpBasic → RpOp → TrLin := by
  intro hChar hFam hWt hRp hOp q _ n i
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' hw hw' hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).1 p w w' (trFam p w q i) (trFam p w' q i)
      (hChar q i p w hw hq).2.1 (hChar q i p w' hw' hq).2.1
    rw [(hChar q i p (w.add w') (hWt.1 p w w' hw hw') hq).2.2 σ hσ n]
    exact op_add_of hRp hOp _ _ σ (fun a => hσd n _ a) x
  · intro Z S p _ d w hw hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).2.1 p d w (trFam p w q i) (hChar q i p w hw hq).2.1
    rw [(hChar q i p (w.smul d) (hWt.2.1 p d w hw) hq).2.2 σ hσ n]
    exact op_smul_of hRp hOp d _ σ (fun a => hσd n _ a) x
  · intro S d hq x
    obtain ⟨σ, hσ, hσd⟩ := (hFam q i).2.2 S d
    rw [(hChar q i (𝟙 S) (Wt.const S d) (hWt.2.2 (𝟙 S) d) hq).2.2 σ hσ n]
    exact op_id_of hRp hOp d σ (fun a => hσd n a) x
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trPush_of :
    TrChar → FamPush → WtPush → RpBasic → RpOp → TrPush := by
  intro hTr hFam hWt hRp hOp q _ n i Z Z' S h p _ _ w hw hq x
  obtain ⟨σ, hσ, hσd⟩ := hFam q i h p w (trFam (h ≫ p) w q i) (hTr q i (h ≫ p) w hw hq).2.1
  have hw' := hWt h p w hw
  have e2 : tr p (Wt.push h w) q n i = σ.op n := by
    ext y
    exact (hTr q i p (Wt.push h w) hw' hq).2.2 σ hσ n ▸ rfl
  rw [e2]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).1 x
  have h1 := hOp (ZMod q) (ZMod q) σ n x a ha
  have h2 := hOp (ZMod q) (ZMod q) (trFam (h ≫ p) w q i) n _ _
    ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).2.2.2.1 Z h x a ha)
  exact ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h2 h1).2.1 (hσd n a).symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def wSum {Z : Scheme.{0}} {ι : Type} (w : ι → Wt Z) (m : ι → ℤ) (s : Finset ι) : Wt Z :=
  fun Ω _ _ z => ∑ a ∈ s, m a * w a Ω z

theorem UpperTheory.Gal.TranscendenceTraces.trRel_of :
    TrLin → WtLin → WtVanish → TrRel := by
  intro hT hW hV q _ n i Z S p _ ι _ w m hw hq D hD hz x
  classical
  obtain ⟨hTa, hTs, -⟩ := hT q n i
  obtain ⟨hWa, hWs, -⟩ := hW
  have h0 : wSum w m ∅ = Wt.const Z 0 := by
    funext Ω _ _ z
    simp [wSum, Wt.const]
  have hc : ∀ y : Ht q (sch.obj Z) n i, tr p (Wt.const Z 0) q n i y = 0 := by
    intro y
    have hs : Wt.smul 0 (Wt.const Z 0) = Wt.const Z 0 := by
      funext Ω _ _ z
      simp [Wt.smul, Wt.const]
    rw [← hs, hTs p 0 _ (isWt_zero p) hq y, zero_smul]
  have hins : ∀ (a : ι) (s : Finset ι), a ∉ s →
      wSum w m (insert a s) = (Wt.smul (m a) (w a)).add (wSum w m s) := by
    intro a s ha
    funext Ω _ _ z
    simp [wSum, Wt.add, Wt.smul, Finset.sum_insert ha]
  have key : ∀ s : Finset ι, IsWt p (wSum w m s) ∧
      ∀ y, tr p (wSum w m s) q n i y = ∑ a ∈ s, m a • tr p (w a) q n i y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [h0]
      exact ⟨isWt_zero p, fun y => by rw [hc y, Finset.sum_empty]⟩
    | insert a s ha ih =>
      rw [hins a s ha]
      have h1 := hWs p (m a) (w a) (hw a)
      refine ⟨hWa p _ _ h1 ih.1, fun y => ?_⟩
      rw [hTa p _ _ h1 ih.1 hq y, hTs p _ _ (hw a) hq y, ih.2 y, Finset.sum_insert ha]
  have hzero : wSum w m Finset.univ = Wt.const Z 0 :=
    hV p _ (key Finset.univ).1 D hD fun Ω _ _ z hz' => hz Ω z hz'
  rw [← (key Finset.univ).2 x, hzero, hc x]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtCrit_of :
    PtEx → WtCrit := by
  intro hPt Z S p w h A φ hφ
  choose N c hN hu hc using h A φ hφ
  refine ⟨c, ?_, fun Ω _ _ x => (hc (pt x) Ω x (hu (pt x))).symm⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨N u, hN u, hu u, fun u' hu' => ?_⟩
  obtain ⟨Ω, _, _, x, rfl⟩ := hPt A.U u'
  rw [← hc (pt x) Ω x (hu (pt x)), hc u Ω x hu']
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtLocal_of :
    WtCrit → WtLocal := by
  intro hcrit Z S p w hloc
  apply hcrit p w
  intro B φ hφ b
  obtain ⟨A, hAo, ⟨a, ha⟩, hA⟩ := hloc (B.u b)
  obtain ⟨W, f1, f2, hW, hf1, c0, hc0⟩ : ∃ (W : Scheme) (f1 : W ⟶ B.U) (f2 : W ⟶ A.U),
      IsPullback f1 f2 B.u A.u ∧ IsOpenImmersion f1 ∧ ∃ c0, f1 c0 = b := by
    obtain ⟨c0, hc0, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := B.u) (g := A.u) b a ha.symm
    exact ⟨_, _, _, IsPullback.of_hasPullback B.u A.u, inferInstance, c0, hc0⟩
  obtain ⟨V', q1, q2, hq⟩ : ∃ (V' : Scheme) (q1 : V' ⟶ A.V) (q2 : V' ⟶ W),
      IsPullback q1 q2 A.r f2 :=
    ⟨_, _, _, IsPullback.of_hasPullback A.r f2⟩
  have hcomm : (q1 ≫ A.v) ≫ p = (q2 ≫ f1) ≫ B.u := by
    simp only [Category.assoc]
    rw [A.pb.w, ← Category.assoc, hq.w, Category.assoc, hW.w]
  obtain ⟨g, hg1, hg2⟩ : ∃ g : V' ⟶ B.V, g ≫ B.v = q1 ≫ A.v ∧ g ≫ B.r = q2 ≫ f1 :=
    ⟨B.pb.lift _ _ hcomm, B.pb.lift_fst _ _ _, B.pb.lift_snd _ _ _⟩
  have hsq : IsPullback g q2 B.r f1 := by
    refine IsPullback.of_right ?_ hg2 B.pb
    rw [hg1, hW.w]
    exact hq.paste_horiz A.pb
  obtain ⟨ψ, hψ, hψs⟩ :=
    hA ⟨W, V', f2, q1, q2, hq⟩ (fun y => φ (g y)) (hφ.comp_continuous g.continuous)
  refine ⟨f1 '' {y | ψ y = ψ c0}, ψ c0, f1.isOpenEmbedding.isOpenMap _ (hψ.isOpen_fiber _),
    ⟨c0, rfl, hc0⟩, ?_⟩
  rintro Ω _ _ x ⟨y, hy, hyx⟩
  have hr : Set.range x ⊆ Set.range f1 := by
    rintro _ ⟨t, rfl⟩
    exact ⟨y, hyx.trans (pt_eq x t).symm⟩
  have hx' : IsOpenImmersion.lift f1 x hr ≫ f1 = x := IsOpenImmersion.lift_fac _ _ _
  have hpt : pt (IsOpenImmersion.lift f1 x hr) = y := by
    apply f1.isOpenEmbedding.injective
    rw [← pt_comp, hx', hyx]
  have hs := hψs Ω (IsOpenImmersion.lift f1 x hr)
  rw [hpt, show ψ y = ψ c0 from hy] at hs
  rw [hs]
  symm
  have hb := fib_bijOn hsq (IsOpenImmersion.lift f1 x hr)
  rw [hx'] at hb
  refine finsum_mem_eq_of_bijOn (fun z => z ≫ g) hb ?_
  intro z _
  simp only [Wt.comap, pt_comp, Category.assoc, hg1]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtNormal_of :
    NormAff → NwtGlue → WtNormal := by
  intro hAff hGlue Z S p _ hS
  have h : ∃ w, IsNwt p w := by
    refine hGlue p (fun s => ?_)
    obtain ⟨U, hU, hs, hd, hi⟩ := hS s
    obtain ⟨A, w, ho, hr, hw⟩ := hAff p U hU hd hi
    exact ⟨A, w, ho, by rw [hr]; exact hs, hw⟩
  unfold nwt
  rw [dite_eq_left h]
  exact h.choose_spec
end
