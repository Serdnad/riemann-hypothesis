module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.RingTheory.LocalRing.Length

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pt_map_ideal {Ω : Type} [Field Ω] {B : CommRingCat.{0}} (s : B ⟶ CommRingCat.of Ω) :
    (show PrimeSpectrum B from pt (Spec.map s)).asIdeal = RingHom.ker s.hom := by
  have h : (pt (Spec.map s) : Spec B) = PrimeSpectrum.comap s.hom (IsLocalRing.closedPoint Ω) := rfl
  change (pt (Spec.map s) : Spec B).asIdeal = _
  rw [h, RingHom.ker_eq_comap_bot]
  change Ideal.comap s.hom (IsLocalRing.maximalIdeal Ω) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]

private theorem exists_retract {Ω : Type} [Field Ω] [IsAlgClosed Ω] {B : CommRingCat.{0}} (φ : CommRingCat.of Ω ⟶ B)
    (hφ : φ.hom.IsIntegral) (q : Ideal B) [q.IsPrime] :
    ∃ s : B ⟶ CommRingCat.of Ω, φ ≫ s = 𝟙 _ ∧ RingHom.ker s.hom = q := by
  letI : Algebra Ω B := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral Ω B := ⟨hφ⟩
  have hb : Function.Bijective (algebraMap Ω (B ⧸ q)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : Ω ≃+* B ⧸ q := RingEquiv.ofBijective (algebraMap Ω (B ⧸ q)) hb
  refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp (Ideal.Quotient.mk q)), ?_, ?_⟩
  · ext a
    change e.symm (Ideal.Quotient.mk q (φ.hom a)) = a
    exact e.symm_apply_apply a
  · ext b
    change e.symm (Ideal.Quotient.mk q b) = 0 ↔ b ∈ q
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp

theorem UpperTheory.Gal.TranscendenceTraces.ptLift_of :
    PtLift := by
  intro V U r _ Ω _ _ x v hv
  obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := r) (g := x) v
    (IsLocalRing.closedPoint Ω) hv
  let P := pullback r x
  haveI : IsIntegralHom (pullback.snd r x) := inferInstance
  haveI : IsAffine P := isAffine_of_isAffineHom (pullback.snd r x)
  let φ : CommRingCat.of Ω ⟶ Γ(P, ⊤) := Spec.preimage (P.isoSpec.inv ≫ pullback.snd r x)
  have hφ' : Spec.map φ = P.isoSpec.inv ≫ pullback.snd r x := Spec.map_preimage _
  have hφ : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ']
    infer_instance
  let y : Spec Γ(P, ⊤) := P.isoSpec.hom t
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  obtain ⟨s, hs, hk⟩ := exists_retract φ hφ y.asIdeal
  refine ⟨Spec.map s ≫ P.isoSpec.inv ≫ pullback.fst r x, ?_, ?_⟩
  · have h1 : Spec.map s ≫ Spec.map φ = 𝟙 _ := by
      rw [← Spec.map_comp, hs, Spec.map_id]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv,
      ← hφ', ← Category.assoc, h1, Category.id_comp]
  · have hy : (pt (Spec.map s) : Spec Γ(P, ⊤)) = y :=
      PrimeSpectrum.ext ((pt_map_ideal s).trans hk)
    rw [← Category.assoc, pt_comp, pt_comp, hy]
    change (pullback.fst r x) (P.isoSpec.inv (P.isoSpec.hom t)) = v
    have h2 : P.isoSpec.inv (P.isoSpec.hom t) = t := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rw [h2, ht1]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem normal_affineOpen_integrallyClosed (S : Scheme.{0}) (hN : Nml S) (U : S.Opens) (hU : IsAffineOpen U)
    [IsDomain Γ(S, U)] : IsIntegrallyClosed Γ(S, U) := by
  refine IsIntegrallyClosed.of_localization_maximal ?_
  intro p _ _
  let y : PrimeSpectrum Γ(S, U) := ⟨p, inferInstance⟩
  have hmem : hU.fromSpec y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hU.fromSpec y, hmem⟩
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hU.fromSpec y)) p := hU.isLocalization_stalk' y hmem
  obtain ⟨_, hint⟩ := hN (hU.fromSpec y)
  haveI := hint
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.nmlInt_of :
    NmlInt := by
  intro S _ hN s
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨s, hs⟩⟩
  haveI : IsDomain Γ(S, U) := IsIntegral.component_integral U
  exact ⟨U, hU, hs, inferInstance, normal_affineOpen_integrallyClosed S hN U hU⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem trHl_id_apply (hHl : TrHl) (hL : TrLin) (hW : WtLin) (l : ℕ) [Fact l.Prime] (n i : ℤ) (S : Scheme.{0})
    (d : ℤ) (hu : IsUnit (l : Γ(S, ⊤))) (x : Hl l (sch.obj S) n i) :
    trHl l (𝟙 S) (Wt.const S d) n i x = d • x := by
  have hw : IsWt (𝟙 S) (Wt.const S d) := hW.2.2 (𝟙 S) d
  refine Subtype.ext (funext fun k => ?_)
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hu.pow k
  refine (hHl l n i (𝟙 S) _ hw hu x k).trans ?_
  exact (hL (l ^ k) n i).2.2 S d hq (x.1 k)

theorem UpperTheory.Gal.TranscendenceTraces.trIdQ_of :
    TrHl → TrLin → WtLin → TrIdQ := by
  intro hHl hL hW l _ n i S d hu
  unfold trHQ
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, trHl_id_apply hHl hL hW l n i S d hu m]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.tmul_smul]
    rw [Int.cast_smul_eq_zsmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trBC_of :
    TrChar → FamBC → WtBC → RpBasic → RpOp → TrBC := by
  intro hChar hFam hWbc hRp hOp q _ n i Z' S' Z S v p' p g _ w hpb hw hq x
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWbc v p' p g w hpb hw
  have hq' : IsUnit ((q : ℕ) : Γ(S', ⊤)) := by
    have := hq.map g.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hs, _⟩ := hChar q i p w hw hq
  obtain ⟨τ', hτ', hτeq⟩ := hFam q i v p' p g w hpb (trFam p w q i) hs
  rw [(hChar q i p w hw hq).2.2 _ hs n, (hChar q i p' _ hw' hq').2.2 τ' hτ' n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) _ Z n).1 x
  have h1 := hOp _ _ (trFam p w q i) n x a ha
  have h2 := (hRp (ZMod q) _ S n).2.2.2.1 S' g _ _ h1
  have h3 := (hRp (ZMod q) _ Z n).2.2.2.1 Z' v x a ha
  have h4 := hOp _ _ τ' n _ _ h3
  have h5 : Rp ((τ'.op n) ((cpull ((chains (ZMod q)).map (sch.map v)) (res (ZMod q) (tw q i)) n) x))
      (Sec.res g ((((trFam p w q i).deg n).app (Sq.self p)) a)) := by
    have e := hτeq n a
    exact e ▸ h4
  exact ((hRp (ZMod q) _ S' n).2.2.1 _ _ _ _ h2 h5).2.1 rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.normAff_of :
    Chart → NormSpec → NormAff := by
  intro hC hN Z S p _ U hU hD hI
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC p Γ(S, U) hU.fromSpec
  obtain ⟨w, hw⟩ := hN Γ(S, U) B
  exact ⟨⟨_, _, hU.fromSpec, v, _, hpb⟩, w, inferInstance, hU.range_fromSpec, hw⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trComp_of :
    TrChar → FamComp → WtComp → RpBasic → RpOp → TrComp := by
  intro hChar hFam hWc hRp hOp q _ n i W Z S r p _ _ w' w hr hp hq x
  have hrp : IsWt (r ≫ p) (Wt.mul r w' w) := hWc r p w' w hr hp
  have hqZ : IsUnit ((q : ℕ) : Γ(Z, ⊤)) := by
    have := hq.map p.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hsr, _⟩ := hChar q i r w' hr hqZ
  obtain ⟨_, hsp, _⟩ := hChar q i p w hp hq
  obtain ⟨σ, hσ, hσeq⟩ := hFam q i r p w' w (trFam r w' q i) (trFam p w q i) hsr hsp
  rw [(hChar q i (r ≫ p) _ hrp hq).2.2 σ hσ n, (hChar q i p w hp hq).2.2 _ hsp n,
    (hChar q i r w' hr hqZ).2.2 _ hsr n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) (res (ZMod q) (tw q i)) W n).1 x
  have h1 := hOp _ _ (trFam r w' q i) n x a ha
  have h2 := hOp _ _ (trFam p w q i) n _ _ h1
  have h3 := hOp _ _ σ n x a ha
  rw [hσeq n a] at h3
  exact ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h3 h2).2.1 rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtFlat_of :
    WtClopen → MultSum → MultBC → MultOpen → WtFlat := by
  intro hC hS hB hO Z S p _ _ _
  refine hC p (mult p) fun A W hW => ?_
  have : IsFinite A.r := A.finite
  have : Flat A.r := MorphismProperty.of_isPullback A.pb ‹_›
  have : LocallyOfFinitePresentation A.r := MorphismProperty.of_isPullback A.pb ‹_›
  let O : A.V.Opens := ⟨W, hW.isOpen⟩
  have : IsClosedImmersion O.ι :=
    IsClosedImmersion.of_isPreimmersion O.ι (by rw [O.range_ι]; exact hW.isClosed)
  have hm : mult (O.ι ≫ A.r) = (mult A.r).comap O.ι := hO O.ι A.r
  have hm' : mult A.r = (mult p).comap A.v := hB A.v A.r p A.u A.pb
  refine ⟨fun u => (((O.ι ≫ A.r).finrank u : ℕ) : ℤ), ?_, ?_⟩
  · exact (Scheme.Hom.isLocallyConstant_finrank (O.ι ≫ A.r)).comp _
  · intro Ω _ _ x
    have h1 := hS (O.ι ≫ A.r) Ω x
    refine h1.symm.trans ?_
    change ∑ᶠ z ∈ fib (O.ι ≫ A.r) x, mult (O.ι ≫ A.r) Ω z = _
    refine finsum_mem_eq_of_bijOn (fun z => z ≫ O.ι) ⟨?_, ?_, ?_⟩ ?_
    · intro z hz
      refine ⟨?_, ?_⟩
      · change (z ≫ O.ι) ≫ A.r = x
        rw [Category.assoc]; exact hz
      · change pt (z ≫ O.ι) ∈ W
        rw [pt_comp]; exact (pt z).2
    · intro z _ z' _ e
      exact (cancel_mono O.ι).1 e
    · rintro z ⟨hz, hzW⟩
      have hr : Set.range z ⊆ Set.range O.ι := by
        rw [O.range_ι]
        rintro _ ⟨t, rfl⟩
        rw [pt_eq]; exact hzW
      refine ⟨IsOpenImmersion.lift O.ι z hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩
      change _ ≫ O.ι ≫ A.r = x
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact hz
    · intro z _
      rw [hm, hm']
      simp [Wt.comap]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumComp_of :
    FibFin → SumComp := by
  intro hF W V U r p _ _ Ω _ x M _ c
  have hset : fib (r ≫ p) x = ⋃ y ∈ fib p x, fib r y := by
    ext z
    simp only [fib, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hz
      exact ⟨z ≫ r, by rw [Category.assoc]; exact hz, rfl⟩
    · rintro ⟨y, hy, hz⟩
      rw [← Category.assoc, hz, hy]
  have hdisj : (fib p x).PairwiseDisjoint (fun y => fib r y) := by
    intro y₁ _ y₂ _ hne
    refine Set.disjoint_left.mpr ?_
    intro z h₁ h₂
    apply hne
    simp only [fib, Set.mem_setOf_eq] at h₁ h₂
    rw [← h₁, ← h₂]
  change ∑ᶠ z ∈ fib (r ≫ p) x, c z = ∑ᶠ y ∈ fib p x, ∑ᶠ z ∈ fib r y, c z
  rw [hset]
  exact finsum_mem_biUnion hdisj (hF p Ω x) (fun y _ => hF r Ω y)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isOpenImmersion_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (s : Y ⟶ X) [Etale f] (h : s ≫ f = 𝟙 Y) :
    IsOpenImmersion s := by
  have hpb := pullback_lift_diagonal_isPullback s f
  have hgr := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb
    (inferInstance : IsOpenImmersion (pullback.diagonal f))
  have hsnd : IsOpenImmersion (pullback.snd (s ≫ f) f) := by
    have : IsIso (s ≫ f) := by rw [h]; infer_instance
    infer_instance
  have hs : s = pullback.lift (𝟙 Y) s (by simp [h]) ≫ pullback.snd (s ≫ f) f :=
    (pullback.lift_snd _ _ _).symm
  rw [hs]
  exact IsOpenImmersion.comp _ _

private theorem length_self_of_isField (R : Type) [CommRing R] (h : IsField R) : Module.length R R = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_self_iff_isUnit]
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  refine ⟨⟨a, b, hab⟩, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
  exact ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩

private theorem length_stalk_pt {V : Scheme.{0}} {Ω : Type} [Field Ω] (s : gp Ω ⟶ V) [IsOpenImmersion s] :
    Module.length (V.presheaf.stalk (pt s)) (V.presheaf.stalk (pt s)) = 1 := by
  have hK : IsField ((Spec (CommRingCat.of Ω)).presheaf.stalk (IsLocalRing.closedPoint Ω)) := by
    have e : (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω)) = genericPoint _ :=
      Subsingleton.elim _ _
    rw [e]
    exact (inferInstance : Field (Spec (CommRingCat.of Ω)).functionField).toIsField
  haveI := (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion s›).2 (IsLocalRing.closedPoint Ω)
  have hV : IsField (V.presheaf.stalk (pt s)) :=
    MulEquiv.isField hK (asIso (s.stalkMap (IsLocalRing.closedPoint Ω))).commRingCatIsoToRingEquiv.toMulEquiv
  exact length_self_of_isField _ hV

theorem UpperTheory.Gal.TranscendenceTraces.multEt_of :
    MultEt := by
  intro Z S p _
  funext Ω _ _ z
  change mult p Ω z = (1 : ℤ)
  have hσ : IsOpenImmersion (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p)) :=
    isOpenImmersion_of_section (pullback.snd p (z ≫ p)) _ (pullback.lift_snd _ _ _)
  have hl := length_stalk_pt (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p))
  simp only [mult]
  rw [hl]
  rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem fsum_single {α : Type*} (s : Set α) (f : α → ℤ) (a : α) (ha : a ∈ s)
    (h : ∀ x ∈ s, f x ≠ 0 → x = a) : ∑ᶠ x ∈ s, f x = f a := by
  classical
  rw [finsum_eq_single (fun x => ∑ᶠ (_ : x ∈ s), f x) a]
  · simp [ha]
  · intro x hx
    by_cases hs : x ∈ s
    · have h0 : f x = 0 := by
        by_contra h0
        exact hx (h x hs h0)
      simp [h0]
    · simp [hs]

private theorem discrete_of_chart (hChart : Chart) {V : Scheme.{0}} (Ω : Type) [Field Ω] (r : V ⟶ gp Ω) [IsFinite r] :
    DiscreteTopology V := by
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hChart r Ω (𝟙 _)
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  haveI : DiscreteTopology (Spec (CommRingCat.of B)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum B))
  exact (Scheme.homeoOfIso (asIso v)).symm.isEmbedding.discreteTopology

theorem UpperTheory.Gal.TranscendenceTraces.wtExt_of :
    PtOne → Chart → WtExt := by
  intro hOne hChart Z S p _ w hw Ω L _ _ _ _ z a
  classical
  haveI hr : IsFinite (pullback.snd p (z ≫ p)) := Sq.finite (Sq.of p (z ≫ p))
  haveI := discrete_of_chart hChart Ω (pullback.snd p (z ≫ p))
  let z0 : gp Ω ⟶ pullback p (z ≫ p) := pullback.lift z (𝟙 _) (by simp)
  have hf : z0 ≫ pullback.fst p (z ≫ p) = z := pullback.lift_fst _ _ _
  have hs : z0 ≫ pullback.snd p (z ≫ p) = 𝟙 _ := pullback.lift_snd _ _ _
  let φ : (pullback p (z ≫ p) : Scheme.{0}) → ℤ := fun y => if y = pt z0 then 1 else 0
  obtain ⟨ψ, -, hψ⟩ := hw (Sq.of p (z ≫ p)) φ (IsLocallyConstant.of_discrete φ)
  have h1 : ψ (pt (𝟙 (gp Ω))) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)),
      w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) := hψ Ω (𝟙 _)
  have h2 : ψ (pt a) = ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a,
      w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) := hψ L a
  have hpt : pt (a ≫ z0) = pt z0 := by rw [pt_comp, pt_eq]
  have hφ : φ (pt z0) = 1 := if_pos rfl
  have hne : ∀ y : (pullback p (z ≫ p) : Scheme.{0}), φ y ≠ 0 → y = pt z0 := by
    intro y hy
    by_contra h
    exact hy (if_neg h)
  have e1 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) (𝟙 (gp Ω)),
      w Ω (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w Ω z := by
    rw [fsum_single _ _ z0 hs, hf, hφ, mul_one]
    intro y hy h0
    exact hOne Ω (pullback.snd p (z ≫ p)) Ω (𝟙 _) y z0 hy hs (hne _ (right_ne_zero_of_mul h0))
  have hs' : (a ≫ z0) ≫ pullback.snd p (z ≫ p) = a := by
    rw [Category.assoc, hs, Category.comp_id]
  have e2 : ∑ᶠ y ∈ fib (pullback.snd p (z ≫ p)) a,
      w L (y ≫ pullback.fst p (z ≫ p)) * φ (pt y) = w L (a ≫ z) := by
    rw [fsum_single _ _ (a ≫ z0) hs', Category.assoc, hf, hpt, hφ, mul_one]
    intro y hy h0
    exact hOne Ω (pullback.snd p (z ≫ p)) L a y (a ≫ z0) hy hs'
      ((hne _ (right_ne_zero_of_mul h0)).trans hpt.symm)
  have hU : pt a = pt (𝟙 (gp Ω)) := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
  rw [← e2, ← e1, ← h2, ← h1]
  exact congrArg ψ hU
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_local (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [Algebra Ω R]
    [Module.Finite Ω R] [IsLocalRing R] : Module.length R R = Module.finrank Ω R := by
  have h1 := IsLocalRing.length_restrictScalars Ω R R
  have h2 : Module.length (IsLocalRing.ResidueField Ω) (IsLocalRing.ResidueField R) = 1 := by
    rw [← Module.length_eq_of_surjective (S := Ω) (M := IsLocalRing.ResidueField R)
      IsLocalRing.residue_surjective]
    haveI : Module.Finite Ω (IsLocalRing.ResidueField R) :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom Ω R (IsLocalRing.ResidueField R)).toLinearMap
        IsLocalRing.residue_surjective
    rw [Module.length_eq_finrank,
      Module.finrank_of_bijective_algebraMap IsAlgClosed.algebraMap_bijective_of_isIntegral]
    rfl
  rw [h2, mul_one, Module.length_eq_finrank] at h1
  exact h1.symm

theorem UpperTheory.Gal.TranscendenceTraces.artSum_of : ArtSum := by
  intro Ω B _ _ _ _ _
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  haveI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  have hbij := PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp
    (inferInstance : DiscreteTopology (PrimeSpectrum B))
  let e : B ≃ₗ[Ω] PrimeSpectrum.PiLocalization B :=
    LinearEquiv.ofBijective
      ((PrimeSpectrum.toPiLocalization B).restrictScalars Ω).toLinearMap hbij
  haveI : Module.Finite Ω (PrimeSpectrum.PiLocalization B) := Module.Finite.equiv e
  haveI : ∀ P : PrimeSpectrum B, Module.Finite Ω (Localization.AtPrime P.asIdeal) := fun P =>
    Module.Finite.of_surjective
      (LinearMap.proj (R := Ω) (φ := fun P : PrimeSpectrum B => Localization.AtPrime P.asIdeal) P)
      (fun x => ⟨Pi.single P x, by simp⟩)
  rw [finsum_eq_sum_of_fintype, e.finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [length_local Ω (Localization.AtPrime P.asIdeal)]
  rfl
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtDeg_of :
    WtNormal → WtDegConst → MultSum → MultBC → GenBasic → NwtDeg := by
  intro hN hD hMS hBC hG Z' Z S K _ v p' p g _ _ hpb hLoc hg
  obtain ⟨hW, hgen⟩ := hN p hLoc
  obtain ⟨d, hd⟩ := hD p (nwt p) hW
  rw [hd]
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  let Ω := AlgebraicClosure K
  let y : gp Ω ⟶ gp K := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have hval := congrArg (fun w : Wt S => w Ω (y ≫ g)) hd
  simp only [Wt.const] at hval
  have h1 : Wt.push p (nwt p) Ω (y ≫ g) = Wt.push p (mult p) Ω (y ≫ g) := by
    simp only [Wt.push]
    apply finsum_congr
    intro z
    apply finsum_congr
    intro hz
    apply hgen
    have hz' : z ≫ p = y ≫ g := hz
    rw [hz', pt_comp, Subsingleton.elim (pt y) (IsLocalRing.closedPoint K)]
    exact (hG.2.2 S _).mpr hg
  have h2 : Wt.push p (mult p) Ω (y ≫ g) = Wt.push p' (mult p') Ω y := by
    simp only [Wt.push]
    symm
    rw [finsum_mem_eq_of_bijOn (fun z => z ≫ v) (fib_bijOn hpb y)
      (g := fun z => mult p Ω z)]
    intro z _
    rw [hBC v p' p g hpb]
    rfl
  have h3 := hMS p' Ω y
  have h4 : pt y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  rw [h1, h2, h3, h4] at hval
  rw [hval]
end
