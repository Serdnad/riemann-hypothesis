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

private theorem isLC_sum {X ι : Type*} [TopologicalSpace X] (s : Finset ι) (f : ι → X → ℤ)
    (h : ∀ j, IsLocallyConstant (f j)) : IsLocallyConstant (fun t => ∑ j ∈ s, f j t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

private theorem key {T Z S : Scheme.{0}} {p : Z ⟶ S} {π : T ⟶ S} {ι : Type} [Fintype ι] [IsFinite p]
    (hFib : FibFin) (σ : ι → (T ⟶ Z)) (m : ι → ℤ) (w : Wt Z) (hC : Counts p π σ m w) (A : Sq p)
    (φ : A.V → ℤ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] {U1 : Scheme.{0}} (f : U1 ⟶ T) (g : U1 ⟶ A.U)
    (hfg : f ≫ π = g ≫ A.u) (τ : ι → (U1 ⟶ A.V)) (hτv : ∀ j, τ j ≫ A.v = f ≫ σ j)
    (hτr : ∀ j, τ j ≫ A.r = g) (x1 : gp Ω ⟶ U1) :
    ∑ j, m j * φ (τ j (pt x1)) = ∑ᶠ z ∈ fib A.r (x1 ≫ g), w Ω (z ≫ A.v) * φ (pt z) := by
  classical
  haveI : IsFinite A.r := A.finite
  have hfin := hFib A.r Ω (x1 ≫ g)
  have hmem : ∀ j, x1 ≫ τ j ∈ fib A.r (x1 ≫ g) := fun j => by
    show (x1 ≫ τ j) ≫ A.r = x1 ≫ g
    rw [Category.assoc, hτr]
  have hiff : ∀ z ∈ fib A.r (x1 ≫ g), ∀ j, (x1 ≫ f) ≫ σ j = z ≫ A.v ↔ x1 ≫ τ j = z := by
    intro z hz j
    have hz' : z ≫ A.r = x1 ≫ g := hz
    constructor
    · intro h
      apply A.pb.hom_ext
      · rw [Category.assoc, hτv, ← Category.assoc, h]
      · rw [Category.assoc, hτr, hz']
    · intro h
      rw [← h, Category.assoc, Category.assoc, hτv]
  have hw : ∀ z ∈ fib A.r (x1 ≫ g),
      w Ω (z ≫ A.v) = ∑ j, if x1 ≫ τ j = z then m j else 0 := by
    intro z hz
    have hz' : z ≫ A.r = x1 ≫ g := hz
    have hsq : (z ≫ A.v) ≫ p = (x1 ≫ f) ≫ π := by
      rw [Category.assoc, A.pb.w, ← Category.assoc, hz', Category.assoc, ← hfg, Category.assoc]
    rw [hC Ω (x1 ≫ f) (z ≫ A.v) hsq, finsum_mem_def, finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : x1 ≫ τ j = z
    · rw [Set.indicator_of_mem
        (show j ∈ {j | (x1 ≫ f) ≫ σ j = z ≫ A.v} from (hiff z hz j).mpr h) m, if_pos h]
    · rw [Set.indicator_of_notMem
        (show j ∉ {j | (x1 ≫ f) ≫ σ j = z ≫ A.v} from fun h' => h ((hiff z hz j).mp h')) m,
        if_neg h]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Finset.sum_congr rfl
    (g := fun z => (∑ j, if x1 ≫ τ j = z then m j else 0) * φ (pt z))
    (fun z hz => by rw [hw z (hfin.mem_toFinset.mp hz)])]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hfin.mem_toFinset.mpr (hmem j)), pt_comp]

theorem UpperTheory.Gal.TranscendenceTraces.countWt_of :
    PtEx → PtLift → FibFin → CountWt := by
  intro hPE hPL hFib T Z S p π _ _ _ ι _ σ m w hσ hC
  classical
  haveI := Fintype.ofFinite ι
  intro A φ hφ
  let f : pullback π A.u ⟶ T := pullback.fst π A.u
  let g : pullback π A.u ⟶ A.U := pullback.snd π A.u
  have hfg : f ≫ π = g ≫ A.u := pullback.condition
  have hpb1 : IsPullback f g π A.u := IsPullback.of_hasPullback π A.u
  haveI : Surjective g := MorphismProperty.of_isPullback (P := @Surjective) hpb1 inferInstance
  haveI : IsIntegralHom g :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom) hpb1 inferInstance
  let τ : ι → (pullback π A.u ⟶ A.V) := fun j =>
    A.pb.lift (f ≫ σ j) g (by rw [Category.assoc, hσ j, hfg])
  have hτv : ∀ j, τ j ≫ A.v = f ≫ σ j := fun j => A.pb.lift_fst _ _ _
  have hτr : ∀ j, τ j ≫ A.r = g := fun j => A.pb.lift_snd _ _ _
  let χ : ↥(pullback π A.u) → ℤ := fun t => ∑ j, m j * φ (τ j t)
  have hχ : IsLocallyConstant χ :=
    isLC_sum Finset.univ (fun j t => m j * φ (τ j t))
      (fun j => (hφ.comp_continuous (τ j).continuous).comp (fun a => m j * a))
  have hconst : ∀ t1 t2, g t1 = g t2 → χ t1 = χ t2 := by
    intro t1 t2 h
    obtain ⟨Ω, hF, hA, x1, hx1⟩ := hPE _ t1
    letI := hF
    haveI := hA
    obtain ⟨z, hz, hzt⟩ := hPL g Ω (x1 ≫ g) t2 (by rw [pt_comp, hx1, h])
    have k1 := key hFib σ m w hC A φ Ω f g hfg τ hτv hτr x1
    have k2 := key hFib σ m w hC A φ Ω f g hfg τ hτv hτr z
    rw [hz] at k2
    show ∑ j, m j * φ (τ j t1) = ∑ j, m j * φ (τ j t2)
    rw [← hx1, ← hzt, k1, k2]
  have hsurj : Function.Surjective g := g.surjective
  let ψ : A.U → ℤ := fun s => χ (Function.surjInv hsurj s)
  have hψg : ∀ t, ψ (g t) = χ t := fun t => hconst _ _ (Function.surjInv_eq hsurj _)
  refine ⟨ψ, ?_, ?_⟩
  · have hq : Topology.IsQuotientMap g := g.isClosedMap.isQuotientMap g.continuous hsurj
    intro s
    rw [← hq.isOpen_preimage]
    have hpre : g ⁻¹' (ψ ⁻¹' s) = χ ⁻¹' s := by
      ext t
      simp only [Set.mem_preimage, hψg]
    rw [hpre]
    exact hχ s
  · intro Ω _ _ x
    obtain ⟨t, ht⟩ := hsurj (pt x)
    obtain ⟨z, hz, _⟩ := hPL g Ω x t ht
    rw [← hz, pt_comp, hψg]
    exact key hFib σ m w hC A φ Ω f g hfg τ hτv hτr z
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isLocallyConstant_weighted_sum {X : Type*} [TopologicalSpace X] (T : Finset ℤ) (f : ℤ → X → ℤ)
    (hf : ∀ c, IsLocallyConstant (f c)) : IsLocallyConstant (fun y => ∑ c ∈ T, c * f c y) := by
  have h : ∀ c, Continuous (f c) := fun c => (IsLocallyConstant.iff_continuous _).1 (hf c)
  exact (IsLocallyConstant.iff_continuous _).2
    (continuous_finsetSum _ fun c _ => continuous_const.mul (h c))

theorem UpperTheory.Gal.TranscendenceTraces.wtClopen_of :
    WtCrit → FibFin → WtClopen := by
  intro hcrit hfin Z S p _ w hcl
  apply hcrit p w
  intro A φ hφ u
  have hφc : Continuous φ := (IsLocallyConstant.iff_continuous φ).1 hφ
  haveI := A.finite
  obtain ⟨U0, hU0, hu, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 A.U.isBasis_affineOpens)
    (show u ∈ (⊤ : A.U.Opens) from trivial)
  have hK : IsCompact (A.r ⁻¹' (U0 : Set A.U)) :=
    QuasiCompact.isCompact_preimage _ U0.isOpen (IsAffineOpen.isCompact hU0)
  let T : Finset ℤ := ((hK.image hφc).finite_of_discrete).toFinset
  choose ψ hψ hψs using fun c : ℤ => hcl A (φ ⁻¹' {c}) (hφ.isClopen_fiber c)
  let Ψ : A.U → ℤ := fun y => ∑ c ∈ T, c * ψ c y
  have hΨ : IsLocallyConstant Ψ := isLocallyConstant_weighted_sum T ψ hψ
  refine ⟨(U0 : Set A.U) ∩ {y | Ψ y = Ψ u}, Ψ u, U0.isOpen.inter (hΨ.isOpen_fiber _),
    ⟨hu, rfl⟩, ?_⟩
  rintro Ω _ _ x ⟨hx0, hxΨ⟩
  rw [← show Ψ (pt x) = Ψ u from hxΨ]
  have hF := hfin A.r Ω x
  classical
  have key : ∀ c, ψ c (pt x) =
      ∑ z ∈ hF.toFinset, if φ (pt z) = c then w Ω (z ≫ A.v) else 0 := by
    intro c
    rw [hψs c Ω x, finsum_mem_eq_finite_toFinset_sum _ (hF.inter_of_left _), ← Finset.sum_filter]
    congr 1
    ext z
    simp
  simp only [Ψ, key, Finset.mul_sum]
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hzf : z ≫ A.r = x := (Set.Finite.mem_toFinset hF).1 hz
  have hmem : φ (pt z) ∈ T := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨pt z, ?_, rfl⟩
    show A.r (pt z) ∈ (U0 : Set A.U)
    rw [← pt_comp, hzf]
    exact hx0
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos hmem, mul_comm]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrEq_of :
    ImageFin → TrRel → TrPush → WtPush → CorrEq := by
  intro hIF hTR hTP hWP q _ n i S Y B bS bY _ _ ι _ c m hc hq D hD hcyc y
  obtain ⟨G, pG, fG, h, hpG, hh, hp, hf, hmono⟩ :=
    hIF bS bY ι (fun a => (c a).Z) (fun a => (c a).p) (fun a => (c a).f) (fun a => (c a).fin) hc
  haveI := hpG
  have hwt : ∀ a, IsWt (h a ≫ pG) (c a).w := by
    intro a
    rw [hp a]
    exact (c a).wt
  have key : ∀ a, (c a).op q n i y =
      tr pG (Wt.push (h a) (c a).w) q n i (pull (ZMod q) (sch.map fG) (tw q i) n y) := by
    intro a
    haveI := hh a
    rw [← hTP q n i (h a) pG (c a).w (hwt a) hq, ← pull_comp, ← Functor.map_comp, hf a]
    simp only [Corr.op, AddMonoidHom.comp_apply]
    rw [hp a]
  simp only [key]
  refine hTR q n i pG ι (fun a => Wt.push (h a) (c a).w) m
    (fun a => by haveI := hh a; exact hWP (h a) pG (c a).w (hwt a)) hq D hD ?_ _
  intro Ω _ _ z hz
  rw [← hcyc Ω (z ≫ pG) (z ≫ fG) hz]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hs : fib (h a) z = {z' | z' ≫ (c a).p = z ≫ pG ∧ z' ≫ (c a).f = z ≫ fG} := by
    ext z'
    simp only [fib, Set.mem_setOf_eq]
    constructor
    · rintro rfl
      exact ⟨by rw [Category.assoc, hp a], by rw [Category.assoc, hf a]⟩
    · rintro ⟨h1, h2⟩
      apply hmono
      · rw [Category.assoc, hp a, h1]
      · rw [Category.assoc, hf a, h2]
  simp only [Wt.push, Corr.cyc]
  rw [hs]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

noncomputable section

private def famAdd {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ τ' : Fam p I J) : Fam p I J where
  deg s := ⟨fun A => (τ.deg s).app A + (τ'.deg s).app A, fun t a => by
    simp only [AddMonoidHom.add_apply]
    rw [← (τ.deg s).nat t a, ← (τ'.deg s).nat t a]
    exact map_add _ _ _⟩
  comm A s t a := by
    simp only [AddMonoidHom.add_apply]
    rw [← τ.comm, ← τ'.comm]
    exact map_add _ _ _

private def famSmul {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (d : ℤ) (τ : Fam p I J) : Fam p I J where
  deg s := ⟨fun A => d • (τ.deg s).app A, fun t a => by
    simp only [AddMonoidHom.smul_apply]
    rw [← (τ.deg s).nat t a]
    exact map_zsmul _ _ _⟩
  comm A s t a := by
    simp only [AddMonoidHom.smul_apply]
    rw [← τ.comm]
    exact map_zsmul _ _ _

private theorem isIso_r {S : Scheme.{0}} (A : Sq (𝟙 S)) : IsIso A.r := A.pb.isIso_snd_of_isIso

private def resInv {S : Scheme.{0}} {R : Type} [CommRing R] (F : Shv R) (A : Sq (𝟙 S)) : Sec F A.V →+ Sec F A.U :=
  haveI := isIso_r A
  AddMonoidHom.mk' (fun a => Sec.res (inv A.r) a) (fun a b => map_add _ _ _)

private theorem resInv_apply {S : Scheme.{0}} {R : Type} [CommRing R] (F : Shv R) (A : Sq (𝟙 S)) [IsIso A.r] (a : Sec F A.V) :
    resInv F A a = Sec.res (inv A.r) a := rfl

private def famId (S : Scheme.{0}) {R : Type} [CommRing R] (I : Cx R) (d : ℤ) : Fam (𝟙 S) I I where
  deg s := ⟨fun A => d • resInv (I.X s) A, fun {A B} t a => by
    haveI := isIso_r A
    haveI := isIso_r B
    simp only [AddMonoidHom.smul_apply, resInv_apply]
    have e : t.g ≫ inv B.r = inv A.r ≫ t.k := by
      rw [IsIso.comp_inv_eq, Category.assoc, t.hr, IsIso.inv_hom_id_assoc]
    rw [show Sec.res t.g (d • Sec.res (inv B.r) a) = d • Sec.res t.g (Sec.res (inv B.r) a) from map_zsmul _ _ _,
      res_res, res_res, e]⟩
  comm A s t a := by
    haveI := isIso_r A
    simp only [AddMonoidHom.smul_apply, resInv_apply]
    rw [show Sec.map (I.d s t) (d • Sec.res (inv A.r) a) = d • Sec.map (I.d s t) (Sec.res (inv A.r) a) from map_zsmul _ _ _,
      map_res]

theorem UpperTheory.Gal.TranscendenceTraces.famLin_of :
    FibFin → FamLin := by
  intro hF q i
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' τ τ' hτ hτ'
    refine ⟨famAdd τ τ', fun A a => ?_, fun n A a => rfl⟩
    obtain ⟨b, hb, hs⟩ := hτ A a
    obtain ⟨b', hb', hs'⟩ := hτ' A a
    refine ⟨b + b', ?_, fun Ω _ _ x => ?_⟩
    · change (τ.deg 0).app A _ + (τ'.deg 0).app A _ = _
      rw [hb, hb']
      exact (map_add _ _ _).symm
    · haveI := Sq.finite A
      have hfin := hF A.r Ω x
      rw [show Sec.res x (b + b') = Sec.res x b + Sec.res x b' from map_add _ _ _, hs Ω x, hs' Ω x,
        ← finsum_mem_add_distrib hfin]
      refine finsum_mem_congr rfl fun z _ => ?_
      simp only [Wt.add, add_smul]
  · intro Z S p _ d w τ hτ
    refine ⟨famSmul d τ, fun A a => ?_, fun n A a => rfl⟩
    obtain ⟨b, hb, hs⟩ := hτ A a
    refine ⟨d • b, ?_, fun Ω _ _ x => ?_⟩
    · change d • (τ.deg 0).app A _ = _
      rw [hb]
      exact (map_zsmul _ _ _).symm
    · haveI := Sq.finite A
      have hfin := hF A.r Ω x
      rw [show Sec.res x (d • b) = d • Sec.res x b from map_zsmul _ _ _, hs Ω x]
      have := (zsmulAddGroupHom (α := Sec (tw q i) (gp Ω)) d).map_finsum_mem
        (fun z => w Ω (z ≫ A.v) • Sec.res z a) hfin
      refine this.trans ?_
      refine finsum_mem_congr rfl fun z _ => ?_
      simp only [Wt.smul, mul_smul, zsmulAddGroupHom_apply]
  · intro S d
    refine ⟨famId S _ d, fun A a => ?_, fun n a => ?_⟩
    · haveI := isIso_r A
      refine ⟨d • Sec.res (inv A.r) a, ?_, fun Ω _ _ x => ?_⟩
      · change d • resInv ((res _ (tw q i)).X 0) A (Sec.map (resι _ (tw q i)) a) = _
        rw [resInv_apply, ← map_res]
        exact (map_zsmul _ _ _).symm
      · have hf : fib A.r x = {x ≫ inv A.r} := by
          ext z
          simp only [fib, Set.mem_setOf_eq, Set.mem_singleton_iff]
          rw [IsIso.eq_comp_inv]
        rw [hf, finsum_mem_singleton]
        rw [show Sec.res x (d • Sec.res (inv A.r) a) = d • Sec.res x (Sec.res (inv A.r) a) from map_zsmul _ _ _, res_res]
        rfl
    · change d • resInv ((res _ (tw q i)).X n) (Sq.self (𝟙 S)) a = _
      haveI := isIso_r (Sq.self (𝟙 S))
      rw [resInv_apply]
      have e : inv (Sq.self (𝟙 S)).r = 𝟙 _ := IsIso.inv_id
      rw [e]
      exact congrArg (d • ·) (res_id a)

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.normSpec_of :
    SplitCover → CountEx → CountWt → MultPt → PtEx → PtLift → GenBasic → NormSpec := by
  intro hS hCE hCW hMP hPE hPL _
  unfold NormSpec
  intro A B _ _ _ _ _ _
  set p := Spec.map (CommRingCat.ofHom (algebraMap A B)) with hp
  haveI : IsFinite p := by
    rw [hp, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨T, π, ι, σ, c, hπi, hπs, hι, hσ, hsym, hgen⟩ := hS A B
  haveI := hπi
  haveI := hπs
  haveI := hι
  have hk : ∀ s : ↥(Spec (CommRingCat.of B)), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (y : gp Ω ⟶ Spec (CommRingCat.of B)), pt y = s := fun s => hPE _ s
  choose Ωk fk ak yk hyk using hk
  let key : ↥(Spec (CommRingCat.of B)) → ℤ := fun s => letI := fk s; letI := ak s; mult p (Ωk s) (yk s)
  let m : ι → ℤ := fun j => key (c j)
  have hm : ∀ j (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Spec (CommRingCat.of B)),
      c j = pt z → m j = mult p Ω z := by
    intro j Ω _ _ z hz
    letI := fk (c j)
    letI := ak (c j)
    exact hMP p (Ωk (c j)) Ω (yk (c j)) z ((hyk (c j)).trans hz)
  have hSy : UpperTheory.Gal.TranscendenceTraces.Sym π σ m := by
    unfold UpperTheory.Gal.TranscendenceTraces.Sym
    intro Ω _ _ x x' hxx'
    obtain ⟨e, he⟩ := hsym Ω x x' hxx'
    exact ⟨e, fun j => ⟨(he j).1, congrArg key (he j).2⟩⟩
  obtain ⟨w, hw⟩ := hCE p π σ m hSy
  refine ⟨w, hCW p π σ m w hσ hw, ?_⟩
  intro Ω _ _ z hz
  obtain ⟨v, hv⟩ := π.surjective (pt (z ≫ p))
  obtain ⟨x, hx, -⟩ := hPL π Ω (z ≫ p) v hv
  have hcount := hw Ω x z hx.symm
  have hbot : (pt (x ≫ π)).asIdeal = ⊥ := by
    rw [hx]
    unfold GenPt at hz
    have h0 := hz (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)
    rw [← h0]
  obtain ⟨⟨j0, hj0, huniq⟩, hcj⟩ := hgen Ω x z hx.symm hbot
  have hset : {j | x ≫ σ j = z} = {j0} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact huniq j
    · rintro rfl
      exact hj0
  rw [hcount, hset, finsum_mem_singleton]
  exact hm j0 Ω z (hcj j0 hj0)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtAgree_of :
    NwtOpen → WtUnique → GenBasic → MultBC → NwtAgree := by
  intro hOpen hUniq hGen _ Z S p _ A B _ _ w w' hw hw' Ω _ _ z z' hz
  have hc : pullback.fst A.u B.u ≫ A.u = pullback.snd A.u B.u ≫ B.u := pullback.condition
  have hP : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.fst A.u B.u ≫ A.u) :=
    IsPullback.of_hasPullback _ _
  have hP' : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.snd A.u B.u ≫ B.u) := by
    rw [← hc]
    exact hP
  have eA : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.fst A.u B.u) ≫ A.u := by
    rw [Category.assoc]
    exact hP.w
  have eB : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.snd A.u B.u) ≫ B.u := by
    rw [Category.assoc]
    exact hP'.w
  let C : Sq A.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.fst A.u B.u,
    A.pb.lift _ _ eA, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [A.pb.lift_fst]; exact hP) (A.pb.lift_snd _ _ _) A.pb⟩
  let C' : Sq B.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.snd A.u B.u,
    B.pb.lift _ _ eB, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [B.pb.lift_fst]; exact hP') (B.pb.lift_snd _ _ _) B.pb⟩
  haveI : IsOpenImmersion C.u := inferInstanceAs (IsOpenImmersion (pullback.fst A.u B.u))
  haveI : IsOpenImmersion C'.u := inferInstanceAs (IsOpenImmersion (pullback.snd A.u B.u))
  have h1 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w.comap C.v) := hOpen A.r w C hw
  have h2 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w'.comap C'.v) := hOpen B.r w' C' hw'
  haveI : IsFinite (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) := MorphismProperty.of_isPullback hP ‹_›
  have hE : w.comap C.v = w'.comap C'.v :=
    hUniq _ _ _ h1.1 h2.1 {s | GenPt s} (hGen.1 _) fun Ω _ _ y hy => by
      rw [h1.2 Ω y hy, h2.2 Ω y hy]
  have e1 : (z ≫ A.r) ≫ A.u = (z' ≫ B.r) ≫ B.u := by
    rw [Category.assoc, Category.assoc, ← A.pb.w, ← B.pb.w, ← Category.assoc, ← Category.assoc, hz]
  have e2 : (z ≫ A.v) ≫ p = pullback.lift (z ≫ A.r) (z' ≫ B.r) e1 ≫ pullback.fst A.u B.u ≫ A.u := by
    rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, A.pb.w]
  let z0 : gp Ω ⟶ pullback p (pullback.fst A.u B.u ≫ A.u) :=
    pullback.lift (z ≫ A.v) (pullback.lift (z ≫ A.r) (z' ≫ B.r) e1) e2
  have hz0 : z0 ≫ C.v = z := by
    apply A.pb.hom_ext
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.v = _
      rw [Category.assoc, A.pb.lift_fst]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.r = _
      rw [Category.assoc, A.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst]
  have hz0' : z0 ≫ C'.v = z' := by
    apply B.pb.hom_ext
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.v = _
      rw [Category.assoc, B.pb.lift_fst, ← hz]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.r = _
      rw [Category.assoc, B.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
  have := congrFun (congrFun (congrFun (congrFun hE Ω) ‹_›) ‹_›) z0
  simpa only [Wt.comap, hz0, hz0'] using this
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtFlat_of :
    WtBC → WtFlat → WtUnique → MultBC → NwtFlat := by
  intro hBC hFlat hUniq hMBC Z' S' Z S v p' p g _ _ _ pb hN hD
  haveI : IsFinite p' := MorphismProperty.of_isPullback pb ‹_›
  refine hUniq p' _ _ (hBC v p' p g _ pb hN.1) (hFlat p') _ hD ?_
  intro Ω _ _ z hz
  rw [hMBC v p' p g pb]
  refine hN.2 Ω (z ≫ v) ?_
  have e : (z ≫ v) ≫ p = (z ≫ p') ≫ g := by
    rw [Category.assoc, pb.w, Category.assoc]
  rw [e, pt_comp]
  exact hz
end
