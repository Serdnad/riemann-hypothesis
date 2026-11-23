module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle001
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

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem bc_isPullback {B B' Z Y : Scheme.{0}} (g : B ⟶ B') (p : Z ⟶ B') (s : Y ⟶ Z) :
    IsPullback (pullback.fst (s ≫ p) g) (bcMap g s rfl) s (pullback.fst p g) := by
  refine IsPullback.of_bot ?_ (bcMap_fst g s rfl).symm (IsPullback.of_hasPullback p g)
  rw [bcMap_snd]
  exact IsPullback.of_hasPullback (s ≫ p) g

theorem UpperTheory.Gal.G3.pBcSplits :
    SplitsBasic → BcSplits := by
  intro hb B B' Z Y W g p q r s hs c hc J _ σ hσ _ _
  subst hs
  subst hc
  have sq := bc_isPullback g p s
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›,
    MorphismProperty.of_isPullback (P := @Etale) sq ‹_›, fun h => ?_⟩
  obtain ⟨h0, -⟩ := id h
  have hcomp : ∀ j, bcMap g (σ j) (hσ j) ≫ bcMap g s rfl = bcMap g c rfl := by
    intro j
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst g s rfl, ← Category.assoc, bcMap_fst g (σ j) (hσ j), Category.assoc, h0 j,
        bcMap_fst g c rfl]
    · rw [Category.assoc, bcMap_snd g s rfl, bcMap_snd g (σ j) (hσ j), bcMap_snd g c rfl]
  have e1 : bcMap g c rfl ≫ pullback.fst p g = pullback.fst (c ≫ p) g ≫ c := bcMap_fst g c rfl
  have e2 : (fun j => bcMap g (σ j) (hσ j) ≫ pullback.fst (s ≫ p) g) = fun j => pullback.fst (c ≫ p) g ≫ σ j :=
    funext fun j => bcMap_fst g (σ j) (hσ j)
  have h2 : Splits s (bcMap g c rfl ≫ pullback.fst p g)
      (fun j => bcMap g (σ j) (hσ j) ≫ pullback.fst (s ≫ p) g) := by
    rw [e1, e2]
    exact hb.1 s c J σ (pullback.fst (c ≫ p) g) h
  exact (hb.2 (pullback.fst (s ≫ p) g) (bcMap g s rfl) s (pullback.fst p g) sq (bcMap g c rfl) J
    (fun j => bcMap g (σ j) (hσ j)) hcomp).2 h2
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.GalV

namespace UpperTheory.Gal.G3

private theorem splits_restrict (hS : SplitsPts) (hP : PtsOfSplits) {Z Y W W' : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s]
    (c : W ⟶ Z) (J : Type) [Finite J] (σ : J → (W ⟶ Y)) (g : W' ⟶ W) (h : Splits s c σ) :
    Splits s (g ≫ c) fun j => g ≫ σ j := by
  have h0 := h
  obtain ⟨hc, -⟩ := h
  refine hS s (g ≫ c) J (fun j => g ≫ σ j) (fun j => by simp [hc j]) ?_
  intro Ω _ _ x y hy
  have hy' : y ≫ s = (x ≫ g) ≫ c := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s c J σ h0 Ω (x ≫ g) y hy'
  exact ⟨j, by simpa using hj, fun i hi => huniq i (by simpa using hi)⟩

private theorem splits_down (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s' c σ) : Splits s (c ≫ g) fun j => σ j ≫ v := by
  refine hS s (c ≫ g) J (fun j => σ j ≫ v)
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, hσ j]) ?_
  intro Ω _ _ x y hy
  have hw : y ≫ s = (x ≫ c) ≫ g := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s' c J σ h Ω x (sq.lift y (x ≫ c) hw) (by simp)
  refine ⟨j, ?_, ?_⟩
  · simp only
    rw [← Category.assoc, hj, sq.lift_fst]
  · intro i hi
    apply huniq
    apply sq.hom_ext
    · simpa using hi
    · simp [hσ i]

private theorem splits_up (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s (c ≫ g) fun j => σ j ≫ v) : Splits s' c σ := by
  have : IsFinite s' := MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›
  have : Etale s' := MorphismProperty.of_isPullback (P := @Etale) sq ‹_›
  refine hS s' c J σ hσ ?_
  intro Ω _ _ x y hy
  have hw : (y ≫ v) ≫ s = x ≫ c ≫ g := by
    rw [Category.assoc, sq.w, ← Category.assoc, hy, Category.assoc]
  obtain ⟨j, hj, huniq⟩ := hP s (c ≫ g) J (fun j => σ j ≫ v) h Ω x (y ≫ v) hw
  refine ⟨j, ?_, ?_⟩
  · apply sq.hom_ext
    · simpa using hj
    · simp [hσ j, hy]
  · intro i hi
    apply huniq
    rw [← Category.assoc, hi]

theorem pSplitsBasic : SplitsPts → PtsOfSplits → SplitsBasic := fun hS hP =>
  ⟨fun s _ _ c J _ σ g h => splits_restrict hS hP s c J σ g h,
   fun _ _ _ _ _ _ sq c J _ σ hσ => ⟨splits_down hS hP sq c J σ hσ, splits_up hS hP sq c J σ hσ⟩⟩

end UpperTheory.Gal.G3

end
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

namespace UpperTheory.Gal.G3

private theorem isUnit_natCast_sp (l : ℕ) (hl : l ≠ 0) (Ω : Type) [Field Ω] [CharZero Ω] :
    IsUnit ((l : Γ(sp Ω, ⊤))) := by
  have h : IsUnit ((l : Ω)) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hl)
  have h2 := h.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using h2

private theorem th_pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}} {p : X ⟶ B}
    {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) : T.pull f h = T.pull f' h' := by
  subst e; rfl

private theorem bcMap_comp' {B B' X Y Z : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : Z ⟶ B'} (u : Z ⟶ Y)
    (f : Y ⟶ X) (hu : u ≫ q = r) (hf : f ≫ p = q) (h : (u ≫ f) ≫ p = r) :
    bcMap g u hu ≫ bcMap g f hf = bcMap g (u ≫ f) h := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, bcMap_fst, Category.assoc]
  · rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]

private theorem lmap_of_key {R : Type*} [Semiring R] {M N P : ℤ → Type*} [∀ m, AddCommMonoid (M m)]
    [∀ m, AddCommMonoid (N m)] [∀ m, AddCommMonoid (P m)] [∀ m, Module R (M m)] [∀ m, Module R (N m)]
    [∀ m, Module R (P m)] (T : ∀ m, M m →ₗ[R] N m) (C : ∀ m, N m →ₗ[R] P m) {I : Type*} [Fintype I]
    (S : I → ∀ m, M m →ₗ[R] P m) (h : ∀ m x, C m (T m x) = ∑ i, S i m x) (x : DirectSum ℤ M) :
    DirectSum.lmap C (DirectSum.lmap T x) = ∑ i, DirectSum.lmap (S i) x := by
  apply DFinsupp.ext
  intro m
  have hs : ∀ s : Finset I, (∑ i ∈ s, DirectSum.lmap (S i) x) m = ∑ i ∈ s, S i m (x m) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, DirectSum.add_apply, ih, DirectSum.lmap_apply]
  rw [hs, DirectSum.lmap_apply, DirectSum.lmap_apply]
  exact h m (x m)

private theorem coverCore (hE : EtnGood) (hS : BcSplits) (hG : BcGal) (hU : CorrUniq) (l : ℕ) [Fact l.Prime]
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [CharZero Ω] (H : HTower k) (g : H.Γ) [IsFinite (H.s g)] [Etale (H.s g)]
    (W : Scheme.{0}) (c : W ⟶ H.Z) (G : Type) [Group G] [Finite G] (a : G → (W ⟶ W)) (I : Type) [Fintype I]
    (σ : I → (W ⟶ H.Y g)) (hσ : ∀ i, (σ i ≫ H.t g) ≫ H.q = c ≫ H.q) (hGal : IsGalois c G a) (hSp : Splits (H.s g) c σ)
    (hEx : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T) :
    ∃ Tm : ∀ m : ℤ, HQ l (sch.obj (H.geomZ Ω)) m 0 →ₗ[ℚ_[l]] HQ l (sch.obj (H.geomZ Ω)) m 0,
      hop l H Ω g = DirectSum.lmap Tm ∧
      (∀ (m : ℤ) (x : HQ l (sch.obj (H.geomZ Ω)) m 0), pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0 (Tm m x) =
        ∑ i, pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0 x) ∧
      ∀ m : ℤ, Function.Injective (pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0) := by
  classical
  have hu := isUnit_natCast_sp l (Fact.out : l.Prime).ne_zero Ω
  have hGood := fun m : ℤ => hE l (sp Ω) hu m 0
  let g₀ : sp Ω ⟶ sp k := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  have hσs : ∀ j, σ j ≫ H.s g ≫ H.q = c ≫ H.q := fun j => by
    rw [← Category.assoc, hSp.choose j]
  have hac : ∀ x, a x ≫ c ≫ H.q = c ≫ H.q := fun x => by
    rw [← Category.assoc, hGal.2.2.2.2.2.choose x]
  obtain ⟨hfin, het, hspl⟩ := hS g₀ H.q (H.s g ≫ H.q) (c ≫ H.q) (H.s g) rfl c rfl I σ hσs
  have hsp' := hspl hSp
  have hgal' := hG g₀ H.q (c ≫ H.q) c rfl G a hac hGal
  choose tr htr using fun m : ℤ => (hGood m).tr (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀)
    (bcMap g₀ (H.s g) rfl) (bcMap_snd _ _ _)
  let Tm : ∀ m : ℤ, HQ l (sch.obj (H.geomZ Ω)) m 0 →ₗ[ℚ_[l]] HQ l (sch.obj (H.geomZ Ω)) m 0 := fun m =>
    tr m ∘ₗ (etn l (sp Ω) m 0).pull (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _)
  have key : ∀ (m : ℤ) (x : HQ l (sch.obj (H.geomZ Ω)) m 0),
      pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0 (Tm m x) =
        ∑ i, pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0 x := by
    intro m x
    have h1 := htr m _ (pullback.snd (c ≫ H.q) g₀) (bcMap g₀ c rfl) (bcMap_snd _ _ _) I
      (fun j => bcMap g₀ (σ j) (hσs j)) (fun j => bcMap_snd _ _ _) hsp'
      ((etn l (sp Ω) m 0).pull (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _) x)
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    have e := bcMap_comp' g₀ (σ i) (H.t g) (hσs i) (H.comm g) (hσ i)
    have h2 := (etn l (sp Ω) m 0).pull_comp (bcMap g₀ (σ i) (hσs i)) (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _)
      (bcMap_snd _ _ _) (by rw [Category.assoc, bcMap_snd, bcMap_snd]) x
    rw [← h2, th_pull_congr _ e _ (bcMap_snd _ _ _)]
    rfl
  have hA : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (DirectSum.lmap Tm) := by
    refine ⟨_, bcMap g₀ c rfl, G, inferInstance, inferInstance, fun x => bcMap g₀ (a x) (hac x), I, inferInstance,
      fun j => bcMap g₀ (σ j) (hσs j), hgal', hsp', fun x => ?_⟩
    have e : ∀ j, bcMap g₀ (σ j) (hσs j) ≫ H.tΩ Ω g = geomMap Ω (c ≫ H.q) (σ j ≫ H.t g) (hσ j) := fun j =>
      bcMap_comp' g₀ (σ j) (H.t g) (hσs j) (H.comm g) (hσ j)
    simp only [e]
    exact lmap_of_key Tm (fun m => pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0)
      (fun i m => pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0) key x
  refine ⟨Tm, ?_, key, fun m => ?_⟩
  · have hh : hop l H Ω g = hEx.choose := by
      unfold hop
      exact dif_pos hEx
    rw [hh]
    exact hU l Ω (pullback.snd H.q g₀) _ _ _ _ hEx.choose_spec hA
  · exact (hGood m).inj _ _ (bcMap g₀ c rfl) (bcMap_snd _ _ _) G _ hgal'

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.jCoverOp :
    EtnGood → BcSplits → BcGal → CorrUniq → PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOp := by
  intro hE hS hG hU l _ K H _ g _ _ W c G _ _ a I _ σ hσ hGal hSp hEx n
  obtain ⟨Tm, h1, h2, h3⟩ := coverCore hE hS hG hU l H g W c G a I σ hσ hGal hSp hEx
  refine ⟨h3 n, Tm n, fun x => ?_, ?_⟩
  · rw [h1, DirectSum.lmap_lof]
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.sum_apply]
    exact h2 n x
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

private theorem iInf_pre {X X' : Scheme.{0}} (g : X' ⟶ X) {n : ℕ} (U : Fin n → X.Opens)
    (S : Finset (Fin n)) : (⨅ i ∈ S, g ⁻¹ᵁ U i) = g ⁻¹ᵁ (⨅ i ∈ S, U i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S _ ih
    rw [Finset.iInf_insert, Finset.iInf_insert, Scheme.Hom.preimage_inf, ih]

private theorem pull_isBC (pE : P_equiv) (pC : P_cube) (pA : P_affine) (pV : P_cover)
    (pO : P_omega) (pH : P_cech) {k k' : Type} [Field k] [Field k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X)
    (h : IsPullback g s' s (spMap (algebraMap k k'))) [IsProper s] (a b : ℕ) :
    IsBC e (hodgePullS h.w a b) := by
  letI := algΓ s
  letI := algΓ s'
  obtain ⟨n, U, hc, hU⟩ := pV k X s
  haveI : IsAffineHom g := pA k k' (algebraMap k k') X X' s s' g h
  have hc' : ⨆ i, g ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  have hU' : ∀ S : Finset (Fin n), S.Nonempty → IsAffineOpen (⨅ i ∈ S, g ⁻¹ᵁ U i) := by
    intro S hS
    rw [iInf_pre]
    exact IsAffineHom.isAffine_preimage _ (hU S hS)
  have hcube : IsBC e
      ((cechCubeMapOver ⊤ U (appTop_algebraMapS h.w) (omegaPullS h.w a)).homology b) := by
    apply pC k k' J e (Fin n)
    intro S hS
    have hA : IsAffineOpen (cechOpen ⊤ U S) := by
      rw [cechOpen, top_inf_eq]
      exact hU S hS
    refine pE k k' J e _ _ _ _
      (sectionsOn.mapOver (appTop_algebraMapS h.w) (omegaPullS h.w a) (cechOpen ⊤ U S))
      (LinearEquiv.refl k _) (sectionsOn.congrOpens k' _ (preimage_cechOpen g ⊤ U S)) _ ?_
      (pO k k' J e X X' s s' g h a _ hA)
    intro x
    exact (sectionsOn.congrOpens_apply k' (Omega s' a) (preimage_cechOpen g ⊤ U S) _).symm
  refine pE k k' J e _ _ _ _ _ (cechHEquivCoh k hc hU (Omega s a) b).symm
    (cechHEquivCoh k' hc' hU' (Omega s' a) b) (hodgePullS h.w a b) ?_ hcube
  intro x
  obtain ⟨y, rfl⟩ := (cechHEquivCoh k hc hU (Omega s a) b).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact pH k k' X X' s s' g h.w a b n U hc hU hc' hU' y

theorem UpperTheory.Gal.G3.jHBC :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cube → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cech → (∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k') {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ)) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (he : IsPullback e r' r (spMap φ)) (f : Y ⟶ X) (hf : f ≫ s = r) (f' : Y' ⟶ X') (hf' : f' ≫ s' = r'), e ≫ f = f' ≫ g → ∀ (a b : ℕ) [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] (y : hodgeH r a b), hodgePullS h.w a b (hodgeTrace hf a b y) = hodgeTrace hf' a b (hodgePullS he.w a b y)) → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HodgeBC := by
  intro pB pE pC pA pV pO pH pT k k' _ _ φ
  refine ⟨fun s s' g h a b ↦ hodgePullS h.w a b, ?_, ?_⟩
  · intro X X' s s' g h _ a b I c
    letI : Algebra k k' := φ.toAlgebra
    have h₀ : IsPullback g s' s (spMap (algebraMap k k')) := h
    exact pB k k' _ (Module.Basis.ofVectorSpace k k') _ _ (hodgePullS h₀.w a b)
      (pull_isBC pE pC pA pV pO pH _ s s' g h₀ a b) I c
  · intro X X' Y Y' s s' g h r r' e he f hf f' hf' w a b
    exact ⟨fun x ↦ hodgePullS_nat_pull h.w he.w hf hf' w a b x,
      fun y ↦ pT k k' φ s s' g h r r' e he f hf f' hf' w a b y⟩
end
