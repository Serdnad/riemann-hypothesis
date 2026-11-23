module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem fderiv_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (F : V → ℂ) (v₀ w : V)
    (hF : DifferentiableAt ℂ F v₀) :
    DifferentiableAt ℂ (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w)) 0 ∧
      fderiv ℂ (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w)) 0 (fun _ => 1) = fderiv ℂ F v₀ w := by
  have hℓ : HasFDerivAt (fun z : Fin 1 → ℂ => v₀ + z 0 • w)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w) 0 := by
    have h1 : HasFDerivAt (fun z : Fin 1 → ℂ => z 0 • w)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w) 0 :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w).hasFDerivAt
    exact h1.const_add v₀
  have hF' : HasFDerivAt F (fderiv ℂ F v₀) ((fun z : Fin 1 → ℂ => v₀ + z 0 • w) 0) := by
    simpa using hF.hasFDerivAt
  have hc : HasFDerivAt (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w))
      ((fderiv ℂ F v₀).comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w)) 0 :=
    hF'.comp (0 : Fin 1 → ℂ) hℓ
  refine ⟨hc.differentiableAt, ?_⟩
  rw [hc.fderiv]
  simp

private theorem exists_isDerivAt0_line_of_isHolTo {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V) :
    ∃ x, IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1) x := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((t v₀) default)) isOpen_univ
  have hW0 : ⊤ ≤ t v₀ ⁻¹ᵁ W := by
    rw [top_le_preimage_iff_mem]
    have hd : (@default (PrimeSpectrum ℂ) _) = (@default (↥(Sp ℂ)) _) := Subsingleton.elim _ _
    rw [hd]
    exact hxW
  have hℓc : Continuous (fun z : Fin 1 → ℂ => v₀ + z 0 • w) := by
    fun_prop
  have hℓ0 : (fun z : Fin 1 → ℂ => v₀ + z 0 • w) 0 = v₀ := by
    simp
  have hev : ∀ᶠ z in 𝓝 (0 : Fin 1 → ℂ), ⊤ ≤ t (v₀ + z 0 • w) ⁻¹ᵁ W := by
    have h1 := LocalLift.hol_eventually_mem ht hv hW0
    have h2 : Tendsto (fun z : Fin 1 → ℂ => v₀ + z 0 • w) (𝓝 0) (𝓝 v₀) := by
      have := hℓc.tendsto 0
      simpa using this
    exact (h2.eventually h1).mono (fun z hz => hz.2)
  have hdiff : ∀ a : Γ(X, W), DifferentiableAt ℂ (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a) 0 :=
    fun a => (fderiv_line (fun v => valAt' (t v) W a) v₀ w
      (LocalLift.hol_differentiableAt ht hv hW0 a)).1
  let ψ : Γ(X, W) →+* DualNumber ℂ :=
    { toFun := fun a => FibreDeriv.jet (fun _ => 1) (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a)
      map_one' := by
        have hc : (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W 1) =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) :=
          hev.mono (fun z hz => valAt'_one _ hz)
        rw [FibreDeriv.jet_congr _ hc, FibreDeriv.jet_const]
        simp
      map_mul' := by
        intro a b
        simp only [valAt'_mul]
        exact FibreDeriv.jet_mul _ (hdiff a) (hdiff b)
      map_zero' := by
        simp only [valAt'_zero]
        rw [FibreDeriv.jet_const]
        simp
      map_add' := by
        intro a b
        simp only [valAt'_add]
        exact FibreDeriv.jet_add _ (hdiff a) (hdiff b) }
  obtain ⟨x, hx, hxψ⟩ := TangentOrigin.exists_evalPt_eq hW ψ
  refine ⟨x, FibreDeriv.isDerivAt0_of_affine ?_ hW hx (fun a => ⟨hdiff a, ?_⟩)⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ x) ⁻¹ᵁ W :=
      (TangentOrigin.top_le_preimage_iff x W).mp hx
    have h0 : ⊤ ≤ t (v₀ + (0 : Fin 1 → ℂ) 0 • w) ⁻¹ᵁ W := by
      simpa using hW0
    refine TangentOrigin.ext_evalPt hW h' h0 (RingHom.ext (fun a => ?_))
    rw [TangentOrigin.evalPt_spMap_comp _ x W hx h' a, hxψ, ← TangentOrigin.valAt'_eq_evalPt]
    exact FibreDeriv.fst_jet (fun _ => 1) (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a)
  · show TangentOrigin.evalPt x W hx a = _
    rw [hxψ]
    rfl

private theorem isDerivAt0_line_const_of_flat {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V)
    (hf : Flat t v₀ w) :
    IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) := by
  have h := LocalLift.isDerivAt0_const (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
    (fun U f hU => by
      have hU' : ⊤ ≤ t v₀ ⁻¹ᵁ U := by
        simpa using hU
      rw [(fderiv_line (fun v => valAt' (t v) U f) v₀ w
        (LocalLift.hol_differentiableAt ht hv hU' f)).2]
      exact hf U f hU')
  simpa using h

private theorem flat_of_isDerivAt0_line_const {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V)
    (hd : IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀)) :
    Flat t v₀ w := by
  intro U f hU
  rw [← (fderiv_line (fun v => valAt' (t v) U f) v₀ w
    (LocalLift.hol_differentiableAt ht hv hU f)).2]
  have hc : IsDerivAt0 (fun _ : Fin 1 → ℂ => t v₀) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) :=
    LocalLift.isDerivAt0_const (fun _ : Fin 1 → ℂ => t v₀) (fun _ => 1)
      (fun U' f' _ => by simp)
  have h : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) ⁻¹ᵁ U := by
    rw [TangentOrigin.top_le_preimage_iff, hc.1]
    exact hU
  rw [← hd.2 U h f, hc.2 U h f]
  simp

theorem UpperTheory.Gal.W2.pbFlat_of :
    UpperTheory.Gal.W2.FlatAffine → UpperTheory.Gal.W2.PbFlat := by
  intro hFA V _ _ P Y₁ Y₂ T p₁ p₂ f₁ f₂ hpb B s v₀ w hB hv h1 h2 hf1 hf2
  have hs : IsHolTo B s :=
    HolPullback.isHolTo_of_components V B Y₁ P T Y₂ p₁ p₂ f₁ f₂ s hpb hB h1 h2
  obtain ⟨x, hx⟩ := exists_isDerivAt0_line_of_isHolTo hs hv w
  have hc1 := isDerivAt0_line_const_of_flat h1 hv w hf1
  have hc2 := isDerivAt0_line_const_of_flat h2 hv w hf2
  have hx1 := FibreDeriv.isDerivAt0_comp hx p₁
  have hx2 := FibreDeriv.isDerivAt0_comp hx p₂
  have he1 : x ≫ p₁ = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀) ≫ p₁ := by
    rw [Category.assoc]
    exact VerticalDeriv.isDerivAt0_unique hx1 hc1
  have he2 : x ≫ p₂ = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀) ≫ p₂ := by
    rw [Category.assoc]
    exact VerticalDeriv.isDerivAt0_unique hx2 hc2
  have hxe : x = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀ := hpb.hom_ext he1 he2
  rw [hxe] at hx
  exact flat_of_isDerivAt0_line_const hs hv w hx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_zero_hom_isIso {X : Scheme.{0}} (A : Over X) : IsIso (GlobalTheory.KS.pow A 0).hom := by
  let t : Over.mk (𝟙 X) ⟶ GlobalTheory.KS.pow A 0 := Pi.lift fun i => Fin.elim0 i
  let u : GlobalTheory.KS.pow A 0 ⟶ Over.mk (𝟙 X) := Over.homMk (GlobalTheory.KS.pow A 0).hom
  have h1 : u ≫ t = 𝟙 _ := Pi.hom_ext _ _ fun i => Fin.elim0 i
  refine ⟨⟨t.left, ?_, ?_⟩⟩
  · have h2 := congrArg Over.Hom.left h1
    simpa [u] using h2
  · simpa using Over.w t

private noncomputable def tailMap {X : Scheme.{0}} (A : Over X) (k : ℕ) : GlobalTheory.KS.pow A (k + 1) ⟶ GlobalTheory.KS.pow A k :=
  Pi.lift fun j => GlobalTheory.KS.pr A j.succ

private theorem tailMap_pr {X : Scheme.{0}} (A : Over X) (k : ℕ) (j : Fin k) :
    tailMap A k ≫ GlobalTheory.KS.pr A j = GlobalTheory.KS.pr A j.succ := by
  simp [tailMap, GlobalTheory.KS.pr]


private theorem pow_succ_isPullback {X : Scheme.{0}} (A : Over X) (k : ℕ) :
    IsPullback (GlobalTheory.KS.pr A (0 : Fin (k + 1))).left (tailMap A k).left A.hom (GlobalTheory.KS.pow A k).hom := by
  refine Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk (GlobalTheory.KS.pr A (0 : Fin (k + 1))) (tailMap A k)) ?_
  refine BinaryFan.IsLimit.mk _ (fun f g => Pi.lift (Fin.cases f (fun j => g ≫ GlobalTheory.KS.pr A j))) ?_ ?_ ?_
  · intro T f g
    simp [GlobalTheory.KS.pr]
  · intro T f g
    refine Pi.hom_ext _ _ fun j => ?_
    simp [tailMap, GlobalTheory.KS.pr]
  · intro T f g m h1 h2
    simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at h1 h2
    refine Pi.hom_ext (f := fun _ : Fin (k + 1) => A) (m : T ⟶ ∏ᶜ fun _ : Fin (k + 1) => A) _ fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [← h1, GlobalTheory.KS.pr]
    · rw [← h2]
      simp [tailMap, GlobalTheory.KS.pr]

theorem UpperTheory.Gal.W2.holPi_of :
    UpperTheory.Gal.W2.HolPi := by
  intro V _ _ X A k
  induction k with
  | zero =>
    intro B s hB h0 _
    haveI := pow_zero_hom_isIso A
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h0 (inv (GlobalTheory.KS.pow A 0).hom)) ?_
    intro b _
    simp
  | succ k ih =>
    intro B s hB h0 hj
    refine GlobalTheory.HolPullback.isHolTo_of_components V B _ _ _ _ _ _ _ _ s (pow_succ_isPullback A k) hB (hj 0) ?_
    apply ih B (fun v => s v ≫ (tailMap A k).left) hB
    · refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr h0 ?_
      intro b _
      simp only [Category.assoc, Over.w]
    · intro j
      refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr (hj j.succ) ?_
      intro b _
      simp only [Category.assoc]
      rw [← Over.comp_left, tailMap_pr]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.expImm_of :
    UpperTheory.Gal.W2.FlatComp → UpperTheory.Gal.W2.FlatPre → UpperTheory.Gal.W2.PbFlat → UpperTheory.Gal.W2.ExpImm0 → UpperTheory.Gal.W2.ExpImm := by
  intro hcomp hpre hpb h0 X A _ g y e he z₀ w hw
  apply h0 X A g y e he w
  have hsplit : ∀ z, e z = e (-z₀) * e (z₀ + z) := by
    intro z
    rw [← he.1, neg_add_cancel_left]
  have hhol : IsHolTo Set.univ (fun z => Over.Hom.left (e (z₀ + z))) :=
    GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp (φ := fun z => z₀ + z) he.2.2.1 isOpen_univ
      (by fun_prop) (Set.mapsTo_univ _ _)
  have hflat : Flat (fun z => Over.Hom.left (e (z₀ + z))) 0 w := by
    have hd : HasFDerivAt (fun z : Fin g → ℂ => z₀ + z) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
      (hasFDerivAt_id 0).const_add z₀
    refine (hpre (Fin g → ℂ) (Fin g → ℂ) A.left Set.univ (fun z => Over.Hom.left (e z)) he.2.2.1
      (fun z => z₀ + z) _ 0 w hd (Set.mem_univ _)).2 ?_
    simpa using hw
  have hpbA : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct A A)
  have h1 : (fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (fst A A).left) =
      fun _ => (e (-z₀)).left := by
    funext z
    rw [← Over.comp_left, lift_fst]
  have h2 : (fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (snd A A).left) =
      fun z => (e (z₀ + z)).left := by
    funext z
    rw [← Over.comp_left, lift_snd]
  have hconstHol : IsHolTo Set.univ (fun _ : Fin g → ℂ => (e (-z₀)).left) := by
    intro U f
    refine ⟨?_, differentiableOn_const _⟩
    by_cases hU : ⊤ ≤ (e (-z₀)).left ⁻¹ᵁ U
    · simp [hU]
    · simp [hU]
  have hconstFlat : Flat (fun _ : Fin g → ℂ => (e (-z₀)).left) 0 w := by
    intro U f _
    simp
  have hs : Flat (fun z => (lift (e (-z₀)) (e (z₀ + z))).left) 0 w := by
    refine hpb (Fin g → ℂ) _ A.left A.left X (fst A A).left (snd A A).left A.hom A.hom hpbA Set.univ
      _ 0 w isOpen_univ (Set.mem_univ _) ?_ ?_ ?_ ?_
    · beta_reduce
      rw [h1]
      exact hconstHol
    · beta_reduce
      rw [h2]
      exact hhol
    · beta_reduce
      rw [h1]
      exact hconstFlat
    · beta_reduce
      rw [h2]
      exact hflat
  have hfe : (fun z => (e z).left) =
      fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (μ : A ⊗ A ⟶ A).left := by
    funext z
    rw [← Over.comp_left, ← Hom.mul_def, ← hsplit]
  rw [hfe]
  exact hcomp (Fin g → ℂ) _ A.left (μ : A ⊗ A ⟶ A).left _ 0 w hs
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.eigTop_of :
    UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.DiagExists → UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.RootsFull → UpperTheory.Gal.W2.MarkDiag → UpperTheory.Gal.W2.BallChar → UpperTheory.Gal.W2.FibDet → UpperTheory.Gal.W2.FibW → UpperTheory.Gal.W2.EvIntegral → UpperTheory.Gal.W2.EigTop := by
  intro hAd hDg hTy hRf hMk hBc hFd hFw hEv F _ _ O _ bar g ρ a n t₀ ε hSig D P₀ M₀ hP hM ga H hFix χ hMin hdeg hsep d co hco T hT k α hα
  have hH : H.det ≠ 0 := (hAd O bar g ρ D P₀ M₀ hP hM ga H hFix).1
  obtain ⟨Sb, ty, ev, hD⟩ := hDg F O bar g ρ a D P₀ hP ga H hFix.2 χ hMin hsep
  have hcnt := hTy F O bar g ρ a n t₀ ε hSig H Sb ty ev hD
  have hrts := hRf F O bar g ρ a n t₀ ε hSig D P₀ hP ga H hFix.2 Sb ty ev hD χ hMin hdeg
  have hmk := hMk F O bar g ρ a n t₀ ε hSig H Sb ty ev hD
  refine ⟨?_, ?_⟩
  · have h1 : (evAt ty ev t₀).card = 1 := by
      have h := (hcnt t₀).1
      simpa [typeMult] using h
    obtain ⟨m, hm⟩ := Multiset.card_eq_one.1 h1
    exact ⟨m, (hmk m).2 hm⟩
  intro mu hmu
  have hE : evAt ty ev t₀ = {mu} := (hmk mu).1 hmu
  have hev0 : ∀ i, ev i ≠ 0 := by
    intro i h0
    have hdet : H.det * Sb.det = Sb.det * ∏ j, ev j := by
      have h := congrArg Matrix.det hD.2.2
      simpa [Matrix.det_mul, Matrix.det_diagonal] using h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero] at hdet
    exact mul_ne_zero hH hD.1 hdet
  have hr0 : rts χ t₀ = mu ::ₘ (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ) := by
    rw [hrts t₀]
    unfold evFull
    rw [hE, Multiset.singleton_add]
  have hnd : (rts χ t₀).Nodup := Polynomial.nodup_roots hsep.map
  rw [hr0, Multiset.nodup_cons] at hnd
  have hne : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), (starRingEnd ℂ) r ≠ mu := by
    intro r hr h
    exact hnd.1 (h ▸ Multiset.mem_map_of_mem _ hr)
  have hnz : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), (starRingEnd ℂ) r ≠ 0 := by
    intro r hr
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hr
    exact (_root_.map_ne_zero _).2 (hev0 i)
  have herase : (rts χ t₀).erase mu = (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ) := by
    rw [hr0, Multiset.erase_cons_head]
  obtain ⟨-, hdetT⟩ := hBc F O bar g ρ a n t₀ ε hSig D P₀ M₀ hP hM H hH Sb ty ev hD mu hE d co hco T hT
  have hT1 : LinearMap.det (1 - T) =
      ((evAt ty ev (ComplexEmbedding.conjugate t₀)).map fun r => 1 - 1 * (mu / (starRingEnd ℂ) r)).prod := by
    have h := hdetT 1
    rwa [one_smul] at h
  have hfac : ∀ r ∈ evAt ty ev (ComplexEmbedding.conjugate t₀), 1 - 1 * (mu / (starRingEnd ℂ) r) ≠ 0 := by
    intro r hr h
    apply hne r hr
    have hs := hnz r hr
    field_simp at h
    linear_combination h
  have hFib := hFd F O bar g ρ a H Sb ty ev hD k α
  have hF1 : LinearMap.det (1 - fibMap H (diagAct a ρ α)) = ∏ s, ∏ i, (1 - ty i (α s : F) * ev i) := by
    have h := hFib 1
    rw [one_smul] at h
    simpa using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr0]
    exact Multiset.mem_cons_self _ _
  · rw [hT1]
    refine Multiset.prod_ne_zero fun h => ?_
    obtain ⟨r, hr, h0⟩ := Multiset.mem_map.1 h
    exact hfac r hr h0
  · rw [hF1]
    refine Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    obtain ⟨x, hx⟩ := hα s
    have h := hEv F O bar g ρ a D P₀ hP ga H hFix.2 Sb ty ev hD i x
    rwa [← hx] at h
  · intro t
    have hball : LinearMap.det (1 - t • T) / LinearMap.det (1 - T) = ballW t₀ t χ mu := by
      unfold ballW
      rw [herase, Multiset.map_map, hdetT t, hT1, ← Multiset.prod_map_div]
      congr 1
      refine Multiset.map_congr rfl fun r hr => ?_
      have hs := hnz r hr
      have h1 := hfac r hr
      have h2 : (starRingEnd ℂ) r - mu ≠ 0 := sub_ne_zero.2 (hne r hr)
      simp only [Function.comp_apply]
      rw [div_eq_div_iff h1 h2]
      field_simp
    unfold locW
    rw [hball, hFib t, hF1, map_prod, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    have h := hFw F g n t₀ ε ty ev χ mu hSig.cx hSig.pos hSig.eps (fun τ => (hcnt τ).1) hrts hE (α s : F) t
    rw [← h, map_prod]
end
