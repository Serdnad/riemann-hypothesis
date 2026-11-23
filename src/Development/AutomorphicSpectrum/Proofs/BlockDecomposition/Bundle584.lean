module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle340
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle469
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle547
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle342
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle326
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle147
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle380
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle360
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SatBridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle650
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle568
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle574
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle575
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle509

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ReductionFirstChern

open GlobalTheory.CompanionTheory.CocCls

section Ring

variable {S S' : Type} [CommRing S] [CommRing S'] {J : Ideal S} {J' : Ideal S'}

theorem dpow_mem_pdP (δ : DividedPowers J) {x : S} (hx : x ∈ J) {k r : ℕ} (h : r ≤ k) : δ.dpow k x ∈ pdP δ r :=
  Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simpa using h, by simp⟩

theorem dlog_trunc (δ : DividedPowers J) {s N : ℕ} (hs : pdP δ s = ⊥) (h : s ≤ N) {v : S} (hv : v - 1 ∈ J) :
    B.dlog δ N v = B.dlog δ s v := by
  unfold B.dlog
  refine (Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_).symm
  have h1 : δ.dpow (k + 1) (v - 1) ∈ pdP δ s := dpow_mem_pdP δ hv (by
    have : s ≤ k := by simpa using hk
    omega)
  rw [hs, Ideal.mem_bot] at h1
  rw [h1, mul_zero]

theorem dlog_red {δ : DividedPowers J} {δ' : DividedPowers J'} {f : S →+* S'} (hf : IsDPMorphism δ δ' f) {s N : ℕ}
    (hs : pdP δ s = ⊥) (hN : ∀ k, N ≤ k → (k.factorial : S') = 0) {v : S} (hv : v - 1 ∈ J) :
    f (B.dlog δ s v) = B.dlog δ' N (f v) := by
  rw [← dlog_trunc δ hs (le_max_left s N) hv, dlog_map hf _ hv]
  exact GlobalTheory.CompanionTheory.FirstChernClassFactorial.dlog_eq_of_factorial δ' (le_max_right s N) hN _

theorem factorial_quot {l : ℕ} (hl : l ≠ 0) (n k : ℕ) (hk : l * n ≤ k) :
    (k.factorial : S ⧸ Ideal.span {(l : S) ^ n}) = 0 := by
  obtain ⟨a, ha⟩ := (GlobalTheory.CompanionTheory.FirstChernClassFactorial.pow_dvd_factorial_mul l (Nat.pos_of_ne_zero hl) n).trans (Nat.factorial_dvd_factorial hk)
  rw [ha, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : S) ^ n})), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Ring

section Lift

variable {O A R : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {s : ℕ} {𝒱 : Set X.Opens}
  {C : Type 1} [Category.{0} C] (g : C ⥤ (TS γ q l s 𝒱).FullSubcategory) {D : E.LineData X}

def redLift (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D) :
    B.CLift (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) (g ⋙ redG q s d 𝒱) D where
  p T := Spec.map (CommRingCat.ofHom (qBar (g.obj T).obj l n)) ≫ Lf.p T
  hp T := by
    rw [Category.assoc, Lf.hp]
    rfl
  w {T T'} φ := Units.map (Ideal.Quotient.mk (lnT (g.obj T').obj l n)).toMonoidHom (Lf.w φ)
  hw {T T'} φ h := by
    have e : B.thSp (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) ((g ⋙ redG q s d 𝒱).map φ) ≫ Spec.map (CommRingCat.ofHom (qBar (g.obj T).obj l n)) ≫ Lf.p T =
        Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ (B.thSp (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) ((g ⋙ (TS γ q l s 𝒱).ι).map φ) ≫ Lf.p T) := by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      unfold B.thSp
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
    have h0 := hh Lf φ
    have h2 : (Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ (B.thSp (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) ((g ⋙ (TS γ q l s 𝒱).ι).map φ) ≫ Lf.p T)) ≫ D.f =
        (Spec.map (CommRingCat.ofHom (qBar (g.obj T').obj l n)) ≫ Lf.p T') ≫ D.f := by
      rw [Category.assoc, h0, Category.assoc]
    have h3 := uq_map D (qBar (g.obj T').obj l n) _ _ h0 h2
    have h4 := uq_congr D e rfl h h2
    have h5 := Lf.hw φ h0
    change _ = (uq D _ _ h).val
    rw [h4, h3]
    change _ = qBar (g.obj T').obj l n (uq D _ _ h0).val
    refine Eq.trans ?_ (congrArg (qBar (g.obj T').obj l n) h5)
    rfl

theorem r_red (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) :
    (B.CLift.r (redLift d g Lf) σ).val = Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n) (B.CLift.r Lf σ).val := by
  have h2 : B.CLift.r (redLift d g Lf) σ =
      Units.map (Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n)).toMonoidHom (B.CLift.r Lf σ) := by
    unfold B.CLift.r
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [h2]
  rfl

theorem r_sub (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) : (B.CLift.r Lf σ).val - 1 ∈ (g.obj (σ.obj (Fin.last 2))).obj.J := by
  have hfg : σ.map' 0 2 = σ.map' 0 1 ≫ σ.map' 1 2 := σ.map'_comp 0 1 2
  have h0 : B.CLift.r Lf σ = Rf Lf (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 1 ≫ σ.map' 1 2) := by
    rw [← hfg]
    rfl
  have h1 : red (σ.obj (Fin.last 2)) (g ⋙ (TS γ q l s 𝒱).ι) (B.CLift.r Lf σ) = 1 := by
    rw [h0]
    exact red_Rf Lf _ _
  exact sub_one_mem h1

theorem coc_red {Λ : Type} [CommRing Λ] (c : Λ →+* R)
    (Lf : B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ (TS γ q l s 𝒱).ι) D)
    (σ : ComposableArrows C 2) :
    B.CLift.coc (redLift d g Lf) c (l * n) σ =
      Ideal.Quotient.mk (lnT (g.obj (σ.obj (Fin.last 2))).obj l n) (B.CLift.coc Lf (RingHom.id A) s σ) := by
  have e1 := dlog_red (redδ_dp (g.obj (σ.obj (Fin.last 2))).obj (g.obj (σ.obj (Fin.last 2))).property.1 n) (s := s) (N := l * n)
    (g.obj (σ.obj (Fin.last 2))).property.1.1 (fun k hk => factorial_quot d.hl n k hk) (r_sub g Lf σ)
  exact (congrArg _ (r_red d g Lf σ)).trans e1.symm

end Lift

section Top

variable {b : Base} {L : b.Fun}

theorem idF_ext {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a a' : IdF A}
    (h : a.S = a'.S) : a = a' := by
  cases a
  cases a'
  cases h
  rfl

theorem stdI_top (Q : ObjectProperty (Thick L)) : stdI Q (some 0) 0 = IdF.top _ :=
  idF_ext (funext fun T => top_unique (le_trans (le_of_eq T.obj.pdPow_zero.symm) le_sup_left))

theorem bij_top {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {a e : IdF (sP Q).A} {a' e' : IdF (sP Q').A}
    (ha : a = IdF.top _) (ha' : a' = IdF.top _) (h1 : (incl h).Le a a') (h2 : (incl h).Le e e') (j : ℕ)
    (H : Function.Bijective (((incl h).sq h1 h2).pull j)) :
    Function.Bijective (((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) h2).pull j) := by
  subst ha ha'
  exact H

end Top

theorem coefficientReduction_firstChernClass_tateTwist : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))
    (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∀ (x : CH.H (B.OM (nlFun δ l X q κ) c) 2) (z : HO (TS γ q l s {⊤}) 2),
    B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R J δ l) (ht := rfl) (κ := κ) D c (l * n) x → IsFirstChernThickening (TS γ q l s {⊤}) D s z →
    redM (TS γ q l s {⊤}) none ((l : A) ^ n) 2 z = (redMor q s d {⊤} c lam hc none).pull 2 x := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s c lam hc D hD x z hx hz
  let Q := TS γ q l s {⊤}
  let Q' := TS γ q l s (𝒱D D)
  have h : Q' ≤ Q := fun T hT => ⟨hT.1, ⊤, rfl, GlobalTheory.CompanionTheory.CrystallineChernClass.inU_top T⟩
  let g : Q'.FullSubcategory ⥤ Q.FullSubcategory := ObjectProperty.ιOfLE h
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun γ 0 X q (κA O I)))) := Or.inl ⟨rfl, l, s, rfl⟩
  have hinj := bij_top h (stdI_top Q) (stdI_top Q') _ (incl_std h none ((l : A) ^ n)) 2
    ((GlobalTheory.T.cech_refinement_cohomology_bijective (TF l s) hU (𝒱D D) {⊤} h (by rintro W rfl; rw [hD]) 2).2.1 (some 0) none 0 ((l : A) ^ n))
  obtain ⟨Lf⟩ := GlobalTheory.T.exists_crystalline_lift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (g ⋙ Q.ι) D (fun T =>
    GlobalTheory.CompanionTheory.CrystallineChernClass.st_le_lifts (γ := γ) (p := 0) (q := q) (κ := κA O I) D T.obj ⟨trivial, T.property.2⟩)
  obtain ⟨hz1, hcl1⟩ := hz Q'.FullSubcategory g (fun T => T.property.2) Lf
  let Lr := redLift d g Lf
  obtain ⟨hz2, hcl2⟩ := hx Q'.FullSubcategory (g ⋙ redG q s d {⊤}) Lr
  apply hinj.1
  let P := (incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h none ((l : A) ^ n))
  let M₁ := (toSq (IdF.top _) (stdI Q none ((l : A) ^ n)) fun _ => rfl).comp P
  let M₂ := (redMor q s d {⊤} c lam hc none).comp (σ'' := lam) P
  let m₁ : CH.Mor (g ⋙ CH.modF (sP Q).A) (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) (RingHom.id A) :=
    { G := 𝟭 _, τ := fun T => M₁.τ T, nat := fun φ x => M₁.nat φ x }
  let m₂ : CH.Mor ((g ⋙ redG q s d {⊤}) ⋙ B.OM (nlFun δ l X q κ) c) (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) lam :=
    { G := 𝟭 _, τ := fun T => M₂.τ T, nat := fun φ x => M₂.nat φ x }
  have hL : P.pull 2 (redM Q none ((l : A) ^ n) 2 z) = m₁.pull 2 ((CH.Mor.restrict (CH.modF (sP Q).A) g).pull 2 z) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  have hR : P.pull 2 ((redMor q s d {⊤} c lam hc none).pull 2 x) =
      m₂.pull 2 ((CH.Mor.restrict (B.OM (nlFun δ l X q κ) c) (g ⋙ redG q s d {⊤})).pull 2 x) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have hE : m₁.pullC 2 (Lf.coc (RingHom.id A) s) = m₂.pullC 2 (Lr.coc c (l * n)) := by
    funext σ
    have e := coc_red d g c Lf σ
    have t : ∀ (T : Q'.FullSubcategory) (b : (g.obj T).obj.B), m₁.τ T b = m₂.τ T (Ideal.Quotient.mk (lnT (g.obj T).obj l n) b) :=
      fun _ _ => rfl
    exact (t _ _).trans (congrArg (m₂.τ _) e.symm)
  have hb1 : CH.d _ 2 (m₁.pullC 2 (Lf.coc (RingHom.id A) s)) = 0 :=
    (m₁.d_pullC 2 _).trans ((congrArg _ hz1).trans (map_zero _))
  have hb2 : CH.d _ 2 (m₂.pullC 2 (Lr.coc c (l * n))) = 0 :=
    (m₂.d_pullC 2 _).trans ((congrArg _ hz2).trans (map_zero _))
  have a1 := CrystallineSemistableComparison.P.mapH_cls m₁.hom 2 _ hz1 hb1
  have a2 := CrystallineSemistableComparison.P.mapH_cls m₂.hom 2 _ hz2 hb2
  have key : ∀ (w w' : CH.Cn (sq (IdF.top (sP Q').A) (stdI Q' none ((l : A) ^ n))) 2) (k : CH.d _ 2 w = 0) (k' : CH.d _ 2 w' = 0),
      w = w' → (CH.cx _).cls w k = (CH.cx _).cls w' k' := by
    rintro _ _ _ _ rfl
    rfl
  exact hL.trans ((congrArg (m₁.pull 2) hcl1.symm).trans (a1.trans ((key _ _ hb1 hb2 hE).trans
    (a2.symm.trans ((congrArg (m₂.pull 2) hcl2).trans hR.symm)))))

end GlobalTheory.CompanionTheory.ReductionFirstChern
end
end

section

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrAdm : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π hs hi =>
  (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

theorem twJ_congr {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    {π' : Representation ℂ G' V} {N : Subgroup G} {N' : Subgroup G'} {θ : N →* ℂˣ} {θ' : N' →* ℂˣ}
    (h : twKer π N θ = twKer π' N' θ') :
    Nontrivial (TwJacquet π N θ) ↔ Nontrivial (TwJacquet π' N' θ') := by
  rw [Submodule.Quotient.nontrivial_iff, Submodule.Quotient.nontrivial_iff, h]

theorem exists_highest (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hn : Nontrivial V)
    (hg : ¬ IsGenericFor ψ π) :
    ∃ n, 0 < n ∧ n < N ∧ Nontrivial (TwJacquet π (derUnip k N n) (derChar k ψ N n)) ∧
      ∀ m < n, Subsingleton (TwJacquet π (derUnip k N m) (derChar k ψ N m)) := by
  have h0 : ¬ Nontrivial (TwJacquet π (derUnip k N 0) (derChar k ψ N 0)) := fun h =>
    hg ((twJ_congr (GlobalTheory.T.derivative_zero_whittaker_kernel k ψ N V π)).1 h)
  rcases N with _ | m
  · exfalso
    refine hg ?_
    show Nontrivial (V ⧸ twKer π (unipB k (Fin 0)) (whitChar ψ 0))
    have hb : twKer π (unipB k (Fin 0)) (whitChar ψ 0) = ⊥ := by
      unfold twKer
      rw [Submodule.span_eq_bot]
      rintro w ⟨u, v, rfl⟩
      have hu : (u : GL (Fin 0) k) = 1 := Subsingleton.elim _ _
      have hu' : u = 1 := Subtype.ext hu
      subst hu'
      simp
    rw [hb]
    exact (Submodule.quotEquivOfEqBot ⊥ rfl).toEquiv.nontrivial
  have hex : ∃ n, n ≤ m ∧ Nontrivial (TwJacquet π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n)) := by
    obtain ⟨n, hnm, h⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hc h1 m V (resM k π).ρ (isSmooth_comp hs _ continuous_subtype_val) hn
    exact ⟨n, hnm, (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ m n V π)).1 h⟩
  classical
  have hmin := fun (l : ℕ) (hl : l < Nat.find hex) => Nat.find_min hex hl
  obtain ⟨hle, hnt⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, Nat.pos_of_ne_zero fun e => h0 (e ▸ hnt), by omega, hnt, fun l hl => ?_⟩
  have := hmin l hl
  rw [not_and] at this
  exact not_nontrivial_iff_subsingleton.1 (this (by omega))

theorem isSmooth_iterPhi (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)), IsSmooth τ.ρ →
    IsSmooth (iterPhi k ψ j τ).ρ
  | 0, _, h => h
  | j + 1, τ, h => isSmooth_iterPhi ψ n j (MRep.phiM k ψ τ) (GlobalTheory.T.smooth_phi_minus k ψ _ _ τ.ρ h)

theorem isSmooth_resM {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin (n + 1)) k) V}
    (h : IsSmooth π) : IsSmooth (resM k π).ρ := isSmooth_comp h _ continuous_subtype_val

theorem isSmooth_deriv (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin (n + j + 1)) k) V} (h : IsSmooth π) : IsSmooth (GlobalTheory.BZMir.deriv k ψ j π) :=
  GlobalTheory.T.smooth_psi_minus k _ _ _ (isSmooth_iterPhi ψ n j _ (isSmooth_resM h))

theorem iterPhi_derUnip (ψ : AddChar k Circle) (n₂ n' : ℕ) (hn : n₂ ≤ n') : ∀ (j : ℕ) (τ : MRep k (n' + j)),
    Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (derUnipM k n' n₂) (derCharM k ψ n' n₂) ≃ₗ[ℂ]
      TwJacquet τ.ρ (derUnipM k (n' + j) n₂) (derCharM k ψ (n' + j) n₂))
  | 0, _ => ⟨LinearEquiv.refl _ _⟩
  | j + 1, τ => by
    refine Nonempty.elim (iterPhi_derUnip ψ n₂ n' hn j (MRep.phiM k ψ τ)) ?_
    intro e₁
    have hnj : n₂ ≤ n' + j := hn.trans (Nat.le_add_right n' j)
    refine Nonempty.elim (GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ (n' + j) n₂ hnj τ.V τ.ρ) ?_
    intro e₂
    exact ⟨e₁.trans e₂⟩

theorem phi_vanish (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V) (hs : IsSmooth π)
    (hlow : ∀ m < n + 1, Subsingleton (TwJacquet π (derUnip k (n + 1 + j + 1) m) (derChar k ψ (n + 1 + j + 1) m))) :
    Subsingleton (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n)) := by
  by_contra hcon
  have hnt : Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n)) :=
    not_subsingleton_iff_nontrivial.1 hcon
  have hT := isSmooth_iterPhi ψ (n + 1) j (resM k π) (isSmooth_resM hs)
  obtain ⟨m, hm, h⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hc h1 n _ (phiMinus k ψ (iterPhi k ψ j (resM k π)).ρ)
    (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hT) hnt
  obtain ⟨e₂⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ n m hm _ (iterPhi k ψ j (resM k π)).ρ
  obtain ⟨e₁⟩ := iterPhi_derUnip ψ m (n + 1) (by omega) j (resM k π)
  have h3 : Nontrivial (TwJacquet (resM k π).ρ (derUnipM k (n + 1 + j) m) (derCharM k ψ (n + 1 + j) m)) :=
    (e₂.trans e₁).symm.toEquiv.nontrivial
  have h4 := (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + 1 + j) m V π)).1 h3
  exact not_subsingleton_iff_nontrivial.2 h4 (hlow m (by omega))

theorem deriv_nontrivial (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (h : Nontrivial (TwJacquet π (derUnip k (n + 1 + j + 1) (n + 1)) (derChar k ψ (n + 1 + j + 1) (n + 1)))) :
    Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1) := by
  obtain ⟨e⟩ := GlobalTheory.T.twisted_jacquet_iterated_phi_equiv k ψ (n + 1) j (resM k π)
  have h2 := (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + 1 + j) (n + 1) V π)).2 h
  exact e.toEquiv.nontrivial

theorem detChar_zero {n : ℕ} (g : GL (Fin n) k) : ((detChar (Fin n) (absPow k ((0 : ℕ) : ℂ)) g : ℂˣ) : ℂ) = 1 := by
  have : absPow k ((0 : ℕ) : ℂ) = 1 := by
    rw [Nat.cast_zero, absPow_zero]
  rw [this]
  simp [detChar]



theorem pair_iter (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n : ℕ) : ∀ (j s : ℕ) (τ τ' : MRep k (n + 1 + j)),
    IsSmooth τ.ρ → IsSmooth τ'.ρ → ∀ B : τ.V →ₗ[ℂ] τ'.V →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1 + j)) v v', B (τ.ρ p v) (τ'.ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    Subsingleton (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k (n + 1)) (mirChar k ψ n)) →
    ∃ B' : TwJacquet (iterPhi k ψ j τ).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ]
        TwJacquet (iterPhi k ψ⁻¹ j τ').ρ (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (derivM k ψ j τ g w) (derivM k ψ⁻¹ j τ' g w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + j : ℕ) : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0)
  | 0, s, τ, τ', hs, hs', B, hB, hn, hv =>
    GlobalTheory.T.invariant_pairing_mirabolic_vanishing k ψ hc h1 n s τ.V τ'.V τ.ρ τ'.ρ hs hs' B hB hn hv
  | j + 1, s, τ, τ', hs, hs', B, hB, hn, hv => by
    refine Exists.elim (GlobalTheory.T.invariant_pairing_mirabolic_smooth k ψ hc h1
      (n + 1 + j) s τ.V τ'.V τ.ρ τ'.ρ hs hs' B hB hn) ?_
    rintro B₁ ⟨hB₁, hn₁⟩
    refine Exists.elim (pair_iter ψ hc h1 n j (s + 1) (MRep.phiM k ψ τ) (MRep.phiM k ψ⁻¹ τ')
      (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hs) (GlobalTheory.T.smooth_phi_minus k ψ⁻¹ _ _ _ hs') B₁ hB₁ hn₁ hv) ?_
    rintro B₂ ⟨hB₂, hn₂⟩
    refine ⟨B₂, fun g w w' => ?_, hn₂⟩
    have e : s + (j + 1) = s + 1 + j := by omega
    rw [e]
    exact hB₂ g w w'



theorem pair_deriv (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V V' : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (π' : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V') (hs : IsSmooth π) (hs' : IsSmooth π')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π g v) (π' g v') = B v v') (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (hv : Subsingleton (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n))) :
    ∃ B' : TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ]
        TwJacquet (iterPhi k ψ⁻¹ j (resM k π')).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (GlobalTheory.BZMir.deriv k ψ j π g w) (GlobalTheory.BZMir.deriv k ψ⁻¹ j π' g w') =
        ((detChar (Fin (n + 1)) (absPow k (j : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  have hB0 : ∀ (p : Mir k (n + 1 + j)) v v', B ((resM k π).ρ p v) ((resM k π').ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k ((0 : ℕ) : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v' := by
    intro p v v'
    rw [detChar_zero, one_mul]
    exact hB (p : GL (Fin (n + 1 + j + 1)) k) v v'
  obtain ⟨B', h2, h3⟩ := pair_iter ψ hc h1 n j 0 (resM k π) (resM k π') (isSmooth_resM hs) (isSmooth_resM hs') B
    hB0 hn hv
  refine ⟨B', fun g w w' => ?_, h3⟩
  have := h2 g w w'
  rwa [Nat.zero_add] at this

end Proofs
end GlobalTheory.CompanionTheory.BZCuspPair
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun

namespace GlobalTheory.CompanionTheory.SatakeBridge

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem satBridge : PositivityTheory.SphericalProduct.SatBridge := by
  intro E _ _ w n V _ _ ρ hs hi α
  constructor
  · exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n V ρ α
  · intro h
    obtain ⟨x, hx⟩ := h.exists_vec
    exact GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨hs, hi⟩ α hx

end GlobalTheory.CompanionTheory.SatakeBridge

end
end

section


theorem _root_.GlobalTheory.T.finite_euler_product_of : PositivityTheory.Rg.BcB.G8.Fin.EulerFinOf' := by
  first | exact @GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | exact GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | (intros; apply GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_reindexing : PositivityTheory.Rg.BcB.G8.Fin.Reindex := by
  first | exact @GlobalTheory.CompanionTheory.SecReindex.reindex | exact GlobalTheory.CompanionTheory.SecReindex.reindex | (intros; apply GlobalTheory.CompanionTheory.SecReindex.reindex <;> assumption)
end

section


theorem _root_.GlobalTheory.T.local_comparison_inert : PositivityTheory.Rg.BcB.G8.Fin.LocCompareInert := by
  first | exact @GlobalTheory.CompanionTheory.LocInert.locCompareInert | exact GlobalTheory.CompanionTheory.LocInert.locCompareInert | (intros; apply GlobalTheory.CompanionTheory.LocInert.locCompareInert <;> assumption)
end

section


theorem _root_.GlobalTheory.T.local_comparison_of : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  first | exact @GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf | exact GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf | (intros; apply GlobalTheory.CompanionTheory.LocCompareHalves.locCompareOf <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical


theorem _root_.GlobalTheory.T.eventually_of_section_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ P : PlF E → Prop,
  (∀ᶠ w : {w : Pl E // w ∈ S} in cofinite, P (w.1.under (𝓞 (maximalRealSubfield E)))) → ∀ᶠ v in cofinite, P v := by
  first | exact @GlobalTheory.CompanionTheory.LocHypSec.eventually_cofinite_of_section | exact GlobalTheory.CompanionTheory.LocHypSec.eventually_cofinite_of_section | (intros; apply GlobalTheory.CompanionTheory.LocHypSec.eventually_cofinite_of_section <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_restriction_vanishing : PositivityTheory.Rg.BcB.G8.Fin.RestrV := by
  first | exact @GlobalTheory.CompanionTheory.EulerV.main | exact GlobalTheory.CompanionTheory.EulerV.main | (intros; apply GlobalTheory.CompanionTheory.EulerV.main <;> assumption)
end
