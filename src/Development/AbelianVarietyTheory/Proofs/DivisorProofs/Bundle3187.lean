module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.rosatiBalanceFormalSum_mem_span_cubicalTheta : ∀ {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → GlobalTheory.TensBal.sig W A A' ∈ Submodule.span ℤ (Set.range fun p : GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r => GlobalTheory.TensBal.theta p.1 p.2.1 p.2.2) := by
  first | exact @GlobalTheory.TensBal.SpanPf.main | exact GlobalTheory.TensBal.SpanPf.main | (intros; apply GlobalTheory.TensBal.SpanPf.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.transported_generator_unique_globalFunctions_base : ∀ {X X' Y S₀ : Scheme.{0}} {M : LB X} {M' : LB X'}, M.IsLB → M'.IsLB → ∀ {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ} (w : LB.Iso M' (LB.LinComb M ψ δ)), w.IsGen → ∀ {K K₁ : Type} [Fintype K] [Fintype K₁] {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}, FormEq (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2) φ ε₁ → ∀ {t' : LB.Gen (LB.LinComb M' φ' ε)}, t'.IsGen → ∀ {t : LB.Gen (LB.LinComb M φ ε₁)}, t.IsGen → ∀ (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 _ → Function.Surjective p.appTop.hom → (∀ (y : S₀) (J : (S₀ ⟶ X) → M.ι) (J' : (S₀ ⟶ X') → M'.ι), Good M y J → Good M' y J' → (∏ a, GlobalTheory.TensBal.isoV w y J J' (e ≫ φ' a) ^ ε a) * val t' e y J' = val t e y J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J → Good M' z J' → (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' = val t r z J := by
  first | exact @GlobalTheory.TensBalUniq.iso_unique | exact GlobalTheory.TensBalUniq.iso_unique | (intros; apply GlobalTheory.TensBalUniq.iso_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isStronglyTrivial_cubicalThetaFinsupp_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), D.TauBimult → ∀ a b c : GlobalTheory.TensBal.Vec r, GlobalTheory.TensBal.Triv T (GlobalTheory.TensBal.theta a b c) := by
  first | exact @GlobalTheory.TensBal.triv_theta | exact GlobalTheory.TensBal.triv_theta | (intros; apply GlobalTheory.TensBal.triv_theta <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isStronglyTrivialFormalSumTensor_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (c c' : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T c' → GlobalTheory.TensBal.Triv T (c + c') := by
  first | exact @GlobalTheory.TensBal.triv_add | exact GlobalTheory.TensBal.triv_add | (intros; apply GlobalTheory.TensBal.triv_add <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.rosatiBalanceFormalSum_psiValues_eq_tauProduct : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), D.TauBimult → ∀ (A A' : Matrix (Fin r) (Fin r) ℤ) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ y y' : D'.X, ∏ v ∈ (GlobalTheory.TensBal.sig W A A').support, val (D.psi (GlobalTheory.TensBal.vecLat T v y y')) (𝟙 _) z J ^ (-(GlobalTheory.TensBal.sig W A A' v)) = ∏ a, GlobalTheory.TensBal.qv T z J (GlobalTheory.TensBal.rosLat T A A' y y' a) ^ (-(rosatiε a)) := by
  first | exact @GlobalTheory.TensBalLat.main | exact GlobalTheory.TensBalLat.main | (intros; apply GlobalTheory.TensBalLat.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

def chartPullCompOf {X Y Y' : Scheme.{0}} (L : LB X) (g : Y ⟶ X) (h : Y' ⟶ Y) (k : Y' ⟶ X) (e : h ≫ g = k) :
    ChartPull (L.pull k) (L.pull g) h where
  idx J := J
  le J y hy := by
    subst e
    exact mem_pull.2 (by simpa using mem_pull.1 hy)
  g y J J' hj hj' := by
    subst e
    have hj₁ : h y ∈ (L.pull g).U J := mem_pull.2 (by simpa using mem_pull.1 hj)
    have hj₁' : h y ∈ (L.pull g).U J' := mem_pull.2 (by simpa using mem_pull.1 hj')
    refine (gm_pull_g L (h ≫ g) (𝟙 _) y J J' hj hj').trans ?_
    refine Eq.trans ?_ (gm_pull_g L g h y J J' hj₁ hj₁').symm
    rw [Category.id_comp]

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem descAt_of_isPullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁)
    (Q : DegPre V) (D : DegPre V₁), IsPullDeg ρ Q D → D.P.g = Q.P.g ∧ ∀ (K : Type) [Field K] (ev : V₁ →+* K)
    (k₀ : Subfield K), DescAt D ev k₀ → DescAt Q (ev.comp ρ) k₀ := by
  intro V V₁ _ _ _ _ ρ Q D p
  have gp := pull_grp p
  refine ⟨H1.dim_unique _ D.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback gp.1 Q.P.smoothDim)
    (eSec D.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V₁)), ?_⟩
  intro K _ ev k₀ hd
  obtain ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hab, hM, h₁, h₀, hw, hc⟩ := hd
  have hL : LBIso (Q.P.L.pull (π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)))) (M₀.pull π₀) :=
    LBIso.trans (pull_isLB Q.P.isLB _) (pull_isLB D.P.isLB _) (pull_isLB hM _)
      (LBIso.chartPull (chartPullCompOf Q.P.L _ π₁ _ rfl) (chartPullPull D.P.L π₁)
        (LBIso.symm ⟨p.w, p.w_gen⟩)) ⟨w, hw⟩
  obtain ⟨w', hw'⟩ := hL
  refine ⟨B₀, i₁, i₂, M₀, fun a => c₀ (p.xe.symm a), B', i₃, π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)),
    π₀, w', fun a => c' (p.xe.symm a), hab, hM, ?_, h₀, hw', fun a => ⟨(hc _).1, ?_, (hc _).2.2⟩⟩
  · exact (h₁.comp gp).congr (spMap_comp_ringHom ρ ev).symm rfl
  · have e₁ := (hc (p.xe.symm a)).2.1
    have e₂ := p.c_pr (p.xe.symm a)
    rw [AddEquiv.apply_symm_apply] at e₂
    rw [← Category.assoc, e₁, Category.assoc, e₂, ← Category.assoc, spMap_comp_ringHom]

end GlobalTheory.USep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GFib

theorem endo_torsion_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → Y.pt ≫ q = X.M.pt → ∀ z : X.M.Z, X.S.TT X.M z ≤ X.S.HH X.M z → ∃ (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)), GlobalTheory.UPoinc.GFib.IsEndoExt X wi FinalForm f ∧ GlobalTheory.UPoinc.GFib.IsTorsExt X wi FinalForm q z gγ := by
  intro E _ _ _ H Dw l Xo cf C X wi Y U₀ EE FinalForm q hO _ hq z hTH
  have hU : (U₀ : Set Y.Z).Nonempty := hO.ne
  have hr : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Y.top_le_preimage_pt hU (x := w) trivial
  let x : Sp X.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hr
  have hx : x ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x ≫ FinalForm.u₀ = spMap X.S.R.val.toRingHom := FinalForm.u₀_gen x hx
  have hwx : wi.α ≫ X.ρ.P.A.hom = (wi.G.hom ≫ x) ≫ FinalForm.u₀ := by
    rw [Category.assoc, hxu]; exact wi.hα.1.w
  let ν : wi.G.left ⟶ pullback X.ρ.P.A.hom FinalForm.u₀ := pullback.lift wi.α (wi.G.hom ≫ x) hwx
  have hν₁ : ν ≫ pullback.fst _ _ = wi.α := pullback.lift_fst _ _ _
  have hν₂ : ν ≫ pullback.snd _ _ = wi.G.hom ≫ x := pullback.lift_snd _ _ _
  let ψ : wi.G.left ⟶ FinalForm.G.left := ν ≫ FinalForm.φ
  have hQ := isGrpPullback_pullback X.ρ.P.A FinalForm.u₀
  have gα : IsGrpPullback wi.G X.ρ.P.A (x ≫ FinalForm.u₀) (ν ≫ pullback.fst X.ρ.P.A.hom FinalForm.u₀) :=
    wi.hα.congr hxu.symm hν₁.symm
  have gν : IsGrpPullback wi.G ((Over.pullback FinalForm.u₀).obj X.ρ.P.A) x ν := hQ.cancel gα hν₂
  have gW : IsGrpPullback wi.G FinalForm.G Y.pt ψ := (gν.comp FinalForm.cart).congr hx rfl

  have hxu' : ∀ (x₀ : Sp X.Ω₁ ⟶ U₀.toScheme), x₀ ≫ U₀.ι = Y.pt → x₀ = x := fun x₀ h₀ =>
    (cancel_mono U₀.ι).1 (h₀.trans hx.symm)

  let P := (Over.pullback Y.pt).obj FinalForm.G
  have gA := isGrpPullback_pullback FinalForm.G Y.pt
  let k : P.left ⟶ wi.G.left := gW.1.lift (pullback.fst FinalForm.G.hom Y.pt) P.hom pullback.condition
  have hk₁ : k ≫ ψ = pullback.fst FinalForm.G.hom Y.pt := gW.1.lift_fst _ _ _
  have hk₂ : k ≫ wi.G.hom = P.hom := gW.1.lift_snd _ _ _
  have gk : IsGrpPullback P wi.G (𝟙 _) k :=
    gW.cancel (gA.congr (Category.id_comp _).symm hk₁.symm) (by rw [hk₂, Category.comp_id])
  haveI : IsIso k := gk.1.isIso_fst_of_isIso

  have hE : ∀ a : 𝓞 E, ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₁ : wi.G ⟶ wi.G,
      e₁.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e₁.left ≫ ψ = ψ ≫ F.left := by
    intro a
    obtain ⟨e₀, he₀, pa⟩ := GlobalTheory.SymBaseChange.exists_endo wi.hβ (Xo.univ.t.act.act a)
    have he₀l : e₀.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left := by
      have := congrArg (fun z => z.left) (pa (𝟙 _))
      simpa [pushPt] using this
    haveI := he₀
    obtain ⟨w', hw', pw⟩ := GlobalTheory.SymBaseChange.exists_endo gk e₀
    have hw'l : w'.left ≫ k = k ≫ e₀.left := by
      have := congrArg (fun z => z.left) (pw (𝟙 _))
      simpa [pushPt] using this
    obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
    have hF' : w'.left ≫ pullback.fst FinalForm.G.hom Y.pt = pullback.fst FinalForm.G.hom Y.pt ≫ F.left := by
      rw [← hFw]
      simp only [Over.pullback_map_left, pullback.lift_fst]
    refine ⟨F, hF, fun e₁ he₁ => ?_⟩
    have h10 : e₁ = e₀ := GlobalTheory.TorusPart.hom_ext_of_pullback wi.hβ (he₁.trans he₀l.symm)
    subst h10
    have e1 : k ≫ e₁.left ≫ ψ = w'.left ≫ k ≫ ψ := by rw [← Category.assoc, ← hw'l, Category.assoc]
    rw [← cancel_epi k, e1, hk₁, hF', ← hk₁, Category.assoc]
  choose f hf using hE
  have hT : ∀ t : X.S.TT X.M z, ∃ g : Over.mk Y.pt ⟶ FinalForm.G, g ^ (X.S.r * X.S.N) = 1 ∧
      (∀ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.G.hom = 𝟙 _ →
        w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt (t : X.S.Gam)).left → w ≫ ψ = g.left) ∧
      ∀ w, q.base w = z → ExtNear g w := by
    intro t
    set b : X.S.Gam := (t : X.S.Gam) with hbdef
    have hb : (spMap X.S.R.val.toRingHom ≫ (X.ρ.pt b).left) ≫ X.ρ.P.A.hom = 𝟙 _ ≫ spMap X.S.R.val.toRingHom := by
      rw [Category.assoc, Over.w (X.ρ.pt b)]; simp
    let w₀ := wi.hα.1.lift _ _ hb
    have hw₁ : w₀ ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt b).left := wi.hα.1.lift_fst _ _ _
    have hw₂ : w₀ ≫ wi.G.hom = 𝟙 _ := wi.hα.1.lift_snd _ _ _
    let sec0 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G := Over.homMk w₀ hw₂
    let V : Over.mk Y.pt ⟶ Over.mk (𝟙 (Sp X.Ω₁) ≫ Y.pt) := Over.homMk (𝟙 _) (by simp)
    let gγ : Over.mk Y.pt ⟶ FinalForm.G := V ≫ pushPt gW.1.w sec0
    have hgl : gγ.left = w₀ ≫ ψ := by simp [gγ, V, pushPt, sec0]
    refine ⟨gγ, ?_, ?_, ?_⟩
    · have h0 : X.ρ.pt 0 = 1 := by
        have := X.ρ.pt_add 0 0
        rw [add_zero] at this
        exact mul_eq_left.1 this.symm
      have hpt : ∀ n : ℕ, (X.ρ.pt b) ^ n = X.ρ.pt (n • b) := by
        intro n
        induction n with
        | zero => simp [h0]
        | succ k ih => rw [pow_succ, ih, ← X.ρ.pt_add, succ_nsmul]
      have hrN : (X.S.r * X.S.N) • b = 0 := by
        funext i
        simp
      let U : Over.mk (𝟙 (Sp X.Ω₁) ≫ spMap X.S.R.val.toRingHom) ⟶ baseOver (Sp X.S.R) :=
        Over.homMk (spMap X.S.R.val.toRingHom) (by simp)
      have hs : pushPt wi.hα.1.w sec0 = U ≫ X.ρ.pt b := by
        apply Over.OverMorphism.ext
        simp [pushPt, sec0, U, hw₁]
      have hsec : sec0 ^ (X.S.r * X.S.N) = 1 := by
        apply GlobalTheory.SymBaseChange.pushPt_injective wi.hα
        have e1 : pushPt wi.hα.1.w (sec0 ^ (X.S.r * X.S.N)) = (pushPt wi.hα.1.w sec0) ^ (X.S.r * X.S.N) :=
          map_pow (pushHom wi.hα _) sec0 _
        have e2 : pushPt wi.hα.1.w (1 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G) = 1 :=
          map_one (pushHom wi.hα _)
        have e3 : (U ≫ X.ρ.pt b) ^ (X.S.r * X.S.N) = U ≫ (X.ρ.pt b) ^ (X.S.r * X.S.N) :=
          (map_pow (preHom U) (X.ρ.pt b) _).symm
        have e4 : U ≫ (1 : baseOver (Sp X.S.R) ⟶ X.ρ.P.A) = 1 := map_one (preHom U)
        rw [e1, e2, hs, e3, hpt, hrN, h0, e4]
      have f1 : gγ ^ (X.S.r * X.S.N) = V ≫ (pushPt gW.1.w sec0) ^ (X.S.r * X.S.N) :=
        map_pow (preHom V) _ _
      have f2 : (pushPt gW.1.w sec0) ^ (X.S.r * X.S.N) = pushPt gW.1.w (sec0 ^ (X.S.r * X.S.N)) :=
        (map_pow (pushHom gW _) sec0 _).symm
      have f3 : pushPt gW.1.w (1 : Over.mk (𝟙 (Sp X.Ω₁)) ⟶ wi.G) = 1 :=
        map_one (pushHom gW _)
      have f4 : V ≫ (1 : Over.mk (𝟙 (Sp X.Ω₁) ≫ Y.pt) ⟶ FinalForm.G) = 1 := map_one (preHom V)
      rw [f1, f2, hsec, f3, f4]
    · intro w h1 h2
      have : w = w₀ := wi.hα.1.hom_ext (by rw [h2, hw₁]) (by rw [hw₂]; exact h1)
      rw [this, hgl]
    · intro w hw
      have hb' : b ∈ X.S.HH Y w := by
        rw [GlobalTheory.Poinc.HHFibre.HH_eq_of_hom X.o₁ X.Ω₁ X.S X.M Y q hq X.hasDiv w]
        have e : q w = z := hw
        rw [e]
        exact hTH t.2
      obtain ⟨W, h, hzW, hh, hx'⟩ := FinalForm.sec w b hb'
      refine ⟨W, h, hzW, hh, fun y hy => ?_⟩
      rw [hgl, hx' y (w₀ ≫ ν) hy ?_ ?_]
      · simp only [ψ, Category.assoc]
      · have := gW.1.w
        simp only [ψ] at this
        rw [Category.assoc, ← Category.assoc ν, this, ← Category.assoc, hw₂, Category.id_comp]
      · rw [Category.assoc, hν₁, hw₁]
  choose gγ hg using hT
  refine ⟨f, gγ, fun a => ⟨(hf a).1, ?_⟩, fun t => ⟨(hg t).1, ?_, (hg t).2.2⟩⟩
  · intro x₀ h₀ hw e₀ he
    have h' := hxu' x₀ h₀
    subst h'
    exact (hf a).2 e₀ he
  · intro x₀ h₀ hw w h1 h2
    have h' := hxu' x₀ h₀
    subst h'
    exact (hg t).2.1 w h1 h2

end GlobalTheory.UPoinc.GFib
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.TwistSum₂

theorem sumI_of_sumF_mul {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] {Ix : Type}
    (y : Ix → V) (v : V) (d : FractionRing V) (hd : d ≠ 0)
    (h : SumF (maximalIdeal V) (FractionRing V) (fun i => algebraMap V (FractionRing V) (y i) * d)
      (algebraMap V (FractionRing V) v * d)) :
    SumI (maximalIdeal V) y v := by
  classical
  have hsm : ∀ (r : V) (x : FractionRing V), r • x = algebraMap V (FractionRing V) r * x := Algebra.smul_def
  have hmod : (Module.compHom (FractionRing V) (algebraMap V (FractionRing V)) : Module V (FractionRing V)) =
      Algebra.toModule := Module.ext' _ _ fun r x => (Algebra.smul_def r x).symm
  unfold SumF at h
  rw [hmod] at h
  obtain ⟨N, hN, -, -, hS⟩ := h
  let P : Submodule V (FractionRing V) := N ⊔ Submodule.span V {d}
  haveI : Module.Finite V P := Module.Finite.iff_fg.mpr (hN.sup (Submodule.fg_span_singleton d))
  let L : Submodule V P := (Submodule.span V {d}).comap P.subtype
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal V) L
  refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS (n + k)
  refine ⟨S, fun T hT => ?_⟩
  set w : V := v - ∑ i ∈ T, y i with hw
  have e : algebraMap V (FractionRing V) w * d =
      algebraMap V (FractionRing V) v * d - ∑ i ∈ T, algebraMap V (FractionRing V) (y i) * d := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sub, map_sum, sub_mul, Finset.sum_mul]
  have h1 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ (n + k) • N := e ▸ hS T hT
  have hwP : algebraMap V (FractionRing V) w * d ∈ P :=
    Submodule.mem_sup_right (by rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d))
  let p : P := ⟨_, hwP⟩
  have hp1 : p ∈ maximalIdeal V ^ (n + k) • (⊤ : Submodule V P) :=
    (Submodule.mem_smul_top_iff _ P p).2 (Submodule.smul_mono le_rfl le_sup_left h1)
  have hp2 : p ∈ L := by
    show algebraMap V (FractionRing V) w * d ∈ Submodule.span V {d}
    rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  have hp3 : p ∈ maximalIdeal V ^ n • L := by
    have := (hk (n + k) (Nat.le_add_left _ _)).le ⟨hp1, hp2⟩
    rw [Nat.add_sub_cancel] at this
    exact Submodule.smul_mono le_rfl inf_le_right this
  have hp4 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ n • Submodule.span V {d} := by
    have := Submodule.mem_map_of_mem (f := P.subtype) hp3
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _) this
  obtain ⟨u, hu, hud⟩ := Submodule.mem_smul_span_singleton.1 hp4
  rw [hsm] at hud
  have hwu : w = u := IsFractionRing.injective V (FractionRing V) (mul_right_cancel₀ hd hud).symm
  rw [hwu]
  simpa using Submodule.smul_mem_smul hu (Submodule.mem_top : (1 : V) ∈ (⊤ : Submodule V V))

end GlobalTheory.Poinc.TwistSum₂

namespace GlobalTheory.Poinc.TwistSum₂

open GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem val_stalkHom (X₁ : Setup F W i) (z₁ : X₁.M.Z) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) [IsLocalHom ev] (a : X₁.M.Z.presheaf.stalk z₁) :
    X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (X₁.M.stalkHom z₁ a) =
      algebraMap V (FractionRing V) (ev a) := by
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have h : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) ⤳ z₁ := specializes_of_eq hc
  have e := RatModel.val_spMap_comp (algebraMap V (FractionRing V)) (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) h
    (X₁.M.stalkEquiv z₁ a)
  rw [RatModel.coe_stalkEquiv] at e
  refine e.trans (congrArg _ ?_)
  have hψ : Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) ≫
      X₁.M.Z.fromSpecStalk z₁ = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have heq : spMap ev = Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫
      Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) := by
    rw [← cancel_mono (X₁.M.Z.fromSpecStalk z₁), hψ]
  have hφψ := Spec.map_injective heq
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  exact (congrArg (fun φ => φ.hom a) hφψ).symm

theorem twistSum_of_sumF : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (e : ℕ), 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 → (∀ mu, ∃ a : X₁.S.Gam, 𝔪.YY a mu) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) → SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) → TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ C lab T sg c τ χ e hθ hY hχ hS
  intro zt h hzt hh wt hwt
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have hsp : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₁.M) (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.closedPoint (FractionRing V)))
  have hgen : (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) ⤳ z₁ := by
    have h1 : (jK V) (closedPoint (FractionRing V)) ⤳ closedPoint V := IsLocalRing.specializes_closedPoint _
    have h2 := h1.map (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁).continuous
    rw [hc] at h2
    exact h2
  have hO : ∀ s, X₁.M.stalkHom z₁ s ∈
      X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := fun s =>
    RatModel.O_le_of_specializes hgen (X₁.M.stalkEquiv z₁ s).2
  have hR : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := 𝔪.reg
  have hyK : ∀ (a : X₁.Ω₁) (ha : a ∈ X₁.S.R), 𝔪.yK ⟨a, ha⟩ = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a :=
    fun a ha => 𝔪.yK_eq ⟨a, ha⟩
  have hyA : ∀ b : X₁.o₁, 𝔪.yK (algebraMap X₁.o₁ X₁.S.R b) =
      X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (algebraMap X₁.o₁ X₁.Ω₁ b) := fun b => by
    rw [𝔪.yK_eq, Subalgebra.coe_algebraMap]
  have hzt' : algebraMap V (FractionRing V) (ev zt) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := by
    rw [← val_stalkHom X₁ z₁ ev, hzt, hyA]
  have hth0 : X₁.S.th x₀ ≠ 0 := by
    intro h0
    apply hθ
    rw [hyK, h0, RatModel.val_zero]
  have hh' : algebraMap V (FractionRing V) (ev h) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ =
      𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩ := by
    rw [← val_stalkHom X₁ z₁ ev, hyA, hyK, hyK, ← RatModel.val_mul hsp (hO h) (hR _ (X₁.S.th_mem x₀)),
      ← RatModel.val_mul hsp (hR _ (Subalgebra.algebraMap_mem _ _)) (hR _ (X₁.S.th_mem _)), hh,
      div_mul_cancel₀ _ hth0]
  have hterm : ∀ mu : Fin 8 → X, ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) *
      (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) =
      algebraMap V (FractionRing V) (ev zt ^ (wt mu).val * T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro mu
    obtain ⟨a, ha⟩ := hY mu
    rw [hχ a mu ha, ← hwt a mu ha, pow_mul, map_pow, map_pow, ← hzt', map_mul, map_pow]
    ring
  refine TwistSum₂.sumI_of_sumF_mul _ _ _ hθ ?_
  convert hS using 1
  · funext mu
    exact (hterm mu).symm

end GlobalTheory.Poinc.TwistSum₂
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_iso_uniformisation_translate_orderTwo : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∃ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen ∧ ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left)) := by
  first | exact @GlobalTheory.MumCmp.exists_iso_twist_of_translate | exact GlobalTheory.MumCmp.exists_iso_twist_of_translate | (intros; apply GlobalTheory.MumCmp.exists_iso_twist_of_translate <;> assumption)
end
