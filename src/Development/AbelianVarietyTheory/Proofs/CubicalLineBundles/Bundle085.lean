module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle083
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle064
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem isLieComb_of_two_pullbacks {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {X : Scheme.{0}}
    {x : Sp R ⟶ X} {x' : Sp S ⟶ X} (hx : x' = spMap f ≫ x) {G : Over X} [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀]
    {G' : Over (Sp S)} [GrpObj G'] {φ : G₀.left ⟶ G.left} {φ' : G'.left ⟶ G.left}
    (h : IsGrpPullback G₀ G x φ) (h' : IsGrpPullback G' G x' φ') {n n' : ℕ} (hn : n' = n)
    {c : Fin n → R} {v : Fin n → (epsR R ⟶ G₀)} {w : epsR R ⟶ G₀} (hc : IsLieComb c v w)
    {v' : Fin n' → (epsR S ⟶ G')} {w' : epsR S ⟶ G'}
    (hv : ∀ i, (v' i).left ≫ φ' = spMap (Formalism.L2.Pj.dualMap f) ≫ (v (i.cast hn)).left ≫ φ)
    (hw : w'.left ≫ φ' = spMap (Formalism.L2.Pj.dualMap f) ≫ w.left ≫ φ) :
    IsLieComb (fun i => f (c (i.cast hn))) v' w' := by
  subst hn
  subst hx
  have hw0 : φ' ≫ G.hom = (G'.hom ≫ spMap f) ≫ x := by rw [Category.assoc]; exact h'.1.w
  have hψ1 : h.1.lift φ' (G'.hom ≫ spMap f) hw0 ≫ φ = φ' := h.1.lift_fst _ _ _
  have hψ2 : h.1.lift φ' (G'.hom ≫ spMap f) hw0 ≫ G₀.hom = G'.hom ≫ spMap f := h.1.lift_snd _ _ _
  have hG : IsGrpPullback G' G₀ (spMap f) (h.1.lift φ' (G'.hom ≫ spMap f) hw0) :=
    IsGrpPullback.cancel h (IsGrpPullback.congr h' rfl hψ1.symm) hψ2
  have he : (algebraMap S (DualNumber S)).comp f = (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) := by
    clear h h' hv hw hc hG hψ1 hψ2 hw0
    first
    | exact RingHom.ext fun r => rfl
    | (ext r <;> simp [Chart.dualMapR] <;> rfl)
    | (ext r <;> simp [Chart.dualMapR] <;> erw [TrivSqZeroExt.algebraMap_eq_inl] <;> simp <;> done)
    | (ext r <;> simp [Chart.dualMapR] <;> simp [Algebra.algebraMap_eq_smul_one] <;> done)
    | (ext r
       · simp [Chart.dualMapR]
         show f r = f r
         rfl
       · simp [Chart.dualMapR]
         show (0 : S) = f 0
         simp)
  refine ReciprocityTheory.ChartRestriction.G.Chart.comb_baseChange f hG hc (fun i => ?_) ?_
  · apply h.1.hom_ext
    · rw [Category.assoc, hψ1, hv i, Category.assoc]
      rfl
    · rw [Category.assoc, hψ2, ← Category.assoc, Over.w (v' i), Category.assoc, Over.w (v i)]
      first
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← spMap_comp, ← spMap_comp, he])
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, he])
      | (unfold epsR; simp only [Over.mk_hom, ← spMap_comp, he])
      | (show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
         rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he])
  · apply h.1.hom_ext
    · rw [Category.assoc, hψ1, hw, Category.assoc]
      rfl
    · rw [Category.assoc, hψ2, ← Category.assoc, Over.w w', Category.assoc, Over.w w]
      first
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← spMap_comp, ← spMap_comp, he])
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, he])
      | (unfold epsR; simp only [Over.mk_hom, ← spMap_comp, he])
      | (show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
         rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he])

theorem hermForm_map_conj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (Hm.map (starRingEnd ℂ)) (fun i => starRingEnd ℂ (z i)) (fun i => starRingEnd ℂ (w i)) =
      starRingEnd ℂ (hermForm Hm z w) := by
  unfold hermForm

  simp [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]

theorem isMetricAt_of_dim {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (Φ : FibKey Xo ℂ x) (g : ℕ) (hg : Φ.key.P.g = g) (u : HolUnif Φ.key.P.A Φ.key.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ))
    (w : ∀ b : E →+* ℂ, Fin (Dw.mult b) → (epsR ℂ ⟶ Φ.key.P.A))
    (W : ∀ b : E →+* ℂ, Fin (Dw.mult b) → Fin g → ℂ)
    (h : SecTie Φ.m Φ.th s ∧ u.IsAH Hm χ ∧ u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧
      IsAddFundamentalDomain u.Λ Fd volume ∧
      N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧
      (∀ b i, (w b i).left ≫ Φ.m.φ = uu b i ∧ u.IsDiff (W b i) (w b i)) ∧
      ∀ b i k, Gr b i k = Real.pi * hermForm Hm (W b k) (W b i)) : IsMetricAt x s uu N Gr := by
  subst hg
  exact ⟨Φ, u, Hm, χ, θ, Fd, w, W, h⟩

theorem isMetricAt_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (hpq : 1 ≤ Dw.p + Dw.q) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x'))
    (uu uu' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (hx : x' = spMap (starRingEnd ℂ) ≫ x) (hs : SecBC (starRingEnd ℂ) 1 x x' s s') (hgen : SecGen x' s')
    (ht : ∀ τ i, IsTanAt x (uu τ i)) (ht' : ∀ τ i, IsTanAt x' (uu' τ i))
    (hu : ∀ τ i, uu' τ i = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ uu τ i)
    (h : IsMetricAt x s uu N Gr) : IsMetricAt x' s' uu' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, hT, hAH, hRig, hFn, hFd, hN, hw, hGr⟩ := h
  obtain ⟨Φ0⟩ := GlobalTheory.T.universalTripleFibreKeyData_nonempty_field E H Dw l Xo ℂ x' hpq
  have hNZ : SecNZ x' s' := GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ x' s' hgen
  obtain ⟨-, hex, huniq⟩ := GlobalTheory.T.rigidifiedSectionCorrespondence_existsUnique_nonvanishing E H Dw l Xo ℂ x' Φ0.T.t Φ0.m
  obtain ⟨th, hth⟩ := hex s'
  have hne := ((huniq th s' hth).2).1 hNZ
  obtain ⟨hg, v', hv', hKey, hvrel⟩ := GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback E H Dw l Xo ℂ ℂ (starRingEnd ℂ) x x' Φ
    { Φ0 with th := th, th_ne := hne } s s' hx hT hth hs
  obtain ⟨u', χ', θ', Fd', hAH', hRig', hFn', hFd', hNeq, hdiff⟩ :=
    GlobalTheory.T.exists_uniformisation_of_complexConjugate_keyDatum Φ.key _ hKey hg _ u Hm χ θ Fd ⟨hAH, hRig, hFn, hFd⟩
  have hpb : ∀ (Ψ : FibKey Xo ℂ x'), IsGrpPullback Ψ.T.t.G Xo.univ.t.G x' Ψ.m.φ := by
    intro Ψ
    exact Ψ.m.cart
  have hpb0 : IsGrpPullback Φ.T.t.G Xo.univ.t.G x Φ.m.φ := Φ.m.cart
  have hcomb : ∀ b i, ∃ cf : Fin Φ.T.g → ℂ, IsLieComb cf Φ.v (w b i) := by
    intro b i
    have hTB := ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x _ Φ.m.φ hpb0).2 _ Φ.v).1 Φ.basis
    obtain ⟨a, ha, -⟩ := hTB.2 _ (ht b i)
    refine ⟨a, (ReciprocityTheory.ChartRestriction.G.Chart.comb_push hpb0 a Φ.v (w b i)).2 ?_⟩
    rw [← (hw b i).1] at ha
    exact ha
  choose cf hcf using hcomb
  have hw' : ∀ b i, ∃ w' : epsR ℂ ⟶ Φ0.T.t.G, w'.left ≫ Φ0.m.φ = uu' b i :=
    fun b i => (GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x' Φ0.T.t.G Φ0.m.φ (hpb Φ0)).1 _ (ht' b i)
  choose w' hw'e using hw'
  refine isMetricAt_of_dim x' s' uu' N _ _ _ hg u' (Hm.map (starRingEnd ℂ)) χ' θ' Fd' w'
    (fun b i k => starRingEnd ℂ (W b i k)) ⟨hth, hAH', hRig', hFn', hFd', ?_, fun b i => ⟨hw'e b i, ?_⟩, fun b i k => ?_⟩
  · rw [hN, hNeq]
  · exact hdiff (cf b i) (w b i) (w' b i) (W b i) (hcf b i)
      (isLieComb_of_two_pullbacks (starRingEnd ℂ) hx hpb0 (hpb _) hg (hcf b i) hvrel
        (by rw [hw'e, hu, (hw b i).1])) (hw b i).2
  · rw [Matrix.map_apply, hGr, map_mul, hermForm_map_conj]
    simp

theorem scal_one_mul_sec {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) (i : (PPx x).ι) :
    scal x 1 i * s.f i = s.f i := by
  simp only [scal]
  first
  | rw [map_one, one_mul]
  | simp [Out.liftFun]

theorem isMetric_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))) (N : ℝ) (Gr : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), 1 ≤ Dw.p + Dw.q → FrMap (FrameNorm.conjAlg σ) y y' → IsMetric y N Gr → IsMetric y' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  intro E _ _ _ H Dw l Xo c σ y y' N Gr hpq hF hM
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hF
  unfold IsMetric at hM ⊢
  refine isMetricAt_conj hpq y.x y'.x y.s y'.s y.u y'.u N Gr hx ?_ y'.gen y.tan y'.tan hu hM
  refine ⟨pm, h1, h2, fun i h => ?_⟩
  have h4 := h3 i h
  first
  | exact (congrArg _ (scal_one_mul_sec (S := ℂ) y.x y.s i)).trans h4
  | exact (congrArg _ (scal_one_mul_sec y.x y.s i)).trans h4
  | (convert h4 using 2; exact scal_one_mul_sec (S := ℂ) y.x y.s i)
  | (convert h4 using 2; simp only [scal]; first | rw [map_one, one_mul] | simp [Out.liftFun])
  | (erw [scal_one_mul_sec]; exact h4)

end GlobalTheory.LamT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem exists_frPt_of_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (e : (Σ b : E →+* ℂ, Fin (Dw.mult b)) ≃ Fin Φ.T.g) (U : Matrix (Fin Φ.T.g) (Fin Φ.T.g) K) (w : Fin Φ.T.g → (epsR K ⟶ Φ.T.t.G)), x ≫ Xo.s = sOf c K → U.det ≠ 0 → (∀ k, IsLieComb (U k) Φ.v (w k)) → (∀ τ i, IsEigAt c τ ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ)) → ∃ y : FrPt Xo c K, y.x = x ∧ SecTie Φ.m Φ.th y.s ∧ ∀ τ i, y.u τ i = (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ := by
  intro E _ _ _ H Dw l Xo c K _ _ x Φ e U w hx hU hw heig
  have hb : IsLieBasis w :=
    ((GlobalTheory.LieComb.lieComb_algebra K Φ.T.t.G Φ.T.g Φ.v Φ.basis.1).2.2.2.2 U w Φ.basis hw).2 hU.isUnit
  have ht : TanBasis x (fun i => (w i).left ≫ Φ.m.φ) :=
    ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo K x Φ.T.t.G Φ.m.φ Φ.m.cart).2 _ w).1 hb
  have htan : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsTanAt x ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ) :=
    fun τ i => ht.1 (e ⟨τ, i⟩)
  have hbas := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c K x
    (fun τ i => (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ) Φ.T.g e.symm htan heig).2 (by
      have : (fun j => (w (e ⟨(e.symm j).1, (e.symm j).2⟩)).left ≫ Φ.m.φ) = fun i => (w i).left ≫ Φ.m.φ :=
        funext fun j => congrArg (fun k => (w k).left ≫ Φ.m.φ) (e.apply_symm_apply j)
      exact this ▸ ht)
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.rigidifiedSectionCorrespondence_existsUnique_nonvanishing E H Dw l Xo K x Φ.T.t Φ.m
  obtain ⟨s, hs⟩ := h1 Φ.th
  have hgen : SecGen x s := GlobalTheory.Frames.secGen_of_secNZ GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo K x s
    ((h3 Φ.th s hs).2.2 Φ.th_ne)
  exact ⟨⟨x, hx, fun τ i => (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ, htan, heig, hbas, s, hgen⟩, rfl, hs, fun _ _ => rfl⟩

end GlobalTheory.LamT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.exists_isFramePolynomialOfRule_numberField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G := by
  first | exact @GlobalTheory.LamT.exists_isFrPoly | exact GlobalTheory.LamT.exists_isFrPoly | (intros; apply GlobalTheory.LamT.exists_isFrPoly <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.metric_change_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y y' : FrPt Xo c (CAt σ)) (N : ℝ) (Gr Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) (a : ℂ), a ≠ 0 → FrChg (S := CAt σ) (fun b => (Y b).transpose) a y y' → IsMetric y N Gr → IsMetric y' (‖a‖ ^ 2 * N) (fun b => (Y b).conjTranspose * Gr b * Y b) := by
  first | exact @GlobalTheory.MetricChange.isMetric_frChg | exact GlobalTheory.MetricChange.isMetric_frChg | (intros; apply GlobalTheory.MetricChange.isMetric_frChg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.unif_metric_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (ξ : ℝ), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (x : (U.X k).dom), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ) → (U.X k).IsOrtho x.1 → IsMetric (U.un k x) 1 (fun _ => ((2 * Real.pi * ξ : ℝ) : ℂ) • 1) := by
  first | exact @GlobalTheory.OrthoMetric.isMetric_of_isOrtho | exact GlobalTheory.OrthoMetric.isMetric_of_isOrtho | (intros; apply GlobalTheory.OrthoMetric.isMetric_of_isOrtho <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

theorem _root_.GlobalTheory.T.thetaLine_degree_and_heightLowerBound : (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi)) ∧ (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) := by
  first | exact @GlobalTheory.thetaDegree_and_lowerBound | exact GlobalTheory.thetaDegree_and_lowerBound | (intros; apply GlobalTheory.thetaDegree_and_lowerBound <;> assumption)
end
