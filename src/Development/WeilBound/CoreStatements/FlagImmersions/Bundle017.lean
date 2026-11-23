module

public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle091
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle105
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceA
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceB
public import Development.WeilBound.CoreStatements.FlagImmersions.Transport
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle004

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem range_sub_iff {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : Set X) : Set.range y ⊆ U ↔ centre y ∈ U := by
  refine ⟨fun h => h ⟨_, rfl⟩, ?_⟩
  rintro h _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact h

theorem mem_of_period {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hty : IsTypeFn H D.p D.q ty) (j : c.F →+* ℂ) {U : Set (Xo.XF c)} (hU : IsClopen U) (i : Fin F.n)
    {P P' : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    {x x' : Sp ℂ ⟶ Xo.XF c} (hx1 : x ≫ pullback.fst _ _ = F.u i P) (hx2 : x ≫ pullback.snd _ _ = spMap j)
    (hx1' : x' ≫ pullback.fst _ _ = F.u i P') (hx2' : x' ≫ pullback.snd _ _ = spMap j) (hx : centre x ∈ U) :
    centre x' ∈ U := by
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  by_contra hn
  let W : (Xo.XF c).Opens := ⟨U, hU.isOpen⟩
  let W' : (Xo.XF c).Opens := ⟨Uᶜ, hU.compl.isOpen⟩
  obtain ⟨t, -, ht, ht'⟩ := hBc.isPreconnected _ _ (hhol W 0).1 (hhol W' 0).1
    (fun t ht => by
      by_cases h : centre (y t) ∈ U
      · exact Or.inl ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W from h)⟩
      · exact Or.inr ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W' from h)⟩)
    ⟨b, hb, hb, GagaRat.top_le_of_centre_mem (show centre (y b) ∈ W from e ▸ hx)⟩
    ⟨b', hb', hb', GagaRat.top_le_of_centre_mem (show centre (y b') ∈ W' from e' ▸ hn)⟩
  exact (GagaRat.centre_mem ht'.2 : centre (y t) ∈ W') (GagaRat.centre_mem ht.2 : centre (y t) ∈ W)

theorem over_const [NumberField c.F] {m : ℕ} {T : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.XF c)}
    (hTc : IsPreconnected T) (hy : IsHolTo T y) {b b' : Fin m → ℂ} (hb : b ∈ T) (hb' : b' ∈ T) :
    y b ≫ pullback.snd _ _ = y b' ≫ pullback.snd _ _ := by
  have hemb : ∀ p : Sp ℂ ⟶ Xo.XF c, ∃ κ : c.F →+* ℂ, p ≫ pullback.snd _ _ = spMap κ := fun p =>
    ⟨(Spec.preimage (p ≫ pullback.snd _ _)).hom, by
      unfold spMap
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  choose κ hκy using fun b => hemb (y b)
  have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T := fun r => by
    have h3 := (GagaRat.isHolTo_comp (pullback.snd _ _) hy ⊤ ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv (r : c.F))).2
    have hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ pullback.snd _ _) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (r : c.F) = valAt' (y b ≫ pullback.snd _ _) ⊤ _
    rw [hκy b]
    exact (PullbackSections.valAt'_spMap (κ b) (r : c.F)).symm
  rw [hκy, hκy, GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected hTc κ hd hb hb']

theorem periodOf : PeriodOf := by
  intro hG E _ _ _ H D l Xo c _ Y U Z hp hq hU _ hgeom
  classical
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := hN E H D l Xo (algebraMap (KA l) ℂ) g ty (by omega) rfl hty
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hsm : SmoothOfRelativeDimension D.dim s :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D.dim).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have hsm' : Smooth s := SmoothOfRelativeDimension.smooth D.dim s
  haveI := Y.jQ_open
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  haveI : IsPreimmersion Y.j := by
    show IsPreimmersion (Y.jQ ≫ pullback.fst _ _)
    infer_instance
  have hξ : IsCptGen Z.ξ₀ := GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ Y.j s hsm' rfl Z.gen (Y.j.stalkMap_surjective _)
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  have hcl : ConstClosed c.F Z.Ω := by
    rintro a ⟨f, hf, hfa⟩
    obtain ⟨x, hx⟩ := hgeom a ⟨f, hf, hfa⟩
    exact ⟨x, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx.symm⟩
  have hover : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ s = spMap (algebraMap c.F ℂ) →
      under x ≫ Xo.s = spMap (algebraMap (KA l) ℂ) := by
    intro x hx
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [hx]
    exact GagaRat.spMap_comp _ _
  have hexF : ∀ x : Sp ℂ ⟶ Xo.XF c, ∃ r : ℂ, (x ≫ s ≠ spMap (algebraMap c.F ℂ) → r = 0) ∧
      (x ≫ s = spMap (algebraMap c.F ℂ) → ∀ k P, IsPeriod (FU.Di k) ty P → FU.u k P = under x → r = ((k : ℕ) : ℂ)) := by
    intro x
    by_cases hx : x ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover x hx)
      exact ⟨((k : ℕ) : ℂ), fun h => absurd hx h, fun _ k' P' hP' e' => by rw [FU.disj k k' P P' hP hP' (e.trans e'.symm)]⟩
    · exact ⟨0, fun _ => rfl, fun h => absurd h hx⟩
  choose F hF0 hF using hexF
  have hconst := SheetDecomposition.One.const_of_hol (algebraMap c.F ℂ) s Z.ξ₀ ⊤ F D.dim hsm Z.over_inc hξ hcl (by
    intro m T y hT hc hy _ b₁ hb₁ b₂ hb₂
    have hall : ∀ b ∈ T, y b ≫ s = y b₁ ≫ s := fun b hb => over_const hc hy hb hb₁
    by_cases h : y b₁ ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨i, hi⟩ := GlobalTheory.T.family_uniformisation_local_period E H D l Xo _ g ty FU m T (fun b => under (y b)) hT hc ⟨b₁, hb₁⟩
        (fun b hb => hover _ ((hall b hb).trans h)) (GagaRat.isHolTo_comp _ hy)
      have key : ∀ b ∈ T, F (y b) = ((i : ℕ) : ℂ) := fun b hb => by
        obtain ⟨B', P, -, m1, -, hP, e⟩ := hi b hb
        exact hF _ ((hall b hb).trans h) i (P b) (hP.1 b m1) (e b m1)
      rw [key b₁ hb₁, key b₂ hb₂]
    · rw [hF0 _ h, hF0 _ (by rw [hall b₂ hb₂]; exact h)])
  obtain ⟨x, hx, hxU⟩ := SheetDecomposition.One.exists_point (algebraMap c.F ℂ) s ⟨U, hU.isOpen⟩ (q := genPt Z.ξ₀) Z.genPt_mem
  have hxU' : centre x ∈ U := GagaRat.centre_mem hxU
  obtain ⟨i, P₀, hP₀, e₀⟩ := FU.onto _ (hover x hx)
  refine ⟨g, ty, FU, i, hty, fun y hy => ?_⟩
  rw [range_sub_iff]
  constructor
  · intro hyU
    obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover y hy)
    have := hconst y x hy hx le_top le_top ((Z.closure _).1 hyU) ((Z.closure _).1 hxU')
    rw [hF _ hy k P hP e, hF _ hx i P₀ hP₀ e₀] at this
    obtain rfl : k = i := Fin.ext (Nat.cast_injective this)
    exact ⟨P, hP, e.symm⟩
  · rintro ⟨P, hP, e⟩
    exact mem_of_period FU hty _ hU i hP₀ hP e₀.symm hx e hy hxU'

end RootFieldNumerics.RF
end
end

section

noncomputable section

namespace RootFieldNumerics.Un

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

section Man

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)

theorem holoOn_chart (k : Fin A.n) {V : Set (Fin e → ℂ)} {f : (Fin e → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f V) :
    A.HoloOn ((A.chart k).source ∩ A.chart k ⁻¹' V) fun y => f (A.chart k y) := fun j t ht =>
  (hf _ ht.2.2).comp (f := A.chart k ∘ (A.chart j).symm) (A.holo j k t ⟨ht.1, ht.2.1⟩)

theorem periodChart {Ψ : Type} [Finite Ψ] {N j : ℕ} (pot : Ψ × Fin N → LocPot X) (k : Fin A.n) {V : Set (Fin e → ℂ)}
    {gm : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} (hV : IsOpen V) {x : X} (hx : x ∈ (A.chart k).source)
    (hxV : A.chart k x ∈ V) (ha : ∀ τ a b, AnalyticOnNhd ℂ (fun t => gm τ t a b) V) (hd : ∀ t ∈ V, ∀ τ, InFlagDomain N j (gm τ t))
    (hp : ∀ p : Ψ × Fin N, ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G (A.chart k x) ∧ ∀ᶠ t in 𝓝 (A.chart k x),
      (pot p).φ x ((A.chart k).symm t) = stepPot N j p.2 (gm p.1 t) + (G t).re) :
    ∃ W, IsPeriodChart A j pot x W fun τ y => gm τ (A.chart k y) := by
  choose G hG hGe using hp
  obtain ⟨V', h', hV', hx'⟩ := eventually_nhds_iff.1 ((hV.eventually_mem hxV).and
    ((Filter.eventually_all.2 fun p => (hG p).eventually_analyticAt).and (Filter.eventually_all.2 hGe)))
  refine ⟨(A.chart k).source ∩ A.chart k ⁻¹' V', (A.chart k).isOpen_inter_preimage hV', ⟨hx, hx'⟩,
    fun τ a b => holoOn_chart A k ((ha τ a b).mono fun t ht => (h' t ht).1), fun τ y hy => hd _ (h' _ hy.2).1 τ,
    fun p => ⟨fun y => G p (A.chart k y), holoOn_chart A k fun t ht => (h' t ht).2.1 p, fun y hy => ?_⟩⟩
  have := (h' _ hy.2).2.2 p
  rwa [(A.chart k).left_inv hy.1] at this

theorem flagImmersion {Ψ : Type} {N : ℕ} (k : Fin A.n) {gm : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ} {x : X}
    (hx : x ∈ (A.chart k).source) (ha : ∀ τ a b, AnalyticAt ℂ (fun t => gm τ t a b) (A.chart k x))
    (h : ∀ v : Fin e → ℂ, (∀ τ, ((gm τ (A.chart k x))⁻¹ *
      Matrix.of fun a b => fderiv ℂ (fun z => gm τ z a b) (A.chart k x) v).BlockTriangular id) → v = 0) :
    IsFlagImmersionAt A (fun τ y => gm τ (A.chart k y)) x := by
  intro k' hx' v hv
  let T := A.chart k ∘ (A.chart k').symm
  let T' := A.chart k' ∘ (A.chart k).symm
  have e₁ : T (A.chart k' x) = A.chart k x := congrArg _ ((A.chart k').left_inv hx')
  have hT : DifferentiableAt ℂ T (A.chart k' x) :=
    (A.holo k' k _ ⟨(A.chart k').map_source hx', by
      rw [Set.mem_preimage]; rwa [(A.chart k').left_inv hx']⟩).differentiableAt
  have hT' : DifferentiableAt ℂ T' (T (A.chart k' x)) := by
    rw [e₁]
    exact (A.holo k k' _ ⟨(A.chart k).map_source hx, by
      rw [Set.mem_preimage]; rwa [(A.chart k).left_inv hx]⟩).differentiableAt
  have h0 : fderiv ℂ T (A.chart k' x) v = 0 := h _ fun τ => by
    have e₂ : (Matrix.of fun a b => fderiv ℂ (fun z => gm τ z a b) (A.chart k x) (fderiv ℂ T (A.chart k' x) v)) =
        Matrix.of fun a b => fderiv ℂ (fun z => gm τ (A.chart k ((A.chart k').symm z)) a b) (A.chart k' x) v := by
      ext a b
      have h1 : DifferentiableAt ℂ (fun t => gm τ t a b) (T (A.chart k' x)) := by
        rw [e₁]
        exact (ha τ a b).differentiableAt
      have h2 := fderiv_comp _ h1 hT
      rw [e₁] at h2
      exact (congrArg (fun L : (Fin e → ℂ) →L[ℂ] ℂ => L v) h2).symm
    rw [e₂]
    exact hv τ
  have hid : T' ∘ T =ᶠ[𝓝 (A.chart k' x)] id := by
    have hc : ContinuousAt (A.chart k').symm (A.chart k' x) := (A.chart k').continuousAt_symm ((A.chart k').map_source hx')
    have h1 : ∀ᶠ t in 𝓝 (A.chart k' x), (A.chart k').symm t ∈ (A.chart k).source :=
      hc.eventually_mem ((A.chart k).open_source.mem_nhds (by rwa [(A.chart k').left_inv hx']))
    filter_upwards [h1, (A.chart k').open_target.mem_nhds ((A.chart k').map_source hx')] with t h1 h2
    show A.chart k' ((A.chart k).symm (A.chart k ((A.chart k').symm t))) = t
    rw [(A.chart k).left_inv h1, (A.chart k').right_inv h2]
  have h3 := hid.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp _ hT' hT, fderiv_id] at h3
  have h4 := congrArg (fun L => L v) h3
  simpa [h0] using h4.symm

end Man

theorem unif_of (hB : Biholo) (hLP : LocPer) (hT : Transport) (hFV : FrameVals) (hPM : PerMat) (hFI : FlagImm)
    (hC : CountGen) (hPot : PotLoc) (hPts : PtsFam) (hG : Top.Given) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    (hN : 1 ≤ D.p + D.q) {RM : Top.RootModel (CMType H) (D.p + D.q)}
    {Sys : AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys} (Or : RootOrigin Y ∅ RM Fx)
    (hJ : Or.Re.J = ⊤) (hd : Or.Fl.deg = 1) (hA : Ht.AmpleQ RM.y RM.A.a) :
    IsUniformised Sys.A Sys.open' D.p fun p => Sys.potH (some p) := by
  obtain ⟨ψ, hψ, hπ, hπ'⟩ := hB E H D l Xo c Y ∅ RM Sys Fx Or hJ hd hA
  obtain ⟨z, hzi, hzc, hzh, hzU⟩ := hPts E H D l Xo c Y ∅ RM Sys Fx Or ψ hJ hψ hπ hπ'
  constructor
  · intro x hx
    obtain ⟨k, hk⟩ := Sys.A.cover x
    obtain ⟨V, gm, hV, hxV, -, -, ha, hfd, hp, -⟩ :=
      locChart hLP hT hFV hPM hPot hG hN Or ψ hψ hπ z hzi hzc k (hzh k) ⊤ x hx hk trivial
    obtain ⟨W, hW⟩ := periodChart Sys.A (fun p => Sys.potH (some p)) k hV hk hxV ha hfd fun p => by
      have := hp _ hxV p
      rwa [(Sys.A.chart k).left_inv hk] at this
    exact ⟨W, _, hW⟩
  · obtain ⟨U, hU, hcnt⟩ := hC hG E H D l Xo c Y RM.Ω RM.K RM.ι RM.y Or.𝔐 Or.Fl hN hd
    obtain ⟨x, hx, hxU⟩ := hzU U hU
    obtain ⟨k, hk⟩ := Sys.A.cover x
    obtain ⟨V, gm, hV, hxV, hVt, hVo, ha, hfd, hp, hcV⟩ :=
      locChart hLP hT hFV hPM hPot hG hN Or ψ hψ hπ z hzi hzc k (hzh k) U x hx hk hxU
    obtain ⟨t, ht, him⟩ := hFI (CMType H) _ _ V gm hV ⟨_, hxV⟩ ha (fun t ht τ => (hfd t ht τ).1) (hcV hcnt)
    have e : Sys.A.chart k ((Sys.A.chart k).symm t) = t := (Sys.A.chart k).right_inv (hVt ht)
    have hs := (Sys.A.chart k).map_target (hVt ht)
    obtain ⟨W, hW⟩ := periodChart Sys.A (fun p => Sys.potH (some p)) k hV hs (by rwa [e]) ha hfd fun p => by
      rw [e]
      exact hp t ht p
    exact ⟨_, hVo t ht, W, _, hW, flagImmersion Sys.A k hs (fun τ a b => by rw [e]; exact ha τ a b t ht) (by rwa [e])⟩

end RootFieldNumerics.Un
end
end
