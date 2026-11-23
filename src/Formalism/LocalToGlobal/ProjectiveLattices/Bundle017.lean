module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import Formalism.LocalToGlobal.ProjectiveLattices.LieAlg
public import Formalism.LocalToGlobal.ProjectiveLattices.LieRel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle080
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivCls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop :=
  fun T ι _ => ∀ a : c.F, a ≠ 0 → ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = ι a

structure QPt where
  T : CDVR
  ι : c.F →+* T.Fr
  y : IntFr Xo c T ι
  triv : trivCls Xo c T ι y

def ordQ (q : QPt Xo c) (f : Rul Xo c) : EReal := nval q.T.V 1 (evI q.y f)

def RegularityR1Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n,
    (∃ la : HeightOneSpectrum (𝓞 c.F), ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
      ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q f

def RegularityR2Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE k : ℕ) (ws : Fin k → Rul Xo c)
    (et : Rul Xo c) (c' : ℝ), 0 ≤ c' → (∀ i, ws i ∈ C aL nL) → et ∈ C aE nE →
    (∃ (la : HeightOneSpectrum (𝓞 c.F)) (nu : ℝ), ∀ v ∈ valSet Xo c (algCls Xo c) la,
      0 ≤ v et ∧ (∃ i, v (ws i) ≠ ⊤) ∧ (v et ≠ ⊤ → (⨅ i, v (ws i)) ≤ (nu : EReal) + (c' : EReal) * v et)) →
    ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q et ∧
      (ordQ Xo c q et ≠ ⊤ → (⨅ i, ordQ Xo c q (ws i)) ≤ (c' : EReal) * ordQ Xo c q et)

end Formalism.L2.PjFree
end
end

section

noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivialClassCondition (T : CDVR) (io : c.F →+* T.Fr) (_y : IntFr Xo c T io) : Prop := True

theorem valSet_alg_subset (la : HeightOneSpectrum (𝓞 c.F)) :
    valSet Xo c (algCls Xo c) la ⊆ valSet Xo c (trivialClassCondition Xo c) la := by
  rintro _ ⟨y, rfl⟩
  exact ⟨PtV.widen (fun _ _ _ _ => trivial) y, rfl⟩

def trivSet : Set (Rul Xo c → EReal) :=
  {q | ∃ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
    (∀ a : c.F, a ≠ 0 → vV T.V (io a) = 0) ∧ q = fun f => nval T.V 1 (evI y f)}

def NoCommonZero {n : ℕ} (ws : Fin n → Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), ∃ i, evR Xo c (ws i) y ≠ 0

abbrev DomWt (E : Type) [Field E] : Type := {x : ((E →+* ℂ) × ℕ → ℕ) × ℕ // Dom x.1 x.2}

def regular₂ {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ReciprocityTheory.ChartRestriction.G.T0.RegLaw (Λ := HeightOneSpectrum (𝓞 c.F)) (Wt := DomWt E)
    (fun w => cusp Xo c U w.1.1 w.1.2)
    (fun la => valSet Xo c (algCls Xo c) la) (fun la => valSet Xo c (trivialClassCondition Xo c) la)
    (fun la v => ⟨v.1, valSet_alg_subset Xo c la v.2⟩) (fun _ v _ F => v.1 F.1)
    (trivSet Xo c) (fun q _ F => q.1 F.1) (fun ws => NoCommonZero Xo c fun i => (ws i).1) ∧
  ∀ a n, Dom a n → ∀ (m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ cusp Xo c U a n) → NoCommonZero Xo c ws →
    ∀ nu : HeightOneSpectrum (𝓞 c.F) → ℝ,
      (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)) →
        ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)

variable {Xo c}

end Formalism.L2.PjFree
end
end

section



noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj tvec_eig_iff isTan_tvec tcoord tcoord_spec univChartLoc tanBC_alg
  pushR pushR_left pushR_inj pushR_map tvec_tmap fB scaleD IsUnivChart dualMapA)
open Formalism.L2.Pj.LieRel Formalism.L2.Pj.LieAlg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem int_val (T : CDVR) (io : c.F →+* T.Fr) (τ : E →+* ℂ) (a : 𝓞 E) :
    ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ a) := by
  obtain ⟨p, hp, hpa⟩ := NumberField.RingOfIntegers.isIntegral a
  refine IsIntegrallyClosed.isIntegral_iff.1 ⟨p.map (Int.castRingHom T.V), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hf : (algebraMap T.V T.Fr).comp (Int.castRingHom T.V) =
      (io.comp (embK c τ)).comp (algebraMap ℤ (𝓞 E)) := RingHom.ext_int _ _
  rw [hf]
  have h3 := Polynomial.hom_eval₂ p (algebraMap ℤ (𝓞 E)) (io.comp (embK c τ)) a
  rw [hpa, map_zero] at h3
  exact h3.symm



theorem lieFree : LieFreeSt Xo c := by
  intro T io G t' x m1 m2 _ u₀ hu₀t hu₀e hu₀b
  let _ := io.toAlgebra
  have := G.semi.smooth
  have : ∀ a, IsMonHom (G.act.act a) := G.act.hom
  obtain ⟨n, xc, hxc⟩ := univChartLoc G.G
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := T.V) (R' := T.Fr) G.G n xc hxc
  have hpt : ∀ cc : Fin n → T.V, pushR G.G (tvec (x := x') (algebraMap T.V T.Fr ∘ cc)) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (dualMapA T.V T.Fr) ≫ tvec (x := xc) cc := fun cc =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp cc]; rfl)
  have hM0 : ∀ (a : 𝓞 E) (cc : Fin n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (algebraMap T.V T.Fr ∘ cc) =
        algebraMap T.V T.Fr ∘ tmap hxc (G.act.act a) cc := by
    intro a cc
    apply tvec_inj hx'
    apply pushR_inj G.G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hxc, Category.assoc]
  have hM : ∀ (a : 𝓞 E) (cc : Fin n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (fun j => algebraMap T.V T.Fr (cc j)) =
        fun j => algebraMap T.V T.Fr (tmap hxc (G.act.act a) cc j) := hM0
  have h1 := m1.cart
  have h2 : IsGrpPullback t'.G G.G (fB T.V T.Fr) m2.φ := m2.cart
  have hex : ∀ e : Fin n → T.Fr, ∃ v, RelA x m1.φ m2.φ v (tvec (x := x') e) :=
    fun e => relA_exists_v x h1 h2 (tvec (x := x') e)
  choose vA hvA using hex
  have coordA : ∀ w, IsTanAt x w → ∃ e : Fin n → T.Fr, (vA e).left = w := by
    intro w hw
    let v0 : epsAt x ⟶ Xo.univ.t.G := Over.homMk w hw.1
    obtain ⟨y0, hy0⟩ := relA_exists_y x h1 h2 v0
    have ht : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y0 := (relA_tan x h1 h2 hy0).1 hw.2
    refine ⟨tcoord hx' y0 ht, ?_⟩
    exact congrArg (fun q => q.left) ((relA_uniq x h1 h2 (hvA _) hy0).2 (tcoord_spec hx' y0 ht).symm)
  have tanA : ∀ e, IsTanAt x (vA e).left := fun e =>
    ⟨Over.w (vA e), (relA_tan x h1 h2 (hvA e)).2 (isTan_tvec hx' e)⟩
  have eigA : ∀ (τ : E →+* ℂ) e, IsEigAt c τ (vA e).left ↔
      ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = io (embK c τ a) • e := by
    intro τ e
    unfold IsEigAt
    refine forall_congr' fun a => ?_
    rw [← tvec_eig_iff hx']
    exact relA_eig x h1 h2 (hvA e) (t'.act.act a) (Xo.univ.t.act.act a) (G.act.act a) (m1.act a) (m2.act a) _
  have combA : ∀ {m : ℕ} (d : Fin m → Fin n → T.Fr) (cf : Fin m → T.Fr) (e : Fin n → T.Fr),
      IsCombAt x (fun i => (vA (d i)).left) cf (vA e).left ↔ e = ∑ i, cf i • d i := by
    intro m d cf e
    have hr : ∀ i, RelA x m1.φ m2.φ (sclA x (cf i) ≫ vA (d i))
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cf i)) ≫ tvec (x := x') (d i)) :=
      fun i => relA_scl x (hvA (d i)) (cf i)
    have hp := relA_prod x h1 h2 _ _ hr
    rw [prod_tvec hx'] at hp
    constructor
    · rintro ⟨u, hu, hw⟩
      have hu' : u = fun i => sclA x (cf i) ≫ vA (d i) := funext fun i => Over.OverMorphism.ext (hu i)
      subst hu'
      exact tvec_inj hx' ((relA_uniq x h1 h2 (hvA e) hp).1 (Over.OverMorphism.ext hw.symm))
    · rintro rfl
      exact ⟨fun i => sclA x (cf i) ≫ vA (d i), fun i => rfl,
        congrArg (fun q => q.left) ((relA_uniq x h1 h2 hp (hvA _)).2 rfl)⟩
  choose χ hχ using fun τ a => int_val c T io τ a
  have key : ∀ τ : E →+* ℂ, ∃ (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
      (u : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
      (∀ i, IsTan (ub i)) ∧ (∀ i, IsEigV c io G τ (ub i)) ∧
      (∀ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w) ∧
      (∀ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = u i ∧
        u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub i).left) ∧
      (∀ i, IsTanAt x (u i)) ∧ (∀ i, IsEigAt c τ (u i)) ∧
      (∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x u a w) ∧
      ∀ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x (u₀ τ) cf (u i) := by
    intro τ
    choose v hv using fun i => coordA (u₀ τ i) (hu₀t τ i)
    have hu₀ : u₀ τ = fun i => (vA (v i)).left := funext fun i => (hv i).symm
    have eigM : ∀ e, IsEigAt c τ (vA e).left ↔
        ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = algebraMap T.V T.Fr (χ τ a) • e := by
      intro e
      rw [eigA τ e]
      simp only [hχ τ]
    have hvM : ∀ a i, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (v i) =
        algebraMap T.V T.Fr (χ τ a) • v i := fun a i => (eigM (v i)).1 (by rw [hv i]; exact hu₀e τ i) a
    have hbM : ∀ w, (∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) w =
        algebraMap T.V T.Fr (χ τ a) • w) → ∃! cf : Fin (Dw.mult τ) → T.Fr, w = ∑ i, cf i • v i := by
      intro w hw
      obtain ⟨cf, hcf, hu⟩ := hu₀b τ (vA w).left (tanA w) ((eigM w).2 hw)
      rw [hu₀] at hcf hu
      exact ⟨cf, (combA v cf w).1 hcf, fun cf' h' => hu cf' ((combA v cf' w).2 h')⟩
    obtain ⟨b, hbe, hbb, hbt⟩ := eig_basis (fun a => tmap hxc (G.act.act a)) (χ τ)
      (fun a => tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a))) hM v hvM hbM
    choose C hCd hCz hCb using hbt
    refine ⟨fun i => cvV (tvec (x := xc) (b i)), fun i => (vA (fun j => algebraMap T.V T.Fr (b i j))).left,
      fun i => isTan_cvV (isTan_tvec hxc (b i)), fun i a z hz => ?_, fun w hw he => ?_, fun i => ?_, fun i => tanA _,
      fun i => ?_, fun w hw he => ?_, fun i => ⟨C i, isUnit_iff_ne_zero.2 (hCd i), hCz i, ?_⟩⟩
    · have hz' : z = χ τ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ τ a).symm)
      subst hz'
      exact (eigV_iff hxc (G.act.act a) (b i) _).2 (hbe a i)
    · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc hw
      have hcc : ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc := fun a =>
        (eigV_iff hxc (G.act.act a) cc _).1 (he a (χ τ a) (hχ τ a))
      obtain ⟨r, hr, hru⟩ := hbb cc hcc
      exact ⟨r, (comb_iff hxc b r cc).2 hr, fun r' h' => hru r' ((comb_iff hxc b r' cc).1 h')⟩
    · obtain ⟨w, hw, hwl⟩ := hvA (fun j => algebraMap T.V T.Fr (b i j))
      have hw' : w.left ≫ m2.φ = (tvec (x := x') (fun j => algebraMap T.V T.Fr (b i j))).left ≫
          pullback.fst G.G.hom (fB T.V T.Fr) := hw
      refine ⟨w.left, hwl.symm, ?_⟩
      rw [cvV_left]
      exact hw'.trans (hcomp (b i))
    · refine (eigA τ _).2 fun a => ?_
      rw [hM a (b i), hbe a i, ← hχ τ a]
      funext j
      simp [Pi.smul_apply, smul_eq_mul, map_mul]
    · obtain ⟨e, rfl⟩ := coordA w hw
      have hP : ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e =
          algebraMap T.V T.Fr (χ τ a) • e := (eigM e).1 he
      obtain ⟨d, hd, hdu⟩ := tri_basis (fun w => ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) w =
          algebraMap T.V T.Fr (χ τ a) • w) v hbM C hCz hCd e hP
      have hCb' : ∀ i, (∑ j, C i j • v j) = fun j => algebraMap T.V T.Fr (b i j) := fun i => (hCb i).symm
      simp only [hCb'] at hd hdu
      exact ⟨d, (combA _ d e).2 hd, fun d' h' => hdu d' ((combA _ d' e).1 h')⟩
    · rw [hu₀]
      exact (combA v (C i) _).2 (hCb i)
  choose ub u hub using key
  exact ⟨ub, u, ⟨fun τ i => (hub τ).1 i, fun τ i => (hub τ).2.1 i, fun τ w hw he => (hub τ).2.2.1 w hw he,
    fun τ i => (hub τ).2.2.2.1 i⟩, fun τ i => (hub τ).2.2.2.2.1 i, fun τ i => (hub τ).2.2.2.2.2.1 i,
    fun τ w hw he => (hub τ).2.2.2.2.2.2.1 w hw he, fun τ i => (hub τ).2.2.2.2.2.2.2 i⟩

end Formalism.L2.Pj
end
end

section



noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem intFr_of_model (hIF : IntFramesSt Xo c) (T : CDVR) (io : c.F →+* T.Fr) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) (hPI : PushInvertible Y.t.G Y.t.PP.L) (b : O →+* T.V)
    (hb : (algebraMap T.V T.Fr).comp b = io.comp β) (y₀ : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), (letI := io.toAlgebra; FrBor t y₀ y.1) := by
  letI := io.toAlgebra
  have e1 : y₀.x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y₀.x_over]
    exact spMap_comp _ _
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Sp T.Fr ⟶ pullback Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom),
      z ≫ pullback.fst _ _ = y₀.x ∧ z ≫ pullback.snd _ _ = spMap io :=
    ⟨pullback.lift y₀.x (spMap io) e1, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have e3 : Out.jK T.V = spMap (algebraMap T.V T.Fr) := rfl
  have e4 : Y.j = Y.jQ ≫ pullback.fst _ _ := rfl
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    rw [e4, e3, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hz2,
      ← spMap_comp, ← spMap_comp, hb]
  obtain ⟨yt, hyt1, -⟩ := extPt Y T b z hx
  exact hIF T io O β Y hPI yt z (by rw [← hyt1, e3]) hz2 y₀ hz1.symm

def ModelAtSt (Xo : Moduli Dw l) (c : Coeff l) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions nonZeroDivisors

theorem b_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h, Ideal.smul_bot, sup_bot_eq] at h2
  exact bot_ne_top h2

theorem one_mem_inverse_halfDifferent (D : D7) : (1 : D.host.E) ∈ D.host.AA0 :=
  FractionalIdeal.one_mem_inv_coe_ideal (b_ne_bot D)

theorem normK_mem_AA (D : D7) : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA := by
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈
      (D.host.ccE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [FractionalIdeal.mem_coeIdeal]
    refine ⟨((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E), ?_, by simp⟩
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    simpa [Host.ccE] using this
  have := FractionalIdeal.mul_mem_mul hN (one_mem_inverse_halfDifferent D)
  rw [mul_one] at this
  exact this

theorem normK_ne_zero (D : D7) : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := by
  rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact D.host.ccK_ne_bot

theorem exists_smul_mem_base_lattice_alt (D : D7) (j : ℕ) (y : (D.sp.W j).V) :
    ∃ s ∈ (𝓞 D.host.E)⁰, s • y ∈ (D.sp.W j).L0 :=
  _root_.UpperTheory.Reformulated.B.EmbeddingTypes.exists_smul_mem_base_lattice_alt D j y

theorem exists_smul_mem_latW (D : D7) (j : ℕ) (y : (D.sp.W j).V) :
    ∃ s ∈ (𝓞 D.host.E)⁰, s • y ∈ latW D j := by
  obtain ⟨s, hs, hsy⟩ := exists_smul_mem_base_lattice_alt D j y
  set n : 𝓞 D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E)
  have hn : algebraMap (𝓞 D.host.E) D.host.E n = ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) := by
    simp [n]
  have hn0 : n ∈ (𝓞 D.host.E)⁰ := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply normK_ne_zero D
    rw [← hn, h0, map_zero]
  refine ⟨n * s, mul_mem hn0 hs, ?_⟩
  rw [mul_smul, ← algebraMap_smul D.host.E n, hn]
  exact Submodule.subset_span ⟨_, normK_mem_AA D, s • y, hsy, rfl⟩

instance latW_isLocalized (D : D7) (j : ℕ) :
    IsLocalizedModule (𝓞 D.host.E)⁰ (latW D j).subtype where
  map_units x := by
    rw [Module.End.isUnit_iff]
    have hx0 : algebraMap (𝓞 D.host.E) D.host.E x ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    have e : ∀ v : (D.sp.W j).V, algebraMap (𝓞 D.host.E) (Module.End (𝓞 D.host.E) (D.sp.W j).V) x v =
        algebraMap (𝓞 D.host.E) D.host.E x • v := by
      intro v
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    constructor
    · intro v w h
      rw [e, e] at h
      exact smul_right_injective _ hx0 h
    · intro v
      refine ⟨(algebraMap (𝓞 D.host.E) D.host.E x)⁻¹ • v, ?_⟩
      rw [e, smul_smul, mul_inv_cancel₀ hx0, one_smul]
  surj y := by
    obtain ⟨s, hs, hsy⟩ := exists_smul_mem_latW D j y
    exact ⟨(⟨s • y, hsy⟩, ⟨s, hs⟩), rfl⟩
  exists_of_eq {x₁ x₂} h := ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩

theorem latW_finrank (D : D7) (j : ℕ) :
    Module.finrank (𝓞 D.host.E) (latW D j) = Module.finrank D.host.E (D.sp.W j).V := by
  rw [IsFractionRing.finrank_right_eq (R := 𝓞 D.host.E) (S := D.host.E) (N := (D.sp.W j).V)]
  exact (IsLocalizedModule.finrank_eq (p := (𝓞 D.host.E)⁰) (f := (latW D j).subtype) le_rfl).symm

theorem latW_rank (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) :
    Module.finrank (𝓞 D.host.E) (latW D j) = (D.R.sigW j).1 + (D.R.sigW j).2 := by
  rw [latW_finrank, (D.sp.W j).rank_eq, D.sp.W_rank j hj.1 hj.2]
  have := D.R.m_add_three_le_k
  simp only [Ranks.sigW, Ranks.r]
  omega

end Formalism.L2.Pj
end
end
