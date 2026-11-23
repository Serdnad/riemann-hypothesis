module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Separation.CompletelyRegular
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def SRel {S : Type} [CommRing S] [Algebra c.F S] (a : S) (y y' : FrPt Xo c S) : Prop :=
  ∃ pm : Gx y'.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y'.x) Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y'.x) Xo.univ.t.G).left ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i),
      (pm.appLE _ _ h).hom (scal y.x a i * y.s.f i) = y'.s.f i

def pmOfGS {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) : Gx x' ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom) (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
    (by
      show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ x =
        pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
      rw [← hx]
      exact pullback.condition)

theorem pmOf_snd {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) :
    pmOfGS hx ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left :=
  pullback.lift_snd _ _ _

theorem pmOf_fst {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) :
    pmOfGS hx ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left :=
  pullback.lift_fst _ _ _

theorem srel_iff {S : Type} [CommRing S] {x x' : Sp S ⟶ Xo.X} (hx : x' = x) (s : LB.Sec (PPx x))
    (s' : LB.Sec (PPx x')) (pm : Gx x' ⟶ Gx x)
    (h1 : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (h2 : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left) (a : S) :
    (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i),
        (pm.appLE _ _ h).hom (scal x a i * s.f i) = s'.f i) ↔
      ∀ i, (hx ▸ s').f i = scal x a i * s.f i := by
  subst hx
  have e1 : pm ≫ pullback.fst (Over.mk x').hom Xo.univ.t.G.hom =
      𝟙 _ ≫ pullback.fst (Over.mk x').hom Xo.univ.t.G.hom := by
    rw [Category.id_comp]
    exact h2
  have e2 : pm ≫ pullback.snd (Over.mk x').hom Xo.univ.t.G.hom =
      𝟙 _ ≫ pullback.snd (Over.mk x').hom Xo.univ.t.G.hom := by
    rw [Category.id_comp]
    exact h1
  have hpm : pm = 𝟙 (Gx x') := pullback.hom_ext e1 e2
  subst hpm
  have e : ∀ (U : (Gx x').Opens) (h : U ≤ (𝟙 (Gx x')) ⁻¹ᵁ U), Scheme.Hom.appLE (𝟙 (Gx x')) U U h = 𝟙 _ := by
    intro U h
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx x').presheaf.map_id]
    rfl
  constructor
  · intro H i
    have := H i (fun _ hp => hp)
    erw [e] at this
    exact this.symm
  · intro H i h
    erw [e]
    exact (H i).symm

theorem srel_exists {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) :
    ∃ a : S, SRel a y y' := by
  obtain ⟨a, ha, -⟩ := y.gen (hx ▸ y'.s)
  exact ⟨a, pmOfGS hx, pmOf_snd hx, pmOf_fst hx, (srel_iff hx y.s y'.s _ (pmOf_snd hx) (pmOf_fst hx) a).2 ha⟩

theorem srel_unique {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (hx : y'.x = y.x) {a b : S}
    (ha : SRel a y y') (hb : SRel b y y') : a = b := by
  obtain ⟨pa, pa1, pa2, pa3⟩ := ha
  obtain ⟨pb, pb1, pb2, pb3⟩ := hb
  have ea := (srel_iff hx y.s y'.s pa pa1 pa2 a).1 pa3
  have eb := (srel_iff hx y.s y'.s pb pb1 pb2 b).1 pb3
  obtain ⟨a', -, hu⟩ := y.gen (hx ▸ y'.s)
  exact (hu a ea).trans (hu b eb).symm

theorem srel_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {a : S} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (hs : SRel a y y') (hz : FrMap φ y z) (hz' : FrMap φ y' z')
    (hxz : z'.x = z.x) : SRel (φ a) z z' := by
  obtain ⟨pmC, hsC, hfC, haC⟩ := hs
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  obtain ⟨hx2, hu2, pmB, hsB, hfB, haB⟩ := hz'
  let pm : Gx z'.x ⟶ Gx z.x := pmOfGS hxz
  have pfst : pm ≫ pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom :=
    pullback.lift_fst _ _ _
  have psnd : pm ≫ pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom :=
    pullback.lift_snd _ _ _
  have hsA' : pmA ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom := hsA
  have hfA' : pmA ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom =
      pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfA
  have hsB' : pmB ≫ pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom := hsB
  have hfB' : pmB ≫ pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom =
      pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfB
  have hsC' : pmC ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom := hsC
  have hfC' : pmC ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom := hfC
  have hcomp : pm ≫ pmA = pmB ≫ pmC := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfA', ← Category.assoc, pfst, Category.assoc, hfC', hfB']
    · rw [Category.assoc, hsA', psnd, Category.assoc, hsC', hsB']
  refine ⟨pm, psnd, pfst, fun i h => ?_⟩
  have hA := ppx_le_cov pmA hsA i
  have hB' := ppx_le_cov pmB hsB i
  have hC' := ppx_le_cov pmC hsC i
  have key : ∀ (q : Gx z'.x ⟶ Gx y.x), q = pmB ≫ pmC → ∀ hh : (PPx z'.x).U i ≤ q ⁻¹ᵁ (PPx y.x).U i,
      (q.appLE _ _ hh).hom (scal y.x a i * y.s.f i) = z'.s.f i := by
    rintro q rfl hh
    have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC' ≫ pmB.appLE _ _ hB' :=
      (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC' hB').symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC', haB i hB']
  show (pm.appLE _ _ h).hom (scal z.x (φ.toRingHom a) i * z.s.f i) = z'.s.f i
  rw [← haA i hA, ← scal_pull φ.toRingHom pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
  have e2 := congrArg (fun f => f.hom (scal y.x a i * y.s.f i))
    (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  exact key _ hcomp _

theorem frBor_descend {S T : Type} [CommRing S] [Algebra c.F S] [IsReduced S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) (hφ : Function.Injective φ) {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} {t : Ix Dw → Tˣ}
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') (hb : FrBor t z z')
    (hinv : ∀ k, ∃ b : S, φ b = ((t k)⁻¹ : Tˣ)) :
    ∃ tS : Ix Dw → Sˣ, FrBor tS y y' ∧ ∀ k, φ (tS k : S) = t k := by
  classical
  have hx : y'.x = y.x := x_eq_of_inj Xo φ.toRingHom hφ (by rw [y'.x_over, y.x_over])
    (by rw [← hz'.1, ← hz.1]; exact hb.1)
  have hU : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ a : Fin (Dw.mult τ) → S,
      IsCombAt y.x (y.u τ) a (y'.u τ i) ∧ (∀ j, i < j → a j = 0) ∧ φ (a i) = t (some ⟨τ, i⟩) := by
    intro τ i
    obtain ⟨a, ha, -⟩ := y.basis τ (y'.u τ i) (hx ▸ y'.tan τ i) (y'.eig τ i)
    have hp := isCombAt_pull φ.toRingHom hz.1 (hz.2.1 τ) (hz'.2.1 τ i) ha
    obtain ⟨cf, hci, hlow, hc⟩ := hb.2.1 τ i
    obtain ⟨a', -, hu⟩ := z.basis τ (z'.u τ i) (hb.1 ▸ z'.tan τ i) (z'.eig τ i)
    have e : (fun j => φ.toRingHom (a j)) = cf := (hu _ hp).trans (hu _ hc).symm
    refine ⟨a, ha, fun j hj => hφ ?_, ?_⟩
    · rw [map_zero, ← hlow j hj]
      exact congrFun e j
    · rw [← hci]
      exact congrFun e i
  choose a ha hlow hdiag using hU
  obtain ⟨a0, hs0⟩ := srel_exists y y' hx
  have hs1 := srel_bc φ hs0 hz hz' hb.1
  have hs2 : SRel (t none : T) z z' := hb.2.2
  have hd0 : φ a0 = t none := srel_unique hb.1 hs1 hs2
  let d : Ix Dw → S := fun k => match k with
    | none => a0
    | some ⟨τ, i⟩ => a τ i i
  have hd : ∀ k, φ (d k) = t k := by
    rintro (_ | ⟨τ, i⟩)
    · exact hd0
    · exact hdiag τ i
  choose b hb' using hinv
  have hdb : ∀ k, d k * b k = 1 := fun k => hφ (by rw [map_mul, hd, hb', map_one, Units.mul_inv])
  let tS : Ix Dw → Sˣ := fun k => ⟨d k, b k, hdb k, by rw [mul_comm]; exact hdb k⟩
  exact ⟨tS, ⟨hx, fun τ i => ⟨a τ i, rfl, hlow τ i, ha τ i⟩, hs0⟩, hd⟩

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

set_option backward.isDefEq.respectTransparency.types false in
instance smoothOfRelativeDimension_strK (Xo : Moduli Dw l) (c : Coeff l) :
    SmoothOfRelativeDimension Dw.dim (strK (Xo := Xo) (c := c)) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} Dw.dim
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension Dw.dim) _ _ Xo.smooth

theorem kapFG_pf (Xo : Moduli Dw l) (c : Coeff l) : KapFG Xo c := by
  intro Z
  have h := @TranscendenceDegreeLemmas.fg_residueField_genericPoint c.F _ _ _ _
    (strK (Xo := Xo) (c := c)) Dw.dim _ _ Z.2 (algKap Z)
  exact h

end Formalism.L2.Pj

end
end

section

noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory Topology NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

def STLoc (h : GenFrEx Xo c) (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c)
    (jc : Comp Xo c → Fin (N + 1)) : Prop :=
  FnTrdeg Xo c Dd → FnFG Xo c → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → ∀ (Z : Comp Xo c) (sg : c.F →+* ℂ),
    ∃ S : Set (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1),
      MeasurableSet S ∧
      Measure.pi (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere) S = 0 ∧
      ∀ t0 ∈ Sᶜ, ∃ U ∈ 𝓝 t0, ∃ (n : ℕ)
        (Q : Fin n → (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Om Z →+* ℂ)),
        (∀ k (a : Om Z), ContinuousOn (fun t => Q k t a) (U ∩ Sᶜ)) ∧
        ∀ t ∈ U ∩ Sᶜ, Function.Injective (fun k => Q k t) ∧
          Set.range (fun k => Q k t) = {P : Om Z →+* ℂ | P ∈ PT sg ∧ ∀ i, ∑ j,
            (t i : EuclideanSpace ℂ (Fin (N + 1))) j *
              P (ratio (Ω := Om Z) (valG h uL (wR j) Z) (valG h uL (wR (jc Z)) Z)) = 0}

def NrmAlong (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp Xo c) (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∀ {X : Type} [TopologicalSpace X] (U : Set X) (Q : X → (Om Z →+* ℂ)), (∀ x ∈ U, Q x ∈ PT sg) →
      (∀ a, ContinuousOn (fun x => Q x a) U) → ContinuousOn (fun x => nrmC fn (yP Z) G f (Q x)) U

theorem nrmContOff_of (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (hst : STLoc h Dd N uL wR jc) (hna : NrmAlong fn yP) (hfn : FnNe Xo c fn) (htr : FnTrdeg Xo c Dd) (hfg : FnFG Xo c)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) :
    NrmContOff h fn yP Dd N uL wR jc := by
  intro Z sg G f hf hf0
  obtain ⟨S, hSm, hS0, hloc⟩ := hst htr hfg hwb Z sg
  refine ⟨S, hSm, hS0, ?_⟩

  have hne : ∀ P : Om Z →+* ℂ, nrmC fn (yP Z) G f P ≠ 0 := by
    intro P
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
    have ha : a ≠ 0 := by rintro rfl; exact hf0 (zero_smul _ _)
    unfold nrmC
    refine mul_ne_zero ?_ ?_
    · rw [norm_ne_zero_iff, map_ne_zero]
      simpa using ha
    · exact Finset.prod_ne_zero_iff.2 fun i _ => by
        have := abs_pos.2 (hfn _ (yP Z P) i)
        positivity
  intro t0 ht0
  obtain ⟨U, hU, n, Q, hQc, hQ⟩ := hloc t0 ht0
  have hg : ContinuousOn (fun t => ∑ k, Real.log (nrmC fn (yP Z) G f (Q k t))) (U ∩ Sᶜ) := by
    refine continuousOn_finsetSum _ fun k _ => ContinuousOn.log ?_ fun t _ => hne _
    refine hna Z sg hf hf0 (U ∩ Sᶜ) (fun t => Q k t) ?_ (fun a => hQc k a)
    intro t ht
    have hm : Q k t ∈ Set.range (fun k => Q k t) := ⟨k, rfl⟩
    rw [(hQ t ht).2] at hm
    exact hm.1
  have key : ∀ t ∈ U ∩ Sᶜ, ∑ᶠ P ∈ Set.range (fun k => Q k t), Real.log (nrmC fn (yP Z) G f P) =
      ∑ k, Real.log (nrmC fn (yP Z) G f (Q k t)) := fun t ht => by
    rw [finsum_mem_range (hQ t ht).1, finsum_eq_sum_of_fintype]
  have hgw := hg.continuousWithinAt ⟨mem_of_mem_nhds hU, ht0⟩
  rw [Set.inter_comm] at hgw
  refine ((continuousWithinAt_inter hU).1 hgw).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [inter_mem_nhdsWithin Sᶜ hU] with t ht
    rw [← key t ⟨ht.2, ht.1⟩, (hQ t ⟨ht.2, ht.1⟩).2]
    rfl
  · rw [← key t0 ⟨mem_of_mem_nhds hU, ht0⟩, (hQ t0 ⟨mem_of_mem_nhds hU, ht0⟩).2]

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure DatAt (Y : Model Xo c β) {p : ℕ} {C : SCF p} (P : PointsOfFlagModel.PtC Y C) : Type 1 where
  R : Type
  [ring : CommRing R]
  [dom : IsDomain R]
  [loc : IsLocalRing R]
  [ch0 : CharZero R]
  noeth : IsNoetherianRing R
  normal : IsIntegrallyClosed R
  complete : IsAdicComplete (maximalIdeal R) R
  ι : Sp R ⟶ Y.X
  f : R →+* intO ↥C.S
  f_loc : ∀ a ∈ maximalIdeal R, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1
  fac : spMap f ≫ ι = P.yt
  t : SAB H (Sp R)
  m : SABMap t Y.t ι
  U : PELUnif (maximalIdeal R) t
  unitOn : ∀ y, PsiUnitOn U.D.toPre y (ι ⁻¹' abLocus Y.t.G)
  tors : U.TorsionIso

attribute [instance] DatAt.ring DatAt.dom DatAt.loc DatAt.ch0

namespace DatAt

variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

abbrev Ylat (A : DatAt Y P) : Type := A.U.D.toPre.X

def beta (A : DatAt Y P) (a b : A.Ylat) : ℝ :=
  betaAt A.U.D.toPre ((intO ↥C.S).subtype.comp A.f) p a b

theorem beta_symm (A : DatAt Y P) (a b : A.Ylat) : A.beta a b = A.beta b a :=
  betaAt_symm _ _ _ a b

end DatAt

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def PiHalf (l : Level H) (D : DepData E) : Prop := Ideal.span {D.pi 0 * D.pi 1} = l.Mb

theorem zeta_mem_of_dvd {l : Level H} (c : Coeff l) {g : ℕ} (hg : g ∣ l.M') (h0 : l.M' ≠ 0) : zeta g ∈ c.F := by
  obtain ⟨k, hk⟩ := hg
  have hg0 : (g : ℂ) ≠ 0 := by
    rintro h'; apply h0; rw [hk, Nat.cast_eq_zero.1 h', zero_mul]
  have hk0 : (k : ℂ) ≠ 0 := by
    rintro h'; apply h0; rw [hk, Nat.cast_eq_zero.1 h', mul_zero]
  have e : zeta g = zeta l.M' ^ k := by
    unfold zeta
    rw [← Complex.exp_nat_mul, hk]
    congr 1
    push_cast
    field_simp
  rw [e]
  exact pow_mem c.zeta_mem k

end Formalism.L2.Pj
end
end
