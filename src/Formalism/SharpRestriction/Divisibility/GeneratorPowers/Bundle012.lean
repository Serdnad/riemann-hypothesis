module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def BetaUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (a : 𝓞 E) (β β' : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε)),
    β.IsGen → β'.IsGen →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β' (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    β = β'

namespace GaugeBeta

theorem pull_unit_eq_one_k {X Y S0 : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : S0 ⟶ Y) (ψ : S0 ⟶ X) (k : ℤ)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => k))
    (t t' : LB.Gen (LB.LinComb L φ ε)) (u : Γ(Y, ⊤)ˣ)
    (hu : ∀ j, t.s j = res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) u * t'.s j)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) rig)
    (hc' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' h) rig) :
    (h.app ⊤).hom (u : Γ(Y, ⊤)) = 1 := by

  let rig1 : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1) := ⟨rig.s⟩
  exact pull_unit_eq_one L hL φ ε h ψ rig1 t t' u hu hc hc'

end GaugeBeta

theorem betaUniq_of_global (hglob : GlobalFnsSt) : BetaUniqSt := by
  intro E _ _ _ H Dw l Xo a β β' hβ hβ' hc hc'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨u, hu⟩ := gen_ratio _ (wchart_cover Xo.univ.t.PP.L hL _) β β' hβ hβ'
  have h1 := GaugeBeta.pull_unit_eq_one_k Xo.univ.t.PP.L hL _ _ (eSec Xo.univ.t.G)
    (eSec Xo.univ.t.G) (-3) (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) β β' u hu hc hc'
  have hu1 : u = 1 := by
    obtain ⟨v, hv⟩ := (hglob _ Xo.univ.t.G (isAbelianScheme_univ Xo)).2 (u : Γ(Xo.univ.t.G.left, ⊤))
    have hw : eSec Xo.univ.t.G ≫ Xo.univ.t.G.hom = 𝟙 _ := by
      unfold eSec
      exact Over.w _
    have e1 : (Scheme.Hom.app (eSec Xo.univ.t.G) ⊤).hom
        ((Scheme.Hom.appTop Xo.univ.t.G.hom).hom v) = v := by
      have := congrArg (fun f => (Scheme.Hom.appTop f).hom v) hw
      simp at this
      exact this
    rw [hv] at e1
    have hv1 : v = 1 := e1.symm.trans h1
    apply Units.ext
    rw [← hv, hv1, map_one]
    rfl
  cases β
  cases β'
  congr 1
  funext j
  have hj := hu j
  rw [hu1, map_one, one_mul] at hj
  exact hj

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Ring

variable {V K : Type} [CommRing V] [CommRing K] (f : V →+* K)

theorem jetCoef_mk (κ : Type) (m : ℕ) (p : MvPolynomial κ V) :
    jetCoef f κ m (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

theorem psTrunc_map {σ : Type} [Fintype σ] [DecidableEq σ] (m : ℕ) (F : MvPowerSeries σ V) :
    psTrunc m (MvPowerSeries.map f F) = MvPolynomial.map f (psTrunc m F) := by

  simp only [psTrunc, map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem jetCoef_alg (κ : Type) (m : ℕ) :
    (jetCoef f κ m).comp (algebraMap V (Jet V κ m)) = (algebraMap K (Jet K κ m)).comp f := by
  refine RingHom.ext fun v => ?_
  first
  | (show jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
     rw [jetCoef_mk, MvPolynomial.map_C])
  | (simp only [RingHom.comp_apply]
     rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
       MvPolynomial.algebraMap_eq, jetCoef_mk, MvPolynomial.map_C])

theorem jetCoef_aug (κ : Type) (m : ℕ) :
    ((jetAug : Jet K κ m →ₐ[K] K) : Jet K κ m →+* K).comp (jetCoef f κ m) =
      f.comp ((jetAug : Jet V κ m →ₐ[V] V) : Jet V κ m →+* V) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C a))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.C a)))
    rw [jetCoef_mk, MvPolynomial.map_C]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.C (f a)) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.C a))
    simp
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)))
    rw [jetCoef_mk, MvPolynomial.map_X]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.X i) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.X i))
    simp

theorem jetCoef_trunc (κ : Type) (m : ℕ) :
    ((jetTrunc : Jet K κ (m + 1) →ₐ[K] Jet K κ m) : Jet K κ (m + 1) →+* Jet K κ m).comp (jetCoef f κ (m + 1)) =
      (jetCoef f κ m).comp ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_)
  first
  | rfl
  | simp [jetCoef_mk, jetTrunc]

theorem jetCoef_map {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ')
    (hφ' : ∀ i, MvPolynomial.map f (φ i) ∈ orig K κ') :
    (jetCoef f κ' m).comp ((jetMap φ hφ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetMap (fun i => MvPolynomial.map f (φ i)) hφ' : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.C a))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.C a)))
    rw [jetCoef_mk]
    simp
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.X i))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.X i)))
    rw [jetCoef_mk]
    simp

end Ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)

abbrev jc (n m : ℕ) : Jet T.V (Fin n × Fin d) m →+* Jet T.Fr (Fin n × Fin d) m :=
  jetCoef (algebraMap T.V T.Fr) (Fin n × Fin d) m

theorem xL_w (m : ℕ) : (spMap (jc (d := d) 1 m) ≫ (xT m).left) ≫ I.G.G.hom =
    spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) ≫ spMap (algebraMap T.V T.Fr) := by
  rw [Category.assoc, Over.w]
  simp only [spMap_comp']
  simp only [jOG, Over.mk_hom, Category.comp_id, spMap_comp']
  congr 1
  ext r
  simp only [jc, jetCoef, RingHom.comp_apply]
  erw [Ideal.Quotient.lift_mk]
  simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  rfl

def xL (m : ℕ) : Sp (Jet T.Fr (Fin 1 × Fin d) m) ⟶ I.t'.G.left :=
  I.m2.cart.1.lift (spMap (jc (d := d) 1 m) ≫ (xT m).left) (spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)))
    (xL_w I xT m)

theorem xL_fst (m : ℕ) : xL I xT m ≫ I.m2.φ = spMap (jc (d := d) 1 m) ≫ (xT m).left := I.m2.cart.1.lift_fst _ _ _

theorem xL_snd (m : ℕ) : xL I xT m ≫ I.t'.G.hom = spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) := I.m2.cart.1.lift_snd _ _ _

def xP (m : ℕ) : jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G :=
  Over.homMk (xL I xT m) (by
    show xL I xT m ≫ I.t'.G.hom = spMap _ ≫ 𝟙 _
    rw [xL_snd, Category.comp_id])

def xU (m : ℕ) : (letI := io.toAlgebra; jO y.1 d m 1) ⟶ Xo.univ.t.G :=
  letI := io.toAlgebra
  Over.homMk (xL I xT m ≫ I.m1.φ) (by
    show (xL I xT m ≫ I.m1.φ) ≫ Xo.univ.t.G.hom = spMap _ ≫ y.1.x
    rw [Category.assoc, I.m1.cart.1.w, ← Category.assoc, xL_snd])

theorem ext2 {Z : Scheme.{0}} {a b : Z ⟶ I.t'.G.left} (h1 : a ≫ I.m2.φ = b ≫ I.m2.φ)
    (h2 : a ≫ I.t'.G.hom = b ≫ I.t'.G.hom) : a = b := I.m2.cart.1.hom_ext h1 h2

end Pt

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ChartPrimTrSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (wPT : PrimTyG I.G),
    IsPrimG I.G wPT →
    letI := io.toAlgebra
    ∃ wP : PrimTy H Xo, IsPrim wP ∧
      ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
        (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
          LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
        ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
          LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ wP I.m1.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

def ChartTransportSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (B : Germ.FB T.V d (𝓞 E)) (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) d xT m) (wPT : PrimTyG I.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d B.G.F B.A.act tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    IsFrameG I.G (𝟙 (Sp T.V)) d xT B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad eT → IsPrimG I.G wPT →
    FrTrunc I.G (𝟙 (Sp T.V)) d xT eT → Rig0G I.G (𝟙 (Sp T.V)) d xT B.A.act eT wPT →
    letI := io.toAlgebra
    ∃ (B' : Germ.FB T.Fr d (𝓞 E)) (uvec : Lt1 Dw → Fin d → T.Fr) (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G)
      (e : ∀ m, FrTy y.1 d x m) (wP : PrimTy H Xo) (h : Germ.PS T.Fr 2 d)
      (hch : Formalism.L2.Pj.IsChart y.1 d B'.G.F B'.A.act uvec x)
      (hfr : IsFrame y.1 d x B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e) (hpr : IsPrim wP)
      (hg : B'.IsCanonGauge T.Fr h)
      (hr : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y.1 d x B'.A.act e wP 0)
          (homAt y.1.x (jetAug : Jet T.Fr (Fin 1 × Fin d) 0 →ₐ[T.Fr] T.Fr)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.1.x T.Fr) 1)),
      IsGenFibreChart (⟨d, B', uvec, x, e, wP, h, hch, hfr, hpr, hg, hr⟩ : ChartAt Xo c y.1) I
        B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad uvecT xT eT wPT

def FBMapSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (B : Germ.FB R d O), ∃ B' : Germ.FB R' d O,
      (∀ j, B'.G.F j = MvPowerSeries.map ψ (B.G.F j)) ∧ (∀ a j, B'.A.act a j = MvPowerSeries.map ψ (B.A.act a j)) ∧
      B'.ph1 = MvPowerSeries.map ψ B.ph1 ∧ B'.ph2 = MvPowerSeries.map ψ B.ph2 ∧ B'.sy = MvPowerSeries.map ψ B.sy ∧
      ∀ a, B'.ad a = MvPowerSeries.map ψ (B.ad a)

def ChartJetTrSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    letI := io.toAlgebra
    ∃ (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G),
      Formalism.L2.Pj.IsChart y.1 d (fun j => MvPowerSeries.map (algebraMap T.V T.Fr) (FT j))
        (fun a j => MvPowerSeries.map (algebraMap T.V T.Fr) (actT a j))
        (fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i)) x ∧
      (∀ m, (x' m).left ≫ I.m2.φ = spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin d) m) ≫ (xT m).left) ∧
      ∀ m, (x' m).left ≫ I.m1.φ = (x m).left

def ChartFrameTrSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (B : Germ.FB T.V d (𝓞 E)) (B' : Germ.FB T.Fr d (𝓞 E)) (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left))
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) d xT m) (wPT : PrimTyG I.G),
    (∀ j, B'.G.F j = MvPowerSeries.map (algebraMap T.V T.Fr) (B.G.F j)) →
    (∀ a j, B'.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (B.A.act a j)) →
    B'.ph1 = MvPowerSeries.map (algebraMap T.V T.Fr) B.ph1 → B'.ph2 = MvPowerSeries.map (algebraMap T.V T.Fr) B.ph2 →
    B'.sy = MvPowerSeries.map (algebraMap T.V T.Fr) B.sy →
    (∀ a, B'.ad a = MvPowerSeries.map (algebraMap T.V T.Fr) (B.ad a)) →
    IsChartG I.G (𝟙 (Sp T.V)) d B.G.F B.A.act tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    IsFrameG I.G (𝟙 (Sp T.V)) d xT B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad eT → IsPrimG I.G wPT →
    FrTrunc I.G (𝟙 (Sp T.V)) d xT eT → Rig0G I.G (𝟙 (Sp T.V)) d xT B.A.act eT wPT →
    letI := io.toAlgebra
    ∀ (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G),
      (∀ m, (x' m).left ≫ I.m2.φ = spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin d) m) ≫ (xT m).left) →
      (∀ m, (x' m).left ≫ I.m1.φ = (x m).left) →
      ∃ (e : ∀ m, FrTy y.1 d x m) (wP : PrimTy H Xo),
        IsFrame y.1 d x B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e ∧ IsPrim wP ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ (eL y.1 d x B'.A.act e wP 0)
            (homAt y.1.x (jetAug : Jet T.Fr (Fin 1 × Fin d) 0 →ₐ[T.Fr] T.Fr)).left)
          (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.1.x T.Fr) 1) ∧
        (∃ e' : ∀ m, FrTyG I.t' (𝟙 (Sp T.Fr)) d x' m, ∀ m, (e' m).IsGen ∧
          (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L
              (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)] J ≫ I.m2.φ) (cε 2)),
            LB.Gen.Corr I.G.PP.L _ _ _ _ c₂
              (LB.pullGen I.G.PP.L _ _ (eT m) (spMap (jetCoef (algebraMap T.V T.Fr) (Fin 2 × Fin d) m))) ∧
            LB.Gen.Maps (LB.linCombIso I.w2 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)]) (cε 2)) (e' m)
              (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
          ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L
              (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)] J ≫ I.m1.φ) (cε 2)),
            LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (e m) ∧
            LB.Gen.Maps (LB.linCombIso I.w1 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)]) (cε 2)) (e' m)
              (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)) ∧
        ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
          (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
            LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
            LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
          ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
            LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ wP I.m1.φ) ∧
            LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)


omit [StarRing (𝓞 E)] in
def FrTanBasisSt : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
    IsTanAt y.x w →
    ∃! a : Lt1 Dw → S, IsCombAt y.x (m := Fintype.card (Lt1 Dw))
      (fun i => y.u ((Fintype.equivFin (Lt1 Dw)).symm i).1 ((Fintype.equivFin (Lt1 Dw)).symm i).2)
      (fun i => a ((Fintype.equivFin (Lt1 Dw)).symm i)) w

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def ExpActOfSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S),
    IsExpOf C.B.G.F C.uvec φ → ∀ (a : 𝓞 E) (j : Fin C.d),
      MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
        MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) =>
          algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) •
            (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (φ j)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def IntChartStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V →
    ∀ (t : SAB H (Sp V)),
    IsProper ((Over.pullback (spMap (algebraMap V (FractionRing V)))).obj t.G).hom →
    ∀ {κ : Type} [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)),
      (∀ ℓ, IsTanAtG t (𝟙 (Sp V)) (tg ℓ)) →
      (∀ w, IsTanAtG t (𝟙 (Sp V)) w →
        ∃! a : κ → V, IsCombAtG t (𝟙 (Sp V)) (m := Fintype.card κ)
          (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) →
      ∀ [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
      ∃ (d : ℕ) (B : Germ.FB V d (𝓞 E)) (uvec : κ → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
        (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t),
        d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧
        IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uvec x ∧
        IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e ∧
        IsPrimG t wP ∧ FrTrunc t (𝟙 (Sp V)) d x e ∧ Rig0G t (𝟙 (Sp V)) d x B.A.act e wP ∧
        ∀ (k : ℕ) (F : LB.Sec (LPow t.G t.PP.L k (Over.mk (𝟙 (Sp V))))),
          ∃ f, IsGermG t (𝟙 (Sp V)) d x B.A.act e wP k F f

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
