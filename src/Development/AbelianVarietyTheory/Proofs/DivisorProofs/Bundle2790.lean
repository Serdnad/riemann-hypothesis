module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem sharpOver_unique : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (u' : T' ⟶ F.X) (h : T ⟶ T'), h ≫ u' = u →
    GlobalTheory.Poinc.SharpOver F W P u → GlobalTheory.Poinc.SharpOver F W P' u' →
    ∃ α : P.A.left ⟶ P'.A.left, IsGrpPullback P.A P'.A h α ∧ LBIso P.L (P'.L.pull α) := by
  intro g n F W T T' P P' u u' h hu hS hS'
  subst hu
  obtain ⟨c, hc, pr, hpr, huniv, hbun⟩ := hS
  obtain ⟨c', hc', pr', hpr', huniv', hbun'⟩ := hS'
  obtain ⟨κ, κ₂, hκ, hsq, hw, -⟩ := GlobalTheory.SiegelPullComp.pb_cancel hc' hc
  have hκw : κ ≫ c'.A.hom = c.A.hom ≫ h := hκ.1.w
  obtain ⟨x₀, hx₀, -⟩ := huniv' (Over.mk (P.A.hom ≫ h)) (fun a => pushPt hκw (pr a))
  let α : P.A.left ⟶ P'.A.left := x₀.left
  have hα : ∀ a, α ≫ (pr' a).left = (pr a).left ≫ κ := fun a => congrArg (fun q => q.left) (hx₀ a)
  have hαw : α ≫ P'.A.hom = P.A.hom ≫ h := Over.w x₀

  have ext' : ∀ {T₁ : Over T'} (v w : T₁ ⟶ P'.A), (∀ a, (v ≫ pr' a).left = (w ≫ pr' a).left) → v = w := by
    intro T₁ v w e
    obtain ⟨_, -, hu⟩ := huniv' T₁ (fun a => w ≫ pr' a)
    exact (hu v fun a => Over.OverMorphism.ext (e a)).trans (hu w fun _ => rfl).symm
  have key : ∀ {Z : Scheme.{0}} (z₁ : Z ⟶ P'.A.left) (z₂ : Z ⟶ T), z₁ ≫ P'.A.hom = z₂ ≫ h →
      ∃! m : Z ⟶ P.A.left, m ≫ α = z₁ ∧ m ≫ P.A.hom = z₂ := by
    intro Z z₁ z₂ e
    have ea : ∀ a, (z₁ ≫ (pr' a).left) ≫ c'.A.hom = z₂ ≫ h := fun a => by
      rw [Category.assoc, Over.w (pr' a), e]
    let ya : Fin 8 → (Over.mk z₂ ⟶ c.A) := fun a =>
      Over.homMk (hκ.1.lift (z₁ ≫ (pr' a).left) z₂ (ea a)) (hκ.1.lift_snd _ _ _)
    have hya : ∀ a, (ya a).left ≫ κ = z₁ ≫ (pr' a).left := fun a => hκ.1.lift_fst _ _ _
    obtain ⟨x, hx, hxu⟩ := huniv (Over.mk z₂) ya
    have hxw : x.left ≫ P.A.hom = z₂ := Over.w x
    refine ⟨x.left, ⟨?_, hxw⟩, fun m ⟨hm₁, hm₂⟩ => ?_⟩
    · have w₁ : (x.left ≫ α) ≫ P'.A.hom = z₂ ≫ h := by rw [Category.assoc, hαw, ← Category.assoc, hxw]
      have := ext' (T₁ := Over.mk (z₂ ≫ h)) (Over.homMk (x.left ≫ α) w₁) (Over.homMk z₁ e) fun a => by
        show (x.left ≫ α) ≫ (pr' a).left = z₁ ≫ (pr' a).left
        rw [Category.assoc, hα, ← Category.assoc, ← hya a, ← hx a]; rfl
      exact congrArg (fun q => q.left) this
    · have := hxu (Over.homMk m hm₂) fun a => Over.OverMorphism.ext (hκ.1.hom_ext (by
        show (m ≫ (pr a).left) ≫ κ = (ya a).left ≫ κ
        rw [Category.assoc, ← hα, ← Category.assoc, hm₁, hya]) (by
        show (m ≫ (pr a).left) ≫ c.A.hom = (ya a).left ≫ c.A.hom
        rw [Category.assoc, Over.w (pr a), hm₂]; exact (Over.w (ya a)).symm))
      exact congrArg (fun q => q.left) this
  have hpb : IsPullback α P.A.hom P'.A.hom h := by
    refine ⟨⟨hαw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (key s.fst s.snd s.condition).exists.choose)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.1)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.2)
      (fun s m h₁ h₂ => (key s.fst s.snd s.condition).unique ⟨h₁, h₂⟩
        (key s.fst s.snd s.condition).exists.choose_spec)⟩⟩
  have hmul : ∀ (T₀ : Over T) (x y : T₀ ⟶ P.A) (x₁ y₁ : Over.mk (T₀.hom ≫ h) ⟶ P'.A),
      x₁.left = x.left ≫ α → y₁.left = y.left ≫ α → (x₁ * y₁).left = (x * y).left ≫ α := by
    intro T₀ x y x₁ y₁ hx hy
    have wz : ((x * y).left ≫ α) ≫ P'.A.hom = (Over.mk (T₀.hom ≫ h)).hom := by
      rw [Category.assoc, hαw, ← Category.assoc, Over.w (x * y)]; rfl
    have := ext' (x₁ * y₁) (Over.homMk ((x * y).left ≫ α) wz) fun a => by
      haveI := hpr a
      haveI := hpr' a
      rw [MonObj.mul_comp]
      have e := hκ.2 T₀ (x ≫ pr a) (y ≫ pr a) (x₁ ≫ pr' a) (y₁ ≫ pr' a)
        (by show x₁.left ≫ (pr' a).left = x.left ≫ (pr a).left ≫ κ; rw [hx, Category.assoc, hα])
        (by show y₁.left ≫ (pr' a).left = y.left ≫ (pr a).left ≫ κ; rw [hy, Category.assoc, hα])
      rw [e, ← MonObj.mul_comp]
      show ((x * y).left ≫ (pr a).left) ≫ κ = ((x * y).left ≫ α) ≫ (pr' a).left
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hα a).symm).trans (Category.assoc _ _ _).symm)
    exact congrArg (fun q => q.left) this
  refine ⟨α, ⟨hpb, hmul⟩, ?_⟩
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr ab.1) (pr ab.2)).left ≫ κ₂ = α ≫ (lift (pr' ab.1) (pr' ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (α ≫ P'.A.hom)) (T' := P.A)
      (𝟙 P.A.left) (pr ab.1) (pr ab.2) (Z := P'.A) α (pr' ab.1) (pr' ab.2)
      ((Category.id_comp _).trans (hα ab.1).symm) ((Category.id_comp _).trans (hα ab.2).symm))
  let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
  have l1 : (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB _ ε
  have l2 : (LB.LinComb (c'.P.pull κ₂) q ε).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c'.P.pull κ₂) (pull_isLB c'.isLB κ₂) q ε
  have l3 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
  have refl1 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P'.L.pull α) ((LB.LinComb c'.P q' ε).pull α) := GlobalTheory.SiegelPullComp.iso_pull α hbun'
  have i3 : LBIso ((LB.LinComb c'.P q' ε).pull α) (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) :=
    LBIso.chartPull (chartPullOut c'.P q' ε α _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) ε) (LB.LinComb (c'.P.pull κ₂) q ε) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c'.P κ₂ q (fun ab => α ≫ q' ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c'.P.pull κ₂) q ε) (LB.LinComb c.P q ε) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q ε
  have h1 := pull_isLB P'.isLB α
  have h2 := pull_isLB l0 α
  have chain : LBIso (P'.L.pull α) (LB.LinComb c.P q ε) :=
    LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5))
  exact LBIso.trans P.isLB l3 h1 hbun chain.symm

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_genericFibre_pullback_siegelTrait_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (f : T.V →+* W) (fK : FractionRing T.V →+* FractionRing W), (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left, IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧ κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) := by
  first | exact @GlobalTheory.Poinc.GenFibre.exists_generic_pullback | exact GlobalTheory.Poinc.GenFibre.exists_generic_pullback | (intros; apply GlobalTheory.Poinc.GenFibre.exists_generic_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.sharp_polarization_pullback_stable : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  first | exact @GlobalTheory.Poinc.sharpOver_pullback | exact GlobalTheory.Poinc.sharpOver_pullback | (intros; apply GlobalTheory.Poinc.sharpOver_pullback <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.model_weight_gap_l1_card_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (u1 : GlobalTheory.AllWt.Weight Dw) (g : ℝ), (∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 → g ≤ (u1 τ a : ℝ) - u1 τ b) → ∀ k : U.Comp, (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ (U.X k).p0 → g ≤ (modelWt U (wtOf Dw u1 0) k τ a : ℝ) - modelWt U (wtOf Dw u1 0) k τ b) ∧ (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (modelWt U (wtOf Dw u1 0) k τ b : ℝ) - modelWt U (wtOf Dw u1 0) k τ a) ∧ (∑ τ, ∑ a, |(modelWt U (wtOf Dw u1 0) k τ a : ℝ)|) = GlobalTheory.CovHt.l1 u1 ∧ (U.X k).Ψ.card = Nat.card (GlobalTheory.AllWt.Psi H) := by
  first | exact @GlobalTheory.ModelWtGap.model_weight_gap_l1_card | exact GlobalTheory.ModelWtGap.model_weight_gap_l1_card | (intros; apply GlobalTheory.ModelWtGap.model_weight_gap_l1_card <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyDatum_false_of_modelSection_zero : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)), KeyOn (RingHom.id K) x G L σ y → (∀ i, σ.f i = 0) → False := by
  first | exact @GlobalTheory.KeyEven.not_keyOn_of_sec_zero | exact GlobalTheory.KeyEven.not_keyOn_of_sec_zero | (intros; apply GlobalTheory.KeyEven.not_keyOn_of_sec_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → IsLieBasis y → NzFib σ → KeyOn (h.comp f) x G L σ y → ∀ [IsCommMonObj ((Over.pullback (spMap f)).obj G)], ∃ (L' : RigLB ((Over.pullback (spMap f)).obj G)) (σ' : L'.L.Sec) (y' : Fin x.P.g → (epsR B ⟶ (Over.pullback (spMap f)).obj G)), LBIso (L.L.pull (pullback.fst G.hom (spMap f))) L'.L ∧ IsLieBasis y' ∧ NzFib σ' ∧ KeyOn h x ((Over.pullback (spMap f)).obj G) L' σ' y' := by
  first | exact @GlobalTheory.KeyEvenBC.keyOn_pullback | exact GlobalTheory.KeyEvenBC.keyOn_pullback | (intros; apply GlobalTheory.KeyEvenBC.keyOn_pullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyDatum_scale_sections_by_constant : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)) (a : K) (th : x.P.L.Sec) (hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus th), (∀ i, th.f i = constFn x.P.A.hom _ a * x.th.f i) → (∀ i, σ'.f i = constFn G.hom _ a * σ.f i) → KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, x.v, x.basis⟩ G L σ' y := by
  first | exact @GlobalTheory.KeyEven.keyOn_scale | exact GlobalTheory.KeyEven.keyOn_scale | (intros; apply GlobalTheory.KeyEven.keyOn_scale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_fanOrder_ideal_glued_clopen_pieces : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) {ι : Type} [Fintype ι] (W : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ), (∀ c, IsClopen (W c)) → (∀ x, ∃! c, x ∈ W c) → (∀ c, 1 ≤ d c) → (∀ c, ∀ x ∈ (J c).support, x ∈ W c ∧ x ∉ Set.range j) → (∀ c (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j → ξ (closedPoint T.V) ∈ W c → ∃ a : ℕ, (a : ℝ) = d c * φ.evalZ T.β ∧ idlAlong (J c) ξ = Ideal.span {T.ϖ ^ a}) → ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range j) ∧ ValOn F j φ J' d' := by
  first | exact @GlobalTheory.Poinc.exists_valOn_of_pieces | exact GlobalTheory.Poinc.exists_valOn_of_pieces | (intros; apply GlobalTheory.Poinc.exists_valOn_of_pieces <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.siegelTrait_characterGroup_finrank_le_genus_of_three_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)), 3 ≤ n → ∀ T : Trait F, Module.finrank ℤ T.D.toPre.X ≤ g := by
  first | exact @GlobalTheory.Poinc.Trait.finrank_le_of_three_le | exact GlobalTheory.Poinc.Trait.finrank_le_of_three_le | (intros; apply GlobalTheory.Poinc.Trait.finrank_le_of_three_le <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_lieBasis_lift_model_vectors : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x x' : KeyIn K) (hg' : x'.P.g = x.P.g) (y y' : Fin x.P.g → (epsR K ⟶ G)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, IsLieComb (M i) y (y' i)) → ∃ (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv : IsLieBasis v), (∀ i, IsLieComb (M i) x.v (v i)) ∧ KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ G L σ y' := by
  first | exact @GlobalTheory.LieLift.main | exact GlobalTheory.LieLift.main | (intros; apply GlobalTheory.LieLift.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.mumfordBundle_trait_fibre_eq_universal : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W) (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left), IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ → κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β → ∀ (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left), IsSquare (κ ≫ T.α) α₂ → LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β))) (F.univ.P.pull α₂) := by
  first | exact @GlobalTheory.Poinc.lam_trait_fibre_eq_univ | exact GlobalTheory.Poinc.lam_trait_fibre_eq_univ | (intros; apply GlobalTheory.Poinc.lam_trait_fibre_eq_univ <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.exists_elt_prescribed_valuations_balanced_archimedean : ∀ (K : Type) [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ), (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → ∃ C : ℝ, ∀ τ : ℕ, ∃ α : K, α ≠ 0 ∧ (∀ la, (τ : ℝ) * e la ≤ (vLa la α : ℝ)) ∧ ∀ σ : K →+* ℂ, Real.log ‖σ α‖ ≤ τ * (cost e t - t σ) + C := by
  first | exact @GlobalTheory.CovHt.exists_elt_balanced | exact GlobalTheory.CovHt.exists_elt_balanced | (intros; apply GlobalTheory.CovHt.exists_elt_balanced <;> assumption)
end
