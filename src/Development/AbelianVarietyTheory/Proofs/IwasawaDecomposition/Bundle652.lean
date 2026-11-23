module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle636
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle638
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CxPts

namespace GlobalTheory.ConstFn

variable {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ}

theorem ev_top_eq (a : Γ(X, ⊤)) (y : CxPts p σ) :
    ev p σ ⊤ a y = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (y.1.appTop.hom a) := by
  have h : ⊤ ≤ y.1 ⁻¹ᵁ (⊤ : X.Opens) := le_rfl
  show valR y.1 ⊤ a = _
  rw [valR, dite_eq_left h]
  rfl

theorem exists_ev_eq [UniversallyClosed p] [GeometricallyIntegral p] (a : Γ(X, ⊤)) :
    ∃ b : ℂ, ∀ y : CxPts p σ, ev p σ ⊤ a y = b := by
  have hZ : IsIntegral (pullback p (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := p) (spMap σ) _ _ (.of_hasPullback _ _)
  let fs := pullback.fst p (spMap σ)
  let sn := pullback.snd p (spMap σ)
  let e : ℂ →+* Γ(pullback p (spMap σ), ⊤) :=
    sn.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  letI : Algebra ℂ Γ(pullback p (spMap σ), ⊤) := e.toAlgebra
  have hcomp : (algebraMap ℂ Γ(pullback p (spMap σ), ⊤)).comp
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom) =
      fs.appTop.hom.comp p.appTop.hom := by
    have h : fs ≫ p = sn ≫ spMap σ := pullback.condition
    ext c
    have h' := congrArg (fun m : pullback p (spMap σ) ⟶ Sp F => m.appTop.hom c) h
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h'
    simp only [RingHom.comp_apply]
    refine Eq.trans ?_ h'.symm
    show sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
    simp
  have hint : IsIntegral ℂ (fs.appTop.hom a) := by
    obtain ⟨P, hP, h0⟩ := isIntegral_appTop_of_universallyClosed p a
    refine ⟨P.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (spMap σ).appTop.hom), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)
    (K := integralClosure ℂ Γ(pullback p (spMap σ), ⊤))).2 ⟨_, hint⟩
  have hr' : e r = fs.appTop.hom a := congrArg Subtype.val hr
  refine ⟨r, fun y => ?_⟩
  let z : Sp ℂ ⟶ pullback p (spMap σ) :=
    pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp])
  have h1 : z ≫ fs = y.1 := pullback.lift_fst _ _ _
  have h2 : z ≫ sn = 𝟙 _ := pullback.lift_snd _ _ _
  have h3 : y.1.appTop.hom a = z.appTop.hom (fs.appTop.hom a) := by
    rw [← h1, Scheme.Hom.comp_appTop]; rfl
  have h4 : z.appTop.hom (sn.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r := by
    have e₂ : (z ≫ sn).appTop = sn.appTop ≫ z.appTop := Scheme.Hom.comp_appTop _ _
    rw [h2] at e₂
    have e₃ := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) e₂
    exact Eq.trans e₃.symm (by simp)
  rw [ev_top_eq, h3, ← hr']
  show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (z.appTop.hom (sn.appTop.hom _)) = r
  rw [h4]
  simp

end GlobalTheory.ConstFn

theorem GlobalTheory.ConstFn.holoOn_univ_const : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim)
    (q : CxPts Y.str σ → ℂ), R.HoloOn Set.univ q → ∃ b : ℂ, ∀ z, q z = b := by
  intro F _ Y σ R q hq
  have hB := LB.isLB_triv Y.X
  have hs : (fun _ => q : (LB.triv Y.X).ι → CxPts Y.str σ → ℂ) ∈ R.holSec (LB.triv Y.X) := by
    refine ⟨⟨fun i j y hi _ => ?_, fun i y h => (h mem_ptsIn_top).elim⟩, fun i => hq.mono (Set.subset_univ _)⟩
    cases i; cases j
    rw [gv_self hB hi, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC Y.isProjOver R hB).2 ⟨_, hs⟩
  let M : Submodule ℂ ((LB.triv Y.X).ι → CxPts Y.str σ → ℂ) :=
    { carrier := {s | ∃ b : ℂ, ∀ i z, s i z = b}
      zero_mem' := ⟨0, fun _ _ => rfl⟩
      add_mem' := fun {s t} ⟨b, hb⟩ ⟨c, hc⟩ => ⟨b + c, fun i z => by simp [hb, hc]⟩
      smul_mem' := fun c s ⟨b, hb⟩ => ⟨c * b, fun i z => by simp [hb]⟩ }
  obtain ⟨b, hb⟩ : SecC.val x ∈ M := SecC.val_mem_of (fun s => by
    obtain ⟨b, hb⟩ := GlobalTheory.ConstFn.exists_ev_eq (p := Y.str) (σ := σ) (s.f PUnit.unit)
    exact ⟨b, fun i z => by cases i; exact hb z⟩) x
  refine ⟨b, fun z => ?_⟩
  have e := congrArg Subtype.val hx
  rw [AnRead.coe_valC] at e
  have := hb PUnit.unit z
  rw [e] at this
  exact this
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem riemannRoch_ne_bot_of_holomorphicSection_ne_bot : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ)
    (R : AnRead Y.str σ Y.dim) (D : Y.Dv), R.holSec (Y.lb D) ≠ ⊥ → Y.H0 D ≠ ⊥ := by
  intro F _ Y σ R D hR hH
  refine hR ?_
  have P := GlobalTheory.Cartier.presents_toLB D
  have hs : ∀ s : (Y.lb D).Sec, s = 0 := fun s => by
    have hm : P.rat s ∈ Y.H0 D := P.rat_mem s
    rw [hH, Submodule.mem_bot] at hm
    exact P.rat_injective (hm.trans (map_zero P.rat).symm)
  have hx : ∀ x : SecC Y.str σ (Y.lb D), x = 0 := fun x => by
    have hle : Submodule.span ℂ (Set.range (SecC.of Y.str σ : (Y.lb D).Sec → _)) ≤ ⊥ :=
      Submodule.span_le.2 (by
        rintro _ ⟨s, rfl⟩
        rw [hs s, map_zero]
        exact zero_mem _)
    exact (Submodule.mem_bot ℂ).1 (hle (SecC.span_range_of.ge Submodule.mem_top))
  have hb := GlobalTheory.AnRead.bijective_valC Y.isProjOver R P.isLB
  refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
  obtain ⟨x, hxf⟩ := hb.2 ⟨f, hf⟩
  rw [hx x, map_zero] at hxf
  exact (congrArg Subtype.val hxf).symm

end GlobalTheory.ShFam.Hor
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_principalCMTriple_exponential_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)), IsTypeFn H DB.p DB.q ty → IsPeriod DB ty PB → ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB ty PB ex := by
  first | exact @GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod | exact GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod | (intros; apply GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PointDer

open CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

def dualHom {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) : A →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr (D f)
  map_one' := by
    have h1 : D 1 = 0 := by simpa using hm 1 1
    ext <;> simp [h1]
  map_mul' f f' := by ext <;> simp [hm, mul_comm]
  map_zero' := by ext <;> simp
  map_add' f f' := by ext <;> simp

@[simp] theorem dualHom_fst {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) (f : A) : (dualHom e D hm f).fst = e f := by
  simp [dualHom]

@[simp] theorem dualHom_snd {A : Type} [CommRing A] (e : A →+* ℂ) (D : A →+ ℂ)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f) (f : A) : (dualHom e D hm f).snd = D f := by
  simp [dualHom]

theorem derivation_eq_zero_of_etale {k A : Type} [CommRing k] [CommRing A] {g : ℕ}
    (φ : MvPolynomial (Fin g) k →+* A) (hφ : φ.Etale) (e : A →+* ℂ) (D : A →+ ℂ)
    (h0 : ∀ a, D (φ (MvPolynomial.C a)) = 0)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f)
    (hX : ∀ i, D (φ (MvPolynomial.X i)) = 0) : D = 0 := by
  have hP : ∀ q, D (φ q) = 0 := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add q r hq hr => rw [map_add (f := _), map_add (f := _), hq, hr, add_zero]
    | mul_X q i hq => rw [map_mul, hm, hq, hX]; simp
  let F : A →+* DualNumber ℂ := dualHom e D hm
  let F₀ : A →+* DualNumber ℂ := (algebraMap ℂ (DualNumber ℂ)).comp e
  have hFF : ∀ q, F (φ q) = F₀ (φ q) := fun q => by
    ext <;> simp [F, F₀, hP, TrivSqZeroExt.algebraMap_eq_inl]
  let _ := φ.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) k) (DualNumber ℂ) := (F₀.comp φ).toAlgebra
  have _ : Algebra.Etale (MvPolynomial (Fin g) k) A := hφ
  let G : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ := { F with commutes' := hFF }
  let G₀ : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ := { F₀ with commutes' := fun q => rfl }
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom hnil G G₀
    (fun x => by simp [G, G₀, F, F₀])
  ext f
  have := congrArg (fun H : A →ₐ[MvPolynomial (Fin g) k] DualNumber ℂ => (H f).snd) hG
  simpa [G, G₀, F, F₀, TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.PointDer

namespace GlobalTheory.PointDer

open CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem exists_eq_fderiv : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source → ∀ (U : Y.affineOpens), x₀ ∈ CxPts.ptsIn p σ U.1 → ∀ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) → (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) → ∃ v : ReciprocityTheory.L2DbarEstimates.V n, ∀ g : Γ(Y, U.1), δ g = fderiv ℂ (CxPts.ev p σ U.1 g ∘ c.e.symm) (c.e x₀) v := by
  intro k _ Y p n σ c x₀ hx₀ U hU δ hδ0 hδm
  have hxc : x₀ ∈ ptsIn p σ c.U := c.source_subset hx₀
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 c.affine _
    ⟨mem_ptsIn.1 hU, mem_ptsIn.1 hxc⟩
  have hWc : Y.basicOpen g ≤ c.U := Y.basicOpen_le g
  have hWU : Y.basicOpen g ≤ U.1 := hfg ▸ Y.basicOpen_le f
  have hxW : x₀ ∈ ptsIn p σ (Y.basicOpen g) := mem_ptsIn.2 (hfg ▸ hxf)

  have hmU : ∀ a b, δ (a * b) = evHom hU a * δ b + evHom hU b * δ a := fun a b => by
    rw [hδm, ev_eq hU, ev_eq hU]
  let ψU := dualHom (evHom hU) δ hmU
  letI : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen g) := (resG Y hWU).toAlgebra
  haveI : IsLocalization.Away f Γ(Y, Y.basicOpen g) :=
    U.2.isLocalization_of_eq_basicOpen f (homOfLE hWU) hfg.symm
  have hfu : IsUnit (ψU f) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualHom_fst, isUnit_iff_ne_zero, ← ev_eq hU]
    exact (mem_ptsIn_basicOpen hU f).1 (mem_ptsIn.2 hxf)
  let ψW : Γ(Y, Y.basicOpen g) →+* DualNumber ℂ := IsLocalization.Away.lift f hfu
  have hψW (a : Γ(Y, U.1)) : ψW (resG Y hWU a) = ψU a := IsLocalization.Away.lift_eq f hfu a
  have hψW1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ψW = evHom hxW := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    change (ψW (resG Y hWU a)).fst = evHom hxW (resG Y hWU a)
    rw [hψW, dualHom_fst, ← ev_eq, ← ev_eq, ev_res _ hxW]
  have hfst (a : Γ(Y, Y.basicOpen g)) : (ψW a).fst = evHom hxW a := RingHom.congr_fun hψW1 a

  let v : ReciprocityTheory.L2DbarEstimates.V n := WithLp.toLp 2 (fun b => (ψW (resG Y hWc (c.x b))).snd)

  have hdW := fun a : Γ(Y, Y.basicOpen g) => c.differentiableAt_ev a hx₀ hxW
  let dW : Γ(Y, Y.basicOpen g) → ℂ := fun a => fderiv ℂ (ev p σ _ a ∘ c.e.symm) (c.e x₀) v
  have hdadd (a b) : dW (a + b) = dW a + dW b := by
    have e : ev p σ _ (a + b) ∘ c.e.symm = (ev p σ _ a ∘ c.e.symm) + (ev p σ _ b ∘ c.e.symm) :=
      funext fun _ => ev_add _ _ _
    simp only [dW, e, fderiv_add (hdW a) (hdW b), ContinuousLinearMap.add_apply]
  have hdmul (a b) : dW (a * b) = evHom hxW a * dW b + evHom hxW b * dW a := by
    have e : ev p σ _ (a * b) ∘ c.e.symm = (ev p σ _ a ∘ c.e.symm) * (ev p σ _ b ∘ c.e.symm) :=
      funext fun _ => ev_mul _ _ _
    simp only [dW, e, fderiv_mul (hdW a) (hdW b), Function.comp_apply, c.e.left_inv hx₀,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ← ev_eq hxW]
  have hn : ∀ᶠ w in 𝓝 (c.e x₀), c.e.symm w ∈ ptsIn p σ (Y.basicOpen g) :=
    Filter.eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn _)).mem_nhds
      (ChartGlue.mem_over c.e hx₀ hxW)) fun _ h => h.2

  let Dd : Γ(Y, Y.basicOpen g) →+ ℂ := AddMonoidHom.mk' (fun a => (ψW a).snd - dW a) fun a b => by
    simp only [map_add (f := _), TrivSqZeroExt.snd_add, hdadd]
    ring
  have hD : Dd = 0 := by
    refine derivation_eq_zero_of_etale ((resG Y hWc).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x))
      ?_ (evHom hxW) Dd ?_ ?_ ?_
    · have hR : (resG Y hWc).Etale := by
        letI : Algebra Γ(Y, c.U) Γ(Y, Y.basicOpen g) := (resG Y hWc).toAlgebra
        haveI : IsLocalization.Away g Γ(Y, Y.basicOpen g) :=
          c.affine.isLocalization_of_eq_basicOpen g (homOfLE hWc) rfl
        exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway g)
      exact RingHom.Etale.stableUnderComposition _ _ c.etale hR
    · intro a
      have e1 : (resG Y hWc) (MvPolynomial.eval₂Hom (algX p c.U) c.x (MvPolynomial.C a)) =
          resG Y hWU (algX p U.1 a) := by
        rw [MvPolynomial.eval₂Hom_C, ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX,
          ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX]
      have e2 : dW (resG Y hWU (algX p U.1 a)) = 0 := by
        have e : ev p σ _ (resG Y hWU (algX p U.1 a)) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)] fun _ => σ a := by
          filter_upwards [hn] with w hw
          rw [Function.comp_apply, ← RingHom.comp_apply, GlobalTheory.TopForm.resG_comp_algX]
          exact ev_algX hw a
        show fderiv ℂ _ _ v = 0
        rw [e.fderiv_eq]
        simp
      simp only [Dd, AddMonoidHom.mk'_apply, RingHom.comp_apply, e1, hψW, ψU, dualHom_snd, hδ0, e2, sub_zero]
    · intro a b
      simp only [Dd, AddMonoidHom.mk'_apply, map_mul, TrivSqZeroExt.snd_mul, hfst, hdmul, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
    · intro i
      have e2 : dW (resG Y hWc (c.x i)) = v i := by
        have e : ev p σ _ (resG Y hWc (c.x i)) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)]
            EuclideanSpace.proj (𝕜 := ℂ) i := by
          filter_upwards [hn, c.e.open_target.mem_nhds (c.e.map_source hx₀)] with w hw hwt
          rw [Function.comp_apply, ev_res hWc hw, ← c.apply_eq _ (c.e.map_target hwt) i,
            c.e.right_inv hwt]
          rfl
        simp only [dW, e.fderiv_eq, ContinuousLinearMap.fderiv]
        rfl
      simp only [Dd, AddMonoidHom.mk'_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', e2]
      simp [v]
  refine ⟨v, fun a => ?_⟩
  have h1 := congrArg (fun D : Γ(Y, Y.basicOpen g) →+ ℂ => D (resG Y hWU a)) hD
  simp only [Dd, AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply, hψW, dualHom_snd, sub_eq_zero] at h1
  rw [show δ a = (ψU a).snd from (dualHom_snd _ _ _ a).symm, h1]
  have e : ev p σ _ (resG Y hWU a) ∘ c.e.symm =ᶠ[𝓝 (c.e x₀)] ev p σ U.1 a ∘ c.e.symm := by
    filter_upwards [hn] with w hw
    exact ev_res hWU hw a
  simp only [dW, e.fderiv_eq]

end GlobalTheory.PointDer
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam

theorem mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : TopologicalSpace.Closeds Y) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1)) (J : Finset (Fin m)), (Scheme.IdealSheafData.vanishingIdeal D).ideal U = Ideal.span {∏ i ∈ J, f i} → ∀ x : CxPts p σ, x ∈ CxPts.ptsIn p σ U.1 → (x.1 (IsLocalRing.closedPoint ℂ) ∈ D ↔ ∃ i ∈ J, CxPts.ev p σ U.1 (f i) x = 0) := by
  intro k _ Y p σ D U m f J h x hx
  have h1 := (ev_eq_zero_iff h hx).symm
  rw [LiesIn] at h1
  rw [h1, CxPts.ev_eq hx, map_prod, Finset.prod_eq_zero_iff]
  simp only [CxPts.ev_eq hx]

end GlobalTheory.ShFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPairFam


open HolTorsion in
theorem cubWeil_const_of_isHolTo : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : ReciprocityTheory.ChartRestriction.G.Semi.RigLB G) (c : ReciprocityTheory.ChartRestriction.G.Semi.CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1) → b₀ ∈ B → b₁ ∈ B → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → GlobalTheory.UU.CubWeil c N (x b₁) (x' b₁) (unitOn ζ) := by
  intro X G _ _ L c m N B y x x' ζ b₀ b₁ hN _ hB hx hx' htor hb₀ hb₁ h₀
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  let mk : G ⟶ G := (𝟙 G) ^ N
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ mk.left = (u ^ N).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst mk.left o
  let q := pullback.snd mk.left o
  have H : IsPullback p q mk.left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  let T : Over X := Over.mk (pullback.fst q q ≫ q)
  let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
    show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq])
  let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
    show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq, pullback.condition])
  have hu : u ^ N = 1 := (hkill T u).2 (by
    show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, Category.assoc])
  have hv : v ^ N = 1 := (hkill T v).2 (by
    show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, pullback.condition, Category.assoc])
  obtain ⟨e, he, -⟩ := UU.existsUnique_cubWeil c hu hv
  have hek : e.val ^ N = 1 := congrArg Units.val he.pow_eq_one
  have hpull : ∀ w ∈ B, UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
    intro w hw
    let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
      show z w ≫ pullback.fst q q ≫ q = y w
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
    have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
      show z w ≫ pullback.fst q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
    have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
      show z w ≫ pullback.snd q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
    have := he.comp h
    rw [e₁, e₂] at this
    exact this
  have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ := (hpull b₀ hb₀).unique h₀
  have e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
    Units.ext ((val_map_appTop (z b₁) e.val).trans
      ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))
  have := hpull b₁ hb₁
  rw [e₁, e₀] at this
  exact this

end GlobalTheory.TorsionPairFam
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan

theorem _root_.GlobalTheory.T.exists_compact_representatives_mod_torusPoints : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) → (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) → ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  first | exact @GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts | exact GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts | (intros; apply GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts <;> assumption)
end
