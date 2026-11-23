module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesInhabited
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle187
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.GoodTransport

theorem exists_equiv_of_lattices {La : Type} [AddCommGroup La] {g : ℕ} (P P' : La →+ (Fin g → ℂ))
    (hi : Function.Injective P) (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hi' : Function.Injective P') (hd' : DiscreteTopology P'.range) (hs' : Submodule.span ℝ (Set.range P') = ⊤) :
    ∃ φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ), ∀ a, φ (P a) = P' a := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  let L' : Submodule ℤ (Fin g → ℂ) := LinearMap.range P'.toIntLinearMap
  haveI : DiscreteTopology L := hd
  haveI : DiscreteTopology L' := hd'
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ L' := ⟨hs'⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hi
  let e' : La ≃ₗ[ℤ] L' := LinearEquiv.ofInjective P'.toIntLinearMap hi'
  let b := Module.Free.chooseBasis ℤ L
  let b₀ := b.map e.symm
  let b' := b₀.map e'
  let φ := (b.ofZLatticeBasis ℝ L).equiv (b'.ofZLatticeBasis ℝ L') (Equiv.refl _)
  have key : (φ.toLinearMap.restrictScalars ℤ).comp P.toIntLinearMap = P'.toIntLinearMap := by
    refine b₀.ext fun k => ?_
    have h1 : P (b₀ k) = b.ofZLatticeBasis ℝ L k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      exact congrArg Subtype.val (e.apply_symm_apply (b k))
    have h2 : P' (b₀ k) = b'.ofZLatticeBasis ℝ L' k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      rfl
    change φ (P (b₀ k)) = P' (b₀ k)
    rw [h1, h2, Module.Basis.equiv_apply]
    rfl
  exact ⟨φ, fun a => LinearMap.congr_fun key a⟩

theorem ex_eq_iff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z w : Fin g → ℂ) :
    u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  have := u.ex_add (z - w) w
  rw [sub_add_cancel] at this
  rw [← u.ker, this]
  exact mul_eq_right

def imHerm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (herm Hm z w).im)
    (fun _ _ _ => by simp [herm])
    (fun r z w => by
      rw [herm, herm, smul_dotProduct, Complex.smul_im])
    (fun _ _ _ => by simp [herm, Matrix.mulVec_add])
    (fun r z w => by
      rw [herm, herm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, star_trivial])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem fibre_marks {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) {y₀ : Sp ℂ ⟶ Xo.X}
    (hy : y₀ = Fu.u i P) {s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀) {g : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (h : (Fin g₀ → ℂ) → (Fin g → ℂ))
    (hh : ∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) :
    (∀ (a : 𝓞 E) z, u.ex (h z) ≫ o.t.act.act a = u.ex (h fun k => ty k (a : E) * z k)) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        o.eta a = u.ex (h ((l.M : ℂ)⁻¹ • P (Fu.t i a)))) ∧
      ∀ a, o.etaA a = u.ex (h ((l.A : ℂ)⁻¹ • P (Fu.t i a))) := by
  subst hy
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x.left ≫ m.toSABMap.φ = y.left ≫ m.toSABMap.φ → x = y :=
    fun x y h => Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w x, Over.w y]))
  refine ⟨fun a z => inj _ _ ?_, fun a ha => inj _ _ ?_, fun a => inj _ _ ?_⟩
  · rw [hh, Fu.ex_lin i P hP, Over.comp_left, Over.comp_left, ← hh, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  · rw [hh, ← Fu.ex_eta i P hP a ha]
    exact m.eta a
  · rw [hh, ← Fu.ex_etaA i P hP a]
    exact m.etaA a

theorem exists_eta_eq (a : D.La) : ∃ a₁ ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta a = o.eta a₁ := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  refine ⟨y • a, Submodule.smul_mem_smul hy trivial, fun o => ?_⟩
  have : a = x • a + y • a := by rw [← add_smul, hxy, one_smul]
  conv_lhs => rw [this]
  rw [o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul hx trivial), _root_.one_mul]

theorem exists_transport {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)}
    (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) {P P' : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    (hP' : IsPeriod (Fu.Di i) ty P') {y₀ y₀' : Sp ℂ ⟶ Xo.X} (hy : y₀ = Fu.u i P) (hy' : y₀' = Fu.u i P')
    {s s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀)
    (m' : ObjMap o' Xo.univ y₀') {g g' : ℕ} (u : HolUnif o.t.G o.t.PP.L g) (u' : HolUnif o'.t.G o'.t.PP.L g')
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {κ : u.Λ → ℂ} {κ' : u'.Λ → ℂ}
    (hAH : u.IsAH Hm κ) (hAH' : u'.IsAH Hm' κ') : ∃ φ, IsTransport o o' u u' Hm Hm' φ := by
  obtain ⟨h, hex, hΛ, hE, -⟩ := FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P y₀ s o m g u Hm κ hP hy hAH
  obtain ⟨h', hex', hΛ', hE', -⟩ :=
    FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P' y₀' s' o' m' g' u' Hm' κ' hP' hy' hAH'
  obtain ⟨a1, a2, a3⟩ := fibre_marks Fu i hP hy m u h hex
  obtain ⟨b1, b2, b3⟩ := fibre_marks Fu i hP' hy' m' u' h' hex'
  obtain ⟨φ₀, hφ₀⟩ := exists_equiv_of_lattices P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
  let φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ) :=
    ((h.symm.restrictScalars ℝ).trans φ₀).trans (h'.restrictScalars ℝ)
  have hφ : ∀ z, φ (h z) = h' (φ₀ z) := fun z => congrArg (fun t => h' (φ₀ t)) (h.symm_apply_apply z)
  have lat : ∀ z, φ z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by
    obtain ⟨z, rfl⟩ := h.surjective z
    rw [hφ, hΛ, hΛ']
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, φ₀.injective ((hφ₀ a).trans ha)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hφ₀ a).symm⟩
  have exq : ∀ z w, u.ex z = u.ex w → u'.ex (φ z) = u'.ex (φ w) := fun z w hzw => by
    rw [ex_eq_iff] at hzw ⊢
    rw [← map_sub, lat]
    exact hzw
  have lin : ∀ (a : 𝓞 E) z, φ₀ (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * φ₀ z k := fun a z => by
    let T : (Fin g₀ → ℂ) →ₗ[ℝ] (Fin g₀ → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have : φ₀.toLinearMap.comp T = T.comp φ₀.toLinearMap := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => ?_
      have e1 : T (P x) = P (a • x) := funext fun k => (hP.1 a x k).symm
      have e2 : T (P' x) = P' (a • x) := funext fun k => (hP'.1 a x k).symm
      change φ₀ (T (P x)) = T (φ₀ (P x))
      rw [e1, hφ₀, hφ₀, e2]
    exact LinearMap.congr_fun this z
  have dv : ∀ (n : ℕ) x, φ₀ ((n : ℂ)⁻¹ • P x) = (n : ℂ)⁻¹ • P' x := fun n x => by
    have e : ∀ v : Fin g₀ → ℂ, (n : ℂ)⁻¹ • v = (n : ℝ)⁻¹ • v := fun v => by
      rw [← Complex.coe_smul]; simp
    rw [e, e, map_smul, hφ₀]
  refine ⟨φ, lat, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · obtain ⟨z, rfl⟩ := h.surjective z
    rw [a1] at hw
    rw [exq _ _ hw, hφ, hφ, b1, lin]
  · obtain ⟨z, rfl⟩ := h.surjective z
    obtain ⟨w, rfl⟩ := h.surjective w
    let j := (h.restrictScalars ℝ).toLinearMap
    have : (imHerm Hm').compl₁₂ (φ.toLinearMap.comp j) (φ.toLinearMap.comp j) = (imHerm Hm).compl₁₂ j j := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => LinearMap.ext_on_range hP.2.2.2.1 fun y => ?_
      change (herm Hm' (φ (h (P x))) (φ (h (P y)))).im = (herm Hm (h (P x)) (h (P y))).im
      rw [hφ, hφ, hφ₀, hφ₀, hE, hE']
    exact LinearMap.congr_fun (LinearMap.congr_fun this z) w
  · obtain ⟨a₁, ha₁, e⟩ := exists_eta_eq (l := l) a
    rw [e o, a2 a₁ ha₁] at hz
    rw [exq _ _ hz, e o', b2 a₁ ha₁, hφ, dv]
  · rw [a3] at hz
    rw [exq _ _ hz, b3, hφ, dv]

theorem hasTransport_of_goodEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → 1 ≤ D.p + D.q → Formalism.L2.PjFree.GoodEmb c e → HasTransport Xo c U e := by
  intro E _ _ _ H D l Xo c O _ β Y U e B io hU hio hr hs hpq he y y' hy hy' hyU hyU' o o' ⟨m⟩ ⟨m'⟩ g g' u u' Hm Hm'
    κ κ' hAH hAH'
  let e₀ : Fin (Fintype.card (Pad.Letter D)) ≃ Pad.Letter D := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good E H l c e he).2.2.2 D _ e₀
  obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c e (e₀ j).1) hpq he hty
  have ov : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ toF Xo c = spMap e →
      (x ≫ toX Xo c) ≫ Xo.s = spMap (e.comp (IntermediateField.inclusion c.le).toRingHom) := fun x hx => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, DetExtendZero.spMap_comp]
  obtain ⟨i, P, hP, hu⟩ := Fu.onto _ (ov y hy)
  obtain ⟨i', P', hP', hu'⟩ := Fu.onto _ (ov y' hy')
  obtain rfl : i = i' := GlobalTheory.T.complexPoints_component_same_periodSpace E H D l Xo c O β Y U e _ _ Fu i i' P P' y y' B io hU hio hr hs hy hy' hyU hyU'
    hP hP' hu.symm hu'.symm
  exact exists_transport Fu i hP hP' hu.symm hu'.symm m m' u u' hAH hAH'

end GlobalTheory.DetLine.GoodTransport
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

theorem _root_.GlobalTheory.T.refining_degenerationData_tauCoordinate_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (hρ : Function.Injective ρ),
    Refines Q ρ D e → ∀ (a b : D.X) (k : (FractionRing R)ˣ), Q.TauCoord (e a) (e b) k →
      ∀ x : (FractionRing R')ˣ, IsTauCoord D a b x → ∃ u : R'ˣ, (x : FractionRing R') =
        algebraMap R' (FractionRing R') u * IsFractionRing.lift (A := R) (K := FractionRing R)
          (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) := by
  first | exact @GlobalTheory.RefTauCoord.main | exact GlobalTheory.RefTauCoord.main | (intros; apply GlobalTheory.RefTauCoord.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TraceLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem cast_trace_mul_bar (x y : 𝓞 E) :
    ((Algebra.trace ℤ (𝓞 E) (x * H.bar y) : ℤ) : ℝ) = GlobalTheory.LatticeBoundTests.trBil E x y := by
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := ((x * H.bar y : 𝓞 E) : E))
  rw [← Algebra.coe_trace_int, ← (RingHom.equivRatAlgHom E ℂ).sum_comp] at h1
  rw [GlobalTheory.LatticeBoundTests.trBil_apply, ← Complex.re_sum]
  have h2 : ∑ σ : E →+* ℂ, σ (x : E) * starRingEnd ℂ (σ (y : E))
      = ((Algebra.trace ℤ (𝓞 E) (x * H.bar y) : ℤ) : ℂ) := by
    rw [← map_intCast (algebraMap ℚ ℂ), h1]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← IsCMField.complexEmbedding_complexConj, ← H.bar_eq, ← map_mul]
    rfl
  rw [h2]; simp

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem exists_traceForm_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : 𝓞 E →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m ∧ B0.transpose = B0 ∧ (B0.map (Int.cast : ℤ → ℝ)).PosDef ∧ ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (H.bar a) := by
  intro E _ _ _ H
  classical
  let J := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let q : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let e : Module.Basis (Fin (Fintype.card J)) ℤ (𝓞 E) := (RingOfIntegers.basis E).reindex q
  refine ⟨Fintype.card J, Matrix.of fun i j => Algebra.trace ℤ (𝓞 E) (e i * H.bar (e j)),
    (Algebra.leftMulMatrix e).toRingHom, ?_, ?_, ?_, ?_⟩
  · rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact Module.finrank_pos
  · ext i j
    apply Int.cast_injective (α := ℝ)
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [cast_trace_mul_bar, cast_trace_mul_bar, GlobalTheory.LatticeBoundTests.trBil_symm]
  · have h := (GlobalTheory.LatticeBoundTests.trBil_posDef E).submatrix q.symm.injective
    convert h using 1
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.submatrix_apply, cast_trace_mul_bar, e,
      Module.Basis.reindex_apply]
  · intro a
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.leftMulMatrix_eq_repr_mul]
    have h1 : ∑ k, e.repr (a * e i) k * Algebra.trace ℤ (𝓞 E) (e k * H.bar (e j))
        = Algebra.trace ℤ (𝓞 E) (a * e i * H.bar (e j)) := by
      conv_rhs => rw [← e.sum_repr (a * e i)]

      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_mul_assoc, map_zsmul, smul_eq_mul]
    have h2 : ∑ k, Algebra.trace ℤ (𝓞 E) (e i * H.bar (e k)) * e.repr (H.bar a * e j) k
        = Algebra.trace ℤ (𝓞 E) (e i * H.bar (H.bar a * e j)) := by
      conv_rhs => rw [← e.sum_repr (H.bar a * e j)]

      rw [map_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, mul_smul_comm, map_zsmul, smul_eq_mul, mul_comm]
    rw [h1, h2, map_mul H.bar, bar_bar]
    congr 1; ring

end GlobalTheory.TraceLattice
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundleIso_const_of_genericIso_dvr : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → ∃ (v : LB.Iso P M) (c : K'), v.IsGen ∧ ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  first | exact @GlobalTheory.GenericIsoConst.exists_iso_const_of_generic | exact GlobalTheory.GenericIsoConst.exists_iso_const_of_generic | (intros; apply GlobalTheory.GenericIsoConst.exists_iso_const_of_generic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FlatGenDescent

variable {X X' : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

theorem exists_mul {M : LB X} (hM : M.IsLB) (u : LB.Sec M) (v : LB.Sec (AbLaw.pw M (-1))) :
    ∃ a : Γ(X, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : M.ι), r z ∈ M.U k →
      gs r z ⊤ a = gs r z (M.U k) (u.f k) * gs r z (M.U k) (v.f k) := by
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' M.U ⊤ (fun k => homOfLE le_top) hM.cover.ge
    (fun k => (show Γ(X, M.U k) from u.f k) * (show Γ(X, M.U k) from v.f k))
    (fun k l => fn_ext (V := M.U k ⊓ M.U l) fun y hy => by
      refine (gs_res (𝟙 X) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
      refine (gs_mul (𝟙 X) y _ hy.1 _ _).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy.2 _ _).symm)
      have h₁ := FlatSec.gs_sec_trans u (𝟙 X) y hy.1 hy.2
      have h₂ : gs (𝟙 X) y (M.U k) (v.f k) = (gm (𝟙 X) y (M.U k ⊓ M.U l) (M.g k l ^ (-1 : ℤ))).val *
          gs (𝟙 X) y (M.U l) (v.f l) := FlatSec.gs_sec_trans v (𝟙 X) y (k := k) (l := l) hy.1 hy.2
      rw [h₁, h₂, map_zpow, zpow_neg_one, _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul])
  refine ⟨a, fun Z r z k hk => ?_⟩
  exact (gs_res r z le_top hk a).symm.trans ((congrArg (gs r z (M.U k)) (ha k)).trans (gs_mul r z _ hk _ _))

def invSec (M : LB X) (π : X' ⟶ X) (t : LB.Gen (M.pull π)) (ht : t.IsGen) : LB.Sec ((AbLaw.pw M (-1)).pull π) :=
  genSec (M := (AbLaw.pw M (-1)).pull π) ⟨fun j => (t.s j)⁻¹⟩ fun i j => by
    have h := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    refine h.trans (congrArg₂ (· * ·) ?_ rfl)
    show (∏ _k : PUnit, (res _ (pullU π _ (M.g _ _))) ^ (1 : ℤ))⁻¹ =
      ∏ _k : PUnit, (res _ (pullU π _ (M.g _ _ ^ (-1 : ℤ)))) ^ (1 : ℤ)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, map_zpow, map_zpow, zpow_neg_one]

theorem exists_sec_of_flat {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Sp R) (π : X' ⟶ X) (f' : X' ⟶ Sp R') (H : IsPullback π f' f (spMap g))
    (M : LB X) (hM : M.IsLB) (t : LB.Gen (M.pull π)) (ht : t.IsGen) (m : Ideal Γ(X, ⊤)) (hm : m.IsMaximal) :
    ∃ u : LB.Sec M, ∀ z : X', (∀ a ∈ m, π z ∉ X.basicOpen a) → π z ∈ nonzeroLocus u := by
  classical
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H M hM (genSec t ht)
  obtain ⟨n', c', v, hv⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H _ (AbLaw.isLB_pw hM (-1))
    (invSec M π t ht)
  choose a ha using fun i j => exists_mul hM (u i) (v j)
  by_cases hne : ∃ i j, a i j ∉ m
  · obtain ⟨i, j, hij⟩ := hne
    refine ⟨u i, fun z hz => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    obtain ⟨y, x, hx, e⟩ := hm.exists_inv hij
    have e' := congrArg (gs π z ⊤) e
    rw [gs_add π z ⊤ trivial, gs_mul π z ⊤ trivial, gs_eq π z ⊤ trivial 1, map_one, map_one] at e'
    have hxu : ¬ IsUnit (gs π z ⊤ x) := fun h => hz x hx ((isUnit_gs_iff π z ⊤ trivial x).1 h)
    have hu1 : IsUnit (gs π z ⊤ y * gs π z ⊤ (a i j)) :=
      (IsLocalRing.isUnit_or_isUnit_of_add_one e').resolve_right hxu
    have hu2 := isUnit_of_mul_isUnit_right hu1
    rw [ha i j X' π z k hk] at hu2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff π z _ hk _).1 (isUnit_of_mul_isUnit_left hu2)⟩
  · push_neg at hne
    refine ⟨⟨fun _ => 0, fun _ _ => by simp⟩, fun z hz => False.elim ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    have hz' : z ∈ (M.pull π).U (fun _ => k) := mem_pull.2 hk
    have h₁ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hu z k hk)
    have h₂ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)⁻¹).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hv z k hk)
    have h₃ := congrArg₂ (· * ·) h₁ h₂
    rw [map_inv, Units.mul_inv, Finset.sum_mul_sum] at h₃
    apply (IsLocalRing.maximalIdeal.isMaximal (X'.presheaf.stalk z)).ne_top
    rw [Ideal.eq_top_iff_one, h₃]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    rw [_root_.mul_mul_mul_comm]
    refine Ideal.mul_mem_left _ _ ?_
    have h₄ : ¬ IsUnit (gs π z ⊤ (a i j)) := fun h => hz _ (hne i j) ((isUnit_gs_iff π z ⊤ trivial _).1 h)
    rw [ha i j X' π z k hk] at h₄
    exact h₄

theorem flat_of_basis {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R')
    (h : ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) : g.Flat := by
  let _ : Algebra R R' := g.toAlgebra
  have hb : Function.Bijective (Fintype.linearCombination R b) := by
    rw [Function.bijective_iff_existsUnique]
    intro r'
    refine (existsUnique_congr fun c => ?_).1 (h r')
    rw [Fintype.linearCombination_apply, eq_comm]
    rfl
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective _ hb).symm

theorem exists_sec_of_free : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R'), (∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) → ∀ (Z Z' : Scheme.{0}) (k' : Z' ⟶ Z) (f : Z ⟶ Sp R) (f' : Z' ⟶ Sp R'), IsPullback k' f' f (spMap g) → ∀ (O : Z.Opens), IsCompact (O : Set Z) → IsQuasiSeparated (O : Set Z) → ∀ (L : LB Z), L.IsLB → ∀ σ : LB.Gen ((L.pull k').pull (k' ⁻¹ᵁ O).ι), σ.IsGen → ∀ m : Ideal Γ(Z, O), m.IsMaximal → ∃ u : LB.Sec (L.pull O.ι), ∀ z : (k' ⁻¹ᵁ O).toScheme, (∀ a ∈ m, k' ((k' ⁻¹ᵁ O).ι z) ∉ Z.basicOpen a) → ∀ z₀ : O.toScheme, O.ι z₀ = k' ((k' ⁻¹ᵁ O).ι z) → z₀ ∈ nonzeroLocus u := by
  intro R R' _ _ g d b hb Z Z' k' f f' H O hO hO' L hL σ hσ m hm
  haveI : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hO
  haveI : QuasiSeparatedSpace O.toScheme := (isQuasiSeparated_iff_quasiSeparatedSpace _ O.isOpen).mp hO'
  have H' : IsPullback (k' ∣_ O) ((k' ⁻¹ᵁ O).ι ≫ f') (O.ι ≫ f) (spMap g) :=
    (isPullback_morphismRestrict k' O).paste_vert H
  obtain ⟨t₁, h₁⟩ := gen_chartPull (chartPullIn L (fun _ : PUnit => k') (fun _ => 1) (k' ⁻¹ᵁ O).ι) σ hσ
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullOut L (fun _ : PUnit => O.ι) (fun _ => 1) (k' ∣_ O) _
    fun _ => (morphismRestrict_ι k' O).symm) t₁ h₁
  let e : Γ(O.toScheme, ⊤) ≃+* Γ(Z, O) := O.topIso.commRingCatIsoToRingEquiv
  haveI := hm
  obtain ⟨u, hu⟩ := exists_sec_of_flat g (flat_of_basis g d b hb) (O.ι ≫ f) (k' ∣_ O) _ H' (L.pull O.ι)
    (LB.isLB_pull hL _) t ht (m.comap e) (Ideal.comap_isMaximal_of_surjective e e.surjective)
  refine ⟨u, fun z hz z₀ hz₀ => ?_⟩
  have hc : O.ι ((k' ∣_ O) z) = k' ((k' ⁻¹ᵁ O).ι z) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  obtain rfl : z₀ = (k' ∣_ O) z := O.ι.injective (hz₀.trans hc.symm)
  refine hu z fun a ha h => hz (e a) ha ?_
  rw [← hc]
  have := O.ι_image_basicOpen_topIso_inv (e a)
  rw [← this]
  exact ⟨_, (show _ ∈ O.toScheme.basicOpen (O.topIso.inv.hom (e a)) from (e.symm_apply_apply a).symm ▸ h), rfl⟩

end GlobalTheory.FlatGenDescent
end
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc


theorem _root_.GlobalTheory.T.functional_pos_on_squares_eq_sum_of_squares : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), (∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → 0 < lam (GlobalTheory.PolFan.sqForm l)) → ∃ (D m : ℕ) (a : Fin m → X), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → ∑ i, β (a i) (a i) = (D : ℤ) * lam β := by
  first | exact @GlobalTheory.Poinc.SumSqFunctional.sumsq_functional | exact GlobalTheory.Poinc.SumSqFunctional.sumsq_functional | (intros; apply GlobalTheory.Poinc.SumSqFunctional.sumsq_functional <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) := by
  first | exact @GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | exact GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | (intros; apply GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int <;> assumption)
end
