module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RingTheory.DualNumber
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ModelQC

theorem isCompact_of_le_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (W : Y.X.Opens), W ≤ U.1 → IsCompact (W : Set Y.X) := by
  intro E _ _ _ H Dw l Xo c Y U W hW
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  have := isProper_str c.F N
  have : IsProper Y.s := hs ▸ inferInstance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : IsNoetherian Y.X := ⟨⟩
  exact TopologicalSpace.NoetherianSpace.isCompact _

end GlobalTheory.ModelQC
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSObj

def chartPullComp {X X' Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (h : Y' ⟶ X') :
    ChartPull (L.pull (h ≫ F)) (L.pull F) h :=
  have hm : ∀ (y : Y') (J : PUnit → L.ι), y ∈ (L.pull (h ≫ F)).U J → h y ∈ (L.pull F).U J := fun y J hy =>
    (mem_pull (L := L) (F := F) (x := h y) (J := J)).2 ((mem_pull (L := L) (F := h ≫ F) (x := y) (J := J)).1 hy)
  { idx := fun J => J
    le := fun J y hy => hm y J hy
    g := fun y J J' hj hj' => (gm_pull_g L (h ≫ F) (𝟙 _) y J J' hj hj').trans
      (by rw [Category.id_comp]; exact (gm_pull_g L F h y J J' (hm y J hj) (hm y J' hj')).symm) }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_of_map {S X : Scheme.{0}} {t : SAB H X} {u : SAB H S} {f : X ⟶ S} (m : SABMap t u f)
    (hp : IsProper u.G.hom) (hA : Out.RelAmple u.G u.PP.L) : Out.RelAmple t.G t.PP.L := by
  have hpt : IsProper t.G.hom := MorphismProperty.of_isPullback m.cart.1 hp
  obtain ⟨w, hw, -⟩ := m.lin
  refine GlobalTheory.AmpleLocal.relAmple_of_locally X t.G t.PP.L t.PP.isLB inferInstance inferInstance fun x => ?_
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f x) trivial
  refine ⟨f ⁻¹ᵁ V, hx, ?_⟩
  have Hp : IsPullback ((t.G.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ m.φ) (t.G.hom ∣_ (f ⁻¹ᵁ V)) u.G.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict t.G.hom (f ⁻¹ᵁ V)).flip.paste_horiz m.cart.1
  obtain ⟨w', hw'⟩ : LBIso (t.PP.L.pull (t.G.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι)
      (u.PP.L.pull ((t.G.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ m.φ)) :=
    LBIso.chartPull (chartPullPull t.PP.L _) (chartPullComp u.PP.L m.φ _) ⟨w, hw⟩
  exact relAmple_pull (A' := Over.mk (t.G.hom ∣_ (f ⁻¹ᵁ V))) Hp u.PP.isLB (pull_isLB t.PP.isLB _)
    ((isGen_iff w').1 hw') V hV (fun y => y.2) hA

theorem proper_ample_kTriv {Dw : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj Dw l b s) {X : Scheme.{0}} {t : SAB H X} {f : X ⟶ S}
    (m : SABMap t o.t f) :
    IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨MorphismProperty.of_isPullback m.cart.1 o.proper, relAmple_of_map m o.proper o.ample,
    kTriv_pull m.cart o.t.PP.isLB t.PP.isLB ((isGen_iff w).1 hw) o.ktriv⟩

end GlobalTheory.KSObj
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartDer

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X)
    (V : X.Opens) (h : f (closedPoint R) ∈ V) : ⊤ ≤ f ⁻¹ᵁ V := by
  intro p _
  have hp : p ⤳ closedPoint R := (PrimeSpectrum.le_iff_specializes p (closedPoint R)).1 (le_maximalIdeal p.2.ne_top)
  exact hp.mem_open (f ⁻¹ᵁ V).2 h

end GlobalTheory.ChartDer
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpecLocalExt

theorem hom_ext_of_localizationAtPrime : ∀ (A : Type) [CommRing A] (X : Scheme.{0}) (a b : Sp A ⟶ X), (∀ (P : Ideal A) [P.IsPrime], spMap (algebraMap A (Localization.AtPrime P)) ≫ a = spMap (algebraMap A (Localization.AtPrime P)) ≫ b) → a = b := by
  intro A _ X a b h
  refine GlobalTheory.hom_ext_of_isLocalRing fun B _ _ φ => ?_
  let P : Ideal A := (IsLocalRing.maximalIdeal B).comap φ
  haveI : P.IsPrime := Ideal.comap_isPrime φ (IsLocalRing.maximalIdeal B)
  have hu : ∀ y : P.primeCompl, IsUnit (φ y) := fun y => by
    by_contra hy
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let ψ : Localization.AtPrime P →+* B := IsLocalization.lift hu
  have e : φ = ψ.comp (algebraMap A (Localization.AtPrime P)) := (IsLocalization.lift_comp hu).symm
  have h' := h P
  simp only [spMap] at h'
  rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, h']

end GlobalTheory.SpecLocalExt
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualUnitGerm

theorem primeSpectrum_subsingleton (k : Type) [Field k] : Subsingleton (PrimeSpectrum (DualNumber k)) := by
  have key : ∀ p : PrimeSpectrum (DualNumber k), p.asIdeal = maximalIdeal (DualNumber k) := by
    intro p
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) ?_
    intro x hx
    have hn : IsNilpotent x := by
      rcases TrivSqZeroExt.isUnit_or_isNilpotent x with h | h
      · exact absurd h hx
      · exact h
    exact (nilpotent_iff_mem_prime.1 hn) p.asIdeal p.isPrime
  exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩

theorem unit_eq_of_germ_eq : ∀ (k : Type) [Field k] (z : Sp (DualNumber k)) (u v : (DualNumber k)ˣ), gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn u) = gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn v) → u = v := by
  intro k _ z u v h
  have hs : Subsingleton (Sp (DualNumber k)) := primeSpectrum_subsingleton k
  have h1 : (unitOn u).val = (unitOn v).val := by
    refine TopCat.Presheaf.section_ext (Sp (DualNumber k)).sheaf ⊤ _ _ fun x hx => ?_
    obtain rfl : x = z := Subsingleton.elim _ _
    have := congrArg Units.val h
    rw [gm_val _ x ⊤ hx, gm_val _ x ⊤ hx] at this
    exact this
  exact Units.ext
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv).1 h1)

end GlobalTheory.DualUnitGerm
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullAutConst

theorem main : ∀ {A : Type} [CommRing A] (B' : Over (Sp A)) [GrpObj B'] {X : Scheme.{0}} (L : LB X) (π : B'.left ⟶ X), IsAbelianScheme B' → L.IsLB → ∀ w : LB.Iso (L.pull π) (L.pull π), w.IsGen → ∃ lam : Aˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (z : Z) (j : L.ι), π (x z) ∈ L.U j → gm x z _ (w.s (fun _ => j, fun _ => j)) = gm (x ≫ B'.hom) z ⊤ (unitOn lam) := by
  intro A _ B' _ X L π hB hL w hw
  have hP := (isGen_iff w).1 hw
  have hg : ∀ (j j' : L.ι) (x : B'.left), π x ∈ L.U j → π x ∈ L.U j' →
      gm (𝟙 B'.left) x _ ((L.pull π).g (fun _ => j) (fun _ => j')) = gm (𝟙 _ ≫ π) x _ (L.g j j') := by
    intro j j' x hj hj'
    have hp : (𝟙 B'.left : B'.left ⟶ B'.left) x ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    show gm _ x _ (∏ _k : PUnit, (res _ (pullU π _ (L.g j j'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ x _ hp _).trans (gm_pull _ π x (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)
  obtain ⟨u, hu⟩ := glue_unit (⊤ : B'.left.Opens)
    (fun j : L.ι => (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j)) (fun _ => le_top)
    (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (π x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, mem_pull.2 hj, mem_pull.2 hj⟩)
    (fun j => w.s (fun _ => j, fun _ => j)) (fun j j' x hx => by
      have hj : π x ∈ L.U j := mem_pull.1 hx.1.1
      have hj' : π x ∈ L.U j' := mem_pull.1 hx.2.1
      have e := hP _ (𝟙 _) x j j' (fun _ => j) (fun _ => j') hj hj' (mem_pull.2 hj) (mem_pull.2 hj')
      rw [hg j j' x hj hj', mul_inv_cancel] at e
      exact e.trans (_root_.one_mul _))
  let e₁ : Γ(Sp A, ⊤) ≃+* Γ(B'.left, ⊤) :=
    RingEquiv.ofBijective B'.hom.appTop.hom (GlobalTheory.globalFns_holds _ B' hB)
  let e₂ : A ≃+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  let e : A ≃+* Γ(B'.left, ⊤) := e₂.trans e₁
  refine ⟨Units.map e.symm.toMonoidHom u, fun Z x z j hj => ?_⟩
  have hl : pullU B'.hom ⊤ (unitOn (Units.map e.symm.toMonoidHom u)) = u :=
    Units.ext (e.apply_symm_apply u.val)
  have hm : x z ∈ (L.pull π).U (fun _ => j) ⊓ (L.pull π).U (fun _ => j) := ⟨mem_pull.2 hj, mem_pull.2 hj⟩
  refine (congrArg (gm x z _) (hu j)).symm.trans ((gm_res x z _ hm _).trans ?_)
  exact (congrArg (gm x z ⊤) hl).symm.trans (gm_pull x B'.hom z ⊤ trivial _)

end GlobalTheory.PullAutConst
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalProj

theorem signature_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ),
    ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) =
      2 * (Module.finrank ℚ E / 2 * p * q) := by
  intro E _ _ _ H p q
  have hdpos : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 := H.sqrt_neg_disc_sq
  have hre : H.rt0.re = 0 := by
    have e1 := congrArg Complex.re h0
    have e2 := congrArg Complex.im h0
    have e3 : H.rt0.re * H.rt0.im = 0 := by
      simp only [pow_two, Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at e2
      linarith
    simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.natCast_re] at e1
    rcases mul_eq_zero.mp e3 with h | h
    · exact h
    · exfalso
      rw [h] at e1
      nlinarith [sq_nonneg H.rt0.re]
  have hne : H.rt0 ≠ 0 := by
    intro h
    rw [h] at h0
    have : (H.d : ℂ) = 0 := by simpa using h0
    exact hdpos.ne' (by exact_mod_cast this)
  have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hnn : H.rt0 ≠ -H.rt0 := by
    intro h
    apply hne
    have : (2 : ℂ) * H.rt0 = 0 := by rw [two_mul]; nth_rewrite 2 [h]; ring
    simpa using this
  have key : ∀ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) = p * q := by
    intro τ
    have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      have hrtE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
        have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
        simpa using this
      rw [← map_pow, hrtE, h0]
      simp
    have hor : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rcases hor with h | h
    · rw [if_pos h, h, hconj, if_neg (Ne.symm hnn)]
    · rw [if_neg (by rw [h]; exact Ne.symm hnn), h, map_neg, hconj, neg_neg, if_pos rfl, mul_comm]
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card E ℂ, smul_eq_mul, NumberField.IsTotallyComplex.finrank]
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

end GlobalTheory.BalProj
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolAVPull

theorem grp_mul_transport {Y X : Scheme.{0}} (G : Over X) [GrpObj G] {a b : Y ⟶ X} (h : a = b)
    (u v : Over.mk a ⟶ G) (u' v' : Over.mk b ⟶ G) (hu : u'.left = u.left) (hv : v'.left = v.left) :
    (u' * v').left = (u * v).left := by
  subst h
  have e1 : u' = u := Over.OverMorphism.ext hu
  have e2 : v' = v := Over.OverMorphism.ext hv
  rw [e1, e2]

theorem polAV_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (T : SAB H X) (t : SAB H X') (g : X' ⟶ X) (φ : SABMap t T g) (K : Type) [Field K] (z : Sp K ⟶ X') (P₀ : PolAV (Sp K)) (θ : P₀.A.left ⟶ T.G.left), IsGrpPullback P₀.A T.G (z ≫ g) θ → LBIso P₀.L (T.PP.L.pull θ) → ∃ m : P₀.A.left ⟶ t.G.left, IsGrpPullback P₀.A t.G z m ∧ LBIso P₀.L (t.PP.L.pull m) := by
  intro E _ _ _ H X X' T t g φ K _ z P₀ θ hθ hL
  have hw : θ ≫ T.G.hom = (P₀.A.hom ≫ z) ≫ g := by rw [Category.assoc]; exact hθ.1.w
  let m : P₀.A.left ⟶ t.G.left := φ.cart.1.lift θ (P₀.A.hom ≫ z) hw
  have hm1 : m ≫ φ.φ = θ := φ.cart.1.lift_fst _ _ _
  have hm2 : m ≫ t.G.hom = P₀.A.hom ≫ z := φ.cart.1.lift_snd _ _ _
  refine ⟨m, ⟨?_, ?_⟩, ?_⟩
  · have s : IsPullback (m ≫ φ.φ) P₀.A.hom T.G.hom (z ≫ g) := by rw [hm1]; exact hθ.1
    exact IsPullback.of_right s hm2 φ.cart.1
  · intro T' x y x₀ y₀ hx hy
    apply φ.cart.1.hom_ext
    · let x₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (x₀.left ≫ φ.φ) (by
          show x₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w x₀]; rfl)
      let y₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (y₀.left ≫ φ.φ) (by
          show y₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w y₀]; rfl)
      have e1 := φ.cart.2 (Over.mk (T'.hom ≫ z)) x₀ y₀ x₁ y₁ rfl rfl
      let x₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (x.left ≫ θ) (by
        show x.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w x]; rfl)
      let y₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (y.left ≫ θ) (by
        show y.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w y]; rfl)
      have e2 := hθ.2 T' x y x₂ y₂ rfl rfl
      have e3 : (x₁ * y₁).left = (x₂ * y₂).left :=
        grp_mul_transport T.G (by simp [Category.assoc]) x₂ y₂ x₁ y₁
          (by simp [x₁, x₂, hx, Category.assoc, hm1]) (by simp [y₁, y₂, hy, Category.assoc, hm1])
      rw [← e1, e3, e2, Category.assoc, hm1]
    · rw [Category.assoc, hm2, Over.w]
      simp only [Over.mk_hom, ← Category.assoc, Over.w]
  · have h1 : LBIso (t.PP.L.pull m) (T.PP.L.pull θ) :=
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L m m rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame T.PP.L (fun _ : PUnit => θ) (fun _ => φ.φ) (fun _ => 1) m (fun _ => hm1.symm))
        (by obtain ⟨w, hw, -⟩ := φ.lin; exact ⟨w, hw⟩)
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.trans P₀.isLB (pull_isLB T.PP.isLB θ) (pull_isLB t.PP.isLB m) hL (ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm h1)

end GlobalTheory.PolAVPull
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio

variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R)

def IsRatio {N : ℕ} {α : Q.X} (σ σ' : Q.SecB N α) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)) : Prop :=
  ∀ z ∈ U, ∀ J, Good Q.P.L z J →
    IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J

def IsRem {N : ℕ} {α : Q.X} (σ' σp σp' : Q.SecB N α) (U : Q.P.A.left.Opens) (f g : Γ(Q.P.A.left, U)) : Prop :=
  ∀ z ∈ U, ∀ J, Good Q.P.L z J →
    sval σp (𝟙 _) z J = gs (𝟙 _) z U f * sval σp' (𝟙 _) z J + gs (𝟙 _) z U g * sval σ' (𝟙 _) z J

end GlobalTheory.HeatRatio
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocus

def KerKilledOn (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] [IsCommMonObj G]
    (P : LB (G2 G).left) (V : S'.Opens) : Prop := by
  letI : (Over.pullback V.ι).Monoidal := (Over.instBraidedPullback (f := V.ι)).toMonoidal
  letI : GrpObj ((Over.pullback V.ι).obj G) := Functor.grpObjObj (F := Over.pullback V.ι)
  exact ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G),
    (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull
        (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen,
        s.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledLocus
end
