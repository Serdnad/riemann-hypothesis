module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem functionFieldMap_fnOf (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {x : X}
    (hx : x ∈ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from hx)) s) =
      GlobalTheory.Cartier.fnOf (f ⁻¹ᵁ U) (GlobalTheory.Cartier.gen_mem hx) (f.app U s) := by
  rw [← GlobalTheory.Cartier.algebraMap_germ (show f x ∈ U from hx), functionFieldMap_algebraMap,
    ← GlobalTheory.Cartier.algebraMap_germ hx]
  congr 1
  exact Scheme.Hom.germ_stalkMap_apply f U x hx s

theorem fnOf_appLE (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    {x : X} (hx : x ∈ V) (s : Γ(Y, U)) :
    GlobalTheory.Cartier.fnOf V (GlobalTheory.Cartier.gen_mem hx) (f.appLE U V e s) =
      functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from e hx)) s) := by
  rw [functionFieldMap_fnOf f (e hx)]
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact X.presheaf.germ_res_apply (homOfLE e) _ _ _

end GlobalTheory.FnPull

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {Γ : Type} [Group Γ]

theorem functionFieldMap_act (ρ : Γ →* Aut X) (q : X ⟶ Y) [IsDominant q]
    (hq : ∀ g, (ρ g).asIso.hom ≫ q = q) (hs : Function.Surjective q) (g : Γ) [IsDominant (ρ g).asIso.hom]
    (c : Y.functionField) :
    functionFieldMap (ρ g).asIso.hom (functionFieldMap q c) = functionFieldMap q c := by
  obtain ⟨U₀, hη, s, rfl⟩ := Y.presheaf.exists_germ_eq c
  obtain ⟨x, hx⟩ := hs (genericPoint Y)
  have hx' : x ∈ q ⁻¹ᵁ U₀ := show q x ∈ U₀ from hx ▸ hη
  change functionFieldMap (ρ g).asIso.hom (functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)) =
    functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)
  rw [functionFieldMap_fnOf q hx' s]
  obtain ⟨e, hinv⟩ := isInvariantSection_app ρ q hq U₀ s g
  rw [← fnOf_appLE (ρ g).asIso.hom e hx', hinv]

theorem isInvariantSection_of_fnOf [Finite Γ] {ρ : Γ →* Aut X} {q : X ⟶ Y} [IsDominant q]
    (h : IsAffineQuotient ρ q) {V : Y.Opens} {x : X} (hx : x ∈ q ⁻¹ᵁ V) (c : Γ(X, q ⁻¹ᵁ V))
    (b : Y.functionField) (hc : GlobalTheory.Cartier.fnOf _ (GlobalTheory.Cartier.gen_mem hx) c = functionFieldMap q b) :
    IsInvariantSection ρ _ c := fun g ↦ by
  haveI : IsIso (ρ g).asIso.hom := Iso.isIso_hom _
  refine ⟨h.preimage_le V g, GlobalTheory.Cartier.fnOf_injective _ (GlobalTheory.Cartier.gen_mem hx) ?_⟩
  rw [fnOf_appLE (ρ g).asIso.hom (h.preimage_le V g) hx, hc,
    functionFieldMap_act ρ q h.comp_eq h.surjective.surj g]

end GlobalTheory.FnPull

namespace GlobalTheory.OrbitSep

theorem unitAt_of_forall_unitAt_fibre : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (y : W) (b : W.functionField),
    (∀ x, q x = y → UnitAt x (functionFieldMap q b)) → UnitAt y b := by
  intro X W _ _ Γ _ _ ρ q _ h y b hb
  have hsurj : Function.Surjective q := h.surjective.surj
  haveI := h.isIntegralHom
  let O : Set X := {x | GlobalTheory.Cartier.UnitAt x (functionFieldMap q b)}
  have hOo : IsOpen O := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hx
    exact ⟨U, fun z hz ↦ hU z hz, U.isOpen, hxU⟩
  have hV : IsOpen (q '' Oᶜ)ᶜ := (q.isClosedMap _ hOo.isClosed_compl).isOpen_compl
  let V : W.Opens := ⟨_, hV⟩
  obtain ⟨x₀, hx₀⟩ := hsurj y
  have hyV : y ∈ V := fun ⟨x, hx, e⟩ ↦ hx (hb x e)
  have hx₀V : x₀ ∈ q ⁻¹ᵁ V := show q x₀ ∈ V from hx₀ ▸ hyV
  have hUO : ∀ x ∈ q ⁻¹ᵁ V, GlobalTheory.Cartier.UnitAt x (functionFieldMap q b) := fun x hx ↦ by
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hUO
  have hgen := GlobalTheory.Cartier.gen_mem hx₀V
  have ha1 : GlobalTheory.Cartier.fnOf _ hgen (a : Γ(X, q ⁻¹ᵁ V)) = functionFieldMap q b := ha hgen
  have ha2 : GlobalTheory.Cartier.fnOf _ hgen ((a⁻¹ : Γ(X, q ⁻¹ᵁ V)ˣ) : Γ(X, q ⁻¹ᵁ V)) =
      functionFieldMap q b⁻¹ := by
    rw [map_units_inv, ha1, map_inv₀]
  obtain ⟨t, ht⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b ha1)
  obtain ⟨t', ht'⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b⁻¹ ha2)
  have htt : t * t' = 1 := h.app_injective V (by rw [map_mul, ht, ht', Units.mul_inv, map_one])
  let u : Γ(W, V)ˣ := ⟨t, t', htt, by rw [mul_comm]; exact htt⟩
  have hgenW := GlobalTheory.Cartier.gen_mem hyV
  have hbu : GlobalTheory.Cartier.fnOf V hgenW t = b := (functionFieldMap q).injective (by
    rw [GlobalTheory.FnPull.functionFieldMap_fnOf q hx₀V t, ht, ha1])
  rw [← hbu]
  exact GlobalTheory.Cartier.unitAt_fnOf hyV hgenW u

end GlobalTheory.OrbitSep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.DomPull

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]

theorem unitAt_map {x : X'} {f : X.functionField} (h : UnitAt (φ x) f) :
    UnitAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨φ.stalkMap x a, ha.map _, (functionFieldMap_algebraMap φ x a).symm⟩

abbrev unitsMap : X.functionFieldˣ →* X'.functionFieldˣ := Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom

theorem germOf_map_eq (D : CartierDiv X) {x : X'} {g g' : X.functionFieldˣ} (hg : D.IsEqn (φ x) g)
    (hg' : D.IsEqn (φ x) g') : germOf x (unitsMap φ g) = germOf x (unitsMap φ g') := by
  rw [germOf_eq_iff]
  have := unitAt_map φ (hg.iff_unitAt.1 hg')
  simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using this

def pullback (D : CartierDiv X) : CartierDiv X' :=
  show cartierGroup X' from ⟨fun x => germOf x (unitsMap φ (D.exists_isEqn (φ x)).choose), fun x => by
    obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (φ x)
    exact ⟨φ ⁻¹ᵁ U, hU, unitsMap φ g, fun y hy =>
      germOf_map_eq φ D (D.exists_isEqn (φ y)).choose_spec (hg _ hy)⟩⟩

theorem isEqn_pullback (D : CartierDiv X) {x : X'} {g : X.functionFieldˣ} (h : D.IsEqn (φ x) g) :
    (pullback φ D).IsEqn x (unitsMap φ g) :=
  germOf_map_eq φ D (D.exists_isEqn (φ x)).choose_spec h

theorem fnOf_app {U : X.Opens} (hU : genericPoint X' ∈ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    fnOf (φ ⁻¹ᵁ U) hU (φ.app U a) = GlobalTheory.functionFieldMap φ (fnOf U (gen_mem (x := φ (genericPoint X')) hU) a) := by
  rw [← algebraMap_germ (x := φ (genericPoint X')) hU a, functionFieldMap_algebraMap]
  erw [Scheme.Hom.germ_stalkMap_apply]
  exact (algebraMap_germ (X := X') hU _).symm

def pullEqns (D : CartierDiv X) (J : ((toLB D).pull φ).ι) : X'.functionFieldˣ :=
  unitsMap φ (J PUnit.unit).1.2

theorem fnOf_pull_g (D : CartierDiv X) (J J' : ((toLB D).pull φ).ι)
    (hg : genericPoint X' ∈ ((toLB D).pull φ).U J ⊓ ((toLB D).pull φ).U J') :
    fnOf _ hg (((toLB D).pull φ).g J J' : Γ(X', ((toLB D).pull φ).U J ⊓ ((toLB D).pull φ).U J')) =
      GlobalTheory.functionFieldMap φ (((J PUnit.unit).1.2 : X.functionField) / ((J' PUnit.unit).1.2 : X.functionField)) := by
  have h₀ : genericPoint X' ∈ φ ⁻¹ᵁ ((toLB D).U (J PUnit.unit) ⊓ (toLB D).U (J' PUnit.unit)) :=
    ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  exact (fnOf_app φ h₀ _).trans (congrArg _ (fnOf_toLB_g _ _ _))

theorem presents_pullback (D : CartierDiv X) :
    Presents (pullback φ D) ((toLB D).pull φ) (pullEqns φ D) := by
  refine ⟨LB.isLB_pull (isLB_toLB D) φ, fun J J' hg => ?_, fun J x hx => ?_⟩
  · rw [fnOf_pull_g φ D J J' hg]
    show GlobalTheory.functionFieldMap φ _ = GlobalTheory.functionFieldMap φ _ * GlobalTheory.functionFieldMap φ _
    rw [← map_mul, div_mul_cancel₀ _ (Units.ne_zero _)]
  · exact isEqn_pullback φ D ((J PUnit.unit).2.2 _ (mem_pull.1 hx))

end GlobalTheory.Cartier.DomPull

namespace GlobalTheory.Cartier


open DomPull in
theorem exists_pullback_cartierDiv : ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]
    (D : CartierDiv X), ∃ D' : CartierDiv X', cls (toLB D') (isLB_toLB D') =
      cls ((toLB D).pull φ) (LB.isLB_pull (isLB_toLB D) φ) ∧
      ∀ (x : X') (g : X.functionFieldˣ), D.IsEqn (φ x) g →
        D'.IsEqn x (Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom g) := by
  intro X X' _ _ φ _ D
  refine ⟨pullback φ D, ?_, fun x g h => isEqn_pullback φ D h⟩
  rw [← toPic_apply]
  exact (presents_pullback φ D).toPic_eq

end GlobalTheory.Cartier
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullDominant

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]

theorem unitAt_map {x : M} {u : W.functionField} (h : UnitAt (f x) u) :
    UnitAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨f.stalkMap x a, ha.map _, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

theorem regAt_map {x : M} {u : W.functionField} (h : RegAt (f x) u) :
    RegAt x (GlobalTheory.functionFieldMap f u) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f.stalkMap x a, (GlobalTheory.functionFieldMap_algebraMap f x a).symm⟩

abbrev unitsMap : W.functionFieldˣ →* M.functionFieldˣ := Units.map (GlobalTheory.functionFieldMap f).toMonoidHom

theorem germOf_map_eq {D₀ : CartierDiv W} {x : M} {g g' : W.functionFieldˣ}
    (h : D₀.IsEqn (f x) g) (h' : D₀.IsEqn (f x) g') :
    germOf x (unitsMap f g) = germOf x (unitsMap f g') := by
  rw [germOf_eq_iff]
  have := unitAt_map f (h.iff_unitAt.1 h')
  simpa [map_div₀] using this

def pullGerm (D₀ : CartierDiv W) (x : M) : Germ x :=
  germOf x (unitsMap f (D₀.exists_isEqn (f x)).choose)

theorem pullGerm_eq {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    pullGerm f D₀ x = germOf x (unitsMap f g) :=
  germOf_map_eq f (D₀.exists_isEqn (f x)).choose_spec h

def pull (D₀ : CartierDiv W) : CartierDiv M :=
  show cartierGroup M from ⟨pullGerm f D₀, fun x => by
    obtain ⟨U, hU, g, hg⟩ := D₀.exists_isEqn_nhds (f x)
    exact ⟨f ⁻¹ᵁ U, hU, unitsMap f g, fun y hy => pullGerm_eq f (hg (f y) hy)⟩⟩

theorem isEqn_pull {D₀ : CartierDiv W} {x : M} {g : W.functionFieldˣ} (h : D₀.IsEqn (f x) g) :
    (pull f D₀).IsEqn x (unitsMap f g) :=
  pullGerm_eq f h

theorem eff_pull {D₀ : CartierDiv W} (hD : D₀.Eff) : (pull f D₀).Eff := by
  intro x
  obtain ⟨g, hg⟩ := D₀.exists_isEqn (f x)
  refine ⟨unitsMap f g, isEqn_pull f hg, ?_⟩
  rw [one_mul]
  exact regAt_map f (CartierDiv.eff_iff.1 hD _ _ hg)

end GlobalTheory.Cartier.PullDominant


open GlobalTheory.Cartier.PullDominant in
theorem GlobalTheory.Cartier.exists_pull_dominant :
    ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f] (D₀ : CartierDiv W), D₀.Eff → ∃ D₁ : CartierDiv M, D₁.Eff ∧ ∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g) := by
  intro M W _ _ f _ D₀ hD
  exact ⟨pull f D₀, eff_pull f hD, fun x g h => isEqn_pull f h⟩
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullPres

theorem fnOf_app {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} (h : genericPoint X ∈ q ⁻¹ᵁ U) (a : Γ(W, U)) :
    fnOf (q ⁻¹ᵁ U) h ((q.app U).hom a) =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) h) a) := by
  rw [← algebraMap_germ h, ← algebraMap_germ (show q (genericPoint X) ∈ U from h),
    functionFieldMap_algebraMap, Scheme.Hom.germ_stalkMap_apply]

theorem fnOf_res_pullU {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    {U : W.Opens} {V : X.Opens} (le : V ≤ q ⁻¹ᵁ U) (hV : genericPoint X ∈ V) (u : Γ(W, U)ˣ) :
    fnOf V hV (res le (pullU q U u)).val =
      functionFieldMap q (fnOf U (gen_mem (x := q (genericPoint X)) (le hV)) u.val) :=
  (fnOf_resG le hV _).trans (fnOf_app q (le hV) _)

theorem presents_pull {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W)
    (hDE : ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) :
    Presents D ((toLB E).pull q) fun J => Units.map (functionFieldMap q).toMonoidHom (J PUnit.unit).1.2 := by
  refine ⟨pull_isLB (isLB_toLB E) q, fun J K h => ?_, fun J x hx => hDE _ _ ((J PUnit.unit).2.2 _ (mem_pull.1 hx)) x rfl⟩
  have le : ((toLB E).pull q).U J ⊓ ((toLB E).pull q).U K ≤
      q ⁻¹ᵁ ((toLB E).U (J PUnit.unit) ⊓ (toLB E).U (K PUnit.unit)) :=
    fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  have hg : ((toLB E).pull q).g J K = res le (pullU q _ ((toLB E).g (J PUnit.unit) (K PUnit.unit))) := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
    rfl
  rw [hg, fnOf_res_pullU, fnOf_toLB_g]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_div₀]
  exact (div_mul_cancel₀ _ ((map_ne_zero _).2 (Units.ne_zero _))).symm

theorem pull_cls_toLB : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q]
    (D : CartierDiv X) (E : CartierDiv W),
    (∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    CechPic.pull q (cls (toLB E) (isLB_toLB E)) = cls (toLB D) (isLB_toLB D) := by
  intro X W _ _ q _ D E hDE
  rw [← cls_pull (isLB_toLB E) q (pull_isLB (isLB_toLB E) q), ← (presents_pull q D E hDE).toPic_eq,
    toPic_apply]

end GlobalTheory.Cartier.PullPres
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CompHS.WeightGapAntitone

theorem antitone_of_gap_nonneg {N : ℕ} (v : Fin N → ℤ) (h : ∀ k, k + 1 < N → 0 ≤ gap v k) : Antitone v := by
  cases N with
  | zero => exact fun a => a.elim0
  | succ n =>
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have := h i (by omega)
    rw [gap, dite_eq_left (by omega)] at this
    have e1 : (⟨(i : ℕ), by omega⟩ : Fin (n + 1)) = Fin.castSucc i := rfl
    have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 1)) = i.succ := rfl
    rw [e1, e2] at this
    omega

end GlobalTheory.CompHS.WeightGapAntitone

theorem GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (P : WtPar Dw) (j : ℕ), (∀ τ, StrictAnti (P.u₁ τ)) →
    2 ≤ GlobalTheory.FlagTan.dimFlag Dw + j → 1 ≤ Dw.p → 1 ≤ Dw.q →
    ∀ τ, Antitone (P.wt j τ) ∧ 1 ≤ GlobalTheory.CompHS.gap (P.wt j τ) (Dw.p - 1) := by
  intro E _ _ _ H Dw P j hu hD hp hq τ
  have key : ∀ k (h : k + 1 < Dw.p + Dw.q), 1 ≤ gap (P.wt j τ) k := by
    intro k h
    have hr := (P.gap_rem τ k).1
    have hu1 : P.u₁ τ ⟨k + 1, h⟩ < P.u₁ τ ⟨k, by omega⟩ := hu τ (Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
    have hk : -2 ≤ FlagTan.kap Dw τ ⟨k, by omega⟩ - FlagTan.kap Dw τ ⟨k + 1, h⟩ := by
      simp only [FlagTan.kap, Fin.val_mk]
      split_ifs <;> push_cast <;> omega
    rw [gap, dite_eq_left h] at hr ⊢
    simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply] at hr ⊢
    simp only [nsmul_eq_mul] at hr ⊢
    have hD' : (2 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + (j : ℤ) := by exact_mod_cast hD
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + j - 2 by linarith)
      (show (0 : ℤ) ≤ P.u₁ τ ⟨k, by omega⟩ - P.u₁ τ ⟨k + 1, h⟩ - 1 by linarith)]
  exact ⟨WeightGapAntitone.antitone_of_gap_nonneg _ fun k h => by have := key k h; omega, key _ (by omega)⟩
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistKernel

theorem twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧ ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  intro R _ _ A _ hA L hL ha T _ hT N hN
  have := hA.proper
  have : LocallyOfFiniteType (A ⊗ T).hom := by
    have := hT
    first
    | infer_instance
    | (show LocallyOfFiniteType (pullback.fst A.hom T.hom ≫ A.hom); infer_instance)
    | (show LocallyOfFiniteType (pullback.snd A.hom T.hom ≫ T.hom); infer_instance)
  have : IsLocallyNoetherian (A ⊗ T).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ T).hom
  have hΛ : Fam A (abelian₂ A L) := ⟨LB.isLB_linComb hL _ _,
    (GlobalTheory.CubeDual.isAdditive_lam GlobalTheory.CubeTop.cubeTheorem hA hL (LB.isLB_linComb hL _ _)).1⟩
  obtain ⟨H, h, hh, hH⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp R) A (A ⊗ T) hA
    (ev (abelian₂ A L) (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T)) (ev N (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
    (hΛ.ev (fst A T)) (hN.ev (snd A T))
  have rep : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T),
      Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
    intro Y a t
    rw [← hH Y (lift a t), same_iff hΛ.isLB hN.isLB, same_iff (hΛ.ev (fst A T)).isLB (hN.ev (snd A T)).isLB,
      evc_ev hΛ.isLB, evc_ev hN.isLB]
    simp
  exact ⟨H, h, hh, GlobalTheory.T.isFinite_twisted_kernel_cubeLambda R A hA L hL ha T hT N hN H h hh rep,
    GlobalTheory.T.flat_finiteTwistedKernel_over_affineParameter R A hA L hL ha T hT N hN H h hh rep (GlobalTheory.T.isFinite_twisted_kernel_cubeLambda R A hA L hL ha T hT N hN H h hh rep),
    GlobalTheory.T.surjective_twistedKernel_additiveLineBundleFamily R A hA L hL ha T hT N hN H h hh rep, rep⟩

end GlobalTheory.TwistKernel
end
end
