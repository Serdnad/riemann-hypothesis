module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle053
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle005
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle149
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraitSectionBasisDescendsFiniteDvrExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_basicOpen_genSec_fibres : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (g : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), PolFib G L g x →
    ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
      ∃ θ : SecAt G L (spMap (algebraMap R (Localization.Away r)) ≫ x),
        ∀ (K : Type) [Field K] (i : Localization.Away r →+* K), IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g R _ _ x hx p
  obtain ⟨P, α, -, hp, w, hw⟩ := hx
  have hS : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  obtain ⟨V, hpV, hV⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near hS P p
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((V : Set (Sp R)) : Set (PrimeSpectrum R))) hpV V.isOpen
  let j := algebraMap R (Localization.Away r)
  have hrange : Set.range (spMap j) ⊆ (V : Set (Sp R)) := by
    intro y hy
    apply hrV
    obtain ⟨z, rfl⟩ := hy
    have hz : PrimeSpectrum.comap j z ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨z, rfl⟩
    exact hz
  obtain ⟨th, hth⟩ := hV (Localization.Away r) (spMap j) hrange
  have hτ : (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) ≫
      (Over.mk (spMap j ≫ x)).hom = (Over.mk (spMap j)).hom ≫ x := Category.id_comp _
  obtain ⟨θ, hθ⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp (T := Over.mk (spMap j)) (T₀ := Over.mk (spMap j ≫ x))
    (𝟙 _) hτ hw hL P.isLB (a := ((1 : ℕ) : ℤ)) th
  refine ⟨r, hpr, θ, fun K _ i => ?_⟩
  have hτ' : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫
      (Over.mk (spMap i ≫ spMap j ≫ x)).hom = (Over.mk (spMap i ≫ spMap j)).hom ≫ x := by
    simp [Category.assoc]
  let ξ : Over.mk (spMap i ≫ spMap j) ⟶ Over.mk (spMap j) := Over.homMk (spMap i) rfl
  let ξ₀ : Over.mk (spMap i ≫ spMap j ≫ x) ⟶ Over.mk (spMap j ≫ x) := Over.homMk (spMap i) rfl
  have hξ : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫ ξ₀.left =
      ξ.left ≫ (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hrel : GlobalTheory.ThetaPtMove.SecRel hp _ hτ' w (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th)
      (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.Ex.OneGen.SecRel.pullS hp _ hτ hθ (T' := Over.mk (spMap i ≫ spMap j))
      (T₀' := Over.mk (spMap i ≫ spMap j ≫ x)) _ hτ' ξ ξ₀ hξ
  have : IsAffine (Over.mk (spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap i ≫ spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have hg : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 ξ th) :=
    GlobalTheory.EmbPull.isGenSec_pullS P hS ξ hth
  have hg' : IsGenSec P.A P.L ((1 : ℕ) : ℤ) (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th) := hg
  have : IsIso (C := Scheme.{0}) (X := (Over.mk (spMap i ≫ spMap j)).left)
      (Y := (Over.mk (spMap i ≫ spMap j ≫ x)).left) (𝟙 (Sp K)) := IsIso.id _
  have h2 : IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.ThetaPtUp.isGenSec_up hp _ hτ' hw hL P.isLB hrel hg'
  exact h2

end GlobalTheory.UMin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem isGenSec_of_univBasis {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {K K' : Type} [CommRing K]
    [CommRing K'] {x : Sp K ⟶ S} {e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))} (he : UnivBasis G L x e)
    (i : K →+* K') {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x') :
    IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e) :=
  (isGenSec_iff _).2 fun s => by
    obtain ⟨c, hc, -⟩ := he K' i x' h s
    exact ⟨c, hc⟩

theorem spMap_id (K : Type) [CommRing K] : spMap (RingHom.id K) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem gen_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (K : Type)
    [Field K] (x : Sp K ⟶ S), PolFib G L g x → (∃ θ : SecAt G L x, IsGenSec G L _ θ) ∧
    ∀ θ : SecAt G L x, IsGenSec G L _ θ → ∀ (K' : Type) [Field K'] (i : K →+* K'),
      IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g K _ x hP
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id, Category.id_comp]
  refine ⟨⟨_, isGenSec_of_univBasis he (RingHom.id K) h0⟩, fun θ hθ K' _ i => ?_⟩
  set e₀ := VVRank.pullS G _ (Over.homMk (spMap (RingHom.id K)) h0 : Over.mk x ⟶ Over.mk x) e with he₀
  obtain ⟨c, hc, -⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G θ)
  obtain ⟨r, hr⟩ := (isGenSec_iff θ).1 hθ (SecM.ofSec G e₀)
  obtain ⟨c₀, -, hu⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G e₀)
  have hrc : r * c = 1 := by
    have e1 : SecM.ofSec G e₀ = (r * c) • SecM.ofSec G e₀ := by
      conv_lhs => rw [hr, hc]
      rw [smul_smul]
    exact (hu _ e1).trans (hu 1 (one_smul _ _).symm).symm
  have hcu : IsUnit c := ⟨⟨c, r, by rw [mul_comm]; exact hrc, hrc⟩, rfl⟩
  have ha : IsUnit ((fnR x).symm c) := hcu.map (fnR x).symm
  have hb := he.smul_pull hL (RingHom.id K) h0 ha
  have eq : SecM.toSec G (fnR x ((fnR x).symm c) • pl (RingHom.id K) h0 (SecM.ofSec G e)) = θ := by
    rw [RingEquiv.apply_symm_apply, pl_ofSec, ← hc]
    rfl
  rw [eq] at hb
  exact isGenSec_of_univBasis hb i rfl

end GlobalTheory.UMin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem polFib_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] (x : Sp R ⟶ Xo.X), PolFib Xo.univ.t.G Xo.univ.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) x := by
  intro E _ _ _ H Dw l Xo c R _ x
  obtain ⟨P', φ, hg, hc, hL⟩ :=
    GlobalTheory.PureType.exists_baseChange GlobalTheory.abelianSchemeLaws_all.1.polBaseChange x (GlobalTheory.objPolAV Xo.univ)
  exact ⟨P', φ, hg, hc, hL⟩

end GlobalTheory.UMin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem hasDiv_of_pCrd_pt : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω)
    (n : ℕ) (g : M.Z ⟶ PSpace o n) (e : Fin (n + 1) → Ω), PCrd (M.pt ≫ g) e → M.HasDiv e := by
  intro k Ω o _ _ _ _ M n g e hP z
  obtain ⟨τ, -, H⟩ := hP
  obtain ⟨c, hc⟩ := GlobalTheory.ProjSpace.exists_mem_chart o n (g z)
  let W : M.Z.Opens := g ⁻¹ᵁ GlobalTheory.ProjSpace.chart o n c
  have hzW : z ∈ W := hc
  have hW : ⊤ ≤ M.pt ⁻¹ᵁ W := M.top_le_preimage_pt ⟨z, hzW⟩
  let j : PUnit → (GlobalTheory.ProjSpace.O1 o n).ι := fun _ => c
  let V := ((GlobalTheory.ProjSpace.O1 o n).pull (M.pt ≫ g)).U j
  have hV : V ≤ (M.pt ≫ g) ⁻¹ᵁ (GlobalTheory.ProjSpace.O1 o n).U (j PUnit.unit) :=
    LB.wchart_le (GlobalTheory.ProjSpace.O1 o n) (fun _ => M.pt ≫ g) j PUnit.unit
  have hV' : ⊤ ≤ V := fun y _ => Set.mem_iInter.2 fun _ => hW (Set.mem_univ y)
  let ev : Γ(Sp Ω, V) →+* Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp ((Sp Ω).presheaf.map (homOfLE hV').op).hom
  have hconst : ∀ a : Ω, ev (resG (Sp Ω) le_top ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a := by
    intro a
    change (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (((Sp Ω).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      (Sp Ω).presheaf.map (homOfLE hV').op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a)) = a
    rw [← Functor.map_comp]
    have : ((homOfLE (le_top : V ≤ ⊤)).op ≫ (homOfLE hV').op : Opposite.op (⊤ : (Sp Ω).Opens) ⟶ _) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    exact (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv_hom_id_apply a
  have hval : ∀ i, ev (((M.pt ≫ g).appLE _ _ hV).hom ((GlobalTheory.ProjSpace.coord o n i).f (j PUnit.unit))) =
      valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) := by
    intro i
    rw [valF, dite_eq_left hW]
    change (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (resG (Sp Ω) hV' _) = _
    rw [GlobalTheory.ProjSpace.resG_appLE, GlobalTheory.ProjSpace.pullRatio, GlobalTheory.ProjSpace.appLE_appLE]
    rfl
  have key : ∀ i, valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) = e i * ev (τ.s j).val := by
    intro i
    rw [← hval, H i j hV, map_mul, hconst]
  have h1 : e c * ev (τ.s j).val = 1 := by
    rw [← key c, GlobalTheory.ProjSpace.pullRatio_self, ← M.res_apply W ⟨z, hzW⟩, map_one]
  have hc0 : e c ≠ 0 := left_ne_zero_of_mul_eq_one h1
  refine ⟨c, hc0, fun i => ?_⟩
  have e1 : e i / e c = valF M.pt W (GlobalTheory.ProjSpace.pullRatio g W c le_rfl i) := by
    rw [key i, eq_inv_of_mul_eq_one_right h1, div_eq_mul_inv]
  rw [e1]
  exact RatModel.valF_mem_O hzW _

end GlobalTheory.UMin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdMap

open GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.QCoh.Qcqs

theorem pCrd_pt {o A : Type} [CommRing o] [CommRing A] {n : ℕ} (c : o →+* A) (v : Fin (n + 1) → A)
    (hv : Ideal.span (Set.range v) = ⊤) : PCrd (pt c v hv) v := by
  have hφ := toProj_coord o n
  have hstr : pt c v hv ≫ PSpace.str o n = spMap c := by
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  have h1 := (ProjCoord.secCoord_iff (Equiv.refl _) (toProj (PSpace.str o n) (coord o n) (iSup_nonzeroLocus_coord o n))
    c (pt c v hv) (by rw [hφ, Category.comp_id]; exact hstr) v).2 ⟨by simpa using hv, by rw [hφ, Category.comp_id]; rfl⟩
  exact (FibreEmbed.secCoord_iff_of_secMaps (LB.isLB_pull (O1_isLB o n) _) (O1_isLB o n)
    (fun j => secMaps_toProjIso _ _ _ j) (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord o n) _)
    (iSup_nonzeroLocus_coord o n)).1 h1

section Map

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {n : ℕ} (c : Fin (n + 1) → Ω)

def dOpen (i : Fin (n + 1)) : M.Z.Opens := ⟨{z | M.Div c i z}, M.isOpen_setOf_div c i⟩

theorem subsingleton_of_not_nonempty {X : Scheme.{0}} {V : X.Opens} (hV : ¬ (V : Set X).Nonempty) :
    Subsingleton Γ(X, V) := by
  have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
  subst this
  infer_instance


variable {M} in
theorem eq_of_valF {V : M.Z.Opens} {f g : Γ(M.Z, V)}
    (h : ∀ hV : (V : Set M.Z).Nonempty, valF M.pt V f = valF M.pt V g) : f = g := by
  by_cases hV : (V : Set M.Z).Nonempty
  · exact M.valF_injective hV (h hV)
  · have := subsingleton_of_not_nonempty hV
    exact Subsingleton.elim _ _


open Classical in
def fnOf (V : M.Z.Opens) (x : Ω) : Γ(M.Z, V) :=
  if h : ∃ f : Γ(M.Z, V), valF M.pt V f = x then h.choose else 0


variable {M} in
theorem valF_fnOf {V : M.Z.Opens} {x : Ω} (h : ∃ f : Γ(M.Z, V), valF M.pt V f = x) :
    valF M.pt V (fnOf M V x) = x := by
  rw [fnOf, dite_eq_left h]
  exact h.choose_spec

def ratioFn (i j : Fin (n + 1)) : Γ(M.Z, dOpen M c i) := fnOf M (dOpen M c i) (c j / c i)

variable {M c}

theorem valF_ratioFn {i j : Fin (n + 1)} {V : M.Z.Opens} (hV : V ≤ dOpen M c i) (hne : (V : Set M.Z).Nonempty) :
    valF M.pt V (resG M.Z hV (ratioFn M c i j)) = c j / c i := by
  have hne' : ((dOpen M c i : M.Z.Opens) : Set M.Z).Nonempty := hne.mono hV
  rw [M.valF_resG hV hne, ratioFn, valF_fnOf]
  exact (RatModel.mem_ringOn_iff_exists hne').1 (RatModel.mem_ringOn.2 fun z hz => hz.2 j)

theorem valF_one' {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) : valF M.pt V 1 = 1 := by
  rw [← M.res_apply V hne, map_one]

theorem valF_mul' {V : M.Z.Opens} (hne : (V : Set M.Z).Nonempty) (f g : Γ(M.Z, V)) :
    valF M.pt V (f * g) = valF M.pt V f * valF M.pt V g := by
  rw [← M.res_apply V hne, map_mul, M.res_apply, M.res_apply]

theorem isCoordFamily_ratioFn (hd : M.HasDiv c) : IsCoordFamily (dOpen M c) (ratioFn M c) := by
  refine { cover := top_le_iff.1 fun z _ => TopologicalSpace.Opens.mem_iSup.2 (hd z)
           self := ?_, mul := ?_, basicOpen_le := ?_ }
  · intro i
    refine eq_of_valF fun hne => ?_
    obtain ⟨z, hz⟩ := hne
    have := valF_ratioFn (j := i) (le_refl (dOpen M c i)) ⟨z, hz⟩
    rw [resG_self] at this
    rw [this, valF_one' ⟨z, hz⟩, div_self hz.1]
  · intro i j k
    refine eq_of_valF fun hne => ?_
    obtain ⟨z, hz⟩ := hne
    rw [valF_mul' ⟨z, hz⟩, valF_ratioFn _ ⟨z, hz⟩, valF_ratioFn _ ⟨z, hz⟩, valF_ratioFn _ ⟨z, hz⟩]
    have h1 := hz.1.1
    have h2 := hz.2.1
    field_simp
  · intro i j z hz
    have hzi : z ∈ dOpen M c i := M.Z.basicOpen_le _ hz
    have hu := (RatModel.isUnit_valF_iff hzi (ratioFn M c i j)).2 hz
    have e : valF M.pt (dOpen M c i) (ratioFn M c i j) = c j / c i := by
      have := valF_ratioFn (j := j) (le_refl (dOpen M c i)) ⟨z, hzi⟩
      rwa [resG_self] at this
    have e' : (⟨valF M.pt (dOpen M c i) (ratioFn M c i j), RatModel.valF_mem_O hzi _⟩ : M.O z) =
        ⟨c j / c i, (show M.Div c i z from hzi).2 j⟩ := Subtype.ext e
    rw [e'] at hu
    exact ((show M.Div c i z from hzi).div_iff_isUnit j).2 hu

end Map

section Main

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {n : ℕ} {c : Fin (n + 1) → Ω}

theorem appLE_eq_fnOn {X : Scheme.{0}} (x : Sp Ω ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    (x.appLE U ⊤ h).hom f = fnOn ⊤ (valF x U f) := by
  rw [valF, dite_eq_left h, fnOn, RingHom.comp_apply, resG_self]
  simp

theorem pt_comp_toHom (hd : M.HasDiv c) (hc : Ideal.span (Set.range c) = ⊤) :
    M.pt ≫ (isCoordFamily_ratioFn hd).toHom M.s = pt (algebraMap o Ω) c hc := by
  let _ := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := o)
  set H := isCoordFamily_ratioFn hd
  obtain ⟨i, hi⟩ := hd (genericPoint M.Z)
  have hpt : ⊤ ≤ M.pt ⁻¹ᵁ dOpen M c i := M.top_le_preimage_pt ⟨_, RatModel.div_genericPoint hi.1⟩
  have h₁ : ⊤ ≤ (M.pt ≫ H.toHom M.s) ⁻¹ᵁ chart o n i :=
    GlobalTheory.Points.le_preimage_comp M.pt _ (H.le_toHom_preimage M.s i) hpt
  have hchart : pt (algebraMap o Ω) c hc ⁻¹ᵁ chart o n i = spOpen (c i) := by
    rw [pt, chart, ProjPoint.ofHom_preimage_basicOpen _ _ _ one_pos (X_mem o n i),
      MvPolynomial.eval₂Hom_X']
    rfl
  have h₂ : ⊤ ≤ pt (algebraMap o Ω) c hc ⁻¹ᵁ chart o n i := by
    rw [hchart]
    exact fun y _ => mem_spOpen.2 fun hm => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (Ne.isUnit hi.1))
  have hstr : pt (algebraMap o Ω) c hc ≫ PSpace.str o n = spMap (algebraMap o Ω) := by
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C (algebraMap o Ω) c r
  refine hom_ext (by rw [Category.assoc, H.toHom_str, M.pt_s, hstr]) fun _ => ⟨⊤, trivial, i, h₁, h₂, fun j => ?_⟩
  have hratio : pullRatio (pt (algebraMap o Ω) c hc) ⊤ i h₂ j * fnOn ⊤ (c i) = fnOn ⊤ (c j) := by
    let β := algebraMap o Ω
    have hunit : IsUnit (MvPolynomial.eval₂Hom β c (MvPolynomial.X i)) := by
      rw [MvPolynomial.eval₂Hom_X']
      exact Ne.isUnit hi.1
    have haway : pt β c hc =
        spMap (ProjPoint.awayLift (grading o n) (MvPolynomial.eval₂Hom β c) (MvPolynomial.X i) hunit) ≫ _ :=
      ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem o n i) hunit
    have heval := ProjPoint.awayLift_mk_mul (grading o n) (MvPolynomial.eval₂Hom β c) hunit
      (X_mem o n i) 1 (MvPolynomial.X j) (X_mem o n j)
    rw [pullRatio_of_eq haway h₂ (haway ▸ h₂), pullRatio_spMap_awayι, ← map_mul]
    exact congrArg _ (by simpa only [ratioAway, MvPolynomial.eval₂Hom_X', pow_one] using heval)
  have hu : IsUnit (fnOn (⊤ : (Sp Ω).Opens) (c i)) := (Ne.isUnit hi.1).map _
  refine hu.mul_right_cancel ?_
  rw [hratio, ← appLE_pullRatio (φ := H.toHom M.s) (hi := H.le_toHom_preimage M.s i) M.pt hpt, H.pullRatio_toHom,
    appLE_eq_fnOn, ← map_mul]
  congr 1
  have := valF_ratioFn (M := M) (c := c) (j := j) (le_refl (dOpen M c i)) ⟨_, RatModel.div_genericPoint hi.1⟩
  rw [resG_self] at this
  rw [this, div_mul_cancel₀ _ hi.1]

theorem exists_map_of_hasDiv : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ)
    (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace k n, h ≫ PSpace.str k n = M.s ∧ PCrd (M.pt ≫ h) c := by
  intro k Ω _ _ _ M n c hd
  obtain ⟨i, hi⟩ := hd (genericPoint M.Z)
  have hc : Ideal.span (Set.range c) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (Ne.isUnit hi.1)
  refine ⟨(isCoordFamily_ratioFn hd).toHom M.s, (isCoordFamily_ratioFn hd).toHom_str M.s, ?_⟩
  rw [pt_comp_toHom hd hc]
  exact pCrd_pt _ c hc

end Main

end GlobalTheory.UMin.CrdMap
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem nz_everywhere {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] (L : LB G.left) {R : Type} [CommRing R]
    [IsLocalRing R] (χ : Sp R ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) (h : NZ G L χ σ) :
    ∀ y : (Over.mk χ).left, ∃ g, (fst (Over.mk χ) G).left g = y ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨x, hc, hx⟩ := h
  haveI : Smooth (fst (Over.mk χ) G).left := by
    change Smooth (pullback.fst χ G.hom)
    infer_instance
  have ho : IsOpen ((fst (Over.mk χ) G).left '' (nonzeroLocus σ : Set _)) :=
    (fst (Over.mk χ) G).left.isOpenMap _ (nonzeroLocus σ).isOpen
  intro y
  obtain ⟨g, hg, e⟩ := (IsLocalRing.specializes_closedPoint (R := R) y).mem_open ho ⟨x, hx, hc⟩
  exact ⟨g, e, hg⟩

theorem nz_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G →
    ∀ (R V : Type) [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (χ : Sp R ⟶ S) (σ : SecAt G L χ)
      (φ : R →+* V), NZ G L χ σ → NZ G L (spMap φ ≫ χ) (SecAt.pull G L σ φ) := by
  intro S G _ L hL hG R V _ _ _ _ χ σ φ h
  haveI : Smooth G.hom := hG.smooth
  exact nz_pullS G hL σ (nz_everywhere G L χ σ h) (spMap φ ≫ χ) _

end GlobalTheory.UMin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.CrdBasic

theorem pCrd_basic : (∀ (o R R' : Type) [CommRing o] [CommRing R] [CommRing R'] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (i : R →+* R'), PCrd x v → PCrd (spMap i ≫ x) (fun j => i (v j))) ∧ (∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (a : R), IsUnit a → PCrd x v → PCrd x (fun j => a * v j)) ∧ ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n), (∃ v, PCrd x v) ∧ ∀ v, PCrd x v → ∃ j, v j ≠ 0 := by
  refine ⟨fun o R R' _ _ _ n x v i h => ?_, fun o R _ _ n x v a ha h => ?_, fun o K _ _ n x => ⟨?_, fun v h => ?_⟩⟩
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).1 R' i
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).2.1 ha.unit
  · exact GlobalTheory.ZM.FieldPoint.exists_secCoord o n K x
  · obtain ⟨c, hc⟩ := RepUniq.exists_spMap (x ≫ PSpace.str o n)
    obtain ⟨hv, -⟩ := GlobalTheory.ZM.ProjExt.eq_pt_of_secCoord c x hc v h
    by_contra h0
    push_neg at h0
    have : Ideal.span (Set.range v) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨j, rfl⟩
      exact h0 j
    rw [this] at hv
    exact bot_ne_top hv

end GlobalTheory.UMin.CrdBasic
end
