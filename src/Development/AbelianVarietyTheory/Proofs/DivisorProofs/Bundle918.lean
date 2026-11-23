module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle889
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer.MaxCharts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

def Alg (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  ∃ x : Sp (Hol W) ⟶ X, (∀ h : ∀ p ∈ W, p.1 ∈ F.V,
      x ≫ s = spMap ((Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) h).toRingHom.comp σ)) ∧
    ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p

theorem alg_of_ev (u : Unif F s σ) (W : Opens (Tot I g)) (x : Sp (Hol W) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p) : Alg u W := by
  refine ⟨x, fun h ↦ ?_, hx⟩
  refine point_hol_ext _ W (Sp B) (⊤_ Scheme.{0}) (terminal.from _) _ _ (terminal.hom_ext _ _) fun p hp ↦ ?_
  have e := hx p hp
  change spMap (Hol.ev p hp).toRingHom ≫ _ = spMap (Hol.ev p hp).toRingHom ≫ _
  rw [← Category.assoc, e, u.w p (h p hp), ← Cris.spMap_comp]
  rfl

theorem alg_mono (u : Unif F s σ) {W W' : Opens (Tot I g)} (h : W' ≤ W) (a : Alg u W) : Alg u W' := by
  obtain ⟨x, -, hx⟩ := a
  refine alg_of_ev u W' (spMap (Hol.comap id analyticOnNhd_id (fun p hp ↦ h hp)).toRingHom ≫ x) fun p hp ↦ ?_
  rw [← Category.assoc, ← Cris.spMap_comp, ← hx p (h hp)]
  rfl

@[reducible] def charts (u : Unif F s σ) : Charts F := Charts.std F (Alg u)

def real [IsSeparated s] (u : Unif F s σ) : Real (charts u) s σ where
  x k := k.2.2.choose
  w k := k.2.2.choose_spec.1 k.2.1
  compat {l k k'} h := by
    refine point_hol_ext _ k'.1 X _ s _ _ ?_ fun p hp ↦ ?_
    · rw [Category.assoc, k.2.2.choose_spec.1 k.2.1, k'.2.2.choose_spec.1 k'.2.1, ← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext fun b ↦ Charts.sh_cst (K := charts u) h (σ b))
    · change spMap (Hol.ev p hp).toRingHom ≫ _ = spMap (Hol.ev p hp).toRingHom ≫ _
      rw [k'.2.2.choose_spec.2 p hp, ← Category.assoc, ← Cris.spMap_comp, ← u.per l p (k'.2.1 p hp),
        ← k.2.2.choose_spec.2 _ (h p hp)]
      rfl

theorem isFor [IsSeparated s] (u : Unif F s σ) : (real u).IsFor u := fun k ↦ k.2.2.choose_spec.2

theorem rich (u : Unif F s σ) : (charts u).Rich := by
  constructor
  · intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := u.E p (default : PrimeSpectrum ℂ))
      (U := ⊤) trivial
    let W : Opens (Tot I g) := ⟨{q | q.1 ∈ F.V ∧ ⊤ ≤ u.E q ⁻¹ᵁ U}, (u.hol U 0).1⟩
    have hol : IsHolTo (W : Set (Tot I g)) u.E := fun U' f ↦ ⟨by
      have e : {q | q ∈ (W : Set (Tot I g)) ∧ ⊤ ≤ u.E q ⁻¹ᵁ U'} =
          (W : Set (Tot I g)) ∩ {q | q.1 ∈ F.V ∧ ⊤ ≤ u.E q ⁻¹ᵁ U'} :=
        Set.ext fun q ↦ ⟨fun h ↦ ⟨h.1, h.1.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
      exact e ▸ W.isOpen.inter (u.hol U' f).1,
      (u.hol U' f).2.mono fun q h ↦ ⟨h.1.1, h.2⟩⟩
    obtain ⟨x, -, hx⟩ := exists_point_hol _ W X u.E U hU hol fun q hq ↦ hq.2
    refine ⟨⟨W, fun q hq ↦ hq.1, alg_of_ev u W x hx⟩, hp, fun y _ ↦ ?_⟩
    obtain rfl : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact hpU
  · intro l k₁ k₂ p h₁ h₂
    have ho : IsOpen ((k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' (k₂.1 : Set (Tot I g))) :=
      (F.shift_analytic l k₁.2.1).continuousOn.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen
    refine ⟨⟨⟨_, ho⟩, fun q hq ↦ k₁.2.1 q hq.1, alg_mono u (fun q hq ↦ hq.1) k₁.2.2⟩, ⟨h₁, h₂⟩,
      fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    rw [F.shift_zero]
    exact hq.1

end GlobalTheory.AnPer.MaxCharts

namespace GlobalTheory.AnPer

theorem period_unique : PUniq := by
  intro I _ g Λ _ F B _ X s _ σ u c per per' h h'
  exact GlobalTheory.T.periodClass_injective_of_rich_charts (MaxCharts.charts u) (MaxCharts.rich u) per per'
    ((h _ _ (MaxCharts.isFor u)).symm.trans (h' _ _ (MaxCharts.isFor u)))

end GlobalTheory.AnPer
end
end

section

set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer.PerExist

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

theorem ev_cst (K : Charts F) (k : K.K) (p : Tot I g) (hp : p ∈ K.W k) :
    (Hol.ev p hp).toRingHom.comp (K.cst k) = (Hol.ev p.1 (K.base k p hp)).toRingHom :=
  RingHom.ext fun f ↦ by
    change Hol.ev p hp (K.cst k f) = Hol.ev p.1 (K.base k p hp) f
    rw [Hol.ev_apply, Hol.ev_apply]
    exact K.fn_cst k f hp

theorem ev_sh {K : Charts F} {l : Λ} {k k' : K.K} (h : K.le l k' k) (p : Tot I g) (hp : p ∈ K.W k') :
    (Hol.ev p hp).toRingHom.comp (Charts.sh h) = (Hol.ev (F.shift l p) (K.maps h p hp)).toRingHom :=
  RingHom.ext fun f ↦ by
    change Hol.ev p hp (Charts.sh h f) = Hol.ev (F.shift l p) (K.maps h p hp) f
    rw [Hol.ev_apply, Hol.ev_apply]
    exact Charts.fn_sh h f hp

def Pt (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  ∃ x : Sp (Hol W) ⟶ X, ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p

theorem Pt.mono {u : Unif F s σ} {W W' : Opens (Tot I g)} (hW : W' ≤ W) (h : Pt u W) : Pt u W' := by
  obtain ⟨x, hx⟩ := h
  refine ⟨spMap (Hol.comap id analyticOnNhd_id (fun p hp ↦ hW hp)).toRingHom ≫ x, fun p hp ↦ ?_⟩
  rw [← Category.assoc, ← Cris.spMap_comp]
  have e : (Hol.ev p hp).toRingHom.comp (Hol.comap id analyticOnNhd_id (fun p hp ↦ hW hp) : Hol W →ₐ[ℂ] Hol W').toRingHom =
      (Hol.ev p (hW hp)).toRingHom :=
    RingHom.ext fun f ↦ by
      change Hol.ev p hp (Hol.comap id analyticOnNhd_id (fun p hp ↦ hW hp) f) = Hol.ev p (hW hp) f
      rw [Hol.ev_apply, Hol.ev_apply]
      exact Hol.fn_comap _ _ _ f hp
  rw [e]
  exact hx p (hW hp)

theorem isHolTo (u : Unif F s σ) (W : Opens (Tot I g)) (hW : ∀ p ∈ W, p.1 ∈ F.V) : IsHolTo (W : Set (Tot I g)) u.E := by
  intro U f
  obtain ⟨ho, hd⟩ := u.hol U f
  have e : {b ∈ (W : Set (Tot I g)) | ⊤ ≤ u.E b ⁻¹ᵁ U} =
      (W : Set (Tot I g)) ∩ {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U} :=
    Set.ext fun b ↦ ⟨fun h ↦ ⟨h.1, hW b h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
  rw [e]
  exact ⟨W.isOpen.inter ho, hd.mono Set.inter_subset_right⟩

theorem pt_of_affine (u : Unif F s σ) (U : X.Opens) (hU : IsAffineOpen U) (W : Opens (Tot I g))
    (hW : ∀ p ∈ W, p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U) : Pt u W := by
  obtain ⟨x, -, hx⟩ := exists_point_hol (Tot I g) W X u.E U hU (isHolTo u W fun p hp ↦ (hW p hp).1)
    fun p hp ↦ (hW p hp).2
  exact ⟨x, hx⟩

def inU (u : Unif F s σ) (U : X.Opens) : Opens (Tot I g) :=
  ⟨{p | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U}, (u.hol U 0).1⟩

variable (u : Unif F s σ)

abbrev Kmax : Charts F := Charts.std F (Pt u)

theorem rich : (Kmax u).Rich := by
  refine ⟨fun p hp ↦ ?_, fun l k₁ k₂ p h₁ h₂ ↦ ?_⟩
  · obtain ⟨_, ⟨U, hU, rfl⟩, hq, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (u.E p (default : PrimeSpectrum ℂ))) isOpen_univ
    have hpU : p ∈ inU u U := ⟨hp, fun y _ ↦ by
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) y default]
      exact hq⟩
    exact ⟨⟨inU u U, fun q hq ↦ hq.1, pt_of_affine u U hU _ fun q hq ↦ hq⟩, hpU⟩
  · let W : Opens (Tot I g) := ⟨(k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' (k₂.1 : Set (Tot I g)),
      (F.shift_analytic l k₁.2.1).continuousOn.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen⟩
    have hW : W ≤ k₁.1 := fun q hq ↦ hq.1
    refine ⟨⟨W, fun q hq ↦ k₁.2.1 q hq.1, k₁.2.2.mono hW⟩, ⟨h₁, h₂⟩, fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    change F.shift 0 q ∈ k₁.1
    rw [F.shift_zero]
    exact hq.1

theorem based (hu : u.Based) : (Kmax u).Based := by
  obtain ⟨U, hU, hz⟩ := hu
  exact ⟨⟨inU u U, fun q hq ↦ hq.1, pt_of_affine u U hU _ fun q hq ↦ hq⟩, fun z hz' ↦ ⟨hz', hz z hz'⟩⟩

theorem over_base (K : Charts F) (k : K.K) (x : Sp (Hol (K.W k)) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p) :
    x ≫ s = spMap ((K.cst k).comp σ) :=
  point_hol_ext (Tot I g) (K.W k) (Sp B) _ (Limits.terminal.from _) _ _ (Limits.terminal.hom_ext _ _) fun p hp ↦ by
    change spMap (Hol.ev p hp).toRingHom ≫ x ≫ s = spMap (Hol.ev p hp).toRingHom ≫ _
    rw [← Category.assoc, hx p hp, u.w p (K.base k p hp), ← Cris.spMap_comp, ← RingHom.comp_assoc, ev_cst]

variable [IsSeparated s]

theorem pt_unique (K : Charts F) (k : K.K) (x x' : Sp (Hol (K.W k)) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p)
    (hx' : ∀ (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ x' = u.E p) : x = x' :=
  point_hol_ext (Tot I g) (K.W k) X (Sp B) s _ _ ((over_base u K k x hx).trans (over_base u K k x' hx').symm)
    fun p hp ↦ (hx p hp).trans (hx' p hp).symm

def rmax : Real (Kmax u) s σ where
  x k := k.2.2.choose
  w k := over_base u (Kmax u) k _ k.2.2.choose_spec
  compat {l k k'} h := pt_unique u (Kmax u) k' _ _ (fun p hp ↦ by
    rw [← Category.assoc, ← Cris.spMap_comp, ev_sh h p hp]
    exact (k.2.2.choose_spec _ _).trans (u.per l p (k'.2.1 p hp))) k'.2.2.choose_spec

variable {u} {K : Charts F} {r : Real K s σ}


omit [IsSeparated s] in
def toMax (hr : r.IsFor u) : K.Obj ⥤ (Kmax u).Obj where
  obj T :=
    { k := ⟨K.W T.k, K.base T.k, r.x T.k, hr T.k⟩
      C := T.C
      J := T.J
      nil := T.nil
      ρ := T.ρ
      ρ_cst := T.ρ_cst }
  map {T T'} f :=
    { φ := (Charts.Hom.φ f : T.C →ₐ[Hol F.V] T'.C)
      deg := Charts.Hom.deg f
      le := K.maps (Charts.Hom.le f)
      mem := Charts.Hom.mem f
      close := Charts.Hom.close f }


omit [IsSeparated s] in
def toMaxCoef (hr : r.IsFor u) : CoefMap (RingHom.id (Hol F.V)) (Kmax u).Oc K.Oc where
  G := toMax hr
  α T := RingHom.id T.C
  naturality _ _ := rfl
  smul _ _ _ := rfl

def toMaxTrans (hr : r.IsFor u) : r.coef.G ⟶ ((rmax u).coef.comp (toMaxCoef hr)).G where
  app T :=
    { φ := { RingHom.id T.C with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id (T.C ⧸ T.J)
      comm := fun _ ↦ rfl
      dp := letI := T.ratAlg; isDPMorphism_of_rat T.δ T.δ (RingHom.id T.C) fun _ h ↦ h
      pt := ((congrArg (· ≫ _) (Cris.spMap_id (T.C ⧸ T.J))).trans (Category.id_comp _)).trans
        (congrArg (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ ·)
          (pt_unique u K T.k _ _ (hr T.k) ((toMax hr).obj T).k.2.2.choose_spec)) }
  naturality _ _ _ := Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)

end GlobalTheory.AnPer.PerExist

namespace GlobalTheory.AnPer


open PerExist in
theorem periods_exist : PExist := by
  intro I _ g Λ _ F B _ X s _ σ u hu c
  obtain ⟨per, hper⟩ := GlobalTheory.T.exists_period_cohomologyClass_of_rich_based (Kmax u) (rich u) (based u hu) ((rmax u).coef.pull1 c)
  refine ⟨per, fun K r hr ↦ ?_⟩
  refine (CoefMap.pullCohomologyOne_eq_of_natTrans r.coef _ (toMaxTrans hr) (fun _ _ ↦ rfl) c).trans ?_
  rw [CoefMap.pullCohomologyOne_comp, hper]
  rfl

end GlobalTheory.AnPer
end
end

section

set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CatCoh GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem taylor_congr {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    {f f' : (I → ℂ) → ℂ} (h : f =ᶠ[nhds 0] f') : GlobalTheory.PeriodFamily.taylor N t f = GlobalTheory.PeriodFamily.taylor N t f' := by
  delta GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(h.iteratedFDeriv ℂ k).eq_of_nhds]

theorem isAb_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A) : IsAbelianScheme A' :=
  GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h

theorem gaussManinPeriods_of_parts : ∀ ε : ℤˣ, GlobalTheory.PeriodFamily.FamUnif → PExist → PHom → PSpan → PLie → PEnd → PChern ε → PFix → PTaylor → GlobalTheory.Published.GaussManinPeriods := by
  intro ε HF HE HH HS HL HEn HC HX HT
  have pm : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      ∀ (L : LB A.left), L.IsLB → ∀ (u : HolUnif A L g) (P : u.Λ →+ HdR A), IsPeriodHom u P → IsPeriodMap ε u P :=
    fun A _ g hA hg L hL u P hP ↦ ⟨(HS A g hA hg L u P hP).1, (HS A g hA hg L u P hP).2, HL A g hA hg L u P hP,
      fun α _ M ↦ HEn A g hA L u P hP α M, fun H χ ψ ↦ HC A g hA L u P hP L u hL rfl H χ ψ⟩
  refine ⟨ε, fun B _ _ _ 𝒜 _ g h𝒜 hg I _ _ U y hU h0 hy A _ φ hφ m L hL A₀ _ φ₀ hφ₀ L₀ hL₀ u₀ ↦ ?_⟩
  obtain ⟨r, u, τ, hr, hrU, hhol, ⟨W, hW, hW0⟩, c1, c2, c3, c4⟩ :=
    HF B 𝒜 g h𝒜 hg I U y hU h0 hy A φ hφ L hL A₀ φ₀ hφ₀ L₀ u₀
  have hA : ∀ z, IsAbelianScheme (A z) := fun z ↦ isAb_pull (hφ z) h𝒜
  have hA₀ : IsAbelianScheme A₀ := isAb_pull hφ₀ h𝒜
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have gA : ∀ z, SmoothOfRelativeDimension g (A z).hom := fun z ↦
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) (hφ z).1 hg
  have gA₀ : SmoothOfRelativeDimension g A₀.hom :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hφ₀.1 hg
  choose P hP using fun z ↦ HH (A z) g (hA z) (L z) (u z)
  obtain ⟨P₀, hP₀⟩ := HH A₀ g hA₀ L₀ u₀
  let V : Opens (I → ℂ) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have V0 : (0 : I → ℂ) ∈ V := Metric.mem_ball_self hr
  let F : Fam I g u₀.Λ :=
    { V := V
      τ := { toFun x z := (τ z x : Fin g → ℂ)
             map_zero' := funext fun z ↦ congrArg Subtype.val ((τ z).map_zero)
             map_add' a b := funext fun z ↦ congrArg Subtype.val ((τ z).map_add a b) }
      hol x := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball (c3 x) }
  have ya : ∀ b, AnalyticOnNhd ℂ (fun z ↦ y z b) V := fun b ↦
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball ((hy b).mono hrU)
  let σ : B →ₐ[ℂ] Hol F.V :=
    { toFun b := Hol.mk _ (ya b)
      map_one' := Subtype.ext (funext fun z ↦ map_one (y z))
      map_mul' a b := Subtype.ext (funext fun z ↦ map_mul (y z) a b)
      map_zero' := Subtype.ext (funext fun z ↦ map_zero (y z))
      map_add' a b := Subtype.ext (funext fun z ↦ map_add (y z) a b)
      commutes' a := Subtype.ext (funext fun z ↦ (y z).commutes a) }
  have hσ : ∀ b, ∀ z ∈ V, (σ b).fn z = y z b := fun b z hz ↦ Hol.fn_mk _ (ya b) hz
  let e : Unif F (𝒜.hom ≫ 𝟙 _) (σ : B →+* Hol F.V) :=
    { E q := (show Sp ℂ ⟶ (A q.1).left from ((u q.1).ex q.2).left) ≫ φ q.1
      w p hp := by
        have e1 : (show Sp ℂ ⟶ (A p.1).left from ((u p.1).ex p.2).left) ≫ (A p.1).hom = 𝟙 _ := Over.w ((u p.1).ex p.2)
        rw [Category.comp_id, Category.assoc, (hφ p.1).1.w, ← Category.assoc, e1, Category.id_comp]
        rfl
      per l p _ := by
        have : (u p.1).ex (p.2 + (τ p.1 l : Fin g → ℂ)) = (u p.1).ex p.2 := by
          rw [(u p.1).ex_add, ((u p.1).ker _).2 (τ p.1 l).2, _root_.mul_one]
        exact congrArg (fun x : 𝟙_ (Over (Sp ℂ)) ⟶ A p.1 ↦ (show Sp ℂ ⟶ (A p.1).left from x.left) ≫ φ p.1) this
      hol U' f := by
        have := hhol U' f
        simp only [Set.mem_prod, Set.mem_univ, and_true] at this
        exact this }
  haveI : IsSeparated (𝒜.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]
    haveI := h𝒜.proper
    infer_instance
  choose per hper using HE I g u₀.Λ F B 𝒜.left _ _ e ⟨W, hW, hW0⟩
  have fix : ∀ x (c : primDR 𝒜), ∀ z ∈ V, P z (τ z x) ((m z).pull c) = (per c.1 x).fn z := fun x c z hz ↦
    HX I g u₀.Λ F B 𝒜 h𝒜 _ e z hz _ (fun b ↦ (hσ b z hz).symm) (A z) (hA z) (φ z) (m z) (L z) (u z) (fun _ ↦ rfl)
      (τ z).toAddMonoidHom (fun _ ↦ rfl) (P z) (hP z) c _ (hper c.1) x
  have nV : (V : Set (I → ℂ)) ∈ nhds (0 : I → ℂ) := V.isOpen.mem_nhds V0
  refine ⟨Metric.ball 0 r, u, τ, P, P₀, Metric.isOpen_ball, V0, hrU, pm A₀ g hA₀ gA₀ L₀ hL₀ u₀ P₀ hP₀,
    fun z _ ↦ pm _ g (hA z) (gA z) _ (hL z) _ _ (hP z), c1, c2, c3, c4,
    fun x c ↦ (per c.1 x).analytic.differentiableOn.congr (fix x c), ?_⟩
  intro D _ _ π κ hκ hπ N t ht hN j hj A' _ φ' hφ' m' i h hi k x d hd c
  rw [HT I g B 𝒜 h𝒜 hg (y 0) A₀ φ₀ hφ₀ L₀ u₀ F σ e V0 (fun b ↦ (hσ b 0 V0).symm) c1 (fun x ↦ c2 x) P₀ hP₀ D π κ hκ hπ N t ht hN j
    (fun b ↦ (hj b).trans (taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (hσ b z hz).symm)))
    A' φ' hφ' m' i h hi k x d hd c _ (hper c.1)]
  exact taylor_congr N t (Filter.mem_of_superset nV fun z hz ↦ (fix x c z hz).symm)

end GlobalTheory.AnPer
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private def piSL {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {J : Type} {M M' : J → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[σ] M' i) : (∀ i, M i) →ₛₗ[σ] (∀ i, M' i) where
  toFun x i := f i (x i)
  map_add' x y := by funext i; simp
  map_smul' r x := by funext i; simp [map_smulₛₗ]

private theorem piSL_bij {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {J : Type} [Finite J]
    {M M' : J → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i)
    (hf : ∀ i, Function.Bijective (liftSemi (f i))) : Function.Bijective (liftSemi (piSL f)) :=
  liftSemi_pi_bijective R R' J M M' f _ (fun _ _ ↦ rfl) hf

theorem liftSemi_pullTot1_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ C _ _ _ F F' α hn hs h
  let a : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T ↦
    { toFun := α T, map_add' := map_add (α T), map_smul' := hs T }
  have ha : ∀ T, Function.Bijective (liftSemi (a T)) := fun T ↦ h T (a T) fun _ ↦ rfl
  have hsh : ∀ T, SemiHom (algebraMap R R') (α T) := fun T ↦
    semiHom_coef (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F') T
  refine GlobalTheory.T.liftBaseChange_prod_bijective_semilinear R R' _ _ _ _
    (piSL fun T : C ↦ piSL fun T' : C ↦ piSL fun _ : T ⟶ T' ↦ a T')
    (piSL fun T : C ↦ (hsh T).m1) _ (fun _ ↦ rfl) ?_ ?_
  · exact piSL_bij _ fun T ↦ piSL_bij _ fun T' ↦ piSL_bij _ fun _ ↦ ha T'
  · exact piSL_bij _ fun T ↦
      GlobalTheory.T.bijective_liftSemi_of_semilinear_hom R R' _ _ (α T) (hsh T) (a T) (fun _ ↦ rfl) (ha T)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.restrict_finite_affineCover_infClosed_pull2_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull2 := by
  first | exact @GlobalTheory.AbCohCover.restrict_pull2_bijective | exact GlobalTheory.AbCohCover.restrict_pull2_bijective | (intros; apply GlobalTheory.AbCohCover.restrict_pull2_bijective <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

theorem _root_.GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (z : Af E), l.Prime → (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v (z w) ≤ 1) → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((algebraMap E (Af E) (M : E) * z) w) ≤ 1 := by
  first | exact @GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | exact GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to | (intros; apply GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_pDivGroupFormalChart_of_connected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  first | exact @GlobalTheory.ChartEx.chart_exists | exact GlobalTheory.ChartEx.chart_exists | (intros; apply GlobalTheory.ChartEx.chart_exists <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  first | exact @GlobalTheory.QLog.Chart.existsUnique_isLie | exact GlobalTheory.QLog.Chart.existsUnique_isLie | (intros; apply GlobalTheory.QLog.Chart.existsUnique_isLie <;> assumption)
end
