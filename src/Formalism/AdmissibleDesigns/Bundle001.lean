module

public import Formalism.AdmissibleDesigns.NonemptyPl
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle010
public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapSecondPlace
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapTheorem
import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle011
public import Formalism.AdmissibleDesigns.TrCMemZ1D
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Formalism.WachLatticeTwists.SplitClassesAll.Statement
import Formalism.WachLatticeTwists.SplitLocalLifts.Statement

@[expose] public section

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.QS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Places
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

def Vo : Type :=
  {v : HeightOneSpectrum (𝓞 D.host.E) // v ∉ placesOver D.host.E (D.nd.l i) ∧ v ∉ D.nd.S i ∧ v ∉ D.nd.Q i}

def VS : Type := {v : HeightOneSpectrum (𝓞 D.host.E) // v ∈ D.nd.S i}

def Io (v : Vo i) : Subgroup (GE D.nd) := Ine (F := D.host.E) (D.nd.plOm.1 v.1)

def IS (v : VS i) : Subgroup (GE D.nd) := Ine (F := D.host.E) (D.nd.plOm.1 v.1)

def I (w : ℕ) : Subgroup (decs D.host.E (Aw i dc) w) :=
  (Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w)

def γQ (w : ℕ) : decs D.host.E (Aw i dc) w :=
  ⟨D.nd.gam0 i (plOf i dc w), Ine_le_Dec _ (D.nd.locNd_chebotarevPlace_mem i (plOf i dc w))⟩

def ζO (w : ℕ) : D.nd.O i := D.nd.zeta i (plOf i dc w)

def nQ (w : ℕ) (g : decs D.host.E (Aw i dc) w) : ℕ :=
  if h : ∃ n : ℕ, D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ n then Nat.find h else 0

def QPow : Prop :=
  ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n

end Places

section Ring
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def ζ (w : ℕ) : Dd.T' := ((Dd.χ (γQ i dc w : GE D.nd) : Dd.T'ˣ) : Dd.T')

abbrev Mc (c : Fin (D.R.t + 1)) : Type := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c

abbrev resU (c : Fin (D.R.t + 1)) (w : ℕ) :=
  resRep (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (decs D.host.E (Aw i dc) w)

def Fpos (c : Fin (D.R.t + 1)) (w : ℕ) : Submodule (D.nd.O i) (H1z (resU i dc Dd c w)) :=
  if w ∈ qsN i dc then unrH1 (resU i dc Dd c w) (I i dc w)
  else if w ∈ rowsN i dc then
    (if (c : ℕ) = 1 then lcH1 (resU i dc Dd c w) ⊓
        unrH1 (resU i dc Dd c w) ((Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w))
      else ⊥)
  else if (c : ℕ) = 1 then unrH1 (resU i dc Dd c w) (I i dc w) else ⊥

def Fall (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1)) (w : ℕ) :
    Submodule (D.nd.O i) (H1z (resU i dc Dd c w)) :=
  Fin.cases (motive := fun c => Submodule (D.nd.O i) (H1z (resU i dc Dd c w))) (F0 w)
    (fun c' => Fpos i dc Dd c'.succ w) c

def c1 : Fin (D.R.t + 1) := ⟨1, by have := RepresentationBoundsCohomology.one_le_letterBlockLength D.R; omega⟩

def InertiaActsTrivially : Prop := ∀ v, ∀ g ∈ Io i v, Dd.r g = 1 ∧ Dd.χ g = 1

def LocClause (c : Fin (D.R.t + 1)) : Prop :=
  InChiLoc (Mc i Dd c) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc) (Fpos i dc Dd c) (Io i) (IS i)
    (I i dc) (γQ i dc) (ζ i dc Dd) (ζO i dc) (nQ i dc)

def CoverClause : Prop :=
  ∀ v, (∃ a, Ine (F := D.host.E) (Av v) ≤ Io i a) ∨ (∃ a, Ine (F := D.host.E) (Av v) ≤ IS i a) ∨
    ∃ w ∈ rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc), ∃ J : Subgroup (decs D.host.E (Aw i dc) w),
      Fpos i dc Dd (c1 (D := D)) w ≤ unrH1 (resU i dc Dd (c1 (D := D)) w) J ∧
      Ine (F := D.host.E) (Av v) ≤ J.map (decs D.host.E (Aw i dc) w).subtype

def NoFixedVectorOffZ : Prop :=
  ∀ x', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) →
    ∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing (D.nd.O i))
        (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.E), η ≠ 0 →
      ∃ g : GE D.nd, ((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') • Dd.r g) • η ≠ η

end Ring

end Formalism.MainNotions.N.K.QS

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB

section Eps

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

def epsHom (e : ℕ) : G →* Matrix (Fin 1) (Fin 1) LL where
  toFun := Formalism.MainNotions.N.epsTw PD (LL := LL) e
  map_one' := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [Formalism.MainNotions.N.epsTw]
  map_mul' g h := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [Formalism.MainNotions.N.epsTw, Matrix.mul_apply, mul_pow]
    ring

theorem matRep_eps (e : ℕ) (g : G) (v : Fin 1 → LL) :
    Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) g v =
      fun _ => (algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) ^ e * v 0 := by
  funext j
  change Matrix.mulVec (Formalism.MainNotions.N.epsTw PD (LL := LL) e g) v j = _
  simp [Matrix.mulVec, dotProduct, Formalism.MainNotions.N.epsTw]

variable {PD}

@[reducible] def twLat (hinj : Function.Injective (algebraMap O LL)) (ε' : G → O)
    (hε : ∀ g, algebraMap O LL (ε' g) = algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) (e : ℕ)
    (hcont : Continuous fun g => (algebraMap O LL (ε' g)) ^ e) : TwLat PD LL O e where
  V := Fin 1 → LL
  ρ := Formalism.MainNotions.N.matRep (epsHom PD e)
  L :=
    { T := Formalism.MainNotions.N.stdG O LL 1
      stable := by
        intro g x hx
        obtain ⟨u, rfl⟩ := hx
        refine ⟨fun _ => (ε' g) ^ e * u 0, ?_⟩
        rw [matRep_eps]
        funext j
        simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, map_mul, map_pow, hε]
      fg := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).fg
      free := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).free
      span := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).span }
  cont := by
    intro x
    have h : (fun g => Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) g x) =
        fun g => fun _ : Fin 1 => (algebraMap O LL (ε' g)) ^ e * x 0 := by
      funext g
      rw [matRep_eps, hε]
    rw [h]
    exact continuous_pi fun _ => hcont.mul continuous_const
  mat := by
    refine ⟨LinearEquiv.refl LL _, fun g v => rfl, fun v => ⟨?_, ?_⟩⟩
    · rintro ⟨u, rfl⟩ j
      exact ⟨u j, rfl⟩
    · intro hv
      choose u hu using hv
      exact ⟨u, funext fun j => hu j⟩

theorem actD_twLat (hinj : Function.Injective (algebraMap O LL)) (ε' : G → O)
    (hε : ∀ g, algebraMap O LL (ε' g) = algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) (e : ℕ)
    (hcont : Continuous fun g => (algebraMap O LL (ε' g)) ^ e) (h : G)
    (x : (twLat hinj ε' hε e hcont).V ⧸ (twLat hinj ε' hε e hcont).L.T) :
    actD (twLat hinj ε' hε e hcont).L h x = (ε' h ^ e) • x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    unfold actD
    refine (congrArg Submodule.Quotient.mk
      (?_ : (twLat hinj ε' hε e hcont).ρ h v = (ε' h ^ e) • v)).trans
      (Submodule.Quotient.mk_smul _ _ _)
    funext j
    show Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) h v j = (ε' h ^ e) • v j
    rw [matRep_eps, Algebra.smul_def, map_pow, hε, Subsingleton.elim j 0]

end Eps

section KO

variable {O' : Type} [CommRing O'] [IsDomain O'] {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  (σ : O' ≃+* O) (eK : FractionRing O' ≃+* LL)
  (heK : ∀ c : O', eK (algebraMap O' (FractionRing O') c) = algebraMap O LL (σ c))

def kVec : FractionRing O' →ₛₗ[σ.toRingHom] (Fin 1 → LL) where
  toFun x := fun _ => eK x
  map_add' x y := by
    funext j
    simp
  map_smul' c x := by
    funext j
    simp only [Algebra.smul_def, map_mul, heK, Pi.smul_apply]
    rfl

def vecK : (Fin 1 → LL) →ₛₗ[σ.symm.toRingHom] FractionRing O' where
  toFun v := eK.symm (v 0)
  map_add' u v := by simp
  map_smul' c v := by
    apply eK.injective
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, RingEquiv.apply_symm_apply, heK]
    exact congrArg (fun y => algebraMap O LL y * v 0) (σ.apply_symm_apply c).symm

theorem kVec_le : (1 : Submodule O' (FractionRing O')) ≤ (Formalism.MainNotions.N.stdG O LL 1).comap (kVec σ eK heK) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hx
  rw [Submodule.mem_comap]
  refine ⟨fun _ => σ c, ?_⟩
  funext j
  show algebraMap O LL (σ c) = eK (algebraMap O' (FractionRing O') c)
  exact (heK c).symm

def koTo : KO O' →ₛₗ[σ.toRingHom] ((Fin 1 → LL) ⧸ Formalism.MainNotions.N.stdG O LL 1) :=
  Submodule.mapQ _ _ (kVec σ eK heK) (kVec_le σ eK heK)

def koEquiv : KO O' ≃+ ((Fin 1 → LL) ⧸ Formalism.MainNotions.N.stdG O LL 1) where
  toFun := koTo σ eK heK
  invFun := Submodule.mapQ _ _ (vecK σ eK heK) (by
    rintro _ ⟨u, rfl⟩
    refine Submodule.mem_one.2 ⟨σ.symm (u 0), ?_⟩
    apply eK.injective
    show eK (algebraMap O' (FractionRing O') (σ.symm (u 0))) = eK (eK.symm (algebraMap O LL (u 0)))
    rw [heK, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply])
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      show Submodule.Quotient.mk (eK.symm (eK x)) = _
      rw [RingEquiv.symm_apply_apply]
  right_inv v := by
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      show Submodule.Quotient.mk (fun _ => eK (eK.symm (v 0))) = _
      congr 1
      funext j
      rw [RingEquiv.apply_symm_apply, Subsingleton.elim j 0]
  map_add' x y := map_add _ x y

theorem koEquiv_smul (a : O') (x : KO O') : koEquiv σ eK heK (a • x) = σ a • koEquiv σ eK heK x := by
  show koTo σ eK heK (a • x) = σ a • koTo σ eK heK x
  exact (koTo σ eK heK).map_smulₛₗ a x

end KO

end Formalism.MainNotions.N.K.TBb

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] {σ : O' ≃+* O}
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    {r : GG →* A} {χ : GG →* T'ˣ} {E : A} {Dw : Subgroup GG} {eG : Dw ≃* G}

theorem back_cob {e cB ℓ : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hp : PD.p = ℓ) (z : Dw → M)
    (x : Cd.Ce.V ⧸ Cd.Ce.L.T) (g : Dw)
    (hg : (((PD.p : O) ^ cB) • trC Cd z) (eG g) = actD Cd.Ce.L (eG g) x - x) :
    ((ℓ : O') ^ cB) • z g = uElt r χ (g : GG) • Cd.u.symm x - Cd.u.symm x := by
  apply Cd.u.injective
  rw [map_sub, Cd.u_act, AddEquiv.apply_symm_apply, Cd.u_smul, map_pow, map_natCast, ← hg, ← hp]
  simp only [trC, MulEquiv.symm_apply_apply, Pi.smul_apply]

theorem tb_pos {e t cB ℓ : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (he : 0 < e) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd) [TopologicalSpace Dw]
    (hloc : YLoc (O := O') M r χ E Dw) (heG : Continuous eG.symm) (hp : PD.p = ℓ)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : ∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : GG))) :
    ((ℓ : O') ^ cB) • (z : Dw → M) ∈ coB1 (resRep (uRep O' (M := M) r χ) Dw) := by
  have hzl : IsLocallyConstant (z : Dw → M) := by
    have h := hloc ψ hψe
    have hf : (z : Dw → M) = fun g : Dw => ψ (yY r χ E (g : GG)) := funext hz
    rw [hf]
    exact h
  have h1 := trC_hf hTB het Y hY Cd hψ ψ hψe (z : Dw → M) hz
  have h2 := trC_mem_Z1D Cd heG z hzl ((PD.p : O) ^ cB)
  obtain ⟨x, hx⟩ := (hTB.2 e het Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat).1 he ⟨h2, h1⟩
  refine ⟨Cd.u.symm x, ?_⟩
  funext g
  show uElt r χ (g : GG) • Cd.u.symm x - Cd.u.symm x = ((ℓ : O') ^ cB) • (z : Dw → M) g
  refine (back_cob Cd hp (z : Dw → M) x g ?_).symm
  have := congrFun hx (eG g)
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
  exact this.symm

theorem tb_zero {e t cB ℓ : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (he : e = 0) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd) [TopologicalSpace Dw]
    (hloc : YLoc (O := O') M r χ E Dw) (heG : Continuous eG.symm) (hp : PD.p = ℓ)
    (I' : Subgroup Dw) (hI : ∀ g : Dw, g ∈ I' → eG g ∈ I)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : ∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : GG))) :
    IsLocallyConstant (z : Dw → M) ∧
    ∃ m : M, ∀ g : Dw, g ∈ I' → ((ℓ : O') ^ cB) • (z : Dw → M) g = uElt r χ (g : GG) • m - m := by
  have hzl : IsLocallyConstant (z : Dw → M) := by
    have h := hloc ψ hψe
    have hf : (z : Dw → M) = fun g : Dw => ψ (yY r χ E (g : GG)) := funext hz
    rw [hf]
    exact h
  refine ⟨hzl, ?_⟩
  have h1 := trC_hf hTB het Y hY Cd hψ ψ hψe (z : Dw → M) hz
  have h2 := trC_mem_Z1D Cd heG z hzl ((PD.p : O) ^ cB)
  have hmem : ((PD.p : O) ^ cB) • trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := ⟨h2, h1⟩
  rw [(hTB.2 e het Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat).2.1 he] at hmem
  obtain ⟨a, ⟨x, hx⟩, b, ⟨y, hy⟩, hab⟩ := Submodule.mem_sup.1 hmem.2
  refine ⟨Cd.u.symm (x + y), fun g hg => back_cob Cd hp (z : Dw → M) (x + y) g ?_⟩
  have hb := congrFun hy (eG g)
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at hb
  rw [← hab, Pi.add_apply, hx (eG g) (hI g hg), ← hb, map_add (f := _)]
  abel

end Transport

section Cls

variable {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (ρ : Representation O Γ M)

theorem mkQ_eq_zero_of (z : coZ1s ρ) (h : (z : Γ → M) ∈ coB1 ρ) :
    (Submodule.mkQ _ z : H1z ρ) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr h

theorem mem_unramified_of_coboundary (I : Subgroup Γ) (z : coZ1s ρ) (m : M) (hm : ∀ g ∈ I, (z : Γ → M) g = ρ g m - m) :
    (Submodule.mkQ _ z : H1z ρ) ∈ unrH1 ρ I := by
  rw [unrH1, LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨m, ?_⟩
  funext g
  exact (hm g.1 g.2).symm

theorem mem_locally_constant_of [TopologicalSpace Γ] (z : coZ1s ρ) (h : IsLocallyConstant (z : Γ → M)) :
    (Submodule.mkQ _ z : H1z ρ) ∈ Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 ρ :=
  ⟨z, h, rfl⟩

end Cls

end Formalism.MainNotions.N.K.TB

end
end
