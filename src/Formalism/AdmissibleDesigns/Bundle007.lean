module

public import Formalism.AdmissibleDesigns.CoboundaryMemFiniteClasses
public import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
public import Formalism.AdmissibleDesigns.Bundle005
public import Formalism.AdmissibleDesigns.Bundle002
public import Formalism.AdmissibleDesigns.EKSymmCont
public import Formalism.AdmissibleDesigns.HigherColumnInvariantsBound
public import Formalism.AdmissibleDesigns.CocZeroOfUnr
public import Formalism.AdmissibleDesigns.H1MapMemLcH1
public import Formalism.AdmissibleDesigns.H1MapMemLocallyConstant
import Formalism.AdmissibleDesigns.TensSubsingleton
public import Formalism.AdmissibleDesigns.Bundle004
public import Formalism.AdmissibleDesigns.URecApply
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem msContW (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : K.TBa.MsContW (i := i) (r := r) hw :=
  fun x => locC_cont i r hc hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) x

end Formalism.MainNotions.N.KOrb

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem coefChange_rec : CoefChange (D.nd.l i) (D.nd.O i) :=
  CoefT.coefChange _ _

theorem tieSel2_full [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}
    {π : D.nd.X i} {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1)) (hc : 2 ≤ (c : ℕ)) :
    TieSel2 i (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) (qsN i dc)
      (Fall i dc Dd F0 c) (Io i) (IS i) (c : ℕ) := by
  exact tieSel2_rec (i := i) (dc := dc) (Dd := Dd) (hD := hD) (hN := hN) (F0 := F0) (c := c) (hc := hc)
    (hC := coefChange_rec i) (hZ := fun e _ => zlSha i dc e)

end Formalism.MainNotions.N.K.ShaT

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section Record

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

theorem nzsd_R' : NoZeroSMulDivisors (D.nd.O i) Dd.R' := by
  first
  | exact inferInstance
  | (haveI : NoZeroSMulDivisors (D.nd.O i) (FractionRing (D.nd.O i)) :=
        NoZeroSMulDivisors.of_algebraMap_injective (IsFractionRing.injective _ _); exact inferInstance)
  | exact ⟨fun {c x} h => by
      by_cases hc : c = 0
      · exact Or.inl hc
      · refine Or.inr (Subtype.ext (funext fun x' => Matrix.ext fun a b => ?_))
        have h1 := congrFun (congrFun (congrFun (congrArg Subtype.val h) x') a) b
        have h2 : algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c ≠ 0 := fun h0 =>
          hc (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)) (h0.trans (map_zero _).symm))
        simp only [SetLike.val_smul, Pi.smul_apply, Matrix.smul_apply,
          ZeroMemClass.coe_zero, Pi.zero_apply, Matrix.zero_apply] at h1
        rw [Algebra.smul_def] at h1
        exact (mul_eq_zero.mp h1).resolve_left h2⟩

theorem heS {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (selfO i hw a) =
      eS i hw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) := by
  first
  | rfl
  | (have e1 : ∀ y, eS i hw y = Formalism.MainNotions.N.Br.toLLK (D.nbr i w hw) y := fun _ => rfl
     rw [e1, Formalism.MainNotions.N.Br.toLLK, IsFractionRing.lift_algebraMap]
     rfl)

variable {i dc r Dd}

theorem fd_yt {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (hemb : YtEmbW i dc r Dd hw) :
    FiniteDimensional ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (TrV (eS i hw) (MK (O := D.nd.O i) (YtM i Dd))) := by
  obtain ⟨m, xs, φ, hφ, -⟩ := hemb
  first
  | exact FiniteDimensional.of_injective φ hφ
  | exact Module.Finite.of_injective φ hφ

private theorem continuous_of_injective_linearMap_comp {K V W G : Type*} [Field K] [TopologicalSpace K]
    {_a : AddCommMonoid V} {_m : Module K V} [TopologicalSpace V] [ContinuousAdd V] [IsModuleTopology K V]
    {_aw : AddCommMonoid W} {_mw : Module K W} [TopologicalSpace W] [IsModuleTopology K W]
    [TopologicalSpace G] (φ : V →ₗ[K] W) (hφ : Function.Injective φ) (f : G → V)
    (hf : Continuous fun g => φ (f g)) : Continuous f := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  haveI : ContinuousSMul K V := by
    first
    | exact inferInstance
    | exact IsModuleTopology.toContinuousSMul K V
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ (LinearMap.ker_eq_bot.mpr hφ)
  have hψc : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ
  have e1 : f = fun g => ψ (φ (f g)) := funext fun g => (LinearMap.congr_fun hψ (f g)).symm
  rw [e1]
  exact hψc.comp hf

theorem cont_yt {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw) (v) : Continuous fun g => ytV i dc Dd hw g v := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := hemb
  have hc' : ∀ x, Continuous (MsW i r hw x) := hc
  refine continuous_of_injective_linearMap_comp φ hφ (fun g => ytV i dc Dd hw g v) ?_
  refine Continuous.congr (f := fun g => fun a => (MsW i r hw (xs a) g).mulVec (φ v a)) ?_
    (fun g => (heq g v).symm)
  refine continuous_pi fun a => ?_
  first
  | exact (hc' (xs a)).matrix_mulVec continuous_const
  | fun_prop

def ytY (hfin : Module.Finite (D.nd.O i) Dd.R') {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw) :
    YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
      ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) :=
  haveI := hfin
  haveI := nzsd_R' i Dd
  ytG ℚ_[D.nd.l i] (heS i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) (fd_yt hemb) (cont_yt hemb hc)

theorem msW_eq {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    MsW i r hw x = twistM (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C (TruncatedSeriesCountingIdentities.CoefExt.self i w hw))⁻¹ := by
  ext g a b
  first
  | exact ((TruncatedSeriesCountingIdentities.CoefExt.self i w hw).inc.comp
      ((algebraMap ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1).comp
        (selfO i hw).toRingHom)).map_mul _ _
  | (simp only [MsW, TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, rTwO, twistM, mapM, Formalism.MainNotions.N.Br.loc, Formalism.MainNotions.N.Br.locChi,
      Formalism.MainNotions.N.Br.locM, Formalism.MainNotions.N.Br.locO, Formalism.MainNotions.N.Br.chiG, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_mk, OneHom.coe_mk, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, MonoidHom.inv_apply,
      Units.coe_map_inv, map_mul]
     rfl)

variable (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))



theorem ytPsi_rec (hfin : Module.Finite (D.nd.O i) Dd.R') {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw)
    [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (c : Fin (D.R.t + 1))
    (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)) :
    PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) (ytY hfin hemb hc) Cd := by
  haveI := hfin
  haveI := nzsd_R' i Dd
  first
  | apply ytG_psi
  | (unfold ytY; apply ytG_psi)

theorem jump_pi (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hc : MsContW i r hw) (x : D.nd.X i) (τ) (a : ℤ)
    (hx : IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) τ a) :
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw π)) τ a := by
  have hFs := hF w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)
  have hMs : ∀ y, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw y)) := fun y => by
    rw [msW_eq]
    exact (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2 y
  have hfd : FiniteDimensional ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
      ↥(DdR (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x))) :=
    fd_of_crys (Br.PD D.loc D.nbr i w hw) hFs (matG (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (MsW i r hw) hc x) (hMs x)
  have hp := mult_pos (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) τ a hx
  have heqm := (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).1.2.1 τ x π a
  rw [← msW_eq, ← msW_eq] at heqm
  exact jump_of_mult _ _ τ a (by rw [← heqm]; exact hp.ne')

theorem ytTarget_of (hfin : Module.Finite (D.nd.O i) Dd.R') (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw)
    [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (c : Fin (D.R.t + 1)) :
    YtTarget i dc r π Dd hw c := by
  intro Cd
  haveI := hfin
  haveI := nzsd_R' i Dd
  have hMs : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) := fun x => by
    rw [msW_eq hw x]
    exact (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2 x
  obtain ⟨m, xs, φ, hφ, heq⟩ := id hemb
  have hcrys : IsCrys (Br.PD D.loc D.nbr i w hw) (ytY hfin hemb hc).ρ ∧
      ∀ τ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (ytY hfin hemb hc).ρ τ a →
        ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) τ a :=
    ytG_crys (hF := hF w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) (Ms := MsW i r hw) (hMc := hc) (hMs := hMs)
      (xs := xs) (φ := φ) (hφ := hφ) (heq := heq) ..
  refine ⟨ytY hfin hemb hc, ?_, ytPsi_rec hfin hemb hc c Cd⟩
  unfold YtCrys
  refine ⟨hcrys.1, fun τ => ?_⟩
  intro a ha
  obtain ⟨x, hx⟩ := hcrys.2 τ a ha
  exact jump_pi (hF := hF) (hG2 := hG2) (hw := hw) (hc := hc) (x := x) (hx := hx)

end Record

end Formalism.MainNotions.N.K.TBa

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT' w)] [∀ w, TopologicalSpace (VT' w)] [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)]
  {T₁ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁]

def RowTop1 : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    ∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hn g)))) →
        Continuous c

theorem rowTop_of
    (hT : ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
      KBKa.TopMatch (eK (D.nbr i _ hn)) (VT' n))
    (h1 : RowTop1 i dc (T₁ := T₁)) : RowTop i dc VT' (T₁ := T₁) := by
  intro n hn hpl
  refine ⟨fun c hc => ?_, h1 n hn hpl⟩
  have h := hT n hn hpl
  have h2 := (KBKa.cont_iff _ h _).1 hc
  have h3 : Continuous fun g => c (Br.iota D.nbr i _ hpl g) := h2
  obtain ⟨hm, hhm⟩ := KBKa.iotaHomeo_rec (i := i) (dc := dc) hpl
  have hc' : c = (fun g => c (Br.iota D.nbr i _ hpl g)) ∘ hm.symm := by
    funext x
    simp only [Function.comp, ← hhm]
    exact congrArg c (hm.apply_symm_apply x).symm
  rw [hc']
  exact h3.comp hm.symm.continuous

end Rec

end Formalism.MainNotions.N.KRow

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem contW_rec (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l :=
  contW_of i dc ρ π (K.Norm.rhoCont_of i r ρ π hd hc) l

end Formalism.MainNotions.N.KOrb

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem uRec_smul {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) (a : D.nd.O i) (m : Mc i Dd c) :
    uRec i Dd hw c φ (a • m) = (D.nbr i w hw).eO a • uRec i Dd hw c φ m := by
  rw [uRec_apply, uRec_apply]
  exact (congrArg (koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw))
    (fun x => Br.toLLK_alg (D.nbr i w hw) x)) (φ.map_smul a m)).trans (koEquiv_smul _ _ _ _ _)

theorem uRep_apply' (c : Fin (D.R.t + 1)) (g : GE D.nd) (m : Mc i Dd c) :
    uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m = uElt Dd.r Dd.χ g • m := rfl

omit [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem koE_apply' (e : ℕ) (g : GE D.nd) (x : KO (D.nd.O i)) : koE i e g x = sE i e g • x := rfl

theorem eO_sE (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (e : ℕ) (g : Dw i dc (idx i dc w)) :
    (D.nbr i w hw).eO (sE i e (g : GE D.nd)) = (epsL i dc hw (eW i dc hw g)) ^ e := by
  have hz : (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = ((cycE i (g : GE D.nd))⁻¹) ^ e := by
    rw [show (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = (cycE i (g : GE D.nd)) ^ (-(e : ℤ)) from rfl,
      zpow_neg, zpow_natCast, inv_pow]
  have key : sE i e (g : GE D.nd) = (algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (((cycE i (g : GE D.nd))⁻¹ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) ^ e := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hz]
    rfl
  rw [key, map_pow]
  simp [epsL]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem uRec_act (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (g : Dw i dc (idx i dc w)) (m : Mc i Dd c) :
    uRec i Dd hw c φ (uElt Dd.r Dd.χ (g : GE D.nd) • m) =
      (epsL i dc hw (eW i dc hw g)) ^ ((c : ℕ) - 1) • uRec i Dd hw c φ m := by
  have h1 : uElt Dd.r Dd.χ (g : GE D.nd) • m = sE i ((c : ℕ) - 1) (g : GE D.nd) • m := by
    apply φ.injective
    rw [← uRep_apply' i Dd c, hφ, koE_apply', φ.map_smul]
  rw [h1, uRec_smul, eO_sE i dc hcyc hw]




def coefDictOf (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (hcont : Continuous fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^ ((c : ℕ) - 1)) :
    CoefDict (Br.PD D.loc D.nbr i w hw) (Br.LLw (D.nbr i w hw)) (Br.Ow (D.nbr i w hw)) (D.nbr i w hw).eO
      (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1) where
  Ce := twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont
  u := uRec i Dd hw c φ
  u_smul a m := uRec_smul i Dd hw c φ a m
  u_act g m := (uRec_act i dc Dd hcyc hw c φ hφ g m).trans
    (actD_twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont (eW i dc hw g)
      (uRec i Dd hw c φ m)).symm

end Dict

end Formalism.MainNotions.N.K.TBb

end
end
