module

public import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
public import Formalism.AdmissibleDesigns.ContOfInjY
public import Formalism.AdmissibleDesigns.TrCMemZ1D
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.FirstSummandRepresentation
public import Formalism.AdmissibleDesigns.TensSubsingleton
import Mathlib.Algebra.Module.Torsion.Prod
public import Formalism.AdmissibleDesigns.ExistsWildInertiaCyclotomicGenerator
public import Formalism.AdmissibleDesigns.FinDimOfLat
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Formalism.WachLatticeTwists.SplitLocalLifts.Statement

@[expose] public section

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i)

theorem wpO_cont (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous (WpO D.nd i ρ π) := by
  have hχ : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have he : (fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      simp [chiU, map_inv]
    rw [he]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  show Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π g
  exact hχ.smul hρ

theorem loc_cont {k : ℕ} {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous ⇑(Br.loc D.nbr i w hw M) := by
  unfold Br.loc Br.locM Br.locO mapM
  simp only [MonoidHom.coe_comp]
  refine Continuous.comp ?_ (Continuous.comp (Continuous.comp ?_ (Continuous.comp hM ?_)) ?_)
  · first
      | exact continuous_id.matrix_map continuous_subtype_val
      | exact continuous_id.matrix_map continuous_induced_dom
  · exact continuous_id.matrix_map (D.nbr i w hw).eO_cont
  · exact continuous_subtype_val
  · first
      | exact (D.nbr i w hw).e_symm_cont
      | exact continuous_subtype_val.comp (D.nbr i w hw).e_symm_cont

theorem contW_of (hρ : Continuous fun g => rhoO D.nd i ρ π g) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l := by
  intro v
  have hL := loc_cont i (KDim.col_over i dc l) (WpO D.nd i ρ π) (wpO_cont i ρ π hρ)
  have h2 : Continuous fun g => Matrix.mulVec (Br.loc D.nbr i _ (KDim.col_over i dc l) (WpO D.nd i ρ π) g) v :=
    hL.matrix_mulVec continuous_const
  refine h2.congr fun g => ?_
  first
    | rfl
    | simp [KDim.repW, matRep, Matrix.toLinAlgEquiv'_apply]

end Formalism.MainNotions.N.KOrb

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section Mk

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {e : FractionRing O ≃+* LL} {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {N : Type} [AddCommGroup N] [Module O N] [Module.Finite O N] [Module.Free O (N × O)] [NoZeroSMulDivisors O (N × O)]
  (Qp : Type) [Field Qp] [Algebra Qp LL]
  (ρM : Representation O Γ (N × O)) (h2 : ∀ g m, (ρM g m).2 = m.2)
  [FiniteDimensional LL (TrV e (MK (O := O) (N × O)))]
  (hcont : ∀ x, Continuous fun g => repL e (locRep ρM) ι g x)

def mkYt : YtLat (G := G) (Qp := Qp) LL Ow where
  V := TrV e (MK (O := O) (N × O))
  ρ := repL e (locRep ρM) ι
  L := latY heO ι ρM
  cont := hcont
  p := pY e N
  p_inv g v := pY_inv ι ρM h2 g v
  p_int v hv := pY_int heO v hv
  e₀ := trY e (mkK (O := O) ((0 : N), (1 : O)))
  e₀_mem := ⟨_, rfl⟩
  p_e₀ := by rw [pY_mk]; simp

end Mk

section GenY

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  {A T' GG : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group GG]
  (r : GG →* A) (χ : GG →* T'ˣ) (E : A)

theorem nzsdY [NoZeroSMulDivisors O A] : NoZeroSMulDivisors O ↥(Ymod r χ E) :=
  Function.Injective.noZeroSMulDivisors (fun y : ↥(Ymod r χ E) => (y : A)) Subtype.val_injective rfl
    (fun _ _ => rfl)

theorem finY [Module.Finite O A] : Module.Finite O ↥(Ymod r χ E) := by
  haveI : IsNoetherian O A := isNoetherian_of_isNoetherianRing_of_finite O A
  let f : ↥(Ymod r χ E) →ₗ[O] A :=
    { toFun := fun y => (y : A), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f Subtype.val_injective

theorem freeY [Module.Finite O A] [NoZeroSMulDivisors O A] : Module.Free O (↥(Ymod r χ E) × O) := by
  haveI := finY (O := O) r χ E
  haveI := nzsdY (O := O) r χ E
  haveI := nzsd_prod (O := O) (N := ↥(Ymod r χ E))
  exact Module.free_of_finite_type_torsion_free'

theorem ytRep_zero (g : GG) (y : ↥(Ymod r χ E)) : ytRep O r χ E g (y, 0) = (uElt r χ g • y, 0) :=
  Prod.ext (by
    show uElt r χ g • y + (0 : O) • yY r χ E g = _
    rw [zero_smul, add_zero]) rfl

theorem ytRep_e (g : GG) : ytRep O r χ E g (0, 1) = (yY r χ E g, 1) :=
  Prod.ext (by
    show uElt r χ g • (0 : ↥(Ymod r χ E)) + (1 : O) • yY r χ E g = _
    rw [smul_zero, one_smul, zero_add]) rfl

end GenY

section GenT

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {Ow : Type} [CommRing Ow] [Algebra Ow LL]
    {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {e : FractionRing O ≃+* LL} {eO : O ≃+* Ow}
    (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    {A T' GG : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group GG]
    (r : GG →* A) (χ : GG →* T'ˣ) (E : A) (Dw : Subgroup GG) (eG : ↥Dw ≃* G)

abbrev ytVG : Representation LL G (TrV e (MK (O := O) (↥(Ymod r χ E) × O))) :=
  repL e (locRep (resRep (ytRep O r χ E) Dw)) eG.symm.toMonoidHom


variable (Qp) in
def ytG [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x) : YtLat (G := G) (Qp := Qp) LL Ow :=
  haveI := finY (O := O) r χ E
  haveI := freeY (O := O) r χ E
  haveI := nzsdY (O := O) r χ E
  haveI := nzsd_prod (O := O) (N := ↥(Ymod r χ E))
  mkYt heO eG.symm.toMonoidHom Qp (resRep (ytRep O r χ E) Dw) (fun _ _ => rfl) hcont

theorem ytG_psi [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x)
    {M : Type} [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M] {e' : ℕ}
    (Cd : CoefDict PD LL Ow eO M r χ Dw eG e') :
    PsiExt eO r χ E Dw eG (ytG Qp heO r χ E Dw eG hfd hcont) Cd := by
  intro ψ hψe
  haveI := nzsdY (O := O) r χ E
  obtain ⟨φ, hφ⟩ := ext_of_baer (e := e) (eO := eO) heO (N := ↥(Ymod r χ E)) (Q := Cd.Ce.V ⧸ Cd.Ce.L.T)
    (div_quot heO Cd.Ce.L.T) (Cd.u.toAddMonoidHom.comp ψ.toAddMonoidHom)
    (fun a n => by
      show Cd.u (ψ (a • n)) = _
      rw [ψ.map_smul, Cd.u_smul]
      rfl)
  refine ⟨φ, ?_, ?_⟩
  · intro g y hy hp
    obtain ⟨⟨n, c0⟩, rfl⟩ := hy
    have hc0 : c0 = 0 := pY_zero (m := (n, c0)) hp
    subst hc0
    show φ (trY e (locRep (resRep (ytRep O r χ E) Dw) (eG.symm g) (mkK (n, (0 : O))))) =
      actD Cd.Ce.L g (φ (trY e (mkK (n, (0 : O)))))
    rw [locRep_mkK]
    show φ (trY e (mkK (ytRep O r χ E ((eG.symm g : ↥Dw) : GG) (n, (0 : O))))) = _
    rw [ytRep_zero, hφ, hφ]
    show Cd.u (ψ _) = _
    rw [hψe _ (eG.symm g).2 n, Cd.u_act (eG.symm g) (ψ n), MulEquiv.apply_symm_apply]
    rfl
  · intro γ
    show φ (trY e (locRep (resRep (ytRep O r χ E) Dw) (eG.symm (eG γ)) (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) -
        trY e (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) = _
    rw [MulEquiv.symm_apply_apply, locRep_mkK]
    show φ (trY e (mkK (ytRep O r χ E (γ : GG) ((0 : ↥(Ymod r χ E)), (1 : O)))) -
        trY e (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) = _
    rw [ytRep_e]
    have h3 : (mkK (O := O) (yY r χ E (γ : GG), (1 : O)) - mkK (O := O) ((0 : ↥(Ymod r χ E)), (1 : O)) :
          MK (O := O) (↥(Ymod r χ E) × O)) = mkK (O := O) (yY r χ E (γ : GG), (0 : O)) := by
      rw [← map_sub]
      congr 1
      ext <;> simp
    exact (congrArg φ h3).trans (hφ _)

theorem ytG_crys [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL Ow) {ιx : Type} {k : ℕ} (Ms : ιx → G →* Matrix (Fin k) (Fin k) LL)
    (hMc : ∀ x, Continuous (Ms x)) (hMs : ∀ x, IsCrys PD (matRep (Ms x))) {m : ℕ} (xs : Fin m → ιx)
    (φ : TrV e (MK (O := O) (↥(Ymod r χ E) × O)) →ₗ[LL] (Fin m → Fin k → LL)) (hφ : Function.Injective φ)
    (heq : ∀ g v, φ (ytVG (e := e) r χ E Dw eG g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) :
    IsCrys PD (ytG Qp heO r χ E Dw eG hfd hcont).ρ ∧
      ∀ τ a, IsJumpV PD (ytG Qp heO r χ E Dw eG hfd hcont).ρ τ a → ∃ x, IsJumpV PD (matRep (Ms x)) τ a := by
  let Ag : GRep G Qp LL Ow :=
    { V := TrV e (MK (O := O) (↥(Ymod r χ E) × O)), ρ := ytVG (e := e) r χ E Dw eG, cont := hcont }
  exact crys_of_inj PD Ms hF hMc hMs Ag xs φ hφ heq

end GenT

end Formalism.MainNotions.N.K.TBa

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.N.K.Topo

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem topoHyps
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (u : ℤ_[D.nd.l i]ˣ)
    (hcyc : ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) :
    letI := fracTopology (D.nd.O i); letI := rTopology (D.nd.O i) Dd.R';
    Function.Injective (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) ∧ PadicCoeff (D.nd.l i) (D.nd.O i) ∧
      FracTop (D.nd.O i) ∧ IsFGTop (D.nd.O i) Dd.R' ∧ IsCycG (D.nd.l i) (epsU D.nd i) ∧
      (Continuous fun g : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) => uElt Dd.r Dd.χ g) ∧
      (∀ v, IsPlaceOver (Formalism.MainNotions.N.K.Av (D := D) v) v) ∧
      (D.nd.l i ≠ 2 ∨ InfinitePlace.nrRealPlaces D.host.E = 0) ∧
      1 ≤ D.nd.s0 i ∧ (D.nd.l i = 2 → 2 ≤ D.nd.s0 i) ∧
      ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) - 1 =
        ((D.nd.l i : ℕ) : D.nd.O i) ^ D.nd.s0 i * ((yU i u : (D.nd.O i)ˣ) : D.nd.O i) ∧
      (∀ w ∈ Formalism.MainNotions.N.K.rowsN i dc, (Formalism.MainNotions.N.K.Aw i dc w).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 ∧
        IsPlaceOver (Formalism.MainNotions.N.K.Aw i dc w) (Formalism.MainNotions.N.K.plOf i dc w)) := by
  refine ⟨?_, padicCoeff_O i, fracTop_O i, fgTop_RD i r π g0 eB e₁ s Dd hD, ?_, uElt_cont i r π g0 eB e₁ s Dd hD hc,
    av_over, ?_, one_le_localLevel i, restNLevelExponent_of_two i, ?_, rows_over i dc⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 : algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((PadicInt.unitCoeff h0 : ℤ_[D.nd.l i]) * (D.nd.l i : ℤ_[D.nd.l i]) ^ x.valuation) = 0 := by
      rw [← PadicInt.unitCoeff_spec h0]
      exact hx
    rw [map_mul, map_pow, map_natCast] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))).ne_zero h
    · exact (padicCoeff_O i).p_ne (pow_eq_zero_iff'.mp h).1
  · apply isCyc_eps <;> assumption
  · apply l_or_noReal <;> assumption
  · have h2 : ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) := rfl
    rw [h2, hcyc]
    simp [yU]

end Formalism.MainNotions.N.K.Topo

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module

section Len

theorem len_comap_surj {O A B : Type} [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    (f : A →ₗ[O] B) (hf : Function.Surjective f) (Q P : Submodule O B) :
    Module.length O (↥(Q.comap f) ⧸ (P.comap f).comap (Q.comap f).subtype) =
      Module.length O (↥Q ⧸ P.comap Q.subtype) := by
  let q : ↥(Q.comap f) →ₗ[O] ↥Q ⧸ P.comap Q.subtype :=
    (P.comap Q.subtype).mkQ ∘ₗ LinearMap.codRestrict Q (f ∘ₗ (Q.comap f).subtype) (fun x => x.2)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨⟨a, hb⟩, rfl⟩
  have hk : LinearMap.ker q = (P.comap f).comap (Q.comap f).subtype := by
    ext x
    rw [LinearMap.mem_ker]
    exact Submodule.Quotient.mk_eq_zero _
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)).length_eq

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)] [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
  (Ψ : M →ₛₗ[(e : R →+* S)] N) (hinj : Function.Injective Ψ)
  (Q P : Submodule R M) (Q' P' : Submodule S N)
  (hQ : ∀ y, y ∈ Q' ↔ ∃ x : M, x ∈ Q ∧ Ψ x = y) (hP : ∀ x ∈ Q, x ∈ P ↔ Ψ x ∈ P')

def resQ : ↥Q →ₛₗ[(e : R →+* S)] ↥Q' where
  toFun x := ⟨Ψ (x : M), (hQ _).2 ⟨x, x.2, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add Ψ (a : M) (b : M))
  map_smul' c a := Subtype.ext (Ψ.map_smulₛₗ c (a : M))

include hinj in
theorem resQ_bij : Function.Bijective (resQ e Ψ Q Q' hQ) := by
  constructor
  · intro a b h
    have h' : Ψ (a : M) = Ψ (b : M) := congrArg Subtype.val h
    exact Subtype.ext (hinj h')
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (hQ y).1 hy
    exact ⟨⟨x, hx⟩, rfl⟩


include hinj hQ in
def resQE : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q' :=
  LinearEquiv.ofBijective (resQ e Ψ Q Q' hQ) (resQ_bij e Ψ hinj Q Q' hQ)

include hinj hQ in
theorem resQE_apply (x : ↥Q) : ((resQE e Ψ hinj Q Q' hQ x : ↥Q') : N) = Ψ (x : M) := rfl


include hinj hQ hP in
theorem len_semi :
    Module.length R (↥Q ⧸ P.comap Q.subtype) = Module.length S (↥Q' ⧸ P'.comap Q'.subtype) := by
  obtain ⟨E, hE⟩ : ∃ E : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q', ∀ x, ((E x : ↥Q') : N) = Ψ (x : M) :=
    ⟨resQE e Ψ hinj Q Q' hQ, resQE_apply e Ψ hinj Q Q' hQ⟩
  have hmap : (P.comap Q.subtype).map (E : ↥Q →ₛₗ[(e : R →+* S)] ↥Q') = P'.comap Q'.subtype := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hE]
      exact (hP x x.2).1 hx
    · intro hy
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hE] at hy
      exact ⟨x, (hP x x.2).2 hy, rfl⟩
  let F := Submodule.Quotient.equiv (P.comap Q.subtype) (P'.comap Q'.subtype) E hmap
  have h1 := Order.height_orderIso (Submodule.orderIsoMapComap F) ⊤
  rw [OrderIso.map_top] at h1
  rw [Module.length_eq_height, Module.length_eq_height]
  exact h1.symm

end Len

section Props

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
  (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
  (vD : ∀ w, T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
  (heD : ∀ w g t, vD w (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD w (π t)))

def imRow (w : ℕ) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 (Dat w).ρTl') :=
  (Hf₁ i dc ρ₁ w).map (gRow (Dat w) (resRep ρ₁ (Γn i dc w)) π (vD w) (hpD w) (heD w))

variable [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

def rowLenD (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (↥(Fs i dc VT VT' Dat w) ⧸
    (imRow i dc VT VT' Dat ρ₁ π vD hpD heD w).comap (Fs i dc VT VT' Dat w).subtype)

theorem heO_br {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap (Br.Ow (D.nbr i _ hn)) (Br.LLw (D.nbr i _ hn)) ((D.nbr i _ hn).eO a) =
      eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) := by
  change _ = Br.toLLK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a)
  rw [Br.toLLK, IsFractionRing.lift_algebraMap]
  rfl

def RowSub (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsSubOfSums (repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x)))

def RowOrb : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    ∀ x, Continuous fun g => repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn) g x

def RowMat (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (πx : D.nd.X i) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsMatLat (ρ := repL (eK (D.nbr i _ hn)) (Dat n).ρT' (Br.iota D.nbr i _ hn))
      (latT (eK (D.nbr i _ hn)) (D.nbr i _ hn).eO (Dat n).T'.subtype (heO_br i dc hn))
      (⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (T2O D.nd i ρ πx)))

def RowTop : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    (∀ c : ↥(Γn i dc n) → VT' n,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (c (Br.iota D.nbr i _ hn g))) → Continuous c) ∧
    (∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hn g)))) →
        Continuous c)

def RowFin : Prop :=
  Module.Finite (D.nd.O i) T₁ ∧ Module.Free (D.nd.O i) T₁ ∧
  ∀ n ∈ K.rowsN i dc, Module.Finite (D.nd.O i) (Dat n).T' ∧ Module.Free (D.nd.O i) (Dat n).T' ∧
    ∀ v : VT' n, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ t : (Dat n).T', (t : VT' n) = c • v

end Props

end Formalism.MainNotions.N.KRow

end
end
