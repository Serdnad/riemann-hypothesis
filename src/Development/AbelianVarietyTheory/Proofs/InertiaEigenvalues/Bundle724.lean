module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BlockCharactersCrystalline
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle712
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle697
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle521
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle708
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle709
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle631
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle710
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section

namespace GlobalTheory.UseLoc

theorem chiT_cont_isCrys_multV : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ), 1 ≤ c → c ≤ D.R.t → TruncatedSeriesCountingIdentities.admG2 i r ρ π → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1)) → IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1)) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) ∧ ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) τ (a + ((c : ℤ) - 1)) = multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ a := by
  intro D i r ρ π w hw C θ c h1 h2 hG2 hθc hθ
  set ψ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ := chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) with hψ
  have hsplit : ∀ g, ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
        ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
    intro g
    simp [tableLineDegreeTwo.charL, chiT, hψ]
  have hent : ∀ g, TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c) g 0 0 =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
    intro g
    change TruncatedSeriesCountingIdentities.CoefExt.inc C (algebraMap _ _ ((D.nbr i w hw).eO
      (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.BlockCharactersCrystallineNonGaloisCusps.chiRatO_apply]
    rfl
  let f : (Fin 1 → ↥C.LL.1) ≃ₗ[↥C.LL.1] ↥C.LL.1 := LinearEquiv.funUnique (Fin 1) ↥C.LL.1 ↥C.LL.1
  have hf : ∀ g x, f (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c)) g x) =
      Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ) g (f x) := by
    intro g x
    show (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c) g).mulVec x 0 =
      ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) • x 0
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_one, hent, smul_eq_mul]
  have cψ : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ)) :=
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ f hf (GlobalTheory.RestPtAssembly.chiRat_isCrys D i w hw C c h1 h2)
  have jψ : ∀ τ, IsJumpV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ)) τ ((c : ℤ) - 1) :=
    fun τ => GlobalTheory.HTW.isJumpV_of_injective _ _ _ f.toLinearMap f.injective hf τ _
      ((((hG2 w hw C).1.2.2.2.1 c h1 h2 τ ((c : ℤ) - 1))).2 rfl)
  have tw : IsTwistRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ))
      (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c))) := by
    refine ⟨LinearEquiv.refl _ _, fun g x => ?_⟩
    simp only [Formalism.WeaklyAdmissibleFiltrations.charRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply,
      LinearEquiv.refl_apply, smul_eq_mul, hsplit]
    ring
  obtain ⟨hcr, hm⟩ := GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL ↥C.LL.1 _ ↥C.LL.1 _ _ tw cψ hθ
  refine ⟨?_, hcr, fun τ a => hm τ a _ (jψ τ)⟩
  have hO : Continuous (fun h : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) h : (D.nd.O i)ˣ) : D.nd.O i)) := by
    have e : (fun h : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) h : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun h => ((D.nd.chi i c h : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i 1 h⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext h
      simp [chiU, map_inv]
    rw [e]
    exact (D.nd.chi_cont i c).mul ((D.nd.chi_cont i 1).comp continuous_inv)
  have hi : Continuous (IntermediateField.inclusion C.le) :=
    continuous_induced_rng.2 continuous_subtype_val
  have hψc : Continuous fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) :=
    hi.comp (continuous_subtype_val.comp ((D.nbr i w hw).eO_cont.comp
      (hO.comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)))))
  have e2 : (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g : (↥C.LL.1)ˣ) : ↥C.LL.1)) =
      fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) ψ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
        ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) := funext hsplit
  rw [e2]
  exact hψc.mul hθc

end GlobalTheory.UseLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.SplitLatIdx

theorem relIndex_map_of_proj {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X) (φ P : X →+ X)
    (pr : X →+ Y) (hK : ∀ x, pr x = 0 → P x = 0) (hPA : ∀ a ∈ A, P a ∈ A)
    (hφ : ∀ x, φ x - P (φ x) = x - P x) (hc : ∀ x, P (φ x) = φ (P x)) :
    (A.map φ).relIndex A = ((A.map φ).map pr).relIndex (A.map pr) := by
  rw [← AddSubgroup.relIndex_comap ((A.map φ).map pr) pr A, ← AddSubgroup.inf_relIndex_right (A.map φ) A,
    ← AddSubgroup.inf_relIndex_right (((A.map φ).map pr).comap pr) A]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨y, ⟨a, ha, rfl⟩, hy⟩, hx⟩
  refine ⟨⟨a + (x - φ a), ?_, ?_⟩, hx⟩
  · have hPz : P (x - φ a) = 0 := hK _ (by rw [map_sub, hy, sub_self])
    have hz : x - φ a = (x - P x) - (a - P a) := by
      calc x - φ a = (x - φ a) - P (x - φ a) := by rw [hPz, sub_zero]
        _ = (x - P x) - (φ a - P (φ a)) := by rw [map_sub]; abel
        _ = _ := by rw [hφ a]
    refine add_mem ha ?_
    rw [hz]
    exact sub_mem (sub_mem hx (hPA x hx)) (sub_mem ha (hPA a ha))
  · have hPz : P (x - φ a) = 0 := hK _ (by rw [map_sub, hy, sub_self])
    have h1 := hφ (x - φ a)
    simp only [hc, hPz, map_zero, sub_zero] at h1
    rw [map_add (f := _), h1]
    abel

end GlobalTheory.SplitLatIdx

namespace GlobalTheory.SplitLatIdx



theorem latIndex_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g * GlobalTheory.LocKerMod.idxAt T w' h' g := by
  intro D T v w w' h h' hv hne g
  classical
  obtain ⟨w'', -, hu, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place (isCMExt_host D) h hv
  have hover : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v → u = w ∨ u = w' := by
    intro u hu0
    rcases (hu u).1 hu0 with e | e
    · exact Or.inl e
    · rcases (hu w').1 h' with e' | e'
      · exact absurd e'.symm hne
      · exact Or.inr (e.trans e'.symm)
  set M := finMat D.sp.cm.sig T.gram (GlobalTheory.FinZeta.embV T v g) with hMdef
  have hcomp : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (y : Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (i : Fin T.rank),
      GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ y) i) = (M.map (GlobalTheory.LFun.compAt D.host.F u) *ᵥ fun j => GlobalTheory.LFun.compAt D.host.F u (y j)) i :=
    fun u y i => RingHom.map_mulVec _ M y i
  have hMw : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (hh : u.under (𝓞 D.host.F) = v),
      M.map (GlobalTheory.LFun.compAt D.host.F u) = (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram hh g).1 := by
    intro u hh
    have e := GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram hh (GlobalTheory.FinZeta.embV T v g)
    rw [proj_emb_self] at e
    exact e
  have hMu : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) ≠ v → M.map (GlobalTheory.LFun.compAt D.host.F u) = 1 := by
    intro u hh
    have e := GlobalTheory.LFun.finMat_map_compAt D.sp.cm.sig T.gram (rfl : u.under (𝓞 D.host.F) = _) (GlobalTheory.FinZeta.embV T v g)
    rw [proj_emb_ne _ _ hh, map_one, Units.val_one] at e
    exact e
  set ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E := GlobalTheory.LFun.singleAt D.host.F w 1 + GlobalTheory.LFun.singleAt D.host.F w' 1 with hεdef
  have hεw : GlobalTheory.LFun.compAt D.host.F w ε = 1 := by
    rw [hεdef, map_add (f := _), GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]
  have hεw' : GlobalTheory.LFun.compAt D.host.F w' ε = 1 := by
    rw [hεdef, map_add (f := _), GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]
  have hεu : ∀ u, u ≠ w → u ≠ w' → GlobalTheory.LFun.compAt D.host.F u ε = 0 := by
    intro u h1 h2
    rw [hεdef, map_add (f := _), GlobalTheory.LFun.compAt_singleAt_ne h1, GlobalTheory.LFun.compAt_singleAt_ne h2, add_zero]
  have hεint : ε ∈ intAE D :=
    add_mem (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _)) (GlobalTheory.LFun.singleAt_mem_intAE (one_mem _))
  let pr : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin T.rank → w.adicCompletion D.host.E) × (Fin T.rank → w'.adicCompletion D.host.E) :=
    AddMonoidHom.mk' (fun x => (fun i => GlobalTheory.LFun.compAt D.host.F w (x i), fun i => GlobalTheory.LFun.compAt D.host.F w' (x i)))
      (fun x y => by ext i <;> simp)
  let P : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun x i => ε * x i) (fun x y => by funext i; simp [mul_add])
  let φ := M.mulVecLin.toAddMonoidHom
  have hφa : ∀ x, φ x = M *ᵥ x := fun x => rfl
  have hK : ∀ x, pr x = 0 → P x = 0 := by
    intro x hx
    have h1 : ∀ i, GlobalTheory.LFun.compAt D.host.F w (x i) = 0 := fun i => congrFun (congrArg Prod.fst hx) i
    have h2 : ∀ i, GlobalTheory.LFun.compAt D.host.F w' (x i) = 0 := fun i => congrFun (congrArg Prod.snd hx) i
    funext i
    refine GlobalTheory.LFun.compAt_ext fun u => ?_
    show GlobalTheory.LFun.compAt D.host.F u (ε * x i) = GlobalTheory.LFun.compAt D.host.F u 0
    rw [map_mul, map_zero]
    by_cases e1 : u = w
    · subst e1; rw [h1 i, mul_zero]
    by_cases e2 : u = w'
    · subst e2; rw [h2 i, mul_zero]
    rw [hεu u e1 e2, zero_mul]
  have hPA : ∀ a ∈ Formalism.L2.NTheta.LamHat T, P a ∈ Formalism.L2.NTheta.LamHat T :=
    fun a ha => (GlobalTheory.LatDual.lamHat_selfDual_and_module T).2 ε hεint a ha
  have hφ : ∀ x, φ x - P (φ x) = x - P x := by
    intro x
    funext i
    refine GlobalTheory.LFun.compAt_ext fun u => ?_
    show GlobalTheory.LFun.compAt D.host.F u ((M *ᵥ x) i - ε * (M *ᵥ x) i) = GlobalTheory.LFun.compAt D.host.F u (x i - ε * x i)
    rw [map_sub, map_sub, map_mul, map_mul]
    by_cases e : u = w ∨ u = w'
    · have : GlobalTheory.LFun.compAt D.host.F u ε = 1 := by rcases e with rfl | rfl; exacts [hεw, hεw']
      rw [this, one_mul, one_mul, sub_self, sub_self]
    · push_neg at e
      have hv' : u.under (𝓞 D.host.F) ≠ v := fun hh => by rcases hover u hh with e' | e' <;> [exact e.1 e'; exact e.2 e']
      rw [hεu u e.1 e.2, zero_mul, zero_mul, hcomp, hMu u hv', Matrix.one_mulVec]
  have hc : ∀ x, P (φ x) = φ (P x) := by
    intro x
    show (fun i => ε * (M *ᵥ x) i) = M *ᵥ (fun j => ε * x j)
    have e : (fun j => ε * x j) = ε • x := rfl
    rw [e, Matrix.mulVec_smul]
    rfl
  have hprφ : ∀ y, pr (φ y) = ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w (y i),
      (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' g).1 *ᵥ fun i => GlobalTheory.LFun.compAt D.host.F w' (y i)) := by
    intro y
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show GlobalTheory.LFun.compAt D.host.F w ((M *ᵥ y) i) = _
      rw [hcomp, hMw w h]
    · show GlobalTheory.LFun.compAt D.host.F w' ((M *ᵥ y) i) = _
      rw [hcomp, hMw w' h']
  have hsg : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E),
      pr (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = (x, x') := by
    intro x x'
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show GlobalTheory.LFun.compAt D.host.F w (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x i
      rw [map_add (f := _), GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne hne, add_zero]
    · show GlobalTheory.LFun.compAt D.host.F w' (GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) = x' i
      rw [map_add (f := _), GlobalTheory.LFun.compAt_singleAt, GlobalTheory.LFun.compAt_singleAt_ne (Ne.symm hne), zero_add]
  have hsgm : ∀ (x : Fin T.rank → w.adicCompletion D.host.E) (x' : Fin T.rank → w'.adicCompletion D.host.E),
      x ∈ GlobalTheory.LFun.latAt w (frameLat T) → x' ∈ GlobalTheory.LFun.latAt w' (frameLat T) →
      (fun i => GlobalTheory.LFun.singleAt D.host.F w (x i) + GlobalTheory.LFun.singleAt D.host.F w' (x' i)) ∈ Formalism.L2.NTheta.LamHat T :=
    fun x x' hx hx' => add_mem (GlobalTheory.LFun.singleAt_mem_lamHat hx) (GlobalTheory.LFun.singleAt_mem_lamHat hx')
  have hmem : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) y, y ∈ Formalism.L2.NTheta.LamHat T →
      (fun i => GlobalTheory.LFun.compAt D.host.F u (y i)) ∈ GlobalTheory.LFun.latAt u (frameLat T) :=
    fun u y hy => GlobalTheory.LFun.compAt_mem_latAt u (hermitianSpaceBaseLattice_eq_frameLattice T ▸ hy)
  have hA : (Formalism.L2.NTheta.LamHat T).map pr =
      (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.prod (GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup := by
    ext ⟨x, x'⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have e1 : (fun i => GlobalTheory.LFun.compAt D.host.F w (y i)) = x := congrArg Prod.fst hxy
      have e2 : (fun i => GlobalTheory.LFun.compAt D.host.F w' (y i)) = x' := congrArg Prod.snd hxy
      subst e1 e2
      exact ⟨hmem w y hy, hmem w' y hy⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨_, hsgm x x' hx hx', hsg x x'⟩
  have hB : ((Formalism.L2.NTheta.LamHat T).map φ).map pr =
      ((GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.map
        (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).prod
      ((GlobalTheory.LFun.latAt w' (frameLat T)).toAddSubgroup.map
        (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' g).1.mulVecLin.toAddMonoidHom) := by
    ext ⟨x, x'⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, hxy⟩
      rw [hprφ] at hxy
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
      exact ⟨⟨_, hmem w a ha, rfl⟩, ⟨_, hmem w' a ha, rfl⟩⟩
    · rintro ⟨⟨b, hb, rfl⟩, ⟨b', hb', rfl⟩⟩
      refine ⟨φ _, ⟨_, hsgm b b' hb hb', rfl⟩, ?_⟩
      rw [hprφ]
      have e := hsg b b'
      simp only [pr, AddMonoidHom.mk'_apply, Prod.mk.injEq] at e
      rw [e.1, e.2]
      rfl
  show ((Formalism.L2.NTheta.LamHat T).map φ).relIndex (Formalism.L2.NTheta.LamHat T) = _
  rw [relIndex_map_of_proj _ φ P pr hK hPA hφ hc, hA, hB, GlobalTheory.BorelUMod.relIndex_prod_prod]
  rfl

end GlobalTheory.SplitLatIdx
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.LocKerMod

theorem relIndex_map_of_proj_left {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X)
    (φ P : X →+ X) (M : X →+ Y) (m : Y →+ Y) (hM : ∀ x, M (φ x) = m (M x)) (hK : ∀ x, M x = 0 → P x = 0)
    (hMP : ∀ x, M (P x) = M x) (hPA : ∀ a ∈ A, P a ∈ A) (hφ : ∀ a ∈ A, φ a - P (φ a) = a - P a) :
    (A.map φ).relIndex A = ((A.map M).map m).relIndex (A.map M) := by
  have e1 : (A.map M).map m = (A.map φ).map M := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun x => (hM x).symm
  rw [e1, ← AddSubgroup.relIndex_comap (H := (A.map φ).map M) M A, ← AddSubgroup.inf_relIndex_right (A.map φ),
    ← AddSubgroup.inf_relIndex_right (((A.map φ).map M).comap M)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨z, ⟨y, hy, rfl⟩, hzx⟩, hx⟩
  refine ⟨?_, hx⟩
  have h1 : P (φ y) = P x := by
    have := hK (φ y - x) (by rw [map_sub, hzx, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  have hy' : (x - P x) + P y ∈ A := add_mem (sub_mem hx (hPA x hx)) (hPA y hy)
  have hMy : M ((x - P x) + P y - y) = 0 := by
    rw [map_sub, map_add (f := _), map_sub, hMP, hMP]; abel
  have h2 : P ((x - P x) + P y) = P y := by
    have := hK _ hMy
    rwa [map_sub, sub_eq_zero] at this
  have h3 : P (φ ((x - P x) + P y)) = P (φ y) := by
    have := hK (φ ((x - P x) + P y) - φ y) (by rw [← map_sub, hM, hMy, map_zero])
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨(x - P x) + P y, hy', ?_⟩
  calc φ ((x - P x) + P y) = (φ ((x - P x) + P y) - P (φ ((x - P x) + P y))) + P (φ ((x - P x) + P y)) := by abel
    _ = ((x - P x) + P y - P ((x - P x) + P y)) + P (φ y) := by rw [hφ _ hy', h3]
    _ = x := by rw [h2, h1]; abel

end GlobalTheory.LocKerMod



open GlobalTheory.LFun in
theorem GlobalTheory.LocKerMod.latIndex_embV_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w →
    ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g := by
  intro D T v w h hi g
  let φ : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finMat D.sp.cm.sig T.gram (GlobalTheory.FinZeta.embV T v g)).mulVecLin.toAddMonoidHom
  let P : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    AddMonoidHom.mk' (fun y i => singleAt D.host.F w 1 * y i) fun a b => funext fun i => mul_add _ _ _
  let M : (Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin T.rank → w.adicCompletion D.host.E) :=
    AddMonoidHom.mk' (fun y i => compAt D.host.F w (y i)) fun a b => funext fun i => map_add _ _ _
  let m : (Fin T.rank → w.adicCompletion D.host.E) →+ (Fin T.rank → w.adicCompletion D.host.E) :=
    (locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom
  have hcomp : ∀ (u : HeightOneSpectrum (𝓞 D.host.E)) (x : Fin T.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) i,
      compAt D.host.F u (φ x i) = ((locMat D.sp.cm.sig T.gram (rfl : u.under (𝓞 D.host.F) = _)
        (proj D.sp.cm.sig T.gram (u.under (𝓞 D.host.F)) (GlobalTheory.FinZeta.embV T v g))).1 *ᵥ
          fun j => compAt D.host.F u (x j)) i := by
    intro u x i
    rw [← finMat_map_compAt D.sp.cm.sig T.gram rfl]
    exact RingHom.map_mulVec (compAt D.host.F u) _ x i
  have hM : ∀ x, M (φ x) = m (M x) := by
    intro x
    funext i
    have := hcomp w x i
    subst h
    rw [proj_emb_self] at this
    exact this
  have hK : ∀ x, M x = 0 → P x = 0 := by
    intro x hx
    funext i
    have h0 : compAt D.host.F w (x i) = 0 := congrFun hx i
    show singleAt D.host.F w 1 * x i = 0
    rw [singleAt_mul, h0, mul_zero, singleAt_zero]
  have hMP : ∀ x, M (P x) = M x := by
    intro x
    funext i
    show compAt D.host.F w (singleAt D.host.F w 1 * x i) = compAt D.host.F w (x i)
    rw [map_mul, compAt_singleAt, one_mul]
  have hPA : ∀ a ∈ Formalism.L2.NTheta.LamHat T, P a ∈ Formalism.L2.NTheta.LamHat T := by
    intro a ha
    have e : P a = fun i => singleAt D.host.F w (compAt D.host.F w (a i)) := by
      funext i
      show singleAt D.host.F w 1 * a i = _
      rw [singleAt_mul, one_mul]
    rw [e]
    exact singleAt_mem_lamHat (compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice T ▸ ha))
  have hφ : ∀ a ∈ Formalism.L2.NTheta.LamHat T, φ a - P (φ a) = a - P a := by
    intro a _
    funext i
    show φ a i - singleAt D.host.F w 1 * φ a i = a i - singleAt D.host.F w 1 * a i
    refine compAt_ext fun u => ?_
    by_cases e : u = w
    · subst e
      simp only [map_sub, map_mul, compAt_singleAt, one_mul, sub_self]
    · have hu : u.under (𝓞 D.host.F) ≠ v := fun hu => e ((InertChart.under_eq_iff hi u).1 hu)
      simp only [map_sub, map_mul, compAt_singleAt_ne e, zero_mul, sub_zero]
      rw [hcomp u a i, GlobalTheory.FinZeta.embV, proj_emb_ne _ _ hu, map_one, Units.val_one, Matrix.one_mulVec]
  have hLM : (Formalism.L2.NTheta.LamHat T).map M = (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup := by
    ext y
    rw [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      show (fun i => compAt D.host.F w (a i)) ∈ GlobalTheory.LFun.latAt w (frameLat T)
      exact compAt_mem_latAt w (hermitianSpaceBaseLattice_eq_frameLattice T ▸ ha)
    · intro hy
      refine ⟨_, singleAt_mem_lamHat hy, ?_⟩
      funext i
      exact compAt_singleAt w (y i)
  unfold latIndex idxAt
  rw [relIndex_map_of_proj_left _ φ P M m hM hK hMP hPA hφ, hLM]
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.isAdicComplete_dividedPowerSeriesSubring_prime : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  first | exact @GlobalTheory.CrysPrism.isAdicComplete_Sd | exact GlobalTheory.CrysPrism.isAdicComplete_Sd | (intros; apply GlobalTheory.CrysPrism.isAdicComplete_Sd <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, (frobTot K a l) F ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e, (frobTot K a l) F = F ^ l + (l : ZMod a → K⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.frob_sd_congr | exact GlobalTheory.CrysPrism.frob_sd_congr | (intros; apply GlobalTheory.CrysPrism.frob_sd_congr <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.isAdicComplete_dividedTwoVariableSubring : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(PPd t K e))}) ↥(PPd t K e) := by
  first | exact @GlobalTheory.CrysPrism.PPd_isAdicComplete | exact GlobalTheory.CrysPrism.PPd_isAdicComplete | (intros; apply GlobalTheory.CrysPrism.PPd_isAdicComplete <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal


theorem _root_.GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K] (C : GlobalTheory.MemLoc.Core l) (η : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, ∃ r ∈ Rpi O K l e, (f τ : K⟦X⟧) = E K l e ^ η * r) → ∃ z : OD l O, iotaO O C (ϖ.iB t K f) = dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ η * z) := by
  first | exact @GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul | exact GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul | (intros; apply GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul <;> assumption)
end
