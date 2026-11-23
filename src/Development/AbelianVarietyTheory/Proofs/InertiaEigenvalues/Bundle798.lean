module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle047
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernel
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle785
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle728
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle593
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle786
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCompat

theorem compAt_eq_zero_of_proj_eq_zero {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (z : AL L) (hp : s.proj z = 0) (hq : s.proj (conjAL L z) = 0) : compAt L s.v z = 0 := by
  obtain ⟨e, hne⟩ : ∃ e : L, e ≠ IsCMField.complexConj L e := by
    by_contra hcon
    push Not at hcon
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext fun x => (hcon x).symm)
  have hli : LinearIndependent (maximalRealSubfield L) ![(1 : L), e] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add (f := _), map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap (maximalRealSubfield L) L t * (e - IsCMField.complexConj L e) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank (maximalRealSubfield L) L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = e := by simp [b]
  obtain ⟨A, B, hAB⟩ := GlobalTheory.tensor_exists_decomp b z
  rw [hb0, hb1] at hAB
  have h1 : s.proj z = A s.v + s.i e * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]
    rfl
  have h2 : s.proj (ReciprocityTheory.Aut.conjAL L z) =
      A s.v + s.i (IsCMField.complexConj L e) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  have hu : s.i e - s.i (IsCMField.complexConj L e) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hne (s.i.toRingHom.injective h)
  have hBv : B s.v = 0 := by
    have hm : (s.i e - s.i (IsCMField.complexConj L e)) * B s.v =
        s.proj z - s.proj (ReciprocityTheory.Aut.conjAL L z) := by
      rw [h1, h2]; ring
    rw [hp, hq, sub_zero] at hm
    exact (mul_eq_zero.1 hm).resolve_left hu
  have hAv : A s.v = 0 := by
    rw [hp, hBv, mul_zero, add_zero] at h1
    exact h1.symm
  rw [hAB]
  have hA' : evalAt L s.v A = 0 := by rw [← hAv]; rfl
  have hB' : evalAt L s.v B = 0 := by rw [← hBv]; rfl
  simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul, hA', hB']

theorem compAt_map_eq_of_loc_eq : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    (x y : GAf L n), s.loc n x = s.loc n y →
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) =
        (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) := by
  intro L _ _ _ n s x y h
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply]
  rw [← sub_eq_zero, ← map_sub]
  apply compAt_eq_zero_of_proj_eq_zero s
  · rw [map_sub, GlobalTheory.SplitLocEq.proj_entry, GlobalTheory.SplitLocEq.proj_entry, h, sub_self]
  · rw [map_sub, map_sub, GlobalTheory.SplitLocEq.conj_entry, GlobalTheory.SplitLocEq.conj_entry, GlobalTheory.SplitLocEq.proj_entry,
      GlobalTheory.SplitLocEq.proj_entry, map_inv, map_inv, h, sub_self]

end GlobalTheory.SplitCompat
end

section

set_option autoImplicit false

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum Formalism.IndefR.Lift

noncomputable section

namespace GlobalTheory.SplitChange

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW ν : (AE D)ˣ →* Circle}
  {om om' : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem resEta_zero_of_triv {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hF : ∀ a, ν (idF D a) = 1) :
    ResEta D ν 0 :=
  ⟨h.1, fun η _ a => by rw [hF, pow_zero]⟩

theorem exists_twist_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g x y, IsDetRoot V h x → IsDetRoot W g y →
      om' (h, g) = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ ho.std V W χV χW ν ν om ho hν hν
    (resEta_zero_of_triv ho.resS hF) (resEta_zero_of_triv ho.resS hF)
  refine ⟨o, h1, fun h g x y hx hy => ?_⟩
  rw [h2 h g x y hx hy, Circle.coe_mul, Circle.coe_inv, mul_comm]

theorem twist_eq_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {h : GA D V} {g : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V h x) (hy : IsDetRoot W g y) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) f := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  calc
    om' (h, g) f = o (h, g) f :=
      GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W _ _ om' o ho' h1 (h, g) f hf
    _ = _ := by rw [h2 h g x y hx hy, LinearMap.smul_apply]

theorem exists_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV) (hW : MuVal W ν nW) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  refine ⟨o, h1, fun h g => ?_⟩
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [h2 h g x y hx hy, hV.2 h x hx, hW.2 g y hy]

theorem twist_eq (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f := by
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [twist_eq_root ho hν hF ho' hx hy hf, hV.2 h x hx, hW.2 g y hy]

theorem thetaKO_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    thetaKO om' h g f = nW g * (nV h)⁻¹ * thetaKO om h g f := by
  unfold thetaKO
  rw [twist_eq ho hν hF ho' hV hW h g hf, Pi.smul_apply, smul_eq_mul]

theorem chrTh_tup {C : Type*} [CommGroup C] (μ : ℕ → C) (η ν : C) (j : ℕ) :
    chrTh (_root_.Formalism.IndefR.Lift.tup μ ν) η j = ((chrTh μ η j).1 * ν, (chrTh μ η j).2 * ν) := by
  unfold chrTh _root_.Formalism.IndefR.Lift.tup
  rw [mul_right_comm]

theorem change_of_splitting_pair (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW ν : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν)
    (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W χV χW om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  refine ⟨?_, fun nV nW hV hW => ⟨exists_twist ho hν hF hV hW, fun om' ho' h g f hf => twist_eq ho hν hF ho' hV hW h g hf⟩,
    fun om₁ h1 => GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W χV χW om₁ om h1 ho⟩
  obtain ⟨nV, hV, -⟩ := GlobalTheory.Member.exists_muVal D V ν hν hF
  obtain ⟨nW, hW, -⟩ := GlobalTheory.Member.exists_muVal D W ν hν hF
  exact ⟨nV, nW, hV, hW⟩

theorem change_of_splitting (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : ℕ → (AE D)ˣ →* Circle)
    (η ν : (AE D)ˣ →* Circle) (j : ℕ) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (ho : IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (chrTh (_root_.Formalism.IndefR.Lift.tup μ ν) η j).1 (chrTh (_root_.Formalism.IndefR.Lift.tup μ ν) η j).2 om' ∧
        ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (chrTh (_root_.Formalism.IndefR.Lift.tup μ ν) η j).1 (chrTh (_root_.Formalism.IndefR.Lift.tup μ ν) η j).2 om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  rw [chrTh_tup]
  exact change_of_splitting_pair D ψ V W _ _ ν om ho hν hF

end GlobalTheory.SplitChange

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.EigPlace

theorem finite_and_mem (hstd : HeckeStdPlain) {D : D7} {M : MtFam D} (HT : HeckeTied D M) (av : AVTied D M)
    (T : NormalizedLocalCompatibility D M) (i : D.nd.Loc) (x : D.nd.X i) (Q : Finset (PlE D.host)) (hQ : D.nd.Q i = Q) :
    (EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q).Finite ∧
      ptSys D i x ∈ EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q := by
  subst hQ
  have hi : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.EigFinite.eigSet_finite hstd D _ _ _ _ _ (badPl D i) ?_ ?_
    · exact hypOutside_transport (D.nd.mu_w i) rfl (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ _ (HT.J_hyp i)
    · intro v k s hg hc
      rw [T.Q_eq _ _ i hi] at hg
      exact genOutBad_of T _ _ i hi v k s hg hc
  · rw [D.nd.w_l i]
    exact GlobalTheory.FitHecke.mt_transport M (fun μ j m => ptSys D i x ∈ EigSet m (D.nd.l i) (D.nd.Q i)) (D.nd.mu_w i) rfl
      (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ (GlobalTheory.PointEigen.ptSys_mem_eigSet D M av i x)


end GlobalTheory.EigPlace

end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.defect_torsion_second_cohomology_kernel : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Pr2d D HW F := by
  first | exact @GlobalTheory.NL.DefectTorsion.defect_torsion | exact GlobalTheory.NL.DefectTorsion.defect_torsion | (intros; apply GlobalTheory.NL.DefectTorsion.defect_torsion <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.CrysCharJumps

open Classical

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l)

def HasJumps (χ : ↥(GK K) →* (↥(OL LL))ˣ) (f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ) : Prop :=
  Continuous (fun g => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ g : (↥LL.1)ˣ) : ↥LL.1)) ∧
    IsCrys (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) ∧
    ∀ τ b, multV (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) τ b = if b = f τ then 1 else 0

variable {P K LL}

theorem charL_val (χ : ↥(GK K) →* (↥(OL LL))ˣ) (g : ↥(GK K)) :
    ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ g : (↥LL.1)ˣ) : ↥LL.1) =
      algebraMap ↥(OL LL) ↥LL.1 ((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) := rfl

theorem isJumpV_of_multV_ne {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ) (h : multV (P.PD K) ρ τ b ≠ 0) :
    IsJumpV (P.PD K) ρ τ b := by
  intro he
  apply h
  unfold multV
  rw [he]
  simp

theorem hasJumps_one (hT : LocTied l P AI) : HasJumps P K LL 1 0 := by
  have hc : Continuous (fun g => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (1 : ↥(GK K) →* (↥(OL LL))ˣ) g : (↥LL.1)ˣ) : ↥LL.1)) := by
    simp only [charL_val, MonoidHom.one_apply, Units.val_one, map_one]
    exact continuous_const
  obtain ⟨h1, h2⟩ := GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero l P AI hT K LL (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) 1) hc
    (fun g _ => by ext; simp [charL_val])
  exact ⟨hc, h1, fun τ b => by rw [h2]; rfl⟩

theorem hasJumps_mul (hT : LocTied l P AI) {χ ψ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f g : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) (hψ : HasJumps P K LL ψ g) :
    HasJumps P K LL (χ * ψ) (f + g) := by
  have htw : IsTwistRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)
      (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ)) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ))) := by
    refine ⟨LinearEquiv.refl _ _, fun x y => ?_⟩
    simp [charRep, charL_val, mul_smul]
  obtain ⟨hc, hm⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l P AI hT K LL ↥LL.1
    (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ)) ↥LL.1
    (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ))) (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ) htw hχ.2.1 hψ.2.1
  refine ⟨?_, hc, fun τ b => ?_⟩
  · have : (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) (χ * ψ) x : (↥LL.1)ˣ) : ↥LL.1)) =
        fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ x : (↥LL.1)ˣ) : ↥LL.1) *
          ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) ψ x : (↥LL.1)ˣ) : ↥LL.1) := by
      funext x
      simp [charL_val]
    rw [this]
    exact hχ.1.mul hψ.1
  · have hj : IsJumpV (P.PD K) (charRep (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)) τ (f τ) :=
      isJumpV_of_multV_ne _ τ (f τ) (by rw [hχ.2.2]; simp)
    have := hm τ (b - f τ) (f τ) hj
    rw [sub_add_cancel] at this
    rw [this, hψ.2.2]
    simp only [Pi.add_apply]
    split_ifs <;> omega

theorem hasJumps_inv (hT : LocTied l P AI) {χ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) :
    HasJumps P K LL χ⁻¹ (-f) := by
  have he : Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ⁻¹ = (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ)⁻¹ := by
    refine MonoidHom.ext fun x => ?_
    simp only [Formalism.MainNotions.tableLineDegreeTwo.charL, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isCrys_inv_and_hodgeTate_jumps_neg l P AI hT K LL (Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ) f hχ.2.1 hχ.2.2
  refine ⟨?_, he ▸ h1, fun τ b => by rw [he, h2]; rfl⟩
  have : (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ⁻¹ x : (↥LL.1)ˣ) : ↥LL.1)) =
      (fun x => ((Formalism.MainNotions.tableLineDegreeTwo.charL (LL := ↥LL.1) χ x : (↥LL.1)ˣ) : ↥LL.1)) ∘ (fun x => x⁻¹) := by
    funext x
    simp only [Function.comp_apply, charL_val, MonoidHom.inv_apply, map_inv]
  rw [this]
  exact hχ.1.comp continuous_inv

theorem hasJumps_zpow (hT : LocTied l P AI) {χ : ↥(GK K) →* (↥(OL LL))ˣ}
    {f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ} (hχ : HasJumps P K LL χ f) (k : ℤ) :
    HasJumps P K LL (χ ^ k) (k • f) := by
  induction k using Int.induction_on with
  | zero =>
    rw [zpow_zero, zero_smul]
    exact hasJumps_one AI hT
  | succ k ih =>
    rw [zpow_add_one, add_smul, one_smul]
    exact hasJumps_mul AI hT ih hχ
  | pred k ih =>
    rw [zpow_sub_one, sub_smul, one_smul, sub_eq_add_neg]
    exact hasJumps_mul AI hT ih (hasJumps_inv AI hT hχ)

theorem hasJumps_prod (hT : LocTied l P AI)
    (ψ : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → (↥(GK K) →* (↥(OL LL))ˣ))
    (hψ : ∀ τ₀, HasJumps P K LL (ψ τ₀) (fun τ => if τ = τ₀ then 1 else 0))
    (c : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ) (s : Finset (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) :
    HasJumps P K LL (∏ τ ∈ s, ψ τ ^ c τ) (fun τ => if τ ∈ s then c τ else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    convert hasJumps_one AI hT using 1
    funext τ
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    convert hasJumps_mul AI hT (hasJumps_zpow AI hT (hψ a) (c a)) ih using 1
    funext τ
    by_cases h : τ = a
    · subst h
      simp [ha]
    · simp [h]

end GlobalTheory.CrysCharJumps


open GlobalTheory.CrysCharJumps Classical in
theorem GlobalTheory.CrysCharJumps.adm20_of_fonOf :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.tableLineDegreeTwo.adm20 D HW F := by
  intro D HW F l _ K LL hA
  refine ⟨fun a => ?_, ?_⟩
  · classical
    choose ψ hψ using fun τ₀ => GlobalTheory.T.exists_crystalline_char_jump_one_alt l (D.loc l) (D.locA l) (D.locT l) K LL hA τ₀
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    haveI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    let c : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ := fun τ =>
      if h : ∃ i, Formalism.MainNotions.tableLineDegreeTwo.Over ((HW l).W K 1 LL hA.2.2).emb i τ then a h.choose else 0
    have hp := hasJumps_prod (D.locA l) (D.locT l) ψ (fun τ₀ => hψ τ₀) c Finset.univ
    refine ⟨∏ τ, ψ τ ^ c τ, hp.1, hp.2.1, fun i τ hi b => ?_⟩
    rw [hp.2.2]
    have hex : ∃ i, Formalism.MainNotions.tableLineDegreeTwo.Over ((HW l).W K 1 LL hA.2.2).emb i τ := ⟨i, hi⟩
    have hc : c τ = a i := by
      simp only [c, dif_pos hex]
      congr 1
      apply ((HW l).W K 1 LL hA.2.2).emb_bij.1
      have h1 := hex.choose_spec
      unfold Formalism.MainNotions.tableLineDegreeTwo.Over at h1 hi
      exact h1.symm.trans hi
    simp [hc]
  · intro V _ _ _ _ _ _ _ ρ ρ' μ hρc hρ hμc hμI hρ'
    obtain ⟨hμcr, hμm⟩ := GlobalTheory.T.unramifiedChar_isCrystalline_hodgeTate_zero l (D.loc l) (D.locA l) (D.locT l) K LL μ hμc hμI
    have htw : IsTwistRep μ ρ ρ' := ⟨LinearEquiv.refl _ _, fun g x => by simp [hρ' g]⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) (D.locT l) K LL
      V ρ V ρ' μ htw hμcr hρ
    refine ⟨h1, fun τ x => ?_⟩
    have hj : IsJumpV ((D.loc l).PD K) (charRep μ) τ 0 :=
      isJumpV_of_multV_ne _ τ 0 (by rw [hμm]; simp)
    simpa using h2 τ x 0 hj
end

section


theorem _root_.GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.Core := by
  first | exact @GlobalTheory.langRecCore_of_artinReciprocity | exact GlobalTheory.langRecCore_of_artinReciprocity | (intros; apply GlobalTheory.langRecCore_of_artinReciprocity <;> assumption)
end
