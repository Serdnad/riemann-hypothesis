module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle525
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle497
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle313
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFinPartILocFEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section
namespace GlobalTheory.RatioConst


open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont Formalism.L2.Pj in
theorem rcoef_one_const {D : D7} {A : HSp D} (m : Measure (GA D A)) (g : GA D A) :
    GlobalTheory.Core.Rk.IP.rcoef m (fun _ => (1 : ℂ)) (fun _ => 1) g = (volQ A m : ℂ) := by
  simp [GlobalTheory.Core.Rk.IP.rcoef, petersson, pet, rTr, AutomorphicL2Unitary.descend, volQ, autMeasure, integral_const]

theorem integral_const_coef : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  IsSelfDualC X.A (stdLat X.A) → (∀ x, x ∈ intG D P.a ↔ X.ιA x ∈ openOff X.A (stdLat X.A) ∅) →
  ∀ (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), GlobalTheory.Doubling.IsMaj X.A a →
  ∀ (Sf : Finset (FinPl D)) (Φ : WO X.A X.B → ℂ) (c : ℂ),
    (∀ x ∈ intG D P.a, ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = c) →
    (∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = 0) →
    (∀ s : ℂ, IntegrableOn (integrand X.om X.m ν 𝓕 (stdLat X.A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff X.A (stdLat X.A) Sf) X.m) ∧
      ∫ g in openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g ∂X.m = c := by
  intro D cc δ t0 Q P X hX hL hint a ν 𝓕 ha Sf Φ c hc h0
  have hF := hX.1
  haveI := hF.haarA
  set K : Set (GA D X.A) := openOff X.A (stdLat X.A) ∅ with hKdef
  have hdec : ∀ g : GA D X.A, ∃ x k, k ∈ GinfC X.A ∧ g = X.ιA x * k := by
    intro g
    obtain ⟨h, hh, k, hk, rfl⟩ := Formalism.IndefR.TopMult.ga_decomp g
    rw [← hF.rangeA] at hh
    obtain ⟨x, rfl⟩ := hh
    exact ⟨x, k, hk, rfl⟩
  have hproj : ∀ k ∈ GinfC X.A, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v k = 1 := by
    intro k hk v
    show GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v ((⟨k, hk⟩ : GinfC X.A) : GA D X.A) = 1
    rw [← GlobalTheory.AutMult.toInf_coe (⟨k, hk⟩ : GinfC X.A)]
    exact GlobalTheory.AdelicU.proj_ofInf _ _ v _
  have hfin : ∀ k ∈ GinfC X.A, Lev.finE X.A k = 1 := by
    intro k hk
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom X.A k = 1 from hk, map_one]
  have hmem : ∀ x k S, k ∈ GinfC X.A →
      (X.ιA x * k ∈ openOff X.A (stdLat X.A) S ↔ X.ιA x ∈ openOff X.A (stdLat X.A) S) := by
    intro x k S hk
    simp only [GlobalTheory.Core.Rk.IP.openOff, Set.mem_setOf_eq, map_mul, hproj k hk, mul_one]
  have hw : ∀ g ∈ openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g = K.indicator (fun _ => c) g := by
    intro g hg
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    by_cases hx : x ∈ intG D P.a
    · rw [Set.indicator_of_mem ((hmem x k ∅ hk).2 ((hint x).1 hx)), hc x hx k hk]
    · rw [Set.indicator_of_notMem (fun h => hx ((hint x).2 ((hmem x k ∅ hk).1 h))),
        h0 x hx ((hmem x k Sf hk).1 hg) k hk]
  have hKsub : K ⊆ openOff X.A (stdLat X.A) Sf := fun g hg v _ => hg v (Finset.notMem_empty v)
  have hKm : MeasurableSet K := (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL ∅).measurableSet
  have hSm : MeasurableSet (openOff X.A (stdLat X.A) Sf) :=
    (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL Sf).measurableSet
  have hKeq : K = ((X.KA.comap (Lev.finE X.A) : Subgroup (GA D X.A)) : Set (GA D X.A)) := by
    ext g
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one, hF.levA_iff, hint, hKdef, hmem x k ∅ hk]
  have hKvol : X.m K = 1 := by
    rw [hKeq]; exact GlobalTheory.Mass.Levels.measure_comap_finE hF.measA.choose_spec.1
  have hKc : IsCompact K := by
    have hG : IsCompact (GinfC X.A : Set (GA D X.A)) :=
      GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one D X.A hF.gramA
    refine (hF.levA.2.mul hG).of_isClosed_subset ?_ ?_
    · rw [hKeq]; exact Subgroup.isClosed_of_isOpen _ hF.levA.1
    · intro g hg
      obtain ⟨x, k, hk, rfl⟩ := hdec g
      rw [hKeq, SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one] at hg
      refine Set.mul_mem_mul ?_ hk
      exact Formalism.IndefR.Lev.mem_levA.2 ⟨hF.rangeA ▸ ⟨x, rfl⟩, hg⟩
  obtain ⟨hcont, hpos, -⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D X.A (stdLat X.A) a hL ha
  refine ⟨fun s => ?_, ?_⟩
  · let F : GA D X.A → ℂ := fun g => c * GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL X.A (stdLat X.A) a g)
        (s - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero X.A X.B) * (volQ X.A X.m : ℂ)
    have hFc : Continuous F := by
      refine (continuous_const.mul ?_).mul continuous_const
      simp only [GlobalTheory.Doubling.npow]
      refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hcont)).cpow continuous_const fun g => ?_
      exact Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast (hpos g).1)
    have hI : Integrable (K.indicator F) X.m :=
      (integrable_indicator_iff hKm).2 (hFc.continuousOn.integrableOn_compact' hKc hKm)
    refine hI.integrableOn.congr_fun (fun g hg => ?_) hSm
    have hr : GlobalTheory.Core.Rk.IP.rcoef X.m (fun _ : GA D X.A => (1 : ℂ)) (fun _ => 1) g = (volQ X.A X.m : ℂ) := by
      exact rcoef_one_const X.m g
    simp only [integrand, hr, hw g hg]
    by_cases hgK : g ∈ K
    · simp [Set.indicator_of_mem hgK, F]
    · simp [Set.indicator_of_notMem hgK]
  · rw [setIntegral_congr_fun hSm hw, integral_indicator hKm, Measure.restrict_restrict hKm,
      Set.inter_eq_left.2 hKsub, setIntegral_const, measureReal_def, hKvol]
    simp

end GlobalTheory.RatioConst
end
end

section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem std_mass_ne_zero : ∀ (D : D7) (N : ℕ), mass D N ≠ 0 := by
  intro D N
  haveI := (GlobalTheory.NormSum.cls_finite_card_le D N).1
  haveI := Fintype.ofFinite (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))
  have hne : (Finset.univ : Finset (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))).Nonempty :=
    ⟨DoubleCoset.mk _ _ 1, Finset.mem_univ _⟩
  have hpos : (0 : ℝ) < ∑ x : GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D N) x.out : ℝ))⁻¹ :=
    Finset.sum_pos (fun x _ => inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero
      (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D N _ le_rfl x.out).1))) hne
  unfold mass
  rw [finsum_eq_sum_of_fintype]
  have h := Complex.ofReal_ne_zero.2 hpos.ne'
  push_cast at h
  exact h

end GlobalTheory.NormRatio
end

section

noncomputable section

open scoped Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory GlobalTheory.RegSch
open Filter Topology

namespace GlobalTheory.RegSch.JointCont


open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model in
theorem levi_weyl_rel {R : Type} [CommRing R] {n : ℕ} {b c : Matrix (Fin n) (Fin n) R} (h1 : b * c = 1) (h2 : c * b = 1) :
    blk4 b 0 0 c * blk4 0 1 (-1) 0 = blk4 1 b 0 1 * blk4 0 1 (-1) 0 * blk4 1 c 0 1 *
      (blk4 0 1 (-1) 0 * blk4 0 1 (-1) 0 * blk4 0 1 (-1) 0) * blk4 1 b 0 1 := by
  simp [submatrix_fromBlocks_mul, h1, h2]


open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model in
theorem resEta_of_isWeilSch {D : D7} {n : ℕ} (hn : 0 < n) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle}
    {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) : ResEta D χ V.rank := by
  obtain ⟨χ₀, h1, h2, -⟩ := GlobalTheory.PlaceCompare.Spherical.exists_unram_char D V.rank
  obtain ⟨ψ₀, h₀, lam, hlam, hψeq⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = shift ψ₀ lam := by
    ext x
    rw [hψeq]
    rfl
  obtain ⟨ω₀, hω₀⟩ := Inhab.weil_exists D n V ψ₀ h₀ lam hlam χ₀ h1 h2 θ hθ μ 𝓕 hμ
  rw [← hsh] at hω₀
  suffices h : ∀ t, χ (idF D t) = χ₀ (idF D t) from ⟨h2.1, fun η hη a => (h a).trans (h2.2 η hη a)⟩
  intro t
  let i₀ : Fin n := ⟨0, hn⟩
  let dg : (AF D.host.F)ˣ → Mx D n n := fun u => Matrix.diagonal (Function.update 1 i₀ (idF D u : AE D))
  have hmul : ∀ u u', dg u * dg u' = dg (u * u') := fun u u' => by
    simp only [dg, Matrix.diagonal_mul_diagonal, map_mul, Units.val_mul]
    congr 1
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  have hone : dg 1 = 1 := by simp [dg]
  have hadj : ∀ u, adj (dg u) = dg u := fun u => by
    ext i j
    simp only [adj, dg, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = i₀
      · subst hi
        simp only [if_true, Function.update_self]
        exact GlobalTheory.HermTransversal.cA_algebraMap _
      · simp [Function.update_of_ne hi]
    · simp [hij, Ne.symm hij]
  have e1 : dg t * dg t⁻¹ = 1 := by rw [hmul, mul_inv_cancel, hone]
  have e2 : dg t⁻¹ * dg t = 1 := by rw [hmul, inv_mul_cancel, hone]
  let a : GL (Fin n) (AE D) := ⟨dg t, dg t⁻¹, e1, e2⟩
  have hdet : Matrix.GeneralLinearGroup.det a = idF D t := by
    ext
    simp [a, dg, Finset.prod_update_of_mem]
  obtain ⟨g, hg⟩ := exists_levi (D := D) (n := n) a
  obtain ⟨u, hu⟩ := (exists_unip (dg t)).2 (hadj t)
  obtain ⟨u', hu'⟩ := (exists_unip (dg t⁻¹)).2 (hadj t⁻¹)
  obtain ⟨w, hw⟩ := exists_weyl (D := D) (n := n)
  have hinj : ∀ x y : StdUnn.G D n, mat x = mat y → x = y := fun x y h => Subtype.ext (Units.ext h)
  have hrel : g * w = u * w * u' * (w * w * w) * u := by
    refine hinj _ _ ?_
    have e4 : (adj (a⁻¹).1 : Mx D n n) = dg t⁻¹ := hadj t⁻¹
    rw [e4] at hg
    change mat g * mat w = mat u * mat w * mat u' * (mat w * mat w * mat w) * mat u
    rw [hg, hw, hu, hu']
    exact levi_weyl_rel e1 e2
  let S := ω.toHomUnits.eqLocus ω₀.toHomUnits
  have hU : ∀ (x : StdUnn.G D n) (b : Mx D n n), mat x = blk4 1 b 0 1 → x ∈ S := fun x b hx =>
    Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun y => (hω.unip x b hx Φ y).trans (hω₀.unip x b hx Φ y).symm))
  have hW : w ∈ S :=
    Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun y => (hω.weyl w hw Φ y).trans (hω₀.weyl w hw Φ y).symm))
  have hgS : g ∈ S := by
    rw [← S.mul_mem_cancel_right hW, hrel]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (hU _ _ hu) hW) (hU _ _ hu')) (S.mul_mem (S.mul_mem hW hW) hW)) (hU _ _ hu)
  have hge : ω g = ω₀ g := congrArg Units.val hgS
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.Published.ThetaConvModel.exists_schwartz θ V.rank n
  have k1 := hω.levi g a hg Φ 0
  rw [hge, hω₀.levi g a hg Φ 0, hdet] at k1
  have z1 : ((0 : Mx D V.rank n) ⬝ a.1 : Mx D V.rank n) = 0 := Matrix.zero_mul _
  rw [z1] at k1
  have hp : npow (absA D (idF D t)) ((V.rank : ℂ) / 2) ≠ 0 := by
    have : absA D (idF D t) ≠ 0 := ((Group.isUnit _).map (absA D)).ne_zero
    rw [npow, Complex.cpow_def_of_ne_zero (by exact_mod_cast this)]
    exact Complex.exp_ne_zero _
  exact Circle.ext (mul_right_cancel₀ hp (mul_right_cancel₀ hΦ k1)).symm

end GlobalTheory.RegSch.JointCont

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.movedTensor_unfolding_integral_valuation_loss_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₂ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t) (w : PlL D),
        ((P : Pl D.host.E) ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ c : ℝ, 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
        ∀ X Y, LossLe w ((ch.S.term t Φ β P).datum X Y) (c + c₂ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  first | exact @GlobalTheory.UnfoldLoss.unfold_loss | exact GlobalTheory.UnfoldLoss.unfold_loss | (intros; apply GlobalTheory.UnfoldLoss.unfold_loss <;> assumption)
end

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.SqTop.BotT

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}

theorem nuH_eq (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    nuH G t i j = nuH G μ₀ i j * L.xiH t := by
  simp only [nuH, hL.xi_base, mul_one]
  exact mul_div_right_comm _ _ _

theorem alphaH_eq (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) :
    alphaH L t i j = alphaH L μ₀ i j * L.xiH t := by
  simp only [alphaH, hL.xi_base, mul_one]
  exact mul_right_comm _ _ _

theorem exists_heckeU_nuInv (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ∃ χ : HeckeU D (botBig D i j + botSmall D i j), (∀ x, χ.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) ∧
      ∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χ.n τ := by
  obtain ⟨χ₀, h₀, hw⟩ := GlobalTheory.BottomNu.exists_heckeU_nu_inv hL G i j
  obtain ⟨ξ, hξ, hn⟩ := GlobalTheory.XiSplit.exists_heckeU_xi hL t
  refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₀ (GlobalTheory.AlphaSplit.invU ξ) (by simp), fun x => ?_, fun τ => ?_⟩
  · rw [GlobalTheory.AlphaSplit.mulU_f, GlobalTheory.AlphaSplit.invU_f, h₀, hξ, nuH_eq hL G t, mul_inv]
    rfl
  · show _ ≤ χ₀.n τ + -ξ.n τ
    rw [hn, neg_zero, add_zero]; exact hw τ

theorem exists_heckeU_alpha (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ∃ χ : HeckeU D (botSmall D i j), ∀ x, χ.f x = (alphaH L t i j).1 (finIdl D x) := by
  obtain ⟨χ₀, h₀⟩ := GlobalTheory.FunObj.SqNum.exists_heckeU_alphaH hL G i j
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.XiSplit.exists_heckeU_xi hL t
  refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₀ ξ (by simp), fun x => ?_⟩
  rw [GlobalTheory.AlphaSplit.mulU_f, h₀, hξ, alphaH_eq hL t]
  rfl

theorem pde_ne_q {large₂ : Formalism.BasicNotions.SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩

end GlobalTheory.SqTop.BotT

namespace GlobalTheory.SqTop

theorem botExT_holds (hI : ∀ D, GlobalTheory.NormSum.Inp D) : BotExT := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro δ t0 Q P t i j
  obtain ⟨hq, hq'⟩ := BotT.pde_ne_q hR
  obtain ⟨χν, hν, hw⟩ := BotT.exists_heckeU_nuInv hL G t i j
  obtain ⟨χβ, hβ⟩ := GlobalTheory.FunObj.SqNum.exists_betaInv_heckeU hL G i j
  obtain ⟨χα, hα⟩ := BotT.exists_heckeU_alpha hL G t i j
  obtain ⟨P₁, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_bottomPair_bigMember_twisted_tuple (hI D) hL hq hq' G t P.crv P.pt0 i j χβ hβ χν hν hw
  obtain ⟨P₂, h1', h2', h3', h4', h5'⟩ := GlobalTheory.T.exists_bottomPair_smallMember_twisted_tuple (hI D) hL hq hq' G t P.crv P.pt0 i j χα hα χν hν hw
  exact ⟨P₁, P₂, ⟨⟨h1, h1', h2, h2'.trans h2.symm⟩, h3, h3', h4, h4', ⟨h5, h5'⟩⟩⟩

end GlobalTheory.SqTop

end
end

section

open GlobalTheory.SqTop Formalism.BasicNotions

namespace GlobalTheory.SqTop

theorem botEx_holds (_ : ∀ D, GlobalTheory.NormSum.Inp D) : BotEx := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  obtain ⟨δ, t0, h⟩ := GlobalTheory.FunObj.SqNum.exists_isBottom hL G ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  exact ⟨δ, t0, fun ij => h ij.1 ij.2⟩

end GlobalTheory.SqTop
end

end

section

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio


theorem _root_.GlobalTheory.T.doublingIntegrand_integrable_of_coefficient_const_compact : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  IsSelfDualC X.A (stdLat X.A) → (∀ x, x ∈ intG D P.a ↔ X.ιA x ∈ openOff X.A (stdLat X.A) ∅) →
  ∀ (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), GlobalTheory.Doubling.IsMaj X.A a →
  ∀ (Sf : Finset (FinPl D)) (Φ : WO X.A X.B → ℂ) (c : ℂ),
    (∀ x ∈ intG D P.a, ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = c) →
    (∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = 0) →
    (∀ s : ℂ, IntegrableOn (integrand X.om X.m ν 𝓕 (stdLat X.A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff X.A (stdLat X.A) Sf) X.m) ∧
      ∫ g in openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g ∂X.m = c := by
  first | exact @GlobalTheory.RatioConst.integral_const_coef | exact GlobalTheory.RatioConst.integral_const_coef | (intros; apply GlobalTheory.RatioConst.integral_const_coef <;> assumption)

end
end
