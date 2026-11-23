module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle298
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle200
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle172
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle794
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle419
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Formalism.LocalRingCardinality.Bundle004
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle796
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle127
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverBCRead

theorem evR_sum_eq {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ)
    (hσ : C.σ₂.comp C.inc = σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {m m' : ℕ} (x : Fin m → C.c'.F)
    (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j)
    (hf : ∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n)
    (hBC : IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs)
    (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) :
    (∑ b, C.σ₂ (C.d.eF (x b)) * toC (evR (T.Q.Xo j) T.Q.c (f b) y)) =
      ∑ i, C.σ₂ (C.d.eF (as i)) * toC (evR (T.Q.Xo j) T.Q.c (fs i) y) := by
  letI : Algebra C.c'.F (CAt σ) := (C.σ₂.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)).toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle (CAt σ) := by
    intro c0
    show C.σ₂ (C.d.eF (incF T.Q.c C.c' C.hle c0)) = σ c0
    exact RingHom.congr_fun hσ c0
  have h1 := hBC (CAt σ) hA (FrPt.ext C.hle hA y)
  rw [Formalism.L2.Pj.evR_sum_smul] at h1
  simp only [GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf _).1 hA, FrPt.res_ext] at h1
  exact h1

theorem phiJ_sum_eq_of_isBC : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.σ₂.comp C.inc = σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m m' : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs → ∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b) = ∑ i, C.σ₂ (C.d.eF (as i)) • T.phiJ j σ a (fs i) := by
  intro D T j σ C hσ a n m m' x f as fs hf hBC
  have key : (∑ b, C.σ₂ (C.d.eF (x b)) • rdU (T.U j σ) (f b) : FDSec (T.U j σ).X) =
      ∑ i, C.σ₂ (C.d.eF (as i)) • rdU (T.U j σ) (fs i) := by
    funext k z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : z ∈ ((T.U j σ).X k).dom
    · simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]
      exact evR_sum_eq T j σ C hσ a n x f as fs hf hBC ((T.U j σ).un k ⟨z, h⟩)
    · simp [rdU, dif_neg h]
  let L : FDSec (T.U j σ).X →ₗ[ℂ] (GA D (T.V j σ) → ℂ) := (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ))
  have e : ∀ g : T.R j, T.phiJ j σ a g = L (rdU (T.U j σ) g) := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, ← map_smul, ← map_sum, key]

end GlobalTheory.CoverBCRead
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem isSubquotient_jac_refine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (_root_.GlobalTheory.SmGL.jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (_root_.GlobalTheory.SmGL.jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (_root_.GlobalTheory.SmGL.jac E π) := by
  intro k _ _ _ _ n s d e V _ _ π hπ X _ _ ρ _ hsub t d' e' Y _ _ ρ' hρ'
  refine ⟨refinePlace e e', ?_⟩
  refine isSubquotient_of_comp (flatHom fun a b => GL (Fin (d' a b)) k) (flatHom_surjective _) ?_
  obtain ⟨φR⟩ := GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested s t (fun a b => GL (Fin (d' a b)) k) Y ρ'
  obtain ⟨φT⟩ := GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized k s d t d' e' X ρ
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s n d e t d' e' V π
  have h1 : IsSubquotient (piTensor fun a => piTensor (ρ' a)) (piTensor fun a => _root_.GlobalTheory.SmGL.jac (e' a) (ρ a)) :=
    GlobalTheory.piTensor_isSubquotient_of_forall _ _ _ _ _ _ hρ'
  have h3 := GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi k s d t d' e' _ _ (piTensor ρ) (_root_.GlobalTheory.SmGL.jac e π) (isSmooth_jac e hπ) hsub
  exact (isSubquotient_of_equiv φR).trans (h1.trans ((isSubquotient_of_equiv φT.symm).trans
    (h3.trans (isSubquotient_of_equiv φS.symm))))

end GlobalTheory.JacStages
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.JacMinCuspGL

open GlobalTheory.SmGL.CuspMax GlobalTheory.JacMinCusp Matrix

theorem isCuspidal_jac₂_inr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    (∀ (r t : ℕ) (h' : r + t = n), 0 < t → t < b → Subsingleton (Jacquet π (unipRad k (two (stdSum h'))))) →
    IsCuspidal (k := k) (n := Fin b) ((jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k))) := by
  intro k _ _ _ _ a b n h V _ _ π hπ hmin
  set J := (jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k)) with hJdef
  refine (isCuspidal_iff_maximal k b _ J).2 ⟨isSmooth_comp (isSmooth_jac₂ _ hπ) _
    (continuous_const.prodMk continuous_id :
      Continuous fun x : GL (Fin b) k => ((1 : GL (Fin a) k), x)),
    fun r t h' hr ht => ?_⟩
  have hcd : a + r + t = n := by omega
  have hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 (hmin (a + r) t hcd ht (by omega))
  set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab
  set K' := twKer J (unipRad k (two (stdSum h'))) 1 with hK'

  have hB : ∀ g : GL (Fin a) k × GL (Fin b) k, g.1 = 1 → GeneralLinearGroup.det g.2 = 1 → ∀ v : V,
      jac₂ (stdSum h) π g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v) := by
    intro g h1 h2 v
    have hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1 := by
      rw [deltaHalf_two, h1, h2]; simp
    show _root_.GlobalTheory.SmGL.jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _
    rw [jac_mk, hd]; simp
  have hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v := by
    intro u hu v
    exact (Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)

  have hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) - Submodule.Quotient.mk v ∈ K' := by
    intro u hu v
    have hu' := (mem_unipRad_two_iff hcd).1 hu
    have hp : u ∈ parab k (two (stdSum h)) := by
      rw [mem_parab]
      intro i j hij
      rw [blk_two_stdSum_lt] at hij
      rw [hu' i j (by omega), Matrix.one_apply_ne]
      intro hij'; subst hij'; omega
    obtain ⟨n', hn', hun⟩ := exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩
    set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg
    have hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩ := by simp [g]
    have hg1 : g.1 = 1 := by
      ext i j
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _
      rw [leviProj_apply, two_false, two_false]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hg2 : g.2 ∈ unipRad k (two (stdSum h')) := by
      rw [mem_unipRad_two_iff]
      intro i j hij
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _
      rw [leviProj_apply, two_true, two_true]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hdet : GeneralLinearGroup.det g.2 = 1 := det_eq_one_of_mem_unipRad k hg2
    have hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n' := by rw [hlg]; exact hun
    have hJu : J g.2 (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π u v) := by
      rw [hu_eq, map_mul, Module.End.mul_apply]
      show jac₂ (stdSum h) π (1, g.2) _ = _
      rw [hB (1, g.2) rfl hdet, show ((1, g.2) : GL (Fin a) k × GL (Fin b) k) = g from Prod.ext hg1.symm rfl]
      refine (Submodule.Quotient.eq Kab).2 ?_
      rw [← map_sub]
      refine twKer_le_comap π _ _ (leviEmb_mem_normalizer k _ _) ?_
      have := (Submodule.Quotient.eq Kab).1 (hN n' hn' v)
      rw [← neg_sub]
      exact Kab.neg_mem this
    rw [← hJu]
    exact Submodule.subset_span ⟨⟨g.2, hg2⟩, Submodule.Quotient.mk v, by simp⟩
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun x _ => ?_)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Kab x
  have hle : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ K'.comap Kab.mkQ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    simpa [Submodule.mkQ_apply] using hC u u.2 w
  exact hle (hJ ▸ Submodule.mem_top)

end GlobalTheory.JacMinCuspGL
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.schur_l2Pairing_realFiniteTranslate : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x y : (R.HW i (sg0 D A)).H), ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  first | exact @GlobalTheory.RawLift.schur_trPair_real_fin | exact GlobalTheory.RawLift.schur_trPair_real_fin | (intros; apply GlobalTheory.RawLift.schur_trPair_real_fin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite.TypeSpan

variable {D : D7} {V W : HSp D}

theorem levChi_mul' {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {k k' : GA D V}
    (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have e := (Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩
  have e' : Formalism.L2.DIV.levFn β L (finE V k * finE V k') =
      Formalism.L2.DIV.levFn β L (finE V k) * Formalism.L2.DIV.levFn β L (finE V k') := e
  unfold levChi
  rw [map_mul, e', Units.val_mul]

theorem levChi_ne_zero (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (k : GA D V) :
    levChi V β L k ≠ 0 := by
  unfold levChi
  exact Units.ne_zero _

theorem eventually_levChi_one (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in nhds (1 : GA D V), levChi V β L κ = 1 := by
  classical
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨-, -, h3⟩ := hh
  unfold levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ fun PP hP => h3 PP (by rcases hP with h | h <;> simp [h]), Units.val_one]

end GlobalTheory.DownLift.GenFinite.TypeSpan

namespace GlobalTheory.DownLift.GenFinite

open GlobalTheory.DownLift.GenFinite.TypeSpan

theorem typeSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ} ∪ GlobalTheory.DownLift.GenFinite.TypeDiff R i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ hP i t f hf
  classical
  have hW := (hP i t).datum
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Vc D i).gram
  obtain ⟨U, U', hUo, -, hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D R.ψ hW.std (Vc D i) (Wc D i) (R.ωP i t)
    (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont f hf
  set J := levG (Vc D i) (R.βV i) (R.datVt i t) with hJ
  set lam := levChi (Vc D i) (R.βV i) (R.datVt i t) with hlam
  set om := R.ωP i t with hom
  have hmul : ∀ a b : GA D (Vc D i), om (a * b, 1) = om (a, 1) * om (b, 1) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hone : om (1, 1) = 1 := by rw [← Prod.one_eq_mk, map_one]
  have hlm : ∀ {a b : GA D (Vc D i)}, a ∈ J → b ∈ J → lam (a * b) = lam a * lam b := fun ha hb => levChi_mul' ha hb
  have hlne : ∀ a : GA D (Vc D i), lam a ≠ 0 := fun a => levChi_ne_zero _ _ a
  have hlam1 : lam 1 = 1 := by
    have e := hlm (one_mem J) (one_mem J)
    rw [mul_one] at e
    have h0 := hlne 1
    have e' : lam 1 * 1 = lam 1 * lam 1 := by rw [mul_one]; exact e
    exact (mul_left_cancel₀ h0 e').symm

  let N : Subgroup J :=
    { carrier := {κ | om ((κ : GA D (Vc D i)), 1) f = f ∧ lam κ = 1}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i)) * b, 1) f = f
          rw [hmul, Module.End.mul_apply, hb1, ha1]
        · show lam ((a : GA D (Vc D i)) * b) = 1
          rw [hlm a.2 b.2, ha2, hb2, one_mul]
      one_mem' := by
        refine ⟨?_, ?_⟩
        · show om (1, 1) f = f
          rw [hone]; rfl
        · exact hlam1
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i))⁻¹, 1) f = f
          conv_lhs => rw [← ha1]
          rw [← Module.End.mul_apply, ← hmul, inv_mul_cancel, hone]; rfl
        · show lam ((a : GA D (Vc D i))⁻¹) = 1
          have e := hlm (inv_mem a.2) a.2
          rw [inv_mul_cancel, hlam1, ha2, mul_one] at e
          exact e.symm }
  have hNo : IsOpen (N : Set J) := by
    refine Subgroup.isOpen_of_mem_nhds N (g := 1) ?_
    have h1 : {x : GA D (Vc D i) | x ∈ U ∧ lam x = 1} ∈ nhds (1 : GA D (Vc D i)) :=
      Filter.inter_mem (hUo.mem_nhds U.one_mem) (eventually_levChi_one _ _)
    have h2 := (continuous_subtype_val (p := fun x => x ∈ J)).continuousAt (x := (1 : J)).preimage_mem_nhds h1
    exact Filter.mem_of_superset h2 fun κ hκ => ⟨hfix _ hκ.1 κ.2.1 1 U'.one_mem (one_mem _), hκ.2⟩
  haveI : CompactSpace J := isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  haveI : Finite (J ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  letI : Fintype (J ⧸ N) := Fintype.ofFinite _

  let Fv : J → (WO (Vc D i) (Wc D i) → ℂ) := fun κ => lam κ • om ((κ : GA D (Vc D i)), 1) f
  have hFvN : ∀ (a n : J), n ∈ N → Fv (a * n) = Fv a := by
    rintro a n ⟨hn1, hn2⟩
    show lam ((a : GA D (Vc D i)) * n) • om ((a : GA D (Vc D i)) * n, 1) f = lam a • om ((a : GA D (Vc D i)), 1) f
    rw [hlm a.2 n.2, hn2, mul_one, hmul, Module.End.mul_apply, hn1]
  let Fb : J ⧸ N → (WO (Vc D i) (Wc D i) → ℂ) := fun q => Fv q.out
  have hFb : ∀ κ : J, Fb (κ : J ⧸ N) = Fv κ := by
    intro κ
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N κ
    show Fv (κ : J ⧸ N).out = Fv κ
    rw [hn]
    exact hFvN κ n n.2
  have hFbTh : ∀ q, IsThetaFunO R.ψ (Vc D i) (Wc D i) (Fb q) := fun q =>
    theta_smul _ (hW.om_pres _ _ hf)

  have hact : ∀ (κ' : J) (q : J ⧸ N), om ((κ' : GA D (Vc D i)), 1) (Fb q) = (lam κ')⁻¹ • Fb (κ' • q) := by
    intro κ' q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [MulAction.Quotient.smul_mk, hFb, hFb]
      show om ((κ' : GA D (Vc D i)), 1) (lam κ • om ((κ : GA D (Vc D i)), 1) f) =
        (lam κ')⁻¹ • (lam ((κ' : GA D (Vc D i)) * κ) • om ((κ' : GA D (Vc D i)) * κ, 1) f)
      rw [map_smul, hmul, Module.End.mul_apply, hlm κ'.2 κ.2, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ (hlne _), one_mul]
  set c : ℂ := ((Fintype.card (J ⧸ N) : ℕ) : ℂ)⁻¹ with hc
  set fJ := c • ∑ q, Fb q with hfJ
  have hfJv : TypeVec R i t fJ := by
    refine ⟨theta_smul _ (theta_sum Finset.univ Fb f hf fun q _ => hFbTh q), fun κ hκ => ?_⟩
    show om (κ, 1) fJ = (lam κ)⁻¹ • fJ
    have e : om (κ, 1) (∑ q, Fb q) = (lam κ)⁻¹ • ∑ q, Fb q := by

      rw [map_sum]
      have := fun q => hact ⟨κ, hκ⟩ q
      simp only [] at this
      rw [Finset.sum_congr rfl fun q _ => this q, ← Finset.smul_sum]
      congr 1
      exact Equiv.sum_comp (MulAction.toPerm (⟨κ, hκ⟩ : J)) Fb
    rw [hfJ, map_smul, e, smul_comm]
  have hdiff : ∀ q, f - Fb q ∈ Submodule.span ℂ ({φ | TypeVec R i t φ} ∪ TypeDiff R i t) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [hFb]
      have e : f - Fv κ = (-lam κ) • (om ((κ : GA D (Vc D i)), 1) f - (lam κ)⁻¹ • f) := by
        show f - lam κ • om ((κ : GA D (Vc D i)), 1) f = _
        rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ (hlne _)]
        simp only [neg_smul, one_smul]
        abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨κ, κ.2, f, hf, rfl⟩))
  have hcard : ((Fintype.card (J ⧸ N) : ℕ) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (J ⧸ N) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsplit : f = fJ + c • ∑ q, (f - Fb q) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      hc, inv_mul_cancel₀ hcard, one_smul, hfJ]
    abel
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.subset_span (Or.inl hfJv))
    (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => hdiff q))

end GlobalTheory.DownLift.GenFinite

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  exact @GlobalTheory.BKGal.JumpDR.basis_images
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

namespace GlobalTheory.RamShift

theorem condOne_condExp : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)), IsUnifV E w (ϖ w : w.adicCompletion E) → GlobalTheory.RamShift.CondOne w ((ϖ w ^ GlobalTheory.RamShift.condExp ϖ w : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  intro E _ _ ϖ w hϖ
  obtain ⟨ψ, hψ, hlc, hne⟩ := GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one E w
  have hcont : Continuous ψ := hlc.continuous
  have hnorm : ∀ t, ‖ψ t‖ = 1 := fun t => by
    rw [hψ]; exact Circle.norm_coe _
  have hne' : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_conductor_exponent E w ψ hcont hnorm hne'
  have hval : Valued.v (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = WithZero.exp n := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    rw [← WithZero.exp, ← WithZero.exp_zsmul]
    simp
  have key : CondOne w (((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) := by
    intro x
    have h1 := hn ((((ϖ w ^ (-n) : (w.adicCompletion E)ˣ)) : w.adicCompletion E) * x)
    simp only [hψ] at h1
    rw [map_mul, hval] at h1
    have h2 : WithZero.exp n * Valued.v x ≤ WithZero.exp n ↔ Valued.v x ≤ 1 := by
      conv_lhs => rhs; rw [← mul_one (WithZero.exp n)]
      exact mul_le_mul_iff_right₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)
    rw [h2] at h1
    exact h1
  unfold condExp
  split_ifs with h1 h2
  · simpa using h1
  · exact h2.choose_spec
  · exact absurd ⟨-n, key⟩ h2

end GlobalTheory.RamShift
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.every_heckeRow_good_at_goodPointLocalisation : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  first | exact @GlobalTheory.ExhaustRows.main | exact GlobalTheory.ExhaustRows.main | (intros; apply GlobalTheory.ExhaustRows.main <;> assumption)
end
