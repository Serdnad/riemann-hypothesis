module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle209
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle653
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle804
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle800
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle797
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle805
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalENM

theorem EN_mem_Man : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ m ∈ P.M, P.EN m ∈ P.Man := by
  intro hB l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hS hC hH m hm
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_eisensteinPow_smul_monodromy_mem_breuilKisin ↥(OL LL) ↥LL.1 l e a ι P
  have hv := hn m hm
  obtain ⟨jD, hjD⟩ := GlobalTheory.T.kisinModule_tensor_bdRPlus_eq_lattice l a e _ _ (thetaW a LL) ϖ ι P T I
  let w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e := fun τ i =>
    toHat _ _ l e ⟨(E ↥LL.1 l e ^ n • P.EN m) τ i, mem_tot.1 hv τ i⟩
  have hw : ∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) =
      hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i) := fun τ i => (hat_coe_Rpi l e _).symm
  clear_value w
  have h3 := GlobalTheory.T.monodromy_image_mem_BdRplus_lattice hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH jD hjD m hm n hv w hw
  choose y hy using fun i => GlobalTheory.T.ideal_power_membership_divisible l a e _ _ (thetaW a LL) ϖ n (fun τ => w τ i) (h3 i)
  have hE : P.EN m ∈ P.Mext (RpiE ↥(OL LL) ↥LL.1 l e) := P.mem_Mext_invE_of_mem_divE hv
  rw [← P.hatTot_mem_Mhat_iff hE, P.mem_Mhat]
  intro τ i
  refine ⟨y i τ, ?_⟩
  have h1 := congrFun (hy i) τ
  have h2 := hw τ i
  have h4 := hat_E_pow_mul (O := ↥(OL LL)) l e n (mem_tot.1 hE τ i)

  have h1' : w τ i = Ehat ↥(OL LL) ↥LL.1 l e ^ n * y i τ := by rw [h1]; rfl
  have h5 : (E ↥LL.1 l e ^ n • P.EN m) τ i = E ↥LL.1 l e ^ n * P.EN m τ i := rfl
  have h7 := ((congrArg (algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e)) h1').symm.trans h2).trans
    ((congrArg (hat ↥(OL LL) l e) h5).trans h4)
  have h8 := (map_mul (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)) _ _).symm.trans h7
  have hu : IsUnit (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e ^ n)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (Ehat ↥(OL LL) ↥LL.1 l e)).pow n
  exact hu.mul_left_cancel h8

end GlobalTheory.NgalENM
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_modification_of_filtration_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (U U' : Matrix (Fin d) (Fin d) (Per.BdR l)), U * U' = 1 → ∀ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), (∀ i, |k i| ≤ N) → (∀ r s, U r s ∈ Per.FilD l (-(N : ℤ))) → (∀ r i, (U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) → (∀ i j, β i j ∈ Per.FilD l (-k i)) → U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 → ∃ (c₂ : ℕ) (X X' : Matrix (Fin d) (Fin d) (bk.S)), X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) ∧ (∀ i j, (U * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) ∧ (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') i j ∈ Per.FilD l N) := by
  first | exact @GlobalTheory.BKModif.exists_modification_of_filtration | exact GlobalTheory.BKModif.exists_modification_of_filtration | (intros; apply GlobalTheory.BKModif.exists_modification_of_filtration <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (c : κ → κ → En.Q.A) (h k : ℕ) (x : κ → En.Q.A), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ^ k ∣ x j := by
  first | exact @GlobalTheory.envelope_dvd_lpow_of_sections | exact GlobalTheory.envelope_dvd_lpow_of_sections | (intros; apply GlobalTheory.envelope_dvd_lpow_of_sections <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.equivariant_latticeMatrix_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T := by
  first | exact @GlobalTheory.BSP.equivariant_matrix_over_bk | exact GlobalTheory.BSP.equivariant_matrix_over_bk | (intros; apply GlobalTheory.BSP.equivariant_matrix_over_bk <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_truncLog_gal_mod_filP : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(GK K) → ℤ_[l]),
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) →
    ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K),
      aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil) | (exact GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil) | (intros; apply GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil  <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sum_adelicReading_eq_of_two_baseChange_decomps_on_cover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.σ₂.comp C.inc = σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m m' : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j) (as : Fin m' → C.c'.F) (fs : Fin m' → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → IsBC C.hle (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) as fs → ∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b) = ∑ i, C.σ₂ (C.d.eF (as i)) • T.phiJ j σ a (fs i) := by
  first | exact @GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC | exact GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC | (intros; apply GlobalTheory.CoverBCRead.phiJ_sum_eq_of_isBC <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.isCuspidal_jacquetModule_second_block_of_vanishing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ (r t : ℕ) (h' : r + t = n), 0 < t → t < b → Subsingleton (Jacquet π (unipRad k (two (stdSum h'))))) → IsCuspidal (k := k) (n := Fin b) ((jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k))) := by
  first | exact @GlobalTheory.JacMinCuspGL.isCuspidal_jac₂_inr | exact GlobalTheory.JacMinCuspGL.isCuspidal_jac₂_inr | (intros; apply GlobalTheory.JacMinCuspGL.isCuspidal_jac₂_inr <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem _root_.GlobalTheory.T.isSubquotient_jacquetModule_refine_tensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (jac E π) := by
  first | exact @GlobalTheory.JacStages.isSubquotient_jac_refine | exact GlobalTheory.JacStages.isSubquotient_jac_refine | (intros; apply GlobalTheory.JacStages.isSubquotient_jac_refine <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem _root_.GlobalTheory.T.isSubquotient_jacquetModule_singleBlock_self : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (e : (Σ _ : Fin 1, Fin N) ≃ Fin N), IsSubquotient (piTensor fun _ : Fin 1 => π) (jac e π) := by
  first | exact @GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac | exact GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac | (intros; apply GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLagTerms
variable {D : D7}

theorem cA_incA_loc (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem adjO_mul_rat (V W : HSp D) (y : Mx D V.rank W.rank) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    GlobalTheory.PairLift.adjO V W (HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (M.map (incA D))) =
      ratMul (hAdj W M) (GlobalTheory.PairLift.adjO V W y) := by
  have e : ((M.map (incA D)).map (cA D))ᵀ = ((M.map star)ᵀ).map (incA D) := by
    ext i j; simp [cA_incA_loc]
  rw [GlobalTheory.AdjLawPf.adjO_eq, GlobalTheory.AdjLawPf.adjO_eq, GlobalTheory.AdjLawPf.conjT_mul, e]
  unfold ratMul hAdj
  rw [Matrix.map_mul, Matrix.map_mul]
  have g1 : (HSpace.gram W).map (incA D) * (HSpace.gram W)⁻¹.map (incA D) = 1 :=
    mul_eq_one_comm.1 (GlobalTheory.AdjLawPf.inv_mul_gram W)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((HSpace.gram W).map (incA D)), g1, Matrix.one_mul]

theorem act_lagr (V W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (hg : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) (y : Mx D V.rank W.rank) :
    actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y) =
      HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D)) := by
  unfold actO
  rw [inv_inv, hg, GlobalTheory.AdjLawPf.mt_one, Matrix.one_mul]

theorem resL_lagr (V W : HSp D) (y : Mx D V.rank W.rank)
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL W V (HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D))) =
      HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (((blk W g₀).toBlocks₁₁ - (blk W g₀).toBlocks₂₁).map (incA D)) := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [GlobalTheory.SiegelFormula.lagr, Matrix.of_apply, GlobalTheory.Doubling.pairVec_inl, GlobalTheory.Doubling.pairVec_inr, blk,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.sub_apply, map_sub, mul_sub,
    Finset.sum_sub_distrib, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  abel

theorem resR_lagr (V W : HSp D) (y : Mx D V.rank W.rank)
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    -GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR W V (HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D))) =
      HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (((blk W g₀).toBlocks₂₂ - (blk W g₀).toBlocks₁₂).map (incA D)) := by
  ext i j
  simp only [Matrix.neg_apply, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [GlobalTheory.SiegelFormula.lagr, Matrix.of_apply, GlobalTheory.Doubling.pairVec_inl, GlobalTheory.Doubling.pairVec_inr, blk,
    Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.sub_apply, map_sub, mul_sub,
    Finset.sum_sub_distrib, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  abel

theorem dbl_actO_lagr : ∀ (D : D7) (V W : HSp D) (f₁ f₂ : WO V W → ℂ) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E),
    Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∀ (y : Mx D V.rank W.rank),
    GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) =
      f₁ (ratMul (frameOf W g₀).1 (GlobalTheory.PairLift.adjO V W y)) * star (f₂ (ratMul (frameOf W g₀).2 (GlobalTheory.PairLift.adjO V W y))) := by
  intro D V W f₁ f₂ γ g₀ hg y
  rw [act_lagr V W γ g₀ hg y, GlobalTheory.SWPairProof.dbl_apply, resL_lagr, resR_lagr, adjO_mul_rat, adjO_mul_rat,
    frameOf_fst, frameOf_snd, starRingEnd_apply, mul_comm]

end GlobalTheory.SWLagTerms
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.thetaFunction_mem_span_levelType_differences : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ} ∪ GlobalTheory.DownLift.GenFinite.TypeDiff R i t) := by
  first | exact @GlobalTheory.DownLift.GenFinite.typeSpan | exact GlobalTheory.DownLift.GenFinite.typeSpan | (intros; apply GlobalTheory.DownLift.GenFinite.typeSpan <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

theorem _root_.GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)), IsUnifV E w (ϖ w : w.adicCompletion E) → GlobalTheory.RamShift.CondOne w ((ϖ w ^ GlobalTheory.RamShift.condExp ϖ w : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  first | (exact @GlobalTheory.RamShift.condOne_condExp) | (exact GlobalTheory.RamShift.condOne_condExp) | (intros; apply GlobalTheory.RamShift.condOne_condExp  <;> assumption)
end
