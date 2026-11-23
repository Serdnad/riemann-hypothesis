module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.BesselDatum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle348
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TargetPairingSizesInCoefficientFieldValueGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Formalism.LocalToGlobal.Columns.TiedLv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistIndexOfCoefficientFieldPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingsCharactersClassGroups
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallFieldClassFieldPieces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle414
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle415
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Formalism.LocalToGlobal.Columns.Bundle032
public import Formalism.LocalToGlobal.Columns.RecLevelCls
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import ReciprocityTheory.Automorphisms.PlaceA
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PosLinVec

theorem hA_single {D : D7} (A : HSp D) (x : Fin A.rank → AE D) (i : Fin A.rank) (s : AE D) :
    hA A x (Pi.single i (cA D s)) = (A.gram.map (incA D)).mulVec x i * s := by
  rw [hA_eq, show (fun j => cA D ((Pi.single i (cA D s) : Fin A.rank → AE D) j)) = Pi.single i s from
    funext fun j => by by_cases e : j = i <;> simp [e, GlobalTheory.RootExch.cA_cA], single_dotProduct, mul_comm]

theorem vec_of_scalar {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    (c : R →+* R) (hc : Continuous c) (ε u w : R) (huw : w * u = 1) (J : Matrix (Fin n) (Fin n) R) (hJ : IsUnit J)
    (h : (Fin n → R) → (Fin n → R) → R) (hh : ∀ x i s, h x (Pi.single i (c s)) = J.mulVec x i * s)
    (P : R → Prop)
    (H : ∀ V ∈ nhds (0 : R), ∃ C : Set R, IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → P (a * s)) → a ∈ C) :
    ∀ V ∈ nhds (0 : Fin n → R), ∃ C : Set (Fin n → R), IsCompact C ∧ ∀ t₀, ε • t₀ = t₀ →
      (∀ t ∈ V, c ε • t = t → P (u * h t₀ t)) → t₀ ∈ C := by
  intro V hV
  have hc' : ∀ i : Fin n, Continuous fun s : R => (Pi.single i (c s) : Fin n → R) := fun i =>
    (continuous_single (A := fun _ : Fin n => R) i).comp hc
  have hVi : ∀ i : Fin n, (fun s : R => (Pi.single i (c s) : Fin n → R)) ⁻¹' V ∈ nhds (0 : R) := fun i =>
    (hc' i).continuousAt.preimage_mem_nhds (by simpa only [map_zero, Pi.single_zero] using hV)
  choose C hC hmem using fun i => H _ (hVi i)
  obtain ⟨K, hK⟩ := hJ.exists_left_inv
  let g : (Fin n → R) → (Fin n → R) := fun a => w • K.mulVec a
  have hg0 : Continuous fun a : Fin n → R => K.mulVec a := continuous_const.matrix_mulVec continuous_id
  have hg : Continuous g := continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp hg0)
  refine ⟨g '' Set.pi Set.univ C, (isCompact_univ_pi hC).image hg, fun t₀ ht h' => ?_⟩
  refine ⟨u • J.mulVec t₀, fun i _ => hmem i _ ?_ fun s hs hεs => ?_, ?_⟩
  · conv_rhs => rw [← ht]
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · have := h' _ hs (by rw [← Pi.single_smul, smul_eq_mul, ← map_mul, hεs])
    rw [hh] at this
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact this
  · simp only [g]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hK, Matrix.one_mulVec, smul_smul, huw, one_smul]

theorem annihilator_subset_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ (A : HSp D) (θ : D.host.E), θ ≠ 0 → ∀ V ∈ nhds (0 : Fin A.rank → AE D), ∃ C : Set (Fin A.rank → AE D), IsCompact C ∧ ∀ t₀, ε • t₀ = t₀ → (∀ t ∈ V, cA D ε • t = t → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D θ * hA A t₀ t)) = 1) → t₀ ∈ C := by
  intro D ψ hψ ε hε A θ hθ
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact vec_of_scalar (cA D) GlobalTheory.FockCompare.ThetaCont.continuous_conj ε (incA D θ) (incA D θ⁻¹)
    (by rw [← RingHom.map_mul, inv_mul_cancel₀ hθ, RingHom.map_one]) (A.gram.map (incA D))
    ((GlobalTheory.BesselCompare.gram_isUnit A).map (incA D).mapMatrix) (hA A) (hA_single A)
    (fun a => ψ (Algebra.trace (AF D.host.F) (AE D) a) = 1)
    (GlobalTheory.T.splitPlace_annihilator_relativelyCompact D ψ (GlobalTheory.T.standardAdelicCharacter_localComponent_ne_one D ψ hψ) ε hε)

end GlobalTheory.PosLinVec
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.targetPairing_sizes_in_coefficientField_valueGroup : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v' : ValQ O u μ (i + 1)) (J : KM.ColChoice ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i)), ∃ b : (I.rec7 l Z).what₂.LL, ‖prTC Pl O Bs u μ w i c' v' J‖ = ‖Pl.iL w b‖ := by
  first | exact @GlobalTheory.KerVal.prTC_val | exact GlobalTheory.KerVal.prTC_val | (intros; apply GlobalTheory.KerVal.prTC_val <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt



theorem pr_lvC_eq_lv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) v (c : ((I.rec7 l Z).mem u).C.cls i), (∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i (le_of_succ_m h2) c) (z' : LdG (I.rec7 l Z) i (le_of_succ_m h2) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).pr v c z' = ((F u).lv i (le_of_succ_m h2)).pr v c z) ∧ ∀ (z : Formalism.L2.Forms.Lk (F u).atT i (le_of_succ_m h2) v c) (z' : LkG (I.rec7 l Z) i (le_of_succ_m h2) (PvG (F u).atT.res v) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).prk v c z' = ((F u).lv i (le_of_succ_m h2)).prk v c z := by
  intro B X I hI hP l Z H F hS hC u i h1 h2 v c
  have hi := le_of_succ_m h2
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  obtain ⟨hg, -, hL⟩ := hsp i hi
  have hlat := (hL u I.mu0).1 c
  obtain ⟨hF, hFC⟩ := hS u
  have hcl : clsCrd (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hlat
  have hres := hF.res
  have hsep := sepElt_of_ok l.pr u
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hLd : Ld (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.Lsh := by
    show dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (clsCrd (I.rec7 l Z) u i hi c) = _
    rw [hg, hcl]
    exact rlc_span_dualSet (I.rec7 l Z).sp.cm _ _
  have hPv : (F u).atT.Pv v = (show (B.primes X).vT u from v).1.asIdeal := by
    ext x
    show (F u).atT.res v x = 0 ↔ _
    rw [hres]
    exact Ideal.Quotient.eq_zero_iff_mem (I := (show HeightOneSpectrum (𝓞 B.fields.E) from v.1).asIdeal)
  have hLk : Formalism.L2.Forms.Lk (F u).atT i hi v c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.LshKer v := by
    rw [lv_LshKer_eq _ hsep v]
    show clsCrd (I.rec7 l Z) u i hi c ⊔ (F u).atT.Pv v • Ld (I.rec7 l Z) u i hi c = _
    rw [hLd, hcl, hPv]
    rfl
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 (I.rec7 l Z).host.E, s = cO B.fields.E ((B.primes X).piT u) := ⟨_, rfl⟩
  have hu : (F u).atT.res v s ≠ 0 := by
    rw [hres, hs]
    exact fun h => hsep.off v (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hd : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Ld (I.rec7 l Z) u i hi c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.N := fun x hx => by
    rw [hs]
    exact (((I.stp u I.mu0 i).rep c).1.1.deco).2.smul_Lsh_mem_N hsep.conj (hLd ▸ hx)
  have hk : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v := fun x hx => by
    rw [hs]
    exact (le_sup_left : _ ≤ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v) (lv_smul_LshKer_mem _ hsep v (hLk ▸ hx))
  refine ⟨fun z z' e => ?_, fun z z' e => ?_⟩
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.pr i hi v c (s • ⟨x', hx⟩) (hd x' hx)
    have e2 := (hFC.1 i h1 h2).1 v c (s • ⟨x', hx'⟩) (hd x' hx)
    rw [((F u).lv i hi).pr_smul] at e1
    rw [((F u).lvC i h1 h2).pr_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.prk i hi v c (s • ⟨x', hx⟩) (hk x' hx)
    have e2 := (hFC.1 i h1 h2).2 v c (s • ⟨x', hx'⟩) (hk x' hx)
    rw [((F u).lv i hi).prk_smul] at e1
    rw [((F u).lvC i h1 h2).prk_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)

end GlobalTheory.Mem.Col2.HAt
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianColumns_generators_baseLattices_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → Formalism.L2.Herm.SymmetricCofactorCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricBaseCompatibility (I.rec7 l Z) H A ∧ Nonempty (Formalism.L2.Herm.SymmetricResidueFieldLevels (I.rec7 l Z) H A) ∧ ∃ X0 : Formalism.L2.Herm.SymmetricLevelZeroData (I.rec7 l Z) H A, ∀ u, (X0 u).piG = X.piG := by
  first | exact @GlobalTheory.Mem.Col2.TC.herm_rest_tied | exact GlobalTheory.Mem.Col2.TC.herm_rest_tied | (intros; apply GlobalTheory.Mem.Col2.TC.herm_rest_tied <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_twistIndex_of_coefficientField_place : ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd)
    (Sp : RingSpec D cf b0 b1 Sx T) (w : D.what₂.places.Pl), ∃ i, T.l i = D.what₂.places.resChar w ∧
      ∀ x : D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔
        T.emb0 i x ∈ (algebraMap (T.O0 i) (FractionRing (T.O0 i))).range := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.CoverPl.exists_setting_of_place | exact GlobalTheory.HeightCounting.FormsStep.CoverPl.exists_setting_of_place | (intros; apply GlobalTheory.HeightCounting.FormsStep.CoverPl.exists_setting_of_place <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_twistRings_characters_classGroups : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (J : ∀ (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 ↥D.LL0)), ((l : ℕ) : 𝓞 ↥D.LL0) ∈ w.asIdeal → (↥D.LL0 →+* PadicAlgCl l)), (∀ (l : ℕ) [Fact l.Prime] w h (x : 𝓞 ↥D.LL0), x ∈ w.asIdeal ↔ ‖J l w h x‖ < 1) → ValLL0 D cf → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → ∃ (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), ∀ i, Sp.j0 i = J (T.l i) (Sp.eTw i) (Sp.pl_emb i).1 ∧ Sp.K0 i = b0 (T.l i) (Sp.j0 i) ∧ Sp.Lw i = b1 (T.l i) (Sp.j0 i) := by
  first | exact @GlobalTheory.TwRing.exists_ringSpec | exact GlobalTheory.TwRing.exists_ringSpec | (intros; apply GlobalTheory.TwRing.exists_ringSpec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_smallField_classFieldPieces : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : FieldDat X.B.toPre) (T : HostTied X.toD7), ∃ P : KsPieces X.toD7 T, P.HK = qb T.fr.ι (hilbertField X.B.host.d δ.jField) ∧ P.rcf = qb T.fr.ι δ.ray ∧ P.M = qb T.fr.ι δ.M ∧ P.MDel = qb T.fr.ι δ.M' ∧ P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) := by
  first | exact @GlobalTheory.SmallFieldPieces.exists_pieces | exact GlobalTheory.SmallFieldPieces.exists_pieces | (intros; apply GlobalTheory.SmallFieldPieces.exists_pieces <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TupTieW

theorem tupTied_of_muIsW : ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl) (xi : X.C.Tup → HChar X.B.host.E), V4.MuIsW X f T Wt xi → (∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt) ∧ Wt.Finite ∧ (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) ∧ ∀ nch : NChoice X.toD7, (∀ w ∈ Wt, nch.Q w = T.Q w) → ∃ tp : TupTied X.toD7 (Fr.at X f) nch, tp.xi = xi ∧ tp.psi = T.psi := by
  intro X f T Wt xi h
  have key : ∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt := by
    intro w
    constructor
    · intro hw
      by_contra hn
      exact hw (h.off w hn)
    · intro hw he
      have he' : X.W.muAt w = X.C.mu0 := he
      rw [h.on w hw] at he'
      have h1 := h.tw w
      rw [he', h.mu0] at h1
      exact (TwFin.tw_fin X.B f T).2.1 w h1.symm
  have hfin : Wt.Finite :=
    Set.Finite.subset (TwFin.tw_fin X.B f T).2.2.2 fun w hw => h.sub w hw
  have hconj : ∀ w ∈ Wt, X.B.places.conj w ∈ Wt := by
    intro w hw
    refine (key _).1 ?_
    have hc : X.toD7.what₂.muAt (X.toD7.what₂.places.conj w) = X.toD7.what₂.muAt w :=
      X.toD7.what₂.muAt_conj w
    intro he
    exact (key w).2 hw (hc.symm.trans he)
  refine ⟨key, hfin, hconj, fun nch hQ => ?_⟩
  have hg : ∀ μ, TupTie.Good X.B.host.F (xi μ) :=
    fun μ => TupTie.good_set f T (h.range ▸ Set.mem_range_self μ)
  refine ⟨⟨xi, h.inj, fun μ => (hg μ).1, fun μ => (hg μ).2.1, fun μ => (hg μ).2.2, T.psi, h.mu0, h.star, h.star', h.tw,
    fun w hw => ?_, fun w hw => ?_⟩, rfl, rfl⟩
  · rw [hQ w ((key w).1 hw)]
    exact T.psi_is w
  · exact h.supp w fun hn => (key w).2 hn hw

end GlobalTheory.Mem.Top.TupTieW
end

section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t : RT Y u u', (Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t)) ∧ (Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t)) ∧ (t.relevant ↔ (eRT Z Y u u' t).relevant) ∧ (t.FeqF ↔ (eRT Z Y u u' t).FeqF) ∧ (t.generic ↔ (eRT Z Y u u' t).generic) ∧ t.G = (eRT Z Y u u' t).G ∧ (∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p) ∧ Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t)) ∧ ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w := by
  first | exact @GlobalTheory.Mem.SRe.eRT_keeps_term_data | exact GlobalTheory.Mem.SRe.eRT_keeps_term_data | (intros; apply GlobalTheory.Mem.SRe.eRT_keeps_term_data <;> assumption)
end

section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finX_spectralRedivisionFullChoices : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  first | exact @GlobalTheory.Mem.SRe.finX_reY | exact GlobalTheory.Mem.SRe.finX_reY | (intros; apply GlobalTheory.Mem.SRe.finX_reY <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem untw_set_eq (B : Base) (pl : Finset ℕ) (f : Fr B.toPre) :
    (TwDat.untw B pl).set f = {1, f.del, f.del'} := by
  refine Set.union_eq_left.2 ?_
  rintro _ ⟨w, rfl⟩
  change (if _ then f.del' else f.del) * 1 ∈ _
  rw [mul_one]
  split_ifs
  · exact .inr (.inr rfl)
  · exact .inr (.inl rfl)

theorem recAtG_of_two_passes : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  intro h2v KP Q Q' hK hF hX hS
  have hL := EvG.imp (EvG.inter hF (EvG.inter hX hS)) fun K _ _ _ _ H =>
    (large₂.inter (large₂.inter H.1 (lg_forced K)) (large₂.inter H.2.1 H.2.2))
  refine EvG.imp (EvG.inter (EvG.inter hK.ex hL) (evG_of_ev GlobalTheory.Mem.Top.LayOfCore.lay_of_core)) ?_
  rintro K _ _ _ _ ⟨⟨⟨P, f₀, hO, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩, hlay⟩
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks (S₁ P f₀) (fun F F₀ => S₂ P f₀ F F₀ {1, f₀.del, f₀.del'}) (a₁ _ _)
    (fun F F₀ => a₂ _ _ F F₀ _)
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨⟨h1, hfo⟩, h2, h3⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hO
    ⟨hH₁, by rw [untw_set_eq]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _))
  obtain ⟨C, W, V, S, N, G, c, hQ⟩ := h1 hKP hfo rfl
  obtain ⟨B', f', T', -, -, -, -, -, C', W', V', S', N', G', c', -, hTw, hQ'⟩ :=
    h3 hKP rfl C W V S N G c hQ (h2 hKP rfl C W V S N G c hQ) (fun _ => ∅) (fun _ _ _ => ∅) (by simp)
  obtain ⟨Y, hY, k1, k2, k3, k4⟩ := hlay ⟨B', C', W', V', S', N', G'⟩ f' T' c' (h2v _ c'.real.vol)
  have hTw' : DQ.TwAllAt (Stages.toD7 ⟨B', C', W', V', S', N', G'⟩) Y.nch Y.xd := by
    have e1 : Y.nch = c'.O.nch := by rw [← hY]; rfl
    have e2 : Y.xd = c'.O.xd := by rw [← hY]; rfl
    rw [e1, e2]
    exact hTw
  exact ⟨_, Y, k1, k2, k3, hTw'.twAt, ⟨_, f', T', c', hQ', by rw [hY]⟩, k4, hTw', c'.mtStable⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

section

noncomputable section

namespace GlobalTheory.Mem.R3

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl}

def Dat.IwasawaPlaceIndex (z : Dat X I hX T Wt) : Set X.B.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({X.toD7.plEq w, Formalism.DivisionValues.conjPl (X.toD7.plEq w)} : Set (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))),
    (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0}

def Dat.W1jw (z : Dat X I hX T Wt) : Set X.B.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({X.toD7.plEq w, Formalism.DivisionValues.conjPl (X.toD7.plEq w)} : Set (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))),
    Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
              (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
      (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
        (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0}

def placesWithNonzeroContentOrConj (D : D7) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) : Set D.what₂.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({D.plEq w, Formalism.DivisionValues.conjPl (D.plEq w)} : Set (HeightOneSpectrum (𝓞 D.what₂.LL))), F0 w' j ≠ 0}

theorem Dat.auxiliaryPlaces_eq_union_three_parts (z : Dat X I hX T Wt) (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ) :
    z.W1 F0 = z.IwasawaPlaceIndex ∪ z.W1jw ∪ placesWithNonzeroContentOrConj X.toD7 F0 := by
  ext w
  simp only [Dat.W1, Dat.IwasawaPlaceIndex, Dat.W1jw, placesWithNonzeroContentOrConj, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, w', hw', h | h | h⟩
    · exact Or.inl (Or.inl ⟨j, w', hw', h⟩)
    · exact Or.inl (Or.inr ⟨j, w', hw', h⟩)
    · exact Or.inr ⟨j, w', hw', h⟩
  · rintro ((⟨j, w', hw', h⟩ | ⟨j, w', hw', h⟩) | ⟨j, w', hw', h⟩)
    · exact ⟨j, w', hw', Or.inl h⟩
    · exact ⟨j, w', hw', Or.inr (Or.inl h)⟩
    · exact ⟨j, w', hw', Or.inr (Or.inr h)⟩

theorem Dat.mem_auxiliaryPlaces_iff_three_parts (z : Dat X I hX T Wt) (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ)
    (w : X.B.places.Pl) : w ∈ z.W1 F0 ↔ (w ∈ z.IwasawaPlaceIndex ∨ w ∈ z.W1jw) ∨ w ∈ placesWithNonzeroContentOrConj X.toD7 F0 :=
  Set.ext_iff.mp (z.auxiliaryPlaces_eq_union_three_parts F0) w

end GlobalTheory.Mem.R3

end
end
