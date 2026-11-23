module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle309
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle300
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle180
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle161
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdMove
variable {D : D7}

theorem moves_exists (V : HSp D) (g : GA D V) : ∃ N, Moves V rfl g N := by
  obtain ⟨Λ, hΛ, -, -, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (GlobalTheory.SplitMove.intSub D V.rank)
    (finHom V g) (GlobalTheory.SplitMove.intSub_fg _) (GlobalTheory.SplitMove.intSub_span _)
  have inv : ∀ y, (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  have inv' : ∀ y, (finHom V g).1 *ᵥ ((finHom V g⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec]
  have ent : ∀ (x : Fin V.rank → D.host.E) i,
      Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E
        (((finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x) i) =
      (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    intro x i

    simp only [GlobalTheory.AdForm.finM, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.reindex_apply,
    finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
  refine ⟨Λ, fun x => ?_⟩
  rw [← SetLike.mem_coe, hΛ, GlobalTheory.SplitMove.coe_intSub]
  change GlobalTheory.AdLat.fv D.host.F x ∈ (finHom V g).1.mulVec '' _ ↔ _
  constructor
  · rintro ⟨y, hy, hxy⟩ i
    rw [← ent, ← hxy, inv]
    exact (GlobalTheory.SplitMove.hat_intVec_iff D V.rank y).1 hy i
  · intro hx
    refine ⟨(finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x, (GlobalTheory.SplitMove.hat_intVec_iff D V.rank _).2 fun i => ?_, inv' _⟩
    rw [ent]; exact hx i

theorem isSdLat_of (V : HSp D) (hV : V.gram = 1) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : IsSelfDualC V N) : Formalism.L2.Col.IsSdLat N := by
  refine ⟨h.1, ?_⟩
  ext x
  rw [h.2 x]
  simp only [Formalism.HermitianLatticesTheory.IsUnimodular, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  have e : Formalism.L2.Col.hStd D.host.E V.rank y x = ∑ i, ∑ j, star (y i) * V.gram i j * x j := by
    rw [hV]
    simp [Formalism.L2.Col.hStd, Matrix.one_apply]
  rw [e]

theorem std_moved_lattice : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), V.gram = 1 → (∀ g : GA D V, ∃ N, Moves V hn g N) ∧ ∀ (g : GA D V) N, Moves V hn g N → Formalism.L2.Col.IsSdLat N ∧ ∃ Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), (Λ : Set (Fin V.rank → D.host.E)) = latFr V hn N ∧ IsSelfDualC V Λ := by
  intro D V n hn hV
  subst hn
  refine ⟨fun g => moves_exists V g, fun g N hN => ?_⟩
  have hsd := GlobalTheory.SplitMove.selfDual_move V hV g N hN
  refine ⟨isSdLat_of V hV N hsd, N, ?_, hsd⟩
  ext x
  first | exact Iff.rfl | simp [GlobalTheory.AdForm.latFr]

end GlobalTheory.StdMove
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.semicharacter_sq_eq_one_on_halfA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, alV D.host.d sc (embH (tauE D) δ x') * alV D.host.d sc (embH (tauE D) δ x') = 1 := by
  first | exact @GlobalTheory.AdForm.HalfASign.alV_mul_self_halfA | exact GlobalTheory.AdForm.HalfASign.alV_mul_self_halfA | (intros; apply GlobalTheory.AdForm.HalfASign.alV_mul_self_halfA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem star_comp_const_smul_eq_conj_smul {α : Type*} (a : ℂ) (F : α → ℂ) :
    (fun x => star ((a • F) x)) = (starRingEnd ℂ a) • (fun x => star (F x)) := by
  funext x
  simp [star_mul']

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi



theorem evalAll_rows : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → _root_.GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → EvalAll X h θ M J χ t v₀ ∧ ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
  intro hDS hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
  have hnorm : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
    intro τ
    obtain ⟨c, -, hc⟩ := hConj
    have h1 := (X.low (X.pl.symm τ)).1
    rw [← (c τ).norm_map, hc τ]
    exact h1
  have hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ; rw [h0, norm_zero] at this; exact zero_ne_one this
  have hfun := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hCusp D X h θ S M J χ t hθ hMat
  obtain ⟨f, hf⟩ : ∃ f : MultT θ M J χ → L2X X, ∀ T : MultT θ M J χ, ((f T : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) :=
    ⟨fun T => ((hfun T.1 T.2 (PiTensorProduct.tprod ℂ v₀)).2).toLp _, fun T => MemLp.coeFn_toLp _⟩
  have hmem : ∀ T : MultT θ M J χ, star (f T) ∈ HHX X := fun T =>
    GlobalTheory.T.conj_translated_evaluation_mem_all_rows_space hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj T.1 T.2 (f T) (hf T)
  have hstar : ∀ T : MultT θ M J χ, ((star (f T) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := fun T => by
    filter_upwards [Lp.coeFn_star (f T), hf T] with x h1 h2
    rw [h1, Pi.star_apply, h2]
  have e1 : ∀ T T' : MultT θ M J χ, (fun x => star (evS X h t ((T + T').1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) +
        (fun x => star (evS X h t (T'.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro T T'
    rw [Submodule.coe_add, LinearMap.add_apply]
    funext x
    exact star_add _ _
  have e2 : ∀ (a : ℂ) (T : MultT θ M J χ), (fun x => star (evS X h t ((a • T).1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (starRingEnd ℂ a) • (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro a T
    rw [Submodule.coe_smul, LinearMap.smul_apply]
    generalize T.1 (PiTensorProduct.tprod ℂ v₀) = F
    exact star_comp_const_smul_eq_conj_smul a (evS X h t F)
  let j : MultT θ M J χ →ₗ⋆[ℂ] HHX X :=
    { toFun := fun T => ⟨star (f T), hmem T⟩
      map_add' := fun T T' => by
        apply Subtype.ext
        show star (f (T + T')) = star (f T) + star (f T')
        apply Lp.ext
        refine (hstar (T + T')).trans ?_
        rw [e1]
        exact ((hstar T).add (hstar T')).symm.trans (Lp.coeFn_add _ _).symm
      map_smul' := fun a T => by
        apply Subtype.ext
        rw [Submodule.coe_smul]
        apply Lp.ext
        refine (hstar (a • T)).trans ?_
        rw [e2]
        exact ((hstar T).const_smul (starRingEnd ℂ a)).symm.trans (Lp.coeFn_smul _ _).symm }
  have hj : ∀ T, (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := hstar
  refine ⟨⟨j, ⟨?_, ?_⟩, hj⟩, hnorm⟩
  · rw [injective_iff_map_eq_zero]
    intro T hT
    have h0 : (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] 0 := by
      rw [hT]; exact Lp.coeFn_zero _ _ _
    have hev : evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 := by
      filter_upwards [hj T, h0] with x h1 h2
      rw [h2] at h1
      have h3 := congrArg star h1
      rw [star_star] at h3
      rw [← h3]
      exact star_zero _
    exact Subtype.ext (GlobalTheory.T.cuspFormMap_eq_zero_of_translatedEval_ae_zero D X h θ S M J χ t v₀ hθ hne T.1 T.2 hev)
  · intro ψ
    have hψ : star (star (ψ : L2X X)) ∈ HHX X := by rw [star_star]; exact ψ.2
    obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.conj_row_eq_translated_evaluation_cusp_form_map hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
      (star (ψ : L2X X)) hψ
    refine ⟨⟨T, hT⟩, ?_⟩
    apply Subtype.ext
    apply Lp.ext
    refine (hj ⟨T, hT⟩).trans ?_
    filter_upwards [Lp.coeFn_star (ψ : L2X X), hTe] with x h2 h3
    rw [h2, Pi.star_apply] at h3
    rw [← h3, star_star]

end GlobalTheory.Core.Mi
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section

namespace GlobalTheory.AdForm.ChiCont



theorem chi_continuous : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ) := by
  intro B X I hI hP l Z u a Ch A hA i hi β
  obtain ⟨n, hn, hfin⟩ := hA.fin i hi β
  let Vs : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) :=
    {v | ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)}
  have hVs : Vs.Finite := by
    have e : Vs = ⋃ P : SBof I a, {v | Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)} := by
      ext v; simp [Vs]
    rw [e]
    refine Set.finite_iUnion fun P => Set.Subsingleton.finite ?_
    intro v hv w hw
    exact HeightOneSpectrum.ext (hv.trans hw.symm)
  have hbad : ∀ v ∈ A.bad i, v ∈ Vs := fun v hv => GlobalTheory.T.exists_badPrime_over_chart_bad_place I hI hP l Z a v (hA.bad_le i hi v hv)
  have hker := GlobalTheory.T.levelCharacter_trivial_near_one_of_local_bad_places (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi)
    (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev Vs hVs hbad (by
    rintro v ⟨P, hv⟩
    obtain ⟨N, hN⟩ := GlobalTheory.T.levelCharacter_eq_one_of_deep_at_splitBadPlace I hI hP l Z a (B.T u) i hi (A.bad i) (A.K i hi β).lev n hn hfin P v hv
    have h2 := GlobalTheory.T.eventually_nhds_one_adelicMatrixCongruentOneAtPrime (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) ((I.rec7 l Z).R.N i) N
      (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    exact h2.mono fun w hw x hx hxw => hN x hx w hw hxw)

  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  haveI : IsTopologicalGroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  let Φ : A.U i β →* GL (Fin ((I.rec7 l Z).R.N i)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    (GlobalTheory.ClassSumLevel.finGLHom ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi)).comp (A.U i β).subtype
  have hΦc : Continuous Φ := (GlobalTheory.ClassSumLevel.continuous_finGLHom _ _).comp continuous_subtype_val
  have ht : Tendsto Φ (nhds 1) (nhds 1) := by
    have := hΦc.tendsto 1
    rwa [map_one] at this
  have hev : ∀ᶠ g in nhds (1 : A.U i β), (1 : ℂˣ) = A.chi i β g := by
    filter_upwards [ht.eventually hker] with g hg
    obtain ⟨κ, hκ⟩ := ((hA.U i hi β g.1).1 g.2).2
    rw [hA.chi i hi β g κ hκ]
    exact (hg κ (Units.ext (hκ.trans rfl))).symm
  have hχ : Continuous (A.chi i β) := by
    refine continuous_of_continuousAt_one (A.chi i β) ?_
    exact continuousAt_const.congr hev
  exact Units.continuous_val.comp hχ

end GlobalTheory.AdForm.ChiCont
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainStep_vector_exists_nonzero_vacuum : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → (∃ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f) ∧ ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → IsThetaFunO c.ψ s.V s'.V f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO c.ψ s.V s'.V) c.θ τ (cplxO (cart s.M τ) (cart s'.M τ)) f) ∧ ∀ φ, IsThetaFunO c.ψ s.V s'.V (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f φ) := by
  first | exact @GlobalTheory.ChainOnto.StepVecOK.stepVec_exists_vac | exact GlobalTheory.ChainOnto.StepVecOK.stepVec_exists_vac | (intros; apply GlobalTheory.ChainOnto.StepVecOK.stepVec_exists_vac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaSplitPairing

theorem hO_ofAdj_right {D : D7} (L S : HSp D) (X : WO L S) (z : Mx D L.rank S.rank) :
    hO L S X (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S z) = incA D (D.host.xi0⁻¹) * (z ⬝ X).trace := by
  rw [hO_eq_trace, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel, trace_smul, smul_eq_mul]
  rw [GlobalTheory.DualPairCheck.cA_incA, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg]

theorem map_trace {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {m : ℕ} (M : Mx D m m) : p.π M.trace = (M.map p.π).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

theorem key : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (s : k) (z₀ : Fin L''.rank → k), s ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * s)) • (fun i => p.pr (ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : Frame k S.rank n) (FL : Frame k L.rank Unit) (FL'' : Frame k L''.rank Unit), (∀ r, FL.β r () = s * p.pr (ζ r)) → (∀ r, FL''.β r () = z₀ r) → ∀ (x : Matrix Unit n k) (a : Matrix n Unit k), p.π (hO L S (p.up FL FS a) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * p.up FS FL'' x))) = -(∑ r, x () r * a r ()) := by
  intro D k _ _ _ _ p L S L'' ζ τ s z₀ hs hτ n _ _ FS FL FL'' hFL hFL'' x a
  rw [hO_ofAdj_right, map_mul, map_trace]
  have hxi : p.π (incA D D.host.xi0⁻¹) = p.xi⁻¹ := by
    change (p.π.comp (incA D)) D.host.xi0⁻¹ = ((p.π.comp (incA D)) D.host.xi0)⁻¹
    exact map_inv₀ _ _
  have hr : (rat τ : Mx D L.rank L''.rank).map p.π = τ.map p.pr := rfl
  have hu : ∀ {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
      (F₁ : Frame k S.rank Y') (F₂ : Frame k T.rank Y) (m : Matrix Y Y' k),
      (p.up F₁ F₂ m : Mx D T.rank S.rank).map p.π = F₂.β * m * F₁.γ := by
    intro Y Y' _ _ _ _ S T F₁ F₂ m
    ext i j
    exact p.π_ι _
  have hcol : τ.map p.pr * FL''.β = (-p.xi) • FL.β := by
    ext r u
    have h1 := congrFun hτ r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mul_apply, hFL'', Matrix.smul_apply, smul_eq_mul, hFL, h1]
    ring
  have hγ : FL.γ * (τ.map p.pr * FL''.β) = (-p.xi) • (1 : Matrix Unit Unit k) := by
    rw [hcol, Matrix.mul_smul, FL.γβ]
  rw [hxi, Matrix.map_mul, Matrix.map_mul, hr, hu, hu]
  have e1 : τ.map p.pr * (FL''.β * x * FS.γ) * (FS.β * a * FL.γ) = (τ.map p.pr * FL''.β) * x * a * FL.γ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc FS.γ, FS.γβ, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hγ]
  have hx := Witness.xi_ne p
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
  simp only [Matrix.smul_apply, smul_eq_mul, neg_mul, Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum, mul_neg,
    inv_mul_cancel_left₀ hx]

end GlobalTheory.KappaSplitPairing
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaModel

def finv {k : Type} [Field k] [MeasurableSpace k] {n : Type} [Fintype n] (ψk : AddChar k Circle) (ν : Measure k) (C : ℂ)
    (Φ : Matrix Unit n k → ℂ) (x : Matrix n Unit k) : ℂ :=
  C * ∫ η : n → k, Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ) ∂(Measure.pi fun _ => ν)

end GlobalTheory.KappaModel

namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem integrable_row (ψk : AddChar k Circle) (hψ : Continuous ψk) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Φ : Matrix Unit n k → ℂ} (hΦ : Φ ∈ SB (Matrix Unit n k)) (x : Matrix n Unit k) :
    Integrable (fun η : n → k => Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ)) (Measure.pi fun _ => ν) := by
  have := secondCountable k
  have := t2Space k
  let e : (n → k) ≃ₜ Matrix Unit n k :=
    { toFun := fun η => Matrix.of fun _ r => η r
      invFun := fun M => M ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h1 : Continuous fun η : n → k => Φ (Matrix.of fun _ r => η r) := hΦ.1.continuous.comp e.continuous
  have h2 : HasCompactSupport fun η : n → k => Φ (Matrix.of fun _ r => η r) := hΦ.2.comp_homeomorph e
  refine Continuous.integrable_of_hasCompactSupport (h1.mul ?_) h2.mul_right
  exact continuous_subtype_val.comp (hψ.comp (by fun_prop))

theorem finv_add (ψk : AddChar k Circle) (hψ : Continuous ψk) (ν : Measure k) [ν.IsAddHaarMeasure] (C : ℂ)
    {Φ Ψ : Matrix Unit n k → ℂ} (hΦ : Φ ∈ SB (Matrix Unit n k)) (hΨ : Ψ ∈ SB (Matrix Unit n k)) :
    finv ψk ν C (Φ + Ψ) = finv ψk ν C Φ + finv ψk ν C Ψ := by
  funext x
  simp only [finv, Pi.add_apply, add_mul]
  rw [integral_add (integrable_row ψk hψ ν hΦ x) (integrable_row ψk hψ ν hΨ x), mul_add]

theorem finv_smul (ψk : AddChar k Circle) (ν : Measure k) (C a : ℂ) (Φ : Matrix Unit n k → ℂ) :
    finv ψk ν C (a • Φ) = a • finv ψk ν C Φ := by
  funext x
  simp only [finv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  ring

theorem finv_trans (ψk : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (C : ℂ) (x : Matrix Unit n k)
    {Φ Φ' : Matrix Unit n k → ℂ} (h : ∀ t, Φ' t = Φ (t + x)) (a : Matrix n Unit k) :
    finv ψk ν C Φ' a = (ψk (-(∑ r, x () r * a r ())) : ℂ) * finv ψk ν C Φ a := by
  have := secondCountable k
  simp only [finv, h]
  rw [mul_left_comm]
  congr 1
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ (fun r => -(x () r))]
  congr 1
  funext η
  have e1 : (Matrix.of fun _ r => (η + fun r => -(x () r)) r : Matrix Unit n k) + x = Matrix.of fun _ r => η r := by
    ext i j; simp [Subsingleton.elim i ()]
  rw [e1]
  have e2 : (η + fun r => -(x () r)) ⬝ᵥ (fun r => a r ()) = (η ⬝ᵥ fun r => a r ()) + -(∑ r, x () r * a r ()) := by
    simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
  rw [e2, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem finv_mod (ψk : AddChar k Circle) (ν : Measure k) (C : ℂ) (t₀ : Matrix n Unit k)
    {Φ Φ' : Matrix Unit n k → ℂ} (h : ∀ t, Φ' t = (ψk (∑ r, t () r * t₀ r ()) : ℂ) * Φ t) (a : Matrix n Unit k) :
    finv ψk ν C Φ' a = finv ψk ν C Φ (a + t₀) := by
  simp only [finv, h]
  congr 1
  congr 1
  funext η
  have e : (η ⬝ᵥ fun r => (a + t₀) r ()) = (η ⬝ᵥ fun r => a r ()) + ∑ r, η r * t₀ r () := by
    simp [dotProduct, mul_add, Finset.sum_add_distrib]
  rw [e, AddChar.map_add_eq_mul, Circle.coe_mul]
  simp only [Matrix.of_apply]
  ring

end GlobalTheory.KappaModel

namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

theorem heis_comp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (L S L'' : HSp D) (κ : WO S L'' → WO L S)
    (hadd : ∀ w w', κ (w + w') = κ w + κ w') (hs : ∀ w w', symplO L S (κ w) (κ w') = symplO S L'' w w')
    (u : WO S L'') (f : WO L S → ℂ) :
    (fun w => heisO ψ L S (κ u) f (κ w)) = heisO ψ S L'' u (fun w => f (κ w)) := by
  funext w
  simp only [heisO, symplOH, hs, hadd]

theorem exists_frame_col {k : Type} [Field k] {N : ℕ} (hN : N = 1) (z₀ : Fin N → k) (hz : z₀ ≠ 0) :
    ∃ F : Frame k N Unit, ∀ r, F.β r () = z₀ r := by
  let i₀ : Fin N := ⟨0, by omega⟩
  have hu : ∀ i : Fin N, i = i₀ := fun i => Fin.ext (by omega)
  have h0 : z₀ i₀ ≠ 0 := fun h => hz (funext fun i => by rw [hu i]; exact h)
  refine ⟨⟨Matrix.of fun r _ => z₀ r, Matrix.of fun _ _ => (z₀ i₀)⁻¹, ?_, ?_⟩, fun _ => rfl⟩
  · ext i j
    rw [hu i, hu j, Matrix.mul_apply, Matrix.one_apply_eq]
    simp [h0]
  · ext i j
    rw [Matrix.mul_apply, Subsingleton.elim i j, Matrix.one_apply_eq, Fintype.sum_eq_single i₀ fun x hx => absurd (hu x) hx]
    simp [h0]

end GlobalTheory.KappaModel
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedLevel_relIndex_eq_prod_parabolicIndices : ∀ (D : D7) (c : Com D) (w : Twist D) (j : ℕ) (s : PiLocalization₂ D), w.Is c → j ≤ D.R.m → IsStage c w j s → ∀ hr χ ξ, Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L ≤ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ∧ (((Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L).relIndex (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) : ℕ) : ℝ) = ∏ PP ∈ w.Q, idxQ PP j := by
  first | exact @GlobalTheory.TwistIndex.relIndex_twist | exact GlobalTheory.TwistIndex.relIndex_twist | (intros; apply GlobalTheory.TwistIndex.relIndex_twist <;> assumption)
end
