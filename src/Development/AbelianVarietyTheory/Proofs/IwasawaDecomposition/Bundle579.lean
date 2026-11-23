module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle801
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProdLevelStdFrameTwoBlockUnipotentLevel
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle553
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevShapeBound

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eq_of_compAt (s : SplitPlace L) {x y : AL L}
    (h : compAt L s.v x = compAt L s.v y) : s.proj x = s.proj y := by
  have key : ∀ z : AL L, s.proj z =
      (Algebra.TensorProduct.lift s.i (AlgHom.id _ (s.v.adicCompletion (maximalRealSubfield L)))
        (fun _ _ => Commute.all _ _)) (compAt L s.v z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]
  rw [key, key, h]

theorem loc_eq_of_comp (s : SplitPlace L) {x y : GAf L n}
    (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v)) :
    s.loc n x = s.loc n y := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hij
  exact proj_eq_of_compAt s hij

end Gen

theorem bound : ∀ (D : D7) (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)), GPlaces D → GrpShape D η J → ∀ κ ∈ J, κ ∈ Umax D.host.E D.R.nV ∧ ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → NG.UniRT s D.R.r (s.loc _ κ) := by
  intro D η J hG hS κ hκ
  obtain ⟨hprod, hpara, huni, hhyp⟩ := hS

  have hloc : ∀ w, ∃ κ' ∈ J, κ' ∈ Umax D.host.E D.R.nV ∧
      (κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) =
        (κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) := by
    intro w
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ w
    refine ⟨κ', hκ', ?_, heq⟩
    by_cases hg : w ∈ gPl D
    · obtain ⟨k, v, s, hsv, hsw⟩ := hG.2.1 w hg
      subst hsv
      have hu := (huni k v s hsw κ' htr).1 hκ'
      exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hu.1.1
    · by_cases hq : w ∈ qPl D η
      · obtain ⟨s, hsv, hs⟩ := hpara w hq
        subst hsv
        have hp := (hs κ' htr).1 hκ'
        exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hp.1
      · refine (hhyp κ' ?_).1 hκ'
        intro u hu
        apply htr u
        rintro rfl
        simp only [Set.mem_compl_iff, not_not, Set.mem_union] at hu
        rcases hu with h | h
        · exact hg h
        · exact hq h
  refine ⟨?_, ?_⟩
  · intro i j
    apply GlobalTheory.FormInner.mem_ALint_of_comp
    intro w
    obtain ⟨κ', -, hU, heq⟩ := hloc w
    refine ⟨(κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)) i j, hU i j, ?_⟩
    have := congrFun (congrFun heq i) j
    simpa only [Matrix.map_apply] using this
  · intro k v s hsw
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ s.v
    have hu := (huni k v s hsw κ' htr).1 hκ'
    rwa [loc_eq_of_comp s heq] at hu

end GlobalTheory.LevShapeBound

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevParaLoc

theorem locM_eq_one_of_ne {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s s' : SplitPlace L)
    {κ : GAf L n} (hκ : TrivOutside {s.v} κ) (h : s'.v ≠ s.v) : NX.locM s' κ = 1 :=
  GlobalTheory.LevGChar.locM_triv s' (B := {s.v}ᶜ) (by rwa [compl_compl]) (by simpa using h)

theorem intLift_one {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 1 = 1 := by
  unfold NX.intLift
  rw [dite_eq_left (v.adicCompletionIntegers (maximalRealSubfield L)).one_mem]
  rfl

theorem intLift_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : NX.intLift v 0 = 0 := by
  unfold NX.intLift
  rw [dite_eq_left (v.adicCompletionIntegers (maximalRealSubfield L)).zero_mem]
  rfl

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem redMat_one {L : Type} [Field L] [NumberField L] [IsCMField L] {r : ℕ}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {R : Type} [CommRing R]
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) :
    NX.redMat v red (1 : Matrix (Fin r) (Fin r) (v.adicCompletion (maximalRealSubfield L))) = 1 := by
  refine Matrix.ext fun a b => ?_
  show red (NX.intLift v ((1 : Matrix (Fin r) (Fin r) _) a b)) = (1 : Matrix (Fin r) (Fin r) R) a b
  by_cases hab : a = b
  · subst hab; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, intLift_one, map_one]
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, intLift_zero, map_zero]

open Classical in
theorem gVal_one (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) :
    NX.gVal D i k b kv s red τ 1 = 1 := by
  have htop : NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV)
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))) = 1 :=
    Matrix.submatrix_one _ (Fin.castLE_injective _)
  have hgl : NX.glOf (1 : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = 1 :=
    Units.ext (NX.glOf_val _ (by simp))
  have hpsi : NX.psiUTot D i b 1 = 1 := by
    unfold NX.psiUTot
    rw [dite_eq_left (one_mem _)]
    have e : (⟨1, one_mem _⟩ : D.nexp.U) = 1 := rfl
    rw [e, map_one, Units.val_one]
  have hd : red (NX.intLift s.v (NX.detT D.R.r
      (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))))) = 1 := by
    rw [GlobalTheory.LevGChar.detT_one', intLift_one, map_one]
  unfold NX.gVal
  rw [htop, redMat_one, hgl, Pi.mulSingle_one, hpsi, map_one, one_mul]
  split_ifs with h
  · have hu : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)
    rw [hu, map_one, Units.val_one, map_one]
  · exact absurd (hd ▸ isUnit_one) h

theorem resRep_one {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    NX.resRep s s.w 1 - 1 ∈ s.w.asIdeal := by
  have hu := GlobalTheory.LevGChar.i_resRep s 1 (map_one _)
  show Valued.v (s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L)) < 1
  have e : s.i (((NX.resRep s s.w 1 - 1 : 𝓞 L)) : L) = s.i ((NX.resRep s s.w 1 : 𝓞 L) : L) - 1 := by
    push_cast; rw [map_sub, map_one]
  rw [e]
  exact hu

end GlobalTheory.LevParaLoc

namespace GlobalTheory.LevParaLoc

theorem mem_iff (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (P : PlE D.host)
    (hP : P ∈ M.QP ∨ P ∈ M.DP) (hG : ∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v)
    (hQ : ∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (hD : ∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P)
    (κ : GAf D.host.E D.R.nV) (hκ : TrivOutside {(M.sp P).v} κ) :
    κ ∈ M.J ↔ NG.ParaRT (M.sp P) D.R.r ((M.sp P).loc _ κ) := by
  have hpar : ((∀ P'' ∈ M.QP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ)) ∧
      (∀ P'' ∈ M.DP, NX.InParah (M.sp P'').v D.R.r (NX.locM (M.sp P'') κ))) ↔
      NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) := by
    constructor
    · rintro ⟨h1, h2⟩
      rcases hP with h | h
      exacts [h1 P h, h2 P h]
    · intro h
      refine ⟨fun P'' hP'' => ?_, fun P'' hP'' => ?_⟩
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hQ P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
      · by_cases hv : (M.sp P'').v = (M.sp P).v
        · rw [hD P'' hP'' hv]; exact h
        · rw [locM_eq_one_of_ne _ _ hκ hv]; exact NX.inParah_one _ _
  have hg : ∀ kv, NX.InLevG (M.sp (NX.pG D kv)).v D.R.r (NX.locM (M.sp (NX.pG D kv)) κ) := fun kv => by
    rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact NX.inLevG_one _ _
  rw [M.J_mem κ]
  constructor
  · rintro ⟨hU, -, h1, h2⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).2 hU, (hpar.1 ⟨h1, h2⟩).2⟩
  · rintro ⟨hGL, hll⟩
    exact ⟨(GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff _ hκ).1 hGL, hg,
      hpar.2 ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hGL).1 a b, hll⟩⟩

theorem levelPara_loc : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (ek : NX.Kk D i k →+* ℂ) (P : PlE D.host) (ξ : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (P ∈ M.QP ∨ P ∈ M.DP) → ¬ (P ∈ M.QP ∧ P ∈ M.DP) → (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v) → (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.QP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' e₀ u = 1) → (∀ P'' ∈ M.DP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀) u = 1) → (P ∈ M.QP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ P e₀ a).1)) → (P ∈ M.DP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e₀ else -e₀) a).1)) → NG.LevelPara M.J (cx ek M.χ) (M.sp P) D.R.r ξ := by
  intro D i j b k Q ψ e₀ W₀ _ _ ρ₀ τ M ek P ξ hP hPn hG hQ hD hψ hδ hξQ hξD
  refine ⟨fun κ hκ => mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ, ?_⟩
  intro κ h hκ u hu
  have hpara := (mem_iff D i j b k Q ψ e₀ W₀ ρ₀ τ M P hP hG hQ hD κ hκ).1 h
  have hUm : κ ∈ Umax D.host.E D.R.nV := ((M.J_mem κ).1 h).1
  have hx : NX.InParah (M.sp P).v D.R.r (NX.locM (M.sp P) κ) :=
    ⟨fun a b => (GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hpara.1).1 a b, hpara.2⟩
  have hv1 : Valued.v (NX.detT D.R.r (NX.locM (M.sp P) κ)) = 1 :=
    GlobalTheory.LevGChar.i_detT_one _ D.R.r _ (NX.locM (M.sp P) κ⁻¹)
      (by rw [← GlobalTheory.LevGChar.locM_mul, mul_inv_cancel, GlobalTheory.LevGChar.locM_one])
      (fun a b => GlobalTheory.LevGChar.locM_int _ (inv_mem hUm) a b) hx
  have hu' : (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) =
      NX.detT D.R.r (NX.locM (M.sp P) κ) := hu
  have hw : (M.sp P).w = P := M.sp_w P (by rcases hP with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  have hclose : Valued.v ((u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) -
      (M.sp P).i ((NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)) : 𝓞 D.host.E) : D.host.E)) < 1 := by
    have := GlobalTheory.LevGChar.i_resRep (M.sp P) _ hv1
    rw [hw] at this
    rw [hu', ← Valuation.map_neg, neg_sub]
    exact this
  have hnm := GlobalTheory.LevGChar.resRep_not_mem (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ))
  have hvu : Valued.v (u : (M.sp P).v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by rw [hu']; exact hv1
  have hGp : ∏ kv, NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (NX.locM (M.sp (NX.pG D kv)) κ) = 1 :=
    Finset.prod_eq_one fun kv _ => by rw [locM_eq_one_of_ne _ _ hκ (hG kv)]; exact gVal_one _ _ _ _ _ _ _ _
  have offQ : ∀ P'' ∈ M.QP, P'' ≠ P → NX.ofOk D i k (NX.tameVal ψ P'' e₀
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hQ P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inl hP'')
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hψ P'' hP'' _ h1, Units.val_one, map_one]
  have offD : ∀ P'' ∈ M.DP, P'' ≠ P → NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀)
      (NX.resRep (M.sp P'') P'' (NX.detT D.R.r (NX.locM (M.sp P'') κ)))).1 = 1 := by
    intro P'' hP'' hne
    have hv : (M.sp P'').v ≠ (M.sp P).v := fun e => hne (hD P'' hP'' e)
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inr (Or.inl hP''))
    rw [locM_eq_one_of_ne _ _ hκ hv, GlobalTheory.LevGChar.detT_one']
    have h1 := resRep_one (M.sp P'')
    rw [hw''] at h1
    rw [hδ P'' hP'' _ h1, Units.val_one, map_one]
  apply Units.ext
  rw [cx_apply, M.chi_eq κ h, hGp, one_mul]
  rcases hP with hPQ | hPD
  · have hPD : P ∉ M.DP := fun h' => hPn ⟨hPQ, h'⟩
    rw [Finset.prod_eq_single_of_mem P hPQ offQ,
      Finset.prod_eq_one (fun P'' hP'' => offD P'' hP'' (fun e => hPD (e ▸ hP''))), mul_one]
    exact (hξQ hPQ u _ hnm hvu hclose).symm
  · have hPQ : P ∉ M.QP := fun h' => hPn ⟨h', hPD⟩
    rw [Finset.prod_eq_single_of_mem P hPD offD,
      Finset.prod_eq_one (fun P'' hP'' => offQ P'' hP'' (fun e => hPQ (e ▸ hP''))), one_mul]
    exact (hξD hPD u _ hnm hvu hclose).symm

end GlobalTheory.LevParaLoc
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevProd

open GlobalTheory.MtInProd
open Formalism.L2.NX (locM InLevG InParah inParah_one)
open Classical

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eA (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    s.proj (eA L v) = if s.v = v then 1 else 0 := by
  show s.i 1 * (idemF (L := L) v) s.v = _
  rw [map_one, one_mul, idemF_apply]

theorem locM_cut (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n) :
    locM s (cutGA (eA_mul v) (conj_eA v) κ) = if s.v = v then locM s κ else 1 := by
  show ((cutGA (eA_mul v) (conj_eA v) κ).1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj = _
  rw [cutGA_val, map_cutMat, proj_eA]
  split_ifs
  · rw [cutMat_one_left]; rfl
  · rw [cutMat_zero_left]

theorem inLevG_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) :
    InLevG v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) := by
  refine ⟨inParah_one v r, fun a b _ _ => ⟨fun hba => ?_, fun hab => ?_⟩⟩
  · have h : a ≠ b := fun e => by subst e; exact lt_irrefl _ hba
    rw [Matrix.one_apply_ne h, map_zero]
    exact WithZero.zero_lt_coe _
  · subst hab
    rw [Matrix.one_apply_eq, sub_self, map_zero]
    exact WithZero.zero_lt_coe _

end Gen

theorem main : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  intro D X i b k Q ψ hA j κ hκ v
  obtain ⟨hU, hG, hQ, hD⟩ := ((cell X b hA j).J_mem κ).1 hκ
  refine ⟨cutGA (eA_mul v) (conj_eA v) κ, ((cell X b hA j).J_mem _).2 ⟨cutGA_mem_Umax _ _ (eA_mem v) hU, fun kv => ?_,
    fun P hP => ?_, fun P hP => ?_⟩, triv_cut_eA v κ, cut_eA_at v κ⟩
  · rw [locM_cut]; split_ifs
    · exact hG kv
    · exact inLevG_one _ _
  · rw [locM_cut]; split_ifs
    · exact hQ P hP
    · exact inParah_one _ _
  · rw [locM_cut]; split_ifs
    · exact hD P hP
    · exact inParah_one _ _

end GlobalTheory.LevProd

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.CoefMatch

theorem vvmatch_repr {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) (y : VV K lam) (i : VVIdx lam) :
    (Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge).repr (mapVV φ lam y) i = φ ((bVV K lam).repr y i) := by
  classical
  set B' := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge
  have hy : mapVV φ lam y = ∑ k, φ ((bVV K lam).repr y k) • B' k := by
    conv_lhs => rw [← (bVV K lam).sum_repr y]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.mk_apply]
  rw [hy, Module.Basis.repr_sum_self]

theorem wtMatch_of_coef : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {ι : Type} [Fintype ι] {K : Type} [Field K] (φ : K →+* ℂ) (emb : ι → L →+* K)
    (lam : ι → DomWeight n) {W₀ W' : Type} [AddCommGroup W₀] [Module K W₀]
    [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀)
    (ρ' : Representation ℂ (GQ L n) W') (T : W₀ ≃ₗ[K] VV K lam),
    (∀ γ x, T (ρ₀ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) →
    ∀ (T' : W' ≃ₗ[ℂ] VV ℂ lam),
    (∀ γ x, T' (ρ' γ x) =
      rhoVr (fun t => φ.comp (emb t)) lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T' x)) →
    GlobalTheory.LevCmp.WtMatch φ ρ₀ ρ' := by
  intro L _ _ _ n ι _ K _ φ emb lam W₀ W' _ _ _ _ ρ₀ ρ' T hT T' hT'
  classical
  set B' := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge with hB'
  refine ⟨VVIdx lam, inferInstance, inferInstance, (bVV K lam).map T.symm, B'.map T'.symm, fun γ => ?_⟩
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp only [Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  rw [hT', hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hj : B' j = mapVV φ lam (bVV K lam j) := Module.Basis.mk_apply _ _ _
  rw [hj, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hB', vvmatch_repr]

end GlobalTheory.CoefMatch
end

section

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar




theorem yRel_of_pin : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))) (m : Moved (oL x L)), m.z = datL x L → m.Coh → ∀ (s : Side0 (oL x L)) (r : ReadPk m s), r.Pin →
      ∀ Y : YT x L s.p0, HEq Y r.Y → YRel L Y := by
  intro K B f T w P x L m hz hC s r hP Y hY
  have hR := CopyRead.repOf_heq x.coh x.r x.pin hC r hP
  obtain ⟨z, intersectionNumber_baseChange, exAt, inGeo, Xg, tr, core, eta, W1, y, tup, t, tA⟩ := m
  dsimp only at hz
  subst hz
  obtain ⟨rY, rZ, rtup, rtupT, rPY, rPW, rjA, rjA0, reMt⟩ := r
  dsimp only at hY
  cases hY
  refine ⟨(by with_unfolding_all exact (hR :)), ?_, ?_⟩
  · intro i y
    have heW := hP.eW
    have hf : HEq t.lf.eW x.m.t.lf.eW := hC.eW.trans x.coh.eW.symm
    have h3 : @Eq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) :=
      @eq_of_heq (type_of% t.lf.eW) t.lf.eW ((by with_unfolding_all exact (x.m.t.lf.eW :))) ((by with_unfolding_all exact (hf :)))
    with_unfolding_all
      exact (heW i y).trans ((heq_of_eq (congrArg (fun g => g i y) h3)).trans (x.pin.eW i y).symm)
  · intro μ h i y
    have hjMt := hP.jMt
    have hf : HEq t.lf.jMt x.m.t.lf.jMt := hC.jMt.trans x.coh.jMt.symm
    have h3 : @Eq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) :=
      @eq_of_heq (type_of% t.lf.jMt) t.lf.jMt ((by with_unfolding_all exact (x.m.t.lf.jMt :))) ((by with_unfolding_all exact (hf :)))
    exact (by with_unfolding_all exact (((hjMt μ h i y).trans ((heq_of_eq (congrArg (fun g => g μ i y) h3)).trans (x.pin.jMt μ h i y).symm)) :))

end GlobalTheory.HeightCounting.Fin3

end
end
