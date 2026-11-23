module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle492
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle944
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle939
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle940
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle938
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle869
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle599
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle213
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.ClassSumPrinc

theorem ratF_injective {D : D7} (S : HSp D) : Function.Injective (Bridge.ratF S) := by
  refine (injective_iff_map_eq_one _).2 fun γ hγ => ?_
  have h1 : GlobalTheory.ClassRegroup.finPt S (γ : GA D S) = 1 := by
    show (GlobalTheory.ClassRegroup.finEquiv S).symm ((finHom S).rangeRestrict (γ : GA D S)) = 1
    have : (finHom S).rangeRestrict (γ : GA D S) = 1 := hγ
    rw [this, map_one]
  exact Subtype.ext (GlobalTheory.ClassRegroup.eq_one_of_finPt S γ.2 h1)

end GlobalTheory.ClassSumPrinc

namespace GlobalTheory.ClassSumPrinc

theorem symm_finPt {D : D7} (S : HSp D) {k : GA D S} (hk : k ∈ GfC S) :
    (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S k) : GfC S) : GA D S) = k := by
  have : (GlobalTheory.ClassRegroup.finEquiv S) ⟨k, hk⟩ = finPt S k := rfl
  rw [← this, MulEquiv.symm_apply_apply]

theorem inner_sum {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) (ω : PairRep S T)
    {Fs : Finset (Bridge.Gf S)} (hF : ∀ u ∈ Fs, u ∈ B.levJ ψ) {κ : ℂ}
    (hκ : ∀ P : Links.PolF D T.rank S.rank,
      ∑ u ∈ Fs.attach, ((B.levLam ψ ⟨u.1, hF u.1 u.2⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u.1 : GfC S) : GA D S), 1) (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) P) =
      κ • B.F.fock (B.vecFlat ψ) P)
    {F : Bridge.Gf S → Links.PolF D T.rank S.rank} (hlaw : B.HasLaw ψ F) {x : GA D S} (hx : x ∈ GfC S) (g : GA D T) :
    ∑ u ∈ Fs, series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)
        (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) (F (finPt S x * u)) g =
      κ * series B.F ω (B.vecFlat ψ) x (F (finPt S x)) g := by
  have hu : ∀ u (hu : u ∈ Fs), series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ)
      (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) (F (finPt S x * u)) g =
      ω (x, g) (((B.levLam ψ ⟨u, hF u hu⟩ : ℂˣ) : ℂ) •
        ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), 1)
          (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (F (finPt S x)))) 0 := by
    intro u hu
    have e1 : F (finPt S x * u) = ((B.levLam ψ ⟨u, hF u hu⟩ : ℂˣ) : ℂ) • F (finPt S x) := by
      have := hlaw 1 (finPt S x) ⟨u, hF u hu⟩
      rw [map_one, one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply] at this
      exact this
    have e2 : (((GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x * u) : GfC S) : GA D S) =
        x * (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S) := by
      have e3 := map_mul (GlobalTheory.ClassRegroup.finEquiv S).symm (finPt S x) u
      rw [e3, Subgroup.coe_mul, symm_finPt S hx]
    rw [series_apply, e2]
    simp only [e1, map_smul]
    have e4 : ω (x * (((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), g) =
        ω (x, g) * ω ((((GlobalTheory.ClassRegroup.finEquiv S).symm u : GfC S) : GA D S), 1) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    have e5 := LinearMap.congr_fun e4 (B.F.fock ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (F (finPt S x)))
    rw [Module.End.mul_apply] at e5
    simp only [e5]
  rw [← Finset.sum_attach Fs, Finset.sum_congr rfl fun u _ => hu u.1 u.2]

  rw [← Finset.sum_apply, ← map_sum, hκ, map_smul, Pi.smul_apply, smul_eq_mul, series_apply]

theorem classSum_princ_eq : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (m : ℕ) (h₀ : Fin m → GA D S), IsClassSystem S ((GlobalTheory.FlatVecSum.princ B).levJ ψ) h₀ →
    ∀ (I : Type) [Fintype I] (h : I → GA D S), IsClassSystem S (B.levJ ψ) h →
    ∃ κ : ℂ, ∀ F ∈ B.formsC ψ, (GlobalTheory.FlatVecSum.princ B).classSum ω ψ h₀ F = κ • B.classSum ω ψ h F := by
  intro D S T B hB hS ψ hψ hQ ω hω m h₀ hC₀ I _ h hC
  obtain ⟨hle, -⟩ := GlobalTheory.T.principalLevel_le_level_characters_agree B hB ψ hQ
  obtain ⟨Fs, hF, hFu⟩ := GlobalTheory.T.finite_coset_representatives_level B hB ψ hQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_const_twistedSum_fockVectors_principalDatum B hB hS ψ hψ hQ ω hω Fs hF hFu
  refine ⟨κ, fun F hFm => ?_⟩
  have hinv := GlobalTheory.T.classSumTerms_invariant_principalLevel B hB hS ψ hψ hQ ω hω F hFm
  have hlaw := ((B.mem_formsC).1 hFm).2
  funext g
  rw [Base.classSum_apply, Base.classSum_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_apply]
  have key := GlobalTheory.T.classSum_regroup_finerLevel_cosets (Bridge.ratF S) (ratF_injective S) hle hF hFu (fun i => finPt S (h₀ i)) hC₀.reps
    (fun i => finPt S (h i)) hC.reps
    (fun y => series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g)
    (fun γ y => (hinv g).1 γ y) (fun k hk y => (hinv g).2 k hk y)
  simp only [symm_finPt S (hC₀.fin _), inner_sum B ψ ω hF hκ hlaw (hC.fin _)] at key
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, show (GlobalTheory.FlatVecSum.princ B).F = B.F from rfl]
  rw [key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.ClassSumPrinc
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.BaseGood

theorem base_good : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ (j : Fin D.R.m) (F : Frame (Vc D j) (Wc D j)) (hF : F.Good) (de : Twist D Circle), de.Good → PlacesOK Rl.Pg de.Q → ∃ (w : _root_.GlobalTheory.ExportSeries.Weight D (Vc D j).rank) (mu : ResChars D Circle), (∀ τ, w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) ∧ (∀ τ, w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) ∧ ∀ P : LevelP Rl.Pg (Wc D j).rank ℂ, (⟨hF.rank_le, F, ⟨Rl.Pg, P, mu⟩, de, w, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩ : Base (Vc D j) (Wc D j)).Good := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC j F hF de hde hpl
  have hL := hC.lev
  have hS : SplitSet Rl.Pg := by
    obtain ⟨P, h1, -, hP⟩ := hpl.split
    exact hP.mono h1
  have hr : Odd D.R.r := Formalism.L2.NTheta.odd_r D.R
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  obtain ⟨Pa, hPa1, hPa2, hPa⟩ := hpl.split
  refine ⟨GlobalTheory.ConjTwist.liftWeight D j, fun PP => GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹,
    fun _ => rfl, fun _ => rfl, fun P => ?_⟩
  exact
    { even := rV ▸ hr.add_odd D.R.t_odd
      odd := rW ▸ hr
      frame := hF
      de := hde
      places := hpl
      wt := GlobalTheory.ConjTwist.liftWeight_good D j
      sig := fun _ => rfl
      sigOK := D.sp.W_sig _
      eta := GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq D Rl.C Rl.eta hL.eta (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL)
      hecke := (hL.mu0 j).1
      real := GlobalTheory.GridWeil.triv_base (hL.mu0 j) (Rl.C.isMu0 j).triv
      unram := GlobalTheory.T.levelChoice_mu_unramified_outside_type_places D _ _ _ hL hS j
      tame := fun PP hPP x hx hi u hu => by
        have e1 := GlobalTheory.ConjTwist.eq_res_of_chrEq (hL.mu0 j) (hS.isIdemAt hPP) ((Rl.C.isMu0 j).tame PP) (hL.chi j PP hPP) x hx hi u hu
        have e2 := GlobalTheory.T.tame_residue_char_trivial_split_place_off_unramified D Circle de.chi de.Q Pa hde.unram hPa hPa2 PP (hPa1 hPP)
          (Finset.disjoint_left.1 hpl.disj hPP) x hx hi u hu
        show Rl.mu0 ((j : ℕ) + 1) x * de.chi x = GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹ u
        rw [e2, MonoidHom.one_apply, mul_one]
        exact Circle.ext e1
      inf := fun τ => by
        have e : ((GlobalTheory.ConjTwist.liftWeight D j).c τ : ℚ) - (((GlobalTheory.ConjTwist.liftWeight D j).p τ : ℚ) -
            (GlobalTheory.ConjTwist.liftWeight D j).q τ) / 2 + 1 / 2 = -(D.hc τ).e j := by
          have h := GlobalTheory.ConjTwist.liftC_cast D j τ
          simp only [GlobalTheory.ConjTwist.liftWeight]
          linarith
        rw [e]
        exact GlobalTheory.ConjRefChar.reference_lift_character_exponent_neg_base hL j τ }

end GlobalTheory.SeriesTie.BaseGood

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspOfReading


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem mem_cuspA_of_rdU_mem_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w hw hn f hf hfh
  classical
  set S := T.cuspA j (wtA w) w.n with hS
  haveI : FiniteDimensional T.Q.c.F S := h.toLawsM.cuspFD j hj (wtA w) w.n (dom_wtA w)
  haveI : Module.Free T.Q.c.F S := Module.Free.of_divisionRing _ _
  let b := Module.finBasis T.Q.c.F S
  let b' : Fin (Module.finrank T.Q.c.F S) → T.R j := fun i => (b i : T.R j)
  have hb'S : Submodule.span T.Q.c.F (Set.range b') ≤ S := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (b i).2
  have hSb' : S ≤ Submodule.span T.Q.c.F (Set.range b') := by
    intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ Submodule.span T.Q.c.F (Set.range b) := by rw [b.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := S.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  by_contra hfS
  have hli : LinearIndependent T.Q.c.F (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) := by
    rw [linearIndependent_finCons]
    exact ⟨b.linearIndependent.map' S.subtype (Submodule.ker_subtype _), fun hm => hfS (hb'S hm)⟩
  have hsec : ∀ i, (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := by
    intro i
    refine Fin.cases hf (fun i => ?_) i
    exact cusp_le_sec _ _ _ _ _ (b i).2
  have hC := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj T.σ₀ T.toCore.good_σ₀ (wtA w) w.n (dom_wtA w) _ _ hsec hli
  have hC' : LinearIndependent ℂ (Fin.cons (rdU (T.U j T.σ₀) f) (fun i => rdU (T.U j T.σ₀) (b' i)) :
      Fin (Module.finrank T.Q.c.F S + 1) → _) := by
    convert hC using 1
    funext i
    refine Fin.cases rfl (fun i => rfl) i
  rw [linearIndependent_finCons] at hC'
  apply hC'.2
  have hspan := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h j hj w hw hn T.σ₀ T.toCore.good_σ₀ hfh
  refine (Submodule.span_le.2 ?_) hspan
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hSb' hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

end GlobalTheory.CuspOfReading
end
