module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle327
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle088
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle032
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.IdemLat

theorem finPart_idem_mem {D : D7} {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D}
    (h : ∀ x : 𝓞 D.host.E, x ≠ 0 →
      (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) :
    finPart D e ∈ intAE D := by
  have h1 : (1 : 𝓞 D.host.E) ∉ P.asIdeal := fun h1 =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := not_not.1 fun hn => h1 ((h 1 one_ne_zero).2 hn)
  simpa using this

theorem finPart_placeIdem_mem {D : D7} {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) : finPart D f ∈ intAE D := by
  rcases h with ⟨⟨_, h⟩, rfl⟩ | ⟨rfl, _, h⟩
  · have he := finPart_idem_mem h
    rw [RingHom.map_add (f := _)]
    exact add_mem he (GlobalTheory.IdemSupport.finPart_cA_mem he)
  · exact finPart_idem_mem h

theorem lamHat_idem : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f →
    ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V := by
  intro D V P e f h y hy
  exact (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2 _ (finPart_placeIdem_mem h) y hy

end GlobalTheory.IdemLat
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)


theorem GlobalTheory.Div.inner_EEp3_eq_zero_of_ne : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ p q, p ≠ q → ∀ e ∈ R.EEp3 p, ∀ e' ∈ R.EEp3 q, ⟪e, e'⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hH hPos hB p q hpq e he e' he'

  have hmap : ∀ r, (R.EEp3 r).map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
      Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum r.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) := by
    intro r
    rw [Submodule.map_le_iff_le_comap]
    exact iSup₂_le fun c hc => Submodule.map_le_iff_le_comap.1 hc.2
  have hx : LinearMap.adjoint (R.Th A3.A.μ0) e ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hmap p (Submodule.mem_map_of_mem he)
  have hy : LinearMap.adjoint (R.Th A3.A.μ0) e' ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hmap q (Submodule.mem_map_of_mem he')
  have h0 := GlobalTheory.T.complex_points_parts_distinct_types_orthogonal R F hOk hC hH p q hpq _ hx _ hy
  have hk := hB A3.A.μ0 p e he
  rw [LinearMap.comp_apply] at hk
  have hin : ⟪R.Th A3.A.μ0 (LinearMap.adjoint (R.Th A3.A.μ0) e), e'⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right]; exact h0
  rw [hk, inner_smul_left] at hin
  have ha : (0 : ℝ) < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.μ0 j p := by
    rw [RealDat3.prod_lamN]
    exact mul_pos hPos.1 (Finset.prod_pos fun j _ => hPos.2 j _ _)
  rcases mul_eq_zero.1 hin with h | h
  · exfalso
    rw [Complex.conj_ofReal] at h
    exact ha.ne' (by exact_mod_cast h)
  · exact h
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdFrame

theorem vStd_of_orthonormal_span : ∀ (D : D7) (i : Fin D.R.m), ((∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → VStd D i := by
  intro D i h
  refine vStd_of_frameChoice D i ⟨h.1, fun a => ?_⟩
  show (Vc D i).frame a ∈ (Vc D i).L0
  rw [h.2]
  exact Submodule.subset_span ⟨a, rfl⟩

end GlobalTheory.StdFrame
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BasePins

theorem orient_std_lev : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) , R.toLevCh.Is A.μ0 → LawsJ T → ∀ i, OMPins T R κ v₀ O i → T.pb = R.C.P.pb ∧ VStd D i ∧ LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (O i).lev := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hT i hO
  exact ⟨GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hL (hO.2.tuple ()).half, hO.2.lift.std, hO.2.lift.lev⟩

end GlobalTheory.BasePins
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PinsFixHalf

theorem pb_eq_of_pins : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → LawsJ T → (∀ i, OMPins T R κ v₀ O i) → T.pb = R.C.P.pb := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hR hT hO
  exact GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hR
    ((hO ⟨0, lt_of_lt_of_le (by norm_num) D.R.two_le_m⟩).2.tuple ()).half

end GlobalTheory.PinsFixHalf
end

section

set_option autoImplicit false

noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftWeight

theorem one_le_aPl_last (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p n : ℕ) (hp : p = D.R.k + i) (hn : n + 1 = p) :
    1 ≤ aPl D i p τ n := by
  subst hp
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hi : (i : ℕ) < D.R.m := i.isLt
  have hlt : n < D.R.k + (i : ℕ) := by omega
  have h1 : ¬ n < D.R.k - 1 := by omega
  have h2 : n - (D.R.k - 1) < D.R.m := by omega
  have hidx : (⟨n - (D.R.k - 1), h2⟩ : Fin D.R.m) = i := Fin.ext (by simp only; omega)
  have hlam : Formalism.L2.NTheta.lamAt (D.hc τ) n = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right h1, dite_eq_left h2, hidx]
  have hg := (D.hc τ).gap_be i
  have hq : ((D.R.k + (i : ℕ) : ℕ) : ℚ) = (n : ℚ) + 1 := by
    rw [← hn]; push_cast; ring
  simp only [aPl, if_pos hlt]
  rw [hlam, hq]
  have hfl : (1 : ℤ) ≤ ⌊-(D.hc τ).b i + (D.hc τ).e i - ((n : ℚ) + 1 - ((n : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

theorem kapTop_lastPos (D : D7) (i : Fin D.R.m) : (kapTop D i).LastPos := by
  intro τ k hk
  have hi : (i : ℕ) < D.R.m := i.isLt
  have hW := D.sp.W_sigval ((i : ℕ) + 1) (by omega) (by omega) (tauE D τ)
  have hs : ((Wc D i).sig (tauE D τ)).1 = D.R.k + (i : ℕ) := by
    show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = D.R.k + (i : ℕ)
    rw [hW]
    show D.R.k + ((i : ℕ) + 1) - 1 = D.R.k + (i : ℕ)
    omega
  have hk' : (k : ℕ) + 1 = D.R.k + (i : ℕ) := by
    have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + ((i : ℕ) + 1) - 1 := rfl
    omega
  exact one_le_aPl_last D i τ _ k hs (hk'.trans hs.symm)

end GlobalTheory.LiftWeight
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem lamAt_last {R : Ranks} (h : HCParam R) (i : Fin R.m) (n : ℕ) (hn : n + 1 = R.k + i) :
    Formalism.L2.NTheta.lamAt h n = -h.b i := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  have e : n - (R.k - 1) = i := by omega
  unfold Formalism.L2.NTheta.lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2
  exact Fin.ext e

theorem lastPos_of_kapIs :
    ∀ (D : D7) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ i, (κ i).LastPos := by
  intro D κ h i τ k hk
  rw [(h i τ).1 k,
    show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hp : (k : ℕ) + 1 = D.R.k + i := by
    rw [hk]
    simp only [Ranks.sigW]
    omega
  have hg := (D.hc τ).gap_be i
  have hq : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) = ((k : ℕ) : ℚ) + 1 := by
    exact_mod_cast hk.symm
  simp only [aPl, if_pos k.2]
  rw [lamAt_last (D.hc τ) i k hp, hq]
  have h1 : (1 : ℤ) ≤ ⌊-(D.hc τ).b i + (D.hc τ).e i - (((k : ℕ) : ℚ) + 1 - (((k : ℕ) : ℚ) + 1)) -
      ((D.R.t : ℚ) + 1) / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

end GlobalTheory.HolDict
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Div

theorem tieIn_of_fwTie : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), FWTie T R κ v₀ → TieIn T R κ v₀ :=
  fun _ _ _ _ _ t => ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.Div
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiDetValues



theorem res_mem {D : D7} (S : Subfield ℂ) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq c χ)
    (hS : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ S)
    (P : Pl D.host.E) (ψ : (kP P)ˣ →* ℂˣ) (hψ : IsRes χ P ψ⁻¹) (u : (kP P)ˣ) : ((ψ u : ℂˣ) : ℂ) ∈ S := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have hnt : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.ext h
    rw [h0, map_zero] at ha
    exact u.ne_zero ha.symm
  have h4 := hψ a (Units.mk0 _ ha0) u rfl ha.symm
  have h5 := hc.2 P e he (Units.mk0 _ ha0) (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) rfl
  have h6 := hS (Formalism.L2.JoinChr.locU he.1 (Units.mk0 _ ha0)) (by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, hinf,
      zero_mul, add_zero])
  rw [h5, ← h4, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at h6
  exact inv_mem_iff.1 h6



theorem chiC_mem_coeff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (g : G), ∃ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = ((chiC R i g : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL t i g
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T t.alg t.laws.pins.2.2.1
  have hσ : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.good_σ₀
  have hA := (t.chiR i D.what₂.embLL hσ).2.2.2.1
  have h : ((chiC R i g : ℂˣ) : ℂ) ∈ (res T D.what₂.embLL).fieldRange := by
    unfold chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy, -⟩ := hA x hx
    exact ⟨y, hy.symm⟩
  exact h

end GlobalTheory.ChiDetValues
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRep



theorem exists_cusp_rep : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → (∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) → ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i), ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) := by
  intro D G _ T κ i lev _ hL hW
  have hnat := fun f (hf : f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) => ((mem_cusp _ _ _ _ _ _).1 hf).1.1
  exact ⟨{ toFun := fun g => (actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev g).restrict (hW g)
           map_one' := LinearMap.ext fun F => Subtype.ext
             (actL_one _ _ _ hL.total hL.func hL.one (hnat _ F.2))
           map_mul' := fun g g' => LinearMap.ext fun F => Subtype.ext
             (actL_mul _ _ _ hL.total hL.func hL.mul g g' (hnat _ F.2)) },
    fun _ _ => rfl⟩

end GlobalTheory.LevelRep
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.LevActInt

theorem fromTest_moved {K : Type} [Field K] {ιB : Type}
    {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
    {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop}
    {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ιB → Sˣ) → pts S → pts S → Prop}
    {G : Type} [Group G] {actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop}
    (hL : ActLaws pts mapR borR actR) (g : G) {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : FromTest pts mapR (mvPt pts actR g y) := by
  obtain ⟨p, φ, z, hz⟩ := hy
  exact ⟨p, φ, _, hL.nat g _ S φ z _ y _ hz (mvPt_spec hL.total g z) (mvPt_spec hL.total g y)⟩

theorem intAll_actLev : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → ∀ g (f f' : Cu T κ i), (f' : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) → Formalism.IndefR.FWT.IntAll T κ f → Formalism.IndefR.FWT.IntAll T κ f' := by
  intro D G _ T κ i lev h hL g f f' hf hF
  have hj := inR (D := D) i
  have hnat := ((mem_cusp _ _ _ _ _ _).1 f.2).1.1
  rintro la ⟨_, ⟨⟨q, S, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩⟩
  let := io.toAlgebra
  have hmv := mvPt_spec hL.total g y.1
  let y' : IntFr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c S io :=
    ⟨_, fromTest_moved hL g y.2.1,
      GlobalTheory.FormTies.LevelMove.integral_of_levR _ _ _ _ _ _ (lev g) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V e (evI y' f.1) := hF la ⟨_, ⟨PtV.mk la ho y' hy () trivial, rfl⟩⟩
  have e1 : evI y f'.1 = evI y' f.1 := by
    rw [hf]
    exact evalAt_actL hL (h.evalWD _ hj) frMap_trans_id g hnat y.1
  show 0 ≤ nval S.V e (evI y f'.1)
  rw [e1]
  exact h0

end GlobalTheory.LevActInt
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem mu_real_eq_prod_det : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) (e : D.what₂.Tau → ℤ), IsInfFam θ → MuVal V χ mu → (∀ ρ, HasInfExp D χ ρ (-(e ρ : ℚ))) → ∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ (-(e ρ)) := by
  intro D θ V χ mu e hθ hmu he u hu
  obtain ⟨x, hx, h⟩ := GlobalTheory.VacuumCharacter.exists_root hθ V
    (fun τ => (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ).ne_zero) u hu
  rw [hmu.2 u x hx, h χ (fun ρ => -(e ρ)) (fun ρ => by push_cast; exact he ρ)]
  rfl

end GlobalTheory.HolRead
end
